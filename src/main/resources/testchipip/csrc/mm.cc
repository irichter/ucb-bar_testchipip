// See LICENSE for license details.

#include "mm.h"
#include <iostream>
#include <fstream>
#include <cstdlib>
#include <cstring>
#include <cassert>
#include <sys/mman.h>
#include <fcntl.h>
#include <fesvr/byteorder.h>
#include <fesvr/elf.h>
#define PT_TLS 7
#include <sys/stat.h>

void mm_t::write(uint64_t addr, uint8_t *data, uint64_t strb, uint64_t size)
{
  strb &= ((1 << size) - 1) << (addr % word_size);
  addr %= this->size;

  uint8_t *base = this->data + (addr / word_size) * word_size;
  for (int i = 0; i < word_size; i++) {
    if (strb & 1)
      base[i] = data[i];
    strb >>= 1;
  }
}

std::vector<char> mm_t::read(uint64_t addr)
{
  addr %= this->size;

  uint8_t *base = this->data + addr;
  return std::vector<char>(base, base + word_size);
}

void mm_t::init(size_t sz, int wsz, int lsz)
{
  assert(wsz > 0 && lsz > 0 && (lsz & (lsz-1)) == 0 && lsz % wsz == 0);
  word_size = wsz;
  line_size = lsz;
  data = (uint8_t *) mmap(
          NULL, sz, PROT_READ|PROT_WRITE, MAP_SHARED|MAP_ANONYMOUS, -1, 0);
  size = sz;
}

mm_t::~mm_t()
{
  munmap(data, this->size);
}

void mm_magic_t::init(size_t sz, int wsz, int lsz)
{
  mm_t::init(sz, wsz, lsz);
  dummy_data.resize(word_size);
}

void mm_magic_t::tick(
  bool reset,

  bool ar_valid,
  uint64_t ar_addr,
  uint64_t ar_id,
  uint64_t ar_size,
  uint64_t ar_len,

  bool aw_valid,
  uint64_t aw_addr,
  uint64_t aw_id,
  uint64_t aw_size,
  uint64_t aw_len,

  bool w_valid,
  uint64_t w_strb,
  void *w_data,
  bool w_last,

  bool r_ready,
  bool b_ready)
{
  bool ar_fire = !reset && ar_valid && ar_ready();
  bool aw_fire = !reset && aw_valid && aw_ready();
  bool w_fire  = !reset && w_valid && w_ready();
  bool r_fire  = !reset && r_valid() && r_ready;
  bool b_fire  = !reset && b_valid() && b_ready;

  if (ar_fire) {
    uint64_t start_addr = (ar_addr / word_size) * word_size;
    for (int i = 0; i <= ar_len; i++) {
      auto dat = read(start_addr + i * word_size);
      rresp.push(mm_rresp_t(ar_id, dat, i == ar_len));
    }
  }

  if (aw_fire) {
    store_addr = aw_addr;
    store_id = aw_id;
    store_count = aw_len + 1;
    store_size = 1 << aw_size;
    store_inflight = true;
  }

  if (w_fire) {
    write(store_addr, (uint8_t *) w_data, w_strb, store_size);
    store_addr += store_size;
    store_count--;

    if (store_count == 0) {
      store_inflight = false;
      bresp.push(store_id);
      assert(w_last);
    }
  }

  if (b_fire)
    bresp.pop();

  if (r_fire)
    rresp.pop();

  cycle++;

  if (reset) {
    while (!bresp.empty()) bresp.pop();
    while (!rresp.empty()) rresp.pop();
    cycle = 0;
  }
}

template <bool isBE, typename T> static inline T to_native(T n)
{
  if (isBE) {
    return swap(n);
  }
  return n;
}

template <typename PHDR, bool isBE, typename EHDR>
static void load_elf_to_data(
  uint64_t start,
  const EHDR *eh,
  size_t file_size,
  uint8_t *data,
  size_t data_size)
{
  assert(
    file_size >= (to_native<isBE>(eh->e_phoff) +
                  (sizeof(PHDR) * to_native<isBE>(eh->e_phnum))));
  const PHDR *ph =
    (const PHDR *) (((const uint8_t *) eh) + to_native<isBE>(eh->e_phoff));
  static_assert(
    sizeof(eh->e_phoff) == sizeof(ph->p_offset), "Wrong PHDR for EHDR");
  for (uint16_t i = 0; i < eh->e_phnum; i++) {
    switch (to_native<isBE>(ph[i].p_type)) {
    case PT_LOAD:
    case PT_TLS:
      fprintf(stderr, "Section[%d](%d):", i, to_native<isBE>(ph[i].p_type));
      auto memsz = to_native<isBE>(ph[i].p_memsz);
      fprintf(stderr, " memsz: 0x%lx", (uint64_t) memsz);
      if (memsz) {
        auto vaddr = to_native<isBE>(ph[i].p_vaddr);
        assert(vaddr >= start);
        auto memoff = vaddr - start;
        auto filesz = to_native<isBE>(ph[i].p_filesz);
        fprintf(
          stderr, " vaddr=0x%lx memoff=0x%lx filesz=0x%lx", (uint64_t) vaddr,
          (uint64_t) memoff, (uint64_t) filesz);
        assert(file_size >= (to_native<isBE>(ph[i].p_offset) + filesz));
        assert(filesz <= memsz);
        assert(memoff + memsz <= data_size);
        memcpy(
          data + memoff,
          (((const uint8_t *) eh) + to_native<isBE>(ph[i].p_offset)), filesz);
        memset(data + memoff + filesz, '\0', memsz - filesz);
      }
      fprintf(stderr, "\n");
    }
  }
}

void mm_t::load_elf(uint64_t start, const char *fname)
{
  int fd = open(fname, O_RDONLY);
  struct stat s;
  assert(fd != -1);
  if (fstat(fd, &s) < 0) {
    fprintf(stderr, "Couldn't open loadelf file %s\n", fname);
    abort();
  }
  size_t file_size = s.st_size;

  char *buf = (char *) mmap(NULL, file_size, PROT_READ, MAP_PRIVATE, fd, 0);
  assert(buf != MAP_FAILED);
  close(fd);

  fprintf(stderr, "load_elf processing %s\n", fname);

  assert(file_size >= sizeof(Elf64_Ehdr));
  const Elf64_Ehdr *eh64 = (const Elf64_Ehdr *) buf;
  assert(IS_ELF32(*eh64) || IS_ELF64(*eh64));
  assert(IS_ELFLE(*eh64) || IS_ELFBE(*eh64));
  assert(IS_ELF_EXEC(*eh64));
  assert(IS_ELF_RISCV(*eh64) || IS_ELF_EM_NONE(*eh64));
  assert(IS_ELF_VCURRENT(*eh64));

  if (IS_ELFLE(*eh64)) {
    if (IS_ELF32(*eh64))
      load_elf_to_data<Elf32_Phdr, false>(
        start, (const Elf32_Ehdr *) buf, file_size, data, size);
    else
      load_elf_to_data<Elf64_Phdr, false>(
        start, (const Elf64_Ehdr *) buf, file_size, data, size);
  } else {
#ifndef RISCV_ENABLE_DUAL_ENDIAN
    throw std::invalid_argument("Specified ELF is big endian.  Configure with "
                                "--enable-dual-endian to enable support");
#else
    memif->set_target_endianness(memif_endianness_big);
    if (IS_ELF32(*eh64))
      load_elf_to_data<Elf32_Phdr, true>(
        start, (const Elf32_Ehdr *) buf, file_size, data, size);
    else
      load_elf_to_data<Elf64_Phdr, true>(
        start, (const Elf64_Ehdr *) buf, file_size, data, size);
#endif
  }

  munmap(buf, file_size);
}

void mm_t::load_mem(unsigned long start, const char *fname)
{
  std::string line;
  std::ifstream in(fname);
  unsigned long fsize = 0;

  if (!in.is_open()) {
    fprintf(stderr, "Couldn't open loadmem file %s\n", fname);
    abort();
  }

  while (std::getline(in, line))
  {
    #define parse_nibble(c) ((c) >= 'a' ? (c)-'a'+10 : (c)-'0')
    for (ssize_t i = line.length()-2, j = 0; i >= 0; i -= 2, j++) {
      char byte = (parse_nibble(line[i]) << 4) | parse_nibble(line[i+1]);
      ssize_t addr = (start + j) % size;
      data[addr] = byte;
    }
    start += line.length()/2;
    fsize += line.length()/2;

    if (fsize > this->size) {
      fprintf(stderr, "Loadmem file is too large\n");
      abort();
    }
  }
}
