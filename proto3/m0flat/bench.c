// C twin of proto3/m0/src/main.bend. Same arrays, same partition, same
// checksum chain. Args: <n> <reps> <variant>.
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#define G 14855u

static uint32_t tbl_size(uint32_t n) { return G * n; }

int main(int argc, char **argv) {
  if (argc < 4) {
    fprintf(stderr, "usage: bench <n> <reps> <variant>\n");
    return 2;
  }
  uint32_t n = (uint32_t)strtoul(argv[1], 0, 10);
  uint32_t reps = (uint32_t)strtoul(argv[2], 0, 10);
  uint32_t variant = (uint32_t)strtoul(argv[3], 0, 10);
  size_t total = (size_t)G * n + 256u + (variant == 0 ? n : 0u);
  uint32_t *a = (uint32_t *)calloc(total, sizeof(uint32_t));
  if (!a) return 1;
  uint32_t cbase = G * n;
  uint32_t ubase = cbase + 256u;
  for (uint32_t g = 0; g < G; g++) {
    uint32_t base = g * n;
    for (uint32_t i = 0; i < n; i++) a[base + i] = (g * 37u + i * 11u) & 255u;
  }
  uint64_t acc = 0;
  uint64_t rows = (uint64_t)reps * G;
  for (uint64_t row = 0; row < rows; row++) {
    uint32_t g = (uint32_t)(row % G);
    uint32_t base = g * n;
    uint32_t sq = 0;
    if (variant == 0) {
      uint32_t nt = 0;
      for (uint32_t i = 0; i < n; i++) {
        uint32_t f = a[base + i];
        uint32_t old = a[cbase + f];
        sq += 2u * old + 1u;
        a[cbase + f] = old + 1u;
        a[ubase + nt] = f;
        nt++;
      }
      for (uint32_t j = 0; j < nt; j++) a[cbase + a[ubase + j]] = 0;
    } else {
      uint32_t genb = (uint32_t)row << 16;
      for (uint32_t i = 0; i < n; i++) {
        uint32_t f = a[base + i];
        uint32_t cell = a[cbase + f];
        uint32_t diff = cell - genb;
        uint32_t fresh = 1u - (diff >> 31);
        uint32_t old = diff * fresh;
        sq += 2u * old + 1u;
        a[cbase + f] = genb + old + 1u;
      }
    }
    acc += sq;
  }
  printf("%llu\n", (unsigned long long)acc);
  return 0;
}
