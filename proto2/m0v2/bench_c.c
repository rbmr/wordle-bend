// C twin of m0/src/main.bend, same loop and layout. Args: <n> <reps>.
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#define G 14855u
#define CNT 256u

int main(int argc, char **argv) {
  if (argc < 3) {
    fprintf(stderr, "usage: bench_c <n> <reps>\n");
    return 2;
  }
  uint32_t n = (uint32_t)strtoul(argv[1], 0, 10);
  uint32_t reps = (uint32_t)strtoul(argv[2], 0, 10);
  size_t total = (size_t)G * n + CNT + n;
  uint32_t *a = (uint32_t *)calloc(total, sizeof(uint32_t));
  if (!a) return 1;
  uint32_t tbase = G * n;
  uint32_t cbase = tbase;
  uint32_t ubase = cbase + CNT;
  for (uint32_t g = 0; g < G; g++) {
    uint32_t base = g * n;
    for (uint32_t i = 0; i < n; i++) {
      a[base + i] = (g * 37u + i * 11u) & 255u;
    }
  }
  uint64_t acc = 0;
  for (uint64_t row = 0; row < (uint64_t)reps * G; row++) {
    uint32_t g = (uint32_t)(row % G);
    uint32_t base = g * n;
    uint32_t sq = 0;
    uint32_t nt = 0;
    for (uint32_t i = 0; i < n; i++) {
      uint32_t f = a[base + i];
      uint32_t old = a[cbase + f];
      sq += 2u * old + 1u;
      a[cbase + f] = old + 1u;
      a[ubase + nt] = f;
      nt++;
    }
    for (uint32_t j = 0; j < nt; j++) {
      a[cbase + a[ubase + j]] = 0;
    }
    acc += sq;
  }
  printf("%llu\n", (unsigned long long)acc);
  return 0;
}
