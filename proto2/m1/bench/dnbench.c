/* C twin of dn_main.bend: the identical loop (packed 4-responses-per-U32
 * feedback table, 256-cell count array, touched-list clear) written directly,
 * so the per-visit cost of the Bend state machine can be compared with plain C
 * on the same machine and the same data. Build:
 *   clang -std=c11 -O3 -o dnbench dnbench.c
 * Usage: ./dnbench [c] [reps]    (default 500 400; gg=14855, k=40 fixed)
 */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>

static uint32_t C = 500;
static uint32_t GG = 14855;
static uint32_t K = 40;
static uint32_t REPS = 400;

static inline uint32_t pbase(void) { return (C * GG) / 4 + 8; }
static inline uint32_t sbase(void) { return pbase() + 1024; }
static inline uint32_t asize(void) { return sbase() + 64; }

static void fill_fb(uint32_t *fb, uint32_t n) {
  uint32_t s = 12345;
  for (uint32_t i = 0; i < n; i++) {
    s = s * 1664525u + 1013904223u;
    fb[i] = s;
  }
}

static void fill_set(uint32_t *set, uint32_t k, uint32_t c) {
  for (uint32_t i = 0; i < k; i++) set[i] = (i * 37 + 11) % c;
}

/* The distinct-count walk, directly (Bend's dn_go phases 0..6 inline). */
static uint32_t dcount(uint32_t *fb, uint32_t *prof, const uint32_t *set,
                       uint32_t g, uint32_t k, uint32_t c) {
  uint32_t *cnt = prof + 224;
  uint32_t *touched = prof + 480;
  uint32_t t = 0;
  const uint32_t fbase = g * c;
  for (uint32_t i = 0; i < k; i++) {
    uint32_t fi = fbase + set[i];
    uint32_t w = fb[fi >> 2];
    uint32_t b = fi & 3;
    uint32_t sh = (b >= 2) ? 16 : 0;
    uint32_t t1 = (w >> sh);
    uint32_t t2 = (b & 1) ? (t1 >> 8) : t1;
    uint32_t r = t2 & 255;
    uint32_t old = cnt[r];
    if (old == 0) touched[t++] = r;
    cnt[r] = old + 1;
  }
  for (uint32_t j = 0; j < t; j++) cnt[touched[j]] = 0;
  prof[736] = t; /* dn_go phase 6 */
  return t;
}

int main(int argc, char **argv) {
  if (argc > 1) C = (uint32_t)strtoul(argv[1], NULL, 10);
  if (argc > 2) REPS = (uint32_t)strtoul(argv[2], NULL, 10);
  uint32_t n = asize();
  uint32_t *a = calloc(n, sizeof(uint32_t));
  if (!a) return 1;
  uint32_t *fb = a;
  uint32_t *prof = a + pbase();
  uint32_t *set = a + sbase();
  fill_fb(fb, (C * GG) / 4);
  fill_set(set, K, C);

  uint64_t iters = (uint64_t)REPS * GG;
  uint32_t g = 0;
  uint32_t last = 0;
  for (uint64_t it = 0; it < iters; it++) {
    last = dcount(fb, prof, set, g, K, C);
    g++;
    if (g >= GG) g = 0;
  }
  uint32_t sum = 0;
  for (uint32_t i = 0; i < 64; i++) sum += a[i];
  (void)sum;
  /* same checksum as the Bend twin: 64 fb words, the result cell, 64 count cells */
  uint32_t chk = 0;
  for (uint32_t i = 0; i < 129; i++) {
    uint32_t v;
    if (i < 64) v = a[i];
    else if (i == 64) v = prof[736];
    else v = prof[224 + (i - 65)];
    chk = chk * 31u + v;
  }
  printf("C=%u G=%u k=%u iters=%llu\n", C, GG, K, (unsigned long long)iters);
  printf("chk %u\n", chk);
  free(a);
  return 0;
}
