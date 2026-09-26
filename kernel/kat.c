/* Native known-answer and round-trip tests for the lattice kernel.
 * Compares every output byte against a plain C reference, then checks that
 * backward undoes forward exactly over many steps and random kick tables. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void lattice_fwd(uint8_t *pts, uint64_t n, const uint8_t kick[256]);
void lattice_bwd(uint8_t *pts, uint64_t n, const uint8_t kick[256]);

static void ref_fwd(uint8_t *q, uint64_t n, const uint8_t *k) {
  for (uint64_t i = 0; i < n; i++) {
    uint8_t x = q[2 * i], p = q[2 * i + 1];
    p = (uint8_t)(p + k[x]);
    x = (uint8_t)(x + p);
    q[2 * i] = x; q[2 * i + 1] = p;
  }
}

static uint64_t rng = 0x9e3779b97f4a7c15ull;
static uint64_t next(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }

int main(void) {
  enum { N = 65536 };
  static uint8_t a[2 * N], b[2 * N], orig[2 * N], kick[256];
  int fails = 0;
  for (int trial = 0; trial < 64; trial++) {
    for (int i = 0; i < 256; i++) kick[i] = (uint8_t)next();
    for (int i = 0; i < 2 * N; i++) orig[i] = a[i] = b[i] = (uint8_t)next();
    uint64_t n = trial == 0 ? 0 : trial == 1 ? 1 : trial < 8 ? (next() % 17) : N;
    for (int step = 0; step < 50; step++) {
      lattice_fwd(a, n, kick);
      ref_fwd(b, n, kick);
      if (memcmp(a, b, sizeof a)) { printf("FAIL fwd trial %d step %d\n", trial, step); fails++; break; }
    }
    for (int step = 0; step < 50; step++) lattice_bwd(a, n, kick);
    if (memcmp(a, orig, sizeof a)) { printf("FAIL round trip trial %d\n", trial); fails++; }
  }
  printf("%s: 64 trials, forward matches reference and backward restores every byte\n", fails ? "FAILED" : "ok");
  return fails != 0;
}
