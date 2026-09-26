/* Run the verified object on the film's exact scenario and print a SHA-256 of the
 * whole point array after every step: 100 steps forward, then 100 back.
 * usage: trace K STEPS < kick-table (256 bytes on stdin, from web/lattice.js) */
#include <CommonCrypto/CommonDigest.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
void lattice_fwd(uint8_t *pts, uint64_t n, const uint8_t kick[256]);
void lattice_bwd(uint8_t *pts, uint64_t n, const uint8_t kick[256]);
static void hash(const uint8_t *p, size_t n) {
  unsigned char d[32]; CC_SHA256(p, (CC_LONG)n, d);
  for (int i = 0; i < 32; i++) printf("%02x", d[i]); printf("\n");
}
int main(int argc, char **argv) {
  int steps = argc > 1 ? atoi(argv[1]) : 100;
  static uint8_t kick[256], pts[2 * 65536];
  if (fread(kick, 1, 256, stdin) != 256) return 2;
  for (int r = 0; r < 256; r++) for (int c = 0; c < 256; c++) {
    pts[2 * (r * 256 + c)] = (uint8_t)c; pts[2 * (r * 256 + c) + 1] = (uint8_t)((128 - 1 - r + 256) % 256);
  }
  hash(pts, sizeof pts);
  for (int s = 0; s < steps; s++) { lattice_fwd(pts, 65536, kick); hash(pts, sizeof pts); }
  for (int s = 0; s < steps; s++) { lattice_bwd(pts, 65536, kick); hash(pts, sizeof pts); }
  return 0;
}
