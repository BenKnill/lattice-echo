/* Rotate-and-back cycles built only from the verified routines:
 *   shear_p(T): lattice_fwd(T) then lattice_bwd(zero)   gives p += T[x]
 *   shear_x(T): swap the bytes of every point, shear_p(T), swap back
 * Prints a SHA-256 of the point array after every shear. stdin: tables A, B, -A, -B (4 x 256 bytes). */
#include <CommonCrypto/CommonDigest.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
void lattice_fwd(uint8_t *pts, uint64_t n, const uint8_t kick[256]);
void lattice_bwd(uint8_t *pts, uint64_t n, const uint8_t kick[256]);
enum { NP = 65536 };
static uint8_t pts[2 * NP], zero[256], A[256], B[256], nA[256], nB[256];
static void hash(void) { unsigned char d[32]; CC_SHA256(pts, sizeof pts, d); for (int i = 0; i < 32; i++) printf("%02x", d[i]); printf("\n"); }
static void swap(void) { for (int i = 0; i < NP; i++) { uint8_t t = pts[2 * i]; pts[2 * i] = pts[2 * i + 1]; pts[2 * i + 1] = t; } }
static void shear_p(const uint8_t *T) { lattice_fwd(pts, NP, T); lattice_bwd(pts, NP, zero); hash(); }
static void shear_x(const uint8_t *T) { swap(); lattice_fwd(pts, NP, T); lattice_bwd(pts, NP, zero); swap(); hash(); }
int main(int argc, char **argv) {
  int cycles = argc > 1 ? atoi(argv[1]) : 10;
  if (fread(A, 1, 256, stdin) != 256 || fread(B, 1, 256, stdin) != 256 || fread(nA, 1, 256, stdin) != 256 || fread(nB, 1, 256, stdin) != 256) return 2;
  for (int r = 0; r < 256; r++) for (int c = 0; c < 256; c++) { pts[2 * (r * 256 + c)] = (uint8_t)c; pts[2 * (r * 256 + c) + 1] = (uint8_t)((127 - r + 256) % 256); }
  hash();
  for (int k = 0; k < cycles; k++) { shear_x(A); shear_p(B); shear_x(A); shear_x(nA); shear_p(nB); shear_x(nA); }
  return 0;
}
