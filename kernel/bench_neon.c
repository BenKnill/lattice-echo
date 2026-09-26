/* Check lattice_fwd_neon against the verified lattice_fwd (every length 0..300, random
 * tables and data), then time both on 65,536 points. */
#include <mach/mach_time.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
void lattice_fwd(uint8_t *pts, uint64_t n, const uint8_t kick[256]);
void lattice_fwd_neon(uint8_t *pts, uint64_t n, const uint8_t kick[256]);
static uint64_t s = 0x2545F4914F6CDD1Dull;
static uint8_t rnd(void) { s ^= s << 13; s ^= s >> 7; s ^= s << 17; return (uint8_t)(s >> 24); }
int main(void) {
  static uint8_t a[2 * 65536 + 64], b[2 * 65536 + 64], kick[256];
  int bad = 0;
  for (int n = 0; n <= 300 && !bad; n++) for (int t = 0; t < 20; t++) {
    for (int i = 0; i < 256; i++) kick[i] = rnd();
    for (int i = 0; i < 2 * n + 64; i++) a[i] = b[i] = rnd();
    lattice_fwd(a, n, kick); lattice_fwd_neon(b, n, kick);
    if (memcmp(a, b, 2 * n + 64)) { printf("MISMATCH n=%d\n", n); bad = 1; break; }
  }
  printf("%s: n = 0..300, 20 random trials each (including bytes past the end)\n", bad ? "FAILED" : "ok");
  mach_timebase_info_data_t tb; mach_timebase_info(&tb);
  for (int i = 0; i < 256; i++) kick[i] = rnd();
  for (int i = 0; i < 2 * 65536; i++) a[i] = b[i] = rnd();
  const int R = 2000; uint64_t t0 = mach_absolute_time();
  for (int r = 0; r < R; r++) lattice_fwd(a, 65536, kick);
  uint64_t t1 = mach_absolute_time();
  for (int r = 0; r < R; r++) lattice_fwd_neon(b, 65536, kick);
  uint64_t t2 = mach_absolute_time();
  double ns_ref = (double)(t1 - t0) * tb.numer / tb.denom / R / 65536, ns_neon = (double)(t2 - t1) * tb.numer / tb.denom / R / 65536;
  printf("reference: %.3f ns/point   neon: %.3f ns/point   speedup %.1fx   states equal: %s\n",
         ns_ref, ns_neon, ns_ref / ns_neon, memcmp(a, b, 2 * 65536) ? "NO" : "yes");
  return bad;
}
