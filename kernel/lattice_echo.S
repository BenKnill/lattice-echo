/*
 * Exactly reversible lattice standard map on the 256 x 256 torus.
 *
 *   void lattice_fwd(uint8_t *pts, uint64_t n, const uint8_t kick[256]);
 *   void lattice_bwd(uint8_t *pts, uint64_t n, const uint8_t kick[256]);
 *
 * pts holds n points as byte pairs (x, p). All arithmetic is mod 256, which
 * the byte stores provide for free.
 *
 *   forward:   p <- p + kick[x];   x <- x + p          (kick, then drift)
 *   backward:  x <- x - p;         p <- p - kick[x]    (undo drift, undo kick)
 *
 * Each half-step is a shear by a whole number of lattice cells, so each is a
 * permutation of the 65536 points, whatever the kick table holds.
 */

        .text
        .p2align 2

#if defined(__APPLE__)
        .globl _lattice_fwd
        .globl _lattice_bwd
_lattice_fwd:
#else
        .globl lattice_fwd
        .type lattice_fwd, %function
        .globl lattice_bwd
        .type lattice_bwd, %function
lattice_fwd:
#endif
        cbz     x1, 2f
1:      ldrb    w3, [x0]            // x
        ldrb    w4, [x0, #1]        // p
        ldrb    w5, [x2, x3]        // kick[x]
        add     w4, w4, w5          // p + kick[x]
        add     w3, w3, w4          // x + p'
        strb    w4, [x0, #1]        // p' = low byte
        strb    w3, [x0], #2        // x' = low byte, advance to next point
        subs    x1, x1, #1
        b.ne    1b
2:      ret

#if defined(__APPLE__)
_lattice_bwd:
#else
        .size lattice_fwd, .-lattice_fwd
lattice_bwd:
#endif
        cbz     x1, 4f
3:      ldrb    w3, [x0]            // x'
        ldrb    w4, [x0, #1]        // p'
        sub     w3, w3, w4          // x' - p'
        and     w3, w3, #0xff       // reduce before indexing the table
        ldrb    w5, [x2, x3]        // kick[x]
        sub     w4, w4, w5          // p' - kick[x]
        strb    w4, [x0, #1]
        strb    w3, [x0], #2
        subs    x1, x1, #1
        b.ne    3b
4:      ret

#if !defined(__APPLE__)
        .size lattice_bwd, .-lattice_bwd
#endif
