/*
 * lattice_fwd_neon: a faster drop-in for lattice_fwd, same contract.
 *
 *   void lattice_fwd_neon(uint8_t *pts, uint64_t n, const uint8_t kick[256]);
 *
 * 16 points per iteration: LDP loads 32 contiguous bytes into two vectors, UZP1/UZP2
 * split them into an x-vector and a p-vector, the 256-byte kick table lives in
 * v16..v31, and kick[x] is assembled from eight 32-byte TBL lookups (an out-of-range
 * TBL index gives 0, so exactly one lookup contributes per lane). ZIP1/ZIP2 re-interleave
 * (x,p) before STP writes them back. The last n mod 16 points use the reference scalar
 * loop. v8..v15 are not touched.
 *
 * Only encodings present in the s2n-bignum ARM model are used (LDP/STP of two Q regs,
 * UZP1/UZP2, ZIP1/ZIP2, MOVI, SUB, TBL, ORR, ADD), so the object decodes for proof.
 */

        .text
        .p2align 2

#if defined(__APPLE__)
        .globl _lattice_fwd_neon
_lattice_fwd_neon:
#else
        .globl lattice_fwd_neon
        .type lattice_fwd_neon, %function
lattice_fwd_neon:
#endif
        ldp     q16, q17, [x2]
        ldp     q18, q19, [x2, #32]
        ldp     q20, q21, [x2, #64]
        ldp     q22, q23, [x2, #96]
        ldp     q24, q25, [x2, #128]
        ldp     q26, q27, [x2, #160]
        ldp     q28, q29, [x2, #192]
        ldp     q30, q31, [x2, #224]
        movi    v7.16b, #32
        lsr     x9, x1, #4
        cbz     x9, 3f
1:      ldp     q0, q1, [x0]                    // 32 contiguous bytes: x0 p0 x1 p1 ...
        uzp1    v5.16b, v0.16b, v1.16b          // v5 = 16 x (even bytes)
        uzp2    v1.16b, v0.16b, v1.16b          // v1 = 16 p (odd bytes)
        mov     v0.16b, v5.16b                  // v0 = 16 x
        tbl     v2.16b, {v16.16b, v17.16b}, v0.16b
        sub     v3.16b, v0.16b, v7.16b
        tbl     v4.16b, {v18.16b, v19.16b}, v3.16b
        orr     v2.16b, v2.16b, v4.16b
        sub     v3.16b, v3.16b, v7.16b
        tbl     v4.16b, {v20.16b, v21.16b}, v3.16b
        orr     v2.16b, v2.16b, v4.16b
        sub     v3.16b, v3.16b, v7.16b
        tbl     v4.16b, {v22.16b, v23.16b}, v3.16b
        orr     v2.16b, v2.16b, v4.16b
        sub     v3.16b, v3.16b, v7.16b
        tbl     v4.16b, {v24.16b, v25.16b}, v3.16b
        orr     v2.16b, v2.16b, v4.16b
        sub     v3.16b, v3.16b, v7.16b
        tbl     v4.16b, {v26.16b, v27.16b}, v3.16b
        orr     v2.16b, v2.16b, v4.16b
        sub     v3.16b, v3.16b, v7.16b
        tbl     v4.16b, {v28.16b, v29.16b}, v3.16b
        orr     v2.16b, v2.16b, v4.16b
        sub     v3.16b, v3.16b, v7.16b
        tbl     v4.16b, {v30.16b, v31.16b}, v3.16b
        orr     v2.16b, v2.16b, v4.16b          // v2 = kick[x]
        add     v1.16b, v1.16b, v2.16b          // p + kick[x]
        add     v0.16b, v0.16b, v1.16b          // x + p
        zip1    v2.16b, v0.16b, v1.16b          // re-interleave: x0 p0 x1 p1 ...
        zip2    v3.16b, v0.16b, v1.16b
        stp     q2, q3, [x0], #32
        subs    x9, x9, #1
        b.ne    1b
3:      and     x1, x1, #15
        cbz     x1, 5f
4:      ldrb    w3, [x0]
        ldrb    w4, [x0, #1]
        ldrb    w5, [x2, x3]
        add     w4, w4, w5
        add     w3, w3, w4
        strb    w4, [x0, #1]
        strb    w3, [x0], #2
        subs    x1, x1, #1
        b.ne    4b
5:      ret

#if !defined(__APPLE__)
        .size lattice_fwd_neon, .-lattice_fwd_neon
#endif
