(* ========================================================================= *)
(* Proof-carrying optimization.                                              *)
(*                                                                           *)
(* lattice_fwd_neon is a faster implementation of the forward step (16 points *)
(* per iteration via LD2/TBL/ST2, ~2.6x the scalar reference on an M-series   *)
(* chip). The goal here is to prove it satisfies the SAME contract as the     *)
(* reference lattice_fwd, so an optimized contribution is accepted on the     *)
(* strength of its proof rather than a reviewer re-reading the kernel.        *)
(*                                                                           *)
(* Status: the object below decodes (lattice_fwd_neon_mc, LATTICE_FWD_NEON_EXEC).  *)
(* Next step: prove LATTICE_FWD_NEON_CORRECT with the same statement as        *)
(* LATTICE_FWD_CORRECT in proofs/lattice_echo.ml. Independent evidence that    *)
(* they already agree: kernel/bench_neon.c checks byte-for-byte equality with  *)
(* the reference over lengths 0..300 with random tables, then times both.      *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
loadt "proofs/lattice_echo.ml";;

let lattice_fwd_neon_mc = define_assert_from_elf "lattice_fwd_neon_mc"
  "build/lattice_fwd_neon.o"
[
  0xad404450       (* ldp q16, q17, [x2] *);
  0xad414c52       (* ldp q18, q19, [x2, #0x20] *);
  0xad425454       (* ldp q20, q21, [x2, #0x40] *);
  0xad435c56       (* ldp q22, q23, [x2, #0x60] *);
  0xad446458       (* ldp q24, q25, [x2, #0x80] *);
  0xad456c5a       (* ldp q26, q27, [x2, #0xa0] *);
  0xad46745c       (* ldp q28, q29, [x2, #0xc0] *);
  0xad477c5e       (* ldp q30, q31, [x2, #0xe0] *);
  0x4f01e407       (* movi.16b v7, #0x20 *);
  0xd344fc29       (* lsr x9, x1, #4 *);
  0xb4000449       (* cbz x9, 0xb0 *);
  0xad400400       (* ldp q0, q1, [x0] *);
  0x4e011805       (* uzp1.16b v5, v0, v1 *);
  0x4e015801       (* uzp2.16b v1, v0, v1 *);
  0x4ea51ca0       (* mov.16b v0, v5 *);
  0x4e002202       (* tbl.16b v2, { v16, v17 }, v0 *);
  0x6e278403       (* sub.16b v3, v0, v7 *);
  0x4e032244       (* tbl.16b v4, { v18, v19 }, v3 *);
  0x4ea41c42       (* orr.16b v2, v2, v4 *);
  0x6e278463       (* sub.16b v3, v3, v7 *);
  0x4e032284       (* tbl.16b v4, { v20, v21 }, v3 *);
  0x4ea41c42       (* orr.16b v2, v2, v4 *);
  0x6e278463       (* sub.16b v3, v3, v7 *);
  0x4e0322c4       (* tbl.16b v4, { v22, v23 }, v3 *);
  0x4ea41c42       (* orr.16b v2, v2, v4 *);
  0x6e278463       (* sub.16b v3, v3, v7 *);
  0x4e032304       (* tbl.16b v4, { v24, v25 }, v3 *);
  0x4ea41c42       (* orr.16b v2, v2, v4 *);
  0x6e278463       (* sub.16b v3, v3, v7 *);
  0x4e032344       (* tbl.16b v4, { v26, v27 }, v3 *);
  0x4ea41c42       (* orr.16b v2, v2, v4 *);
  0x6e278463       (* sub.16b v3, v3, v7 *);
  0x4e032384       (* tbl.16b v4, { v28, v29 }, v3 *);
  0x4ea41c42       (* orr.16b v2, v2, v4 *);
  0x6e278463       (* sub.16b v3, v3, v7 *);
  0x4e0323c4       (* tbl.16b v4, { v30, v31 }, v3 *);
  0x4ea41c42       (* orr.16b v2, v2, v4 *);
  0x4e228421       (* add.16b v1, v1, v2 *);
  0x4e218400       (* add.16b v0, v0, v1 *);
  0x4e013802       (* zip1.16b v2, v0, v1 *);
  0x4e017803       (* zip2.16b v3, v0, v1 *);
  0xac810c02       (* stp q2, q3, [x0], #0x20 *);
  0xf1000529       (* subs x9, x9, #0x1 *);
  0x54fffc01       (* b.ne 0x2c *);
  0x92400c21       (* and x1, x1, #0xf *);
  0xb4000141       (* cbz x1, 0xdc *);
  0x39400003       (* ldrb w3, [x0] *);
  0x39400404       (* ldrb w4, [x0, #0x1] *);
  0x38636845       (* ldrb w5, [x2, x3] *);
  0x0b050084       (* add w4, w4, w5 *);
  0x0b040063       (* add w3, w3, w4 *);
  0x39000404       (* strb w4, [x0, #0x1] *);
  0x38002403       (* strb w3, [x0], #0x2 *);
  0xf1000421       (* subs x1, x1, #0x1 *);
  0x54ffff01       (* b.ne 0xb8 *);
  0xd65f03c0       (* ret *)
];;

let LATTICE_FWD_NEON_EXEC = ARM_MK_EXEC_RULE lattice_fwd_neon_mc;;
