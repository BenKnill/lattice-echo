(* ========================================================================= *)
(* Exactly reversible lattice standard map: object-code correctness.         *)
(*                                                                           *)
(*   lattice_fwd:  p <- p + kick[x];  x <- x + p        (all mod 256)        *)
(*   lattice_bwd:  x <- x - p;        p <- p - kick[x]                       *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

let lattice_echo_mc = define_assert_from_elf "lattice_echo_mc"
  "build/lattice_echo.o"
[
  0xb4000141;       (* arm_CBZ X1 (word 40) *)
  0x39400003;       (* arm_LDRB W3 X0 (Immediate_Offset (word 0)) *)
  0x39400404;       (* arm_LDRB W4 X0 (Immediate_Offset (word 1)) *)
  0x38636845;       (* arm_LDRB W5 X2 (Register_Offset X3) *)
  0x0b050084;       (* arm_ADD W4 W4 W5 *)
  0x0b040063;       (* arm_ADD W3 W3 W4 *)
  0x39000404;       (* arm_STRB W4 X0 (Immediate_Offset (word 1)) *)
  0x38002403;       (* arm_STRB W3 X0 (Postimmediate_Offset (word 2)) *)
  0xf1000421;       (* arm_SUBS X1 X1 (rvalue (word 1)) *)
  0x54ffff01;       (* arm_BNE (word 2097120) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xb4000161;       (* arm_CBZ X1 (word 44) *)
  0x39400003;       (* arm_LDRB W3 X0 (Immediate_Offset (word 0)) *)
  0x39400404;       (* arm_LDRB W4 X0 (Immediate_Offset (word 1)) *)
  0x4b040063;       (* arm_SUB W3 W3 W4 *)
  0x12001c63;       (* arm_AND W3 W3 (rvalue (word 255)) *)
  0x38636845;       (* arm_LDRB W5 X2 (Register_Offset X3) *)
  0x4b050084;       (* arm_SUB W4 W4 W5 *)
  0x39000404;       (* arm_STRB W4 X0 (Immediate_Offset (word 1)) *)
  0x38002403;       (* arm_STRB W3 X0 (Postimmediate_Offset (word 2)) *)
  0xf1000421;       (* arm_SUBS X1 X1 (rvalue (word 1)) *)
  0x54fffee1;       (* arm_BNE (word 2097116) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let LATTICE_ECHO_EXEC = ARM_MK_EXEC_RULE lattice_echo_mc;;
