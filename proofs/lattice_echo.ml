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

(* ------------------------------------------------------------------------- *)
(* The map on one point, with coordinates as bytes (so arithmetic is mod 256) *)
(* and an arbitrary kick table.                                               *)
(* ------------------------------------------------------------------------- *)

let fwd_p = new_definition
 `fwd_p (kick:num->byte) (x:byte) (p:byte) = word_add p (kick (val x))`;;

let fwd_x = new_definition
 `fwd_x (kick:num->byte) (x:byte) (p:byte) = word_add x (fwd_p kick x p)`;;

let bwd_x = new_definition
 `bwd_x (x:byte) (p:byte) = word_sub x p`;;

let bwd_p = new_definition
 `bwd_p (kick:num->byte) (x:byte) (p:byte) = word_sub p (kick (val (bwd_x x p)))`;;

(* Backward undoes forward, and forward undoes backward: the step is a
   bijection of the 256 x 256 torus, whatever the kick table holds. *)

let WORD_ADD_SUB_CANCEL = WORD_RULE `!a b:N word. word_sub (word_add a b) b = a`;;
let WORD_SUB_ADD_CANCEL = WORD_RULE `!a b:N word. word_add (word_sub a b) b = a`;;

let LATTICE_BWD_FWD = prove
 (`!kick x p. bwd_x (fwd_x kick x p) (fwd_p kick x p) = x /\
              bwd_p kick (fwd_x kick x p) (fwd_p kick x p) = p`,
  REWRITE_TAC[fwd_p; fwd_x; bwd_x; bwd_p; WORD_ADD_SUB_CANCEL]);;

let LATTICE_FWD_BWD = prove
 (`!kick x p. fwd_x kick (bwd_x x p) (bwd_p kick x p) = x /\
              fwd_p kick (bwd_x x p) (bwd_p kick x p) = p`,
  REWRITE_TAC[fwd_p; fwd_x; bwd_x; bwd_p; WORD_SUB_ADD_CANCEL]);;

(* ------------------------------------------------------------------------- *)
(* Small facts about bytes and the address/zero-extension shapes that the     *)
(* ARM simulator produces.                                                    *)
(* ------------------------------------------------------------------------- *)

let WORD_ZX_ZX_BYTE = prove
 (`!x:byte. (word_zx (word_zx x:int32):int64) = word (val x)`,
  GEN_TAC THEN REWRITE_TAC[GSYM word_zx] THEN BITBLAST_TAC);;

(* The backward kernel reduces x - p with AND #0xff before indexing. *)
let BWD_INDEX = prove
 (`!x p:byte. (word_and (word_sub (word_zx x:int32) (word_zx p)) (word 255):int32) =
              word_zx (word_sub x p)`,
  BITBLAST_TAC);;

let WORD_ZX_SUB_BYTE = prove
 (`!a b:byte. (word_zx (word_sub (word_zx a:int32) (word_zx b)):byte) = word_sub a b`,
  BITBLAST_TAC);;

let VAL_BYTE_LT_256 = prove
 (`!x:byte. val x < 256`,
  GEN_TAC THEN MP_TAC(ISPEC `x:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC);;

let ZX_SIMP_TAC =
  SIMP_TAC[WORD_ZX_ZX; WORD_ZX_ADD; WORD_ZX_SUB_BYTE;
           DIMINDEX_8; DIMINDEX_32; DIMINDEX_64; ARITH];;

(* Split each "untouched suffix" fact !j. i <= j /\ j < n ==> P j into P i
   and the strict suffix !j. i < j /\ j < n ==> P j. The strict form lets the
   simulator carry it across the stores at index i. *)

let SUFFIX_SPLIT_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_forall c && can (find_term ((=) `i <= j:num`)) c then
      let b = prove(`i:num < j /\ j < n ==> i <= j /\ j < n`, ARITH_TAC) in
      ASSUME_TAC(MP (SPEC `i:num` th) (CONJ (SPEC `i:num` LE_REFL) (ASSUME `i:num < n`))) THEN
      ASSUME_TAC(GEN `j:num` (DISCH `i:num < j /\ j < n`
        (MP (SPEC `j:num` th) (MP b (ASSUME `i:num < j /\ j < n`)))))
    else failwith "SUFFIX_SPLIT_TAC"));;

(* The flag after SUBS on the counter: zero exactly when the last point is done. *)

let COUNTER_ZF_TAC =
  DISCH_TAC THEN
  REWRITE_TAC[GSYM WORD_ADD;
    WORD_RULE `!a b c:int64. word_sub (word_sub a b) c = word_sub a (word_add b c)`] THEN
  SUBGOAL_THEN `word_sub (word n) (word (i + 1)):int64 = word(n - (i + 1))` SUBST1_TAC THENL
   [ASM_SIMP_TAC[WORD_SUB; ARITH_RULE `i < n ==> i + 1 <= n`]; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `n - (i + 1) < 2 EXP 64` (fun th -> SIMP_TAC[MOD_LT; th]) THEN
  ASM_ARITH_TAC;;

(* ------------------------------------------------------------------------- *)
(* Forward kernel: every point (x,p) becomes (fwd_x, fwd_p).                  *)
(* ------------------------------------------------------------------------- *)

let LATTICE_FWD_CORRECT = prove
 (`!pts n tbl (xs:num->byte) (ps:num->byte) (kick:num->byte) pc.
     n < 2 EXP 63 /\
     nonoverlapping (word pc,0x5c) (pts,2 * n) /\
     nonoverlapping (pts,2 * n) (tbl,256)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) lattice_echo_mc /\
               read PC s = word pc /\
               C_ARGUMENTS [pts; word n; tbl] s /\
               (!j. j < 256
                    ==> read (memory :> bytes8 (word_add tbl (word j))) s = kick j) /\
               (!i. i < n
                    ==> read (memory :> bytes8 (word_add pts (word (2 * i)))) s = xs i /\
                        read (memory :> bytes8 (word_add pts (word (2 * i + 1)))) s = ps i))
          (\s. read PC s = word (pc + 0x28) /\
               (!i. i < n
                    ==> read (memory :> bytes8 (word_add pts (word (2 * i)))) s =
                          fwd_x kick (xs i) (ps i) /\
                        read (memory :> bytes8 (word_add pts (word (2 * i + 1)))) s =
                          fwd_p kick (xs i) (ps i)))
          (MAYCHANGE [PC; X0; X1; X3; X4; X5] ,, MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(pts,2 * n)])`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; C_ARGUMENTS; SOME_FLAGS] THEN
  MAP_EVERY X_GEN_TAC [`pts:int64`; `n:num`; `tbl:int64`; `xs:num->byte`;
                       `ps:num->byte`; `kick:num->byte`; `pc:num`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN VAL_INT64_TAC `n:num` THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[LT] THEN ARM_SIM_TAC LATTICE_ECHO_EXEC [1]; ALL_TAC] THEN
  ENSURES_WHILE_UP_TAC `n:num` `pc + 0x4` `pc + 0x24`
   `\i s. read X0 s = word_add pts (word (2 * i)) /\
          read X1 s = word_sub (word n) (word i) /\
          read X2 s = tbl /\
          (!j. j < 256
               ==> read (memory :> bytes8 (word_add tbl (word j))) s = kick j) /\
          (!j. j < i
               ==> read (memory :> bytes8 (word_add pts (word (2 * j)))) s =
                   fwd_x kick (xs j) (ps j)) /\
          (!j. j < i
               ==> read (memory :> bytes8 (word_add pts (word (2 * j + 1)))) s =
                   fwd_p kick (xs j) (ps j)) /\
          (!j. i <= j /\ j < n
               ==> read (memory :> bytes8 (word_add pts (word (2 * j)))) s = xs j) /\
          (!j. i <= j /\ j < n
               ==> read (memory :> bytes8 (word_add pts (word (2 * j + 1)))) s = ps j) /\
          (~(i = 0) ==> (read ZF s <=> i = n))` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(*** entry: CBZ falls through ***)
    ARM_SIM_TAC LATTICE_ECHO_EXEC [1] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; WORD_SUB_0; LT; LE_0] THEN ASM_MESON_TAC[];

    (*** one iteration: point i is transformed in place ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ENSURES_INIT_TAC "s0" THEN SUFFIX_SPLIT_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `val(xs(i:num):byte)` o check (free_in `tbl:int64` o concl)) THEN
    REWRITE_TAC[VAL_BYTE_LT_256; GSYM WORD_ZX_ZX_BYTE] THEN DISCH_TAC THEN
    ARM_STEPS_TAC LATTICE_ECHO_EXEC (1--8) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [CONV_TAC WORD_RULE;
      CONV_TAC WORD_RULE;
      X_GEN_TAC `j:num` THEN REWRITE_TAC[ARITH_RULE `j < i + 1 <=> j < i \/ j = i`] THEN
      STRIP_TAC THENL
       [ASM_SIMP_TAC[];
        FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[fwd_x; fwd_p] THEN ZX_SIMP_TAC];
      X_GEN_TAC `j:num` THEN REWRITE_TAC[ARITH_RULE `j < i + 1 <=> j < i \/ j = i`] THEN
      STRIP_TAC THENL
       [ASM_SIMP_TAC[];
        FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[fwd_x; fwd_p] THEN ZX_SIMP_TAC];
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      COUNTER_ZF_TAC];

    (*** back edge: B.NE taken while points remain ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    UNDISCH_TAC `~(i = 0) ==> (read ZF s0 <=> i = n)` THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN ARM_STEPS_TAC LATTICE_ECHO_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** exit: B.NE falls through after the last point ***)
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC LATTICE_ECHO_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_SIMP_TAC[]]);;

let LATTICE_BWD_CORRECT = prove
 (`!pts n tbl (xs:num->byte) (ps:num->byte) (kick:num->byte) pc.
     n < 2 EXP 63 /\
     nonoverlapping (word pc,0x5c) (pts,2 * n) /\
     nonoverlapping (pts,2 * n) (tbl,256)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) lattice_echo_mc /\
               read PC s = word (pc + 0x2c) /\
               C_ARGUMENTS [pts; word n; tbl] s /\
               (!j. j < 256
                    ==> read (memory :> bytes8 (word_add tbl (word j))) s = kick j) /\
               (!i. i < n
                    ==> read (memory :> bytes8 (word_add pts (word (2 * i)))) s = xs i /\
                        read (memory :> bytes8 (word_add pts (word (2 * i + 1)))) s = ps i))
          (\s. read PC s = word (pc + 0x58) /\
               (!i. i < n
                    ==> read (memory :> bytes8 (word_add pts (word (2 * i)))) s =
                          bwd_x (xs i) (ps i) /\
                        read (memory :> bytes8 (word_add pts (word (2 * i + 1)))) s =
                          bwd_p kick (xs i) (ps i)))
          (MAYCHANGE [PC; X0; X1; X3; X4; X5] ,, MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(pts,2 * n)])`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; C_ARGUMENTS; SOME_FLAGS] THEN
  MAP_EVERY X_GEN_TAC [`pts:int64`; `n:num`; `tbl:int64`; `xs:num->byte`;
                       `ps:num->byte`; `kick:num->byte`; `pc:num`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN VAL_INT64_TAC `n:num` THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[LT] THEN ARM_SIM_TAC LATTICE_ECHO_EXEC [1]; ALL_TAC] THEN
  ENSURES_WHILE_UP_TAC `n:num` `pc + 0x30` `pc + 0x54`
   `\i s. read X0 s = word_add pts (word (2 * i)) /\
          read X1 s = word_sub (word n) (word i) /\
          read X2 s = tbl /\
          (!j. j < 256
               ==> read (memory :> bytes8 (word_add tbl (word j))) s = kick j) /\
          (!j. j < i
               ==> read (memory :> bytes8 (word_add pts (word (2 * j)))) s =
                   bwd_x (xs j) (ps j)) /\
          (!j. j < i
               ==> read (memory :> bytes8 (word_add pts (word (2 * j + 1)))) s =
                   bwd_p kick (xs j) (ps j)) /\
          (!j. i <= j /\ j < n
               ==> read (memory :> bytes8 (word_add pts (word (2 * j)))) s = xs j) /\
          (!j. i <= j /\ j < n
               ==> read (memory :> bytes8 (word_add pts (word (2 * j + 1)))) s = ps j) /\
          (~(i = 0) ==> (read ZF s <=> i = n))` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(*** entry: CBZ falls through ***)
    ARM_SIM_TAC LATTICE_ECHO_EXEC [1] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; WORD_SUB_0; LT; LE_0] THEN ASM_MESON_TAC[];

    (*** one iteration: point i is restored in place ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ENSURES_INIT_TAC "s0" THEN SUFFIX_SPLIT_TAC THEN
    ARM_STEPS_TAC LATTICE_ECHO_EXEC (1--4) THEN
    FIRST_X_ASSUM(fun th ->
      if can (term_match [] `read X3 s4 = x`) (concl th)
      then ASSUME_TAC(SIMP_RULE[WORD_ZX_ZX; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64;
                                ARITH; BWD_INDEX] th)
      else failwith "not X3") THEN
    FIRST_ASSUM(MP_TAC o SPEC `val(word_sub (xs(i:num)) (ps i):byte)` o
                check (free_in `tbl:int64` o concl)) THEN
    REWRITE_TAC[VAL_BYTE_LT_256; GSYM WORD_ZX_ZX_BYTE] THEN DISCH_TAC THEN
    ARM_STEPS_TAC LATTICE_ECHO_EXEC (5--9) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [CONV_TAC WORD_RULE;
      CONV_TAC WORD_RULE;
      X_GEN_TAC `j:num` THEN REWRITE_TAC[ARITH_RULE `j < i + 1 <=> j < i \/ j = i`] THEN
      STRIP_TAC THENL
       [ASM_SIMP_TAC[];
        FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[bwd_x; bwd_p] THEN ZX_SIMP_TAC];
      X_GEN_TAC `j:num` THEN REWRITE_TAC[ARITH_RULE `j < i + 1 <=> j < i \/ j = i`] THEN
      STRIP_TAC THENL
       [ASM_SIMP_TAC[];
        FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[bwd_x; bwd_p] THEN ZX_SIMP_TAC];
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      COUNTER_ZF_TAC];

    (*** back edge: B.NE taken while points remain ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    UNDISCH_TAC `~(i = 0) ==> (read ZF s0 <=> i = n)` THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN ARM_STEPS_TAC LATTICE_ECHO_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** exit: B.NE falls through after the last point ***)
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC LATTICE_ECHO_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Subroutine forms: include the RET and the ABI's register discipline.       *)
(* ------------------------------------------------------------------------- *)

let LATTICE_FWD_SUBROUTINE_CORRECT = prove
 (`!pts n tbl (xs:num->byte) (ps:num->byte) (kick:num->byte) pc returnaddress.
     n < 2 EXP 63 /\
     nonoverlapping (word pc,0x5c) (pts,2 * n) /\
     nonoverlapping (pts,2 * n) (tbl,256)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) lattice_echo_mc /\
               read PC s = word pc /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [pts; word n; tbl] s /\
               (!j. j < 256
                    ==> read (memory :> bytes8 (word_add tbl (word j))) s = kick j) /\
               (!i. i < n
                    ==> read (memory :> bytes8 (word_add pts (word (2 * i)))) s = xs i /\
                        read (memory :> bytes8 (word_add pts (word (2 * i + 1)))) s = ps i))
          (\s. read PC s = returnaddress /\
               (!i. i < n
                    ==> read (memory :> bytes8 (word_add pts (word (2 * i)))) s =
                          fwd_x kick (xs i) (ps i) /\
                        read (memory :> bytes8 (word_add pts (word (2 * i + 1)))) s =
                          fwd_p kick (xs i) (ps i)))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(pts,2 * n)])`,
  ARM_ADD_RETURN_NOSTACK_TAC LATTICE_ECHO_EXEC LATTICE_FWD_CORRECT);;

let LATTICE_BWD_SUBROUTINE_CORRECT = prove
 (`!pts n tbl (xs:num->byte) (ps:num->byte) (kick:num->byte) pc returnaddress.
     n < 2 EXP 63 /\
     nonoverlapping (word pc,0x5c) (pts,2 * n) /\
     nonoverlapping (pts,2 * n) (tbl,256)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) lattice_echo_mc /\
               read PC s = word (pc + 0x2c) /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [pts; word n; tbl] s /\
               (!j. j < 256
                    ==> read (memory :> bytes8 (word_add tbl (word j))) s = kick j) /\
               (!i. i < n
                    ==> read (memory :> bytes8 (word_add pts (word (2 * i)))) s = xs i /\
                        read (memory :> bytes8 (word_add pts (word (2 * i + 1)))) s = ps i))
          (\s. read PC s = returnaddress /\
               (!i. i < n
                    ==> read (memory :> bytes8 (word_add pts (word (2 * i)))) s =
                          bwd_x (xs i) (ps i) /\
                        read (memory :> bytes8 (word_add pts (word (2 * i + 1)))) s =
                          bwd_p kick (xs i) (ps i)))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(pts,2 * n)])`,
  ARM_ADD_RETURN_NOSTACK_TAC LATTICE_ECHO_EXEC LATTICE_BWD_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* The echo: feeding lattice_fwd's output to lattice_bwd returns every input  *)
(* byte, for every kick table and every point.                               *)
(* ------------------------------------------------------------------------- *)

let LATTICE_ECHO_ROUND_TRIP = prove
 (`!kick (xs:num->byte) (ps:num->byte) i.
     bwd_x (fwd_x kick (xs i) (ps i)) (fwd_p kick (xs i) (ps i)) = xs i /\
     bwd_p kick (fwd_x kick (xs i) (ps i)) (fwd_p kick (xs i) (ps i)) = ps i`,
  REWRITE_TAC[LATTICE_BWD_FWD]);;
