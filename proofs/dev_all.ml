(* Development replay for LATTICE_FWD_CORE: re-run from the top each time. *)

let WORD_ZX_ZX_BYTE = prove
 (`!x:byte. (word_zx (word_zx x:int32):int64) = word (val x)`,
  GEN_TAC THEN REWRITE_TAC[GSYM word_zx] THEN CONV_TAC WORD_BLAST);;

let VAL_BYTE_LT_256 = prove
 (`!x:byte. val x < 256`,
  GEN_TAC THEN MP_TAC(ISPEC `x:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC);;

let ADDR_SUCC = WORD_RULE
 `!a:int64 k. word_add (word_add a (word k)) (word 1) = word_add a (word (k + 1))`;;

g `!pts n tbl (xs:num->byte) (ps:num->byte) (kick:num->byte) pc.
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
           MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(pts,2 * n)])`;;

e(REWRITE_TAC[NONOVERLAPPING_CLAUSES; C_ARGUMENTS; SOME_FLAGS]);;
e(MAP_EVERY X_GEN_TAC [`pts:int64`; `n:num`; `tbl:int64`; `xs:num->byte`;
                       `ps:num->byte`; `kick:num->byte`; `pc:num`]);;
e(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN VAL_INT64_TAC `n:num`);;
e(ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[LT] THEN ARM_SIM_TAC LATTICE_ECHO_EXEC [1]; ALL_TAC]);;
e(ENSURES_WHILE_UP_TAC `n:num` `pc + 0x4` `pc + 0x24`
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
          (~(i = 0) ==> (read ZF s <=> i = n))`);;
e(ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ARM_SIM_TAC LATTICE_ECHO_EXEC [1] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; WORD_SUB_0; LT; LE_0] THEN ASM_MESON_TAC[];
    ALL_TAC; ALL_TAC; ALL_TAC]);;

(* ---- loop body: i -> i + 1 ---- *)
e(X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  ENSURES_INIT_TAC "s0");;
(* peel index i off each untouched-suffix fact, leaving a strict suffix *)
e(REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_forall c && can (find_term ((=) `i <= j:num`)) c then
      let a = SPEC `i:num` th in
      let b = prove(mk_imp(`i:num < j /\ j < n`, `i:num <= j /\ j < n`), ARITH_TAC) in
      ASSUME_TAC(MP (SPEC `i:num` th) (CONJ (SPEC `i:num` LE_REFL) (ASSUME `i:num < n`))) THEN
      ASSUME_TAC(GEN `j:num` (DISCH `i:num < j /\ j < n`
        (MP (SPEC `j:num` th) (MP b (ASSUME `i:num < j /\ j < n`)))))
    else failwith "no")));;
e(FIRST_ASSUM(MP_TAC o SPEC `val(xs(i:num):byte)` o check (free_in `tbl:int64` o concl)) THEN
  REWRITE_TAC[VAL_BYTE_LT_256; GSYM WORD_ZX_ZX_BYTE] THEN DISCH_TAC);;
e(ARM_STEPS_TAC LATTICE_ECHO_EXEC (1--8));;
e(ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [CONV_TAC WORD_RULE;
    CONV_TAC WORD_RULE;
    X_GEN_TAC `j:num` THEN REWRITE_TAC[ARITH_RULE `j < i + 1 <=> j < i \/ j = i`] THEN
    STRIP_TAC THENL
     [ASM_SIMP_TAC[];
      FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[fwd_x; fwd_p] THEN
      SIMP_TAC[WORD_ZX_ZX; WORD_ZX_ADD; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64; ARITH]];
    X_GEN_TAC `j:num` THEN REWRITE_TAC[ARITH_RULE `j < i + 1 <=> j < i \/ j = i`] THEN
    STRIP_TAC THENL
     [ASM_SIMP_TAC[];
      FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[fwd_x; fwd_p] THEN
      SIMP_TAC[WORD_ZX_ZX; WORD_ZX_ADD; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64; ARITH]];
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    DISCH_TAC THEN
    REWRITE_TAC[GSYM WORD_ADD;
      WORD_RULE `!a b c:int64. word_sub (word_sub a b) c = word_sub a (word_add b c)`] THEN
    ASM_SIMP_TAC[WORD_SUB; ARITH_RULE `i < n ==> i + 1 <= n`; VAL_WORD; DIMINDEX_64] THEN
    SUBGOAL_THEN `n - (i + 1) < 2 EXP 64` (fun th -> SIMP_TAC[MOD_LT; th]) THEN
    ASM_ARITH_TAC]);;

(* ---- back edge: B.NE taken while i < n ---- *)
e(X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  UNDISCH_TAC `~(i = 0) ==> (read ZF s0 <=> i = n)` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ARM_STEPS_TAC LATTICE_ECHO_EXEC [1] THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

(* ---- exit: B.NE falls through once i = n ---- *)
e(ENSURES_INIT_TAC "s0" THEN
  UNDISCH_TAC `~(n = 0) ==> (read ZF s0 <=> n = n)` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ARM_STEPS_TAC LATTICE_ECHO_EXEC [1] THEN ENSURES_FINAL_STATE_TAC THEN ASM_SIMP_TAC[]);;
top_thm();;
