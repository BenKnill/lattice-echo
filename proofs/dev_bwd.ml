g `!pts n tbl (xs:num->byte) (ps:num->byte) (kick:num->byte) pc.
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
           MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(pts,2 * n)])`;;
e(REWRITE_TAC[NONOVERLAPPING_CLAUSES; C_ARGUMENTS; SOME_FLAGS] THEN
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
   [ARM_SIM_TAC LATTICE_ECHO_EXEC [1] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; WORD_SUB_0; LT; LE_0] THEN ASM_MESON_TAC[];
    ALL_TAC; ALL_TAC; ALL_TAC]);;
e(X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  ENSURES_INIT_TAC "s0" THEN SUFFIX_SPLIT_TAC);;
e(ARM_STEPS_TAC LATTICE_ECHO_EXEC (1--4));;
let BWD_INDEX = prove(`!x p:byte. (word_and (word_sub (word_zx x:int32) (word_zx p)) (word 255):int32) = word_zx (word_sub x p)`, BITBLAST_TAC);;
let WORD_ZX_SUB_BYTE = prove(`!a b:byte. (word_zx (word_sub (word_zx a:int32) (word_zx b)):byte) = word_sub a b`, BITBLAST_TAC);;
e(FIRST_X_ASSUM(fun th ->
    if can (term_match [] `read X3 s4 = x`) (concl th)
    then ASSUME_TAC(SIMP_RULE[WORD_ZX_ZX; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64; ARITH; BWD_INDEX] th)
    else failwith "not X3"));;
e(FIRST_ASSUM(MP_TAC o SPEC `val(word_sub (xs(i:num)) (ps i):byte)` o check (free_in `tbl:int64` o concl)) THEN
  REWRITE_TAC[VAL_BYTE_LT_256; GSYM WORD_ZX_ZX_BYTE] THEN DISCH_TAC);;
e(ARM_STEPS_TAC LATTICE_ECHO_EXEC (5--9));;
e(ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC);;
show_goals();;
