
e(SUBGOAL_THEN
   `read (memory :> bytes8 (word_add pts (word (2 * i)))) s0 = xs i /\
    read (memory :> bytes8 (word_add (word_add pts (word (2 * i))) (word 1))) s0 = ps i /\
    read (memory :> bytes8 (word_add pts (word (2 * i + 1)))) s0 = ps i /\
    read (memory :> bytes8 (word_add (tbl:int64) (word_zx (word_zx ((xs:num->byte) (i:num)):int32):int64))) (s0:armstate) =
      (kick:num->byte) (val (xs i))`
   STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; word_zx; VAL_WORD; DIMINDEX_32] THEN
    SIMP_TAC[MOD_LT; ARITH_RULE `x < 256 ==> x < 2 EXP 32`;
             REWRITE_RULE[DIMINDEX_8] (ISPEC `x:byte` VAL_BOUND)] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT CONJ_TAC THENL
     [MEM_AT_TAC `i:num` `xs:num->byte`;
      MEM_AT_TAC `i:num` `xs:num->byte`;
      MEM_AT_TAC `i:num` `xs:num->byte`;
      MEM_AT_TAC `val(xs(i:num):byte)` `tbl:int64`];
    ALL_TAC]);;
e(ARM_STEPS_TAC LATTICE_ECHO_EXEC (1--3));;
