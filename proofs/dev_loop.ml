e(ENSURES_WHILE_UP_TAC `n:num` `pc + 0x4` `pc + 0x24`
   `\i s. read X0 s = word_add pts (word (2 * i)) /\
          read X1 s = word_sub (word n) (word i) /\
          read X2 s = tbl /\
          (!j. j < 256
               ==> read (memory :> bytes8 (word_add tbl (word j))) s = kick j) /\
          (!j. j < n
               ==> read (memory :> bytes8 (word_add pts (word (2 * j)))) s =
                     (if j < i then fwd_x kick (xs j) (ps j) else xs j) /\
                   read (memory :> bytes8 (word_add pts (word (2 * j + 1)))) s =
                     (if j < i then fwd_p kick (xs j) (ps j) else ps j)) /\
          (~(i = 0) ==> (read ZF s <=> i = n))`);;
e(ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC);;
(* init: CBZ not taken *)
e(ARM_SIM_TAC LATTICE_ECHO_EXEC [1] THEN
  REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; WORD_SUB_0; LT] THEN ASM_REWRITE_TAC[]);;
