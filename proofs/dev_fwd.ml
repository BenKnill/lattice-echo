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
e(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC));;
e(ASM_CASES_TAC `n = 0`);;
(* n = 0: CBZ jumps straight to the return. *)
e(ASM_REWRITE_TAC[LT] THEN ARM_SIM_TAC LATTICE_ECHO_EXEC [1]);;
