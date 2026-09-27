(* ========================================================================= *)
(* Proof-carrying optimization.                                              *)
(*                                                                           *)
(* lattice_fwd_neon is a faster implementation of the forward step (16 points *)
(* per iteration via LDP/UZP/TBL/ZIP/STP, ~2.9x the scalar reference on an    *)
(* M-series chip). The point is that it satisfies the SAME contract as the    *)
(* reference lattice_fwd, so an optimized contribution is accepted on the     *)
(* strength of its proof rather than a reviewer re-reading the kernel.        *)
(*                                                                           *)
(* LATTICE_FWD_NEON_SUBROUTINE_CORRECT below has the statement of               *)
(* LATTICE_FWD_SUBROUTINE_CORRECT in proofs/lattice_echo.ml with only the code  *)
(* object (and its length) changed. Independent evidence that the two kernels  *)
(* agree: kernel/bench_neon.c checks byte-for-byte equality with the reference *)
(* over lengths 0..300 with random tables, then times both.                    *)
(*                                                                             *)
(* Proof shape: the entry loads the 256-byte table into Q16..Q31; a loop       *)
(* handles 16 points per iteration (invariant neon_inv), and the scalar tail   *)
(* handles the last n MOD 16 points (invariant tail_inv). Inside the vector    *)
(* body every 128-bit intermediate is abbreviated to a fresh variable together *)
(* with its 16 byte-lane values, which keeps the symbolic state small.         *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "proofs/lattice_echo.ml";;

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
(* ------------------------------------------------------------------------- *)
(* Byte lane m of a 128-bit memory word is the byte at offset m.             *)
(* ------------------------------------------------------------------------- *)

(* Proved lane by lane: READ_MEMORY_BYTESIZED_SPLIT breaks the 128-bit read
   into bytes and WORD_SIMPLE_SUBWORD_CONV picks the lane out of the join. *)

let bytes128_lane_k k =
  let kt = mk_small_numeral k in
  prove(subst [kt,`k:num`]
   `!a s. word_subword (read (memory :> bytes128 a) (s:armstate)) (8*k,8) : byte =
          read (memory :> bytes8 (word_add a (word k))) s`,
    REPEAT GEN_TAC THEN REWRITE_TAC[READ_MEMORY_BYTESIZED_SPLIT] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS; WORD_ADD_0] THEN CONV_TAC NUM_REDUCE_CONV THEN REFL_TAC);;

let BYTES128_LANE = prove
 (`!a s m. m < 16
           ==> word_subword (read (memory :> bytes128 a) (s:armstate)) (8*m,8) : byte =
               read (memory :> bytes8 (word_add a (word m))) s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP (ARITH_RULE
   `m < 16 ==> m = 0 \/ m = 1 \/ m = 2 \/ m = 3 \/ m = 4 \/ m = 5 \/ m = 6 \/ m = 7 \/
               m = 8 \/ m = 9 \/ m = 10 \/ m = 11 \/ m = 12 \/ m = 13 \/ m = 14 \/ m = 15`) th)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC (map bytes128_lane_k (0--15)));;

(* The same with the lane position as a numeral, for rewriting. *)

let bytes128_lane_num m =
  let th = SPECL [`a:int64`; `s:armstate`; mk_small_numeral m] BYTES128_LANE in
  let th = MP th (ARITH_RULE (mk_binary "<" (mk_small_numeral m, `16`))) in
  GENL [`a:int64`; `s:armstate`] (CONV_RULE (DEPTH_CONV NUM_MULT_CONV) th);;

let BYTES128_LANES_NUM = map bytes128_lane_num (0--15);;

(* ------------------------------------------------------------------------- *)
(* TBL over a 32-byte table pair: the lookup at index x - b returns kick x    *)
(* when b <= x < b + 32, and 0 when the index is out of range.               *)
(* ------------------------------------------------------------------------- *)

let TBL_OOR_NUM = prove
 (`!(t2:int128) (t1:int128) k.
     32 <= k ==> word_subword (word_join t2 t1 : 256 word) (8 * k, 8) : byte = word 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD_0; DIMINDEX_8] THEN
  MATCH_MP_TAC(MESON[MOD_0] `x = 0 ==> x MOD n = 0`) THEN MATCH_MP_TAC DIV_LT THEN
  TRANS_TAC LTE_TRANS `2 EXP 256` THEN CONJ_TAC THENL
   [MP_TAC(ISPEC `word_join (t2:int128) (t1:int128):256 word` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_256];
    REWRITE_TAC[LE_EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC]);;

let look_lemma b =
  let n k = mk_small_numeral k in
  let s t = subst [n b,`b:num`; n (b+16),`b16:num`; n (b+32),`b32:num`] t in
  prove(s `!(t2:int128) (t1:int128) (x:byte) (kick:num->byte).
      (!m. m < 16 ==> word_subword t1 (8*m,8):byte = kick (b + m)) /\
      (!m. m < 16 ==> word_subword t2 (8*m,8):byte = kick (b16 + m))
      ==> word_subword (word_join t2 t1 : 256 word) (8 * val (word_sub x (word b)), 8) : byte
          = (if b <= val x /\ val x < b32 then kick (val x) else word 0)`,
   REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC(ISPEC `x:byte` VAL_BYTE_LT_256) THEN DISCH_TAC THEN
   REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
   ASM_CASES_TAC (s `b <= val (x:byte) /\ val x < b32`) THENL
    [POP_ASSUM STRIP_ASSUME_TAC THEN ASM_REWRITE_TAC[] THEN
     ASM_CASES_TAC (s `val (x:byte) < b16`) THENL
      [W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_JOIN_LOWER o lhand o snd) THEN
       REWRITE_TAC[DIMINDEX_128; DIMINDEX_256] THEN
       ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
       FIRST_X_ASSUM(fun th -> MP_TAC(SPEC (s `val (x:byte) - b`)
         (check (fun t -> free_in `t1:int128` (concl t)) th))) THEN
       ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
       W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_JOIN_UPPER o lhand o snd) THEN
       REWRITE_TAC[DIMINDEX_128; DIMINDEX_256] THEN
       ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
       SUBGOAL_THEN (s `8 * (val (x:byte) - b) - 128 = 8 * (val x - b16)`) SUBST1_TAC THENL
        [ASM_ARITH_TAC; ALL_TAC] THEN
       FIRST_X_ASSUM(fun th -> MP_TAC(SPEC (s `val (x:byte) - b16`)
         (check (fun t -> free_in `t2:int128` (concl t)) th))) THEN
       ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN AP_TERM_TAC THEN ASM_ARITH_TAC];
     ASM_REWRITE_TAC[LE_0] THEN TRY COND_CASES_TAC THEN MATCH_MP_TAC TBL_OOR_NUM THEN ASM_ARITH_TAC]);;

let LOOK_LEMMAS = map look_lemma [0;32;64;96;128;160;192;224];;

(* The kernel ORs the eight lookups together, one per 32-byte table pair; on
   each byte lane exactly one of them is in range, so the OR is kick x. *)

let lk t2 t1 b = subst [t2,`t2:int128`; t1,`t1:int128`; mk_small_numeral b,`b:num`]
  `word_subword (word_join (t2:int128) (t1:int128) : 256 word) (8 * val (word_sub (x:byte) (word b)), 8) : byte`;;
let tv i = mk_var("T"^string_of_int i, `:int128`);;
let chain = itlist (fun j acc -> mk_comb(mk_comb(`word_or:byte->byte->byte`, lk (tv (2*j+1)) (tv (2*j)) (32*j)), acc))
                   [7;6;5;4;3;2;1] (lk (tv 1) (tv 0) 0);;
let lane_hyps = list_mk_conj (map (fun j -> subst [tv j,`t:int128`; mk_small_numeral (16*j),`c:num`]
  `!m. m < 16 ==> word_subword (t:int128) (8*m,8):byte = kick (c + m)`) (0--15));;
let sgs = map (fun j -> let b = 32*j in
      subst [tv (2*j+1),`t2:int128`; tv (2*j),`t1:int128`; mk_small_numeral b,`b:num`; mk_small_numeral (b+32),`b32:num`]
        `word_subword (word_join (t2:int128) (t1:int128) : 256 word) (8 * val (word_sub (x:byte) (word b)), 8) : byte
         = (if b <= val x /\ val x < b32 then (kick:num->byte) (val x) else word 0)`) (0--7);;
let atoms = map (fun b -> subst [mk_small_numeral b,`b:num`] `b <= val (x:byte)`) [0;32;64;96;128;160;192;224] @
            map (fun c -> subst [mk_small_numeral c,`c:num`] `val (x:byte) < c`) [32;64;96;128;160;192;224;256];;
let DECIDE_CONDS_TAC =
  MAP_EVERY (fun c ->
    (SUBGOAL_THEN c (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC]) ORELSE
    (SUBGOAL_THEN (mk_neg c) (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC])) atoms;;

let KICK_CHAIN_LANE = prove
 (mk_forall(`x:byte`, mk_imp(lane_hyps, mk_eq(chain, `(kick:num->byte) (val (x:byte))`))),
  GEN_TAC THEN STRIP_TAC THEN MP_TAC(ISPEC `x:byte` VAL_BYTE_LT_256) THEN DISCH_TAC THEN
  SUBGOAL_THEN (list_mk_conj sgs) (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT CONJ_TAC THEN
    MAP_FIRST (fun l -> MATCH_MP_TAC l THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC) LOOK_LEMMAS;
    ALL_TAC] THEN
  MP_TAC(ARITH_RULE
   `val (x:byte) < 256
    ==> val x < 32 \/ 32 <= val x /\ val x < 64 \/ 64 <= val x /\ val x < 96 \/
        96 <= val x /\ val x < 128 \/ 128 <= val x /\ val x < 160 \/ 160 <= val x /\ val x < 192 \/
        192 <= val x /\ val x < 224 \/ 224 <= val x`) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN DECIDE_CONDS_TAC THEN REWRITE_TAC[WORD_OR_0]);;

(* The kernel's first lookup indexes with x itself, not x - 0. *)

let KICK_CHAIN_LANE' = REWRITE_RULE[ADD_CLAUSES; WORD_SUB_0] KICK_CHAIN_LANE;;

(* ------------------------------------------------------------------------- *)
(* Small word facts.                                                          *)
(* ------------------------------------------------------------------------- *)

let WORD_SUBWORD_OR_8 = prove
 (`!a b:int128 k. word_subword (word_or a b) (k,8):byte =
                  word_or (word_subword a (k,8)) (word_subword b (k,8))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_OR; DIMINDEX_8; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC[BIT_TRIVIAL; DIMINDEX_128; NOT_LT]);;

let WORD_USHR_DIV16 = prove
 (`!n. n < 2 EXP 64 ==> word_ushr (word n:int64) 4 = word (n DIV 16)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; VAL_WORD; DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `n < 2 EXP 64 ==> n DIV 2 EXP 4 < 2 EXP 64 /\ n DIV 16 < 2 EXP 64`] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let WORD_AND_MOD16 = prove
 (`!n. n < 2 EXP 64 ==> word_and (word n:int64) (word 15) = word (n MOD 16)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  SUBGOAL_THEN `(word 15:int64) = word (2 EXP 4 - 1)` SUBST1_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD; VAL_WORD; DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `n MOD 16 < 2 EXP 64`] THEN CONV_TAC NUM_REDUCE_CONV);;

(* A precondition may fix auxiliary values existentially. *)

let ENSURES_EXISTS_PRE = prove
 (`!(P:B->A->bool) Q C.
     (!x. ensures step (\s. P x s) Q C) ==> ensures step (\s. ?x. P x s) Q C`,
  REWRITE_TAC[ensures] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Lane bookkeeping for the vector body. Point 16*i+m of the block being     *)
(* processed has coordinates xs(16*i+m), ps(16*i+m); every 128-bit value is  *)
(* named by a fresh variable and described by its 16 byte lanes.             *)
(* ------------------------------------------------------------------------- *)

let LANE_CONV = TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV;;

let idx m = mk_binop `(+):num->num->num` `16 * i` (mk_small_numeral m);;
let xs_at m = mk_comb(`xs:num->byte`, idx m);;
let ps_at m = mk_comb(`ps:num->byte`, idx m);;
let dsub k m = mk_binop `word_sub:byte->byte->byte` (xs_at m) (mk_comb(`word:num->byte`, mk_small_numeral (32*k)));;
let kick_at m = mk_comb(`kick:num->byte`, mk_comb(`val:byte->num`, xs_at m));;
let fwdp_at m = list_mk_comb(`fwd_p:(num->byte)->byte->byte->byte`, [`kick:num->byte`; xs_at m; ps_at m]);;
let fwdx_at m = list_mk_comb(`fwd_x:(num->byte)->byte->byte->byte`, [`kick:num->byte`; xs_at m; ps_at m]);;
let lane_sub v m = mk_comb(mk_comb(`word_subword:int128->num#num->byte`, v), mk_pair(mk_small_numeral (8*m), `8`));;
let addr_x k = mk_comb(mk_comb(`word_add:int64->int64->int64`, `pts:int64`),
                       mk_comb(`word:num->int64`, mk_binop `(*):num->num->num` `2` (idx k)));;
let addr_p k = mk_comb(mk_comb(`word_add:int64->int64->int64`, `pts:int64`),
                       mk_comb(`word:num->int64`, mk_binop `(+):num->num->num` (mk_binop `(*):num->num->num` `2` (idx k)) `1`));;

(* Name the value of 128-bit register reg in state st as nm, and record its 16
   lanes  word_subword nm (8m,8) = target m,  each proved by lane_tac after
   expanding the abbreviation. *)

let ABBREV_LANES_TAC nm reg st (target: int -> term) (lane_tac: tactic) : tactic = fun (asl,w) ->
  let sv = mk_var(st,`:armstate`) in
  let pat = mk_comb(mk_comb(`read:(armstate,int128)component->armstate->int128`, reg), sv) in
  let th = snd (find (fun (_,th) -> let c = concl th in is_eq c && lhs c = pat) asl) in
  let v = mk_var(nm,`:int128`) in
  (ABBREV_TAC (mk_eq (v, rhs (concl th))) THEN
   MAP_EVERY (fun m -> SUBGOAL_THEN (mk_eq (lane_sub v m, target m)) ASSUME_TAC THENL
                        [EXPAND_TAC nm THEN lane_tac; ALL_TAC]) (0--15)) (asl,w);;

(* Lanes of the 128-bit memory word nm at address base in state s0: lane m
   holds point k0 + m DIV 2, x for even m and p for odd m. *)

let MEM_LANES_TAC nm base k0 : tactic =
  let v = mk_var(nm,`:int128`) in
  MAP_EVERY (fun m ->
    let k = k0 + m / 2 in
    let target = if m mod 2 = 0 then xs_at k else ps_at k in
    let addr2 = if m mod 2 = 0 then addr_x k else addr_p k in
    let addr1 = mk_comb(mk_comb(`word_add:int64->int64->int64`, base), mk_comb(`word:num->int64`, mk_small_numeral m)) in
    SUBGOAL_THEN (mk_eq (lane_sub v m, target)) ASSUME_TAC THENL
     [EXPAND_TAC nm THEN REWRITE_TAC[el m BYTES128_LANES_NUM] THEN
      SUBGOAL_THEN (mk_eq (addr1, addr2)) SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
      FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN UNDISCH_TAC `16 * i + 16 <= n` THEN ARITH_TAC);
      ALL_TAC]) (0--15);;

(* Rewrite with just those assumptions whose left-hand side satisfies p. *)

let REWRITE_WITH_ASSUMS_TAC (p:term->bool) : tactic = fun (asl,w) ->
  REWRITE_TAC (filter (fun th -> let c = concl th in is_eq c && p (lhs c)) (map snd asl)) (asl,w);;

(* After the STP: the byte of point 16*i+k is lane 2k (x) or 2k+1 (p) of the
   128-bit word stored at pts+32i (k < 8) or pts+32i+16 (k >= 8). *)

let store_base k =
  if k < 8 then `word_add (pts:int64) (word (32 * i))` else `word_add (pts:int64) (word (32 * i + 16))`;;

let STORE_LANE_TAC isx k =
  let m = (if k < 8 then 2 * k else 2 * (k - 8)) + (if isx then 0 else 1) in
  let addr = if isx then addr_x k else addr_p k in
  let addr' = mk_comb(mk_comb(`word_add:int64->int64->int64`, store_base k), mk_comb(`word:num->int64`, mk_small_numeral m)) in
  SUBGOAL_THEN (mk_eq (addr, addr')) SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  REWRITE_TAC[GSYM (el m BYTES128_LANES_NUM)] THEN
  REWRITE_WITH_ASSUMS_TAC (can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes128"))) THEN
  CONV_TAC(LAND_CONV LANE_CONV) THEN
  REWRITE_WITH_ASSUMS_TAC (can (find_term (fun t -> is_var t && (fst(dest_var t) = "XPV" || fst(dest_var t) = "PPV"))));;

let CASES16 = prove
 (`!k. k < 16 ==> k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/
                  k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15`,
  CONV_TAC(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV));;

let DONE16_TAC isx =
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `j < 16 * i` THENL
   [FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN FIRST_ASSUM ACCEPT_TAC); ALL_TAC] THEN
  SUBGOAL_THEN `?k. k < 16 /\ j = 16 * i + k`
    (CHOOSE_THEN (CONJUNCTS_THEN2 (MP_TAC o MATCH_MP CASES16) SUBST1_TAC)) THENL
   [EXISTS_TAC `j - 16 * i` THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THENL (map (fun k -> FIRST_X_ASSUM SUBST1_TAC THEN STORE_LANE_TAC isx k) (0--15));;

(* ZF after SUBS on a down-counter with bound b: set exactly when i + 1 = b. *)

let COUNTER_ZF_TAC bound facts =
  let s t = subst [bound,`b:num`] t in
  DISCH_TAC THEN
  REWRITE_TAC[GSYM WORD_ADD;
    WORD_RULE `!a b c:int64. word_sub (word_sub a b) c = word_sub a (word_add b c)`] THEN
  SUBGOAL_THEN (s `word_sub (word b) (word (i + 1)):int64 = word(b - (i + 1))`) SUBST1_TAC THENL
   [REWRITE_TAC[WORD_SUB] THEN SUBGOAL_THEN (s `i + 1 <= b`) (fun th -> REWRITE_TAC[th]) THEN
    MAP_EVERY UNDISCH_TAC facts THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN (s `b - (i + 1) < 2 EXP 64`) (fun th -> SIMP_TAC[MOD_LT; th]) THEN
  MAP_EVERY UNDISCH_TAC facts THEN ARITH_TAC;;

(* Rewrite the register facts with an equation already in the assumptions. *)

let REWRITE_REGS_WITH_ASSUM_TAC (pat:term) : tactic = fun (asl,w) ->
  let th = snd(find (fun (_,th) -> concl th = pat) asl) in
  RULE_ASSUM_TAC(PURE_REWRITE_RULE[th]) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* The loop invariants and the state between the two loops.                  *)
(* ------------------------------------------------------------------------- *)

let treg_str = String.concat " /\\\n  " (map (fun k -> Printf.sprintf "read Q%d s = (t%d:int128)" (16+k) k) (0--15));;
let lane_hyp_str = String.concat " /\\\n  " (map (fun k ->
  if k = 0 then "(!m. m < 16 ==> word_subword (t0:int128) (8 * m,8):byte = (kick:num->byte) m)"
  else Printf.sprintf "(!m. m < 16 ==> word_subword (t%d:int128) (8 * m,8):byte = (kick:num->byte) (%d + m))" k (16*k)) (0--15));;
let tmem_str = String.concat " /\\\n  " (map (fun k ->
  if k = 0 then "read (memory :> bytes128 tbl) s = (t0:int128)"
  else Printf.sprintf "read (memory :> bytes128 (word_add tbl (word %d))) s = (t%d:int128)" (16*k) k) (0--15));;

let neon_inv = parse_term (Printf.sprintf "\\i s.
  read X0 s = word_add (pts:int64) (word (32 * i)) /\\
  read X9 s = word_sub (word (q:num)) (word i) /\\
  read X1 s = word (n:num) /\\ read X2 s = (tbl:int64) /\\
  read Q7 s = word 0x20202020202020202020202020202020 /\\
  %s /\\
  %s /\\
  (!j. j < 256 ==> read (memory :> bytes8 (word_add tbl (word j))) s = kick j) /\\
  (!j. j < 16 * i ==> read (memory :> bytes8 (word_add pts (word (2 * j)))) s = fwd_x kick ((xs:num->byte) j) ((ps:num->byte) j)) /\\
  (!j. j < 16 * i ==> read (memory :> bytes8 (word_add pts (word (2 * j + 1)))) s = fwd_p kick (xs j) (ps j)) /\\
  (!j. 16 * i <= j /\\ j < n ==> read (memory :> bytes8 (word_add pts (word (2 * j)))) s = xs j) /\\
  (!j. 16 * i <= j /\\ j < n ==> read (memory :> bytes8 (word_add pts (word (2 * j + 1)))) s = ps j) /\\
  (~(i = 0) ==> (read ZF s <=> i = q))" treg_str lane_hyp_str);;

let tail_inv = `\i s.
  read X0 s = word_add (pts:int64) (word (2 * (16 * q + i))) /\
  read X1 s = word_sub (word (r:num)) (word i) /\
  read X2 s = (tbl:int64) /\
  (!j. j < 256 ==> read (memory :> bytes8 (word_add tbl (word j))) s = (kick:num->byte) j) /\
  (!j. j < 16 * q + i ==> read (memory :> bytes8 (word_add pts (word (2 * j)))) s = fwd_x kick ((xs:num->byte) j) ((ps:num->byte) j)) /\
  (!j. j < 16 * q + i ==> read (memory :> bytes8 (word_add pts (word (2 * j + 1)))) s = fwd_p kick (xs j) (ps j)) /\
  (!j. 16 * q + i <= j /\ j < (n:num) ==> read (memory :> bytes8 (word_add pts (word (2 * j)))) s = xs j) /\
  (!j. 16 * q + i <= j /\ j < n ==> read (memory :> bytes8 (word_add pts (word (2 * j + 1)))) s = ps j) /\
  (~(i = 0) ==> (read ZF s <=> i = r))`;;

let mid_cond = `\s.
  read X0 s = word_add (pts:int64) (word (32 * q)) /\ read X1 s = word (n:num) /\ read X2 s = (tbl:int64) /\
  (!j. j < 256 ==> read (memory :> bytes8 (word_add tbl (word j))) s = (kick:num->byte) j) /\
  (!j. j < 16 * q ==> read (memory :> bytes8 (word_add pts (word (2 * j)))) s = fwd_x kick ((xs:num->byte) j) ((ps:num->byte) j)) /\
  (!j. j < 16 * q ==> read (memory :> bytes8 (word_add pts (word (2 * j + 1)))) s = fwd_p kick (xs j) (ps j)) /\
  (!j. 16 * q <= j /\ j < n ==> read (memory :> bytes8 (word_add pts (word (2 * j)))) s = xs j) /\
  (!j. 16 * q <= j /\ j < n ==> read (memory :> bytes8 (word_add pts (word (2 * j + 1)))) s = ps j)`;;

(* ------------------------------------------------------------------------- *)
(* One iteration of the vector loop: points 16i..16i+15 are transformed.     *)
(* ------------------------------------------------------------------------- *)

let LANE_TAC = CONV_TAC(LAND_CONV LANE_CONV) THEN ASM_REWRITE_TAC[];;
let D_TAC = LANE_TAC THEN CONV_TAC WORD_RULE;;
let K_TAC =
  REWRITE_TAC[WORD_SUBWORD_OR_8] THEN CONV_TAC(LAND_CONV LANE_CONV) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC KICK_CHAIN_LANE' THEN ASM_REWRITE_TAC[];;

let NEON_BODY_TAC =
  ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN `16 * i + 16 <= n /\ 32 * i + 32 <= 2 * n` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  (*** the untouched points after this block, in the form that survives the stores ***)
  SUBGOAL_THEN `!j. 16 * (i + 1) <= j /\ j < n
                    ==> read (memory :> bytes8 (word_add pts (word (2 * j)))) s0 = xs j` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN ASM_ARITH_TAC); ALL_TAC] THEN
  SUBGOAL_THEN `!j. 16 * (i + 1) <= j /\ j < n
                    ==> read (memory :> bytes8 (word_add pts (word (2 * j + 1)))) s0 = ps j` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN ASM_ARITH_TAC); ALL_TAC] THEN
  (*** the 32 bytes about to be loaded ***)
  ABBREV_TAC `(WA:int128) = read (memory :> bytes128 (word_add pts (word (32 * i)))) (s0:armstate)` THEN
  ABBREV_TAC `(WB:int128) = read (memory :> bytes128 (word_add pts (word (32 * i + 16)))) (s0:armstate)` THEN
  MEM_LANES_TAC "WA" `word_add (pts:int64) (word (32 * i))` 0 THEN
  MEM_LANES_TAC "WB" `word_add (pts:int64) (word (32 * i + 16))` 8 THEN
  (*** LDP, UZP1, UZP2, MOV: XV holds the 16 x bytes, PV the 16 p bytes ***)
  ARM_STEPS_TAC LATTICE_FWD_NEON_EXEC (1--4) THEN
  ABBREV_LANES_TAC "XV" `Q0` "s4" xs_at LANE_TAC THEN
  ABBREV_LANES_TAC "PV" `Q1` "s4" ps_at LANE_TAC THEN
  (*** eight TBL lookups, indices x - 32k ***)
  ARM_STEPS_TAC LATTICE_FWD_NEON_EXEC (5--6) THEN ABBREV_LANES_TAC "DV1" `Q3` "s6" (dsub 1) D_TAC THEN
  ARM_STEPS_TAC LATTICE_FWD_NEON_EXEC (7--9) THEN ABBREV_LANES_TAC "DV2" `Q3` "s9" (dsub 2) D_TAC THEN
  ARM_STEPS_TAC LATTICE_FWD_NEON_EXEC (10--12) THEN ABBREV_LANES_TAC "DV3" `Q3` "s12" (dsub 3) D_TAC THEN
  ARM_STEPS_TAC LATTICE_FWD_NEON_EXEC (13--15) THEN ABBREV_LANES_TAC "DV4" `Q3` "s15" (dsub 4) D_TAC THEN
  ARM_STEPS_TAC LATTICE_FWD_NEON_EXEC (16--18) THEN ABBREV_LANES_TAC "DV5" `Q3` "s18" (dsub 5) D_TAC THEN
  ARM_STEPS_TAC LATTICE_FWD_NEON_EXEC (19--21) THEN ABBREV_LANES_TAC "DV6" `Q3` "s21" (dsub 6) D_TAC THEN
  ARM_STEPS_TAC LATTICE_FWD_NEON_EXEC (22--24) THEN ABBREV_LANES_TAC "DV7" `Q3` "s24" (dsub 7) D_TAC THEN
  ARM_STEPS_TAC LATTICE_FWD_NEON_EXEC (25--26) THEN
  (*** the OR of the eight lookups is kick[x] on every lane ***)
  ABBREV_LANES_TAC "KV" `Q2` "s26" kick_at K_TAC THEN
  (*** p + kick[x], then x + p ***)
  ARM_STEPS_TAC LATTICE_FWD_NEON_EXEC (27--27) THEN
  ABBREV_LANES_TAC "PPV" `Q1` "s27" fwdp_at (CONV_TAC(LAND_CONV LANE_CONV) THEN ASM_REWRITE_TAC[fwd_p]) THEN
  ARM_STEPS_TAC LATTICE_FWD_NEON_EXEC (28--28) THEN
  ABBREV_LANES_TAC "XPV" `Q0` "s28" fwdx_at (CONV_TAC(LAND_CONV LANE_CONV) THEN ASM_REWRITE_TAC[fwd_x]) THEN
  (*** ZIP1, ZIP2, STP, SUBS ***)
  ARM_STEPS_TAC LATTICE_FWD_NEON_EXEC (29--32) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [CONV_TAC WORD_RULE;
    CONV_TAC WORD_RULE;
    DONE16_TAC true;
    DONE16_TAC false;
    COUNTER_ZF_TAC `q:num` [`i < q`; `16 * q + r = n`; `n < 2 EXP 63`]];;

(* ------------------------------------------------------------------------- *)
(* One iteration of the scalar tail: point 16q+i, exactly as in the           *)
(* reference proof with i shifted by 16q.                                     *)
(* ------------------------------------------------------------------------- *)

let TAIL_SUFFIX_SPLIT_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_forall c && can (find_term ((=) `16 * q + i <= j:num`)) c then
      let b = prove(`16 * q + i < j /\ j < n ==> 16 * q + i <= j /\ j < n`, ARITH_TAC) in
      ASSUME_TAC(MP (SPEC `16 * q + i` th)
                    (CONJ (SPEC `16 * q + i` LE_REFL) (ASSUME `16 * q + i < n`))) THEN
      ASSUME_TAC(GEN `j:num` (DISCH `16 * q + i < j /\ j < n`
        (MP (SPEC `j:num` th) (MP b (ASSUME `16 * q + i < j /\ j < n`)))))
    else failwith "TAIL_SUFFIX_SPLIT_TAC"));;

let TAIL_BODY_TAC =
  ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN `16 * q + i < n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  TAIL_SUFFIX_SPLIT_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `val(xs(16 * q + i):byte)` o check (free_in `tbl:int64` o concl)) THEN
  REWRITE_TAC[VAL_BYTE_LT_256; GSYM WORD_ZX_ZX_BYTE] THEN DISCH_TAC THEN
  ARM_STEPS_TAC LATTICE_FWD_NEON_EXEC (1--8) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [CONV_TAC WORD_RULE;
    CONV_TAC WORD_RULE;
    X_GEN_TAC `j:num` THEN
    REWRITE_TAC[ARITH_RULE `j < 16 * q + (i + 1) <=> j < 16 * q + i \/ j = 16 * q + i`] THEN
    STRIP_TAC THENL
     [ASM_SIMP_TAC[];
      FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[fwd_x; fwd_p] THEN ZX_SIMP_TAC];
    X_GEN_TAC `j:num` THEN
    REWRITE_TAC[ARITH_RULE `j < 16 * q + (i + 1) <=> j < 16 * q + i \/ j = 16 * q + i`] THEN
    STRIP_TAC THENL
     [ASM_SIMP_TAC[];
      FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[fwd_x; fwd_p] THEN ZX_SIMP_TAC];
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    COUNTER_ZF_TAC `r:num` [`i < r`; `r < 16`]];;

(* ------------------------------------------------------------------------- *)
(* The core theorem, with the table halves named t0..t15 so that the vector  *)
(* registers have symbolic values throughout the loop.                        *)
(* ------------------------------------------------------------------------- *)

let tvars = map (fun k -> mk_var("t"^string_of_int k, `:int128`)) (0--15);;

let core_pre_str = Printf.sprintf
 "aligned_bytes_loaded s (word pc) lattice_fwd_neon_mc /\\
  read PC s = word pc /\\
  C_ARGUMENTS [pts; word n; tbl] s /\\
  %s /\\
  %s /\\
  (!j. j < 256 ==> read (memory :> bytes8 (word_add tbl (word j))) s = kick j) /\\
  (!i. i < n ==> read (memory :> bytes8 (word_add pts (word (2 * i)))) s = xs i /\\
                 read (memory :> bytes8 (word_add pts (word (2 * i + 1)))) s = ps i)" tmem_str lane_hyp_str;;

let neon_post_str =
 "read PC s = word (pc + 0xdc) /\\
  (!i. i < n ==> read (memory :> bytes8 (word_add pts (word (2 * i)))) s = fwd_x kick (xs i) (ps i) /\\
                 read (memory :> bytes8 (word_add pts (word (2 * i + 1)))) s = fwd_p kick (xs i) (ps i))";;

let neon_frame_str =
 "MAYCHANGE [PC; X0; X1; X3; X4; X5; X9] ,,
  MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q7; Q16; Q17; Q18; Q19; Q20; Q21; Q22; Q23;
             Q24; Q25; Q26; Q27; Q28; Q29; Q30; Q31] ,,
  MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(pts,2 * n)]";;

let core_stmt = parse_term (Printf.sprintf
 "!pts n tbl (xs:num->byte) (ps:num->byte) (kick:num->byte) pc %s.
     n < 2 EXP 63 /\\
     nonoverlapping (word pc,0xe0) (pts,2 * n) /\\
     nonoverlapping (pts,2 * n) (tbl,256)
     ==> ensures arm (\\s. %s) (\\s. %s) (%s)"
  (String.concat " " (map (fun k -> Printf.sprintf "(t%d:int128)" k) (0--15)))
  core_pre_str neon_post_str neon_frame_str);;

let NEON_PRELUDE_TAC =
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; C_ARGUMENTS; SOME_FLAGS] THEN
  MAP_EVERY X_GEN_TAC ([`pts:int64`; `n:num`; `tbl:int64`; `xs:num->byte`;
                        `ps:num->byte`; `kick:num->byte`; `pc:num`] @ tvars) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN VAL_INT64_TAC `n:num` THEN
  (*** q full blocks of 16 points, then r single points ***)
  ABBREV_TAC `q = n DIV 16` THEN ABBREV_TAC `r = n MOD 16` THEN
  SUBGOAL_THEN `word_ushr (word n:int64) 4 = word q /\ word_and (word n:int64) (word 15) = word r`
    STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q"; "r"] THEN CONJ_TAC THENL
     [MATCH_MP_TAC WORD_USHR_DIV16; MATCH_MP_TAC WORD_AND_MOD16] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `16 * q + r = n /\ r < 16` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q"; "r"] THEN
    MP_TAC(SPEC `n:num` (MATCH_MP DIVISION (ARITH_RULE `~(16 = 0)`))) THEN ARITH_TAC;
    ALL_TAC] THEN
  VAL_INT64_TAC `q:num` THEN VAL_INT64_TAC `r:num` THEN
  ENSURES_SEQUENCE_TAC `pc + 0xb0` mid_cond THEN CONJ_TAC;;

(* Part A, no full block: the table is loaded and the vector loop is skipped. *)

let NEON_SKIP_TAC =
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC LATTICE_FWD_NEON_EXEC (1--10) THEN
  REWRITE_REGS_WITH_ASSUM_TAC `word_ushr (word n:int64) 4 = word 0` THEN
  ARM_STEPS_TAC LATTICE_FWD_NEON_EXEC (11--11) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; LT; LE_0] THEN ASM_MESON_TAC[];;

(* Part A, at least one full block: entry, body, back edge, exit of the loop. *)

let NEON_ENTRY_TAC =
  ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC LATTICE_FWD_NEON_EXEC (1--10) THEN
  REWRITE_REGS_WITH_ASSUM_TAC `word_ushr (word n:int64) 4 = word q` THEN
  ARM_STEPS_TAC LATTICE_FWD_NEON_EXEC (11--11) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; WORD_SUB_0; LT; LE_0] THEN ASM_MESON_TAC[];;

let NEON_BACK_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  UNDISCH_TAC `~(i = 0) ==> (read ZF s0 <=> i = q)` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ARM_STEPS_TAC LATTICE_FWD_NEON_EXEC (1--1) THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

let NEON_EXIT_TAC =
  ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC LATTICE_FWD_NEON_EXEC (1--1) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_SIMP_TAC[];;

let NEON_LOOP_TAC =
  ENSURES_WHILE_UP_TAC `q:num` `pc + 0x2c` `pc + 0xac` neon_inv THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [NEON_ENTRY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN NEON_BODY_TAC;
    NEON_BACK_TAC;
    NEON_EXIT_TAC];;

(* Part B, no leftover point: AND gives 0, CBZ goes straight to the RET. *)

let TAIL_SKIP_TAC =
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC LATTICE_FWD_NEON_EXEC (1--1) THEN
  REWRITE_REGS_WITH_ASSUM_TAC `word_and (word n:int64) (word 15) = word 0` THEN
  ARM_STEPS_TAC LATTICE_FWD_NEON_EXEC (2--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `n = 16 * q` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN ASM_MESON_TAC[];;

(* Part B, r leftover points: the scalar loop of the reference kernel. *)

let TAIL_ENTRY_TAC =
  ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC LATTICE_FWD_NEON_EXEC (1--1) THEN
  REWRITE_REGS_WITH_ASSUM_TAC `word_and (word n:int64) (word 15) = word r` THEN
  ARM_STEPS_TAC LATTICE_FWD_NEON_EXEC (2--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES; WORD_SUB_0] THEN
  REPEAT CONJ_TAC THEN CONV_TAC WORD_RULE;;

let TAIL_BACK_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  UNDISCH_TAC `~(i = 0) ==> (read ZF s0 <=> i = r)` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ARM_STEPS_TAC LATTICE_FWD_NEON_EXEC (1--1) THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

let TAIL_EXIT_TAC =
  ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC LATTICE_FWD_NEON_EXEC (1--1) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `n = 16 * q + r` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN ASM_MESON_TAC[];;

let TAIL_LOOP_TAC =
  ENSURES_WHILE_UP_TAC `r:num` `pc + 0xb8` `pc + 0xd8` tail_inv THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [TAIL_ENTRY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN TAIL_BODY_TAC;
    TAIL_BACK_TAC;
    TAIL_EXIT_TAC];;

let LATTICE_FWD_NEON_CORE = prove
 (core_stmt,
  NEON_PRELUDE_TAC THENL
   [ASM_CASES_TAC `q = 0` THENL [NEON_SKIP_TAC; NEON_LOOP_TAC];
    ASM_CASES_TAC `r = 0` THENL [TAIL_SKIP_TAC; TAIL_LOOP_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* The contract of the reference kernel: the table halves are whatever the    *)
(* table memory holds, and their lanes are the table bytes.                   *)
(* ------------------------------------------------------------------------- *)

let LATTICE_FWD_NEON_CORRECT = prove
 (`!pts n tbl (xs:num->byte) (ps:num->byte) (kick:num->byte) pc.
     n < 2 EXP 63 /\
     nonoverlapping (word pc,0xe0) (pts,2 * n) /\
     nonoverlapping (pts,2 * n) (tbl,256)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) lattice_fwd_neon_mc /\
               read PC s = word pc /\
               C_ARGUMENTS [pts; word n; tbl] s /\
               (!j. j < 256
                    ==> read (memory :> bytes8 (word_add tbl (word j))) s = kick j) /\
               (!i. i < n
                    ==> read (memory :> bytes8 (word_add pts (word (2 * i)))) s = xs i /\
                        read (memory :> bytes8 (word_add pts (word (2 * i + 1)))) s = ps i))
          (\s. read PC s = word (pc + 0xdc) /\
               (!i. i < n
                    ==> read (memory :> bytes8 (word_add pts (word (2 * i)))) s =
                          fwd_x kick (xs i) (ps i) /\
                        read (memory :> bytes8 (word_add pts (word (2 * i + 1)))) s =
                          fwd_p kick (xs i) (ps i)))
          (MAYCHANGE [PC; X0; X1; X3; X4; X5; X9] ,,
           MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q7; Q16; Q17; Q18; Q19; Q20; Q21; Q22; Q23;
                      Q24; Q25; Q26; Q27; Q28; Q29; Q30; Q31] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(pts,2 * n)])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ENSURES_PRECONDITION_TAC (parse_term (Printf.sprintf "\\s. ?%s. %s"
    (String.concat " " (map (fun k -> Printf.sprintf "(t%d:int128)" k) (0--15))) core_pre_str)) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:armstate` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC
      (map (fun k -> if k = 0 then `read (memory :> bytes128 tbl) (s:armstate)`
                     else parse_term (Printf.sprintf
                       "read (memory :> bytes128 (word_add (tbl:int64) (word %d))) (s:armstate)" (16*k))) (0--15)) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[BYTES128_LANE; WORD_ADD_ASSOC_CONSTS] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    REPEAT(MATCH_MP_TAC ENSURES_EXISTS_PRE THEN GEN_TAC THEN BETA_TAC) THEN
    MATCH_MP_TAC LATTICE_FWD_NEON_CORE THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Subroutine form: the statement of LATTICE_FWD_SUBROUTINE_CORRECT with the *)
(* code object replaced.                                                      *)
(* ------------------------------------------------------------------------- *)

let LATTICE_FWD_NEON_SUBROUTINE_CORRECT = prove
 (`!pts n tbl (xs:num->byte) (ps:num->byte) (kick:num->byte) pc returnaddress.
     n < 2 EXP 63 /\
     nonoverlapping (word pc,0xe0) (pts,2 * n) /\
     nonoverlapping (pts,2 * n) (tbl,256)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) lattice_fwd_neon_mc /\
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
  ARM_ADD_RETURN_NOSTACK_TAC LATTICE_FWD_NEON_EXEC LATTICE_FWD_NEON_CORRECT);;
