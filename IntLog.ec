(* integer logarithms - both rounding down (default) and rounding
   up *)

(* --------------------------------------------------------------------
 * Copyright (c) - 2021 - Boston University
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

prover [""].  (* no use of SMT provers *)

require import AllCore StdOrder IntDiv.
import IntOrder.

(* lemmas about exponentiation *)

lemma ge2_exp_le_equiv (d n m : int) :
  2 <= d => 0 <= n => 0 <= m =>
  n <= m <=> d ^ n <= d ^ m.
proof.
move => ge2_d ge0_n ge0_m.
split => [le_n_m | le_d2n_d2m].
by rewrite ler_weexpn2l 1:(ler_trans 2).
case (n <= m) => [// | lt_m_n]; rewrite -ltrNge in lt_m_n.
have le_d2m_d2n : d ^ m <= d ^ n.
  by rewrite ler_weexpn2l // 1:(ler_trans 2) // 1:ge0_m /= ltzW.
have eq_d2m_d2n : d ^ m = d ^ n by apply ler_asym.
have eq_m_n : m = n.
  rewrite (ieexprIn d _ _ m n) 1:(ltr_le_trans 1) // 1:(ler_trans 2) //.
  by rewrite gtr_eqF 1:(ltr_le_trans 2).
move : lt_m_n; by rewrite eq_m_n.
qed.

lemma ge2_exp_lt_equiv (d n m : int) :
  2 <= d => 0 <= n => 0 <= m =>
  n < m <=> d ^ n < d ^ m.
proof.
move => ge2_d ge0_n ge0_m.
split => [lt_n_m | lt_d2n_d2m].
rewrite ltz_def -ge2_exp_le_equiv // ltzW //=.
case (d ^ m = d ^ n) => [eq_d2m_d2n | //].
have eq_m_n : m = n.
  rewrite (ieexprIn d _ _ m n) 1:(ltr_le_trans 1) // 1:(ler_trans 2) //.
  by rewrite gtr_eqF 1:(ltr_le_trans 2).
move : lt_n_m; by rewrite eq_m_n.
rewrite ltz_def (ge2_exp_le_equiv d) // ltzW //=.
case (m = n) => [eq_m_n | //].
move : lt_d2n_d2m; by rewrite eq_m_n.
qed.

(* rounding down integer logarithm (default) *)

lemma exists_int_log (b n : int) :
  2 <= b => 1 <= n =>
  exists (k : int), 0 <= k /\ b ^ k <= n < b ^ (k + 1).
proof.
move => ge2_b ge1_n.
have gt1_b : 1 < b by rewrite ltzE.
have gt0_b : 0 < b by rewrite (ltr_trans 1).
have ge0_b : 0 <= b by rewrite ltrW.
have H :
  forall n,
  0 <= n => 1 <= n =>
  exists (k : int), 0 <= k /\ b ^ k <= n < b ^ (k + 1).
  apply sintind => i ge0_i IH /= ge1_i.
  case (i < b) => [lt_i_b | ge_b_i].
  exists 0; by rewrite /= expr0 ge1_i /= expr1.
  rewrite -lerNgt in ge_b_i.
  have [ge1_i_div_b i_div_b_lt_i] : 1 <= i %/ b < i.
    split => [| _].
    by rewrite lez_divRL 1:gt0_b.
    by rewrite ltz_divLR 1:gt0_b -divr1 mulzA 1:ltr_pmul2l ltzE.
  have /= [k [#] ge0_k b_exp_k_le_i_div_b i_div_b_lt_b_tim_b_exp_k]
       := IH (i %/ b) _ _.
    split; [by rewrite (lez_trans 1) | trivial].
    trivial.
  rewrite exprS // in i_div_b_lt_b_tim_b_exp_k.
  exists (k + 1).
  split; first by rewrite ler_paddl.
  rewrite exprS // mulzC exprS 1:ler_paddr // exprS //.
  split => [| _].
  rewrite (lez_trans ((i %/ b) * b)).
  by rewrite ler_wpmul2r 1:(lez_trans 2).
  by rewrite leq_trunc_div 1:(lez_trans 1).
  rewrite ltz_divLR // in i_div_b_lt_b_tim_b_exp_k.
  by rewrite mulzC.
by rewrite H (lez_trans 1).
qed.

lemma int_log_uniq (b n k1 k2 : int) :
  2 <= b =>
  0 <= k1 => b ^ k1 <= n => n < b ^ (k1 + 1) =>
  0 <= k2 => b ^ k2 <= n => n < b ^ (k2 + 1) =>
  k1 = k2.
proof.
move => ge2_b ge0_k1 b2k1_le_n n_lt_b2k1p1 ge0_k2 b2k2_le_n n_lt_b2k2p1.
have ge1_b : 1 <= b.
  by rewrite (lez_trans 2).
case (k1 = k2) => [// | /ltr_total [lt_k1_k2 | lt_k2_k1]].
rewrite ltzE in lt_k1_k2.
have b2k1p1_le_b2k2 : b ^ (k1 + 1) <= b ^ k2.
  by rewrite ler_weexpn2l // lt_k1_k2 /= addr_ge0.
have // : n < n.
  by rewrite (ltr_le_trans (b ^ (k1 + 1))) // (lez_trans (b ^ k2)).
rewrite ltzE in lt_k2_k1.
have b2k2p1_le_b2k1 : b ^ (k2 + 1) <= b ^ k1.
  by rewrite ler_weexpn2l // lt_k2_k1 /= addr_ge0.
have // : n < n.
  by rewrite (ltr_le_trans (b ^ (k2 + 1))) // (lez_trans (b ^ k1)).
qed.

(* integer logarithm (should not be applied when b <= 1 or n <= 0) *)

op nosmt int_log (b n : int) : int =
  choiceb
  (fun (k : int) => 0 <= k /\ b ^ k <= n < b ^ (k + 1))
  0.

lemma int_logP (b n : int) :
  2 <= b => 1 <= n =>
  0 <= int_log b n /\ b ^ (int_log b n) <= n < b ^ (int_log b n + 1).
proof.
move => ge2_b ge1_n.
have // := choicebP (fun k => 0 <= k /\ b ^ k <= n < b ^ (k + 1)) 0 _.
  by rewrite /= exists_int_log.
qed.

lemma int_log_ge0 (b n : int) :
  2 <= b => 1 <= n => 0 <= int_log b n.
proof.
move => ge2_b ge1_n.
have := int_logP b n _ _ => //.
qed.

lemma int_log_lb_le (b n : int) :
  2 <= b => 1 <= n => b ^ (int_log b n) <= n.
proof.
move => ge2_b ge1_n.
have := int_logP b n _ _ => //.
qed.

lemma int_log_ub_lt (b n : int) :
  2 <= b => 1 <= n => n < b ^ (int_log b n + 1).
proof.
move => ge2_b ge1_n.
have := int_logP b n _ _ => //.
qed.

lemma int_logPuniq (b n l : int) :
  2 <= b =>
  0 <= l => b ^ l <= n < b ^ (l + 1) =>
  l = int_log b n.
proof.
move => ge2_b ge0_n [b2l_le_n n_lt_b2lp1].
have ge1_n : 1 <= n.
  by rewrite (lez_trans (b ^ l)) // exprn_ege1 // (lez_trans 2).
have := int_logP b n _ _ => // [#] ge0_il b2il_le_n n_lt_b2ilp1.
by apply (int_log_uniq b n).
qed.

lemma int_log1_eq0 (b : int) :
  2 <= b => int_log b 1 = 0.
proof.
move => ge2_b.
by rewrite eq_sym (int_logPuniq b 1) // expr0 expr1 /= ltzE.
qed.

lemma int_log_le (b n m : int) :
  2 <= b => 1 <= n <= m =>
  int_log b n <= int_log b m.
proof.
move => ge2_b [ge1_n le_n_m].
have ge1_m : 1 <= m by rewrite (ler_trans n).
case (int_log b n <= int_log b m) => [// | il_m_plus1_le_il_n].
rewrite lerNgt /= ltzE in il_m_plus1_le_il_n.
have [#] _ b2il_n_le_n _ := int_logP b n _ _ => //.
have [#] _ _ m_lt_b2il_m_plus1 := int_logP b m _ _ => //.
have lt_m_n : m < n.
  rewrite (ltr_le_trans (b ^ (int_log b m + 1))) //.
  rewrite (ler_trans (b ^ (int_log b n))) //.
  rewrite ler_weexpn2l 1:(ler_trans 2) // il_m_plus1_le_il_n /=.
  by rewrite addz_ge0 1:int_log_ge0.
have // : n < n by rewrite (ler_lt_trans m).
qed.

lemma int_log_pow_b (b i : int) :
  2 <= b => 0 <= i =>
  int_log b (b ^ i) = i.
proof.
move => ge2_b ge0_i.
have ge1_b2i: 1 <= b ^ i by rewrite exprn_ege1 // (ler_trans 2).
have [#] ge0_il_b2i b2ilb2i_le_b2i b2i_lt_b2ilb2i_plus1
     := int_logP b (b ^ i) _ _ => //.
rewrite (ler_anti (int_log b (b ^ i)) i) //.
split => [| _].
rewrite (ge2_exp_le_equiv b (int_log b (b ^ i)) i) //.
move : b2i_lt_b2ilb2i_plus1.
rewrite -(ge2_exp_lt_equiv b i (int_log b (b ^ i) + 1)) //.
by rewrite addz_ge0 1:int_log_ge0.
by rewrite ltzS.
qed.

lemma int_log_distr_mul (b n m : int) :
  2 <= b => 1 <= n => 1 <= m =>
  int_log b n + int_log b m <=
  int_log b (n * m) <=
  int_log b n + int_log b m + 1.
proof.
move => ge2_b ge1_n ge1_m.
have ge0_b : 0 <= b by rewrite (ler_trans 2).
have ge0_n : 0 <= n by rewrite (ler_trans 1).
have ge0_m : 0 <= m by rewrite (ler_trans 1).
have [ge0_il_b_n [b2il_b_n_le_n n_lt_b2_il_b_n_plus1]]
     := int_logP b n _ _ => //.
have [ge0_il_b_m [b2il_b_m_le_m m_lt_b2_il_b_m_plus1]]
     := int_logP b m _ _ => //.
have nm_b2_lb_le : b ^ (int_log b n + int_log b m) <= n * m.
  rewrite exprD_nneg // ler_pmul // expr_ge0 ge0_b.
have nm_b2_ub_lt : n * m < b ^ (int_log b n + int_log b m + 2).
  have -> :
    (int_log b n + int_log b m + 2) =
    (int_log b n + 1) + (int_log b m + 1) by algebra.
  rewrite exprD_nneg 1:addr_ge0 // 1:addr_ge0 // ltr_pmul //.
case (n * m < b ^ (int_log b n + int_log b m + 1)) =>
  [nm_lt_b2_il_b_n_plus_il_b_m_plus1 | b2_il_b_n_plus_il_b_m_plus1_le_nm].
have il_b_nm_eq_il_b_n_plus_il_b_m :
  int_log b (n * m) = int_log b n + int_log b m.
  by rewrite (int_logPuniq b (n * m) (int_log b n + int_log b m)) //
             1:addr_ge0.
split => [| _].
by rewrite il_b_nm_eq_il_b_n_plus_il_b_m.
by rewrite -il_b_nm_eq_il_b_n_plus_il_b_m ler_addl.
rewrite -lerNgt in b2_il_b_n_plus_il_b_m_plus1_le_nm.
have il_b_nm_eq_il_b_n_plus_il_b_m_plus1 :
  int_log b (n * m) = int_log b n + int_log b m + 1.
  by rewrite (int_logPuniq b (n * m) (int_log b n + int_log b m + 1)) //
             addr_ge0 1:addr_ge0.
split => [| _].
by rewrite il_b_nm_eq_il_b_n_plus_il_b_m_plus1 ler_addl.
by rewrite -il_b_nm_eq_il_b_n_plus_il_b_m_plus1.
qed.

lemma int_log_distr_mul_lb (b n m : int) :
  2 <= b => 1 <= n => 1 <= m =>
  int_log b n + int_log b m <= int_log b (n * m).
proof.
move => ge2_b ge1_n ge1_m.
have := int_log_distr_mul b n m _ _ _ => //.
qed.

lemma int_log_distr_mul_ub (b n m : int) :
  2 <= b => 1 <= n => 1 <= m =>
  int_log b (n * m) <= int_log b n + int_log b m + 1.
proof.
move => ge2_b ge1_n ge1_m.
have := int_log_distr_mul b n m _ _ _ => //.
qed.

(* integer logarithm rounding up (should not be applied when b <= 1 or
   n <= 0) *)

op int_log_up (b n : int) : int =
  int_log b n + ((b ^ int_log b n = n) ? 0 : 1).

lemma int_log_int_log_up_le (b n : int) :
  int_log b n <= int_log_up b n.
proof.
rewrite /int_log_up.
case (b ^ int_log b n = n) => [// | _].
by rewrite ler_paddr.
qed.

lemma int_log_upP (b n : int) :
  2 <= b => 1 <= n =>
  (int_log_up b n = 0 /\ n = 1 \/
   1 <= int_log_up b n /\
   b ^ (int_log_up b n - 1) < n <= b ^ (int_log_up b n)).
proof.
move => ge2_b ge1_n.
rewrite /int_log_up.
have [#] ge0_il b2il_le_n n_lt_b2ilp1 := int_logP b n _ _ => //.
case (int_log_up b n = 0) => [eq0_ilu | ne0_ilu].
rewrite /int_log_up in eq0_ilu.
left.
rewrite eq0_ilu /=.
have eq_b2il_n : b ^ int_log b n = n.
  case (b ^ int_log b n = n) => [// | ne_b2il_n].
  move : eq0_ilu.
  by rewrite ne_b2il_n /= addz1_neq0.
have eq0_il : int_log b n = 0.
  move : eq0_ilu.
  by rewrite eq_b2il_n.
move : eq_b2il_n.
by rewrite eq0_il expr0.
rewrite /int_log_up in ne0_ilu.
right.
case (b ^ int_log b n = n) => [eq_b2il_n | ne_b2il_n].
move : ne0_ilu.
rewrite eq_b2il_n /= => ne0_il.
have ge1_il : 1 <= int_log b n.
  rewrite -lt0n // -lez_add1r // in ne0_il.
split => //.
rewrite eq_b2il_n /=.
have [p] [ge0_p eq_il_p_plus1]
     : exists p, 0 <= p /\ int_log b n = p + 1.
  exists (int_log b n - 1).
  by rewrite /= subr_ge0.
rewrite eq_il_p_plus1 /= -eq_b2il_n ltz_def.
split.
case (b ^ int_log b n = b ^ p) => [eq_b2il_b2p | //].
have eq_il_p : int_log b n = p.
  rewrite (ieexprIn b _ _ (int_log b n) p) // 1:(ltr_le_trans 2) //.
by rewrite eq_sym ltr_eqF 1:(ltr_le_trans 2).
move : eq_il_p_plus1; rewrite eq_il_p => eq_p_p_plus1.
have // : 0 = 1.
  have -> : 0 = p - p by trivial.
  have -> // : 1 = p - p by rewrite {1}eq_p_p_plus1 //; algebra.
rewrite ler_weexpn2l 1:(ler_trans 2) // ge0_p /=.
by rewrite eq_il_p_plus1 ler_addl.
split => [| /=].
by rewrite -subr_ge0.
split => [// | _].
by rewrite ltz_def eq_sym.
by rewrite ltrW.
qed.

lemma int_log_up_ge0 (b n : int) :
  2 <= b => 1 <= n => 0 <= int_log_up b n.
proof.
move => ge2_b ge1_n.
have [[->] | [ge1_ilu _]] := int_log_upP b n _ _ => //.
by rewrite (ler_trans 1).
qed.

lemma int_log_up_zero_iff (b n : int) :
  2 <= b => 1 <= n =>
  int_log_up b n = 0 <=> n = 1.
proof.
move => ge2_b ge1_n.
have [// | [#] ge1_il lt_b2ilu_min1_n _] := int_log_upP b n _ _ => //.
split => [eq0_ilu | eq1_n].
have // : 1 <= 0 by rewrite (ler_trans (int_log_up b n)) // eq0_ilu.
have : b ^ (int_log_up b n - 1) = 0.
  rewrite eqr_le.
  split => [| _].
  by rewrite -ltzS /= -{2}eq1_n.
  rewrite expr_ge0 (ler_trans 2) //.
rewrite expf_eq0 => [[_ eq0_b]].
have // : 2 <= 0 by rewrite (ler_trans b) // eq0_b.
qed.

lemma int_log_up_ge2_implies_ge1 (b n : int) :
  2 <= b => 2 <= n => 1 <= int_log_up b n.
proof.
move => ge2_b ge2_n.
have [[_ eq1_n] |] := int_log_upP b n _ _ => //.
  by rewrite (ler_trans 2).
have // : 2 <= 1 by rewrite -eq1_n.
qed.

lemma int_log_up_ge2_lb_lt (b n : int) :
  2 <= b => 2 <= n => b ^ (int_log_up b n - 1) < n.
proof.
move => ge2_b ge2_n.
have [[_ eq1_n] |] := int_log_upP b n _ _ => //.
  by rewrite (ler_trans 2).
have // : 2 <= 1 by rewrite -eq1_n.
qed.

lemma int_log_up_ge2_ub_le (b n : int) :
  2 <= b => 2 <= n => n <= b ^ (int_log_up b n).
proof.
move => ge2_b ge2_n.
have [[_ eq1_n] |] := int_log_upP b n _ _ => //.
  by rewrite (ler_trans 2).
have // : 2 <= 1 by rewrite -eq1_n.
qed.

lemma int_log_up_ge2_uniq (b n k1 k2 : int) :
  2 <= b => 2 <= n =>
  1 <= k1 => b ^ (k1 - 1) < n <= b ^ k1 =>
  1 <= k2 => b ^ (k2 - 1) < n <= b ^ k2 =>
  k1 = k2.
proof.
move => ge2_b ge2_n.
move => ge1_k1 [lt_b2k1min1_n le_n_b2k1].
move => ge1_k2 [lt_b2k2min1_n le_n_b2k2].
have ge1_b : 1 <= b.
  by rewrite (lez_trans 2).
have ge0_k1 : 0 <= k1 by rewrite (ler_trans 1).
have ge0_k2 : 0 <= k2 by rewrite (ler_trans 1).
case (k1 = k2) => [// | /ltr_total [lt_k1_k2 | lt_k2_k1]].
have le_k1_k2min1 : k1 <= k2 - 1 by rewrite -ltzS.
have b2k1_le_b2k2min1 : b ^ k1 <= b ^ (k2 - 1)
  by rewrite ler_weexpn2l.
have // : n < n.
  by rewrite (ler_lt_trans (b ^ k1)) //
             (ler_lt_trans (b ^ (k2 - 1))).
have le_k2_k1min1 : k2 <= k1 - 1 by rewrite -ltzS.
have b2k2_le_b2k1min1 : b ^ k2 <= b ^ (k1 - 1).
  by rewrite ler_weexpn2l.
have // : n < n.
  by rewrite (ler_lt_trans (b ^ k2)) //
             (ler_lt_trans (b ^ (k1 - 1))).
qed.

lemma int_log_up_ge2_Puniq (b n l : int) :
  2 <= b => 2 <= n =>
  1 <= l => b ^ (l - 1) < n <= b ^ l =>
  l = int_log_up b n.
proof.
move => ge2_b ge2_n ge1_l [ge1_b2l_min1 le_n_b2l].
have [[_ eq1_n] |] := int_log_upP b n _ _ => //.
  by rewrite (ler_trans 2).
have // : 2 <= 1 by rewrite -eq1_n.
pose l' := int_log_up b n.
move => [#] ge1_l' lt_b2l'min1_n le_n_b2l'.
by apply (int_log_up_ge2_uniq b n).
qed.

lemma int_log_up_le (b n m : int) :
  2 <= b => 1 <= n <= m =>
  int_log_up b n <= int_log_up b m.
proof.
move => ge2_b [ge1_n le_n_m].
have ge1_m : 1 <= m by rewrite (ler_trans n).
case (int_log_up b n <= int_log_up b m) => [// | ilu_m_plus1_le_ilu_n].
rewrite lerNgt /= ltzE in ilu_m_plus1_le_ilu_n.
have [[eq0_ilu_n _] | [#] _ b2ilu_n_min1_lt_n _] := int_log_upP b n _ _ => //.
move : ilu_m_plus1_le_ilu_n.
rewrite eq0_ilu_n => le0_ilu_m_plus1.
have // : 1 <= 0.
  by rewrite (ler_trans (int_log_up b m + 1)) // ler_addr int_log_up_ge0.
have [[eq0_ilu_m eq1_m] | [#] _ _ le_m_b2ilu_m] := int_log_upP b m _ _ => //.
have eq1_n : n = 1.
  move : le_n_m; rewrite eq1_m => le1_n.
  rewrite (ler_anti n 1) 1:le1_n //.
rewrite -(int_log_up_zero_iff b n) // in eq1_n.
have // : 1 <= 0.
  have -> : 1 = int_log_up b m + 1.
  by rewrite eq0_ilu_m.
  by rewrite (ler_trans (int_log_up b n)) // eq1_n.
have ilu_m_le_ilu_n_min1 : int_log_up b m <= int_log_up b n - 1.
  by rewrite -ler_subr_addr in ilu_m_plus1_le_ilu_n.
have lt_m_n : m < n.
  rewrite (ler_lt_trans (b ^ (int_log_up b m))) //.
  rewrite (ler_lt_trans (b ^ (int_log_up b n - 1))) //.
  rewrite -ge2_exp_le_equiv // 1:int_log_up_ge0 //.
  rewrite (ler_trans (int_log_up b m)) 1:int_log_up_ge0 //.
have // : n < n by rewrite (ler_lt_trans m).
qed.

lemma int_log_up_pow_b (b i : int) :
  2 <= b => 0 <= i =>
  int_log_up b (b ^ i) = i.
proof.
move => ge2_b ge0_i.
have ge1_b2i: 1 <= b ^ i by rewrite exprn_ege1 // (ler_trans 2).
have [[-> eq1_b2i ] | [#] ge1_ilu b2ilu_b2i_min1_lt_b2i b2i_le_b2_ilu_b2i]
     := int_log_upP b (b ^ i) _ _ => //.
rewrite (ler_anti 0 i) // 1:ge0_i /=.
case (i <= 0) => [// | gt0_i].
rewrite lerNgt /= in gt0_i.
have le_b_b2i : b <= b ^ i by rewrite ler_eexpr // (ler_trans 2).
rewrite eq1_b2i in le_b_b2i.
have // : 2 <= 1 by rewrite (ler_trans b).
rewrite (ler_anti (int_log_up b (b ^ i)) i) //.
split.
move : b2ilu_b2i_min1_lt_b2i.
by rewrite -(ge2_exp_lt_equiv b (int_log_up b (b ^ i) - 1) i) //
           1:ler_subr_addr // ltr_subl_addl addrC ltzS.
by rewrite (ge2_exp_le_equiv b i (int_log_up b (b ^ i))) // int_log_up_ge0.
qed.

lemma int_log_up_distr_mul (b n m : int) :
  2 <= b => 1 <= n => 1 <= m =>
  int_log_up b n + int_log_up b m - 1 <=
  int_log_up b (n * m) <=
  int_log_up b n + int_log_up b m.
proof.
move => ge2_b ge1_n ge1_m.
have ge0_b : 0 <= b by rewrite (ler_trans 2).
have ge1_b : 1 <= b by rewrite (ler_trans 2).
have ge0_n : 0 <= n by rewrite (ler_trans 1).
have ge0_m : 0 <= m by rewrite (ler_trans 1).
have [[eq0_ilu_b_n eq1_n] |
      [ge1_ilu_b_n [b2ilu_b_n_min1_lt_n n_le_b2_ilu_b_n]]]
     := int_log_upP b n _ _ => //.
have [[eq0_ilu_b_m eq1_m] |
      [ge1_ilu_b_m [b2ilu_b_m_min1_lt_m m_le_b2_ilu_b_m]]]
     := int_log_upP b m _ _ => //.
rewrite eq0_ilu_b_n eq0_ilu_b_m eq1_n eq1_m /=.
have -> // : int_log_up b 1 = 0 by rewrite int_log_up_zero_iff.
rewrite eq0_ilu_b_n eq1_n /= ler_subl_addl ler_addr //.
have [[eq0_ilu_b_m eq1_m] |
      [ge1_ilu_b_m [b2ilu_b_m_min1_lt_m m_le_b2_ilu_b_m]]]
     := int_log_upP b m _ _ => //.
rewrite eq0_ilu_b_m eq1_m /= ler_subl_addl ler_addr //.
have nm_b2_lb_lt : b ^ (int_log_up b n + int_log_up b m - 2) < n * m.
  have -> :
    int_log_up b n + int_log_up b m - 2 =
    (int_log_up b n - 1) + (int_log_up b m - 1) by algebra.
  rewrite exprD_nneg 1:ler_subr_addr // 1:ler_subr_addr //.
  by rewrite ltr_pmul 1:expr_ge0 // 1:expr_ge0.
have nm_b2_ub_le : n * m <= b ^ (int_log_up b n + int_log_up b m).
  by rewrite exprD_nneg // 1:(ler_trans 1) // 1:(ler_trans 1) // ler_pmul.
case (b ^ (int_log_up b n + int_log_up b m - 1) < n * m) =>
  [b2_ilu_b_n_plus_ilu_b_m_min1_lt_nm | nm_le_b2_ilu_b_n_plus_ilu_b_m_min1].
have ilu_b_nm_eq_ilu_b_n_plus_ilu_b_m :
  int_log_up b (n * m) = int_log_up b n + int_log_up b m.
  rewrite (int_log_up_ge2_Puniq b (n * m)
          (int_log_up b n + int_log_up b m)) //.
  have -> : 2 = 1 + 1 by trivial.
  rewrite lez_add1r
          (ler_lt_trans (b ^ (int_log_up b n + int_log_up b m - 2)))
          1:exprn_ege1 //.
  have -> :
    int_log_up b n + int_log_up b m - 2 =
    (int_log_up b n - 1) + (int_log_up b m - 1) by algebra.
  rewrite addr_ge0 ler_subr_addl //.
  by rewrite (ler_trans (1 + 1)) // ler_add.
rewrite ilu_b_nm_eq_ilu_b_n_plus_ilu_b_m.
split => [| //].
by rewrite ler_subl_addr ler_addl.
rewrite -lerNgt in nm_le_b2_ilu_b_n_plus_ilu_b_m_min1.
have ilu_b_nm_eq_ilu_b_n_plus_ilu_b_m_min1 :
  int_log_up b (n * m) = int_log_up b n + int_log_up b m - 1.
  rewrite (int_log_up_ge2_Puniq b (n * m)
           (int_log_up b n + int_log_up b m - 1)) //.
  have -> : 2 = 1 + 1 by trivial.
  rewrite lez_add1r
          (ler_lt_trans (b ^ (int_log_up b n + int_log_up b m - 2))) //
          exprn_ege1 //.
  have -> :
    int_log_up b n + int_log_up b m - 2 =
    (int_log_up b n - 1) + (int_log_up b m - 1) by algebra.
  rewrite addr_ge0 ler_subr_addl //.
  rewrite ler_subr_addl /=.
  have -> : 2 = 1 + 1 by trivial.
  by rewrite ler_add.
split => [| _].
by rewrite ilu_b_nm_eq_ilu_b_n_plus_ilu_b_m_min1.
rewrite ilu_b_nm_eq_ilu_b_n_plus_ilu_b_m_min1.
by rewrite ler_subl_addr ler_addl.
qed.

lemma int_log_up_distr_mul_lb (b n m : int) :
  2 <= b => 1 <= n => 1 <= m =>
  int_log_up b n + int_log_up b m - 1 <= int_log_up b (n * m).
proof.
move => ge2_b ge1_n ge1_m.
have := int_log_up_distr_mul b n m _ _ _ => //.
qed.

lemma int_log_up_distr_mul_ub (b n m : int) :
  2 <= b => 1 <= n => 1 <= m =>
  int_log_up b (n * m) <= int_log_up b n + int_log_up b m.
proof.
move => ge2_b ge1_n ge1_m.
have := int_log_up_distr_mul b n m _ _ _ => //.
qed.
