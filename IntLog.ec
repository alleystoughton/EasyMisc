(* integer logarithm *)

require import AllCore StdOrder IntDiv.
import IntOrder.

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

(* integer logarithm *)

op int_log (b n : int) : int =
  choiceb
  (fun (k : int) => 0 <= k /\ b ^ k <= n < b ^ (k + 1))
  0.

lemma int_log (b n : int) :
  2 <= b => 1 <= n =>
  0 <= int_log b n /\ b ^ (int_log b n) <= n < b ^ (int_log b n + 1).
proof.
move => ge2_b ge1_n.
have // := choicebP (fun k => 0 <= k /\ b ^ k <= n < b ^ (k + 1)) 0 _.
  by rewrite /= exists_int_log.
qed.
