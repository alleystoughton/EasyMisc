(*^ This theory proves the module-based law of total probability for
    finite ranges. See the module type `T`, the parameterized module
    `Rand(M)` and the lemma `total_prob`. It then specializes these
    definitions and the result to booleans (see theory
    `TotalBool`). ^*)

require import AllCore List StdOrder StdBigop Distr DBool.
import RealOrder Bigreal BRA.

(* auxiliary definitions and lemmas *)

module type RANGE = {
  proc main(m : int, n : int) : int
}.

module Range1 : RANGE = {
  proc main(m : int, n : int) : int = {
    var i : int;
    i <$ drange m n;
    return i;
  }
}.

module Range2 : RANGE = {
  proc main(m : int, n : int) : int = {
    var i : int;
    if (m = n - 1) {
      i <- m;
    }
    else {
      i <$ drange m n;
      if (i <> n - 1) {
        i <$ drange m (n - 1);
      }
    }
    return i;
  }
}.

lemma Range (m' n' : int) :
  m' < n' =>
  equiv
  [Range1.main ~ Range2.main :
   ={m, n} /\ m{1} = m' /\ n{1} = n' ==> ={res}].
proof.
move => lt_m'_n' /=.
bypr res{1} res{2} => // &1 &2 r [#] -> -> -> ->.
case (m' <= r < n') => [r_in | r_out].
have -> :
  Pr[Range1.main(m', n') @ &1 : res = r] = 1%r / (n' - m')%r.
  byphoare (_ : m = m' /\ n = n' /\ m' <= r < n' ==> _) => //.
  proc => /=.
  rnd (pred1 r).  
  auto; smt(drange1E).
have -> :
  Pr[Range2.main(m', n') @ &2 : res = r] = 1%r / (n' - m')%r.
  byphoare (_ : m = m' /\ n = n' /\ m' <= r < n' ==> _) => //.
  proc => /=.
  if; first auto; smt(invr1).
  case (r = n - 1).
  seq 1 :
    (i = n - 1)
    (1%r / (n' - m')%r)
    1%r
    ((n' - m' - 1)%r / (n' - m')%r)
    0%r
    (m = m' /\ n = n' /\ m' <= r < n' /\ m <> n - 1 /\ r = n - 1) => //.
  auto.
  rnd (pred1 (n - 1)); auto; smt(drange1E).
  rcondf 1; auto.
  rcondt 1; first auto.
  rnd pred0; auto; smt(mu0 supp_drange).
  (* r <> n - 1 *)
  seq 1 :
    (i = n - 1)
    (1%r / (n' - m')%r)
    0%r
    ((n' - m' - 1)%r / (n' - m')%r)
    (1%r / (n' - m' - 1)%r)
    (m = m' /\ n = n' /\ m' <= r < n' /\ m <> n - 1 /\ r <> n - 1) => //.
  auto.
  rcondf 1; first auto.
  hoare; auto; smt().
  rnd (predC (pred1 (n - 1))).
  auto => /> _ _ _ _.
  rewrite mu_not drange1E drangeE (_ : m' <= n' - 1 < n') 1:/#.
  rewrite count_predT size_range /#.
  rcondt 1; first auto.
  rnd (pred1 r); auto; smt(drange1E).
  smt(). smt().
have -> :
  Pr[Range1.main(m', n') @ &1 : res = r] = 0%r.
  byphoare (_ : m = m' /\ n = n' /\ ! (m' <= r < n') ==> _) => //.
  proc => /=.
  rnd pred0; auto; smt(mu0 supp_drange).
have -> // :
  Pr[Range2.main(m', n') @ &2 : res = r] = 0%r.
  byphoare (_ : m = m' /\ n = n' /\ ! (m' <= r < n') ==> _) => //.
  proc => /=; hoare.
  if; first auto; smt().
  seq 1 : (#pre /\ m <= i < n).
  auto; smt(supp_drange).
  if; auto; smt(supp_drange).
qed.

(*& A module with a `main` procedure taking in an integer and
    returning a boolean. &*)

module type T = {
  proc main(i : int) : bool
}.

(*& For a module `M` with module type `T`, `Rand(M).doit(m, n)`
    samples a uniformly random integer `i` that is `>=` `m` and `<`
    `n`, passes it to `M.main`, and returns the boolean `M.main`
    returns. &*)

module Rand(M : T) = {
  proc doit(m : int, n : int) : bool = {
    var b : bool; var i : int;
    i <$ drange m n;
    b <@ M.main(i);
    return b;
  }
}.

(* auxiliary definition and lemma *)

module Rand2(M : T) = {
  proc doit(m : int, n : int) : bool = {
    var b : bool; var i : int;
    if (m = n - 1) {
      i <- m;
    }
    else {
      i <$ drange m n;
      if (i <> n - 1) {
        i <$ drange m (n - 1);
      }
    }
    b <@ M.main(i);
    return b;
  }
}.

lemma Rand_eq (M <: T) (m' n' : int) &m :
  0 <= m' < n' =>
  Pr[Rand(M).doit(m', n') @ &m : res] =
  Pr[Rand2(M).doit(m', n') @ &m : res].
move => [ge0_m' lt_m'_n'].
byequiv => //; proc => /=.
proc change{1} [1 .. 2] :
  { i <@ Range1.main(m, n); b <@ M.main(i); }.
inline*; sim.
proc change{2} [1 .. 2] :
  { i <@ Range2.main(m, n); b <@ M.main(i); }.
inline*; sim.
call (_ : true).
exlim m{1}, m{2} => m_L m_R.
call (_ : ={m, n} /\ m{1} = m' /\ n{1} = n' ==> ={res}).
by apply Range.
auto.
qed.

(*& Law of total probability for finite ranges. &*)

lemma total_prob (M <: T) (m' n' : int) &m :
  0 <= m' < n' =>
  Pr[Rand(M).doit(m', n') @ &m : res] =
  bigi predT
  (fun i' => (1%r / (n' - m')%r) * Pr[M.main(i') @ &m : res])
  m' n'.
proof.
move => [ge0_m' lt_m'_n'].
rewrite (Rand_eq M) 1:/#.
have ind :
  forall n',
  0 <= n' => m' < n' =>
  Pr[Rand2(M).doit(m', n') @ &m : res] =
  bigi predT
  (fun i' => (1%r / (n' - m')%r) * Pr[M.main(i') @ &m : res])
  m' n'.
  elim => [/# | i' ge0_i' IH le_m'_i']; rewrite ltzS in le_m'_i'.
  rewrite big_int_recr //=.
  byphoare (_ : m = m' /\ n = i' + 1 /\ glob M = (glob M){m} ==> res) => //.
  proc => /=.
  if.
  sp.
  call (_ : i = m' /\ m' = i' /\ (glob M) = (glob M){m} ==> res).
  bypr => &hr [#] -> -> glob_eq.
  rewrite (_ : i' + 1 - i' = 1) 1:/# Num.Domain.invr1 /= big_geq //=.
  byequiv => //; sim.
  auto.
  (* m <> n - 1 *)
  seq 1 :
    (i = i')
    (1%r / (i' + 1 - m')%r)
    Pr[M.main(i') @ &m : res]
    ((i' - m')%r / (i' + 1 - m')%r)
    (bigi predT
     (fun i'' => (1%r / (i' - m')%r) * Pr[M.main(i'') @ &m : res])
     m' i')
    (glob M = (glob M){m} /\ m = m' /\ m <= i <= i' /\ n = i' + 1 /\ m' < i').
  auto; smt(supp_drange).
  rnd (pred1 i'); auto; smt(drange1E).
  rcondf 1; first auto.
  call (_ : i = i' /\ (glob M) = (glob M){m} ==> res).
  bypr => &hr eq_glob.
  byequiv => //; sim.
  auto.
  rnd (predC (pred1 i')); auto => /> ne_m'_i'.
  rewrite mu_not drange1E drangeE (_ : m' <= i' < i' + 1) 1:/#.
  rewrite count_predT size_range /#.
  rcondt 1; first auto.
  case  @[ambient] (m' < i') => [lt_m'_i' | nlt_m'_i']; last exfalso; smt().
  conseq (_ : _ ==> _ : = Pr[Rand(M).doit(m', i') @ &m : res]).
  move => /> &hr _ _ _.
  rewrite -IH // (Rand_eq M) /#.
  proc change [1 .. 2] : { b <@ Rand(M).doit(m, n - 1); }.
  conseq (_ : ={glob M, m, n} ==> _) => //.
  inline{2} 1; wp; sp.
  call (_ : true).
  rnd; auto.
  call (_ : (glob M) = (glob M){m} /\ m = m' /\ n = i' ==> res).
  bypr => &hr [#] glob_eq -> ->.
  byequiv => //; sim.
  auto.
  move => &hr [#] -> -> glob_eq /= ne_m'_i'.
  rewrite -RField.addrC; congr.
  rewrite RField.mulrC RField.mulrA mulr_sumr.
  congr.
  rewrite fun_ext => a /#.
by rewrite ind 1:(lez_trans m') // IntOrder.ltrW.
qed.

(*& Specialization of the range-based total probability definitions
    and lemma to the booleans. &*)

theory TotalBool.

(*& A module with a `main` procedure taking in a boolean and
    returning a boolean. &*)

module type T = {
  proc main(b : bool) : bool
}.

(*& For a module `M` with module type `T`, `Rand(M).doit()` samples a
    uniformly random boolean `b`, passes it to `M.main`, and returns
    the boolean `M.main` returns. &*)

module Rand(M : T) = {
  proc doit() : bool = {
    var b, b' : bool;
    b <$ DBool.dbool;
    b' <@ M.main(b);
    return b';
  }
}.

(* auxiliary definitions and lemmas *)

module Conv(M : T) : Top.T = {
  proc main(i : int) : bool = {
    var b : bool;
    b <@ M.main(i = 0);
    return b;
  }
}.

lemma Conv_equiv (M <: T) :
  equiv [Conv(M).main ~ M.main : ={glob M} /\ b{2} = (i{1} = 0) ==> ={res}].
proof. proc*; inline*; wp; sp; call (_ : true); auto. qed.

lemma Conv (M <: T) (i : int) &m :
  Pr[Conv(M).main(i) @ &m : res] = Pr[M.main(i = 0) @ &m : res].
proof. byequiv => //; by conseq (Conv_equiv M). qed.

lemma Rand_eq (M <: T) &m :
  Pr[Top.Rand(Conv(M)).doit(0, 2) @ &m : res] = Pr[Rand(M).doit() @ &m : res].
proof.
byequiv => //; proc.
seq 1 1 : (={glob M} /\ b{2} = (i{1} = 0)).
rnd (fun j => j = 0) (fun b' => if b' then 0 else 1).
auto; smt(dbool1E drange1E supp_drange).
call (Conv_equiv M); auto.
qed.

(*& Law of total probability for the booleans. &*)

lemma total_prob (M <: T) &m :
  Pr[Rand(M).doit() @ &m : res] =
  (1%r / 2%r) * Pr[M.main(true) @ &m : res] +
  (1%r / 2%r) * Pr[M.main(false) @ &m : res].
proof.
rewrite -(Rand_eq M) (Top.total_prob (Conv(M))) //= (_ : 2 = (0 + 1 + 1)) //.
by rewrite big_int_recr // big_int_recr // big_geq //= 2!(Conv M).
qed.

end TotalBool.
