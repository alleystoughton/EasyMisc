(* this script illustrates a progressive slowdown of EasyCrypt

   this phenomenon is known to happen with large amounts of pretty
   printing during proof development, but a self-contained script
   illustrating this isn't known (I believe)

   the script repeats an aborted lemma making use of simplification
   hints, over and over

   at first the lemma is proved instantly, later it takes longer,
   but there are points where nothing happens for minutes (garbage
   collection?), and then progress is again faster, but still
   slow; the trend is a progressive slowdown

   removing one of the simplification hints stops the progressive
   slowdown, so the problem isn't the repeated aborted lemmas *)

require import AllCore List FMap.
require BitWord.

clone import BitWord as BW with
  op n <- 256
proof *.
realize gt0_n. trivial. qed.

lemma mkword_inj (s1 s2 : bool list) :
  size s1 = 256 => size s2 = 256 => mkword s1 = mkword s2 <=> s1 = s2.
proof.
move => size_s1 size_s2; split => [| -> //].
by apply mkword_pinj.
qed.

lemma nseqnS ['a] (n : int) (x : 'a) :
  0 < n => nseq n x = x :: nseq (n - 1) x.
proof.
move => ngt0.
by rewrite (nseqS (n - 1)) 1:-ltzS.
qed.

hint simplify
  get_setE,
  nseq0,
  nseqnS,  (* taking this lemma out makes the script run quickly,
              with no progressive slowdown, but without solving
              the goal; thus a long series of aborted lemmas
              is not what causes the progressive slowdown *)
  mkword_inj.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
(* solves the goal, but we abort anyway *)
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

lemma foo (x1 x2 x3 x4 : word) :
  x1 = mkword (nseq 255 false ++ [true]) =>
  x2 = mkword (nseq 254 false ++ [true; false]) =>
  x3 = mkword (nseq 254 false ++ [true; true]) =>
  x4 = mkword (nseq 253 false ++ [true; false; false]) =>
  (empty.[x1 <- 1].[x2 <- 2].[x3 <- 3].[x4 <- 4]).[x3] = Some 3.
proof.
move => />.
abort.

