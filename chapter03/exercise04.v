Add LoadPath "/Users/danielle/projects/software-foundations/chapter03".
Require Import case.
Require Import exercise02.

Require Import Utf8.

Theorem plus_swap: ∀ n m p: nat,
  n + (m + p) = m + (n + p).Proof.
  intros n m p.
  assert (H: m + (n + p) = (m + n) + p).
    Case "Associative property".
    rewrite -> plus_assoc.
    reflexivity.
  rewrite -> H.
  assert (H': m + n = n + m).
    Case "Commutative property".
    rewrite -> plus_comm.
    reflexivity.
  rewrite -> H'.
  assert (H'': n + (m + p) = (n + m) + p).
    Case "Associative property".
    rewrite -> plus_assoc.
    reflexivity.
  rewrite -> H''.
  reflexivity.
  Qed.