Add LoadPath "/Users/danielle/projects/software-foundations/chapter02/".
Require Import compare.

Require Import Utf8.

Theorem plus_1_neq_0: 
  ∀ n : nat, 
  beq_nat 0 (n + 1) = false.Proof.  intros n.
  destruct n as [| n'].  reflexivity.
  reflexivity.
  Qed.
