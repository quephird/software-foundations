Add LoadPath "/Users/danielle/projects/software-foundations/chapter02/".
Require Import compare.

Require Import Utf8.

Theorem plus_1_neq_0: 
  ∀ n : nat, 
  beq_nat (n + 1) 0 = false.
  destruct n as [| n'].
  reflexivity.
  Qed.

Theorem negb_involutive : ∀ b : bool,
  negb (negb b) = b.
  reflexivity. Qed.