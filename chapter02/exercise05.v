Add LoadPath "/Users/danielle/projects/software-foundations/chapter02/".
Require Import basics.

Require Import Utf8.
Add LoadPath "/Users/danielle/projects/software-foundations/".
Require Import notations.

Theorem mult_S_1:
  ∀ n m: nat,
  m = S n -> m ⨉ (1 + n) = m * m.Proof.
  intros n m.
  intros H.  rewrite -> plus_1_l.
  rewrite <- H.
  reflexivity. 
  Qed.