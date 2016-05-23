Add LoadPath "/Users/danielle/projects/software-foundations/chapter02/".

Require Import simpl.

Require Import Utf8.

Theorem mult_S_1:
  ∀ n m: nat,
  m = S n -> m * (1 + n) = m * m.
  intros n m.
  intros H.
  rewrite <- H.
  reflexivity. 
  Qed.