Require Import Utf8.

Theorem plus_id_exercise: 
   ∀ n m o: nat, 
  n = m -> m = o -> n + m = m + o.
  intros n m o.
  intros H.
  rewrite -> H.
  intros H'.
  rewrite -> H'.
  reflexivity.
  Qed.