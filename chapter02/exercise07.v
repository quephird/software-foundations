Require Import Utf8.

Theorem identity_fn_applied_twice: 
  ∀ (f: bool -> bool),
  ∀ (b: bool), f (f b) = b.
  intros.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
  Qed.
