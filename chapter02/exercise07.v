Require Import Utf8.

Theorem identity_fn_applied_twice: 
  ∀ (f: bool -> bool), (∀ (x: bool), f x = x) ->
  ∀ (b: bool), f (f b) = b.Proof. 
  intros.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
  Qed.

