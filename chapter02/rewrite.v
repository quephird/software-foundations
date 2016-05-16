Require Import Utf8.

Theorem plus_id_example: ∀ n m: nat, n = m -> n + n = m + m.
(* Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity.
  Qed.
 *)
Proof.
  intros n m.
  intros H.
  rewrite <- H.
  reflexivity.
  Qed.




