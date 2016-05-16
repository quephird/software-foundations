Require Import Utf8.

Theorem plus_O_n: ∀ n : nat, 0 + n = n. 
Proof.
  intros n. reflexivity. Qed.
Theorem plus_n_O: ∀ n, n + 0 = n.
Proof.  simpl. Abort.

Theorem plus_1_l: ∀ n: nat, 1 + n = S n.
Proof.  intros n. reflexivity. Qed.
Theorem mult_0_l: ∀ n: nat, 0 * n = 0.
Proof.  intros n. reflexivity. Qed.

