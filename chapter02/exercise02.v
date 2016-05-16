Fixpoint factorial (n:nat) : nat :=
  | O => S O
  | S n => mult (S n) (factorial n)
  end.

Proof. reflexivity. Qed.
Proof. reflexivity. Qed.