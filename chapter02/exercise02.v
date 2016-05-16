Fixpoint factorial (n:nat) : nat :=  match n with
  | O => S O
  | S n => mult (S n) (factorial n)
  end.
Example test_factorial1: (factorial 3) = 6. 
Proof. reflexivity. Qed.Example test_factorial2: (factorial 5) = (mult 10 12). 
Proof. reflexivity. Qed.