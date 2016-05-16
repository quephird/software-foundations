Module Playground1.
  Inductive nat : Type := 
    | O : nat    | S : nat -> nat.

  Definition pred (n : nat) : nat := 
    match n with    | O => O    | S n' => n'
    end.
End Playground1.

Definition minustwo (n : nat) : nat := 
  match n with  | O => O 
  | S O => O  | S (S n') => n'  end.

Check (S (S (S (S O)))).Eval compute in (minustwo 4).

Check S.Check pred. 
Check minustwo.

Fixpoint evenb (n:nat) : bool := 
  match n with  | O => true  | S O => false  | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool := 
  negb (evenb n).
Example test_oddb1: (oddb (S O)) = true.Proof. reflexivity. Qed.Example test_oddb2: (oddb (S (S (S (S O))))) = false. 
Proof. reflexivity. Qed.

Module Playground2.  Fixpoint plus (n : nat) (m : nat) : nat := 
    match n with    | O => m    | S n' => S (plus n' m)
    end.

Eval compute in (plus (S (S (S O))) (S (S O))).

Fixpoint mult (n m : nat) : nat := 
  match n with  | O => O  | S n' => plus m (mult n' m)
  end.
Example test_mult1: (mult 3 3) = 9. 
Proof. reflexivity. Qed.

Fixpoint minus (n m:nat) : nat := 
  match n, m with  | O, _ => O  | S _ , O => n  | S n', S m' => minus n' m'
  end.

End Playground2.

