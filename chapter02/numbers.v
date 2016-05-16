Module Playground1.
  Inductive nat : Type := 
    | O : nat

  Definition pred (n : nat) : nat := 
    match n with
    end.
End Playground1.

Definition minustwo (n : nat) : nat := 
  match n with
  | S O => O

Check (S (S (S (S O)))).

Check S.
Check minustwo.

Fixpoint evenb (n:nat) : bool := 
  match n with
  end.

Definition oddb (n:nat) : bool := 
  negb (evenb n).

Proof. reflexivity. Qed.

Module Playground2.
    match n with
    end.

Eval compute in (plus (S (S (S O))) (S (S O))).

Fixpoint mult (n m : nat) : nat := 
  match n with
  end.
Example test_mult1: (mult 3 3) = 9. 
Proof. reflexivity. Qed.

Fixpoint minus (n m:nat) : nat := 
  match n, m with
  end.

End Playground2.
