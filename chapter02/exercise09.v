Inductive bin : Type := 
  | Z : bin  | T : bin -> bin
  | TPO: bin -> bin.

Check Z.
Check T Z.
Check TPO Z.
Check T (TPO Z).
Check TPO (T (TPO Z)).

Definition incr (n : bin) : bin := 
  match n with  | Z => TPO Z 
  | T n' => TPO n'  | TPO n' => T (match n' with
                 | Z => TPO Z
                 | TPO n'' => T (T n'')
                 | T n'' => TPO n''
                 end)  end.

Check incr Z.
Check incr (TPO Z).
Check incr (T (TPO Z)).

Fixpoint bin_to_nat (n: bin): nat := 
  match n with  | Z => O
  | T n' => mult (S (S O)) (bin_to_nat n')
  | TPO n' => S (mult (S (S O)) (bin_to_nat n'))  end.

Check bin_to_nat Z.
Check bin_to_nat (TPO Z).
Check bin_to_nat (T (TPO Z)).
Check bin_to_nat (TPO (T (T (T (TPO Z))))).

Example bin_0_equals_nat_0: bin_to_nat Z = 0.
Proof. reflexivity. Qed.
Example bin_1_equals_nat_1: bin_to_nat (TPO Z) = 1.
Proof. reflexivity. Qed.
Example bin_2_equals_nat_2: bin_to_nat (T (TPO Z)) = 2.
Proof. reflexivity. Qed.
Example bin_9_equals_nat_9:  bin_to_nat (TPO (T (T (TPO Z)))) = 9.
Proof. reflexivity. Qed.

Example test_bin_incr1: bin_to_nat (incr Z) = 1.
Proof. reflexivity. Qed.
Example test_bin_incr2: bin_to_nat (incr (TPO Z)) = 2.
Proof. reflexivity. Qed.
Example test_bin_incr6: bin_to_nat (incr (TPO (T (TPO Z)))) = 6.
Proof. reflexivity. Qed.
Example test_bin_incr9: bin_to_nat (incr (T (T (T (TPO Z))))) = 9.
Proof. reflexivity. Qed.





