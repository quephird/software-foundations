Add LoadPath "/Users/danielle/projects/software-foundations/chapter02/".

Require Import my_compare.

Definition blt_nat (n m : nat) : bool := 
  negb (MyCompare.ble_nat m n).
Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.Proof. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. reflexivity. Qed.

