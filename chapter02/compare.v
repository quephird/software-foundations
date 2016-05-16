Module Compare.
  Fixpoint beq_nat (n m : nat) : bool := 
    match n with    | O => match m with           | O => true 
           | S m' => false 
           end    | S n' => match m with
              | O => false              | S m' => beq_nat n' m'              end
    end.

  Example test_beq_nat1: (beq_nat 0 0) = true. 
  Proof. reflexivity. Qed.
  Example test_beq_nat2: (beq_nat 2 0) = false. 
  Proof. reflexivity. Qed.
  Example test_beq_nat3: (beq_nat 0 2) = false. 
  Proof. reflexivity. Qed.
  Example test_beq_nat4: (beq_nat 4 4) = true. 
  Proof. reflexivity. Qed.
  Example test_beq_nat5: (beq_nat 3 5) = false. 
  Proof. reflexivity. Qed.
  Example test_beq_nat6: (beq_nat 1 6) = false. 
  Proof. reflexivity. Qed.

  Fixpoint ble_nat (n m : nat) : bool := 
    match n with      | O => true      | S n' =>          match m with          | O => false          | S m' => ble_nat n' m'
          end       end.
  Example test_ble_nat1: (ble_nat 2 2) = true. 
  Proof. reflexivity. Qed.  Example test_ble_nat2: (ble_nat 2 4) = true. 
  Proof. reflexivity. Qed.  Example test_ble_nat3: (ble_nat 4 2) = false. 
  Proof. reflexivity. Qed.

  Definition blt_nat (n m : nat) : bool := 
    negb (ble_nat m n).
  Example test_blt_nat1: (blt_nat 2 2) = false.
  Proof. reflexivity. Qed.
  Example test_blt_nat2: (blt_nat 2 4) = true.  Proof. reflexivity. Qed.
  Example test_blt_nat3: (blt_nat 4 2) = false.  Proof. reflexivity. Qed.
End Compare.

