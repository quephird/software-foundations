Require Import Utf8.

(* Booleans *)

Inductive bool : Type := 
  | true : bool  | false : bool.

Definition negb (b:bool) : bool := 
  match b with  | true => false  | false => true  end.Definition andb (b1:bool) (b2:bool) : bool := 
  match b1 with  | true => b2  | false => false  end.Definition orb (b1:bool) (b2:bool) : bool := 
  match b1 with  | true => true  | false => b2  end.

Example test_orb1: (orb true false) = true. 
Proof. reflexivity. Qed.Example test_orb2: (orb false false) = false. 
Proof. reflexivity. Qed.Example test_orb3: (orb false true) = true. 
Proof. reflexivity. Qed.Example test_orb4: (orb true true) = true. 
Proof. reflexivity. Qed.

(* Naturals *)

Definition pred (n: nat): nat := 
  match n with  | O => O  | S n' => n'
  end.

Definition minustwo (n: nat): nat := 
  match n with  | O => O 
  | S O => O  | S (S n') => n'  end.

Fixpoint evenb (n: nat): bool := 
  match n with  | O => true  | S O => false  | S (S n') => evenb n'
  end.

Definition oddb (n: nat): bool := 
  negb (evenb n).
Example test_oddb1: (oddb (S O)) = true.Proof. reflexivity. Qed.Example test_oddb2: (oddb (S (S (S (S O))))) = false. 
Proof. reflexivity. Qed.

Fixpoint plus (n: nat) (m: nat) : nat := 
  match n with  | O => m  | S n' => S (plus n' m)
  end.

Fixpoint mult (n m : nat) : nat := 
  match n with  | O => O  | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9. 
Proof. reflexivity. Qed.

Fixpoint minus (n m:nat) : nat := 
  match n, m with  | O, _ => O  | S _ , O => n  | S n', S m' => minus n' m'
  end.

(* Natural comparisons *)

Fixpoint beq_nat (n m : nat) : bool := 
  match n with  | O => match m with         | O => true 
         | S m' => false 
         end  | S n' => match m with
            | O => false            | S m' => beq_nat n' m'            end
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
  match n with    | O => true    | S n' =>        match m with        | O => false        | S m' => ble_nat n' m'
        end     end.
Example test_ble_nat1: (ble_nat 2 2) = true. 
Proof. reflexivity. Qed.Example test_ble_nat2: (ble_nat 2 4) = true. 
Proof. reflexivity. Qed.Example test_ble_nat3: (ble_nat 4 2) = false. 
Proof. reflexivity. Qed.

Definition blt_nat (n m : nat) : bool := 
  negb (ble_nat m n).
Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.Proof. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.Proof. reflexivity. Qed.

(* Natural theorems *)

Theorem plus_1_l: ∀ n: nat,
  1 + n = S n.
Proof.  intros n.
  reflexivity.
  Qed.
Theorem mult_0_l: ∀ n: nat,
  0 * n = 0.
Proof.  intros n.
  reflexivity.
  Qed.

(* Notations *)

Notation "x + y" := (plus x y)  (at level 50, left associativity)
  : nat_scope.
Notation "x - y" := (minus x y)  (at level 50, left associativity)
  : nat_scope.
Notation "x * y" := (mult x y)  (at level 40, left associativity) 
  : nat_scope.

Check ((0 + 1) + 1).
