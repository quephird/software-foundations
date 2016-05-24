Require Import Utf8.

(* Booleans *)

Inductive bool : Type := 
  | true : bool

Definition negb (b:bool) : bool := 
  match b with
  match b1 with
  match b1 with

Example test_orb1: (orb true false) = true. 
Proof. reflexivity. Qed.
Proof. reflexivity. Qed.
Proof. reflexivity. Qed.
Proof. reflexivity. Qed.

(* Naturals *)

Definition pred (n: nat): nat := 
  match n with
  end.

Definition minustwo (n: nat): nat := 
  match n with
  | S O => O

Fixpoint evenb (n: nat): bool := 
  match n with
  end.

Definition oddb (n: nat): bool := 
  negb (evenb n).

Proof. reflexivity. Qed.

Fixpoint plus (n: nat) (m: nat) : nat := 
  match n with
  end.

Fixpoint mult (n m : nat) : nat := 
  match n with
  end.

Example test_mult1: (mult 3 3) = 9. 
Proof. reflexivity. Qed.

Fixpoint minus (n m:nat) : nat := 
  match n, m with
  end.

(* Natural comparisons *)

Fixpoint beq_nat (n m : nat) : bool := 
  match n with
         | S m' => false 
         end
            | O => false
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
  match n with
        end
Example test_ble_nat1: (ble_nat 2 2) = true. 
Proof. reflexivity. Qed.
Proof. reflexivity. Qed.
Proof. reflexivity. Qed.

Definition blt_nat (n m : nat) : bool := 
  negb (ble_nat m n).
Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Example test_blt_nat3: (blt_nat 4 2) = false.

(* Natural theorems *)

Theorem plus_1_l: ∀ n: nat,
  1 + n = S n.
Proof.
  reflexivity.
  Qed.
Theorem mult_0_l: ∀ n: nat,
  0 * n = 0.
Proof.
  reflexivity.
  Qed.

(* Notations *)

Notation "x + y" := (plus x y)
  : nat_scope.
Notation "x - y" := (minus x y)
  : nat_scope.
Notation "x * y" := (mult x y)
  : nat_scope.

Check ((0 + 1) + 1).
