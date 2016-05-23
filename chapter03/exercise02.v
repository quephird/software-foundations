Add LoadPath "/Users/danielle/projects/software-foundations/chapter03".
Require Import case.

Require Import Utf8.

Theorem plus_0_r: ∀ n: nat, n + 0 = n. 
Proof.
  induction n as [| n'].
    reflexivity.
    simpl.
    rewrite -> IHn'.
    reflexivity.
    Qed.

(* Exercises *)

Theorem mult_0_r: ∀ n: nat,
  n * 0 = 0.
  intros n.
  induction n as [| n'].
    reflexivity.
    simpl.
    rewrite -> IHn'.
    reflexivity.
  Qed.

Theorem plus_n_Sm: ∀ n m: nat,
  S(n + m) = n + (S m).
  intros n m.
  induction n as [| n'].
    reflexivity.
    simpl.
    rewrite -> IHn'.
    reflexivity.

Theorem plus_comm: ∀ n m: nat,
  n + m = m + n.
  intros n m.
  induction n as [| n'].
    rewrite -> plus_0_r.
  Case "n = S n’".
    simpl.
    rewrite -> IHn'.
    rewrite -> plus_n_Sm.
    reflexivity.
  Qed.

Theorem plus_assoc: ∀ n m p: nat,
  n + (m + p) = (n + m) + p.
  intros n m p.
  induction n as [| n'].
    reflexivity.
  Case "n = S n’".
    simpl.
    rewrite -> IHn'.
    reflexivity.
  Qed.