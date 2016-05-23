Add LoadPath "/Users/danielle/projects/software-foundations/chapter03".
Require Import case.

Require Import Utf8.

Theorem plus_0_r: ∀ n: nat, n + 0 = n. 
Proof.  intros n.
  induction n as [| n'].  Case "n = 0".
    reflexivity.  Case "n = S n’".
    simpl.
    rewrite -> IHn'.
    reflexivity.
    Qed.

(* Exercises *)

Theorem mult_0_r: ∀ n: nat,
  n * 0 = 0.Proof.
  intros n.
  induction n as [| n'].  Case "n = 0".
    reflexivity.  Case "n = S n’".
    simpl.
    rewrite -> IHn'.
    reflexivity.
  Qed.

Theorem plus_n_Sm: ∀ n m: nat,
  S(n + m) = n + (S m).Proof.
  intros n m.
  induction n as [| n'].  Case "n = 0".
    reflexivity.  Case "n = S n’".
    simpl.
    rewrite -> IHn'.
    reflexivity.  Qed.

Theorem plus_comm: ∀ n m: nat,
  n + m = m + n.Proof.
  intros n m.
  induction n as [| n'].  Case "n = 0".
    rewrite -> plus_0_r.    reflexivity.
  Case "n = S n’".
    simpl.
    rewrite -> IHn'.
    rewrite -> plus_n_Sm.
    reflexivity.
  Qed.

Theorem plus_assoc: ∀ n m p: nat,
  n + (m + p) = (n + m) + p.Proof.
  intros n m p.
  induction n as [| n'].  Case "n = 0".
    reflexivity.
  Case "n = S n’".
    simpl.
    rewrite -> IHn'.
    reflexivity.
  Qed.
