Add LoadPath "/Users/danielle/projects/software-foundations/chapter03".
Require Import case.
Add LoadPath "/Users/danielle/projects/software-foundations/chapter02".
Require Import basics.

Require Import Utf8.

Lemma negb_negb: ∀ b: bool, 
  b = negb (negb b).
Proof.
  intros b.
  destruct b.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
  Qed.

Theorem evenb_n__oddb_Sn: ∀ n: nat,
  evenb n = negb (evenb (S n)).
Proof.
  intros n.
  induction n as [|n'].
  Case "n = 0".
    simpl.
    reflexivity.
  Case "n = n'".
    simpl.
    destruct n' as [|n''].
    simpl.
    reflexivity.
    SCase "n' = n''".
      rewrite IHn'.
      simpl.
      rewrite <- negb_negb.
      reflexivity.
  Qed.
