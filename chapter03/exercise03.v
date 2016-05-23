Add LoadPath "/Users/danielle/projects/software-foundations/chapter03".
Require Import case.
Require Import exercise02.

Require Import Utf8.

Fixpoint double(n: nat) := 
  match n with
  end.

Lemma double_plus: ∀ n,
  double n = n + n.
Proof.
  intros n.
  induction n as [| n'].
    reflexivity.
    simpl.
    rewrite -> IHn'.
    simpl.
    rewrite -> plus_n_Sm.
    reflexivity.
  Qed.

