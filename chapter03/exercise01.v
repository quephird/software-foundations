Add LoadPath "/Users/danielle/projects/software-foundations/chapter03".
Require Import case.

Require Import Utf8.

Theorem andb_true_elim2 : ∀ b c : bool, 
  andb b c = true -> c = true.Proof.  intros b c H. 
  destruct c.    Case "c = true".
      reflexivity. 
    Case "c = false".
      rewrite <- H.
      destruct b.
      SCase "b = true".
        reflexivity.
      SCase "b = false".
        reflexivity.
  Qed.
