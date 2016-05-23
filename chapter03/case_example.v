Add LoadPath "/Users/danielle/projects/software-foundations/".
Require Import basics.

Add LoadPath "/Users/danielle/projects/software-foundations/chapter03".
Require Import case.

Require Import Utf8.

Theorem andb_true_elim1 : ∀ b c : bool, 
  andb b c = true -> b = true.Proof.  intros b c H. 
  destruct b.    Case "b = true". 
      reflexivity. 
    Case "b = false".
      rewrite <- H.
      reflexivity. 
  Qed.