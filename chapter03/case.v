Require Import Utf8.

Require String. Open Scope string_scope.
Ltac move_to_top x :=
  end.
Tactic Notation "assert_eq" ident(x) constr(v) := 
  let H := fresh in
Tactic Notation "Case_aux" ident(x) constr(name) := 
  first [
Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.