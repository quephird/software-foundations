Notation "x + y" := (plus x y)  (at level 50, left associativity)
  : nat_scope.
Notation "x - y" := (minus x y)  (at level 50, left associativity)
  : nat_scope.
Notation "x * y" := (mult x y)  (at level 40, left associativity) 
  : nat_scope.

Check ((0 + 1) + 1).
