Inductive day : Type := 
  | monday : day
  | friday : day
  | sunday : day.

Definition next_weekday (d:day) : day := match d with
  | thursday => friday
  end.

Eval compute in (next_weekday friday).

Example test next_weekday:
