(* common not using type Z *)

Inductive positive' : Set :=
  | x'I : positive' -> positive'
  | x'O : positive' -> positive'
  | x'H : positive'.

Inductive Z' : Set :=
  | Z'0 : Z'
  | Z'pos : positive' -> Z'
  | Z'neg : positive' -> Z'.

Fixpoint pos'pred_double x :=
  match x with
  | x'I p => x'I (x'O p)
  | x'O p => x'I (pos'pred_double p)
  | x'H => x'H
  end.

Definition Z'succ_double x' :=
  match x' with
  | Z'0 => Z'pos x'H
  | Z'pos p' => Z'pos (x'I p')
  | Z'neg p' => Z'neg (pos'pred_double p')
  end.

Definition Z'double x' :=
  match x' with
  | Z'0 => Z'0
  | Z'pos p' => Z'pos (x'O p')
  | Z'neg p' => Z'neg (x'O p')
  end.
