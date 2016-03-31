(* common using type Z *)

Fixpoint pos_of_pos' p' :=
  match p' with
  | x'H => xH
  | x'O p' => xO (pos_of_pos' p')
  | x'I p' => xI (pos_of_pos' p')
  end.

Definition Z_of_Z' z' :=
  match z' with
  | Z'0 => Z0
  | Z'pos p' => Zpos (pos_of_pos' p')
  | Z'neg p' => Zneg (pos_of_pos' p')
  end.

Fixpoint pos'_of_pos p :=
  match p with
  | xH => x'H
  | xO p => x'O (pos'_of_pos p)
  | xI p => x'I (pos'_of_pos p)
  end.

Definition Z'_of_Z z :=
  match z with
  | Z0 => Z'0
  | Zpos p => Z'pos (pos'_of_pos p)
  | Zneg p => Z'neg (pos'_of_pos p)
  end.
