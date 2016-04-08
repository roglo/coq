Load common_syntax.
Load common_z_syntax.

Definition pos_of_Z' z' :=
  match z' with
  | Z'0 => None
  | Z'pos p' => Some (pos_of_pos' p')
  | Z'neg p' => None
  end.

Definition Z'_of_pos p := Some (Z'pos (pos'_of_pos p)).

Definition some_Z_of_Z' z' := Some (Z_of_Z' z').
Definition some_Z'_of_Z z := Some (Z'_of_Z z).

Definition N_of_Z' z' :=
  match z' with
  | Z'0 => Some N0
  | Z'pos p' => Some (Npos (pos_of_pos' p'))
  | Z'neg p' => None
  end.

Definition Z'_of_N n :=
  match n with
  | N0 => Some Z'0
  | Npos p => Some (Z'pos (pos'_of_pos p))
  end.

Numeral Notation positive pos_of_Z' Z'_of_pos : positive_scope.
Numeral Notation N N_of_Z' Z'_of_N : N_scope.
Numeral Notation Z some_Z_of_Z' some_Z'_of_Z : Z_scope.
