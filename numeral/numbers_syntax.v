Load common_syntax.
Load common_z_syntax.

Definition int31_of_Z' z' :=
  match z' with
  | Z'0 | Z'pos _ => Some (phi_inv (Z_of_Z' z'))
  | Z'neg _ => None
  end.
Definition Z'_of_int31 n := Some (Z'_of_Z (phi n)).

Numeral Notation int31 int31_of_Z' Z'_of_int31 : int31_scope.

Definition bigN_of_Z' z' :=
  match z' with
  | Z'0 | Z'pos _ => Some (BigN.N_of_Z (Z_of_Z' z'))
  | Z'neg _ => None
  end.
Ltac Z'_of_bigN n := constr: (Z'_of_Z (BigN.to_Z n)).

Numeral Notation BigN.t bigN_of_Z' Z'_of_bigN : bigN_scope
  (printing
     BigN.N0 BigN.N1 BigN.N2 BigN.N3 BigN.N4 BigN.N5 BigN.N6
     BigN.Nn).
