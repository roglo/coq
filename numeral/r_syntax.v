Load common_syntax.

Fixpoint R_of_pos' (p' : positive') : R :=
  match p' with
  | x'H => R1
  | x'O x'H => Rplus R1 R1
  | x'I x'H => Rplus R1 (Rplus R1 R1)
  | x'O q => Rmult (Rplus R1 R1) (R_of_pos' q)
  | x'I q => Rplus R1 (Rmult (Rplus R1 R1) (R_of_pos' q))
  end.

Definition R_of_Z' (z' : Z') : option R :=
  match z' with
  | Z'0 => Some R0
  | Z'pos p' => Some (R_of_pos' p')
  | Z'neg p' => Some (Ropp (R_of_pos' p'))
  end.

Ltac Z'_of_posR2 r :=
  match r with
  | Rplus R1 R1 => constr: (Z'pos (x'O x'H))
  | Rplus R1 (Rplus R1 R1) => constr: (Z'pos (x'I x'H))
  | Rmult ?a ?b =>
      match Z'_of_posR2 a with
      | Z'pos (x'O x'H) => let b' := Z'_of_posR2 b in constr: (Z'double b')
      end
  | Rplus R1 (Rmult ?a ?b) =>
      match Z'_of_posR2 a with
      | Z'pos (x'O x'H) => let b' := Z'_of_posR2 b in constr: (Z'succ_double b')
      end
  end.

Ltac Z'_of_posR r :=
  match r with
  | R0 => constr: Z'0
  | R1 => constr: (Z'pos x'H)
  | ?r => Z'_of_posR2 r
  end.

Definition Z'opp z' :=
  match z' with
  | Z'0 => Z'0
  | Z'pos q => Z'neg q
  | Z'neg q => Z'pos q
  end.

Ltac Z'_of_R r :=
  match r with
  | Ropp ?s =>
      match Z'_of_posR s with
      | Z'0 => fail
      | ?z => constr: (Z'opp z)
      end
  | _ =>
      Z'_of_posR r
  end.

Numeral Notation R R_of_Z' Z'_of_R : R_scope (printing Ropp R0 Rplus Rmult R1).
