(* moved into coq library Nat.v *)

Load common_syntax.

Definition nat_of_Z' x :=
  match x with
  | Z'0 => Some O
  | Z'pos p =>
      let fix iter p a :=
        match p with
        | x'I p0 => a + iter p0 (a + a)
        | x'O p0 => iter p0 (a + a)
        | x'H => a
        end
      in
      Some (iter p (S O))
  | Z'neg p => None
  end.

Fixpoint pos'succ x := 
  match x with
  | x'I p => x'O (pos'succ p)
  | x'O p => x'I p
  | x'H => x'O x'H
  end.

Definition Z'succ x := 
  match x with
  | Z'0 => Z'pos x'H
  | Z'pos x' => Z'pos (pos'succ x')
  | Z'neg x' =>
      match x' with
      | x'I p => Z'neg (x'O p)
      | x'O p => Z'neg (pos'pred_double p)
      | x'H => Z'0
      end
  end.

Fixpoint Z'_of_nat_loop n :=
  match n with
  | O => Z'0
  | S p => Z'succ (Z'_of_nat_loop p)
  end.

Definition Z'_of_nat n := Some (Z'_of_nat_loop n).
Definition Z'_of_nat_noprint (n : nat) : option Z' := None.

Numeral Notation nat nat_of_Z' Z'_of_nat : nat_scope (warning after 5000).
