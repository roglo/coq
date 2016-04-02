Load common_syntax.
Load common_z_syntax.

Definition int31_of_Z' z' := Some (phi_inv (Z_of_Z' z')).
Definition Z'_of_int31 n := Some (Z'_of_Z (phi n)).

Number Notation int31 int31_of_Z' Z'_of_int31 : int31_scope.

Definition bigN_of_Z' z' := Some (BigN.N_of_Z (Z_of_Z' z')).
Definition Z'_of_bigN n := Some (Z'_of_Z (BigN.to_Z n)).

Number Notation BigN.t' bigN_of_Z' Z'_of_bigN : bigN_scope.

bbb.

Definition bigN_of_Z' z' := Some (BigN.N_of_Z (Z_of_Z' z')).
Ltac Z'_of_bigN n := constr: (Z'_of_Z (BigN.to_Z n)).

Number Notation BigN.t bigN_of_Z' Z'_of_bigN : bigN_scope
  (printing
     BigN.N0 BigN.N1 BigN.N2 BigN.N3 BigN.N4 BigN.N5 BigN.N6
     BigN.Nn).


Fixpoint int31_of_pos' p' :=
  match p' with
  | x'I q' => Int31.twice_plus_one (int31_of_pos' q')
  | x'O q' => Int31.twice (int31_of_pos' q')
  | x'H => In
  end.

Definition int31_of_Z' z' :=
  match z' with
  | Z'0 => Some Int31.On
  | Z'pos p' => Some (int31_of_pos' p')
  | Z'neg p' => None
  end.

Definition Z'_of_int31 n :=
  Int31.recr Z' Z'0
    (fun (b : digits) (_ : int31) =>
     match b with
     | D0 => Z'double
     | D1 => Z'succ_double
     end) n.

Definition some_Z'_of_int31 n := Some (Z'_of_int31 n).

Number Notation int31 int31_of_Z' some_Z'_of_int31 : int31_scope.

Definition rank n :=
  let fix rk n pow2 :=
    match n with
    | O => pow2
    | S n1 => rk n1 (Z.mul pow2 pow2)
    end
  in
  rk n base.

Definition split_at n n' := Z.div_eucl n' (rank (pred n)).

Fixpoint pos'log2 (bi : positive') :=
  match bi with
  | x'H => O
  | x'I q => S (pos'log2 q)
  | x'O q => S (pos'log2 q)
  end.

Definition height (bi : positive') :=
  pos'log2 (pos'_of_pos (Pos.of_nat (Nat.double (pos'log2 bi / size)))).

Definition transport (A : Type) (B : A -> Type) (x y : A)
    (p : x = y) (q : B x) :=
  match p in _ = y return B y with
  | eq_refl => q
  end.

Fixpoint P (n : nat) : Type :=
  match n with
  | O => int31
  | S n1 => zn2z (P n1)
  end.

Definition P (n : nat) : Type :=
  match n with
  | O => int31
  | S O => zn2z int31
  | S (S O) => zn2z (zn2z int31)
  | S (S (S O)) => zn2z (zn2z (zn2z int31))
  | S (S (S (S O))) => zn2z (zn2z (zn2z (zn2z int31)))
  | S (S (S (S (S O)))) =>
      zn2z (zn2z (zn2z (zn2z (zn2z int31))))
  | S (S (S (S (S (S O))))) =>
      zn2z (zn2z (zn2z (zn2z (zn2z (zn2z int31)))))
  | _ =>
      word (zn2z (zn2z (zn2z (zn2z (zn2z (zn2z int31)))))) (S n)
  end.

(*
Definition proof_eq (x y : nat) : x = y.
Admitted.

Fixpoint word_of_pos_bigint hgt z :=
  match hgt with
  | O => existT P O (phi_inv z)
  | S n =>
      let '(h, l) := split_at hgt z in
      let wh := word_of_pos_bigint n h in
      let wl := word_of_pos_bigint n l in
      let p := proof_eq (projT1 wl) (projT1 wh) in
      existT P n
        (WW (projT2 wh)
          (transport nat
           (fun n => zn2z (P (projT1 wh)))
           (projT1 wl) (projT1 wh) p (projT2 wl)))
  end.
*)

Definition n_inlined := S (S (S (S (S (S (S O)))))).

Fixpoint word_of_pos_bigint hgt z :=
  match hgt with
  | O => BigN.N0 (phi_inv z)
  | S n =>
      let '(h, l) := split_at hgt z in
      let wh := word_of_pos_bigint n h in
      let wl := word_of_pos_bigint n l in
      match (wh, wl) with
      | (BigN.N0 wh1, BigN.N0 wl1) => BigN.N1 (WW wh1 wl1)
      | (BigN.N1 wh1, BigN.N1 wl1) => BigN.N2 (WW wh1 wl1)
      | (BigN.N2 wh1, BigN.N2 wl1) => BigN.N3 (WW wh1 wl1)
      | (BigN.N3 wh1, BigN.N3 wl1) => BigN.N4 (WW wh1 wl1)
      | (BigN.N4 wh1, BigN.N4 wl1) => BigN.N5 (WW wh1 wl1)
      | (BigN.N5 wh1, BigN.N5 wl1) => BigN.N6 (WW wh1 wl1)
      | (BigN.N6 wh1, BigN.N6 wl1) => BigN.Nn O (WW wh1 wl1)
      | (BigN.Nn O wh1, BigN.Nn O wl1) =>
          BigN.Nn (S O) (WW wh1 wl1)
      | (BigN.Nn (S O) wh1, BigN.Nn (S O) wl1) =>
          BigN.Nn (S (S O)) (WW wh1 wl1)
(*
      | (BigN.Nn u wh1, BigN.Nn v wl1) =>
           if Nat.eq_dec u v then BigN.Nn (S u) (WW wh1 wl1)
           else wh
*)
      | _ => wh
      end
  end.

Definition word_of_pos_bigint_0 z :=
  phi_inv z.

Definition word_of_pos_bigint_1 z :=
  let hgt := S O in
  let '(h, l) := split_at hgt z in
  let w1 := word_of_pos_bigint_0 h in
  let w2 := word_of_pos_bigint_0 l in
  WW w1 w2.

Definition word_of_pos_bigint_2 z :=
  let hgt := S (S O) in
  let '(h, l) := split_at hgt z in
  let w1 := word_of_pos_bigint_1 h in
  let w2 := word_of_pos_bigint_1 l in
  WW w1 w2.

Definition word_of_pos_bigint_3 z :=
  let hgt := S (S (S O)) in
  let '(h, l) := split_at hgt z in
  let w1 := word_of_pos_bigint_2 h in
  let w2 := word_of_pos_bigint_2 l in
  WW w1 w2.

Definition bigN_of_pos' (n' : positive') :=
  let h := height n' in
  let z := Z_of_Z' (Z'pos n') in
  match h with
  | O => BigN.N0 (word_of_pos_bigint_0 z)
  | S O => BigN.N1 (word_of_pos_bigint_1 z)
  | S (S O) => BigN.N2 (word_of_pos_bigint_2 z)
  | S (S (S O)) => BigN.N3 (word_of_pos_bigint_3 z)
  | _ => word_of_pos_bigint h z
  end.

Definition bigN_of_Z' z' :=
  match z' with
  | Z'0 => Some BigN.zero
  | Z'pos n' => Some (bigN_of_pos' n')
  | Z'neg n' => None
  end.

Ltac get_height rc :=
  match rc with
  | WW ?lft ?rght =>
      let hl := get_height lft in
      let hr := get_height rght in
      constr: (Z.succ (Z.max hl hr))
  | _ => constr: Z0
  end.

Definition Z'add x' y' := Z'_of_Z (Z.add (Z_of_Z' x') (Z_of_Z' y')).
Definition Z'mul x' y' := Z'_of_Z (Z.mul (Z_of_Z' x') (Z_of_Z' y')).

Ltac transform hght rc :=
  match rc with
  | W0 _ => constr: Z'0
  | WW ?lft ?rght =>
      let new_hght := constr: (Z.pred hght) in
      let x := transform new_hght lft in
      let y := transform new_hght rght in
      constr: (Z'add (Z'mul (Z'_of_Z (rank (Z.to_nat new_hght))) x) y)
  | _ => constr: (Z'_of_int31 rc)
  end.

Ltac Z'_of_word rc :=
  let hght := get_height rc in
  transform hght rc.

Ltac Z'_of_bigN n :=
  match n with
  | _ ?one_arg => Z'_of_word one_arg
  | _ _ ?second_arg => Z'_of_word second_arg
  end.

Number Notation BigN.t bigN_of_Z' Z'_of_bigN : bigN_scope
  (printing
     BigN.N0 BigN.N1 BigN.N2 BigN.N3 BigN.N4 BigN.N5 BigN.N6
     BigN.Nn).
