(* Extraction into Haskell *)

Require Import Cantor Instances Class Util.
Require Import QArith Qcountable.
Require Import Extraction.
Require Import ExtrHaskellBasic ExtrHaskellZInteger ExtrHaskellNatInteger.


Definition nth_Qnz : nat -> Puncture 0%Q := from_nat.
Definition Qnz_to_Q : Puncture 0%Q -> Q := forward.

Definition nth_pair : nat -> Q * Q := from_nat.
Definition Q_times_Q_to_Q : Q * Q -> Q := forward.

Definition nth_rat : nat -> Q := from_nat.
Definition Q_plus_Q_to_Q : Q + Q -> Q := forward.

Extraction Language Haskell.

Extract Inductive sigT => "(,)" ["(,)"].

Extract Constant fst => "Prelude.fst".
Extract Constant snd => "Prelude.snd".
Extract Constant nat_dec_eq => "(\x y -> x Prelude.== y)".
Extract Constant pos_trich => "(\x y -> if x Prelude.== y then Prelude.Nothing else Prelude.Just (x Prelude.< y))".
Extract Constant Pos.sub => "(\x y -> x Prelude.- y)".
Extract Constant Pos.add => "(\x y -> x Prelude.+ y)".
Extract Constant Z.eq_dec => "(\x y -> x Prelude.== y)".
Extract Constant even => "Prelude.even".

Extraction "out.hs" nth_Qnz Qnz_to_Q nth_pair Q_times_Q_to_Q nth_rat Q_plus_Q_to_Q.