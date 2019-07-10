Require Import Cantor Instances Class.
Require Import QArith Qcountable.
Require Import Extraction.
Require Import ExtrHaskellBasic ExtrHaskellZInt ExtrHaskellNatInt.

Definition Q_to_Qnz : Q -> Qnz := forward.
Definition Qnz_to_Q : Qnz -> Q := back.

Extraction Language Haskell.

Extract Inductive sigT => "(,)" ["(,)"].

Extract Constant fst => "Prelude.fst".
Extract Constant snd => "Prelude.snd".
Extract Constant nat_dec_eq => "(\x y -> x Prelude.== y)".
Extract Constant pos_trich => "(\x y -> if x Prelude.== y then Prelude.Nothing else Prelude.Just (x Prelude.< y))".
Extract Constant Pos.sub => "(\x y -> x Prelude.- y)".
Extract Constant Pos.add => "(\x y -> x Prelude.+ y)".
Extract Constant Z.eq_dec => "(\x y -> x Prelude.== y)".

Extraction "out.hs" Q_to_Qnz Qnz_to_Q.
