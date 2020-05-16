(* Proof that Q is a countable setoid *)

Require Import Lia SetoidClass BinPos Recdef Util Arith.

Record Qpos := mkQp { Qnump : positive; Qdenp : positive }.

Instance Qpos_Setoid : Setoid Qpos :=
  {|
    equiv := fun p q => (Qnump p * Qdenp q = Qnump q * Qdenp p)%positive
  |}.
Proof.
  split.
  - intros []; simpl.
    lia.
  - intros [] []; simpl.
    lia.
  - intros [a b] [c d] [e f]; simpl.
    intros.
    apply (Pos.mul_cancel_l _ _ d).
    rewrite (Pos.mul_assoc d a f).
    rewrite (Pos.mul_comm d a).
    rewrite H.
    rewrite <- (Pos.mul_assoc c b f).
    rewrite (Pos.mul_comm b f).
    rewrite (Pos.mul_assoc c f b).
    rewrite H0; lia.
Defined.

Inductive BinPath :=
  | Empty : BinPath
  | Left : BinPath -> BinPath
  | Right : BinPath -> BinPath.

Definition qp_left : Qpos -> Qpos :=
  fun q => match q with
           | mkQp a b => mkQp a (a + b)
           end.

Definition qp_right : Qpos -> Qpos :=
  fun q => match q with
           | mkQp a b => mkQp (a + b) b
           end.

Lemma qp_left_morph : forall q q', q == q' -> qp_left q == qp_left q'.
Proof.
  intros [] [] G.
  simpl in G.
  unfold qp_left; simpl.
  lia.
Qed.

Lemma qp_right_morph : forall q q', q == q' -> qp_right q == qp_right q'.
Proof.
  intros [] [] G.
  simpl in G.
  unfold qp_right; simpl.
  lia.
Qed.

Fixpoint BinPath_to_Qpos(x : BinPath) : Qpos :=
  match x with
  | Empty => mkQp 1 1
  | Left p => qp_left (BinPath_to_Qpos p)
  | Right p => qp_right (BinPath_to_Qpos p)
  end.

Lemma pos_trich : forall x y : positive,
  {(x < y)%positive} + {(y < x)%positive} + {x = y}.
Proof.
  induction x; destruct y;
  try destruct (IHx y) as [[|]|].
  - left; left; lia.
  - left; right; lia.
  - right; lia.
  - left; left; lia.
  - left; right; lia.
  - left; right; lia.
  - left; right; lia.
  - left; left; lia.
  - left; right; lia.
  - left; left; lia.
  - left; left; lia.
  - left; right; lia.
  - right; lia.
  - left; right; lia.
  - left; left; lia.
  - left; left; lia.
  - right; lia.
Defined.

Lemma pos_trich2 : forall x y : positive,
  {_ : unit & x = y} + {z : positive & (x + z = y)%positive} + {z : positive & (y + z = x)%positive}.
Proof.
  intros.
  destruct (pos_trich x y) as [[|]|].
  - left; right; exists (y-x)%positive; lia.
  - right; exists (x-y)%positive; lia.
  - left; left; exists tt; auto.
Defined.

Lemma pos_trich2_inl_inl : forall x y p, x == y ->
  pos_trich2 (Qnump x) (Qdenp x) = inl (inl p) -> exists q, pos_trich2 (Qnump y) (Qdenp y) = inl (inl q).
Proof.
  intros.
  simpl in H.
  destruct (pos_trich2 (Qnump y) (Qdenp y)) as [[|]|].
  - exists s; reflexivity.
  - destruct s as [z Hz].
    clear H0.
    destruct p as [_ G].
    rewrite <- Hz in H.
    rewrite G in H.
    rewrite Pos.mul_add_distr_l in H.
    rewrite (Pos.mul_comm (Qdenp x)) in H.
    absurd (Qnump y * Qdenp x < Qnump y * Qdenp x)%positive.
    + lia.
    + rewrite <- H at 2.
      apply Pos.lt_add_diag_r.
  - destruct s as [z Hz].
    clear H0.
    destruct p as [_ G].
    rewrite G in H.
    rewrite <- Hz in H.
    rewrite Pos.mul_add_distr_r in H.
    rewrite (Pos.mul_comm (Qdenp x)) in H.
    absurd (Qdenp y * Qdenp x < Qdenp y * Qdenp x)%positive.
    + lia.
    + rewrite H at 2.
      apply Pos.lt_add_diag_r.
Qed.

Lemma pos_trich2_inl_inr : forall x y p, x == y ->
  pos_trich2 (Qnump x) (Qdenp x) = inl (inr p) -> exists q, pos_trich2 (Qnump y) (Qdenp y) = inl (inr q).
Proof.
  intros.
  simpl in H.
  destruct p.
  clear H0.
  destruct (pos_trich2 (Qnump y) (Qdenp y)) as [[|]|].
  - destruct s.
    rewrite e0 in H.
    rewrite <- e in H.
    rewrite Pos.mul_add_distr_l in H.
    absurd (Qnump x * Qdenp y < Qnump x * Qdenp y)%positive.
    + lia.
    + rewrite H at 2.
      rewrite (Pos.mul_comm (Qdenp y)).
      apply Pos.lt_add_diag_r.
  - exists s; auto.
  - destruct s.
    rewrite <- e0 in H.
    rewrite <- e in H.
    rewrite Pos.mul_add_distr_r in H.
    absurd (Qnump x * Qdenp y < Qnump x * Qdenp y)%positive.
    + lia.
    + rewrite H at 2.
      rewrite (Pos.mul_comm (Qdenp y)).
      rewrite Pos.mul_add_distr_r.
      rewrite <- Pos.add_assoc.
      apply Pos.lt_add_diag_r.
Qed.

Lemma pos_trich2_inr : forall x y p, x == y ->
  pos_trich2 (Qnump x) (Qdenp x) = (inr p) -> exists q, pos_trich2 (Qnump y) (Qdenp y) = (inr q).
Proof.
  intros.
  simpl in H.
  destruct p.
  clear H0.
  destruct (pos_trich2 (Qnump y) (Qdenp y)) as [[|]|].
  - destruct s.
    rewrite e0 in H.
    rewrite <- e in H.
    rewrite Pos.mul_add_distr_r in H.
    absurd (Qdenp x * Qdenp y < Qdenp x * Qdenp y)%positive.
    + lia.
    + rewrite (Pos.mul_comm (Qdenp y)) in H.
      rewrite <- H at 2.
      apply Pos.lt_add_diag_r.
  - destruct s.
    rewrite <- e0 in H.
    rewrite <- e in H.
    rewrite Pos.mul_add_distr_r in H.
    absurd (Qdenp x * Qnump y < Qdenp x * Qnump y)%positive.
    + lia.
    + rewrite (Pos.mul_comm (Qnump y)) in H.
      rewrite <- H at 2.
      rewrite Pos.mul_add_distr_l.
      rewrite <- Pos.add_assoc.
      apply Pos.lt_add_diag_r.
  - exists s; auto.
Qed.

Function Qpos_to_BinPath(q : Qpos){measure (fun x => Pos.to_nat (Qnump x + Qdenp x))%positive} : BinPath :=
  match pos_trich2 (Qnump q) (Qdenp q) with
  | inl (inl _) => Empty
  | inl (inr (existT _ z _)) => Left (Qpos_to_BinPath (mkQp (Qnump q) z))
  | inr (existT _ z _) => Right (Qpos_to_BinPath (mkQp z (Qdenp q)))
  end.
Proof.
  - intros.
    apply Pnat.Pos2Nat.inj_lt.
    simpl.
    rewrite e.
    rewrite Pos.add_comm.
    apply Pos.lt_add_diag_r.
  - intros.
    apply Pnat.Pos2Nat.inj_lt.
    simpl.
    rewrite (Pos.add_comm z).
    rewrite e.
    apply Pos.lt_add_diag_r.
Defined.

Lemma Qpos_to_BinPath_morph : forall q q', q == q' ->
  Qpos_to_BinPath q = Qpos_to_BinPath q'.
Proof.
  intro q; apply Qpos_to_BinPath_ind; intros;
  rewrite Qpos_to_BinPath_equation.
  - destruct (pos_trich2_inl_inl _ _ _ H e).
    rewrite H0; auto.
  - rewrite (Qpos_to_BinPath_equation q').
    destruct (pos_trich2_inl_inr _ _ _  H0 e).
    rewrite H1.
    destruct x.
    rewrite <- H.
    + f_equal.
      simpl.
      rewrite Qpos_to_BinPath_equation.
      simpl.
      reflexivity.
    + simpl in H0.
      rewrite <- _x in H0.
      rewrite <- e0 in H0.
      simpl.
      lia.
  - rewrite (Qpos_to_BinPath_equation q').
    destruct (pos_trich2_inr _ _ _ H0 e).
    rewrite H1.
    destruct x.
    rewrite <- H.
    + f_equal.
      simpl.
      rewrite Qpos_to_BinPath_equation.
      simpl.
      reflexivity.
    + simpl in H0.
      rewrite <- e0 in H0.
      rewrite <- _x in H0.
      simpl.
      lia.
Qed.

Lemma Qpos_to_from : forall q, BinPath_to_Qpos (Qpos_to_BinPath q) == q.
Proof.
  intro.
  apply Qpos_to_BinPath_ind.
  - intros.
    simpl.
    destruct _x.
    rewrite e0.
    lia.
 - intros.
    simpl.
    pose ((BinPath_to_Qpos
      (Qpos_to_BinPath {| Qnump := Qnump q0; Qdenp := z |}))) as x.
    fold x.
    fold x in H.
    unfold qp_left.
    destruct x.
    simpl.
    simpl in H.
    rewrite <- _x.
    rewrite Pos.mul_add_distr_l.
    rewrite H.
    lia.
  - intros.
    simpl.
    pose (BinPath_to_Qpos (Qpos_to_BinPath {| Qnump := z; Qdenp := Qdenp q0 |})) as x.
    fold x.
    fold x in H.
    unfold qp_right.
    destruct x.
    simpl.
    simpl in H.
    rewrite <- _x.
    rewrite Pos.mul_add_distr_r.
    rewrite H.
    lia.
Qed.

Lemma qp_left_Left : forall x, Qpos_to_BinPath (qp_left x) = Left
  (Qpos_to_BinPath x).
Proof.
  intros.
  unfold qp_left.
  destruct x.
  rewrite Qpos_to_BinPath_equation.
  simpl.
  destruct pos_trich2 as [[|]|].
  - destruct s.
    lia.
  - destruct s.
    assert (x = Qdenp0) by lia.
    rewrite H.
    auto.
  - destruct s.
    lia.
Qed.

Lemma qp_right_Right : forall x, Qpos_to_BinPath (qp_right x) = Right
  (Qpos_to_BinPath x).
Proof.
  intros.
  unfold qp_right.
  destruct x.
  rewrite Qpos_to_BinPath_equation.
  simpl.
  destruct pos_trich2 as [[|]|].
  - destruct s.
    lia.
  - destruct s.
    lia.
  - destruct s.
    assert (x = Qnump0) by lia.
    rewrite H.
    auto.
Qed.

Lemma Qpos_from_to : forall x, Qpos_to_BinPath (BinPath_to_Qpos x) = x.
Proof.
  intro.
  induction x.
  - simpl.
    rewrite Qpos_to_BinPath_equation.
    destruct pos_trich2 as [[|]|].
    + reflexivity.
    + destruct s as [z Hz].
      simpl Qnump in Hz; simpl Qdenp in Hz; lia.
    + destruct s as [z Hz].
      simpl Qnump in Hz; simpl Qdenp in Hz; lia.
  - simpl.
    rewrite qp_left_Left.
    rewrite IHx; auto.
  - simpl.
    rewrite qp_right_Right.
    rewrite IHx; auto.
Qed.

Fixpoint path_to_nat(x : BinPath) : nat :=
  match x with
  | Empty => 0
  | Left y => S (2 * path_to_nat y)
  | Right y => S (S (2 * path_to_nat y))
  end.

Lemma path_to_nat_Left : forall x,
  path_to_nat (Left x) = S (2 * path_to_nat x).
Proof.
  auto.
Qed.

Lemma path_to_nat_Right : forall x,
  path_to_nat (Right x) = S (S (2 * path_to_nat x)).
Proof.
  auto.
Qed.

Function path_from_nat(n : nat){measure id n} : BinPath :=
  match n with
  | 0 => Empty
  | S m => if Util.even m then Left (path_from_nat (m/2)) else Right (path_from_nat (m/2))
  end.
Proof.
  - intros; unfold id.
    destruct (even_half _ teq0) as [k Hk].
    rewrite <- Hk.
    rewrite half_2k.
    lia.
  - intros.
    unfold id.
    destruct (odd_half _ teq0) as [k Hk].
    rewrite <- Hk.
    rewrite half_2k1.
    lia.
Defined.

Lemma path_from_to : forall x, path_from_nat (path_to_nat x) = x.
Proof.
  induction x.
  - auto.
  - rewrite path_to_nat_Left.
    rewrite path_from_nat_equation.
    rewrite even_2k.
    rewrite half_2k.
    rewrite IHx; auto.
  - rewrite path_to_nat_Right.
    rewrite path_from_nat_equation.
    rewrite odd_2k1.
    rewrite half_2k1.
    rewrite IHx; auto.
Qed.

Lemma path_to_from : forall x, path_to_nat (path_from_nat x) = x.
Proof.
  intro x.
  apply path_from_nat_ind.
  - auto.
  - intros.
    rewrite path_to_nat_Left.
    rewrite H.
    destruct (even_half _ e0) as [k Hk].
    rewrite <- Hk.
    rewrite half_2k; auto.
  - intros.
    rewrite path_to_nat_Right.
    rewrite H.
    destruct (odd_half _ e0) as [k Hk].
    rewrite <- Hk.
    rewrite half_2k1; auto.
Qed.

Definition Qpos_to_nat : Qpos -> nat :=
  fun q => path_to_nat (Qpos_to_BinPath q).

Definition nat_to_Qpos : nat -> Qpos :=
  fun x => BinPath_to_Qpos (path_from_nat x).

Lemma Qpos_to_nat_morph : forall q q',
  q == q' -> Qpos_to_nat q = Qpos_to_nat q'.
Proof.
  intros.
  unfold Qpos_to_nat.
  f_equal.
  apply Qpos_to_BinPath_morph; auto.
Qed.

Lemma Qpos_nat_to_from : forall x, Qpos_to_nat (nat_to_Qpos x) = x.
Proof.
  intro.
  unfold Qpos_to_nat.
  unfold nat_to_Qpos.
  rewrite Qpos_from_to.
  apply path_to_from.
Qed.

Lemma Qpos_nat_from_to : forall x, nat_to_Qpos (Qpos_to_nat x) == x.
Proof.
  intro.
  unfold nat_to_Qpos.
  unfold Qpos_to_nat.
  rewrite path_from_to.
  apply Qpos_to_from.
Qed.

Require Import QArith SetoidClass.

Definition Qpos_to_Q_pos : Qpos -> Q :=
  fun q => match q with
           | mkQp a b => Qmake (Zpos a) b
           end.

Definition Qpos_to_Q_neg : Qpos -> Q :=
  fun q => match q with
           | mkQp a b => Qmake (Zneg a) b
           end.

Definition Q_to_nat : Q -> nat :=
  fun q => match q with
           | Qmake Z0 _ => 0%nat
           | Qmake (Zpos p) d => S (2 * Qpos_to_nat (mkQp p d))
           | Qmake (Zneg p) d => S (S (2 * Qpos_to_nat (mkQp p d)))
           end.

Definition nat_to_Q : nat -> Q :=
  fun n => match n with
           | 0%nat => 0
           | S m => if even m then (Qpos_to_Q_pos (nat_to_Qpos (m/2)))
                      else (Qpos_to_Q_neg (nat_to_Qpos (m/2)))
           end.

Instance Setoid_Q : Setoid Q := {|
  equiv := Qeq
  |}.

Lemma Q_to_nat_morph : forall q q', q == q' -> Q_to_nat q = Q_to_nat q'.
Proof.
  intros.
  simpl in H.
  unfold Q_to_nat.
  destruct q,q'.
  unfold Qeq in H.
  destruct Qnum, Qnum0; try auto; try discriminate.
  - simpl in H.
    f_equal.
    f_equal.
    unfold Qpos_to_nat.
    f_equal.
    apply Qpos_to_BinPath_morph.
    simpl.
    inversion H; auto.
  - simpl in H.
    f_equal; f_equal; f_equal.
    unfold Qpos_to_nat; f_equal.
    apply Qpos_to_BinPath_morph.
    simpl.
    inversion H; auto.
Qed.

Lemma Q_to_from : forall x, Q_to_nat (nat_to_Q x) = x.
Proof.
  intro.
  unfold Q_to_nat.
  unfold nat_to_Q.
  destruct x.
  - reflexivity.
  - destruct (even x) eqn:G.
    + unfold Qpos_to_Q_pos.
      destruct nat_to_Qpos eqn:G1.
      rewrite <- G1.
      rewrite Qpos_nat_to_from.
      destruct (even_half _ G) as [k Hk].
      rewrite <- Hk.
      rewrite half_2k; auto.
    + unfold Qpos_to_Q_neg.
      destruct nat_to_Qpos eqn:G2.
      rewrite <- G2.
      rewrite Qpos_nat_to_from.
      destruct (odd_half _ G) as [k Hk].
      rewrite <- Hk.
      rewrite half_2k1; auto.
Qed.

Lemma Q_from_to : forall x, nat_to_Q (Q_to_nat x) == x.
Proof.
  intro.
  unfold Q_to_nat.
  unfold nat_to_Q.
  destruct x.
  destruct Qnum.
  - simpl; unfold Qeq.
    simpl; lia.
  - rewrite even_2k.
    unfold Qpos_to_Q_pos.
    rewrite half_2k.
    destruct nat_to_Qpos eqn:G.
    pose (Qpos_nat_from_to {| Qnump := p; Qdenp := Qden |}).
    rewrite G in e.
    simpl in e.
    simpl.
    unfold Qeq.
    simpl.
    f_equal.
    auto.
  - rewrite odd_2k1.
    unfold Qpos_to_Q_neg.
    rewrite half_2k1.
    destruct nat_to_Qpos eqn:G.
    pose (Qpos_nat_from_to {| Qnump := p; Qdenp := Qden |}).
    rewrite G in e.
    simpl in e.
    simpl.
    unfold Qeq.
    simpl.
    f_equal.
    auto.
Qed.