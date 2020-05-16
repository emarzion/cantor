Require Import Cantor Class Util SetoidClass Omega.

Instance SetoidSum{X Y}`{Setoid X, Setoid Y} : Setoid (X + Y) :=
  {|
    equiv := fun s1 s2 => match s1,s2 with
                          | inl x1, inl x2 => (x1 == x2)%type
                          | inr y1, inr y2 => (y1 == y2)%type
                          | _,_ => False
                          end
  |}.
Proof.
  split.
  - intros [|]; reflexivity.
  - intros [|] [|]; try tauto; 
    intro; symmetry; auto.
  - intros [|] [|] [|]; try tauto;
    intros H1 H2; rewrite H1; auto.
Defined.

Instance OrdSum X Y `{Ord X, Ord Y} : Ord (X + Y) :=
  {|
    lt := fun s1 s2 => match s1,s2 with
                       | inl _, inr _ => True
                       | inl x1, inl x2 => x1 << x2
                       | inr y1, inr y2 => y1 << y2
                       | _,_ => False
                       end
  |}.
Proof.
  intros [|] [|] [|] [|] G1 G2; 
  simpl in G1, G2; try tauto; try discriminate;
  apply lt_morph; auto.
  - intros [|]; apply lt_irref.
  - intros [|] [|] [|]; try tauto; apply Class.lt_trans.
  - intros [|] [|]; try tauto; simpl; apply lt_trich.
Defined.

Definition nat_to_sum : nat -> nat + nat :=
  fun n => if even n then inl (n/2) else inr (n/2).

Definition nat_from_sum : nat + nat -> nat :=
  fun s => match s with
           | inl n => (2*n)
           | inr n => S (2*n)
           end.

Lemma nat_sum_to_from : forall s, nat_to_sum (nat_from_sum s) = s.
Proof.
  intros []; unfold nat_to_sum, nat_from_sum.
  - rewrite even_2k.
    rewrite half_2k; auto.
  - rewrite odd_2k1.
    rewrite half_2k1; auto.
Qed.

Lemma nat_sum_from_to : forall n, nat_from_sum (nat_to_sum n) = n.
Proof.
  intro; unfold nat_from_sum, nat_to_sum.
  destruct (even n) eqn:G.
  - destruct (even_half _ G) as [k Hk].
    rewrite <- Hk at 1.
    rewrite half_2k; auto.
  - destruct (odd_half _ G) as [k Hk].
    rewrite <- Hk at 1.
    rewrite half_2k1; auto.
Qed.

Instance CDLOWOEPSum{X Y}`{Ord X, Ord Y}`{CDLOWOEP X, CDLOWOEP Y}
  : CDLOWOEP (OrdSum X Y) :=
  {| to_nat := fun s => match s with
                        | inl x => nat_from_sum (inl (to_nat x))
                        | inr y => nat_from_sum (inr (to_nat y))
                        end;
     from_nat := fun n => match nat_to_sum n with
                          | inl i => inl (from_nat i)
                          | inr j => inr (from_nat j)
                          end;
     mid := fun s1 s2 => match s1,s2 with
                         | inl x1, inl x2 => inl (mid x1 x2)
                         | inl x, inr y => inl (right x)
                         | inr y, inl x => inl (right x)
                         | inr y1, inr y2 => inr (mid y1 y2)
                         end;
     left := fun s => match s with
                      | inl x => inl (left x)
                      | inr y => inr (left y)
                      end;
     right := fun s => match s with
                       | inl x => inl (right x)
                       | inr y => inr (right y)
                       end
  |}.
Proof.
  intros [|] [|] G; simpl in G; try tauto.
  - f_equal; f_equal.
    apply to_nat_morph; auto.
  - f_equal; f_equal.
    apply to_nat_morph; auto.
  - intro.
    destruct nat_to_sum eqn:G.
    + rewrite to_from.
      rewrite <- G.
      apply nat_sum_from_to.
    + rewrite to_from.
      rewrite <- G.
      apply nat_sum_from_to.
  - intros [|]; rewrite nat_sum_to_from; simpl; apply from_to.
  - intros [|] [|] [|] [|]; simpl; intros G1 G2; try tauto.
    + apply mid_morph; auto.
    + apply right_morph; auto.
    + apply right_morph; auto.
    + apply mid_morph; auto.
  - intros [|] [|]; simpl.
    + apply mid_comm.
    + reflexivity.
    + reflexivity.
    + apply mid_comm.
  - intros [|] [|]; simpl; intro; try tauto.
    + apply mid_lt_left; auto.
    + apply right_lt.
    + apply mid_lt_left; auto.
  - intros [|] [|]; simpl; intro; try tauto.
    + apply mid_lt_right; auto.
    + apply mid_lt_right; auto.
  - intros [|]; simpl; apply mid_idem.
  - intros [|] [|]; simpl; intro; try tauto.
    + apply left_morph; auto.
    + apply left_morph; auto.
  - intros [|]; simpl; apply left_lt.
  - intros [|] [|]; simpl; intro; try tauto.
    + apply right_morph; auto.
    + apply right_morph; auto.
  - intros [|]; simpl; apply right_lt.
Defined.

Instance SetoidProd{X Y}`{Setoid X, Setoid Y} : Setoid (X * Y) :=
  {|
    equiv := fun p1 p2 => fst p1 == fst p2 /\ snd p1 == snd p2
  |}.
Proof.
  split.
  - intros [x y]; split; simpl; reflexivity.
  - intros [x1 y1] [x2 y2]; simpl;
    intros [G1 G2]; split; symmetry; auto.
  - intros [x1 y1] [x2 y2] [x3 y3]; simpl.
    intros [] []; split.
    + rewrite H1; auto.
    + rewrite H2; auto.
Defined.

Instance OrdProd X Y`{Ord X, Ord Y} : Ord (X * Y) :=
  {|
    lt := fun p1 p2 => fst p1 << fst p2 \/ (fst p1 == fst p2 /\ snd p1 << snd p2)
  |}.
Proof.
  - intros [x1 y1] [x2 y2] [x3 y3] [x4 y4]; simpl.
    intros [] [] [|].
    + left; exact (lt_morph _ _ _ _ H3 H5 H7).
    + right; destruct H7; split.
      * rewrite <- H3, <- H5; auto.
      * exact (lt_morph _ _ _ _ H4 H6 H8).
  - intros p [|[]].
    + exact (lt_irref _ H3).
    + exact (lt_irref _ H4).
  - intros p1 p2 p3 [|[]] [|[]]; try tauto.
    + left; exact (Class.lt_trans _ _ _ H3 H4).
    + left; exact (lt_morph _ _ _ _ (reflexivity _) H4 H3).
    + left.
      symmetry in H3.
      exact (lt_morph _ _ _ _ H3 (reflexivity _) H5).
    + right; split.
      * rewrite <- H5; auto.
      * exact (Class.lt_trans _ _ _ H4 H6).
  - intros; simpl.
    destruct (lt_trich (fst x) (fst y)) as [[|]|].
    + tauto.
    + destruct (lt_trich (snd x) (snd y)) as [[|]|].
      * tauto.
      * tauto.
      * symmetry in e; tauto.
    + tauto.
Defined.

Definition next_pair(p : nat * nat) : nat * nat :=
  match p with
  | (x,0)   => (0,S x)
  | (x,S y) => (S x,y)
  end.

Fixpoint iter{X}(f : X -> X)(n : nat)(x0 : X) : X :=
  match n with
  | 0   => x0
  | S m => f (iter f m x0)
  end.

Lemma iter_sum : forall {X}(f : X -> X)(n m : nat)(x0 : X),
  iter f (n + m) x0 = iter f n (iter f m x0).
Proof.
  intros.
  induction n.
  - auto.
  - simpl.
    rewrite IHn; auto.
Qed.

Definition to_pair : nat -> nat * nat :=
  fun n => iter next_pair n (0,0).

Fixpoint triangle(n : nat) : nat :=
  match n with
  | 0   => 0
  | S m => n + (triangle m)
  end.

Definition from_pair(p : nat * nat) : nat :=
  let (x,y) := p in (triangle (x+y) + x).

Lemma next_pair_lemma : forall x y, y <= x -> iter next_pair y (0,x) = (y,x - y).
Proof.
  intro x; induction y; intro.
  - inversion H; reflexivity.
  - simpl.
    assert (y <= x) by omega.
    rewrite (IHy H0).
    simpl.
    destruct (x - y) eqn:G.
    + omega.
    + destruct x.
      * omega.
      * simpl.
        assert (S x - y = S (x - y)) by omega.
        rewrite H1 in G.
        inversion G.
        reflexivity.
Qed.

Lemma pair_num : forall x, to_pair (from_pair (0,x)) = (0,x).
Proof.
  unfold from_pair.
  simpl.
  intro x.
  rewrite <- plus_n_O.
  induction x.
  - reflexivity.
  - assert (triangle (S x) = (S x) + triangle x) by reflexivity.
    rewrite H.
    unfold to_pair.
    rewrite iter_sum.
    unfold to_pair in IHx.
    rewrite IHx.
    simpl.
    assert (iter next_pair x (0,x) = (x,0)).
    + assert (x <= x) by omega.
      pose (next_pair_lemma _ _ H0).
      rewrite e.
      rewrite Nat.sub_diag; reflexivity.
    + rewrite H0; reflexivity.
Qed.

Lemma tp_fp_correct : forall p, to_pair (from_pair p) = p.
Proof.
  unfold to_pair, from_pair.
  destruct p.
  rewrite plus_comm.
  rewrite iter_sum.
  pose (pair_num (n + n0)).
  unfold to_pair, from_pair in e.
  simpl in e.
  rewrite <- plus_n_O in e.
  rewrite e.
  assert (n <= n + n0) by omega.
  pose (next_pair_lemma _ _ H).
  rewrite e0.
  assert (n + n0 - n = n0) by omega.
  congruence.
Qed.

Lemma fp_tp_correct : forall n, from_pair (to_pair n) = n.
Proof.
  unfold from_pair, to_pair.
  induction n.
  - reflexivity.
  - simpl.
    destruct (iter next_pair n (0,0)) eqn:G.
    simpl.
    destruct n1.
    + simpl.
      rewrite <- plus_n_O.
      rewrite <- plus_n_O in IHn.
      omega.
    + simpl.
      rewrite <- plus_n_Sm in IHn.
      simpl in IHn.
      omega.
Qed.

Definition nat_to_prod := to_pair.
Definition nat_from_prod := from_pair.

Opaque nat_to_prod.
Opaque nat_from_prod.

Lemma nat_prod_to_from : forall p, nat_to_prod (nat_from_prod p) = p.
Proof.
  exact tp_fp_correct.
Qed.

Lemma nat_prod_from_to : forall n, nat_from_prod (nat_to_prod n) = n.
Proof.
  exact fp_tp_correct.
Qed.

Instance CDLOWOEPProd{X Y}`{Ord X, Ord Y}`{CDLOWOEP X, CDLOWOEP Y}
  : CDLOWOEP (OrdProd X Y) :=
  {|
    to_nat := fun p => nat_from_prod (to_nat (fst p), to_nat (snd p));
    from_nat := fun n => let p := nat_to_prod n in (from_nat (fst p), from_nat (snd p));
    mid := fun p1 p2 => if Class.dec_eq (fst p1) (fst p2) then (fst p1,mid (snd p1) (snd p2)) else (mid (fst p1) (fst p2), mid (snd p1) (snd p2));
    left := fun p => (fst p, left (snd p));
    right := fun p => (fst p, right (snd p))
  |}.
Proof.
  - simpl; unfold fst, snd.
    intros [] []; intros [G1 G2].
    f_equal; f_equal; apply to_nat_morph; auto.
  - simpl.
    intro; rewrite to_from.
    unfold fst,snd.
    destruct (nat_to_prod n) eqn:G.
    rewrite to_from.
    rewrite <- G.
    apply nat_prod_from_to.
  - intro; rewrite nat_prod_to_from.
    cbv zeta.
    split; unfold fst,snd; destruct x; apply from_to.
  - intros.
    repeat destruct Class.dec_eq; try tauto.
    + split.
      * simpl fst.
        destruct H7; auto.
      * simpl snd.
        destruct H7,H8.
        apply mid_morph; auto.
    + elim n.
      destruct H7,H8.
      rewrite <- H7, <- H8; auto.
    + elim n.
      destruct H7,H8.
      rewrite H7, H8; auto.
    + destruct H7,H8; split.
      * simpl fst; apply mid_morph; auto.
      * simpl snd; apply mid_morph; auto.
  - intros [] []; simpl fst; simpl snd.
    destruct (Class.dec_eq x x0); destruct (Class.dec_eq x0 x).
    + split.
      * simpl; auto.
      * simpl; apply mid_comm.
    + symmetry in e; contradiction.
    + symmetry in e; contradiction.
    + split; simpl; apply mid_comm.
  - intros [] [] [|[]].
    + destruct Class.dec_eq.
      * simpl fst in H7,e.
        elim (lt_irref _ (@lt_morph _ _ _ _ _ _ _  e (reflexivity  _) H7)).
      * left.
        simpl fst in *.
        apply mid_lt_left; auto.
    + destruct Class.dec_eq.
      * clear e.
        right; simpl fst; simpl snd; split.
        ** reflexivity.
        ** apply mid_lt_left; auto.
      * contradiction.
  - intros [] [] [|[]].
    + destruct Class.dec_eq.
      * simpl fst in H7,e.
        elim (lt_irref _ (@lt_morph _ _ _ _ _ _ _ e (reflexivity _) H7)).
      * simpl fst; simpl snd.
        left; simpl fst; apply mid_lt_right; auto.
    + destruct Class.dec_eq.
      * right; simpl fst; simpl snd; split.
        ** auto.
        ** apply mid_lt_right; auto.
      * contradiction.
  - intros []; simpl.
    destruct (lt_trich x x) as [[|]|]; simpl.
    + elim (lt_irref x l).
    + split; [reflexivity|apply mid_idem].
    + elim (lt_irref x l).
  - intros; split; destruct H7.
    + simpl fst; auto.
    + simpl snd; apply left_morph; auto.
  - intros.
    right; simpl fst; simpl snd; split.
    + reflexivity.
    + apply left_lt.
  - intros; split; destruct H7; simpl fst; simpl snd.
    + auto.
    + apply right_morph; auto.
  - intros.
    right; simpl fst; simpl snd; split.
    + reflexivity.
    + apply right_lt.
Defined.

Definition Puncture{X}`{Setoid X}(x : X) : Type := { x' : X & ~ x == x' }.

Instance Puncture_setoid{X}`{Setoid X}(x : X) : Setoid (Puncture x) := {|
  equiv := fun a b => projT1 a == projT1 b;
  |}.
Proof.
  split.
  - intro a; reflexivity.
  - intros a b; symmetry; auto.
  - intros a b c Hac Hbc.
    rewrite Hac; auto.
Defined.

Instance punc_Ord{X}`{Ord X}(x : X) : Ord (Puncture x) := {|
  lt := fun a b => projT1 a << projT1 b
  |}.
Proof.
  - intros.
    destruct x0,x',y,y'; simpl in *.
    eapply lt_morph.
    + exact H1.
    + exact H2.
    + exact H3.
  - intros; apply lt_irref.
  - intros; eapply Class.lt_trans.
    + exact H1.
    + exact H2.
  - intros [] []; simpl; apply lt_trich.
Defined.

Definition punc_to_nat{X}`{CDLOWOEP X}{x : X} : Puncture x -> nat :=
  fun a =>
    match lt_dec (to_nat (projT1 a)) (to_nat x) with
    | Specif.left _ => to_nat (projT1 a)
    | Specif.right _ => pred (to_nat (projT1 a))
    end.

Definition punc_from_nat{X}`{CDLOWOEP X}{x : X} : nat -> Puncture x.
Proof.
  intro n.
  destruct (lt_dec n (to_nat x)).
  - exists (from_nat n).
    intro.
    pose (to_nat_morph _ _ H1).
    rewrite to_from in e.
    omega.
  - exists (from_nat (S n)).
    intro.
    pose (to_nat_morph _ _ H1).
    rewrite to_from in e; omega.
Defined.

Definition punc_mid{X}`{CDLOWOEP X}{x : X} : Puncture x -> Puncture x -> Puncture x.
Proof.
  intros [] [].
  destruct (lt_trich x (mid x0 x1)) as [[Hlt|Heq]|Hgt].
  - exists (mid x0 x1).
    intro.
    elim (lt_irref x).
    eapply lt_morph.
    + reflexivity.
    + symmetry; exact H1.
    + exact Hlt.
  - destruct (lt_trich x0 x1) as [[Glt|Geq]|Ggt].
    + exists (mid x x1).
      destruct (lt_trich x x1) as [[Ilt|Ieq]|Igt].
      * intro.
        elim (lt_irref x).
        eapply lt_morph.
        ** reflexivity.
        ** symmetry; exact H1.
        ** exact (mid_lt_left _ _ Ilt).
      * contradiction.
      * pose (mid_lt_right _ _ Glt).
        elim (lt_irref x).
        eapply lt_morph.
        ** symmetry; exact Heq.
        ** reflexivity.
        ** apply (Class.lt_trans _ x1); auto.
    + elim n.
      rewrite Heq.
      rewrite  <- (mid_idem x0) at 2.
      apply mid_morph.
      * reflexivity.
      * symmetry; exact Geq.
    + exists (mid x x0).
      intro.
      destruct (lt_trich x x0) as [[Ilt|Ieq]|Igt].
      * elim (lt_irref x).
        eapply lt_morph.
        ** reflexivity.
        ** symmetry; exact H1.
        ** exact (mid_lt_left _ _ Ilt).
      * contradiction.
      * pose (mid_lt_right _ _ Ggt).
        elim (lt_irref x).
        apply (Class.lt_trans _ x0).
        ** eapply lt_morph.
           *** rewrite mid_comm in Heq.
               symmetry in Heq; exact Heq.
           *** reflexivity.
           *** exact l.
        ** exact Igt.
  - exists (mid x0 x1).
    intro.
    elim (lt_irref x).
    eapply lt_morph.
    + symmetry; exact H1.
    + reflexivity.
    + exact Hgt.
Defined.

Definition punc_left{X}`{CDLOWOEP X}{x : X} : Puncture x -> Puncture x.
Proof.
  intros [].
  destruct (lt_trich (left x0) x) as [[|]|].
  - exists (left x0).
    intro.
    elim (lt_irref x).
    eapply lt_morph.
    + symmetry; exact H1.
    + reflexivity.
    + exact l.
  - exists (left x).
    intro.
    elim (lt_irref x).
    eapply lt_morph.
    + symmetry; exact H1.
    + reflexivity.
    + apply left_lt.
  - exists (left x0).
    intro.
    elim (lt_irref x).
    eapply lt_morph.
    + reflexivity.
    + symmetry; exact H1.
    + exact l.
Defined.

Definition punc_right{X}`{CDLOWOEP X}{x : X} : Puncture x -> Puncture x.
Proof.
  intros [].
  destruct (lt_trich (right x0) x) as [[|]|].
  - exists (right x0).
    intro.
    elim (lt_irref x).
    eapply lt_morph.
    + symmetry; exact H1.
    + reflexivity.
    + exact l.
  - exists (right x).
    intro.
    elim (lt_irref x).
    eapply lt_morph.
    + reflexivity.
    + symmetry; exact H1.
    + apply right_lt.
  - exists (right x0).
    intro.
    elim (lt_irref x).
    eapply lt_morph.
    + reflexivity.
    + symmetry; exact H1.
    + exact l.
Defined.

Definition use_false_subterm : forall (P : False -> Type){e}, P e :=
  fun P e => match e with end.

Instance punc_CDLOWOEP{X}`{CDLOWOEP X}{x : X} : CDLOWOEP (punc_Ord x) :=
  {| to_nat := punc_to_nat;
     from_nat := punc_from_nat;
     mid := punc_mid;
     left := punc_left;
     right := punc_right
  |}.
Proof.
  - intros.
    unfold punc_to_nat.
    destruct (lt_dec (to_nat (projT1 x0)) (to_nat x));
    destruct (lt_dec (to_nat (projT1 x')) (to_nat x)).
    + apply to_nat_morph; exact H1.
    + destruct x0,x'; simpl in *.
      rewrite (to_nat_morph _ _ H1) in l; contradiction.
    + destruct x0,x'; simpl in *.
      rewrite (to_nat_morph _ _ H1) in n; contradiction.
    + f_equal; apply to_nat_morph; exact H1.
  - intro.
    unfold punc_to_nat, punc_from_nat.
    destruct (lt_dec n (to_nat x)); simpl.
    + rewrite to_from.
      destruct (lt_dec n (to_nat x)).
      * reflexivity.
      * contradiction.
    + rewrite to_from.
      destruct (lt_dec (S n) (to_nat x)).
      * omega.
      * reflexivity.
  - intros [].
    unfold punc_from_nat, punc_to_nat; simpl.
    destruct (lt_dec (to_nat x0) (to_nat x)); simpl.
    + destruct (lt_dec (to_nat x0) (to_nat x)); simpl.
      * apply from_to.
      * contradiction.
    + destruct (lt_dec (Init.Nat.pred (to_nat x0)) (to_nat x)); simpl.
      * assert (to_nat x0 = to_nat x) by omega.
        elim n.
        symmetry.
        rewrite <- (from_to x0), <- (from_to x).
        rewrite H1; reflexivity.
      * assert (to_nat x0 <> to_nat x).
        ** intro.
           elim n.
           rewrite <- (from_to x), <- (from_to x0).
           rewrite H1; reflexivity.
        ** rewrite Nat.succ_pred_pos.
           *** apply from_to.
           *** omega.
  - intros.
    destruct x0,x',y,y'.
    simpl in *.
    destruct (lt_trich x (mid x0 x2)) as [[|]|].
    + simpl.
      destruct (lt_trich x (mid x1 x3)) as [[|]|]; simpl.
      * apply mid_morph; auto.
      * destruct (lt_trich x1 x3) as [[|]|]; simpl.
        ** elim (lt_irref x).
           eapply lt_morph.
           *** reflexivity.
           *** rewrite <- (mid_morph _ _ _ _ H1 H2) in e.
               symmetry; exact e.
           *** exact l.
        ** apply (use_false_subterm (fun e => mid x0 x2 == projT1 (False_rect (Puncture x) e))).
        ** elim (lt_irref x).
           eapply lt_morph.
           *** reflexivity.
           *** rewrite <- (mid_morph _ _ _ _ H1 H2) in e.
               symmetry in e; exact e.
           *** exact l.
      * apply mid_morph; auto.
    + destruct (lt_trich x0 x2) as [[|]|]; simpl.
      * destruct (lt_trich x (mid x1 x3)) as [[|]|]; simpl.
        ** elim (lt_irref x).
           eapply lt_morph.
           *** reflexivity.
           *** symmetry in H1,H2.
               rewrite <- (mid_morph _ _ _ _ H1 H2) in e.
               symmetry in e; exact e.
           *** exact l0.
        ** destruct (lt_trich x1 x3) as [[|]|]; simpl.
           *** apply mid_morph; [reflexivity|auto].
           *** apply (use_false_subterm (fun e => mid x x2 == projT1 (False_rect (Puncture x) e))).
           *** elim (lt_irref x3).
               apply (Class.lt_trans _ x1); auto.
               eapply lt_morph.
               **** exact H1.
               **** exact H2.
               **** exact l.
        ** elim (lt_irref x).
           eapply lt_morph.
           *** rewrite (mid_morph _ _ _ _ H1 H2) in e.
               symmetry; exact e.
           *** reflexivity.
           *** exact l0.
      * apply (use_false_subterm (fun e => projT1 (False_rect (Puncture x) e) == _)).
      * destruct (lt_trich x (mid x1 x3)) as [[|]|]; simpl.
        ** elim (lt_irref x).
           eapply lt_morph.
           *** reflexivity.
           *** rewrite e; apply mid_morph.
               **** symmetry; exact H1.
               **** symmetry; exact H2.
           *** exact l0.
        ** destruct (lt_trich x1 x3) as [[|]|]; simpl.
           *** elim (lt_irref x2).
               apply (Class.lt_trans _ x0); auto.
               eapply lt_morph.
               **** symmetry; exact H1.
               **** symmetry; exact H2.
               **** exact l0.
           *** apply (use_false_subterm (fun e => _ == projT1 (False_rect _ e))).
           *** apply mid_morph; [reflexivity|exact H1].
        ** elim (lt_irref x).
           eapply lt_morph.
           *** rewrite e; apply mid_morph; [symmetry; exact H1|symmetry; exact H2].
           *** reflexivity.
           *** exact l0.
    + simpl.
      destruct (lt_trich x (mid x1 x3)) as [[|]|]; simpl.
      ** apply mid_morph; auto.
      ** elim (lt_irref x).
         eapply lt_morph.
         *** rewrite e; apply mid_morph; [exact H1|exact H2].
         *** reflexivity.
         *** exact l.
      ** apply mid_morph; auto.
  - intros [] []; simpl.
    destruct (lt_trich x (mid x0 x1)) as [[|]|]; simpl.
    + destruct (lt_trich x (mid x1 x0)) as [[|]|]; simpl.
      * apply mid_comm.
      * elim (lt_irref x).
        eapply lt_morph.
        ** reflexivity.
        ** rewrite e; apply mid_comm.
        ** exact l.
      * apply mid_comm.
    + destruct (lt_trich x0 x1) as [[|]|]; simpl.
      * destruct (lt_trich x (mid x1 x0)) as [[|]|]; simpl.
        ** elim (lt_irref x).
           eapply lt_morph.
           *** reflexivity.
           *** rewrite e; apply mid_comm.
           *** exact l0.
        ** destruct (lt_trich x1 x0) as [[|]|]; simpl.
           *** elim (lt_irref x0).
               apply (Class.lt_trans _ x1); auto.
           *** apply (use_false_subterm (fun e => _ == projT1 (False_rect _ e))).
           *** reflexivity.
        ** elim (lt_irref x).
           eapply lt_morph.
           *** rewrite e; apply mid_comm.
           *** reflexivity.
           *** exact l0.
      * apply (use_false_subterm (fun e => projT1 (False_rect _ e) == _)).
      * destruct (lt_trich x (mid x1 x0)) as [[|]|]; simpl.
        ** elim (lt_irref x).
           eapply lt_morph.
           *** reflexivity.
           *** rewrite e; apply mid_comm.
           *** exact l0.
        ** destruct (lt_trich x1 x0) as [[|]|]; simpl.
           *** reflexivity.
           *** apply (use_false_subterm (fun e => _ == projT1 (False_rect _ e))).
           *** elim (lt_irref x1).
               apply (Class.lt_trans _ x0); auto.
        ** elim (lt_irref x).
           eapply lt_morph.
           *** rewrite e; apply mid_comm.
           *** reflexivity.
           *** exact l0.
    + destruct (lt_trich x (mid x1 x0)) as [[|]|]; simpl.
      * apply mid_comm.
      * elim (lt_irref x).
        eapply lt_morph.
        ** rewrite e; apply mid_comm.
        ** reflexivity.
        ** exact l.
      * apply mid_comm.
  - intros.
    destruct x0,x'; simpl in *.
    destruct (lt_trich x (mid x0 x1)) as [[|]|]; simpl.
    + apply mid_lt_left; auto.
    + destruct (lt_trich x0 x1) as [[|]|]; simpl.
      * apply (Class.lt_trans _ x).
        ** eapply lt_morph.
           *** reflexivity.
           *** symmetry; exact e.
           *** apply mid_lt_left; auto.
        ** apply mid_lt_left.
           eapply lt_morph.
           *** symmetry; exact e.
           *** reflexivity.
           *** apply mid_lt_right; auto.
      * elim (lt_irref x0).
        eapply lt_morph.
        ** reflexivity.
        ** symmetry; exact e0.
        ** exact H1.
      * elim (lt_irref x0).
        apply (Class.lt_trans _ x1); auto.
    + apply mid_lt_left; auto.
  - intros.
    destruct x0,x'; simpl in *.
    destruct (lt_trich x (mid x0 x1)) as [[|]|]; simpl.
    + apply mid_lt_right; auto.
    + destruct (lt_trich x0 x1) as [[|]|]; simpl.
      * apply mid_lt_right.
        eapply lt_morph.
        ** symmetry; exact e.
        ** reflexivity.
        ** apply mid_lt_right; auto.
      * apply (use_false_subterm (fun e => projT1 (False_rect _ e) << _)).
      * elim (lt_irref x0).
        apply (Class.lt_trans _ x1); auto.
    + apply mid_lt_right; auto.
  - intros []; simpl.
    destruct (lt_trich x (mid x0 x0)) as [[|]|]; simpl.
    + apply mid_idem.
    + destruct (lt_trich x0 x0) as [[|]|]; simpl.
      * elim (lt_irref _ l).
      * apply (use_false_subterm (fun e => projT1 (False_rect _ e) == _)).
      * elim (lt_irref _ l).
    + apply mid_idem.
  - intros.
    destruct x0,x'; simpl in *.
    destruct (lt_trich (left x0) x) as [[|]|]; simpl.
    + destruct (lt_trich (left x1) x) as [[|]|]; simpl.
      * apply left_morph; auto.
      * elim (lt_irref x).
        eapply lt_morph.
        ** rewrite <- e; apply left_morph; exact H1.
        ** reflexivity.
        ** exact l.
      * apply left_morph; auto.
    + destruct (lt_trich (left x1) x) as [[|]|]; simpl.
      * elim (lt_irref x).
        eapply lt_morph.
        ** rewrite <- e; apply left_morph; symmetry; exact H1.
        ** reflexivity.
        ** exact l.
      * reflexivity.
      * elim (lt_irref x).
        eapply lt_morph.
        ** reflexivity.
        ** rewrite <- e; apply left_morph; symmetry; exact H1.
        ** exact l.
    + destruct (lt_trich (left x1) x) as [[|]|]; simpl.
      * apply left_morph; auto.
      * elim (lt_irref x).
        eapply lt_morph.
        ** reflexivity.
        ** rewrite <- e; apply left_morph; exact H1.
        ** exact l.
      * apply left_morph; auto.
  - intros []; simpl.
    destruct (lt_trich (left x0) x) as [[|]|]; simpl.
    + apply left_lt.
    + apply (Class.lt_trans _ x).
      * apply left_lt.
      * eapply lt_morph.
        ** exact e.
        ** reflexivity.
        ** apply left_lt.
    + apply left_lt.
  - intros.
    destruct x0,x'; simpl in *.
    destruct (lt_trich (right x0) x) as [[|]|]; simpl.
    + destruct (lt_trich (right x1) x) as [[|]|]; simpl.
      * apply right_morph; auto.
      * elim (lt_irref x).
        eapply lt_morph.
        ** rewrite <- e; apply right_morph; exact H1.
        ** reflexivity.
        ** exact l.
      * apply right_morph; auto.
    + destruct (lt_trich (right x1) x) as [[|]|]; simpl.
      * elim (lt_irref x).
        eapply lt_morph.
        ** rewrite <- e; apply right_morph; symmetry; exact H1.
        ** reflexivity.
        ** exact l.
      * reflexivity.
      * elim (lt_irref x).
        eapply lt_morph.
        ** reflexivity.
        ** rewrite <- e; apply right_morph; symmetry; exact H1.
        ** exact l.
    + destruct (lt_trich (right x1) x) as [[|]|]; simpl.
      * apply right_morph; auto.
      * elim (lt_irref x).
        eapply lt_morph.
        ** reflexivity.
        ** rewrite <- e; apply right_morph; exact H1.
        ** exact l.
      * apply right_morph; auto.
  - intros []; simpl.
    destruct (lt_trich (right x0) x) as [[|]|]; simpl.
    + apply right_lt.
    + apply (Class.lt_trans _ x).
      * eapply lt_morph.
        ** reflexivity.
        ** exact e.
        ** apply right_lt.
      * apply right_lt.
    + apply right_lt.
Defined.

Require Import QArith Qcountable Lia.

Instance Q_Ord : Ord Q :=
  {|
    lt := Qlt
  |}.
Proof.
  - intros.
    rewrite <- H, <-H0; auto.
  - exact Qlt_irrefl.
  - exact Qlt_trans.
  - unfold Qlt.
    simpl.
    unfold Qeq.
    intros.
    pose (a := (Qnum x * QDen y)%Z).
    pose (b := (Qnum y * QDen x)%Z).
    fold a; fold b.
    destruct (Z_ge_lt_dec a b).
    + destruct (Z.eq_dec a b).
      * left; right; auto.
      * right.
        lia.
    + left; auto.
Defined.

Instance Q_CDLOWOEP : CDLOWOEP Q_Ord :=
  {|
    to_nat := Q_to_nat;
    from_nat := nat_to_Q;
    mid := fun x y => (x + y)/(2 # 1);
    left := fun x => x - 1;
    right := fun x => x + 1
  |}.
Proof.
  - exact Q_to_nat_morph.
  - exact Q_to_from.
  - exact Q_from_to.
  - intros.
    rewrite H,H0; reflexivity.
  - intros.
    unfold Qdiv.
    repeat rewrite Qmult_plus_distr_l.
    apply Qplus_comm.
  - intros.
    simpl.
    unfold Qdiv.
    rewrite Qmult_plus_distr_l.
    unfold Qinv.
    unfold Qnum.
    simpl.
    simpl in H.
    rewrite <- (Qplus_lt_r _ _ (x * (-1 # 2))).
    rewrite <- (Qmult_1_r x) at 2.
    rewrite <- Qmult_plus_distr_r.
    assert ((-1 # 2) + 1 == 1 # 2) by (unfold Qplus; simpl; reflexivity).
    rewrite H0.
    rewrite Qplus_assoc.
    rewrite <- Qmult_plus_distr_r.
    assert ((-1 # 2) + (1 # 2) == 0) by (unfold Qplus; simpl; reflexivity).
    rewrite H1, Qmult_0_r, Qplus_0_l.
    apply Qmult_lt_compat_r.
    + unfold Qlt; simpl; lia.
    + exact H.
  - intros.
    simpl.
    unfold Qdiv.
    rewrite Qmult_plus_distr_l.
    unfold Qinv.
    simpl.
    simpl in H.
    rewrite <- (Qplus_lt_l _ _ (x' * (-1 # 2))).
    rewrite <- Qplus_assoc.
    rewrite <- Qmult_plus_distr_r.
    assert ((1 # 2) + (-1 # 2) == 0) by (unfold Qplus; simpl; reflexivity).
    rewrite H0, Qmult_0_r, Qplus_0_r.
    rewrite <- (Qmult_1_r x') at 1.
    rewrite <- Qmult_plus_distr_r.
    assert (1 + (-1 # 2) == (1 # 2)) by (unfold Qplus; simpl; reflexivity).
    rewrite H1.
    apply Qmult_lt_compat_r.
    + unfold Qlt; simpl; lia.
    + exact H.
  - intros.
    rewrite <- (Qmult_1_l x) at 1 2.
    rewrite <- Qmult_plus_distr_l.
    assert (1 + 1 == 2 # 1) by (unfold Qplus; simpl; reflexivity).
    rewrite H, Qmult_comm.
    apply Qdiv_mult_l.
    unfold Qeq.
    simpl; lia.
  - intros.
    rewrite H; reflexivity.
  - intro; simpl.
    rewrite <- (Qplus_0_r x) at 2.
    unfold Qminus.
    apply Qplus_lt_r.
    unfold Qlt; simpl; lia.
  - intros.
    rewrite H; reflexivity.
  - intros; simpl.
    rewrite <- (Qplus_0_r x) at 1.
    apply Qplus_lt_r.
    unfold Qlt; simpl; lia.
Defined.
