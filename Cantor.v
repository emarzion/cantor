(* Proof of Cantor's Theorem *)

Require Import SetoidClass List PeanoNat Omega.
Import ListNotations.

Require Import Class Util.

Infix "!" := list_index (at level 10).
 
Definition ord_cons_x{X Y}`{Ord X, Ord Y}(ps : list (X * Y)) :=
  forall i j, Fin_le i j -> fst (ps ! i) << fst (ps ! j).

Lemma ord_cons_x_tail{X Y}`{Ord X, Ord Y}(p : X * Y)(ps : list (X * Y)) :
  ord_cons_x (p::ps) -> ord_cons_x ps.
Proof.
  intros Hpps i j Hij.
  exact (Hpps (inr i) (inr j) Hij).
Qed.

Definition ord_cons_y{X Y}`{Ord X, Ord Y}(ps : list (X * Y)) :=
  forall i j, Fin_le i j -> snd (ps ! i) << snd (ps ! j).

Lemma ord_cons_y_tail{X Y}`{Ord X, Ord Y}(p : X * Y)(ps : list (X * Y)) :
  ord_cons_y (p::ps) -> ord_cons_y ps.
Proof.
  intros Hpps i j Hij.
  exact (Hpps (inr i) (inr j) Hij).
Qed.

Definition below_x{X Y}`{Ord X, Ord Y}(x : X)(ps : list (X * Y)) := forall i, x << fst (ps ! i).

Definition below_y{X Y}`{Ord X, Ord Y}(y : Y)(ps : list (X * Y)) := forall i, y << snd (ps ! i).

Record Partial_Iso(X Y : Type)`{CDLOWOEP X, CDLOWOEP Y} := {
  pairs : list (X * Y);
  pairs_ord_cons_x : ord_cons_x pairs;
  pairs_ord_cons_y : ord_cons_y pairs
  }.

Definition empty_Partial_Iso{X Y}`{CDLOWOEP X, CDLOWOEP Y} : Partial_Iso X Y := {|
  pairs := [];
  pairs_ord_cons_x := fun i => match i with end;
  pairs_ord_cons_y := fun i => match i with end
  |}.

Fixpoint insert_x_aux{X Y}`{CDLOWOEP X, CDLOWOEP Y}(last : option Y)(x : X)(ps : list (X * Y)){struct ps} : list (X * Y) :=
  match ps with
  | [] => match last with
          | None => [(x,from_nat 0)]
          | Some y_r => [(x, right y_r)]
          end
  | (x0,y0)::qs => match lt_trich x x0 with
                   | inleft (Specif.left _) => match last with
                                         | None => (x, left y0)::ps
                                         | Some y_r => (x, mid y_r y0)::ps
                                         end
                   | inleft (Specif.right _) => ps
                   | inright _ => (x0,y0) :: insert_x_aux (Some y0) x qs
                   end
  end.

Fixpoint insert_y_aux{X Y}`{CDLOWOEP X, CDLOWOEP Y}(last : option X)(y : Y)(ps : list (X * Y)){struct ps} : list (X * Y) :=
  match ps with
  | [] => match last with
          | None => [(from_nat 0,y)]
          | Some x_r => [(right x_r, y)]
          end
  | (x0,y0)::qs => match lt_trich y y0 with
                   | inleft (Specif.left _) => match last with
                                         | None => (left x0, y)::ps
                                         | Some x_r => (mid x_r x0, y)::ps
                                         end
                   | inleft (Specif.right _) => ps
                   | inright _ => (x0,y0) :: insert_y_aux (Some x0) y qs
                   end
  end.

Definition insert_x{X Y}`{CDLOWOEP X, CDLOWOEP Y} : X -> list (X * Y) -> list (X * Y) := insert_x_aux None.

Definition insert_y{X Y}`{CDLOWOEP X, CDLOWOEP Y} : Y -> list (X * Y) -> list (X * Y) := insert_y_aux None.

Lemma In_insert_x_aux_In{X Y}`{CDLOWOEP X, CDLOWOEP Y} : forall (ps : list (X * Y))(p : X * Y)(x : X)(y : Y), setoidIn p ps -> setoidIn p (insert_x_aux (Some y) x ps).
Proof.
  induction ps; intros.
  - destruct H3.
  - simpl.
    destruct a.
    destruct (lt_trich x x0) as [[|]|].
    + right; exact H3.
    + exact H3.
    + destruct H3.
      * left; exact H3.
      * right; apply IHps; auto.
Qed.

Lemma In_insert_x_In{X Y}`{CDLOWOEP X, CDLOWOEP Y} : forall (ps : list (X * Y))(p : X * Y)(x : X),
  setoidIn p ps -> setoidIn p (insert_x x ps).
Proof.
  intros.
  destruct ps.
  - destruct H3.
  - unfold insert_x.
    simpl.
    destruct p0.
    destruct (lt_trich x x0) as [[|]|].
    + right; exact H3.
    + exact H3.
    + destruct H3.
      * left; exact H3.
      * right; apply In_insert_x_aux_In; exact H3.
Qed.

Lemma In_insert_y_aux_In{X Y}`{CDLOWOEP X, CDLOWOEP Y} : forall (ps : list (X * Y))(p : X * Y)(y : Y)(x : X), setoidIn p ps -> setoidIn p (insert_y_aux (Some x) y ps).
Proof.
  induction ps; intros.
  - destruct H3.
  - simpl.
    destruct a.
    destruct (lt_trich y y0) as [[|]|].
    + right; exact H3.
    + exact H3.
    + destruct H3.
      * left; exact H3.
      * right; apply IHps; auto.
Qed.

Lemma In_insert_y_In{X Y}`{CDLOWOEP X, CDLOWOEP Y} : forall (ps : list (X * Y))(p : X * Y)(y : Y),
  setoidIn p ps -> setoidIn p (insert_y y ps).
Proof.
  intros.
  destruct ps.
  - destruct H3.
  - unfold insert_y.
    simpl.
    destruct p0.
    destruct (lt_trich y y0) as [[|]|].
    + right; exact H3.
    + exact H3.
    + destruct H3.
      * left; exact H3.
      * right; apply In_insert_y_aux_In; exact H3.
Qed.

Lemma below_x_x_lemma{X Y}`{CDLOWOEP X, CDLOWOEP Y} : forall (ps : list (X * Y))(x x' : X)(y : Y), below_x x ps -> x << x' ->
  below_x x (insert_x_aux (Some y) x' ps).
Proof.
  induction ps; intros.
  - simpl.
    intros [[]|[]]; exact H4.
  - simpl.
    destruct a as [x0 y0].
    destruct lt_trich as [[Hlt|Heq]|Hgt].
    + intros [|[|i]]; simpl.
      * exact H4.
      * apply (lt_trans _ x' _); auto.
      * apply (H3 (inr i)).
    + exact H3.
    + intros [|i]; simpl.
      * apply (H3 (inl tt)).
      * apply IHps; auto.
        intro j; apply (H3 (inr j)).
Qed.

Lemma below_x_y_lemma{X Y}`{CDLOWOEP X, CDLOWOEP Y} : forall (ps : list (X * Y))(x x' : X)(y : Y), ord_cons_x ps -> below_x x ps -> (x = x' \/ x << x') -> below_x x (insert_y_aux (Some x') y ps).
Proof.
  induction ps; intros.
  - simpl.
    intros [[]|[]]; simpl.
    destruct H5.
    + rewrite H5; apply right_lt.
    + apply (lt_trans _ x' _); auto.
      apply right_lt.
  - simpl.
    destruct a as [x0 y0].
    destruct lt_trich as [[Hlt|Heq]|Hgt].
    + intros [|[|i]]; simpl.
      * pose (H4 (inl tt)) as pf; simpl in pf.
        destruct (lt_trich x' x0) as [[Glt|Geq]|Ggt].
        ** destruct H5.
           *** rewrite H5.
               apply mid_lt_left; auto.
           *** apply (lt_trans _ x' _); auto.
               apply mid_lt_left; auto.
        ** apply (lt_morph x _ x' _).
           *** reflexivity.
           *** transitivity (mid x' x').
               symmetry; apply mid_idem.
               apply mid_morph; [ reflexivity | auto ].
           *** apply (lt_morph x _ x0 _).
               **** reflexivity.
               **** symmetry; exact Geq.
               **** exact pf.
        ** apply (lt_trans _ x0).
           *** exact pf.
           *** apply mid_lt_left2; auto.
      * exact (H4 (inl tt)).
      * exact (H4 (inr i)).
    + exact H4.
    + intros [|i]; simpl.
      * exact (H4 (inl tt)).
      * eapply IHps.
        ** eapply ord_cons_x_tail; exact H3.
        ** intro j.
           exact (H4 (inr j)).
        ** right.
           exact (H4 (inl tt)).
Qed.

Lemma below_y_y_lemma{X Y}`{CDLOWOEP X, CDLOWOEP Y} : forall (ps : list (X * Y))(y y' : Y)(x : X), below_y y ps -> y << y' ->
  below_y y (insert_y_aux (Some x) y' ps).
Proof.
  induction ps; intros.
  - simpl.
    intros [[]|[]]; exact H4.
  - simpl.
    destruct a as [x0 y0].
    destruct lt_trich as [[Hlt|Heq]|Hgt].
    + intros [|[|i]]; simpl.
      * exact H4.
      * apply (lt_trans _ y' _); auto.
      * apply (H3 (inr i)).
    + exact H3.
    + intros [|i]; simpl.
      * apply (H3 (inl tt)).
      * apply IHps; auto.
        intro j; apply (H3 (inr j)).
Qed.

Lemma below_y_x_lemma{X Y}`{CDLOWOEP X, CDLOWOEP Y} : forall (ps : list (X * Y))(y y' : Y)(x : X), ord_cons_y ps -> below_y y ps -> (y = y' \/ y <<  y') -> below_y y (insert_x_aux (Some y') x ps).
Proof.
  induction ps; intros.
  - simpl.
    intros [[]|[]]; simpl.
    destruct H5.
    + rewrite H5; apply right_lt.
    + apply (lt_trans _ y' _); auto.
      apply right_lt.
  - simpl.
    destruct a as [x0 y0].
    destruct lt_trich as [[Hlt|Heq]|Hgt].
    + intros [|[|i]]; simpl.
      * pose (H4 (inl tt)) as pf; simpl in pf.
        destruct (lt_trich y' y0) as [[Glt|Geq]|Ggt].
        ** destruct H5.
           *** rewrite H5.
               apply mid_lt_left; auto.
           *** apply (lt_trans _ y' _); auto.
               apply mid_lt_left; auto.
        ** apply (lt_morph y _ y' _).
           *** reflexivity.
           *** transitivity (mid y' y').
               symmetry; apply mid_idem.
               apply mid_morph; [ reflexivity | auto ].
           *** apply (lt_morph y _ y0 _).
               **** reflexivity.
               **** symmetry; exact Geq.
               **** exact pf.
        ** apply (lt_trans _ y0).
           *** exact pf.
           *** apply mid_lt_left2; auto.
      * exact (H4 (inl tt)).
      * exact (H4 (inr i)).
    + exact H4.
    + intros [|i]; simpl.
      * exact (H4 (inl tt)).
      * eapply IHps.
        ** eapply ord_cons_y_tail; exact H3.
        ** intro j.
           exact (H4 (inr j)).
        ** right.
           exact (H4 (inl tt)).
Qed.

Lemma insert_x_aux_ord_cons_x{X Y}`{CDLOWOEP X, CDLOWOEP Y} : forall (ps : list (X * Y)) x y, ord_cons_x ps ->
  ord_cons_x (insert_x_aux (Some y) x ps).
Proof.
  induction ps; intros.
  - simpl.
    intros [[]|[]] [[]|[]] Hij.
    destruct Hij.
  - simpl.
    destruct a as [x0 y0].
    destruct lt_trich as [[Hlt|Heq]|Hgt].
    + intros [|[|i]] [|[|j]] Hij; simpl; try destruct Hij.
      * exact Hlt.
      * apply (lt_trans _ x0 _); auto.
        apply (H3 (inl tt) (inr j)); exact I.
      * apply (H3 (inl tt) (inr j)); exact I.
      * apply (H3 (inr i) (inr j)); exact Hij.
    + exact H3.
    + intros [|i] [|j] Hij; simpl; try destruct Hij.
      * apply below_x_x_lemma; auto.
        intro i.
        apply (H3 (inl tt) (inr i)); exact I.
      * apply IHps.
        ** exact (ord_cons_x_tail (x0,y0) ps H3).
        ** exact Hij.
Qed.

Lemma insert_y_aux_ord_cons_x{X Y}`{CDLOWOEP X, CDLOWOEP Y} : forall (ps : list (X * Y)) x y, ord_cons_x ps ->
  below_x x ps -> ord_cons_x (insert_y_aux (Some x) y ps).
Proof.
  induction ps; intros.
  - simpl.
    intros [[]|[]] [[]|[]] Hij; simpl.
    destruct Hij.
  - simpl.
    destruct a as [x0 y0].
    assert (x << x0) by (apply (H4 (inl tt))).
    destruct lt_trich as [[Hlt|Heq]|Hgt].
    + intros [|[|i]] [|[|j]] Hij; simpl; try destruct Hij.
      * apply mid_lt_right; auto.
      * apply (lt_trans _ x0 _).
        ** apply mid_lt_right; auto.
        ** apply (H3 (inl tt) (inr j)); exact I.
      * apply (H3 (inl tt) (inr j)); exact I.
      * apply (H3 (inr i) (inr j)); exact Hij.
    + exact H3.
    + intros [|i] [|j] Hij; simpl; try destruct Hij.
      * eapply below_x_y_lemma.
        ** eapply ord_cons_x_tail; exact H3.
        ** intro i. apply (H3 (inl tt) (inr i)); exact I.
        ** left; reflexivity.
      * apply IHps.
        ** exact (ord_cons_x_tail (x0,y0) ps H3).
        ** intro k; apply (H3 (inl tt) (inr k)); exact I.
        ** exact Hij.
Qed.

Lemma insert_y_aux_ord_cons_y{X Y}`{CDLOWOEP X, CDLOWOEP Y} : forall (ps : list (X * Y)) x y, ord_cons_y ps ->
  ord_cons_y (insert_y_aux (Some x) y ps).
Proof.
  induction ps; intros.
  - simpl.
    intros [[]|[]] [[]|[]] Hij.
    destruct Hij.
  - simpl.
    destruct a as [x0 y0].
    destruct lt_trich as [[Hlt|Heq]|Hgt].
    + intros [|[|i]] [|[|j]] Hij; simpl; try destruct Hij.
      * exact Hlt.
      * apply (lt_trans _ y0 _); auto.
        apply (H3 (inl tt) (inr j)); exact I.
      * apply (H3 (inl tt) (inr j)); exact I.
      * apply (H3 (inr i) (inr j)); exact Hij.
    + exact H3.
    + intros [|i] [|j] Hij; simpl; try destruct Hij.
      * apply below_y_y_lemma; auto.
        intro i.
        apply (H3 (inl tt) (inr i)); exact I.
      * apply IHps.
        exact (ord_cons_y_tail (x0,y0) ps H3).
        exact Hij.
Qed.

Lemma insert_x_aux_ord_cons_y{X Y}`{CDLOWOEP X, CDLOWOEP Y} : forall (ps : list (X * Y)) x y, ord_cons_y ps ->
  below_y y ps -> ord_cons_y (insert_x_aux (Some y) x ps).
Proof.
  induction ps; intros.
  - simpl.
    intros [[]|[]] [[]|[]] Hij; simpl.
    destruct Hij.
  - simpl.
    destruct a as [x0 y0].
    assert (y << y0) by (apply (H4 (inl tt))).
    destruct lt_trich as [[Hlt|Heq]|Hgt].
    + intros [|[|i]] [|[|j]] Hij; simpl; try destruct Hij.
      * apply mid_lt_right; auto.
      * apply (lt_trans _ y0 _).
        ** apply mid_lt_right; auto.
        ** apply (H3 (inl tt) (inr j)); exact I.
      * apply (H3 (inl tt) (inr j)); exact I.
      * apply (H3 (inr i) (inr j)); exact Hij.
    + exact H3.
    + intros [|i] [|j] Hij; simpl; try destruct Hij.
      * eapply below_y_x_lemma.
        ** eapply ord_cons_y_tail; exact H3.
        ** intro i. apply (H3 (inl tt) (inr i)); exact I.
        ** left; reflexivity.
      * apply IHps.
        ** exact (ord_cons_y_tail (x0,y0) ps H3).
        ** intro k; apply (H3 (inl tt) (inr k)); exact I.
        ** exact Hij.
Qed.

Lemma insert_x_ord_cons_x{X Y}`{CDLOWOEP X, CDLOWOEP Y} : forall (ps : list (X * Y)) x, ord_cons_x ps ->
  ord_cons_x (insert_x x ps).
Proof.
  intros.
  unfold insert_x.
  destruct ps.
  - intros [[]|[]] [[]|[]] [].
  - simpl.
    destruct p.
    destruct (lt_trich x x0) as [[Hlt|Heq]|Hgt].
    + intros [[]|i] [[]|j] Hij; simpl.
      * destruct Hij.
      * destruct j; simpl.
        ** auto.
        ** apply (lt_trans _ x0 _); auto.
           apply (H3 (inl tt) (inr f)); exact I.
      * destruct Hij.
      * destruct i,j; simpl.
        ** destruct Hij.
        ** apply (H3 (inl tt) (inr f)); exact I.
        ** destruct Hij.
        ** apply (H3 (inr f) (inr f0)); exact Hij.
    + exact H3.
    + intros [[]|i] [[]|j] Hij; simpl.
      * destruct Hij.
      * apply below_x_x_lemma; auto.
        intro i.
        apply (H3 (inl tt) (inr i)); auto.
      * destruct Hij.
      * eapply insert_x_aux_ord_cons_x; auto.
        eapply ord_cons_x_tail; exact H3.
Qed.

Lemma insert_y_ord_cons_y{X Y}`{CDLOWOEP X, CDLOWOEP Y} : forall (ps : list (X * Y)) y, ord_cons_y ps ->
  ord_cons_y (insert_y y ps).
Proof.
  intros.
  unfold insert_y.
  destruct ps.
  - intros [[]|[]] [[]|[]] [].
  - simpl.
    destruct p.
    destruct (lt_trich y y0) as [[Hlt|Heq]|Hgt].
    + intros [[]|i] [[]|j] Hij; simpl.
      * destruct Hij.
      * destruct j; simpl.
        ** auto.
        ** apply (lt_trans _ y0 _); auto.
           apply (H3 (inl tt) (inr f)); exact I.
      * destruct Hij.
      * destruct i,j; simpl.
        ** destruct Hij.
        ** apply (H3 (inl tt) (inr f)); exact I.
        ** destruct Hij.
        ** apply (H3 (inr f) (inr f0)); exact Hij.
    + exact H3.
    + intros [[]|i] [[]|j] Hij; simpl.
      * destruct Hij.
      * apply below_y_y_lemma; auto.
        intro i.
        apply (H3 (inl tt) (inr i)); auto.
      * destruct Hij.
      * eapply insert_y_aux_ord_cons_y; auto.
        eapply ord_cons_y_tail; exact H3.
Qed.

Lemma insert_x_ord_cons_y{X Y}`{CDLOWOEP X, CDLOWOEP Y} : forall (ps : list (X * Y)) x, ord_cons_y ps ->
  ord_cons_y (insert_x x ps).
Proof.
  intros.
  unfold insert_x.
  destruct ps.
  - intros [[]|[]] [[]|[]] [].
  - simpl.
    destruct p.
    destruct (lt_trich x x0) as [[Hlt|Heq]|Hgt].
    + intros [[]|i] [[]|j] Hij; simpl.
      * destruct Hij.
      * destruct j; simpl.
        ** apply left_lt.
        ** apply (lt_trans _ y _).
           *** apply left_lt.
           *** apply (H3 (inl tt) (inr f)); exact I.
      * destruct Hij.
      * destruct i,j; simpl.
        ** destruct Hij.
        ** apply (H3 (inl tt) (inr f)); exact I.
        ** destruct Hij.
        ** apply (H3 (inr f) (inr f0)); exact Hij.
    + exact H3.
    + intros [[]|i] [[]|j] Hij; simpl.
      * destruct Hij.
      * eapply below_y_x_lemma.
        ** eapply ord_cons_y_tail; exact H3.
        ** intro k; apply (H3 (inl tt) (inr k)); exact I.
        ** left; reflexivity.
      * destruct Hij.
      * eapply insert_x_aux_ord_cons_y.
        eapply ord_cons_y_tail; exact H3.
        ** intro k; apply (H3 (inl tt) (inr k)); exact I.
        ** exact Hij.
Qed.

Lemma insert_y_ord_cons_x{X Y}`{CDLOWOEP X, CDLOWOEP Y} : forall (ps : list (X * Y)) y, ord_cons_x ps ->
  ord_cons_x (insert_y y ps).
Proof.
  intros.
  unfold insert_y.
  destruct ps.
  - intros [[]|[]] [[]|[]] [].
  - simpl.
    destruct p.
    destruct (lt_trich y y0) as [[Hlt|Heq]|Hgt].
    + intros [[]|i] [[]|j] Hij; simpl.
      * destruct Hij.
      * destruct j; simpl.
        ** apply left_lt.
        ** apply (lt_trans _ x _).
           *** apply left_lt.
           *** apply (H3 (inl tt) (inr f)); exact I.
      * destruct Hij.
      * destruct i,j; simpl.
        ** destruct Hij.
        ** apply (H3 (inl tt) (inr f)); exact I.
        ** destruct Hij.
        ** apply (H3 (inr f) (inr f0)); exact Hij.
    + exact H3.
    + intros [[]|i] [[]|j] Hij; simpl.
      * destruct Hij.
      * eapply below_x_y_lemma.
        ** eapply ord_cons_x_tail; exact H3.
        ** intro k; apply (H3 (inl tt) (inr k)); exact I.
        ** left; reflexivity.
      * destruct Hij.
      * eapply insert_y_aux_ord_cons_x.
        eapply ord_cons_x_tail; exact H3.
        ** intro k; apply (H3 (inl tt) (inr k)); exact I.
        ** exact Hij.
Qed.

Lemma insert_x_aux_In{X Y}`{CDLOWOEP X, CDLOWOEP Y} : forall (ps : list (X * Y)) x y0,
  { y : Y & setoidIn (x,y) (insert_x_aux (Some y0) x ps) }.
Proof.
  induction ps; intros.
  - simpl.
    exists (right y0).
    left; split; reflexivity.
  - simpl.
    destruct a.
    destruct (lt_trich x x0) as [[Hlt|Heq]|Hgt].
    + exists (mid y0 y).
      left; reflexivity.
    + exists y.
      left.
      split; [auto|reflexivity].
    + destruct (IHps x y) as [y' Hy'].
      exists y'.
      right; exact Hy'.
Defined.

Lemma insert_x_In{X Y}`{CDLOWOEP X, CDLOWOEP Y} : forall (ps : list (X * Y)) x,
  { y : Y & setoidIn (x,y) (insert_x x ps) }.
Proof.
  destruct ps.
  - intro; simpl.
    exists (from_nat 0).
    left; split; reflexivity.
  - intro; unfold insert_x; simpl.
    destruct p.
    destruct (lt_trich x x0) as [[Hlt|Heq]|Hgt].
    + exists (left y).
      left; reflexivity.
    + exists y.
      left; split; [auto|reflexivity].
    + destruct (insert_x_aux_In ps x y) as [y' Hy'].
      exists y'.
      right; exact Hy'.
Defined.

Lemma insert_y_aux_In{X Y}`{CDLOWOEP X, CDLOWOEP Y} : forall (ps : list (X * Y)) y x0,
  { x : X & setoidIn (x,y) (insert_y_aux (Some x0) y ps) }.
Proof.
  induction ps; intros.
  - simpl.
    exists (right x0).
    left; split; reflexivity.
  - simpl.
    destruct a.
    destruct (lt_trich y y0) as [[Hlt|Heq]|Hgt].
    + exists (mid x0 x).
      left; reflexivity.
    + exists x.
      left.
      split; [reflexivity|auto].
    + destruct (IHps y x) as [x' Hx'].
      exists x'.
      right; exact Hx'.
Defined.

Lemma insert_y_In{X Y}`{CDLOWOEP X, CDLOWOEP Y} : forall (ps : list (X * Y)) y,
  { x : X & setoidIn (x,y) (insert_y y ps) }.
Proof.
  destruct ps.
  - intro; simpl.
    exists (from_nat 0).
    left; split; reflexivity.
  - intro; unfold insert_y; simpl.
    destruct p.
    destruct (lt_trich y y0) as [[Hlt|Heq]|Hgt].
    + exists (left x).
      left; reflexivity.
    + exists x.
      left; split; [reflexivity|auto].
    + destruct (insert_y_aux_In ps y x) as [x' Hx'].
      exists x'.
      right; exact Hx'.
Defined.

Lemma insert_x_aux_morph{X Y}`{CDLOWOEP X, CDLOWOEP Y} : forall (ps : list (X * Y))(p : X * Y)(x x' : X)(y : Y), x == x' -> setoidIn p (insert_x_aux (Some y) x ps) -> setoidIn p (insert_x_aux (Some y) x' ps).
Proof.
  induction ps; intros; simpl.
  - destruct p.
    simpl in H4.
    rewrite <- H3; auto.
  - destruct a.
    destruct (lt_trich x' x0) as [[Hlt|Heq]|Hgt].
    + simpl in H4.
      destruct (lt_trich x x0) as [[Glt|Geq]|Ggt].
      * destruct H4.
        ** left; rewrite H4; split; [auto|reflexivity].
        ** right; exact H4.
      * elim (lt_irref x).
        eapply lt_morph.
        ** symmetry; exact H3.
        ** symmetry; exact Geq.
        ** exact Hlt.
      * elim (lt_irref x).
        eapply lt_morph.
        ** symmetry; exact H3.
        ** reflexivity.
        ** apply (lt_trans _ x0 _); auto.
    + simpl in H4.
      destruct (lt_trich x x0) as [[Glt|Geq]|Ggt].
      * elim (lt_irref x).
        eapply lt_morph.
        ** reflexivity.
        ** rewrite H3.
           symmetry; exact Heq.
        ** exact Glt.
      * exact H4.
      * elim (lt_irref x).
        eapply lt_morph.
        ** rewrite H3.
           symmetry; exact Heq.
        ** reflexivity.
        ** exact Ggt.
    + simpl in H4.
      destruct (lt_trich x x0) as [[Glt|Geq]|Ggt].
      * elim (lt_irref x).
        eapply lt_morph.
        ** reflexivity.
        ** symmetry; exact H3.
        ** apply (lt_trans _ x0 _); auto.
      * elim (lt_irref x).
        eapply lt_morph.
        ** symmetry; exact Geq.
        ** symmetry; exact H3.
        ** exact Hgt.
      * destruct H4.
        ** left; exact H4.
        ** right; eapply IHps.
           *** exact H3.
           *** exact H4.
Qed.

Lemma insert_x_morph{X Y}`{CDLOWOEP X, CDLOWOEP Y} : forall (ps : list (X * Y))(p : X * Y)(x x' : X),
  x == x' -> setoidIn p (insert_x x ps) -> setoidIn p (insert_x x' ps).
Proof.
  destruct ps.
  - simpl; intros.
    destruct p.
    rewrite <- H3; exact H4.
  - intros; simpl.
    unfold insert_x in H4.
    simpl in H4.
    destruct p.
    unfold insert_x; simpl.
    destruct (lt_trich x x0) as [[Hlt|Heq]|Hgt].
    + destruct (lt_trich x' x0) as [[Glt|Geq]|Ggt].
      * destruct H4.
        ** destruct p0; destruct H4; left; split; auto.
           rewrite H4; auto.
        ** right; exact H4.
      * elim (lt_irref x).
        eapply lt_morph.
        ** reflexivity.
        ** rewrite H3; symmetry; exact Geq.
        ** exact Hlt.
      * elim (lt_irref x).
        eapply lt_morph.
        ** reflexivity.
        ** symmetry; exact H3.
        ** apply (lt_trans _ x0 _); auto.
    + destruct (lt_trich x' x0) as [[Glt|Geq]|Ggt].
      * elim (lt_irref x).
        eapply lt_morph.
        ** symmetry; exact H3.
        ** symmetry; exact Heq.
        ** exact Glt.
      * exact H4.
      * elim (lt_irref x).
        eapply lt_morph.
        ** symmetry; exact Heq.
        ** symmetry; exact H3.
        ** exact Ggt.
    + destruct (lt_trich x' x0) as [[Glt|Geq]|Ggt].
      * elim (lt_irref x).
        eapply lt_morph.
        ** symmetry; exact H3.
        ** reflexivity.
        ** apply (lt_trans _ x0 _); auto.
      * elim (lt_irref x).
        eapply lt_morph.
        ** rewrite H3; symmetry; exact Geq.
        ** reflexivity.
        ** exact Hgt.
      * destruct H4.
        ** left; exact H4.
        ** right; eapply insert_x_aux_morph; [exact H3|exact H4].
Qed.

Lemma insert_y_aux_morph{X Y}`{CDLOWOEP X, CDLOWOEP Y} : forall (ps : list (X * Y))(p : X * Y)(y y' : Y)(x : X), y == y' -> setoidIn p (insert_y_aux (Some x) y ps) -> setoidIn p (insert_y_aux (Some x) y' ps).
Proof.
  induction ps; intros; simpl.
  - destruct p.
    simpl in H4.
    rewrite <- H3; auto.
  - destruct a.
    destruct (lt_trich y' y0) as [[Hlt|Heq]|Hgt].
    + simpl in H4.
      destruct (lt_trich y y0) as [[Glt|Geq]|Ggt].
      * destruct H4.
        ** left; rewrite H4; split; [reflexivity|auto].
        ** right; exact H4.
      * elim (lt_irref y).
        eapply lt_morph.
        ** symmetry; exact H3.
        ** symmetry; exact Geq.
        ** exact Hlt.
      * elim (lt_irref y).
        eapply lt_morph.
        ** symmetry; exact H3.
        ** reflexivity.
        ** apply (lt_trans _ y0 _); auto.
    + simpl in H4.
      destruct (lt_trich y y0) as [[Glt|Geq]|Ggt].
      * elim (lt_irref y).
        eapply lt_morph.
        ** reflexivity.
        ** rewrite H3.
           symmetry; exact Heq.
        ** exact Glt.
      * exact H4.
      * elim (lt_irref y).
        eapply lt_morph.
        ** rewrite H3.
           symmetry; exact Heq.
        ** reflexivity.
        ** exact Ggt.
    + simpl in H4.
      destruct (lt_trich y y0) as [[Glt|Geq]|Ggt].
      * elim (lt_irref y).
        eapply lt_morph.
        ** reflexivity.
        ** symmetry; exact H3.
        ** apply (lt_trans _ y0 _); auto.
      * elim (lt_irref y).
        eapply lt_morph.
        ** symmetry; exact Geq.
        ** symmetry; exact H3.
        ** exact Hgt.
      * destruct H4.
        ** left; exact H4.
        ** right; eapply IHps.
           *** exact H3.
           *** exact H4.
Qed.

Lemma insert_y_morph{X Y}`{CDLOWOEP X, CDLOWOEP Y} : forall (ps : list (X * Y))(p : X * Y)(y y' : Y),
  y == y' -> setoidIn p (insert_y y ps) -> setoidIn p (insert_y y' ps).
Proof.
  destruct ps.
  - simpl; intros.
    destruct p.
    rewrite <- H3; exact H4.
  - intros; simpl.
    unfold insert_y in H4.
    simpl in H4.
    destruct p.
    unfold insert_y; simpl.
    destruct (lt_trich y y0) as [[Hlt|Heq]|Hgt].
    + destruct (lt_trich y' y0) as [[Glt|Geq]|Ggt].
      * destruct H4.
        ** destruct p0; destruct H4; left; split; auto.
           rewrite H5; auto.
        ** right; exact H4.
      * elim (lt_irref y).
        eapply lt_morph.
        ** reflexivity.
        ** rewrite H3; symmetry; exact Geq.
        ** exact Hlt.
      * elim (lt_irref y).
        eapply lt_morph.
        ** reflexivity.
        ** symmetry; exact H3.
        ** apply (lt_trans _ y0 _); auto.
    + destruct (lt_trich y' y0) as [[Glt|Geq]|Ggt].
      * elim (lt_irref y).
        eapply lt_morph.
        ** symmetry; exact H3.
        ** symmetry; exact Heq.
        ** exact Glt.
      * exact H4.
      * elim (lt_irref y).
        eapply lt_morph.
        ** symmetry; exact Heq.
        ** symmetry; exact H3.
        ** exact Ggt.
    + destruct (lt_trich y' y0) as [[Glt|Geq]|Ggt].
      * elim (lt_irref y).
        eapply lt_morph.
        ** symmetry; exact H3.
        ** reflexivity.
        ** apply (lt_trans _ y0 _); auto.
      * elim (lt_irref y).
        eapply lt_morph.
        ** rewrite H3; symmetry; exact Geq.
        ** reflexivity.
        ** exact Hgt.
      * destruct H4.
        ** left; exact H4.
        ** right; eapply insert_y_aux_morph; [exact H3|exact H4].
Qed.

Fixpoint partial_map{X Y}`{CDLOWOEP X, CDLOWOEP Y}(n : nat) : list (X * Y) :=
  match n with
  | 0 => []
  | S m => match even m with
           | true => insert_x (from_nat (m/2)) (partial_map m)
           | false => insert_y (from_nat (m/2)) (partial_map m)
           end
  end.

Lemma pm_eq{X Y}`{CDLOWOEP X, CDLOWOEP Y} : forall n, (partial_map n : list (X* Y)) =
  match n with
  | 0 => []
  | S m => match even m with
           | true => insert_x (from_nat (m/2)) (partial_map m)
           | false => insert_y (from_nat (m/2)) (partial_map m)
           end
  end.
Proof.
  intro.
  destruct n; reflexivity.
Qed.

Lemma X_part_map_surj{X Y}`{CDLOWOEP X, CDLOWOEP Y} : forall x : X, {y : Y & setoidIn (x,y) (partial_map (S (2*(to_nat x))))}.
Proof.
  intro.
  rewrite pm_eq.
  rewrite even_2k.
  rewrite half_2k.
  destruct (insert_x_In (partial_map (2 * to_nat x)) x) as [y Hy].
  exists y.
  eapply insert_x_morph.
  - symmetry; apply from_to.
  - exact Hy.
Defined.

Lemma Y_part_map_surj{X Y}`{CDLOWOEP X, CDLOWOEP Y} : forall y : Y, {x : X & setoidIn (x,y) (partial_map (S (S (2*(to_nat y)))))}.
Proof.
  intro.
  rewrite pm_eq.
  rewrite odd_2k1.
  rewrite half_2k1.
  destruct (insert_y_In ((partial_map (S (2 * to_nat y))) : list (X * Y)) y) as [x Hx].
  exists x.
  eapply insert_y_morph.
  - symmetry; apply from_to.
  - exact Hx.
Defined.

Lemma part_map_cumulative{X Y}`{CDLOWOEP X, CDLOWOEP Y} : forall m n p, m <= n ->
  setoidIn p (partial_map m : list (X * Y)) -> setoidIn p (partial_map n).
Proof.
  intros.
  induction H3.
  - exact H4.
  - rewrite pm_eq.
    destruct (even m0).
    + apply In_insert_x_In; auto.
    + apply In_insert_y_In; auto.
Qed.

Lemma ord_cons_x_part_map{X Y}`{CDLOWOEP X, CDLOWOEP Y} : forall n, ord_cons_x (partial_map n : list (X * Y)).
Proof.
  induction n.
  - intros [].
  - rewrite pm_eq.
    destruct (even n).
    + apply insert_x_ord_cons_x; exact IHn.
    + apply insert_y_ord_cons_x; exact IHn.
Qed.

Lemma ord_cons_y_part_map{X Y}`{CDLOWOEP X, CDLOWOEP Y} : forall n, ord_cons_y (partial_map n : list (X * Y)).
Proof.
  induction n.
  - intros [].
  - rewrite pm_eq.
    destruct (even n).
    + apply insert_x_ord_cons_y; exact IHn.
    + apply insert_y_ord_cons_y; exact IHn.
Qed.

Lemma part_map_functional_xy{X Y}`{CDLOWOEP X, CDLOWOEP Y} : forall (n : nat)(x x' : X)(y y' : Y),
  x == x' -> setoidIn (x,y) (partial_map n) -> setoidIn (x',y') (partial_map n) -> y == y'.
Proof.
  intros.
  destruct (in_index _ _ H4) as [i Hi].
  destruct (in_index _ _ H5) as [j Hj].
  destruct (Fin_trich _ i j) as [[Heq|Hlt]|Hgt].
  - rewrite Heq in Hi.
    rewrite Hi in Hj.
    destruct Hj; auto.
  - destruct (partial_map n ! i) eqn:G.
    destruct (partial_map n ! j) eqn:G0.
    pose (ord_cons_x_part_map n i j Hlt).
    rewrite G,G0 in l; simpl in l.
    destruct Hi,Hj.
    elim (lt_irref x).
    eapply lt_morph.
    + exact H6.
    + rewrite H3; exact H8.
    + exact l.
  - destruct (partial_map n ! i) eqn:G.
    destruct (partial_map n ! j) eqn:G0.
    pose (ord_cons_x_part_map n j i Hgt).
    rewrite G,G0 in l; simpl in l.
    destruct Hi,Hj.
    elim (lt_irref x).
    eapply lt_morph.
    + rewrite H3; exact H8.
    + exact H6.
    + exact l.
Qed.

Lemma part_map_functional_yx{X Y}`{CDLOWOEP X, CDLOWOEP Y} : forall (n : nat)(y y' : Y)(x x' : X),
  y == y' -> setoidIn (x,y) (partial_map n) -> setoidIn (x',y') (partial_map n) -> x == x'.
Proof.
  intros.
  destruct (in_index _ _ H4) as [i Hi].
  destruct (in_index _ _ H5) as [j Hj].
  destruct (Fin_trich _ i j) as [[Heq|Hlt]|Hgt].
  - rewrite Heq in Hi.
    rewrite Hi in Hj.
    destruct Hj; auto.
  - destruct (partial_map n ! i) eqn:G.
    destruct (partial_map n ! j) eqn:G0.
    pose (ord_cons_y_part_map n i j Hlt).
    rewrite G,G0 in l; simpl in l.
    destruct Hi,Hj.
    elim (lt_irref y).
    eapply lt_morph.
    + exact H7.
    + rewrite H3; exact H9.
    + exact l.
  - destruct (partial_map n ! i) eqn:G.
    destruct (partial_map n ! j) eqn:G0.
    pose (ord_cons_y_part_map n j i Hgt).
    rewrite G,G0 in l; simpl in l.
    destruct Hi,Hj.
    elim (lt_irref y).
    eapply lt_morph.
    + rewrite H3; exact H9.
    + exact H7.
    + exact l.
Qed.

Section Cantor.

Variable X : Type.
Variable sX : Setoid X.
Variable oX : Ord X.
Variable cX : CDLOWOEP oX.

Variable Y : Type.
Variable sY : Setoid Y.
Variable oY : Ord Y.
Variable cY : CDLOWOEP oY.

Theorem Cantor : Iso oX oY.
Proof.
  exists (fun x => projT1 (X_part_map_surj x)) (fun y => projT1 (Y_part_map_surj y)).
  - intros.
    destruct (X_part_map_surj x); destruct (X_part_map_surj x'); simpl.
    eapply (@part_map_functional_xy X Y).
    + exact H.
    + exact s.
    + rewrite <- (to_nat_morph _ _ H) in s0.
      exact s0.
  - intros.
    destruct (Y_part_map_surj y); destruct (Y_part_map_surj y'); simpl.
    eapply (@part_map_functional_yx X Y).
    + exact H.
    + exact s.
    + rewrite <- (to_nat_morph _ _ H) in s0.
      exact s0.
  - intro.
    destruct (Y_part_map_surj y) as [x Hx]; simpl.
    destruct (X_part_map_surj x) as [y' Hy']; simpl.
    pose (a := S (S (2 * to_nat y))); fold a in Hx.
    pose (b := S (2 * to_nat x)); fold b in Hy'.
    eapply (@part_map_functional_xy X Y).
    + reflexivity.
    + exact (@part_map_cumulative X Y _ _ _ _ _ _ b (Nat.max a b) (x,y') (Nat.le_max_r _ _) Hy').
    + eapply part_map_cumulative.
      * apply Nat.le_max_l.
      * exact Hx.
  - intro.
    destruct (X_part_map_surj x) as [y Hy]; simpl.
    destruct (Y_part_map_surj y) as [x' Hx']; simpl.
    pose (a := (S (2 * to_nat x))); fold a in Hy.
    pose (b := (S (S (2 * to_nat y)))); fold b in Hx'.
    eapply (@part_map_functional_yx X Y).
    + reflexivity.
    + exact (@part_map_cumulative X Y _ _ _ _ _ _ b (Nat.max a b) (x',y) (Nat.le_max_r _ _) Hx').
    + eapply part_map_cumulative.
      * apply Nat.le_max_l.
      * exact Hy.
  - intros.
    destruct (X_part_map_surj x) as [y Hy]; simpl.
    destruct (X_part_map_surj x') as [y' Hy']; simpl.
    pose (a := S (2 * to_nat x)); fold a in Hy.
    pose (b := S (2 * to_nat x')); fold b in Hy'.
    pose (part_map_cumulative a (Nat.max a b) (x,y) (Nat.le_max_l _ _) Hy).
    pose (part_map_cumulative b (Nat.max a b) (x',y') (Nat.le_max_r _ _) Hy').
    destruct (in_index _ _ s) as [i Hi].
    destruct (in_index _ _ s0) as [j Hj].
    destruct (Fin_trich _ i j) as [[Geq|Glt]|Ggt].
    + rewrite Geq in Hi.
      rewrite Hi in Hj.
      destruct Hj.
      elim (lt_irref x).
      eapply lt_morph.
      * reflexivity.
      * symmetry; exact H0.
      * exact H.
    + destruct (partial_map (Nat.max a b) ! i) eqn:Gi.
      destruct (partial_map (Nat.max a b) ! j) eqn:Gj.
      pose (@ord_cons_y_part_map X Y _ _ _ _ _ _ (Nat.max a b) i j Glt).
      rewrite Gi,Gj in l; simpl in l.
      destruct Hi,Hj.
      eapply lt_morph.
      * exact H1.
      * exact H3.
      * exact l.
    + destruct (partial_map (Nat.max a b) ! i) eqn:Gi.
      destruct (partial_map (Nat.max a b) ! j) eqn:Gj.
      pose (@ord_cons_x_part_map X Y _ _ _ _ _ _ (Nat.max a b) j i Ggt).
      rewrite Gi,Gj in l; simpl in l.
      destruct Hi,Hj.
      elim (lt_irref x0).
      apply (lt_trans _ x1 _).
      * eapply lt_morph.
        ** symmetry; exact H0.
        ** symmetry; exact H2. 
        ** exact H.
      * exact l.
  - intros.
    destruct (Y_part_map_surj y) as [x Hx]; simpl.
    destruct (Y_part_map_surj y') as [x' Hx']; simpl.
    pose (a := S (S (2 * to_nat y))); fold a in Hx.
    pose (b := S (S (2 * to_nat y'))); fold b in Hx'.
    pose (part_map_cumulative a (Nat.max a b) (x,y) (Nat.le_max_l _ _) Hx).
    pose (part_map_cumulative b (Nat.max a b) (x',y') (Nat.le_max_r _ _) Hx').
    destruct (in_index _ _ s) as [i Hi].
    destruct (in_index _ _ s0) as [j Hj].
    destruct (Fin_trich _ i j) as [[Geq|Glt]|Ggt].
    + rewrite Geq in Hi.
      rewrite Hi in Hj.
      destruct Hj.
      elim (lt_irref y).
      eapply lt_morph.
      * reflexivity.
      * symmetry; exact H1.
      * exact H.
    + destruct (partial_map (Nat.max a b) ! i) eqn:Gi.
      destruct (partial_map (Nat.max a b) ! j) eqn:Gj.
      pose (@ord_cons_x_part_map X Y _ _ _ _ _ _ (Nat.max a b) i j Glt).
      rewrite Gi,Gj in l; simpl in l.
      destruct Hi,Hj.
      eapply lt_morph.
      * exact H0.
      * exact H2.
      * exact l.
    + destruct (partial_map (Nat.max a b) ! i) eqn:Gi.
      destruct (partial_map (Nat.max a b) ! j) eqn:Gj.
      pose (@ord_cons_y_part_map X Y _ _ _ _ _ _ (Nat.max a b) j i Ggt).
      rewrite Gi,Gj in l; simpl in l.
      destruct Hi,Hj.
      elim (lt_irref y).
      apply (lt_trans _ y' _).
      * exact H.
      * eapply lt_morph.
        ** exact H3.
        ** exact H1.
        ** exact l.
Defined.

End Cantor.

Instance CantorISO{X Y}`{oX : Ord X}`{oY : Ord Y}`{@CDLOWOEP _ _ oX, @CDLOWOEP _ _ oY} : Iso oX oY.
Proof.
  apply Cantor; auto.
Defined.