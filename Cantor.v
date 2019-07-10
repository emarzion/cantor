Require Import SetoidClass List PeanoNat Omega.
Import ListNotations.

Require Import Class Util.

Inductive Situation X :=
  | Empty : Situation X (* no other points *)
  | Leftmost : X -> Situation X (* leftmost, giving the element immediately to the right *)
  | Middle : X -> X -> Situation X (* somewhere in the middle, giving the elemens immediately to the left and right *)
  | Rightmost : X -> Situation X. (* rightmost, giving the element immediately to the left *)

Arguments Empty {_}.
Arguments Leftmost {_} _.
Arguments Middle {_} _ _.
Arguments Rightmost {_} _.

Definition get_situation_by{X Y}`{Ord Y}(f : X -> Y)(xs : list X)(y : Y) : Situation X :=
  let (lower,upper) := partby f xs y in
    match maxby f lower, minby f upper with
    | None,None => Empty
    | None,Some x => Leftmost x
    | Some x,None => Rightmost x
    | Some x1, Some x2 => Middle x1 x2
    end.

Section Cantor.

Variable X : Type.
Variable sX : Setoid X.
Variable oX : Ord X.
Variable cX : CDLOWOEP oX.

Variable Y : Type.
Variable sY : Setoid Y.
Variable oY : Ord Y.
Variable cY : CDLOWOEP oY.

Lemma fst_dec : forall x (p : X * Y), 
  { fst p == x } + { ~ fst p == x }.
Proof.
  intros; apply dec_eq.
Defined.

Lemma fst_dec_setoid : forall ps (x x' : X),
  x == x' -> searchBy (fst_dec x) ps = searchBy (fst_dec x') ps.
Proof.
  induction ps.
  auto.
  intros.
  simpl.
  repeat destruct fst_dec.
  reflexivity.
  elim n.
  rewrite e; auto.
  elim n.
  rewrite e; symmetry; auto.
  apply IHps.
  exact H.
Qed.

Lemma fst_dec_search : forall ps (x x' : X) y,
  searchBy (fst_dec x) ps = Some (x',y) -> x == x'.
Proof.
  intros.
  induction ps.
  discriminate.
  simpl in H.
  destruct fst_dec in H.
  inversion H.
  destruct a.
  simpl in e.
  inversion H1.
  rewrite <- H2.
  symmetry; auto.
  auto.
Qed.

Lemma fst_dec_search_not_None : forall ps (x x' : X) y, x == x' ->
  setoidIn (x',y) ps -> ~ searchBy (fst_dec x) ps = None.
Proof.
  induction ps; intros.
  destruct H0.
  destruct H0.
  simpl.
  destruct a.
  unfold fst_dec.
  unfold fst.
  destruct dec_eq.
  discriminate.
  elim n.
  destruct H0.
  rewrite H.
  symmetry; auto.
  simpl.
  unfold fst_dec.
  destruct a.
  unfold fst.
  destruct dec_eq.
  discriminate.
  apply (IHps x x' y); auto.
Qed.

Lemma snd_dec : forall y (p : X * Y), 
  { snd p == y } + { ~ snd p == y }.
Proof.
  intros; apply dec_eq.
Defined.

Lemma snd_dec_setoid : forall ps (y y' : Y),
  y == y' -> searchBy (snd_dec y) ps = searchBy (snd_dec y') ps.
Proof.
  induction ps.
  auto.
  intros.
  simpl.
  repeat destruct snd_dec.
  reflexivity.
  elim n.
  rewrite e; auto.
  elim n.
  rewrite e; symmetry; auto.
  apply IHps.
  exact H.
Qed.

Lemma snd_dec_search : forall ps (y y' : Y) x,
  searchBy (snd_dec y) ps = Some (x,y') -> y == y'.
Proof.
  intros.
  induction ps.
  discriminate.
  simpl in H.
  destruct snd_dec in H.
  inversion H.
  destruct a.
  simpl in e.
  inversion H1.
  rewrite <- H3.
  symmetry; auto.
  auto.
Qed.

Lemma snd_dec_search_not_None : forall ps x (y y' : Y), y == y' ->
  setoidIn (x,y') ps -> ~ searchBy (snd_dec y) ps = None.
Proof.
  induction ps; intros.
  destruct H0.
  destruct H0.
  simpl.
  destruct a.
  unfold snd_dec.
  unfold snd.
  destruct dec_eq.
  discriminate.
  elim n.
  destruct H0.
  rewrite H.
  symmetry; auto.
  simpl.
  unfold snd_dec.
  destruct a.
  unfold snd.
  destruct dec_eq.
  discriminate.
  apply (IHps x y y'); auto.
Qed.

Fixpoint partial_map n : list (X * Y) :=
  match n with
  | 0 => []
  | S m => let ps := partial_map m in
    match even m with
    (* X stage *)
    | true => let x_i := from_nat (m/2) in
      match searchBy (fst_dec x_i) ps with
      | Some _ => ps (* element already mapped, do nothing *)
      | None => match get_situation_by fst ps x_i with
                | Empty => (x_i,from_nat 0)::ps
                | Leftmost (_,y) => (x_i, left y)::ps
                | Middle (_,y1) (_,y2) => (x_i, mid y1 y2)::ps
                | Rightmost (_,y) => (x_i, right y)::ps
                end
      end
    (* Y stage *)
    | false => let y_i := from_nat (m/2) in
      match searchBy (snd_dec y_i) ps with
      | Some _ => ps
      | None => match get_situation_by snd ps y_i with
                | Empty => (from_nat 0,y_i)::ps
                | Leftmost (x,_) => (left x, y_i)::ps
                | Middle (x1,_) (x2,_) => (mid x1 x2, y_i)::ps
                | Rightmost (x,_) => (right x, y_i)::ps
                end
      end
    end
  end.

Lemma pm_eq : forall m, partial_map (S m) =
  let ps := partial_map m in
    match even m with
    (* X stage *)
    | true => let x_i := from_nat (m/2) in
      match searchBy (fst_dec x_i) ps with
      | Some _ => ps (* element already mapped, do nothing *)
      | None => match get_situation_by fst ps x_i with
                | Empty => (x_i,from_nat 0)::ps
                | Leftmost (_,y) => (x_i, left y)::ps
                | Middle (_,y1) (_,y2) => (x_i, mid y1 y2)::ps
                | Rightmost (_,y) => (x_i, right y)::ps
                end
      end
    (* Y stage *)
    | false => let y_i := from_nat (m/2) in
      match searchBy (snd_dec y_i) ps with
      | Some _ => ps
      | None => match get_situation_by snd ps y_i with
                | Empty => (from_nat 0,y_i)::ps
                | Leftmost (x,_) => (left x, y_i)::ps
                | Middle (x1,_) (x2,_) => (mid x1 x2, y_i)::ps
                | Rightmost (x,_) => (right x, y_i)::ps
                end
      end
    end.
Proof.
  auto.
Qed.


Lemma X_part_map_surj : forall x, {y : Y & setoidIn (x,y) (partial_map (S (2*(to_nat x))))}.
Proof.
  intro.
  destruct (searchBy (fst_dec x) (partial_map (2 * to_nat x))) as [[x' y]|] eqn:G.
  exists y.
  rewrite pm_eq.
  rewrite even_2k.
  rewrite half_2k.
  cbv zeta.
  rewrite (fst_dec_setoid _ _ _ (from_to x)).
  rewrite G.
  pose (fst_dec_search _ _ _ _ G).
  apply (setoidIn_equiv (x',y)).
  split; [symmetry; auto | reflexivity].
  apply (searchBy_in (fst_dec x)); exact G.
  unfold partial_map.
  rewrite even_2k.
  fold partial_map.
  rewrite half_2k.
  rewrite (fst_dec_setoid _ _ _ (from_to x)).
  rewrite G.
  destruct get_situation_by.
  exists (from_nat 0).
  left.
  split.
  symmetry; apply from_to.
  reflexivity.
  destruct p.
  exists (left y).
  left.
  split.
  symmetry; apply from_to.
  reflexivity.
  destruct p,p0.
  exists (mid y y0).
  left.
  split.
  symmetry; apply from_to.
  reflexivity.
  destruct p.
  exists (right y).
  left.
  split.
  symmetry; apply from_to.
  reflexivity.
Defined.

Lemma Y_part_map_surj : forall y, {x : X & setoidIn (x,y) (partial_map (S (S (2*(to_nat y)))))}.
Proof.
  intro.
  destruct (searchBy (snd_dec y) (partial_map (S(2 * to_nat y)))) as [[x y']|] eqn:G.
  exists x.
  rewrite pm_eq.
  rewrite odd_2k1.
  rewrite half_2k1.
  cbv zeta.
  rewrite (snd_dec_setoid _ _ _ (from_to y)).
  rewrite G.
  pose (snd_dec_search _ _ _ _ G).
  apply (setoidIn_equiv (x,y')).
  split; [reflexivity | symmetry; auto].
  apply (searchBy_in (snd_dec y)); exact G.
  rewrite pm_eq.
  rewrite odd_2k1.
  rewrite half_2k1.
  cbv zeta.
  rewrite (snd_dec_setoid _ _ _ (from_to y)).
  rewrite G.
  destruct get_situation_by.
  exists (from_nat 0).
  left.
  split.
  reflexivity.
  symmetry; apply from_to.
  destruct p.
  exists (left x).
  left.
  split.
  reflexivity.
  symmetry; apply from_to.
  destruct p,p0.
  exists (mid x x0).
  left.
  split.
  reflexivity.
  symmetry; apply from_to.
  destruct p.
  exists (right x).
  left.
  split.
  reflexivity.
  symmetry; apply from_to.
Defined.

Lemma part_map_cumulative : forall m n p, m <= n ->
  setoidIn p (partial_map m) -> setoidIn p (partial_map n).
Proof.
  intros.
  induction H.
  exact H0.
  rewrite pm_eq.
  cbv zeta.
  destruct even.
  destruct searchBy.
  exact IHle.
  destruct get_situation_by.
  right; auto.
  destruct p0; right; auto.
  destruct p0; destruct p1; right; auto.
  destruct p0; right; auto.
  destruct searchBy.
  exact IHle.
  destruct get_situation_by.
  right; auto.
  destruct p0; right; auto.
  destruct p0; destruct p1; right; auto.
  destruct p0; right; auto.
Qed.

Lemma part_map_ne : forall n,
  partial_map (S n) <> [].
Proof.
  intro n.
  rewrite pm_eq.
  destruct even.
  cbv zeta.
  destruct searchBy eqn:G.
  pose (searchBy_in _ _ _ G).
  intro.
  rewrite H in s.
  destruct s.
  destruct get_situation_by.
  discriminate.
  destruct p; discriminate.
  destruct p,p0; discriminate.
  destruct p; discriminate.
  cbv zeta.
  destruct searchBy eqn:G.
  pose (searchBy_in _ _ _ G).
  intro.
  rewrite H in s.
  destruct s.
  destruct get_situation_by.
  discriminate.
  destruct p; discriminate.
  destruct p,p0; discriminate.
  destruct p; discriminate.
Qed.

Lemma part_map_ord_x : forall n x x' y y', x << x' -> setoidIn (x,y) (partial_map n) -> setoidIn (x',y') (partial_map n) -> y << y'.
Proof.
  induction n; intros.
  destruct H0.
Admitted.

Lemma part_map_ord_y : forall n x x' y y', y << y' -> setoidIn (x,y) (partial_map n) -> x << x'.
Proof.
Admitted.

Lemma part_map_add_new_x : forall m p,
  partial_map (S m) = p :: partial_map m -> forall x y,
  setoidIn (x,y) (partial_map m) -> ~ fst p == x.
Proof.
  intros.
  rewrite pm_eq in H.
  cbv zeta in H.
  destruct (even m) eqn:E.
  assert (fst p == (from_nat (m / 2))).
Admitted.

(*

  destruct (searchBy (fst_dec (from_nat (m/2))) (partial_map m)) eqn:G.
  absurd (length (partial_map m) = length (p :: partial_map m)).
  simpl; omega.
  rewrite <- H; auto.
  destruct get_situation_by; destruct p; unfold fst.
  inversion H; reflexivity.
  destruct p0.
  inversion H; reflexivity.
  destruct p0,p1.
  inversion H; reflexivity.
  destruct p0.
  inversion H; reflexivity.
  rewrite H1.
  destrut (
  
   inversion H; unfold fst; auto.
  absurd (length (partial_map m) = length (p :: partial_map m)).
  simpl; omega.
  rewrite <- H; auto.
  destruct m.
  simpl in H.
  destruct H0.
  destruct (get_situation_by fst (partial_map (S m)) (from_nat (S m / 2))) eqn:G0.
  Search _ partial_map.
  destruct p0.
  assert (p = (from_nat (S m / 2) , left y0)).
  inversion H; auto.
  rewrite H1.
  unfold fst.
  intro.
  Search _ searchBy.
  apply (fst_dec_search_not_None _ _ _ _ H2 H0 G).
  destruct p0,p1.
  intro.
*)
Lemma part_map_add_new_y : forall m p,
  partial_map (S m) = p :: partial_map m -> forall x y,
  setoidIn (x,y) (partial_map m) -> ~ snd p == y.
Proof.
Admitted.

Lemma part_map_add : forall m, partial_map (S m) = partial_map m \/
  exists p, partial_map (S m) = p :: partial_map m.
Proof.
  intro.
  rewrite pm_eq.
  cbv zeta.
  destruct (even m).
  destruct searchBy.
  left; auto.
  right.
  destruct get_situation_by.
  eexists; auto.
  destruct p; eexists; auto.
  destruct p, p0; eexists; auto.
  destruct p; eexists; auto.
  destruct searchBy.
  left; auto.
  right.
  destruct get_situation_by.
  eexists; auto.
  destruct p; eexists; auto.
  destruct p, p0; eexists; auto.
  destruct p; eexists; auto.
Qed.

(* Lemma part_map_in_stage : forall n p, setoidIn p (partial_map n) ->
  exists m, S m <= n /\  partial_map (S m) = p :: partial_map m.
Proof.
  induction n; intros.
  destruct H.
  rewrite pm_eq in H.
  cbv zeta in H.
  destruct (even n).
  destruct (searchBy (fst_dec (from_nat (n/2))) (partial_map n)).
  destruct (IHn p H) as [m [Hm1 Hm2]].
  exists m; split.
  omega.
  auto.
  destruct get_situation_by eqn:G in H.
  unfold get_situation_by in G.
  destruct (partby fst (partial_map n) (from_nat (n/2))) eqn:G1.
  destruct (maxby fst l) eqn:G2.
  destruct (minby fst l0); discriminate.
Admitted.
 *)

Lemma part_map_functional_xy : forall n x x' y y', x == x' ->
  setoidIn (x,y) (partial_map n) -> setoidIn (x',y') (partial_map n) -> y == y'.
Proof.
  induction n; intros.
  destruct H0.
  destruct (part_map_add n) as [G|[p G]].
  rewrite G in H0,H1.
  exact (IHn x x' y y' H H0 H1).
  rewrite G in H0,H1.
  destruct H0.
  destruct H1.
  rewrite <- H1 in H0.
  destruct H0; auto.
  elim (part_map_add_new_x _ _ G _ _ H1).
  destruct p; simpl.
  destruct H0; rewrite <- H; symmetry; auto.
  destruct H1.
  elim (part_map_add_new_x _ _ G _ _ H0).
  destruct p; simpl.
  rewrite H; destruct H1; symmetry; auto.
  exact (IHn x x' y y' H H0 H1).
Qed.

Lemma part_map_functional_yx : forall n x x' y y', y == y' ->
  setoidIn (x,y) (partial_map n) -> setoidIn (x',y') (partial_map n) -> x == x'.
Proof.
  induction n; intros.
  destruct H0.
  destruct (part_map_add n) as [G|[p G]].
  rewrite G in H0,H1.
  exact (IHn x x' y y' H H0 H1).
  rewrite G in H0,H1.
  destruct H0.
  destruct H1.
  rewrite <- H1 in H0.
  destruct H0; auto.
  elim (part_map_add_new_y _ _ G _ _ H1).
  destruct p; simpl.
  destruct H0; rewrite <- H; symmetry; auto.
  destruct H1.
  elim (part_map_add_new_y _ _ G _ _ H0).
  destruct p; simpl.
  rewrite H; destruct H1; symmetry; auto.
  exact (IHn x x' y y' H H0 H1).
Qed.

(* 
Lemma situation_not_Empty : forall n p,
  get_situation_by fst (partial_map (S n)) p <> Empty.
Proof.
  intros.
  unfold get_situation_by.
  destruct partby eqn:G.
  destruct maxby eqn:G1.
  destruct minby; discriminate.
  destruct minby eqn:G2.
  discriminate.
  
  rewrite pm_eq.
  destruct (even n).
  cbv zeta.
  destruct searchBy eqn:G.
  unfold
 *)

Theorem Cantor : Iso oX oY.
Proof.
  exists (fun x => projT1 (X_part_map_surj x))
         (fun y => projT1 (Y_part_map_surj y)).
  -
  intros.
  repeat destruct X_part_map_surj; simpl.
  rewrite (to_nat_morph _ _ H) in s.
  apply (part_map_functional_xy _ _ _ _ _ H s s0).
  -
  intros.
  repeat destruct Y_part_map_surj; simpl.
  rewrite (to_nat_morph _ _ H) in s.
  apply (part_map_functional_yx _ _ _ _ _ H s s0).
  -
  intro.
  destruct Y_part_map_surj.
  simpl.
  destruct X_part_map_surj.
  simpl.
  pose (m := S (S (2 * to_nat y))); fold m in s.
  pose (n := S (2 * to_nat x)); fold n in s0.
  destruct (Nat.le_ge_cases m n).
  apply (part_map_functional_xy _ _ _ _ _ (reflexivity x) s0).
  apply (part_map_cumulative _ _ _ H); auto.
  symmetry; apply (part_map_functional_xy _ _ _ _ _ (reflexivity x) s).
  apply (part_map_cumulative _ _ _ H); auto.
  -
  intro.
  destruct X_part_map_surj.
  simpl.
  destruct Y_part_map_surj.
  simpl.
  pose (m := S (2 * to_nat x)); fold m in s.
  pose (n := S (S (2 * to_nat x0))); fold n in s0.
  destruct (Nat.le_ge_cases m n).
  apply (part_map_functional_yx _ _ _ _ _ (reflexivity x0) s0).
  apply (part_map_cumulative _ _ _ H); auto.
  symmetry; apply (part_map_functional_yx _ _ _ _ _ (reflexivity x0) s).
  apply (part_map_cumulative _ _ _ H); auto.
  -
  intros.
  repeat destruct X_part_map_surj; simpl.
  pose (m := S (2 * to_nat x)); fold m in s.
  pose (n := S (2 * to_nat x')); fold n in s0.
  destruct (Nat.le_ge_cases m n).
  apply (part_map_ord_x n _ _ _ _ H).
  apply (part_map_cumulative m); auto.
  exact s0.
  apply (part_map_ord_x m _ _ _ _ H).
  exact s.
  apply (part_map_cumulative n); auto.
  -
  intros.
  repeat destruct Y_part_map_surj; simpl.
  pose (m := S (S (2 * to_nat y))); fold m in s.
  pose (n := S (S (2 * to_nat y'))); fold n in s0.
  destruct (Nat.le_ge_cases m n).
  apply (part_map_ord_y n _ _ _ _ H).
  apply (part_map_cumulative m); auto.
  apply (part_map_ord_y m _ _ _ _ H).
  auto.
Defined.

End Cantor.

Instance CantorISO{X Y}`{oX : Ord X}`{oY : Ord Y}`{@CDLOWOEP _ _ oX, @CDLOWOEP _ _ oY} : Iso oX oY.
Proof.
  apply Cantor; auto.
Defined.