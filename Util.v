Require Import List Omega SetoidClass Recdef.
Import ListNotations.

Require Import Class.

Definition setoid_inj{X Y}`{Setoid Y}(f : X -> Y) := forall x x', f x == f x' -> x = x'.

Definition setoid_inj2{X Y}`{Setoid X}(f : X -> Y) := forall x x', f x = f x' -> x == x'.

Fixpoint searchBy{X P}(Pd : forall x : X, {P x} + {~ P x})(xs : list X) : option X :=
  match xs with
  | [] => None
  | x::ys => if Pd x then Some x else searchBy Pd ys
  end.

Lemma searchBy_in{X P}`{Eq X} : forall (Pd : forall x:X, {P x} + {~ P x}) x xs,
  searchBy Pd xs = Some x -> setoidIn x xs.
Proof.
  induction xs; intros.
  discriminate.
  simpl in H1.
  destruct (Pd a).
  left.
  inversion H1; reflexivity.
  right; auto.
Qed.

Fixpoint even n :=
  match n with
  | 0 => true
  | S m => negb (even m)
  end.

Lemma even_odd_half : forall n, (even n = true -> exists k, 2 * k = n) /\
  (even n = false -> exists k, S (2 * k) = n).
Proof.
  induction n; split; intros.
  exists 0; auto.
  discriminate.
  simpl in H.
  destruct IHn.
  destruct H1 as [k Hk].
  destruct (even n); [discriminate | auto].
  exists (S k).
  omega.
  destruct IHn.
  destruct H0 as [k Hk].
  simpl in H.
  destruct (even n); [auto | discriminate].
  exists k; omega.
Qed.

Lemma even_half : forall n, even n = true -> exists k, 2 * k = n.
Proof.
  intros; apply even_odd_half; auto.
Qed.

Lemma odd_half : forall n, even n = false -> exists k, S (2 * k) = n.
Proof.
  intros; apply even_odd_half; auto.
Qed.

Lemma even_2k : forall k, even (2 * k) = true.
Proof.
  induction k.
  auto.
  simpl; rewrite <- plus_n_Sm; simpl.
  simpl in IHk; rewrite IHk. auto.
Qed.

Lemma odd_2k1 : forall k, even (S (2 * k)) = false.
Proof.
  induction k.
  auto.
  simpl; rewrite <- plus_n_Sm.
  simpl; simpl in IHk.
  rewrite IHk; auto.
Qed.

Lemma half_2k : forall k, (2*k)/2 = k.
Proof.
  intro.
  rewrite Nat.mul_comm.
  rewrite Nat.div_mul; omega.
Qed.

Lemma half_2k1 : forall k, (S (2 * k))/2 = k.
Proof.
  intro.
  pose (Nat.add_b2n_double_div2 true).
  simpl Nat.b2n in e.
  apply e.
Qed.

Fixpoint partby{X Y}`{Ord Y}(f : X -> Y)(xs : list X) y : (list X * list X) :=
  match xs with
  | [] => ([],[])
  | x::xs' => let (below,above) := partby f xs' y in
    match lt_trich (f x) y with
    | inleft _ => (x::below,above)
    | inright _ => (below,x::above)
    end
  end.

Lemma partby_ne{X Y }`{Ord Y} : forall (f : X -> Y)(xs : list X) y,
  xs <> [] -> partby f xs y <> ([],[]).
Proof.
  intros.
  destruct xs.
  elim H1; reflexivity.
  simpl.
  destruct partby.
  destruct lt_trich; discriminate.
Qed.

Fixpoint maxby{X Y}`{Ord Y}(f : X -> Y)(xs : list X) : option X :=
  match xs with
  | [] => None
  | x::xs' => match maxby f xs' with
              | None => Some x
              | Some x' => match lt_trich (f x) (f x') with
                           | inleft _ => Some x'
                           | _ => Some x
                           end
              end
  end.

Fixpoint minby{X Y}`{Ord Y}(f : X -> Y)(xs : list X) : option X :=
  match xs with
  | [] => None
  | x::xs' => match minby f xs' with
              | None => Some x
              | Some x' => match lt_trich (f x) (f x') with
                           | inleft _ => Some x
                           | _ => Some x'
                           end
              end
  end.

Lemma maxby_none{X Y}`{Ord Y} : forall (f : X -> Y) xs,
  maxby f xs = None -> xs = [].
Proof.
  induction xs; intros.
  reflexivity.
  simpl in H1.
  destruct maxby in H1.
  destruct lt_trich; discriminate.
  discriminate.
Qed.

Lemma minby_none{X Y}`{Ord Y} : forall (f : X -> Y) xs,
  minby f xs = None -> xs = [].
Proof.
  induction xs; intros.
  reflexivity.
  simpl in H1.
  destruct minby in H1.
  destruct lt_trich; discriminate.
  discriminate.
Qed.

Lemma maxby_Some_in{X Y}`{Ord Y} : forall (f : X -> Y) xs x,
  maxby f xs = Some x -> In x xs.
Proof.
  induction xs; intros.
  simpl in H1; discriminate.
  simpl in H1.
  destruct (maxby f xs) eqn:G.
  destruct lt_trich in H1.
  right; exact (IHxs _ H1).
  left; inversion H1; auto.
  left; inversion H1; congruence.
Qed.

Lemma maxby_max{X Y}`{Ord Y} : forall (f : X -> Y) xs x,
  maxby f xs = Some x -> forall x', In x' xs -> f x' << f x \/ f x' == f x.
Proof.
  induction xs; intros.
  discriminate.
  simpl in H1.
  destruct (maxby f xs) eqn:G.
  destruct (lt_trich (f a) (f x0)).
  destruct s.
  destruct H2.
  left.
  inversion H1; congruence.
  auto.
  destruct H2.
  right.
  inversion H1; congruence.
  auto.
  destruct H2.
  right.
  inversion H1.
  rewrite <- H2, <- H4; reflexivity.
  inversion H1.
  left.
  rewrite H4 in H1.
  destruct (IHxs x0 eq_refl x').
  auto.
  apply (@lt_trans Y H H0 _ (f x0)).
  exact H3.
  rewrite <- H4; exact l.
  rewrite <- H4.
  apply (@lt_morph Y H H0 (f x0) (f x') (f a) (f a)).
  symmetry; exact H3.
  reflexivity.
  exact l.
  destruct H2.
  right.
  rewrite <- H2.
  inversion H1.
  reflexivity.
  destruct xs.
  destruct H2.
  simpl in G.
  destruct (maxby f xs).
  destruct lt_trich in G; discriminate.
  discriminate G.
Qed.

Lemma minby_min{X Y}`{Ord Y} : forall (f : X -> Y) xs x,
  minby f xs = Some x -> forall x', In x' xs -> f x << f x' \/ f x' == f x.
Proof.
  induction xs; intros.
  discriminate.
  simpl in H1.
  destruct (minby f xs) eqn:G.
  destruct (lt_trich (f a) (f x0)).
  destruct s.
  destruct H2.
  right.
  inversion H1.
  rewrite <- H2, <- H4; reflexivity.
  destruct (IHxs x0 eq_refl x' H2).
  left.
  inversion H1.
  rewrite H5 in l.
  apply (@lt_trans Y H H0 (f x) (f x0)); auto.
  left.
  inversion H1.
  rewrite <- H5.
  apply (@lt_morph Y H H0 (f a) (f a) (f x0) (f x')).
  reflexivity.
  symmetry; auto.
  exact l.
  destruct H2.
  right.
  rewrite <- H2.
  inversion H1.
  reflexivity.
  destruct (IHxs x0 eq_refl x' H2).
  left.
  inversion H1.
  rewrite <- H5.
  apply (@lt_morph Y H H0 (f x0) (f a) (f x') (f x')).
  symmetry; auto.
  reflexivity.
  exact H3.
  right.
  inversion H1.
  rewrite H5 in e.
  rewrite e; auto.
  destruct H2.
  left.
  inversion H1; congruence.
  apply IHxs; auto.
  destruct xs.
  destruct H2.
  right.
  inversion H1.
  rewrite <- H2, <- H4; reflexivity.
  destruct H2.
  simpl in G.
  destruct minby in G.
  destruct lt_trich in G; discriminate.
  discriminate.
Qed.