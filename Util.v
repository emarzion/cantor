Require Import List Omega SetoidClass Recdef.
Import ListNotations.

Require Import Class.

Fixpoint even n :=
  match n with
  | 0 => true
  | S m => negb (even m)
  end.

Lemma even_odd_half : forall n, (even n = true -> exists k, 2 * k = n) /\
  (even n = false -> exists k, S (2 * k) = n).
Proof.
  induction n; split; intros.
  - exists 0; auto.
  - discriminate.
  - simpl in H.
    destruct IHn.
    destruct H1 as [k Hk].
    + destruct (even n); [discriminate | auto].
    + exists (S k).
      omega.
  - destruct IHn.
    destruct H0 as [k Hk].
    + simpl in H.
      destruct (even n); [auto | discriminate].
    + exists k; omega.
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
  - auto.
  - simpl; rewrite <- plus_n_Sm; simpl.
    simpl in IHk; rewrite IHk; auto.
Qed.

Lemma odd_2k1 : forall k, even (S (2 * k)) = false.
Proof.
  induction k.
  - auto.
  - simpl; rewrite <- plus_n_Sm.
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

Section Fin.

Fixpoint Fin(n : nat) : Type :=
  match n with
  | 0 => Empty_set
  | S m => unit + Fin m
  end.

Fixpoint Fin_le{n} : Fin n -> Fin n -> Prop :=
  match n with
  | 0 => fun i _ => match i with end
  | S m => fun i j => match i,j with
                      | inl _, inl _ => False
                      | inl _, inr _ => True
                      | inr _, inl _ => False
                      | inr i', inr j' => Fin_le i' j'
                      end
  end.

Lemma Fin_le_irref : forall (n : nat)(i : Fin n), ~ Fin_le i i.
Proof.
  induction n.
  - intros [].
  - destruct i as [[]|j].
    + tauto.
    + apply IHn.
Qed.

Lemma Fin_le_trans : forall (n : nat)(i j k : Fin n), Fin_le i j -> Fin_le j k -> Fin_le i k.
Proof.
  induction n; intros.
  - destruct i.
  - destruct i as [|i']; destruct k as [|k'].
    + destruct j; auto.
    + exact I.
    + destruct j; auto.
    + destruct j as [|j'].
      * destruct H.
      * apply (IHn _ j' _); auto.
Qed.

Lemma Fin_trich : forall (n : nat)(i j : Fin n), {i = j} + {Fin_le i j} + {Fin_le j i}.
Proof.
  induction n.
  - intros [].
  - intros [[]|i'] [[]|j'].
    + left; left; auto.
    + left; right; exact I.
    + right; exact I.
    + destruct (IHn i' j') as [[Heq|Hle]|Hge].
      * left; left; congruence.
      * left; right; exact Hle.
      * right; exact Hge.
Qed.

Fixpoint list_index{X}(xs : list X){struct xs} : Fin (length xs) -> X :=
  match xs return Fin (length xs) -> X with
  | [] => fun i => match i with end
  | y::ys => fun i => match i with
                      | inl _ => y
                      | inr j => list_index ys j
                      end
  end.

Lemma in_index : forall {X}`{Eq X}(xs : list X)(x : X), setoidIn x xs -> exists (i : Fin (length xs)),
  list_index xs i == x.
Proof.
  induction xs; intros.
  - destruct H1.
  - destruct H1.
    + exists (inl tt); simpl; symmetry; auto.
    + destruct (IHxs x H1) as [i Hi].
      exists (inr i); auto.
Qed.

End Fin.