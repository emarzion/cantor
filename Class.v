Require Import SetoidClass List Omega.
Import ListNotations.

Definition nat_dec_eq : forall x y : nat, {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

Instance SetoidProd{X Y}`{Setoid X,Setoid Y} : Setoid (X * Y) :=
  {|
    equiv := fun '(x1,y1) '(x2,y2) => x1 == x2 /\ y1 == y2
  |}.
Proof.
  split.
  intros [x y]; split; reflexivity.
  intros [x y] [x' y'] [H1 H2]; split; symmetry; auto.
  intros [x y] [x' y'] [x'' y''] [H1 H2] [H3 H4]; split.
  rewrite H1; auto.
  rewrite H2; auto.
Defined.

Class Eq X `{Setoid X} := {
  dec_eq : forall x x', {x == x'} + {~ x == x'}
  }.

Instance EqProd{X Y}`{Eq X, Eq Y} : Eq (X * Y).
Proof.
  constructor; intros [x1 y1] [x2 y2].
  destruct (dec_eq x1 x2).
  destruct (dec_eq y1 y2).
  left; split; auto.
  right; intros [_ G]; contradiction.
  right; intros [G _]; contradiction.
Defined.

Fixpoint setoidIn{X}`{Eq X} (x : X) xs : Prop :=
  match xs with
  | [] => False
  | y::ys => x == y \/ setoidIn x ys
  end.

Lemma dec_setoidIn{X}`{Setoid X}`{Eq X} : forall (x : X) xs, {setoidIn x xs} + {~setoidIn x xs}.
Proof.
  induction xs.
  right; simpl; tauto.
  destruct (dec_eq x a).
  left; simpl; tauto.
  destruct IHxs.
  left; simpl; tauto.
  right; simpl; tauto.
Defined.

Lemma setoidIn_equiv{X}`{Setoid X}`{Eq X} : forall (x x' : X) xs,
  x == x' -> setoidIn x xs -> setoidIn x' xs.
Proof.
  induction xs; intros.
  destruct H3.
  destruct H3.
  left.
  rewrite <- H2; auto.
  right.
  apply IHxs; auto.
Qed.

Class Ord X `{Setoid X} := {
  lt : X -> X -> Prop;
  lt_morph : forall x x' y y', x == x' -> y == y' ->
    lt x y -> lt x' y';
  lt_irref : forall x, ~ lt x x;
  lt_trans : forall x y z, lt x y -> lt y z -> lt x z;
  lt_trich : forall x y, {lt x y} + {x == y} + {lt y x}
  }.

Arguments lt {_} {_} {_} _ _.
Infix "<<" := lt (at level 20).

Class Iso {X} {Y} `{Setoid X,Setoid Y} (oX : Ord X)(oY : Ord Y) := {
  forward : X -> Y;
  forward_morph : forall x x', x == x' -> forward x == forward x';
  back : Y -> X;
  back_morph : forall y y', y == y' -> back y == back y';
  fb_eq : forall y, forward (back y) == y;
  bf_eq : forall x, back (forward x) == x;
  forward_ord_morph : forall x x', x << x' -> forward x << forward x';
  back_ord_morph : forall y y', y << y' -> back y << back y'
  }.

Class CDLOWOEP {X} `{Setoid X} (O:Ord X) := {

  (*countable*)
  to_nat : X -> nat;
  from_nat : nat -> X;
  to_nat_morph : forall x x', x == x' -> to_nat x = to_nat x';
  to_from : forall n, to_nat (from_nat n) = n;
  from_to : forall x, from_nat (to_nat x) == x;

  (*dense*)
  mid : X -> X -> X;
  mid_morph : forall x x' y y', x == x' -> y == y' -> mid x y == mid x' y';
  mid_lt_left : forall x x', x << x' -> x << mid x x';
  mid_lt_right : forall x x', x << x' -> mid x x' << x';

  (*without endpoints*)
  left : X -> X;
  left_morph : forall x x', x == x' -> left x == left x';
  left_lt: forall x, left x << x;
  right : X -> X;
  right_morph : forall x x', x == x' -> right x == right x';
  right_lt : forall x, x << right x

  }.

(* don't use this, use Ord instead *)
Instance CDLOWOEP_Eq{X}`{sX : Setoid X}(oX : Ord X)`{@CDLOWOEP X sX oX} : Eq X.
Proof.
  constructor; intros.
  destruct (nat_dec_eq (to_nat x) (to_nat x')).
  left.
  rewrite <- (from_to x), <- (from_to x'), e; reflexivity.
  right; intro; apply n.
  apply to_nat_morph; auto.
Defined.