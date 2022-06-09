From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts.
From Undecidability.Shared Require Import embed_nat Dec.
Require Import Vector.
Require Import Undecidability.Shared.Libs.DLW.Vec.vec.
Require Import ConstructiveEpsilon.
From Equations Require Import Equations.

Local Set Implicit Arguments.
Local Unset Strict Implicit.



Ltac first s := only 1: s.
Ltac last s := cycle -1; only 1: (s + fail).


Definition mu (p : nat -> Prop) :
  (forall x, dec (p x)) -> ex p -> sig p.
Proof.
  apply constructive_indefinite_ground_description_nat_Acc.
Qed.
Lemma vec_1_inv X (v : vec X 1) : {a & v = a ## vec_nil}.
Proof.
  repeat depelim v. eauto.
Qed.
Lemma vec_2_inv X (v : vec X 2) : { a & { b & v = a ## b ## vec_nil} }.
Proof.
  repeat depelim v. eauto.
Qed.
Lemma vec_singleton {X} (a b : X) : Vector.In a (Vector.cons _ b _ (Vector.nil _)) -> a = b.
Proof.
  inversion 1.
  { reflexivity. }
  inversion H2.
Qed.

Definition core_valid {Y : Type} (core : nat -> option Y) :=
  forall y1 y2 k1 k2, core k1 = Some y1 -> core k2 = Some y2 -> y1 = y2.

Record part (Y : Type) : Type := mkPart {
  core : nat -> option Y;
  valid : core_valid core 
}.
Arguments mkPart {_} _ _.
Arguments valid [_] _.
Definition part_eval {Y : Type} (p : part Y) (y : Y) :=
  exists k, (core p) k = Some y.
Notation "p ▷ y" := (part_eval p y) (at level 30).
Notation "'partial' f " := ({| core := f; valid := _ |}) (at level 30, only printing).

Definition part_stationary Y (p : part Y) :=
  forall y k1 k2, p.(core) k1 = Some y -> k2 >= k1 -> p.(core) k2 = Some y.

Lemma totalise_part X (p : part X) : (exists y, p ▷ y) -> {y & p ▷ y}.
Proof.
  intros H.
  assert (exists k, exists y, p.(core) k = Some y) as H'%mu by firstorder.
  - destruct H' as [k H'']. destruct (p.(core) k) as [x|] eqn:Heq.
    + firstorder.
    + exfalso. now destruct H''.
  - intros k. destruct (p.(core) k) as [x|] eqn:H''.
    + left. eauto.
    + right. now intros [y Hy].
Qed.
Notation "A -\ B" := (A -> part B) (at level 30).


Lemma totalise X Y (f : X -\ Y) : (forall x, exists y, f x ▷ y) -> forall x, {y & f x ▷ y}.
Proof.
  intros H x. apply totalise_part, H.
Qed.

Lemma part_functional {X : Type} (p : part X) (x y : X) : p ▷ x -> p ▷ y -> x = y.
Proof.
  intros [k1 H1] [k2 H2].
  eapply (p.(valid)); eassumption.
Qed.





