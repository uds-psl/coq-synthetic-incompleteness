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


(* Utilities for vectors *)
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



(** * Synthetic computability *)
(** Partial functions **)

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
(* Notation for evaluation *)
Notation "p ▷ y" := (part_eval p y) (at level 30).
(* Print only notation to avoid printing validity proofs *)
Notation "'partial' f " := ({| core := f; valid := _ |}) (at level 30, only printing).
(* Notation for partial functions *)
Notation "A -\ B" := (A -> part B) (at level 30).

(* Totalisation of total partial functions *)
Definition mu (p : nat -> Prop) :
  (forall x, dec (p x)) -> ex p -> sig p.
Proof.
  apply constructive_indefinite_ground_description_nat_Acc.
Qed.

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

Theorem totalise X Y (f : X -\ Y) : (forall x, exists y, f x ▷ y) -> forall x, {y & f x ▷ y}.
Proof.
  intros H x. apply totalise_part, H.
Qed.
Definition partialise X Y (f : X -> Y) : X -\ Y.
Proof.
  intros x. exists (fun _ => Some (f x)). congruence.
Defined.

(* Utilities for working with partial functions *)
Lemma part_functional {X : Type} (p : part X) (x y : X) : p ▷ x -> p ▷ y -> x = y.
Proof.
  intros [k1 H1] [k2 H2].
  eapply (p.(valid)); eassumption.
Qed.

(* Composition of parts with total or partial functions *)
Program Definition comp_part_total Y Z (f : Y -> Z) (g : part Y) : part Z.
Proof.
  unshelve eexists.
  { intros k. exact (match g.(core) k with Some y => Some (f y) | None => None end). }
  intros z1 z2 k1 k2 H1 H2. 
  destruct (core _ k1) as [y1|] eqn:Hk1, (core _ k2) as [y2|] eqn:Hk2; try congruence.
  enough (y1 = y2) by congruence.
  eapply part_functional; eexists; eassumption.
Defined.
Program Definition comp_part_partial Y Z (f : Y -\ Z) (g : part Y) : part Z.
Proof.
  unshelve eexists.
  { intros k. exact (match g.(core) k with Some y => (f y).(core) k | None => None end). }
  intros z1 z2 k1 k2 H1 H2. 
  destruct (core _ k1) as [y1|] eqn:Hk1, (core _ k2) as [y2|] eqn:Hk2; try congruence.
  assert (y1 = y2) as ->.
  { eapply part_functional with (p := g); eexists; eassumption. }
  eapply part_functional; eexists; eassumption.
Defined.





(* Disjoint and semi-decidable predicates can be recursively separated *)
(* Note that enumerability and discreteness suffice for semi-decidability *)
Lemma enumerable_separable (X : Type) (P1 P2 : X -> Prop) : 
  (forall x, P1 x -> P2 x -> False) ->
  semi_decidable P1 -> semi_decidable P2 -> exists f : X -\ bool,
  (forall x, P1 x <-> f x ▷ true) /\
  (forall x, P2 x <-> f x ▷ false).
Proof.
  intros Pdisjoint [f1 Hf1] [f2 Hf2].
  unshelve eexists.
  { intros x. unshelve eexists.
    { intros k. refine (if f1 x k then Some true else if f2 x k then Some false else None). }
    intros y1 y2 k1 k2 H1 H2.
    destruct (f1 x k1) eqn:H11, (f2 x k1) eqn:H21, (f1 x k2) eqn:H12, (f2 x k2) eqn:H22; try congruence.
    all: destruct (Pdisjoint x); apply Hf1+apply Hf2; eauto. }
 split; intros x; split.
 - intros [k Hk]%Hf1. exists k. cbn. now rewrite Hk.
 - intros [k Hk]. apply Hf1. exists k. cbn in Hk. now destruct (f1 x k), (f2 x k).
 - intros [k Hk]%Hf2. exists k. cbn. destruct (f1 x k) eqn:Hk'.
   + destruct (Pdisjoint x); apply Hf1 + apply Hf2; eauto.
   + now rewrite Hk.
 - intros [k Hk]. apply Hf2. exists k. cbn in Hk. now destruct (f1 x k), (f2 x k).
Qed.


