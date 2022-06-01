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


Lemma decidable_equiv X p q : (forall (x : X), p x <-> q x) -> decidable p -> decidable q.
Proof.
  firstorder.
Qed.
Lemma enumerable_equiv X (P Q : X -> Prop) :
  (forall x, P x <-> Q x) -> enumerable P -> enumerable Q.
Proof.
  intros H [f Hf]. exists f. intros x. rewrite <- H. apply Hf.
Qed.

Definition ldecidable X (p : X -> Prop) := forall x, p x \/ ~p x.

Definition mu (p : nat -> Prop) :
  (forall x, dec (p x)) -> ex p -> sig p.
Proof.
  apply constructive_indefinite_ground_description_nat_Acc.
Qed.

Theorem weakPost X (p : X -> Prop) :
  discrete X -> ldecidable p -> enumerable p -> enumerable (fun x => ~ p x) -> decidable p.
Proof.
  intros [E] % discrete_iff Hl [f Hf] [g Hg].
  eapply decidable_iff. econstructor. intros x.
  assert (exists n, f n = Some x \/ g n = Some x) by (destruct (Hl x); firstorder).
  destruct (@mu (fun n => f n = Some x \/ g n = Some x)) as [n HN]; trivial.
  - intros n. exact _.
  - decide (f n = Some x); decide (g n = Some x); firstorder.
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

(* TODO rename *)
Lemma total_part_decidable (p : part bool) : (exists y, p ▷ y) -> {y | p ▷ y}.
Proof.
  intro Hy. 
  assert (exists k, (core p) k = Some true \/ (core p) k = Some false) as H.
  { destruct Hy as ( [] & k & H); firstorder. }
  apply mu in H as [k Hk].
  - destruct (core p k) as [[]|] eqn:H.
    + now exists true, k. 
    + now exists false, k.
    + exists false. now destruct Hk.
  - intros x. exact _.
Qed.

Lemma part_functional {X : Type} (p : part X) (x y : X) : p ▷ x -> p ▷ y -> x = y.
Proof.
  intros [k1 H1] [k2 H2].
  eapply (p.(valid)); eassumption.
Qed.


Notation "A -\ B" := (A -> part B) (at level 30).

