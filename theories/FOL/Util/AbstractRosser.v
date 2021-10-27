(** * Abstract Incompleteness using Rosser's Trick *)

From Undecidability.Synthetic Require Import Definitions Undecidability.
From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
From Undecidability.Synthetic Require Import ListEnumerabilityFacts MoreEnumerabilityFacts.
From Undecidability.Shared Require Import Dec embed_nat.
From Equations Require Import Equations.
Require Import ConstructiveEpsilon.
Require Import List.
Import ListNotations.

Local Set Implicit Arguments.
Local Unset Strict Implicit.



Notation "'Sigma' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.
Definition pi1 {A : Type} {P : A -> Type} (e : Sigma x, P x): A := let (x, _) := e in x.

Definition tenumerable X := exists (f : nat -> X), forall x, exists k, f k = x.


Definition mu (p : nat -> Prop) :
  (forall x, dec (p x)) -> ex p -> sig p.
Proof.
  apply constructive_indefinite_ground_description_nat_Acc.
Qed.

Definition ldecidable {X} (p : X -> Prop) :=
  forall x, p x \/ ~ p x.

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

Section s.
  Variable (T R : Type).
  Definition function := Sigma (f : T -> nat -> option R), forall x k k' y y',
        f x k = Some y -> f x k' = Some y' -> y = y'.

  Variable (f : function).

  Definition returns (x : T) (y : R) : Prop := exists k, pi1 f x k = Some y.
  Definition diverges (x : T) : Prop := forall k, pi1 f x k = None.
  Definition halts (x : T) : Prop := exists y, returns x y.

  Lemma returns_functional (x : T) (y1 y2 : R) : returns x y1 -> returns x y2 -> y1 = y2.
  Proof.
    intros (k & Hk) (k' & Hk').
    destruct f as [f' Hf].
    exact (Hf x k k' y1 y2 Hk Hk').
  Qed.
End s.

Arguments returns {T R}.
Arguments diverges {T R}.
Arguments halts {T R}.

Inductive out : Type := ACC | REJ.
Section s.
  Variable (T : Type) (f : function T out).

  Definition accepts (x : T) : Prop := returns f x ACC.
  Definition rejects (x : T) : Prop := returns f x REJ.

  Lemma accepts_rejects (x : T) : accepts x -> rejects x -> False.
  Proof.
    intros Ha Hr. enough (ACC = REJ) by discriminate. eapply returns_functional; eassumption.
  Qed.
End s.

Arguments accepts {T}.
Arguments rejects {T}.


Section Abstract.
  Variable sentences : Type.
  Variable neg : sentences -> sentences.
  Hypothesis sentences_discrete : forall (s1 s2 : sentences), (s1 = s2) + (s1 <> s2).
  Hypothesis sentences_enumerable : tenumerable sentences.


  (* Replacing this with an enumerable predicate makes things difficult
     because the enumerator must be computational (not under an exists) *)
  Variable (provable_enumerator : nat -> sentences).
  Definition provable s := exists k, provable_enumerator k = s.

  Hypothesis consistent : forall s, provable s -> provable (neg s) -> False.
  Arguments consistent s : clear implicits.
  Definition completeness := forall s, provable s \/ provable (neg s).

  Lemma neg_no_fixpoint : forall s, provable s -> s <> neg s.
  Proof.
    intros s Hs Heq. apply (consistent s); congruence.
  Qed.
  Lemma neg_no_fixpoint2 : forall s, provable (neg s) -> s <> neg s.
  Proof.
    intros s Hs Heq. apply (consistent s); congruence.
  Qed.

  Lemma undeepen_provability s : completeness -> ~provable s -> provable (neg s).
  Proof.
    intros complete Hnprov. now destruct (complete s).
  Qed.
  Lemma deepen_provability s : provable (neg s) -> ~provable s.
  Proof.
    intros Hprovn Hnprov. apply (consistent s); eassumption.
  Qed.
  Lemma unprovable_nonempty : completeness -> exists s, ~provable s.
  Proof.
    intros complete.
    destruct sentences_enumerable as [sentences_enumerator Hsent].
    destruct (complete (sentences_enumerator 0)).
    - exists (neg (sentences_enumerator 0)). intros H1.
      now destruct (consistent (sentences_enumerator 0)).
    - exists (sentences_enumerator 0). intros H1.
      now destruct (consistent (sentences_enumerator 0)).
  Qed.

  Lemma ldecidable_provable : completeness -> ldecidable provable.
  Proof.
    intros complete s. destruct (complete s); intuition.
  Qed.

  Lemma provable_enumerable : senumerable provable.
  Proof.
    now exists provable_enumerator.
  Qed.
  Lemma provable_coenumerable : completeness -> senumerable (fun s => ~provable s).
  Proof.
    intros complete.
    destruct sentences_enumerable as [sentences_enumerator Hsent].
    apply enumerable_senumerable. 1: now apply unprovable_nonempty.
    unshelve eexists.
    { intros [k1 k2] % unembed.
      destruct (sentences_discrete (provable_enumerator k1) (neg (sentences_enumerator k2))).
      - exact (Some (sentences_enumerator k2)).
      - exact None. }
    intros s. split.
    - intros [k1 Hk1] % undeepen_provability. 2: exact complete.
      destruct (Hsent s) as [k2 Hk2].
      exists (embed (k1, k2)). rewrite embedP. cbn.
      rewrite Hk1, Hk2. now destruct sentences_discrete.
    - intros [k Hk].
      destruct (unembed k) as [k1 k2]. cbn in Hk.
      destruct sentences_discrete as [Heq|?]. 2: discriminate.
      injection Hk as <-.
      apply deepen_provability. now exists k1.
  Qed.
  Lemma decidable_provable : completeness -> decidable provable.
  Proof.
    intros complete.
    apply sWeakPost.
    - unfold discrete, decidable, decider, reflects.
      exists (fun '(s1, s2) => if sentences_discrete s1 s2 then true else false).
      intros [s1 s2]. split; destruct sentences_discrete; auto.
    - apply ldecidable_provable, complete.
    - apply provable_enumerable.
    - apply provable_coenumerable, complete.
  Qed.

  Section representability_prop.
    Variable T : Type.
    Variable P : T -> Prop.
    Variable f : T -> sentences.

    Definition weakly_represents :=
      forall t, P t <-> provable (f t).
    Definition strongly_represents :=
      forall t, (P t -> provable (f t)) /\ (~provable (neg (f t)) -> P t).
    Definition strongly_represents_classic :=
      forall t, (P t -> provable (f t)) /\ (~P t -> provable (neg (f t))).

    Lemma strongly_weakly_represents : strongly_represents -> weakly_represents.
    Proof.
      intros Hf t. split.
      - apply Hf.
      - intros Hprov. apply Hf.
        intros Hnprov. eapply consistent.
        + exact Hprov.
        + exact Hnprov.
    Qed.
    Lemma weakly_strongly_represents :
      completeness -> weakly_represents -> strongly_represents.
    Proof.
      intros complete Hf t. split.
      - apply Hf.
      - intros Hnprov. apply Hf.
        destruct (complete (f t)).
        + assumption.
        + contradiction.
    Qed.
    Lemma weakly_strongly_represents_classic :
      completeness -> weakly_represents -> strongly_represents_classic.
    Proof.
      intros complete Hf t. split.
      - apply Hf.
      - intros Hnpt. destruct (complete (f t)); firstorder.
    Qed.

    Lemma weakly_represents_dec : completeness -> weakly_represents -> decidable P.
    Proof.
      intros complete Hf.
      destruct (decidable_provable complete) as [g Hg].
      exists (fun t => g (f t)). firstorder.
    Qed.
  End representability_prop.
  Arguments weakly_represents {T}.
  Arguments strongly_represents_classic {T}.
  Definition weakly_representable {T} (P : T -> Prop) := exists f, weakly_represents P f.
  Definition strongly_representable_classic {T} (P : T -> Prop) := exists f, strongly_represents_classic P f.

  Section acceptance.
    Variable (T : Type) (t : T).
    (* NOTE: This is not consistent guessing anymore, the acceptance problem *)
    Definition acceptance_pred (g : function T out) : Prop := (accepts g t).
    (* TODO (why) does implication suffice here? In our old formulation it did as well*)
    (* NOTE This is some kind of representability on a meta-level? *)
    Hypothesis no_acceptance : ~decidable acceptance_pred.

    Lemma acceptance_false : completeness -> weakly_representable acceptance_pred -> False.
    Proof.
      intros complete [f Hf].
      eapply no_acceptance, weakly_represents_dec; eassumption.
    Qed.
  End acceptance.

End Abstract.
