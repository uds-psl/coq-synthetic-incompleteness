From Undecidability.Synthetic Require Import Definitions Undecidability. From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
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

Definition tenumerator X (f : nat -> option X) := forall x, exists k, f k = Some x.
Definition tenumerable X := exists (f : nat -> option X), tenumerator f.

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
  Variable (sentences : Type) (neg : sentences -> sentences).
  Hypothesis sentences_discrete : forall (s1 s2 : sentences), (s1 = s2) + (s1 <> s2).
  Variable sentences_enumerator : nat -> option sentences.
  Hypothesis sentences_enumerable : tenumerator sentences_enumerator.

  Variable (provable : sentences -> Prop) (provable_enumerator : nat -> option sentences).
  Hypothesis provable_enumerable : enumerator provable_enumerator provable.

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
  Lemma neg_no_fixpoint_comp : completeness -> forall s, s <> neg s.
  Proof.
    intros complete s. destruct (complete s).
    - now apply neg_no_fixpoint.
    - now apply neg_no_fixpoint2.
  Qed.

  Lemma undeepen_provability s : completeness -> ~provable s -> provable (neg s).
  Proof.
    intros complete Hnprov. now destruct (complete s).
  Qed.
  Lemma deepen_provability s : provable (neg s) -> ~provable s.
  Proof.
    intros Hprovn Hnprov. apply (consistent s); eassumption.
  Qed.

  Lemma ldecidable_provable : completeness -> ldecidable provable.
  Proof.
    intros complete s. destruct (complete s); intuition.
  Qed.

  Lemma provable_coenumerable : completeness -> enumerable (fun s => ~provable s).
  Proof.
    intros complete.
    unshelve eexists.
    { intros [k1 k2] % unembed.
      destruct (provable_enumerator k1) as [p|]. 2: exact None.
      destruct (sentences_enumerator k2) as [s|]. 2: exact None.
      destruct (sentences_discrete p (neg s)).
      - exact (Some s).
      - exact None. }
    intros s. split.
    - intros Hprov.
      apply undeepen_provability, provable_enumerable in Hprov as [k1 Hk1]. 2: assumption.
      destruct (sentences_enumerable s) as [k2 Hk2].
      exists (embed (k1, k2)). rewrite embedP. cbn.
      destruct provable_enumerator, sentences_enumerator. 2-4: discriminate.
      destruct sentences_discrete; congruence.
    - intros [k Hk].
      destruct (unembed k) as [k1 k2]. cbn in Hk.
      destruct (provable_enumerator k1) eqn:H, (sentences_enumerator k2). 2-4: discriminate.
      destruct sentences_discrete as [Heq|?]. 2: discriminate.
      apply deepen_provability. apply provable_enumerable. exists k1.
      congruence.
  Qed.
  Lemma decidable_provable : completeness -> decidable provable.
  Proof.
    intros complete.
    apply weakPost.
    - exists (fun '(s1, s2) => if sentences_discrete s1 s2 then true else false).
      intros [s1 s2]. split; destruct sentences_discrete; auto.
    - apply ldecidable_provable, complete.
    - now exists provable_enumerator.
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


  Section representable_predicate.
    Variable (T : Type) (P : T -> Prop).
    Variable repr : T -> sentences.
    Section strongly_representable_predicate.
      Hypothesis Hrepr : strongly_represents_classic P repr.

      Lemma srepr_fn : function T out.
      Proof.
        unshelve eexists.
        - intros t k.
          destruct (provable_enumerator k) as [s|]. 2: exact None.
          destruct (sentences_discrete s (repr t)).
          + exact (Some ACC).
          + destruct (sentences_discrete s (neg (repr t))).
            * exact (Some REJ).
            * exact None.
        - intros x k1 k2 y1 y2. cbn.
          destruct (provable_enumerator k1) eqn:H1. 2: congruence.
          destruct (provable_enumerator k2) eqn:H2. 2: congruence.
          repeat destruct sentences_discrete; try congruence.
          all: edestruct consistent; apply provable_enumerable.
          + exists k1. eassumption.
          + exists k2. congruence.
          + exists k2. eassumption.
          + exists k1. congruence.
      Defined.

      Lemma srepr_fn_correct t : (P t -> accepts srepr_fn t) /\ (~P t -> rejects srepr_fn t).
      Proof.
        split.
        - intros pt. unfold accepts, returns.
          assert (provable (repr t)) as [k Hk] % provable_enumerable by intuition.
          exists k. cbv. rewrite Hk.
          destruct sentences_discrete; easy.
        - intros Hnpt. unfold rejects, returns.
          assert (provable (neg (repr t))) as [k Hk] % provable_enumerable by intuition.
          exists k. cbv. rewrite Hk.
          destruct sentences_discrete as [Heq | ?].
          + destruct (@neg_no_fixpoint (repr t)).
            * apply provable_enumerable. exists k. congruence.
            * easy.
          + destruct sentences_discrete; easy.
      Qed.
    End strongly_representable_predicate.

    Section weakly_representable_predicate.
      Variable (Tdis : forall (t1 t2 : T), (t1 = t2) + (t1 <> t2)) (Tenumerable : exists (f : nat -> T), forall t, exists n, f n = t).

      Hypothesis Hrepr : weakly_represents P repr.
      Hypothesis complete : completeness.

      Lemma wrepr_dec : decidable P.
      Proof.
        eapply weakly_represents_dec; eassumption.
      Qed.
      Lemma wrepr_ldec : ldecidable P.
      Proof.
        destruct (wrepr_dec) as [f Hf].
        intros t. destruct (f t) eqn:H.
        - left. firstorder.
        - right. intros ? % Hf. congruence.
      Qed.
      Local Lemma wrepr_srepr : strongly_represents_classic P repr.
      Proof.
        now apply weakly_strongly_represents_classic.
      Qed.

      Lemma wrepr_fn_correct_iff t : (P t <-> accepts srepr_fn t) /\ (~P t <-> rejects srepr_fn t).
      Proof.
        split; split. 1, 3: now apply srepr_fn_correct, weakly_strongly_represents_classic.
        - intros Hacc.
          destruct (wrepr_ldec t) as [H|H]. 1: easy.
          apply srepr_fn_correct in H. 2: apply wrepr_srepr.
          edestruct accepts_rejects; eassumption.
        - destruct (wrepr_ldec t) as [H|H]. 2: easy.
          apply srepr_fn_correct in H. 2: apply wrepr_srepr.
          intros H'.
          edestruct accepts_rejects; eassumption.
      Qed.
    End weakly_representable_predicate.
  End representable_predicate.


  Section halting.
    Hypothesis halting_weakly_representable : weakly_representable (fun (f : nat -> bool) => exists n, f n = true).
    Hypothesis no_halting : ~decidable (fun (f : nat -> bool) => exists n, f n = true).

    Lemma halting_incomplete : completeness -> False.
    Proof.
      intros complete. destruct halting_weakly_representable as [f Hf].
      eapply no_halting, weakly_represents_dec; eassumption.
    Qed.
  End halting.

  Section cg.
    Variable (T : Type).

    Variable repr : function T out -> T -> out -> sentences.
    Hypothesis Hrepr : forall (f: function T out) (t : T) (y : out),
        (returns f t y -> provable (repr f t y)) /\
        forall y', returns f t y -> y' <> y -> ~provable (repr f t y').

    Hypothesis provable_decidable : forall s, (provable s) + ~provable s.

    Definition frepr_fn : T -> function T out -> bool.
    Proof.
      intros t g.
      destruct (provable_decidable (repr g t ACC)).
      + exact true.
      + exact false.
    Defined.

    Lemma frepr_fn_correct : forall g t,
          (accepts g t -> frepr_fn t g = true) /\
            (rejects g t -> frepr_fn t g = false).
    Proof.
      intros g t. split.
      - intros H % Hrepr. cbv.
        now destruct provable_decidable as [H'|H'].
      - intros Hrej.
        assert (~provable (repr g t ACC)) as H.
        { eapply Hrepr. 1: exact Hrej. congruence. }
        cbv. now destruct provable_decidable as [H'|H'].
    Qed.
  End cg.


End Abstract.
