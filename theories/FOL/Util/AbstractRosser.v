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

(* TODO remove _all_ decidables and so on *)


Notation "'Sigma' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.
Definition pi1 {A : Type} {P : A -> Type} (e : Sigma x, P x): A := let (x, _) := e in x.

Definition tenumerator X (f : nat -> X) := forall x, exists k, f k = x.
Definition tenumerable X := exists (f : nat -> X), tenumerator f.
(* Slightly weaker notion of enumerability, but easier to handle *)
Definition senumerator {X} (f : nat -> X) P := forall x, P x <-> exists n, f n = x.
Definition senumerable {X} (P : X -> Prop) := exists f, senumerator f P.

Lemma senumerable_enumerable X (P : X -> Prop) : senumerable P -> enumerable P.
Proof.
  intros [f Hf]. exists (fun x => Some (f x)).
  intros x. split.
  - intros Hpx. apply Hf in Hpx.
    destruct Hpx as [n Hn]. exists n. congruence.
  - intros [k Hk].
    destruct (Hf x) as [H1 H2].
    apply H2. exists k. congruence.
Qed.
Lemma enumerable_senumerable X (P : X -> Prop) : (exists x, P x) -> enumerable P -> senumerable P.
Proof.
  intros [a Ha] [f Hf].
  exists (fix g n := match n with 0 => a | S n => match f n with None => g n | Some x => x end end).
  intros x. split.
  - intros Hpx. destruct (Hf x) as [H1 _].
    destruct (H1 Hpx) as [n Hn]. exists (S n). now rewrite Hn.
  - intros [n Hn]. induction n.
    + congruence.
    + destruct (f n) eqn:H.
      * apply Hf. exists n. congruence.
      * apply IHn, Hn.
Qed.


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
(* TODO weaken post to use sigmas instead of existentials *)
Theorem sWeakPost X (p : X -> Prop) :
  discrete X -> ldecidable p -> senumerable p -> senumerable (fun x => ~ p x) -> decidable p.
Proof.
  auto using weakPost, senumerable_enumerable.
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
  Variable sentences_enumerator : nat -> sentences.
  Hypothesis sentences_enumerable : tenumerator sentences_enumerator.

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
  Lemma unprovable_nonempty : completeness -> exists s, ~provable s.
  Proof.
    intros complete.
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
    apply enumerable_senumerable. 1: now apply unprovable_nonempty.
    unshelve eexists.
    { intros [k1 k2] % unembed.
      destruct (sentences_discrete (provable_enumerator k1) (neg (sentences_enumerator k2))).
      - exact (Some (sentences_enumerator k2)).
      - exact None. }
    intros s. split.
    - intros [k1 Hk1] % undeepen_provability. 2: exact complete.
      destruct (sentences_enumerable s) as [k2 Hk2].
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


  Section representable_predicate.
    Variable (T : Type) (P : T -> Prop).
    Variable repr : T -> sentences.
    Section strongly_representable_predicate.
      Hypothesis Hrepr : strongly_represents_classic P repr.

      (* TODO work on an abstract machine model using Church's Thesis *)
      (* TODO this as a Coq function using Posts Theorem *)
      Lemma srepr_fn : function T out.
      Proof.
        unshelve eexists.
        - intros t k.
          destruct (sentences_discrete (provable_enumerator k) (repr t)).
          + exact (Some ACC).
          + destruct (sentences_discrete (provable_enumerator k) (neg (repr t))).
            * exact (Some REJ).
            * exact None.
        - intros x k1 k2 y1 y2. cbn.
          repeat destruct sentences_discrete; try congruence.
          all: edestruct consistent.
          + exists k1. eassumption.
          + exists k2. congruence.
          + exists k2. eassumption.
          + exists k1. congruence.
      Defined.

      Lemma srepr_fn_correct t : (P t -> accepts srepr_fn t) /\ (~P t -> rejects srepr_fn t).
      Proof.
        split.
        - intros pt. unfold accepts, returns.
          assert (provable (repr t)) as [k Hk] by intuition.
          exists k. cbv. rewrite Hk.
          destruct sentences_discrete; easy.
        - intros Hnpt. unfold rejects, returns.
          assert (provable (neg (repr t))) as [k Hk] by intuition.
          exists k. cbv. rewrite Hk.
          destruct sentences_discrete as [Heq | ?].
          + destruct (@neg_no_fixpoint (repr t)).
            * exists k. congruence.
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
    Variable (T : Type)
             (Tdis : forall (t1 t2 : T), (t1 = t2) + (t1 <> t2))
             (Tenumerable : Sigma (f : nat -> T), forall t, exists n, f n = t).

    Variable repr : function T out -> T -> out -> sentences.
    Hypothesis Hrepr : forall (f: function T out) (t : T) (y : out),
        (returns f t y -> provable (repr f t y)) /\
        forall y', returns f t y -> y' <> y -> provable (neg (repr f t y')).

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
        destruct provable_decidable as [H'|H'].
        + reflexivity.
        + contradiction.
      - intros Hrej.
        assert (provable (neg (repr g t ACC))) as H.
        { eapply Hrepr. 1: exact Hrej. congruence. }
        cbv. destruct provable_decidable as [H'|H'].
        + destruct (consistent _ H' H).
        + reflexivity.
    Qed.
  End cg.

  Section CT.
    (* TODO see above *)
    Hypothesis provable_decidable : forall s, (provable s) + ~provable s.

    (* I need to encode partial functions... *)
    Variable phi : nat -> nat -> nat -> option nat.
    Hypothesis CT : forall f, exists c, forall x, match f x with
                                     None => forall n, phi c x n = None
                                   | Some y => exists n, phi c x n = Some y
                                   end.
    (* Hypothesis SI : forall c x n1 n2 y, phi c x n1 = Some y -> n2 >= n1 -> phi c x n2 = Some y. *)

    Definition CTreturns c x y := exists n, phi c x n = Some y.
    Definition CThalts c x := exists y, CTreturns c x y.
    Definition CTdecider c (P : nat -> Prop) :=
      forall x, (P x -> CTreturns c x 0) /\ (~P x -> CTreturns c x 1).

    Variable wrepr : nat -> nat -> sentences.
    Hypothesis Hwrepr : forall (c x : nat), CThalts c x <-> provable (wrepr c x).

    Lemma CTwrepr_dec (c x : nat) : (CThalts c x) + ~CThalts c x.
    Proof.
      enough (provable (wrepr c x) + ~provable (wrepr c x)) as [H|H].
      - left. now apply Hwrepr.
      - right. contradict H. now apply Hwrepr.
      - intuition.
    Qed.

    Lemma CTspecial_halting : ~decidable (fun d => CThalts d d).
    Proof.
      unfold CThalts, CTreturns, decidable, decider, reflects.
      intros [f Hf].
      destruct (CT (fun n => if f n then None else Some 1)) as [c Hc].
      specialize (Hf c).
      specialize (Hc c).
      destruct (f c).
      - destruct Hf as [_ H].
        destruct (H eq_refl) as (y & n & Hyn).
        congruence.
      - enough (false = true) by congruence.
        apply Hf. destruct Hc as [n Hc].
        now exists 1, n.
    Qed.
    Lemma CTwrepr : False.
    Proof.
      apply CTspecial_halting.
      exists (fun d => if CTwrepr_dec d d then true else false).
      intros d. split; now destruct CTwrepr_dec.
    Qed.

    Variable repr : nat -> nat -> nat -> sentences.
    Hypothesis Hrepr : forall (c x y : nat),
        (CTreturns c x y -> provable (repr c x y)) /\
          forall y', CTreturns c x y -> y <> y' -> ~provable ((repr c x y')).

    Definition CTrepr_fn (c x : nat) : nat.
    Proof.
      destruct (provable_decidable (repr c x 0)).
      - exact 0.
      - exact 1.
    Defined.
    Lemma CTrepr_fn_correct : forall c x,
        (CTreturns c x 0 -> CTrepr_fn c x = 0) /\
          (CTreturns c x 1 -> CTrepr_fn c x = 1).
    Proof.
      intros c x. split.
      - intros Hprov % Hrepr. cbv.
        destruct provable_decidable as [H|H].
        + reflexivity.
        + contradiction.
      - intros Hret1.
        assert (~provable ((repr c x 0))) as H.
        { now apply (Hrepr c x 1). }
        cbv. destruct provable_decidable as [H'|H']; easy.
    Qed.

    Lemma CTcg : ~exists (f : nat -> nat), forall c x,
                     (CTreturns c x 0 -> f (embed (c, x)) = 0) /\
                       (CTreturns c x 1 -> f (embed (c, x)) = 1).
    Proof.
      intros [f Hf].
      destruct (CT (fun c => if f (embed (c, c)) then Some 1 else Some 0)) as [c Hc].
      specialize (Hc c).
      specialize (Hf c c).
      destruct (f (embed (c, c))).
      - enough (0 = 1) by congruence. apply Hf. exact Hc.
      - enough (S n = 0) by congruence. apply Hf. exact Hc.
    Qed.
    Lemma CTcg2 : ~exists (f : nat -> nat), forall c x y, (CTreturns c x y -> f (embed (c, x)) = y).
    Proof.
      intros [f Hf].
      destruct (CT (fun c => Some (S (f (embed (c, c)))))) as [c Hc].
      specialize (Hf c c (S (f (embed (c, c)))) (Hc c)).
      lia.
    Qed.

    Lemma CTrepr : False.
    Proof.
      apply CTcg.
      exists (fun t => let (c, x) := unembed t in CTrepr_fn c x).
      intros c x. split; rewrite embedP; apply CTrepr_fn_correct.
    Qed.

  End CT.
  Check CTrepr.
End Abstract.

Check CTrepr.
