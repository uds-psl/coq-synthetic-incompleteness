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
  Hypothesis sentences_enumerable : Sigma (f : nat -> option sentences), forall s, exists k, f k = Some s.


  Variable (provable_enumerator : nat -> option sentences).
  Definition provable s := exists k, provable_enumerator k = Some s.

  Hypothesis consistent : forall s, provable s -> provable (neg s) -> False.
  Definition completeness := forall s, provable s \/ provable (neg s).

  Lemma neg_no_fixpoint : forall s, provable s -> s <> neg s.
  Proof.
    intros s Hs Heq. eapply consistent.
    - exact Hs.
    - rewrite <- Heq. exact Hs.
  Qed.
  Lemma neg_no_fixpoint2 : forall s, provable (neg s) -> s <> neg s.
  Proof.
    intros s Hs Heq. eapply consistent.
    2: exact Hs.
    congruence.
  Qed.

  Lemma undeepen_provability s : completeness -> ~provable s -> provable (neg s).
  Proof.
    intros complete Hnprov.
    destruct (complete s).
    - contradiction.
    - assumption.
  Qed.
  Lemma deepen_provability s : provable (neg s) -> ~provable s.
  Proof.
    intros Hprovn Hnprov. eapply consistent; eassumption.
  Qed.
  Lemma deep_provability_equiv s : completeness -> (~provable s <-> provable (neg s)).
  Proof.
    intros complete. split.
    - now apply undeepen_provability.
    - now apply deepen_provability.
  Qed.


  Lemma ldecidable_provable : completeness -> ldecidable provable.
  Proof.
    intros complete s.
    destruct (complete s).
    - now left.
    - right. intros ?.
      now apply (@consistent s).
  Qed.
  Lemma provable_coenumerable : completeness -> enumerable (fun s => ~provable s).
  Proof.
    intros complete.
    destruct sentences_enumerable as [sentences_enumerator Hsent].
    unshelve eexists.
    { intros [k1 k2] % unembed.
      destruct (provable_enumerator k1) as [sprov|]. 2: exact None.
      destruct (sentences_enumerator k2) as [ssent|]. 2: exact None.
      destruct (sentences_discrete sprov (neg ssent)).
      - exact (Some ssent).
      - exact None. }
    intros s. split.
    - intros [k1 Hk1] % undeepen_provability. 2: exact complete.
      destruct (Hsent s) as [k2 Hk2].
      exists (embed (k1, k2)). rewrite embedP. cbn.
      rewrite Hk1, Hk2.
      now destruct sentences_discrete.
    - intros [k Hk].
      destruct (unembed k) as [k1 k2]. cbn in Hk.
      destruct provable_enumerator as [s1|] eqn:Hs1. 2: discriminate.
      destruct sentences_enumerator as [s2|]. 2: discriminate.
      destruct sentences_discrete as [Heq|?]. 2: discriminate.
      injection Hk. intros ->.
      intros Hprov. eapply consistent.
      + exact Hprov.
      + rewrite <- Heq. now exists k1.
  Defined.
  Lemma decidable_provable : completeness -> decidable provable.
  Proof.
    intros complete.
    apply weakPost.
    - unfold discrete, decidable, decider, reflects.
      exists (fun '(s1, s2) => if sentences_discrete s1 s2 then true else false).
      intros [s1 s2]. split; destruct sentences_discrete; auto.
    - apply ldecidable_provable, complete.
    - exists provable_enumerator. intros s. reflexivity.
    - now apply provable_coenumerable.
  Qed.


  Section representability_prop.
    Variable T : Type.
    Variable P : T -> Prop.

    Definition weakly_representable :=
      Sigma f, forall t, P t <-> provable (f t).
    Definition strongly_representable :=
      Sigma f, forall t, (P t -> provable (f t)) /\ (~provable (neg (f t)) -> P t).
    Definition strongly_representable_classic :=
      Sigma f, forall t, (P t -> provable (f t)) /\ (~P t -> provable (neg (f t))).

    Lemma strongly_weakly_representable : strongly_representable -> weakly_representable.
    Proof.
      intros [f Hf].
      exists f. intros t. split.
      - apply Hf.
      - intros Hprov. apply Hf.
        intros Hnprov. eapply consistent.
        + exact Hprov.
        + exact Hnprov.
    Qed.
    Lemma weakly_strongly_representable :
      completeness -> weakly_representable -> strongly_representable.
    Proof.
      intros complete [f Hf].
      exists f. intros t. split.
      - apply Hf.
      - intros Hnprov. apply Hf.
        destruct (complete (f t)).
        + assumption.
        + contradiction.
    Qed.
    (* TODO completeness -> ldecidable provable *)
    Lemma weakly_strongly_representable_classic :
      completeness -> weakly_representable -> strongly_representable_classic.
    Proof.
      intros complete [f Hf]. exists f.
      intros t. split.
      - apply Hf.
      - intros Hnpt. destruct (complete (f t)).
        + firstorder.
        + assumption.
    Qed.


    Goal ldecidable provable -> strongly_representable -> strongly_representable_classic.
    Proof.
      intros ldec [f Hf]. exists f.
      intros t. split.
      - apply Hf.
      - intros Hnpt. destruct (ldec (neg (f t))).
        + assumption.
        + firstorder.
    Qed.
    Goal ldecidable P -> strongly_representable_classic -> strongly_representable.
    Proof.
      intros ldec [f Hf]. exists f.
      intros t. split.
      - apply Hf.
      - intros Hnprov. destruct (ldec t); firstorder.
    Qed.
  End representability_prop.
  Arguments weakly_representable {T}.
  Arguments strongly_representable {T}.
  Arguments strongly_representable_classic {T}.

  (* TODO update webpage: short synposis of what im doing (strengthening existing results)) *)
  Section decidability_predicate.
    Variable (T : Type) (Tdis : forall (t1 t2 : T), (t1 = t2) + (t1 <> t2)) (Tenumerable : Sigma (f : nat -> option T), forall t, exists n, f n = Some t).
    Variable (P : T -> Prop).
    Variable srepr : strongly_representable_classic P.

    (* TODO work on an abstract machine model using Church's Thesis *)
    (* TODO this as a Coq function using Posts Theorem *)
    Lemma srepr_fn : function T out.
    Proof.
      destruct srepr as [psent Hpsent].
      unshelve eexists.
      - intros t k.
        destruct (provable_enumerator k) as [s|]. 2: exact None.
        destruct (sentences_discrete s (psent t)).
        + exact (Some ACC).
        + destruct (sentences_discrete s (neg (psent t))).
          * exact (Some REJ).
          * exact None.
      - intros x k1 k2 y1 y2. cbn.
        destruct (provable_enumerator k1) as [s1|] eqn:Hs1, (provable_enumerator k2) as [s2|] eqn:Hs2; try congruence.
        repeat destruct sentences_discrete; try congruence.
        all: edestruct consistent.
        + exists k1. eassumption.
        + exists k2. congruence.
        + exists k2. eassumption.
        + exists k1. congruence.
    Defined.

    Lemma srepr_fn_correct t : (P t -> accepts srepr_fn t) /\ (~P t -> rejects srepr_fn t).
    Proof.
      destruct srepr as [psent Hpsent] eqn:Hsrepr.
      split.
      - intros pt. unfold accepts, returns.
        assert (provable (psent t)) as [k Hk] by intuition.
        exists k. cbv. rewrite Hsrepr, Hk.
        destruct sentences_discrete; easy.
      - intros Hnpt. unfold rejects, returns.
        assert (provable (neg (psent t))) as [k Hk] by intuition.
        exists k. cbv. rewrite Hsrepr, Hk.
        destruct sentences_discrete as [Heq | ?].
        { destruct (@neg_no_fixpoint (psent t)).
          - exists k. congruence. 
          - easy. }
        destruct sentences_discrete; easy.
    Qed.

    (* NOTE: Proof does not directly require representability *)
    Lemma srepr_fn_correct_iff (ldec : ldecidable P) t : (P t <-> accepts srepr_fn t) /\ (~P t <-> rejects srepr_fn t).
    Proof.
      split; split. 1, 3: now apply srepr_fn_correct.
      - destruct (ldec t) as [H|H]. 1: easy.
        apply srepr_fn_correct in H.
        intros H'.
        edestruct accepts_rejects; eassumption.
      - destruct (ldec t) as [H|H]. 2: easy.
        apply srepr_fn_correct in H.
        intros H'.
        edestruct accepts_rejects; eassumption.
    Qed.

    (* TODO can we get logical decidability of P somehow? maybe using decidability of provability under completeness? *)
    Lemma srepr_decidable : completeness -> (ldecidable P) -> decidable P.
    Proof.
      intros complete Pldec.
      apply weakPost.
      - unfold discrete, decidable, decider, reflects.
        exists (fun '(t1, t2) => if Tdis t1 t2 then true else false).
        intros [t1 t2]. split; destruct Tdis; intuition.
      - assumption.
      - destruct srepr as [repr Hrepr], Tenumerable as [Tenum HTenum].
        unshelve eexists.
        { intros k. destruct (unembed k) as [k1 k2].
          destruct (Tenum k1) as [t|]. 2: exact None.
          destruct (provable_enumerator k2) as [s|]. 2: exact None.
          destruct (sentences_discrete (repr t) s).
          - exact (Some t).
          - exact None.
        }
        intros t. split.
        + intros Hpt. apply Hrepr in Hpt.
          destruct (HTenum t) as [k1 Hk1].
          destruct (Hpt) as [k2 Hk2].
          exists (embed (k1, k2)). rewrite embedP. cbn.
          rewrite Hk1, Hk2.
          now destruct sentences_discrete.
        + intros [k Hk].
          destruct (unembed k) as [k1 k2]. cbn in Hk.
          destruct Tenum. 2: discriminate.
          destruct provable_enumerator eqn:HProv. 2: discriminate.
          destruct sentences_discrete as [Heq|Heq]. 2: discriminate.
          destruct (Pldec t) as [H|H]. 1: assumption.
          edestruct consistent.
          * exists k2. exact HProv.
          * rewrite <- Heq. apply Hrepr. congruence.
      (* TODO it might be possible to remove the completeness requirement here
          essentially by inlining the coenumerability proof for the sentences
          that strongly represent *)
      - destruct provable_coenumerable as [provable_coenumerator Hprov_coenum]. 1: assumption.
        destruct srepr as [repr Hrepr], Tenumerable as [Tenum HTenum].
        unshelve eexists.
        { intros k. destruct (unembed k) as [k1 k2].
          destruct (Tenum k1) as [t|]. 2: exact None.
          destruct (provable_coenumerator k2) as [s|]. 2: exact None.
          destruct (sentences_discrete (repr t) s).
          - exact (Some t).
          - exact None.
        }
        intros t. split.
        + intros Hnpt. apply Hrepr in Hnpt.
          destruct (HTenum t) as [k1 Hk1].
          unfold enumerator in Hprov_coenum.
          destruct (Hprov_coenum (repr t)) as [[k2 Hk2] _].
          1: now apply deepen_provability.
          exists (embed (k1, k2)). rewrite embedP. cbn.
          rewrite Hk1, Hk2. now destruct sentences_discrete.
        + intros [k Hk].
          destruct (unembed k) as [k1 k2]. cbn in Hk.
          destruct Tenum. 2: discriminate.
          destruct provable_coenumerator eqn:Hprov. 2: discriminate.
          destruct sentences_discrete as [Heq|Heq]. 2: discriminate.
          destruct (Pldec t) as [H|H]. 2: assumption.
          destruct (@consistent (repr t)).
          * now apply Hrepr.
          * apply undeepen_provability. 1: assumption.
            apply Hprov_coenum.
            exists k2. congruence.
    Qed.

  End decidability_predicate.


  (* NOTE out can probably be abstracted to be any finite, maybe enumerable type. *)
  (* This will not be interesting for Gödel itself *)
  Section s.
    Variable (T : Type) (p : T -> out -> Prop).
    Hypothesis p_func : forall t y1 y2, p t y1 -> p t y2 -> y1 = y2.

    Variable p_sentence : T -> out -> sentences.
    Hypothesis p_repr1 : forall t y, p t y -> provable (p_sentence t y).
    Hypothesis p_repr2 : forall t y, ~p t y -> provable (neg (p_sentence t y)).

    Definition f : function T out.
    Proof.
      unshelve eexists.
      - intros f k.
        destruct (provable_enumerator k) as [s|]. 2: exact None.
        destruct (sentences_discrete (p_sentence f ACC) s).
        + exact (Some ACC).
        + destruct (sentences_discrete (neg (p_sentence f ACC)) s).
          * exact (Some REJ).
          * exact None.
      - intros x k1 k2 y1 y2. cbn.
        destruct (provable_enumerator k1) as [s1|] eqn:Hs1, (provable_enumerator k2) as [s2|] eqn:Hs2; try congruence.
        repeat destruct sentences_discrete; try congruence.
        all: edestruct consistent.
        + exists k1. eassumption.
        + exists k2. congruence.
        + exists k2. eassumption.
        + exists k1. congruence.
    Defined.


    (* NOTE this is not a reduction but a weaker notion. Can this be strengthened? *)
    Lemma f_correct : (forall t y, p t y -> returns f t y) /\ (forall t, (forall y, ~p t y) -> halts f t).
    Proof.
      split.
      - intros t [] Hf.
        + destruct (p_repr1 Hf) as [k Hk].
          exists k. cbn. rewrite Hk.
          destruct sentences_discrete; congruence.
        + assert (~p t ACC) as Hf'.
          { intros Hf'. enough (ACC=REJ) by discriminate. eapply p_func; eassumption. }
          destruct (p_repr2 Hf') as [k Hk].
          exists k. cbn. rewrite Hk.
          destruct sentences_discrete as [H|H].
          * edestruct neg_no_fixpoint2.
            2: exact H.
            now exists k.
          * destruct sentences_discrete; congruence.
      - intros t Hdiv.
        exists REJ.
        destruct (p_repr2 (Hdiv ACC)).
        exists x. cbn. rewrite H.
        repeat destruct sentences_discrete.
        + edestruct neg_no_fixpoint2.
          2: exact e.
          exists x. assumption.
        + reflexivity.
        + easy.
    Qed.
  End s.

  Section cg.
    Variable (T : Type) (t : T).
    (* NOTE: We do not want to have anything in our relation if g diverges *)
    Definition cg_pred (g : function T out) (y : out): Prop :=
      (accepts g t /\ y = ACC) \/
      (rejects g t /\ y = REJ) \/
      (diverges g t /\ y = REJ).
    (* TODO (why) does implication suffice here? In our old formulation it did as well*)
    Hypothesis no_cg : ~exists f, forall g y, cg_pred g y -> returns f g y.

    Variable cg_sentence : (function T out) -> out -> sentences.
    Hypothesis cg_repr1 : forall f y, cg_pred f y -> provable (cg_sentence f y).
    Hypothesis cg_repr2 : forall f y, ~cg_pred f y -> provable (neg (cg_sentence f y)).

    Lemma cg_false : False.
    Proof.
      apply no_cg. exists (f cg_sentence).
      unshelve edestruct (@f_correct (function T out) cg_pred) as [H1 H2].
      - exact cg_sentence.
      - intros g [] [] [[H11 H12]|[[H11 H12]|[H11 H12]]] [[H21 H22]|[[H21 H22]|[H21 H22]]]. all: try congruence.
        + eapply returns_functional; eassumption.
        + destruct H11 as [k ?]. specialize (H21 k). congruence.
        + eapply returns_functional; eassumption.
        + destruct H21 as [k ?]. specialize (H11 k). congruence.
      - assumption.
      - assumption.
      - intros g y [[H3 H4]|[[H3 H4]|[H3 H4]]]; firstorder.
    Qed.
  End cg.
End Abstract.

Check f_correct.

