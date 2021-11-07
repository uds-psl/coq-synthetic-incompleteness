(** * Abstract Incompleteness using Rosser's Trick *)

From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
From Undecidability.Shared Require Import embed_nat Dec.
From Equations Require Import Equations.
Require Import ConstructiveEpsilon.

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Definition tenumerator X (f : nat -> option X) := forall x, exists k, f k = Some x.
Definition tenumerable X := exists (f : nat -> option X), tenumerator f.

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


Class FS : Type := mkFS { sentences : Type
                    ; neg : sentences -> sentences
                    ; sentences_discrete : discrete sentences
                    ; sentences_enumerable : tenumerable sentences
                    ; provable : sentences -> Prop
                    ; provable_enumerable : enumerable provable
                    ; consistent : forall s, provable s -> provable (neg s) -> False }.
(* TODO is there syntax for non-implicit arguments? why is s taken implicitly here? *)
Arguments consistent {_} _ _ _.

Definition completeness {fs : FS} := forall s, provable s \/ provable (neg s).

Section facts.
  Context {fs : FS}.

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
    intros complete s. destruct (complete s); firstorder using consistent.
  Qed.

  Lemma provable_coenumerable : completeness -> enumerable (fun s => ~provable s).
  Proof.
    destruct provable_enumerable as [provable_enumerator provable_enumerable].
    destruct sentences_enumerable as [sentences_enumerator sentences_enumerable].
    pose proof sentences_discrete as [sentences_discrete]%discrete_iff.

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
    - exact sentences_discrete.
    - apply ldecidable_provable, complete.
    - exact provable_enumerable.
    - apply provable_coenumerable, complete.
  Qed.

End facts.

From Undecidability.FOL.Util Require Import Syntax_facts FullDeduction FullDeduction_facts FullTarski FullTarski_facts Axiomatisations.
From Undecidability.FOL Require Import PA.
Module instantiation.
  Section instantiation.
    Context {Σ_funcs : funcs_signature}.
    Context {Σ_preds : preds_signature}.
    Hypothesis (syms_eq_dec : eq_dec syms) (syms_enumerable : enumerable__T syms).
    Hypothesis (preds_eq_dec : eq_dec preds) (preds_enumerable : enumerable__T preds).

    (* It suffices to talk about finite extensions here for the purposes
       of talking about Q because of compactness *)
    Context (T : form -> Prop) (T_enumerable : enumerable T).
    Hypothesis consistent : ~ T ⊢TC ⊥.


    Instance EqDec_syms : EqDec syms.
    Proof.
      intros x y. apply syms_eq_dec.
    Qed.
    Instance EqDec_preds : EqDec preds.
    Proof.
      intros x y. apply preds_eq_dec.
    Qed.

    Definition closed phi :=
      (if bounded_dec phi 0 then true else false) = true.

    Lemma closed_mere phi (H H' : closed phi) :
      H = H'.
    Proof.
      apply EqDec.peq_proofs_unicity.
    Qed.
    Lemma bounded_closed phi :
      bounded 0 phi <-> closed phi.
    Proof.
      unfold closed. destruct bounded_dec; intuition congruence.
    Qed.

    Lemma closed_dec phi :
      dec (closed phi).
    Proof.
      eapply dec_transfer; try apply bounded_closed. apply bounded_dec.
    Qed.

    Lemma bot_closed :
      closed ⊥.
    Proof.
      apply bounded_closed. constructor.
    Qed.

    Lemma closed_discrete :
      discrete {phi | closed phi}.
    Proof.
      apply decidable_iff. constructor. intros [[phi H1] [psi H2]].
      destruct dec_form with falsity_on phi psi as [->|H]; eauto.
      1,2: intros x y; unfold dec; decide equality.
      - left. f_equal. apply closed_mere.
      - right. intros [=]. tauto.
    Qed.

    Lemma closed_enum :
      enumerable__T form -> enumerable__T {phi | closed phi}.
    Proof.
      intros [f Hf]. unshelve eexists.
      - intros n. destruct (f n) as [phi|].
        + destruct (closed_dec phi) as [H|_].
          * apply Some. now exists phi.
          * exact None.
        + exact None.
      - intros [phi Hp]. destruct (Hf phi) as [n Hn].
        exists n. cbn. rewrite Hn. destruct closed_dec as [H|H]; try tauto.
        repeat f_equal. apply closed_mere.
    Qed.


    Definition provable (phi : {phi | closed phi}) := T ⊢TC proj1_sig phi.
    Lemma provable_enumerable : enumerable provable.
    Proof.
      unfold provable.
      assert (enumerable (fun phi => T ⊢TC phi)) as [f Hf] by now unshelve eapply tprv_enumerable.
      unshelve eexists.
      - intros k. destruct (f k) as [phi|]. 2: exact None.
        destruct (closed_dec phi).
        + left. now exists phi.
        + exact None.
      - intros [phi Hphi]. split; cbn.
        + intros [k Hk]%(Hf phi). exists k.
          destruct (f k). 2: congruence.
          destruct closed_dec; subst.
          * injection Hk. intros. subst.
            repeat f_equal. apply closed_mere.
          * injection Hk. intros. subst. congruence.
        + intros [k Hk].
          destruct (f k) eqn:H. 2: congruence.
          destruct closed_dec. 2: congruence.
          apply Hf. exists k. congruence.
    Qed.

    Lemma consistency : forall phi, T ⊢TC phi -> T ⊢TC ¬phi -> False.
    Proof.
      intros phi (L1 & Hsub1 & Hprov1) (L2 & Hsub2 & Hprov2).
      apply consistent.
      exists (L1 ++ L2)%list. split.
      - intros psi [H|H]%List.in_app_or; eauto.
      - eapply IE; eapply Weak; eauto.
    Qed.

    Instance fs_fo : FS.
    Proof.
      unshelve econstructor.
      - exact {phi | closed phi}.
      - intros [phi Hphi]. exists (¬phi).
        apply bounded_closed.
        constructor.
        + apply bounded_closed. exact Hphi.
        + constructor.
      - exact provable.
      - exact closed_discrete.
      - apply closed_enum.
        now unshelve eapply form_enumerable.
      - exact provable_enumerable.
      - cbn. intros [] H1 H2.
        eapply consistency.
        + exact H1.
        + exact H2.
    Qed.
  End instantiation.
End instantiation.
Definition fs_fo := instantiation.fs_fo.
Check fs_fo.

