(** * Abstract Incompleteness using Rosser's Trick *)

From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
From Undecidability.Shared Require Import embed_nat Dec.
From Equations Require Import Equations.
Require Import ConstructiveEpsilon.

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Lemma decidable_equiv X p q : (forall (x : X), p x <-> q x) -> decidable p -> decidable q.
Proof.
  firstorder.
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

Definition sfunction X Y := { f : X -> nat -> option Y & forall x k k' y y', f x k = Some y -> f x k' = Some y' -> y = y' }.
Definition stotal {X Y} (f : sfunction X Y) := forall x, exists k y, projT1 f x k = Some y.

Lemma totalize X (Xdis : discrete X) (Xenum : enumerable__T X) (f : sfunction X bool) :
  stotal f -> decidable (fun x => exists k, projT1 f x k = Some true).
Proof.
  destruct f as [f Hfunc]. unfold stotal. cbn.
  destruct Xenum as [Xe HXe].
  intros Hf.
  apply weakPost.
  - assumption.
  - intros x.
    destruct (Hf x) as (k & [] & H).
    + left. eauto.
    + right. intros [k' Hk'].
      specialize (Hfunc x k k' false true H Hk'). congruence.
  - unshelve eexists.
    { intros [k1 k2]%unembed. destruct (Xe k1) as [x|]. 2: exact None.
      destruct (f x k2) as [[]|]. 1: exact (Some x).
      all: exact None.
    }
    intros x. split.
    + intros [k2 Hk2].
      destruct (HXe x) as [k1 Hk1].
      exists (embed (k1, k2)).
      rewrite embedP. cbn.
      now rewrite Hk1, Hk2.
    + intros [k Hk].
      destruct (unembed k) as [k1 k2]. cbn in Hk.
      destruct (Xe k1) as [x'|]. 2: congruence.
      destruct (f x' k2) as [[]|] eqn:H. 2,3: congruence.
      exists k2. congruence.
  - unshelve eexists.
    { intros [k1 k2]%unembed. destruct (Xe k1) as [x|]. 2: exact None.
      destruct (f x k2) as [[]|]. 2: exact (Some x).
      all: exact None.
    }
    intros x. split.
    + intros Hn.
      destruct (Hf x) as (k2 & b & Hk2).
      destruct b.
      1: { exfalso. eauto. }
      destruct (HXe x) as [k1 Hk1].
      exists (embed (k1, k2)).
      rewrite embedP. cbn. now rewrite Hk1, Hk2.
    + intros [k Hk] [k' Hk'].
      destruct (unembed k) as [k1 k2]. cbn in Hk.
      destruct (Xe k1) as [x'|]. 2: congruence.
      destruct (f x' k2) as [[]|] eqn:H. 1, 3: congruence.
      injection Hk as ->.
      specialize (Hfunc x k' k2 true false Hk' H). congruence.
Qed.

Class FS : Type := mkFS { sentences : Type
                    ; neg : sentences -> sentences
                    ; sentences_discrete : discrete sentences
                    ; sentences_enumerable : enumerable__T sentences
                    ; provable : sentences -> Prop
                    ; provable_enumerable : enumerable provable
                    ; consistent : forall s, provable s -> provable (neg s) -> False }.
Arguments consistent {_} _ _.

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
    firstorder.
  Qed.
  Lemma deepen_provability s : provable (neg s) -> ~provable s.
  Proof.
    eauto using consistent.
  Qed.

  Lemma deep_provability_iff s : completeness -> (provable (neg s) <-> ~provable s).
  Proof.
    firstorder using undeepen_provability, deepen_provability.
  Qed.

  Lemma provable_ldecidable : completeness -> ldecidable provable.
  Proof.
    intros complete s. destruct (complete s); firstorder using consistent.
  Qed.

  Lemma enumerable_equiv X (P Q : X -> Prop) :
    (forall x, P x <-> Q x) -> enumerable P -> enumerable Q.
  Proof.
    intros H [f Hf]. exists f. intros x. rewrite <- H. apply Hf.
  Qed.
  Lemma provable_coenumerable : completeness -> enumerable (fun s => ~provable s).
  Proof.
    intros complete.
    apply enumerable_equiv with (P := (fun s => provable (neg (s)))).
    1: auto using deep_provability_iff.
    apply semi_decidable_enumerable. 1: exact sentences_enumerable.

    destruct provable_enumerable as [provable_enumerator provable_enumerable].
    pose proof sentences_discrete as [sentences_eqdec]%discrete_iff.
    unshelve eexists.
    {
      intros s k.
      destruct (provable_enumerator k) as [p|]. 2: exact false.
      destruct (sentences_eqdec (neg s) p).
      - exact true.
      - exact false.
    }
    intros s. split.
    - intros [k Hk]%provable_enumerable.
      exists k. rewrite Hk. cbn.
      now destruct sentences_eqdec.
    - intros [k Hk]. cbn in Hk.
      apply provable_enumerable. exists k.
      destruct (provable_enumerator) eqn:Heq. 2: congruence.
      destruct sentences_eqdec; congruence.
  Qed.

  Lemma provable_decidable : completeness -> decidable provable.
  Proof.
    intros complete.
    apply weakPost.
    - exact sentences_discrete.
    - apply provable_ldecidable, complete.
    - exact provable_enumerable.
    - apply provable_coenumerable, complete.
  Qed.
End facts.

From Undecidability.FOL.Util Require Import Syntax_facts FullDeduction FullDeduction_facts FullTarski FullTarski_facts Axiomatisations.
From Undecidability.FOL Require Import PA.
Section instantiation.
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context (T : form -> Prop) (T_enumerable : enumerable T).

  Context {syms_eq_dec : EqDec syms} (syms_enumerable : enumerable__T syms).
  Context {preds_eq_dec : EqDec preds} (preds_enumerable : enumerable__T preds).

  Context {peirce : peirce}.

  Hypothesis consistent : ~ T ⊢T ⊥.


  (* Mostly stolen from Dominik *)

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
  Proof.  apply bounded_closed. constructor.  Qed.
  Lemma neg_closed (s : { phi | closed phi }) : closed (¬proj1_sig s).
  Proof.
    apply bounded_closed. constructor; apply bounded_closed.
    - now destruct s.
    - apply bot_closed.
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
  
  Definition form_neg (s : { phi | closed phi }) : { phi | closed phi }.
  Proof.
    unshelve econstructor.
    - exact (¬proj1_sig s).
    - apply neg_closed. 
  Defined.
  Definition form_provable (s : { phi | closed phi }) := T ⊢T proj1_sig s.


  Lemma form_provable_enumerable : enumerable form_provable.
  Proof.
    assert (enumerable (fun phi => T ⊢T phi)) as [f Hf]
        by now unshelve eapply tprv_enumerable.
    unshelve eexists.
    - intros k. destruct (f k) as [phi|]. 2: exact None.
      destruct (closed_dec phi).
      + left. now exists phi.
      + exact None.
    - intros [phi Hphi]. split; cbn.
      + intros [k Hk]%Hf. exists k.
        destruct (f k). 2: congruence.
        injection Hk as ->.
        destruct closed_dec.
        * repeat f_equal. apply closed_mere.
        * contradiction.
      + intros [k Hk].
        destruct (f k) eqn:H. 2: congruence.
        destruct closed_dec. 2: congruence.
        apply Hf. exists k. cbn. congruence.
  Qed.

  Lemma consistency : forall phi, T ⊢T phi -> T ⊢T ¬phi -> False.
  Proof.
    intros phi (L1 & Hsub1 & Hprov1) (L2 & Hsub2 & Hprov2).
    apply consistent.
    exists (L1 ++ L2)%list. split.
    - intros psi [H|H]%List.in_app_or; eauto.
    - eapply IE; eapply Weak; eauto.
  Qed.

  Definition fs_fo : FS.
  Proof.
    unshelve econstructor.
    - exact { phi | closed phi }.
    - exact form_neg. 
    - exact form_provable.
    - exact closed_discrete.
    - now unshelve eapply closed_enum, form_enumerable.
    - exact form_provable_enumerable.
    - intros [s ?] H1 H2.
      apply (@consistency s); assumption.
  Qed.
End instantiation.


From Undecidability.FOL.Util Require Import Syntax_facts FullDeduction FullDeduction_facts FullTarski FullTarski_facts Axiomatisations.
From Undecidability.FOL Require Import PA.

Definition Q := list_theory Qeq.
Goal forall (T : form -> Prop), Q <<= T -> ~(T ⊢TC ⊥) -> exists phi, ~(T ⊢TC phi) /\ ~(T ⊢TC ¬phi).
Abort.
