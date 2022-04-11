From Undecidability.FOL.Incompleteness Require Import utils.

From Undecidability.Synthetic Require Import Definitions Undecidability.
From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts.
From Undecidability.Shared Require Import Dec.
(* Required for... EqDec? *)
From Equations Require Import Equations.


Local Set Implicit Arguments.
Local Unset Strict Implicit.

Record FS (S : Type) (neg : S -> S) : Type := 
  mkFS { P : S -> Prop
       ; S_discrete : discrete S
       ; S_enumerable : enumerable__T S
       ; P_enumerable : enumerable P
       ; consistent : forall s, P s -> P (neg s) -> False }.
Arguments FS : clear implicits.

Arguments consistent {S neg} _ _ _ _.

Notation "fs ⊢F s" := (fs.(P) s) (at level 30).
Notation "fs ⊬F s" := (~fs.(P) s) (at level 30).

(*Definition complete {S : Type} {neg : S -> S} (fs : FS S neg) :=
   forall s, fs ⊢F s \/ fs ⊢F neg s.*)

Definition extension {S : Type} {neg : S -> S} (fs1 fs2 : FS S neg) :=
  forall s, fs1 ⊢F s -> fs2 ⊢F s.

Section facts.
  Context {S : Type} {neg : S -> S} (fs : FS S neg).

  Definition complete := forall s, fs ⊢F s \/ fs ⊢F neg s.
  Definition independent s := fs ⊬F s /\ fs ⊬F neg s.

  Lemma neg_no_fixpoint_provable : forall s, fs ⊢F s -> s <> neg s.
  Proof.
    intros s Hs Heq. eapply (consistent fs s); congruence.
  Qed.
  Lemma neg_no_fixpoint_refutable : forall s, fs ⊢F neg s -> s <> neg s.
  Proof.
    intros s Hs Heq. apply (consistent fs s); congruence.
  Qed.
  Lemma neg_no_fixpoint_comp : complete -> forall s, s <> neg s.
  Proof.
    intros complete s. destruct (complete s).
    - now apply neg_no_fixpoint_provable.
    - now apply neg_no_fixpoint_refutable.
  Qed.

  Lemma undeepen_provability s : complete -> fs ⊬F s -> fs ⊢F neg s.
  Proof.
    firstorder.
  Qed.
  Lemma deepen_provability s : fs ⊢F neg s -> fs ⊬F s.
  Proof.
    eauto using consistent.
  Qed.

  Lemma deep_provability_iff s : complete -> (fs ⊢F neg s <-> fs ⊬F s).
  Proof.
    firstorder using undeepen_provability, deepen_provability.
  Qed.

  Lemma provable_ldecidable : complete -> ldecidable fs.(P).
  Proof.
    intros complete s. destruct (complete s); firstorder using deep_provability_iff.
  Qed.

  Lemma provable_coenumerable : complete -> enumerable (fun s => fs ⊬F s).
  Proof.
    intros complete.
    apply enumerable_equiv with (P := (fun s => fs ⊢F neg s)).
    1: auto using deep_provability_iff.
    apply semi_decidable_enumerable. 1: exact fs.(S_enumerable).

    destruct fs.(P_enumerable) as [prov Hprov].
    pose proof fs.(S_discrete) as [S_eqdec]%discrete_iff.
    unshelve eexists.
    {
      intros s k.
      destruct (prov k) as [p|]. 2: exact false.
      destruct (S_eqdec (neg s) p).
      - exact true.
      - exact false.
    }
    intros s. split.
    - intros [k Hk]%Hprov.
      exists k. rewrite Hk. cbn.
      now destruct S_eqdec.
    - intros [k Hk]. cbn in Hk.
      apply Hprov. exists k.
      destruct (prov k) eqn:Heq. 2: congruence.
      destruct S_eqdec; congruence.
  Qed.

  Lemma provable_decidable : complete -> decidable fs.(P).
  Proof.
    intros complete. apply weakPost.
    - exact fs.(S_discrete).
    - apply provable_ldecidable, complete.
    - exact fs.(P_enumerable).
    - apply provable_coenumerable, complete.
  Qed.

  Lemma is_provable : exists f : S -\ bool, 
    (forall s, fs ⊢F s <-> f s ▷ true) /\
    (forall s, fs ⊢F neg s <-> f s ▷ false).
  Proof.
    destruct fs.(P_enumerable) as [prov Hprov].
    pose proof fs.(S_discrete) as [S_eqdec]%discrete_iff.
    unshelve eexists.
    1: intros s; unshelve econstructor.
    { intros k.  
      refine (match prov k with Some s' => _ | None => None end).
      refine (if S_eqdec s s' then _ else _).
      - exact (Some true).
      - refine (if S_eqdec (neg s) s' then Some false else None). }
    { cbn. intros y1 y2 k1 k2 H1 H2.
      destruct (prov k1) as [s1|] eqn:Hk1,
               (prov k2) as [s2|] eqn:Hk2.
      all: cbn in *; try congruence.
      repeat destruct S_eqdec; try congruence; subst.
      - edestruct fs.(consistent); apply Hprov.
        + exists k1. eassumption.
        + exists k2. assumption.
      - edestruct fs.(consistent); apply Hprov.
        + exists k2. eassumption.
        + exists k1. assumption. }
    cbn. split; intros s; split.
    - intros [k Hk]%Hprov. exists k. cbn. rewrite Hk.
      destruct S_eqdec; congruence.
    - intros [k Hk]. cbn in Hk.
      destruct (prov k) as [s'|] eqn:H. 2: discriminate.
      repeat destruct S_eqdec; try discriminate.
      apply Hprov. exists k. now subst.
    - intros [k Hk]%Hprov. exists k. cbn. rewrite Hk.
      repeat destruct S_eqdec; try congruence.
      edestruct neg_no_fixpoint_refutable.
      { apply Hprov. exists k. apply Hk. }
      assumption.
    - intros [k Hk]. cbn in Hk.
      destruct (prov k) as [s'|] eqn:H. 2: discriminate.
      repeat destruct S_eqdec; try discriminate.
      apply Hprov. exists k. now subst.
  Qed.

  Lemma provable_decidable' : complete -> decidable fs.(P).
  Proof.
    intros complete.
    destruct is_provable as [f Hf].
    apply decidable_iff. constructor. intros s.
    destruct (@total_part_decidable (f s)) as [[] H].
    - destruct (provable_ldecidable complete s) as [Hs|Hs].
      + exists true. firstorder.
      + exists false. firstorder.
    - firstorder.
    - firstorder using deep_provability_iff.
  Qed.


End facts.
