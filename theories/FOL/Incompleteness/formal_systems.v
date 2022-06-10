From Undecidability.FOL.Incompleteness Require Import utils.

From Undecidability.Synthetic Require Import Definitions Undecidability.
From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts.
From Undecidability.Shared Require Import Dec.
(* Required for... EqDec? *)
From Equations Require Import Equations.


Local Set Implicit Arguments.
Local Unset Strict Implicit.

(** * Abstract Incompleteness *)
(** ** Formal Systems *)

Record FS (S : Type) (neg : S -> S) : Type := 
  mkFS { P : S -> Prop
       ; S_discrete : discrete S
       ; P_enumerable : enumerable P
       ; consistent : forall s, P s -> P (neg s) -> False }.
Arguments FS : clear implicits.

Arguments consistent {S neg} _ _ _ _.

Notation "fs ⊢F s" := (fs.(P) s) (at level 30).
Notation "fs ⊬F s" := (~fs.(P) s) (at level 30).

Definition extension {S : Type} {neg : S -> S} (fs1 fs2 : FS S neg) :=
  forall s, fs1 ⊢F s -> fs2 ⊢F s.

Section facts.
  Context {S : Type} {neg : S -> S} (fs : FS S neg).

  Definition weakly_represents (P : nat -> Prop) (r : nat -> S) :=
    forall x, P x <-> fs ⊢F r x.
  Definition strongly_separates (P1 P2 : nat -> Prop) (r : nat -> S) :=
    (forall x, P1 x -> fs ⊢F r x) /\
    (forall x, P2 x -> fs ⊢F neg (r x)).

  Definition complete := forall s, fs ⊢F s \/ fs ⊢F neg s.
  Definition independent s := fs ⊬F s /\ fs ⊬F neg s.
  Lemma is_provable : exists f : S -\ bool, 
    (forall s, fs ⊢F s <-> f s ▷ true) /\
    (forall s, fs ⊢F neg s <-> f s ▷ false).
  Proof.
    destruct fs.(P_enumerable) as [prov Hprov].
    pose proof fs.(S_discrete) as [S_eqdec]%discrete_iff.
    unshelve eexists.
    { intros s. unshelve econstructor.
      { intros k.
        refine (match prov k with Some s' => _ | None => None end).
        refine (if S_eqdec s s' then _ else _).
        - exact (Some true).
        - refine (if S_eqdec (neg s) s' then Some false else None). }
      intros y1 y2 k1 k2 H1 H2.
      destruct (prov k1) as [s1|] eqn:Hk1,
               (prov k2) as [s2|] eqn:Hk2.
      all: cbn in *; try congruence.
      repeat destruct S_eqdec; try congruence; subst.
      - destruct (@fs.(consistent) s1); apply Hprov; eauto.
      - destruct (@fs.(consistent) s2); apply Hprov; eauto. }
    cbn. split; intros s; split.
    - intros [k Hk]%Hprov. exists k. cbn. rewrite Hk.
      destruct S_eqdec; congruence.
    - intros [k Hk]. cbn in Hk.
      apply Hprov. exists k.
      destruct (prov k) as [s'|] eqn:H. 2: discriminate.
      repeat destruct S_eqdec; congruence.
    - intros [k Hk]%Hprov. exists k. cbn. rewrite Hk.
      repeat destruct S_eqdec; try congruence.
      edestruct (@fs.(consistent) s).
      all: apply Hprov; exists k; congruence.
    - intros [k Hk]. cbn in Hk.
      apply Hprov. exists k.
      destruct (prov k) as [s'|] eqn:H. 2: discriminate.
      repeat destruct S_eqdec; congruence.
  Qed.
  Lemma complete_decidable : complete -> decidable fs.(P).
  Proof.
    intros complete. destruct is_provable as [f Hf].
    assert (forall x, exists b, f x ▷ b) as Htotal.
    { intros x. destruct (complete x) as [H|H].
      - exists true. now apply Hf.
      - exists false. now apply Hf. }
    exists (fun x => projT1 (totalise Htotal x)).
    intros x. destruct totalise as [[] Hb]; split; cbn.
    - easy.
    - intros _. now apply Hf.
    - intros H%Hf. eapply part_functional; eassumption.
    - discriminate.
  Qed.

End facts.
