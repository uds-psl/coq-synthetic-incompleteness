From Undecidability.FOL.Incompleteness Require Import FS.
From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
From Undecidability.Shared Require Import Dec embed_nat.

Require Import Lia.


Definition stationary {X} (f : nat -> option X) := forall k k' y, f k = Some y -> k' >= k -> f k' = Some y.

Definition mkstat {X} (f : nat -> option X) : nat -> option X :=
  fix g k := match k with
            | 0 => f 0
            | S k => match g k with
                    | None => f (S k)
                    | Some x => Some x
                    end
            end.

Lemma mkstat_stationary {X} (f : nat -> option X) : stationary (mkstat f).
Proof.
  intros k k' y. revert k'. induction k; intros k'.
  - intros H0. induction k'.
    + easy.
    + intros ?. cbn. rewrite IHk'.
      * reflexivity.
      * lia.
  - cbn. destruct (mkstat f k) eqn:Heq.
    + intros [= ->]. induction k'.
      * lia.
      * intros H. cbn.
        assert (k' = k \/ k' > k) as [->|H1] by lia.
        -- now rewrite Heq.
        -- rewrite IHk'.  2: lia.
           reflexivity.
    + intros Heq'. induction k'.
      * lia.
      * intros H. cbn.
        assert (k' = k \/ k' > k) as [->|H1] by lia.
        -- now rewrite Heq.
        -- rewrite IHk'. 2: lia.
           reflexivity.
Qed.
Lemma mkstat_correct {X} (f : nat -> option X) :
    (forall k1 k2 y1 y2, f k1 = Some y1 -> f k2 = Some y2 -> y1 = y2) ->
    forall y, (exists k, f k = Some y) <-> (exists k, mkstat f k = Some y).
Proof.
  intros Hf x. split; intros [k Hk].
  - enough (mkstat f k = Some x \/ forall k', k' <= k -> f k' = None).
    { destruct (H) as [H' | H'].
      - eauto.
      - specialize (H' k (le_n _)). congruence.
    }
    induction k.
    + now left.
    + destruct (f k) as [y|] eqn:Heq.
      * destruct IHk as [H|H].
        -- f_equal. eapply Hf; eassumption.
        -- left. cbn. now rewrite H.
        -- specialize (H k (le_n _)). congruence.
      * 
  - induction k.
    + now exists 0.
    + cbn in Hk.
      destruct (mkstat f k) as [y|].
      * apply IHk, Hk.
      * now exists (S k).
Admitted.

Lemma stationize {X} (f : nat -> nat -> option X) :
    (forall x k1 k2 y1 y2, f x k1 = Some y1 -> f x k2 = Some y2 -> y1 = y2) ->
    exists g, (forall x, stationary (g x)) /\ forall x y, (exists k, f x k = Some y) <-> (exists k, g x k = Some y).
Proof.
  intros Hfunc.
  exists (fun x => mkstat (f x)).
  split; first (intros; apply mkstat_stationary).
  intros x y. apply mkstat_correct, Hfunc.
Qed.


Section CT.
  Variable theta : nat -> nat -> nat -> option bool.
  Variable theta_stationary : forall c x, stationary (theta c x).
  Variable theta_univ :
      forall (f : nat -> nat -> option bool),
        (forall x, stationary (f x)) ->
        exists c, forall x y, (exists k, f x k = Some y) <-> (exists k, theta c x k = Some y).
  Arguments theta_univ : clear implicits.

  Definition CTreturns c x y := exists n, theta c x n = Some y.
  Definition CThalts c x := exists y, CTreturns c x y.

  Lemma CTspecial_halting_undec : ~decidable (fun d => CThalts d d).
  Proof.
    intros [f Hf].
    destruct (theta_univ (fun n _ => if f n then None else Some true)) as [c Hc].
    1: congruence.
    specialize (Hf c). specialize (Hc c).
    destruct (f c).
    - assert (CThalts c c) as [y Hy] by firstorder.
      assert (~CTreturns c c y) by intros [_ [=]]%Hc.
      contradiction.
    - enough (false = true) by congruence.
      apply Hf. exists true. apply Hc. eauto.
  Qed.

  Section CThalt.
    Variable fs : FS.
    Hypothesis provable_decidable : decidable provable.

    Variable wrepr : nat -> nat -> sentences.
    Hypothesis Hwrepr : forall (c x : nat), CThalts c x <-> provable (wrepr c x).

    Lemma CTwrepr_dec : decidable (fun '(c, x) => CThalts c x).
    Proof.
      destruct provable_decidable as [f Hf].
      exists (fun '(c, x) => f (wrepr c x)).
      intros [c x]. unfold reflects.
      rewrite Hwrepr. apply Hf.
    Qed.

    Lemma CTwrepr : False.
    Proof.
      apply CTspecial_halting_undec.
      destruct (CTwrepr_dec) as [f Hf].
      exists (fun d => f (d, d)). firstorder.
    Qed.
  End CThalt.


  Definition CGfunc (f : nat -> nat -> bool) := forall c x y,
      (CTreturns c x y -> f c x = y).

  Lemma CG_undec : ~exists f, CGfunc f.
  Proof.
    intros [f Hf].
    destruct (theta_univ (fun c _ => Some (negb (f c c)))) as [c Hc].
    { congruence. }
    specialize (Hc c). specialize (Hf c c).
    destruct (f c c).
    - enough (true = false) by discriminate.
      apply Hf, Hc. eauto.
    - enough (false = true) by discriminate.
      apply Hf, Hc. eauto.
  Qed.

  Section CTguess.
    Variable fs : FS.
    Hypothesis provable_decidable : decidable provable.

    (*Hypothesis Hrepr : forall (f : nat -> nat -> option bool), exists (repr : nat -> bool -> sentences),
        forall x y, (exists k, f x k = Some y) -> provable (repr x y) /\ provable (neg (repr x (negb y))).*)
    Hypothesis Hrepr : forall c, { repr : nat -> bool -> sentences &
        forall x y, CTreturns c x y -> provable (repr x y) /\ provable (neg (repr x (negb y))) }.
    Arguments Hrepr : clear implicits.

    Lemma CG_dec : exists f, CGfunc f.
    Proof.
      apply decidable_iff in provable_decidable as [prov_dec].
      exists (fun c x => if prov_dec (projT1 (Hrepr c) x true) then true else false).
      intros c x [] Hret; destruct prov_dec as [H|H]; destruct (Hrepr c) as [r Hr]; cbn in H.
      - reflexivity.
      - contradict H. apply Hr, Hret.
      - destruct (consistent (r x (negb false))); intuition.
      - reflexivity.
    Qed.

    Lemma CTrepr : False.
    Proof.
      apply CG_undec, CG_dec.
    Qed.
  End CTguess.


  Section CTexpl.
    Variable fs : FS.

    Variable repr : nat -> nat -> bool -> sentences.
    Hypothesis Hrepr : forall c x y,
        CTreturns c x y -> provable (repr c x y) /\ provable (neg (repr c x (negb y))).

    Lemma CGexpl : exists s, ~provable s /\ ~provable (neg s).
    Proof.
      destruct provable_enumerable as [prov Hprov].
      pose proof sentences_discrete as sentences_discrete.
      apply discrete_iff in sentences_discrete as [sentences_eqdec].

      unshelve evar (f : nat -> nat -> nat -> option bool).
      { intros c x k.
        destruct (prov k) as [p|]. 2: exact None.

        destruct (sentences_eqdec p (repr c x true)).
        1: exact (Some true).
        destruct (sentences_eqdec p (neg(repr c x true))).
        - exact (Some false).
        - exact None. }

      unshelve evar (g : nat -> nat -> option bool).
      {
        intros c k. destruct (f c c k) as [b|].
        - exact (Some (negb b)).
        - exact None.
      }
      destruct (@stationize _ g) as (g' & Hgstat & Hgcorr).
      {
        intros x k1 k2 y1 y2.
        unfold g, f.
        destruct (prov k1) eqn:Hk1, (prov k2) eqn:Hk2; try congruence.
        repeat destruct sentences_eqdec; try congruence; subst.
        all: destruct (consistent (repr x x true)); apply Hprov; eauto.
      }

      destruct (theta_univ g' Hgstat) as [c Hc].
      exists (repr c c true).
      split.
      - intros Hp.
        eapply consistent; first exact Hp.
        apply Hprov in Hp as [k Hk].
        apply Hrepr with (y := false), Hc, Hgcorr.
        exists k. unfold g, f. rewrite Hk.
        destruct sentences_eqdec; cbn; congruence.
      - intros Hp. apply (consistent (repr c c true)); last assumption.
        apply Hprov in Hp as [k Hk].
        apply Hrepr, Hc, Hgcorr.
        exists k. unfold g, f. rewrite Hk.
        destruct sentences_eqdec.
        + destruct (@neg_no_fixpoint2 _ (repr c c true)); firstorder.
        + now destruct sentences_eqdec.
    Qed.
  End CTexpl.
End CT.

Section CTrepr.
  Variable fs : FS.

  Definition weakRepr (P : nat -> Prop) :=
    exists (repr : nat -> sentences), forall x, P x <-> provable (repr x).
  Definition valueRepr (f : nat -> nat -> option bool) :=
    exists (repr : nat -> bool -> sentences),
    forall x y, (exists k, f x k = Some y) -> provable (repr x y) /\ provable (neg (repr x (negb y))).

  Lemma complete_repr_weak_value f : (forall x, stationary (f x)) -> 
    completeness -> weakRepr (fun x => exists k, f x k = Some true) -> valueRepr f.
  Proof.
    intros Hstat complete [repr Hrepr].
    exists ((fun x (b : bool) => if b then repr x else neg (repr x))).
    intros x [] [k1 Hk1]; split; cbn.
    - firstorder.
    - destruct (complete (neg (repr x))); last easy.
      exfalso.
      eapply (deepen_provability); first exact H.
      apply Hrepr. eauto.
    - apply deep_provability_iff; first assumption.
      intros [k2 Hk2]%Hrepr.
      destruct (Compare_dec.le_ge_dec k1 k2) as [Hk|Hk].
      + specialize (Hstat x k1 k2 false Hk1 Hk). congruence.
      + specialize (Hstat x k2 k1 true Hk2 Hk). congruence.
    - apply deep_provability_iff; first exact complete.
      intros [k2 Hk2]%Hrepr.
      destruct (Compare_dec.le_ge_dec k1 k2) as [Hk|Hk].
      + specialize (Hstat x k1 k2 false Hk1 Hk). congruence.
      + specialize (Hstat x k2 k1 true Hk2 Hk). congruence.
  Qed.

  (* weakRepr -/> valueRepr in above sense: choose FS neg s := \False which is unprovable*)
  (* Can we do it without choosing FS? Maybe not, we need a more concrete idea on how general of a theorem we want to show (arbitraty FS? f? instead of existence of counter-examples) *)
  (* valueRepr -/> weakRepr: does not hold, although proving this (in Coq?) is
     going to be difficult *)
  (* Idea: we need to encode a hard (TM) problem into the inputs there valueRepr is free to do anything and choose provability such that semi-deciding provability already leads to a contradiction *)
  (* We _will_ have to do something related to computability because otherwise weak representability could just decide by itself whether p holds and return apropriatly *)

End CTrepr.

From Undecidability.FOL.Util Require Import Syntax_facts FullDeduction FullDeduction_facts FullTarski FullTarski_facts Axiomatisations.
From Undecidability.FOL Require Import PA.

Definition Q := list_theory Qeq.

Instance Qfs : FS.
Proof.
  eapply fs_fo with (T := Q).
  - Check List.nth.
  - intros x y. decide equality.
  - admit.
  - intros x y. decide equality.
  - admit.
  - admit.
Admitted.

Section Qexpl.
  Variable theta : nat -> nat -> nat -> option bool.
  Variable theta_stationary : forall c x, stationary (theta c x).
  Variable theta_univ :
      forall (f : nat -> nat -> option bool),
        (forall x, stationary (f x)) ->
        exists c, forall x y, (exists k, f x k = Some y) <-> (exists k, theta c x k = Some y).
  Arguments theta_univ : clear implicits.
  
  Context {peirce : peirce}.

  Hypothesis Hrepr : forall (f : nat -> nat -> option bool), (forall x, stationary (f x)) ->
    { repr : nat -> bool -> form | forall x y, (exists k, f x k = Some y) -> 
      Q ⊢T repr x y /\ Q ⊢T ¬repr x (negb y) }.



  Lemma Qexpl : exists φ, ~Q ⊢T φ \/ ~Q ⊢T ¬φ.
  Proof.
    Check CGexpl.
    unshelve edestruct CGexpl with (theta := theta) (fs := Qfs).
    - intros c x y.
      destruct (@Hrepr (theta c) (@theta_stationary c)) as [r Hr].
      unfold sentences. destruct Qfs.
      exists (r x y).

End Qexpl.