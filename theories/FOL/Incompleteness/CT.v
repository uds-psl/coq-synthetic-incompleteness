From Undecidability.FOL.Incompleteness Require Import FS.
From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
From Undecidability.Shared Require Import Dec embed_nat.



Section CT.
  Variable phi : nat -> nat -> nat -> option nat.
  Hypothesis CT : forall (f : nat -> nat -> option nat), exists c, forall x k, phi c x k = f x k.

  Definition CTreturns c x y := exists n, phi c x n = Some y.
  Definition CThalts c x := exists y, CTreturns c x y.

  Lemma CTspecial_halting_undec : ~decidable (fun d => CThalts d d).
  Proof.
    intros [f Hf].
    destruct (CT (fun n _ => if f n then None else Some 1)) as [c Hc].
    specialize (Hf c). specialize (Hc c).
    destruct (f c).
    - enough (CThalts c c) as (?&?&?) by congruence.
      now apply Hf.
    - enough (false = true) by congruence.
      apply Hf. now exists 1, 0.
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


  Definition CGpred (p : nat -> nat -> Prop) := forall c x,
      (CTreturns c x 0 -> p c x) /\
        (CTreturns c x 1 -> ~p c x).

  Lemma CGpred_undec p : CGpred p -> ~exists f, forall c x, p c x <-> f c x = true.
  Proof.
    intros HCG [f Hf].
    destruct (CT (fun c _ => if f c c then Some 1 else Some 0)) as [c Hc].
    specialize (Hc c). specialize (Hf c c). specialize (HCG c c).
    destruct (f c c); firstorder.
  Qed.

  Section CTguess.
    Variable fs : FS.
    Hypothesis provable_decidable : decidable provable.

    (* TODO check how this notion of representability turns up in Kleene *)
    Variable repr : nat -> nat -> nat -> sentences.
    Hypothesis Hrepr : forall (c x y : nat),
        (CTreturns c x y -> provable (repr c x y)) /\
          forall y', CTreturns c x y -> y <> y' -> ~provable ((repr c x y')).

    Lemma CGpred_dec : exists f p, CGpred p /\ forall c x, p c x <-> f c x = true.
    Proof.
      apply decidable_iff in provable_decidable as [prov_dec].
      exists (fun c x => if prov_dec (repr c x 0) then true else false).
      exists (fun c x => if prov_dec (repr c x 0) then True else False).
      split.
      - intros c x. split.
        + intros Hprov % Hrepr. now destruct prov_dec.
        + intros Hret ?. destruct prov_dec. 2: easy.
          destruct (Hrepr c x 1) as [_ Hfunc].
          now apply (Hfunc 0).
      - intros c x. destruct prov_dec; easy.
    Qed.

    Lemma CTrepr : False.
    Proof.
      destruct CGpred_dec as (f & p & HCG & Hdec).
      apply (CGpred_undec HCG); eauto.
    Qed.
  End CTguess.

  Section CTexpl.
    Variable fs : FS.

    Variable repr : nat -> nat -> nat -> sentences.
    Hypothesis Hrepr : forall (c x y : nat),
        (CTreturns c x y -> provable (repr c x y)) /\
          forall y', CTreturns c x y -> y <> y' -> ~provable ((repr c x y')).

    Lemma CGexpl : exists s, ~provable s /\ ~provable (neg s).
    Proof.
      destruct provable_enumerable as [prov Hprov].
      pose proof sentences_discrete as sentences_discrete.
      apply discrete_iff in sentences_discrete as [sentences_eqdec].

      unshelve evar (f : nat -> nat -> nat -> option bool).
      { intros c x k.
        destruct (prov k) as [p|]. 2: exact None.

        destruct (sentences_eqdec p (repr c x 0)).
        1: exact (Some true).
        destruct (sentences_eqdec p (neg(repr c x 0))).
        - exact (Some false).
        - exact None. }

      unshelve evar (g : nat -> nat -> option nat).
      {
        intros c k. destruct (f c c k) as [[]|].
        - exact (Some 1).
        - exact (Some 0).
        - exact None.
      }

      destruct (CT g) as [c Hc].
      exists (repr c c 0).
      split.
      - intros Hp.
        apply Hrepr with (c := c) (x := c) (y := 1) (y' := 0).
        + unfold CTreturns.
          apply Hprov in Hp as [k Hk].
          exists k. rewrite Hc.
          unfold g, f. rewrite Hk.
          destruct sentences_eqdec; congruence.
        + discriminate.
        + assumption.
      - intros Hp. unshelve eapply (consistent (repr c c 0) _ Hp).
        apply Hrepr. apply Hprov in Hp as [k Hk].
        exists k. rewrite Hc.
        unfold g, f. rewrite Hk.
        destruct sentences_eqdec.
        + destruct (@neg_no_fixpoint2 _ (repr c c 0)); firstorder.
        + now destruct sentences_eqdec.
    Qed.
  End CTexpl.
End CT.
