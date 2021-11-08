From Undecidability.FOL.Incompleteness Require Import FS.
From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
From Undecidability.Shared Require Import Dec embed_nat.



Module CT. Section CT.
  Variable phi : nat -> nat -> nat -> option nat.
  Hypothesis CT : forall f, exists c, forall x, exists n, phi c x n = Some (f x).

  Definition CTreturns c x y := exists n, phi c x n = Some y.
  Definition CThalts c x := exists y, CTreturns c x y.

  Definition CGpred (p : nat -> nat -> Prop) := forall c x,
      (CTreturns c x 0 -> p c x) /\
        (CTreturns c x 1 -> ~p c x).

  Lemma CGpred_undec p : CGpred p -> ~exists f, forall c x, p c x <-> f c x = true.
  Proof.
    intros HCG [f Hf].
    destruct (CT (fun c => if f c c then 1 else 0)) as [c Hc].
    specialize (Hc c). specialize (Hf c c). specialize (HCG c c).
    destruct (f c c).
    - apply HCG; tauto.
    - enough (false = true) by discriminate. apply Hf, HCG, Hc.
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
End CT. End CT.

Module CTexpl. Section CTexpl.
  Variable phi : nat -> nat -> nat -> option nat.
  Hypothesis CT : forall f, exists c, forall x n, phi c x n = f x n.

  Definition CTreturns c x y := exists n, phi c x n = Some y.
  Definition CThalts c x := exists y, CTreturns c x y.

  Definition CGpred (p : nat -> nat -> Prop) := forall c x,
      (CTreturns c x 0 -> p c x) /\
        (CTreturns c x 1 -> ~p c x).

  Lemma CGpred_undec p : CGpred p -> ~exists f, forall c x, p c x <-> f c x = true.
  Proof.
    intros HCG [f Hf].
    destruct (CT (fun c _ => if f c c then Some 1 else Some 0)) as [c Hc].
    specialize (Hc c). specialize (Hf c c). specialize (HCG c c).
    destruct (f c c).
    - apply HCG; firstorder.
    - enough (false = true) by discriminate. firstorder.
  Qed.

  Section CTguess.
    Variable fs : FS.

    Variable repr : nat -> nat -> nat -> sentences.
    Hypothesis Hrepr : forall (c x y : nat),
        (CTreturns c x y -> provable (repr c x y)) /\
          forall y', CTreturns c x y -> y <> y' -> ~provable ((repr c x y')).


    Definition CGf
               (prov: nat -> option sentences) (Hprov : enumerator prov provable)
               (sentences_eqdec : forall (x y : sentences), Dec.dec (x=y)) :
      nat -> nat -> nat -> option nat.
    Proof.
      intros c x k.
      destruct (prov k) as [p|]. 2: exact None.

      destruct (sentences_eqdec p (repr c x 0)).
      1: exact (Some 0).
      destruct (sentences_eqdec p (neg(repr c x 0))).
      - exact (Some 1).
      - exact None.
    Defined.


    Lemma CGpred_dec (complete : completeness) : exists (f : nat -> nat -> nat -> option nat) p, CGpred p /\ forall c x, exists k y, f c x k = Some y /\ (y = 0 <-> p c x).
    Proof.
      destruct provable_enumerable as [prov Hprov].
      pose proof sentences_discrete as sentences_discrete.
      apply discrete_iff in sentences_discrete as [sentences_eqdec].
      pose (f := @CGf prov Hprov sentences_eqdec).
      exists f, (fun c x => exists k, f c x k = Some 0).
      split.
      - intros c x. split.
        + intros Hret.
          apply Hrepr, Hprov in Hret as [k Hk].
          exists k. unfold f, CGf. simpl.
          destruct (prov k). 2: congruence.
          destruct sentences_eqdec; congruence.
        + intros Hret [k Hk].
          unfold f, CGf in Hk.
          destruct prov eqn:H. 2: congruence.
          destruct sentences_eqdec.
          2: destruct sentences_eqdec; congruence.
          eapply Hrepr.
          * exact Hret.
          * now instantiate (1 := 0).
          * apply Hprov. exists k. congruence.
      - intros c x.
        destruct (complete (repr c x 0)) as [[k Hk]%Hprov|[k Hk]%Hprov].
        + exists k, 0. enough (f c x k = Some 0) by firstorder.
          unfold f, CGf.
          destruct prov. 2: congruence.
          destruct sentences_eqdec; congruence.
        + exists k, 1.
          split.
          * unfold f, CGf.
            destruct (prov k). 2: congruence.
            destruct (sentences_eqdec).
            -- edestruct (@neg_no_fixpoint_comp _ complete (repr c x 0)); congruence.
            -- destruct (sentences_eqdec); congruence.
          * split. 1: discriminate.
            intros [k' Hk'].
            unfold f, CGf in Hk'.
            destruct (prov k') eqn:H'. 2: congruence.
            destruct sentences_eqdec as [->|]. 2: now destruct sentences_eqdec.
            exfalso. eapply consistent; apply Hprov.
            -- exists k'. eassumption.
            -- now exists k.
    Qed.
    Lemma CTrepr : False.
    Proof.
      admit.
    Abort.

    Lemma CGexpl : exists s, ~provable s /\ ~provable (neg s).
    Proof.
      destruct provable_enumerable as [prov Hprov].
      pose proof sentences_discrete as sentences_discrete.
      apply discrete_iff in sentences_discrete as [sentences_eqdec].
      pose (f := @CGf prov Hprov sentences_eqdec).

      pose (g := fun c k => match f c c k with
                          Some 0 => Some 1
                        | Some 1 => Some 0
                        | _ => None end).
      destruct (CT g) as [c Hc].
      exists (repr c c 0).
      split.
      - intros Hp. eapply Hrepr.
        3: exact Hp.
        + instantiate (1 := 1).
          unfold CTreturns.
          enough (exists k, g c k = Some 1) as [k Hk].
          { exists k. rewrite <-Hk. apply Hc. }
          apply Hprov in Hp as [k Hk].
          exists k. unfold g, f, CGf.
          destruct (prov k) eqn:Heq. 2: congruence.
          destruct sentences_eqdec. 2: congruence.
          reflexivity.
        + discriminate.
      - intros Hp. eapply Hrepr.
        instantiate (1 := 0). instantiate (2 := c). instantiate (1 := c). 2: instantiate (1 := 1).
        + apply Hprov in Hp as [k Hk]. exists k.
          rewrite Hc. unfold g, f, CGf.
          destruct (prov k) eqn:Heq. 2: congruence.
          destruct sentences_eqdec.
          2: destruct sentences_eqdec; congruence.
          edestruct (@neg_no_fixpoint).
          * apply Hprov. exists k. eassumption.
          * congruence.
        + discriminate.
        + apply Hrepr.

    Admitted.
  End CTguess.
End CTexpl. End CTexpl.
