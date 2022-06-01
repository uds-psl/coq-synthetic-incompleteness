From Undecidability.FOL.Incompleteness Require Import utils formal_systems churchs_thesis.

From Undecidability.Synthetic Require Import DecidabilityFacts.

Section abstract.
  Variable (theta : nat -> nat -\ bool).
  Hypothesis theta_universal : is_universal theta.

  Context {S : Type} {neg : S -> S} (fs : FS S neg).

  Section halt.
    Hypothesis prov_dec : decidable fs.(P).

    Variable (r : nat -> S).
    Hypothesis Hrepr : forall c, (exists y, theta c c ▷ y) <-> fs ⊢F r c.

    Lemma halt_undecidability : False.
    Proof.
      destruct prov_dec as [f Hf].
      enough (decidable (fun c => exists y, theta c c ▷ y)).
      { now eapply special_halting_undec. }
      exists (fun c => f (r c)).
      unfold decider,reflects in *.
      intros x. rewrite <-Hf. apply Hrepr.
    Qed.
  End halt.
  Section halt.
    Variable (r : nat -> S).
    Hypothesis Hrepr : forall c, (exists y, theta c c ▷ y) <-> fs ⊢F r c.

    Lemma halt_incompleteness : exists n, independent fs (r n).
    Proof.
      destruct fs.(P_enumerable) as [prov Hprov].
      pose proof fs.(S_discrete) as [S_eqdec]%discrete_iff.

      unshelve evar (f : nat -\ bool).
      { intros x. unshelve eexists.
        { intros k. 
          refine (match prov k with Some s => _ | None => None end).
          refine (if S_eqdec (neg (r x)) s then Some true else None). }
        cbn. intros y1 y2 k1 k2 H1 H2.
        destruct (prov k1), (prov k2); repeat destruct S_eqdec; try congruence. }

      destruct (theta_universal f) as [c Hc]. exists c.
      enough (fs ⊢F r c <-> fs ⊢F neg (r c)) as H.
      { split; intros H'; apply (consistent fs (r c)); tauto. }
      rewrite <-Hrepr. split.
      - intros [y Hy]. rewrite <-Hc in Hy.
        destruct Hy as [k Hk]. cbn in Hk.
        destruct (prov k) eqn:H; try destruct S_eqdec; try congruence.
        apply Hprov. exists k. congruence.
      - intros [k Hk]%Hprov. exists true. rewrite <-Hc. exists k.
        cbn. rewrite Hk. now destruct S_eqdec.
    Qed.
  End halt.

  Section insep.
    Hypothesis prov_dec : decidable fs.(P).

    Variable r : nat -> S.
    Hypothesis Hrepr : forall c,
      (theta c c ▷ true -> fs ⊢F r c) /\
      (theta c c ▷ false -> fs ⊢F neg (r c)).

    Lemma insep_undecidability : False.
    Proof.
      destruct prov_dec as [f Hf].
      unshelve eapply (@no_recursively_separating theta theta_universal).
      { exact (fun c => f (r c)). } cbn. 
      intros [] c H.
      - apply Hf, Hrepr, H.
      - enough (f (r c) <> true) by now destruct f.
        unfold decider, reflects in Hf.
        rewrite <-Hf. apply deepen_provability, Hrepr, H.
    Qed.
  End insep.

  Section insep.
    Variable r : nat -> S.
    Hypothesis Hrepr :  forall c,
      (theta c c ▷ true -> fs ⊢F r c) /\
      (theta c c ▷ false -> fs ⊢F neg (r c)).

    Lemma insep_incompleteness : exists n, independent fs (r n).
      destruct fs.(P_enumerable) as [prov Hprov].
      pose proof fs.(S_discrete) as [S_eqdec]%discrete_iff.
      destruct (is_provable fs) as [Pdec HPdec].

      unshelve evar (f : nat -\ bool).
      { intros c. unshelve eexists.
        { intros k. exact ((Pdec (r c)).(core) k). }
        cbn. intros y1 y2 k1 k2 H1 H2.
        apply ((Pdec (r c)).(valid) y1 y2 k1 k2 H1 H2). }
      assert (forall b c, Pdec (r c) ▷ b -> f c ▷ b) as Hfcorr.
      { intros b c [k Hk]. exists k. exact Hk. }
      destruct (@recursively_separating_diverge theta theta_universal f) as [c Hc].
      { intros [] c Hc; apply Hfcorr, HPdec, Hrepr, Hc. }
      exists c. split.
      - specialize (Hc true). contradict Hc.
        apply Hfcorr, HPdec, Hc.
      - specialize (Hc false). contradict Hc.
        apply Hfcorr, HPdec, Hc.
    Qed.
  End insep.
  Section insep.
    Variable (fs' : FS S neg).
    Hypothesis fs'_extension : extension fs' fs.

    Variable r : nat -> S.
    Hypothesis Hrepr : forall c,
      (theta c c ▷ true -> fs' ⊢F r c) /\
      (theta c c ▷ false -> fs' ⊢F neg (r c)).

    Lemma insep_essential_incompleteness : exists n, independent fs (r n).
    Proof.
      apply (@insep_incompleteness r).
      intros c. destruct (Hrepr c) as [Hr1 Hr2].
      split; intros H.
      - apply fs'_extension. auto.
      - apply fs'_extension. auto.
    Qed.
  End insep.

  Section repr.
    Lemma weak_representability_strong_separability r :
      complete fs ->
      (( forall c, theta c c ▷ true <-> fs ⊢F r c) ->
      ( forall c, (theta c c ▷ true -> fs ⊢F r c) /\
      (theta c c ▷ false -> fs ⊢F neg (r c)))).
    Proof.
      intros complete. intros Hr c.
      split.
      + firstorder.
      + intros H. apply undeepen_provability. 1: assumption.
        intros Htrue%Hr. enough (true = false) by discriminate.
        eapply (@part_functional _ (theta c c)); assumption.
    Qed.
  End repr.
End abstract.
