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
      destruct (is_provable fs) as (f & Hf1 & Hf2). 

      unshelve evar (g : nat -\ bool).
      { intros x. unshelve eexists.
        { intros k. exact (core (f (r x)) k). }
        apply f. }
      destruct (theta_universal g) as [c Hc]. 
      assert (exists c, forall b, ~g c ▷ b) as [d Hd].
      { eapply special_halting_diverge; try eassumption.
        - intros d [k Hk]. apply Hrepr, Hf1. exists k.
          apply Hk.
        - intros d [k Hk] y Hy.
          eapply (fs.(consistent)).
          + apply Hrepr. eauto.
          + apply Hf2. exists k. apply Hk. }
      exists d. split.
      - intros H. apply (Hd true).
        apply Hf1 in H as [k Hk]. exists k. apply Hk.
      - intros H. apply (Hd false).
        apply Hf2 in H as [k Hk]. exists k. apply Hk.
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

    Lemma strong_separability_extension : forall c,
      (theta c c ▷ true -> fs ⊢F r c) /\
      (theta c c ▷ false -> fs ⊢F neg (r c)).
    Proof.
      firstorder.
    Qed.

    Lemma insep_essential_incompleteness : exists n, independent fs (r n).
    Proof.
      apply (@insep_incompleteness r).
      apply strong_separability_extension.
    Qed.
    Lemma insep_essential_undecidability : ~decidable (fun s => fs ⊢F s).
    Proof.
      intros H. eapply (@insep_undecidability H).
      apply strong_separability_extension.
    Qed.
  End insep.

End abstract.
