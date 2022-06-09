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
      exists (fun x => f (r x)).
      unfold decider,reflects in *.
      intros x. rewrite <-Hf. apply Hrepr.
    Qed.
  End halt.
  Section halt.
    Variable (r : nat -> S).
    Hypothesis Hrepr : forall c, (exists y, theta c c ▷ y) <-> fs ⊢F r c.

    Lemma halt_incompleteness : exists n, independent fs (r n).
    Proof.
      destruct (is_provable fs) as (f & Hf1 & Hf2). 
      assert (exists c, forall b, ~f (r c) ▷ b) as [d Hd].
      { eapply special_halting_diverge; try eassumption.
        - intros d H. firstorder.
        - intros d H y Hy.
          eapply (fs.(consistent) (r d)); firstorder. }
      exists d. split; firstorder.
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
      destruct (is_provable fs) as (f & Hf1 & Hf2). 
      assert (exists c, forall b, ~f (r c) ▷ b) as [c Hc].
      { eapply recursively_separating_diverge; try eassumption.
        intros [] c Hc; firstorder. }
      exists c. split; firstorder.
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
