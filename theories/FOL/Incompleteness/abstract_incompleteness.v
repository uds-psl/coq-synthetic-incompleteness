From Undecidability.FOL.Incompleteness Require Import utils formal_systems churchs_thesis.

From Undecidability.Synthetic Require Import DecidabilityFacts.


Section abstract.
  Variable (theta : nat -> nat -\ bool).
  Hypothesis theta_universal : is_universal theta.

  Context {S : Type} {neg : S -> S} (fs : FS S neg).

  (** ** Folklore proof using soundness *)

  Lemma weakly_representable_decidable (p : nat -> Prop) :
    decidable (fs.(P)) -> 
    (exists r, weakly_represents fs p r) ->
    decidable p.
  Proof.
    intros Hdec [r Hr].
    eapply ReducibilityFacts.dec_red; last eassumption.
    now exists r. 
  Qed.

  Section halt.
    Variable (r : nat -> S).
    Hypothesis Hrepr : weakly_represents fs (fun x => exists y, theta x x ▷ y) r.

    Lemma halt_undecidability : ~decidable fs.(P).
    Proof.
      intros Hdec. eapply special_halting_undec; first eassumption.
      apply weakly_representable_decidable; eauto.
    Qed.
    Lemma halt_incompleteness' : ~complete fs.
    Proof.
      intros Hdec%complete_decidable.
      now apply halt_undecidability.
    Qed.
  End halt.
  Section halt.
    Variable (r : nat -> S).
    Hypothesis Hrepr : weakly_represents fs (fun x => exists y, theta x x ▷ y) r.

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
    Variable r : nat -> S.
    Hypothesis Hrepr : 
      strongly_separates fs (fun x => theta x x ▷ true) (fun x => theta x x ▷ false) r.

    Lemma insep_undecidability : ~decidable fs.(P).
    Proof.
      intros [f Hf].
      unshelve eapply (@no_recursively_separating theta theta_universal).
      { exact (fun c => f (r c)). } cbn. 
      intros [] c H.
      - apply Hf, Hrepr, H.
      - enough (f (r c) <> true) by now destruct f.
        intros Hc. eapply (@fs.(consistent) (r c)); firstorder.
    Qed.
  End insep.

  (** ** Strengthened proof using consistency *)

  Section insep.
    Variable r : nat -> S.
    Hypothesis Hrepr : 
      strongly_separates fs (fun x => theta x x ▷ true) (fun x => theta x x ▷ false) r.

    Lemma insep_incompleteness : exists n, independent fs (r n).
      destruct (is_provable fs) as (f & Hf1 & Hf2). 
      assert (exists c, forall b, ~f (r c) ▷ b) as [c Hc].
      { eapply recursively_separating_diverge; try eassumption.
        intros [] c Hc; firstorder. }
      exists c. firstorder.
    Qed.
  End insep.
  Section insep.
    Variable (fs' : FS S neg).
    Hypothesis fs'_extension : extension fs' fs.

    Variable r : nat -> S.
    Hypothesis Hrepr : 
      strongly_separates fs' (fun x => theta x x ▷ true) (fun x => theta x x ▷ false) r.

    Lemma strong_separability_extension : 
      strongly_separates fs (fun x => theta x x ▷ true) (fun x => theta x x ▷ false) r.
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
      intros H. 
      eapply insep_undecidability; eauto using strong_separability_extension.
    Qed.
  End insep.

End abstract.
