From Undecidability.FOL.Incompleteness Require Import utils formal_systems epf.

From Undecidability.Synthetic Require Import DecidabilityFacts.


Section abstract.
  Variable (theta : nat -> nat -\ bool).
  Hypothesis theta_universal : is_universal theta.

  Context {S : Type} {neg : S -> S} (fs : FS S neg).

  (** ** Folklore proof using soundness *)

  (* Any weakly representable predicate is decidable *)
  Lemma weakly_representable_decidable (p : nat -> Prop) :
    decidable (fs.(fprv)) -> 
    (exists r, weakly_represents fs p r) ->
    decidable p.
  Proof.
    intros Hdec [r Hr].
    eapply ReducibilityFacts.dec_red; last eassumption.
    now exists r. 
  Qed.

  (* Any formal system weakly representing the halting problem is undecidable and therefore incomplete *)
  Section halt.
    Variable (r : nat -> S).
    Hypothesis Hrepr : weakly_represents fs (self_halting theta) r.

    Lemma halt_undecidability : ~decidable fs.(fprv).
    Proof.
      intros Hdec. eapply self_halting_undec; first eassumption.
      apply weakly_representable_decidable; eauto.
    Qed.

    Lemma halt_incompleteness' : ~complete fs.
    Proof.
      intros Hdec%complete_decidable.
      now apply halt_undecidability.
    Qed.

  End halt.
  (* Any formal system weakly representing the halting problem has an independent sentence *)
  Section halt.
    Variable (r : nat -> S).
    Hypothesis Hrepr : weakly_represents fs (self_halting theta) r.

    Lemma halt_incompleteness : exists n, independent fs (r n).
    Proof.
      destruct (is_provable fs) as (f & Hf1 & Hf2). 
      assert (exists c, forall b, ~f (r c) ▷ b) as [d Hd].
      { eapply self_halting_diverge; try eassumption.
        intros c. rewrite <-Hf1. symmetry. apply Hrepr. }
      exists d. split; firstorder.
    Qed.

  End halt.

  (** ** Strengthened proof using consistency *)

  (* Any formal system strongly separating two recursively inseparable sets is undecidable *)
  Section insep.
    Variable r : nat -> S.
    Hypothesis Hrepr : 
      strongly_separates fs (theta_self_return theta true) (theta_self_return theta false) r.

    Lemma insep_undecidability : ~decidable fs.(fprv).
    Proof.
      intros [f Hf].
      unshelve eapply (@no_recursively_separating theta theta_universal).
      { exact (fun c => f (r c)). } cbn. 
      intros [] c H.
      - apply Hf, Hrepr, H.
      - enough (f (r c) <> true) by now destruct f.
        intros Hc. eapply (@fs.(consistent) (r c)); firstorder.
    Qed.

    (* We could deduce incompleteness here already, similar to halt_incompleteness' *)

  End insep.

  (* Any formal system strongly separating two recursively inseparable sets has an independent sentence *)
  Section insep.
    Variable r : nat -> S.
    Hypothesis Hrepr : 
      strongly_separates fs (theta_self_return theta true) (theta_self_return theta false) r.

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
      strongly_separates fs' (theta_self_return theta true) (theta_self_return theta false) r.

    (* If a formal system strongly separates two predicates, its extensions do, too *)
    Lemma strong_separability_extension : 
      strongly_separates fs (theta_self_return theta true) (theta_self_return theta false) r.
    Proof.
      firstorder.
    Qed.

    (* Essential incompleteness and undecidability *)
    Theorem insep_essential_incompleteness : exists n, independent fs (r n).
    Proof.
      apply (@insep_incompleteness r).
      apply strong_separability_extension.
    Qed.

    Theorem insep_essential_undecidability : ~decidable (fun s => fs ⊢F s).
    Proof.
      intros H. 
      eapply insep_undecidability; eauto using strong_separability_extension.
    Qed.

  End insep.

End abstract.
