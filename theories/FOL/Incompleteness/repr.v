From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
From Undecidability.Shared Require Import Dec embed_nat.

From Undecidability.FOL.Util Require Import Syntax_facts FullDeduction FullDeduction_facts FullTarski FullTarski_facts Axiomatisations FA_facts Syntax.
From Undecidability.FOL Require Import PA.
From Undecidability.FOL.Proofmode Require Import Theories ProofMode Hoas.
From Undecidability.FOL.Incompleteness Require Import formal_systems fol qdec.


From Equations Require Import Equations DepElim.
Require Import String List.
Open Scope string_scope.
Section Qtrichotomy.
  Existing Instance PA_funcs_signature.
  Existing Instance PA_preds_signature.

  (* Cannot be concrete here due to bug in Proofmode *)
  Variable (p : peirce).

  Lemma Qdec_le x : Qeq ⊢ ∀((num x ⧀= $0) ∨ ($0 ⧀= (num x))).
  Proof.
    induction x; fstart; fintro "y".
    - fleft. rewrite pless_eq. fexists y. 
      frewrite (ax_add_zero y). fapply ax_refl.
    - fassert (ax_cases); first ctx.
      fdestruct ("H" y) as "[H|[y' H]]".
      + fright. rewrite pless_eq. fexists (σ (num x)). 
        frewrite "H". frewrite (ax_add_zero (σ num x)).
        fapply ax_refl.
      + fspecialize (IHx y'). rewrite !pless_subst in IHx. cbn in IHx. rewrite num_subst in IHx. 
        fdestruct IHx.
        * fleft. rewrite !pless_eq. custom_simpl.
          fdestruct "H0". fexists x0. frewrite "H". frewrite "H0".
          fapply ax_sym. fapply ax_add_rec.
        * fright. rewrite !pless_eq. custom_simpl.
          fdestruct "H0". fexists x0. frewrite "H". frewrite "H0".
          fapply ax_sym. fapply ax_add_rec.
  Qed.
End Qtrichotomy.


Section value_disjoint.
  Existing Instance PA_funcs_signature.
  Existing Instance PA_preds_signature.
  Existing Instance intu.


  Variable P1 P2 : nat -> Prop.
  Hypothesis P_disjoint : forall x, P1 x -> P2 x -> False.

  Variable φ1 φ2 : form.
  Hypothesis (φ1_bounded : bounded 2 φ1) (φ2_bounded : bounded 2 φ2).
  Hypothesis (φ1_qdec : Qdec φ1) (φ2_qdec : Qdec φ2).
  Hypothesis (φ1_sem : forall x ρ, P1 x <-> interp_nat; ρ ⊨ ∃ φ1[(num x) ..])
             (φ2_sem : forall x ρ, P2 x <-> interp_nat; ρ ⊨ ∃ φ2[(num x) ..]).


  Definition φ1' := φ1 ∧ ∀ $0 ⧀= $2 ~> φ2[$1 .: $0 ..] ~> ⊥.
  Definition φ2' := φ2 ∧ ∀ $0 ⧀= $2 ~> φ1[$1 .: $0 ..] ~> ⊥.

  Lemma φ1'_bounded : bounded 2 φ1'.
  Proof.
    unfold φ1'. rewrite pless_eq.
    repeat solve_bounds.
    - assumption.
    - eapply subst_bound; first eassumption.
      intros [|[|n]] H; cbn; solve_bounds.
  Qed.
  Lemma φ2'_bounded : bounded 2 φ2'.
  Proof.
    unfold φ2'. rewrite pless_eq.
    repeat solve_bounds.
    - assumption.
    - eapply subst_bound; first eassumption.
      intros [|[|n]] H; cbn; solve_bounds.
  Qed.
  Lemma φ1'_qdec : Qdec φ1'.
  Proof.
    apply Qdec_and; first assumption.
    apply (@Qdec_bounded_forall _ $1).
    apply Qdec_impl.
    - apply Qdec_subst, φ2_qdec.
    - apply Qdec_bot.
  Qed.
  Lemma φ2'_qdec : Qdec φ2'.
  Proof.
    apply Qdec_and; first assumption.
    apply (@Qdec_bounded_forall _ $1).
    apply Qdec_impl.
    - apply Qdec_subst, φ1_qdec.
    - apply Qdec_bot.
  Qed.

  Local Lemma DR1 x : P1 x -> Qeq ⊢ ∃ φ1'[(num x)..].
  Proof.
    intros HP1. apply Σ1_completeness. 
    { constructor. apply Σ1_subst. constructor. apply φ1'_qdec. }
    { constructor. eapply subst_bound; first apply φ1'_bounded.
      intros [|[|n]] H; try solve_bounds. apply num_bound. }
    intros ρ. pose proof HP1 as H. rewrite (φ1_sem _ ρ) in H.
    destruct H as [k Hk]. exists k.
    split; first assumption.
    cbn. intros k' _ Hk'. apply (@P_disjoint x).
    - eapply φ1_sem. exists k. apply Hk.
    - eapply φ2_sem with (ρ := k .: ρ). exists k'.
      rewrite subst_comp in Hk'.
      erewrite bounded_subst. 1-2: eassumption.
      intros [|[|n]] H; cbn.
      + now rewrite num_subst.
      + easy.
      + lia.
  Qed.
  Local Lemma DR1' x : P2 x -> interp_nat ⊨= ∃ φ2'[(num x)..].
  Proof. Admitted.
  Local Lemma DR2 x : P2 x -> Qeq ⊢ ¬∃ φ1'[(num x)..].
  Proof. 
    cbn. intros HP2. 
    assert (exists k, Qeq ⊢ φ2'[(num x)..][(num k)..]) as [k Hk].
    { apply Σ1_witness.
      - constructor. apply Qdec_subst. apply φ2'_qdec.
      - eapply subst_bound; first apply φ2'_bounded.
        intros [|[|n]] H; try solve_bounds. apply num_bound.
      - apply Σ1_completeness.
        + constructor. apply Σ1_subst. constructor. apply φ2'_qdec.
        + constructor. eapply subst_bound; first apply φ2'_bounded.
          intros [|[|n]] H; try solve_bounds. apply num_bound.
        + apply DR1', HP2. }
    cbn in Hk. 

    custom_simpl. unfold "↑". fstart.
    fintros "H". fdestruct "H". fdestruct "H".

    pose proof (Qdec_le intu k). fspecialize (H x0). 
    rewrite !pless_subst, !num_subst in H. cbn in H.
    fdestruct H.
    - fapply ("H0" (num k)).
      + rewrite pless_subst. simpl_subst. ctx.
      + simpl_subst. fassert (φ2[(num x)..][(num k)..]).
        { fstop. eapply CE1, Weak; eauto. }
        rewrite !subst_comp. erewrite bounded_subst.
        * fapply "H2".
        * eassumption.
        * intros [|[|[|l]]]; cbn; (now rewrite ?num_subst + lia).
    - rewrite !pless_subst in Hk.  cbn in Hk. rewrite num_subst in Hk.
      fassert (∀ $0 ⧀= num k ~> ¬ φ1[$1 .: $0..][up (num x)..][up (num k)..]).
      { fstop. eapply CE2, Weak; eauto. }
      fapply ("H2" x0).
      + rewrite pless_subst. simpl_subst. fapply "H1".
      + rewrite !subst_comp. pattern (φ1[(num x).. >> subst_term x0..]). erewrite bounded_subst.
        * fapply "H".
        * eassumption.
        * intros [|[|[|l]]]; cbn; (now rewrite ?num_subst + lia).
  Qed.

  Lemma weak_strong : exists φ, Σ1 φ /\
    (forall x, P1 x -> Qeq ⊢ φ[(num x)..]) /\
    (forall x, P2 x -> Qeq ⊢ ¬φ[(num x)..]).
  Proof.
    admit.
  Admitted.


End value_disjoint.
