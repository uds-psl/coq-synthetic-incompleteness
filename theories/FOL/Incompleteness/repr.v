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

  Section value_disjoint'.
    Variable φ1 φ2 : form.
    Hypothesis (φ1_bounded : bounded 2 φ1) (φ2_bounded : bounded 2 φ2).
    Hypothesis (φ1_qdec : Qdec φ1) (φ2_qdec : Qdec φ2).
    Hypothesis (φ1_syn : forall x, P1 x <-> Qeq ⊢ ∃ φ1[(num x) ..])
               (φ2_syn : forall x, P2 x <-> Qeq ⊢ ∃ φ2[(num x) ..]).

    Local Lemma φ1_sem x ρ : P1 x <-> interp_nat; ρ ⊨ ∃ φ1[(num x) ..].
    Proof.
      rewrite φ1_syn.
      split.
      - intros H%soundness. apply H, nat_is_Q_model.
      - apply Σ1_completeness.
        + do 2 constructor. now apply Qdec_subst.
        + solve_bounds. eapply subst_bound; last eassumption.
          intros [|[|n]] H; cbn. 2-3: solve_bounds.
          apply num_bound.
    Qed.
    Local Lemma φ2_sem x ρ : P2 x <-> interp_nat; ρ ⊨ ∃ φ2[(num x) ..].
    Proof.
      rewrite φ2_syn.
      split.
      - intros H%soundness. apply H, nat_is_Q_model.
      - apply Σ1_completeness.
        + do 2 constructor. now apply Qdec_subst.
        + solve_bounds. eapply subst_bound; last eassumption.
          intros [|[|n]] H; cbn. 2-3: solve_bounds.
          apply num_bound.
    Qed.
          
    Definition φ1' := φ1 ∧ ∀ $0 ⧀= $2 ~> φ2[$1 .: $0 ..] ~> ⊥.
    Definition φ2' := φ2 ∧ ∀ $0 ⧀= $2 ~> φ1[$1 .: $0 ..] ~> ⊥.

    Lemma φ1'_bounded : bounded 2 φ1'.
    Proof.
      unfold φ1'. rewrite pless_eq.
      repeat solve_bounds.
      - assumption.
      - eapply subst_bound; last eassumption.
        intros [|[|n]] H; cbn; solve_bounds.
    Qed.
    Lemma φ2'_bounded : bounded 2 φ2'.
    Proof.
      unfold φ2'. rewrite pless_eq.
      repeat solve_bounds.
      - assumption.
      - eapply subst_bound; last eassumption.
        intros [|[|n]] H; cbn; solve_bounds.
    Qed.
    Lemma φ1'_qdec : Qdec φ1'.
    Proof.
      apply Qdec_and; first assumption.
      apply (@Qdec_bounded_forall _ 1).
      apply Qdec_impl.
      - apply Qdec_subst, φ2_qdec.
      - apply Qdec_bot.
    Qed.
    Lemma φ2'_qdec : Qdec φ2'.
    Proof.
      apply Qdec_and; first assumption.
      apply (@Qdec_bounded_forall _ 1).
      apply Qdec_impl.
      - apply Qdec_subst, φ1_qdec.
      - apply Qdec_bot.
    Qed.

    Local Lemma DR1 x : P1 x -> Qeq ⊢ ∃ φ1'[(num x)..].
    Proof.
      intros HP1. eapply Σ1_completeness with (ρ := fun _ => 0).
      { constructor. apply Σ1_subst. constructor. apply φ1'_qdec. }
      { constructor. eapply subst_bound; last apply φ1'_bounded.
        intros [|[|n]] H; try solve_bounds. apply num_bound. }
      pose proof HP1 as H. erewrite (φ1_sem _ _) in H.
      destruct H as [k Hk]. exists k.
      split; first eassumption.
      cbn. intros k' _ Hk'. apply (@P_disjoint x).
      - eapply φ1_sem. exists k. apply Hk.
      - eapply φ2_sem with (ρ := k .: (fun _ => 0)). exists k'.
        rewrite subst_comp in Hk'.
        erewrite bounded_subst. 1-2: eassumption.
        intros [|[|n]] H; cbn.
        + now rewrite num_subst.
        + easy.
        + lia.
    Qed.
    Local Lemma DR1' x : P2 x -> Qeq ⊢ ∃ φ2'[(num x)..].
    Proof. 
      intros HP1. eapply Σ1_completeness with (ρ := fun _ => 0).
      { constructor. apply Σ1_subst. constructor. apply φ2'_qdec. }
      { constructor. eapply subst_bound; last apply φ2'_bounded.
        intros [|[|n]] H; try solve_bounds. apply num_bound. }
      pose proof HP1 as H. erewrite (φ2_sem _ _) in H.
      destruct H as [k Hk]. exists k.
      split; first eassumption.
      cbn. intros k' _ Hk'. apply (@P_disjoint x).
      - eapply φ1_sem with (ρ := k .: (fun _ => 0)). exists k'.
        rewrite subst_comp in Hk'.
        erewrite bounded_subst. 1-2: eassumption.
        intros [|[|n]] H; cbn.
        + now rewrite num_subst.
        + easy.
        + lia.
      - eapply φ2_sem. exists k. apply Hk.
    Qed.
    Local Lemma DR2 x : P2 x -> Qeq ⊢ ¬∃ φ1'[(num x)..].
    Proof. 
      cbn. intros HP2. 
      assert (exists k, Qeq ⊢ φ2'[(num x)..][(num k)..]) as [k Hk].
      { apply Σ1_witness.
        - constructor. apply Qdec_subst. apply φ2'_qdec.
        - eapply subst_bound; last apply φ2'_bounded.
          intros [|[|n]] H; try solve_bounds. apply num_bound.
        - apply Σ1_completeness with (ρ := id).
          + constructor. apply Σ1_subst. constructor. apply φ2'_qdec.
          + constructor. eapply subst_bound; last apply φ2'_bounded.
            intros [|[|n]] H; try solve_bounds. apply num_bound.
          + apply DR1', soundness in HP2. apply HP2.
            apply nat_is_Q_model. }
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

    Lemma weak_strong' : exists φ, Σ1 φ /\ bounded 1 φ /\
      (forall x, P1 x -> Qeq ⊢ φ[(num x)..]) /\
      (forall x, P2 x -> Qeq ⊢ ¬φ[(num x)..]).
    Proof.
      exists (∃ φ1'[$1 .: $0 ..]). repeat apply conj.
      { do 2 constructor. apply Qdec_subst, φ1'_qdec. }
      { constructor. eapply subst_bound; last apply φ1'_bounded.
        intros [|[|n]]; solve_bounds. }
      - intros x H%DR1. 
        replace ((_)[_]) with (∃ φ1'[(num x)..]); first assumption.
        change (∃ _)[_] with (∃ φ1'[$1 .: $0 ..][up (num x)..]).
        f_equal. rewrite subst_comp. eapply bounded_subst; first apply φ1'_bounded.
        intros [|[|n]] Hn; cbn. 2-3:solve_bounds.
        now rewrite num_subst.
      - intros x H%DR2.
        replace ((_)[_]) with (∃ φ1'[(num x)..]); first assumption.
        change (∃ _)[_] with (∃ φ1'[$1 .: $0 ..][up (num x)..]).
        f_equal. rewrite subst_comp. eapply bounded_subst; first apply φ1'_bounded.
        intros [|[|n]] Hn; cbn. 2-3:solve_bounds.
        now rewrite num_subst.
    Qed.
  End value_disjoint'.

  Section weak_strong.
    Existing Instance intu.

    Variable φ1 φ2 : form.
    Hypothesis (φ1_bounded : bounded 1 φ1) (φ2_bounded : bounded 1 φ2).
    Hypothesis (φ1_Σ : Σ1 φ1) (φ2_qdec : Σ1 φ2).
    Hypothesis (φ1_syn : forall x, P1 x <-> Qeq ⊢ φ1[(num x) ..])
               (φ2_syn : forall x, P2 x <-> Qeq ⊢ φ2[(num x) ..]).

    Lemma iff_iff φ ψ : (Qeq ⊢ φ <~> ψ) -> Qeq ⊢ φ <-> Qeq ⊢ ψ.
    Proof.
      intros H. split; intros H'; fapply H; exact H'.
    Qed.
    Lemma weak_strong : exists φ, Σ1 φ /\ bounded 1 φ /\
      (forall x, P1 x -> Qeq ⊢ φ[(num x)..]) /\
      (forall x, P2 x -> Qeq ⊢ ¬φ[(num x)..]).
    Proof.
      destruct (@Σ1_compression _ φ1 1) as (ψ1 & HQ1 & Hb1 & Hψ1), (@Σ1_compression _ φ2 1) as (ψ2 & HQ2 & Hb2 & Hψ2).
      all: try assumption.
      apply weak_strong' with (φ1 := ψ1[$1.:$0..]) (φ2 := ψ2[$1.:$0..]).
      { eapply subst_bound; last eassumption. intros [|[|n]]; solve_bounds. }
      { eapply subst_bound; last eassumption. intros [|[|n]]; solve_bounds. }
      { now apply Qdec_subst. }
      { now apply Qdec_subst. }
      - intros x. rewrite φ1_syn. 
        apply iff_iff.
        apply (subst_Weak ((num x)..)) in Hψ1.
        change (map _ _) with Qeq in Hψ1.
        cbn in Hψ1.
        assert (ψ1[$1 .: $0 ..][(num x) ..] = ψ1[up (num x)..]) as ->; last assumption.
        { rewrite subst_comp. eapply bounded_subst; first eassumption.
          intros [|[|n]] Hn; cbn.
          - reflexivity.
          - now rewrite num_subst.
          - lia. }
      - intros x. rewrite φ2_syn. 
        apply iff_iff.
        apply (subst_Weak ((num x)..)) in Hψ2.
        change (map _ _) with Qeq in Hψ2.
        cbn in Hψ2.
        assert (ψ2[$1 .: $0 ..][(num x) ..] = ψ2[up (num x)..]) as ->; last assumption.
        { rewrite subst_comp. eapply bounded_subst; first eassumption.
          intros [|[|n]] Hn; cbn.
          - reflexivity.
          - now rewrite num_subst.
          - lia. }
    Qed.

  End weak_strong.


End value_disjoint.

