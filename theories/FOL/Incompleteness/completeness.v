From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
From Undecidability.Shared Require Import Dec embed_nat.

From Undecidability.FOL.Util Require Import Syntax_facts FullDeduction FullDeduction_facts FullTarski FullTarski_facts Axiomatisations FA_facts Syntax.
From Undecidability.FOL Require Import PA.

From Undecidability.FOL.Incompleteness Require Import fol qdec.


From Equations Require Import Equations DepElim.


Notation "x 'i⧀=' y"  := (exists k, y = x i⊕ k) (at level 42) : PA_Notation.

Section Qmodel.
  Existing Instance PA_funcs_signature.
  Existing Instance PA_preds_signature.

  Existing Instance class.

  Context [M : Type] [I : interp M].
  Context [QM : I ⊨=L Qeq] [Mext : extensional I].

  Local Ltac search_list :=
   repeat ((left; reflexivity) + right) .
  Lemma add_zero m : iO i⊕ m = m.
  Proof.
    rewrite <-Mext. enough (I ⊨= ax_add_zero).
    { cbn in H. now apply H. }
    apply QM. search_list.
  Qed.
  Lemma add_rec m n : iσ m i⊕ n = iσ (m i⊕ n).
  Proof.
    rewrite <-Mext. enough (I ⊨= ax_add_rec).
    { cbn in H. now apply H. }
    apply QM. search_list.
  Qed.
  Lemma mult_zero m : iO i⊗ m = iO.
  Proof.
    rewrite <-Mext. enough (I ⊨= ax_mult_zero).
    { cbn in H. now apply H. }
    apply QM. search_list.
  Qed.
  Lemma mult_rec m n : iσ m i⊗ n = n i⊕ m i⊗ n.
  Proof.
    rewrite <-Mext. enough (I ⊨= ax_mult_rec).
    { cbn in H. now apply H. }
    apply QM. search_list.
  Qed.
  Lemma zero_succ m : ~iO = iσ m.
  Proof.
    rewrite <-Mext. enough (I ⊨= ax_zero_succ).
    { cbn in H. unfold "~". now apply H. }
    apply QM. search_list.
  Qed.
  Lemma succ_inj m n : iσ m = iσ n -> m = n.
  Proof.
    rewrite <-!Mext. enough (I ⊨= ax_succ_inj).
    { cbn in H. now apply H. }
    apply QM. search_list.
  Qed.
  Lemma cases m : m = iO \/ exists m', m = iσ m'.
  Proof.
    enough (m i= iO \/ exists m', m i= iσ m') as [H|(m' & Hm)].
    - rewrite <-Mext. now left.
    - right. exists m'. now rewrite <-Mext.
    - enough (I ⊨= ax_cases) as H.
      { cbn in H. apply H. easy. }
      apply QM. search_list.
  Qed.

  Lemma add_hom x y : iμ x i⊕ iμ y = iμ (x + y).
  Proof.
    induction x.
    - cbn. now rewrite add_zero.
    - cbn. rewrite add_rec. congruence.
  Qed.

  Lemma iμ_inj m n : iμ m = iμ n -> m = n.
  Proof.
    induction m in n |-*; destruct n.
    - easy.
    - intros []%zero_succ.
    - intros H. symmetry in H. destruct (zero_succ H).
    - cbn. intros H%succ_inj. f_equal. now apply IHm.
  Qed.


  Definition standard {M} {I : interp M} (m : M) := exists k, iμ k = m.
  Lemma num_standard (n : nat) : standard (iμ n).
  Proof.
    induction n; cbn.
    - now exists 0.
    - exists (S n). cbn. congruence.
  Qed.
  Lemma standard_succ (m : M) : standard m <-> standard (iσ m).
  Proof.
    split.
    - intros [k Hk]. exists (S k). cbn. congruence.
    - intros [k Hk]. exists (k-1).
      destruct k.
      { edestruct zero_succ. apply Hk. }
      cbn. apply succ_inj.
      replace (k-0) with k by lia. assumption.
  Qed.
  Lemma standard_add (m n : M) : standard (m i⊕ n) <-> standard m /\ standard n.
  Proof.
    split.
    - intros [k' Hk]. revert Hk. induction k' in m, n |-*; intros Hk; subst.
      + destruct (cases m) as [-> | (m' & ->)].
        2: { rewrite add_rec in Hk. edestruct zero_succ. apply Hk. }
        rewrite add_zero in Hk. subst.
        split; now exists 0.
      + destruct (cases m) as [-> | (m' & ->)], (cases n) as [-> | (n' & ->)].
        * split; now exists 0.
        * split; first now exists 0.
          rewrite <-add_zero, <-Hk.
          now exists (S k').
        * rewrite add_rec in Hk.
          enough (standard m' /\ standard iO).
          { pose proof (@standard_succ m'). tauto. }
          eapply IHk'. apply succ_inj, Hk.
        * rewrite add_rec in Hk.
          enough (standard m' /\ standard (iσ n')).
          { pose proof (@standard_succ m'). tauto. }
          eapply IHk'. apply succ_inj, Hk.
    - intros [[m' Hm] [n' Hn]]. exists (m' + n'). rewrite <-add_hom. congruence.
  Qed.

  Lemma standard_le (m : M) (k : nat) :
    m i⧀= iμ k -> standard m.
  Proof.
    intros [d Hd]. 
    destruct (cases m) as [Hm|[m' Hm]].
    { exists 0. easy. }
    subst.
    rewrite add_rec in Hd.
    destruct k.
    { edestruct zero_succ. apply Hd. }
    cbn in Hd. apply succ_inj in Hd.
    assert (standard (iμ k)) as H by now eexists. rewrite Hd in H.
    eapply standard_add in H. now rewrite <- standard_succ.
  Qed.

  Lemma standard_bound (m n : M) : standard n -> m i⧀= n -> standard m.
  Proof.
    intros [n' <-]. apply standard_le.
  Qed.
  Lemma nonstandard_large (n : nat) (m : M) : ~standard m -> iμ n i⧀= m.
  Proof.
    induction n in m |-*.
    - intros H. exists m. cbn. now rewrite add_zero.
    - intros H. destruct (cases m) as [-> | [m' ->]].
      + destruct H. now exists 0.
      + destruct (IHn m') as [d Hd].
        { contradict H. now rewrite <-standard_succ. }
        exists d. cbn. rewrite add_rec. congruence.
  Qed.
End Qmodel.

Module completeness. Section completeness.
  Existing Instance PA_funcs_signature.
  Existing Instance PA_preds_signature.


  Existing Instance class.
  Existing Instance interp_nat.

  Hypothesis completeness : forall φ,
      Qeq ⊢C φ <-> forall (M : Type) (I : interp M) ρ, extensional I -> I ⊨=L Qeq -> ρ ⊨ φ.

  Lemma Qdec_absoluteness M1 M2 (I1 : interp M1) (I2 : interp M2) (QM1 : I1 ⊨=L Qeq) (Mext1 : extensional I1) (QM2 : I2 ⊨=L Qeq) (Mext2 : extensional I2) ρ1 ρ2 φ :
    bounded 0 φ -> Qdec φ -> I1; ρ1 ⊨ φ -> I2; ρ2 ⊨ φ.
  Proof.
    intros Hb HQ H1. destruct (HQ var) as [H|H].
    { eapply subst_bound; last eassumption. lia. }
    all: rewrite completeness in H.
    - rewrite <-subst_var. now apply H.
    - contradict H1. pattern φ. rewrite <-subst_var. now apply H.
  Qed.
  Lemma Qdec_absoluteness_nat M (I : interp M) (QM : I ⊨=L Qeq) (Mext : extensional I) ρN ρM φ :
    bounded 0 φ -> Qdec φ -> interp_nat; ρN ⊨ φ <-> I; ρM ⊨ φ.
  Proof.
    intros Hb Qdec. split; intros H.
    - eapply (@Qdec_absoluteness nat M); now eauto using nat_is_Q_model.
    - eapply (@Qdec_absoluteness M nat); now eauto using nat_is_Q_model.
  Qed.

  Section value_disj.
    Variable P1 P2 : nat -> Prop.
    Hypothesis P_disjoint : forall x, P1 x -> P2 x -> False.

    Variable φ1 φ2 : form.
    Hypothesis (φ1_bounded : bounded 2 φ1) (φ2_bounded : bounded 2 φ2).
    Hypothesis (φ1_dec : forall x k, Qdec (φ1[num x .: (num k) ..]))
               (φ2_dec : forall x k, Qdec (φ2[num x .: (num k) ..])).
    Hypothesis (φ1_sem : forall x ρ, P1 x <-> interp_nat; ρ ⊨ ∃ φ1[(num x) ..])
               (φ2_sem : forall x ρ, P2 x <-> interp_nat; ρ ⊨ ∃ φ2[(num x) ..]).


    Definition φ1' := φ1 ∧ ∀ $0 ⧀= $2 ~> φ2[$1 .: $0 ..] ~> ⊥.
    Definition φ2' := φ2 ∧ ∀ $0 ⧀= $2 ~> φ1[$1 .: $0 ..] ~> ⊥.

    Lemma bounded_subst_2 φ ρ : bounded 2 φ -> φ[ρ] = φ[ρ 0 .: (ρ 1) ..].
    Proof.
      intros H. eapply bounded_subst; first eassumption.
      intros [|[|k]]; easy + lia.
    Qed.
    Lemma φ1_sem' x ρ : P1 x <-> exists k, interp_nat; ρ ⊨ φ1[num x .: (num k) ..].
    Proof.
      rewrite φ1_sem. cbn.
      setoid_rewrite sat_single_nat. setoid_rewrite subst_comp.
      setoid_rewrite (bounded_subst_2 _ φ1_bounded).
      setoid_rewrite num_subst. reflexivity.
    Qed.
    Lemma φ2_sem' x ρ : P2 x <-> exists k, interp_nat; ρ ⊨ φ2[num x .: (num k) ..].
    Proof.
      rewrite φ2_sem. cbn.
      setoid_rewrite sat_single_nat. setoid_rewrite subst_comp.
      setoid_rewrite (bounded_subst_2 _ φ2_bounded).
      setoid_rewrite num_subst. reflexivity.
    Qed.

    Lemma DR1 x : P1 x -> Qeq ⊢C ∃ φ1'[(num x)..].
    Proof.
      intros H. apply completeness. intros M I ρ Mext QM.
      assert (exists k, (fun _ => 0) ⊨ φ1[num x .: (num k) ..]) as [k Hk] by now apply φ1_sem'.
      exists (iμ k). split.
      - rewrite sat_single_PA, subst_comp, bounded_subst_2; last assumption. cbn.
        rewrite num_subst. eapply Qdec_absoluteness_nat; eauto.
        eapply subst_bound; last eassumption.
        intros [|[|n]] Hn; (apply num_bound + lia).
      - cbn. intros k' [d Hd] H2.

        assert (standard k') as [k'' <-].
        { unshelve eapply standard_le; try auto. exists d. now apply Mext. }

        rewrite !sat_single_PA, !subst_comp, bounded_subst_2 in H2; last assumption. cbn in H2.
        rewrite !num_subst in H2.

        enough (P2 x) by (eapply P_disjoint; eassumption).
        eapply φ2_sem' with (ρ := fun _ => 0). exists k''. eapply Qdec_absoluteness_nat; eauto.
        eapply subst_bound; last eassumption.
        intros [|[|n]] Hn; (apply num_bound + lia).
    Qed.
    Lemma DR2 x : P2 x -> Qeq ⊢C ¬∃ φ1'[(num x)..].
    Proof.
      intros H. apply completeness. intros M I ρ Mext QM [k [Hk1 Hk2]].
      cbn in Hk1, Hk2. cbn.
      assert (exists k, (fun _ => 0) ⊨ φ2[num x .: (num k) ..]) as [kk Hkk] by now apply φ2_sem'.
      apply (Hk2 (iμ kk)).
      - enough (~standard k).
        { rewrite pless_eq. cbn. setoid_rewrite Mext. apply nonstandard_large; assumption. }
        intros [k' <-].

        rewrite sat_single_PA in Hk1. rewrite !subst_comp, bounded_subst_2 in Hk1; last assumption. cbn in Hk1.
        rewrite num_subst in Hk1.

        enough (P1 x) by (eapply P_disjoint; eassumption).
        eapply φ1_sem' with (ρ := (fun _ => 0)). exists k'. eapply Qdec_absoluteness_nat; eauto.
        eapply subst_bound; last eassumption.
        intros [|[|n]] Hn; (apply num_bound + lia).
      - rewrite sat_single_PA, !subst_comp, bounded_subst_2; last assumption. cbn.
        rewrite !num_subst. eapply Qdec_absoluteness_nat; eauto.
        eapply subst_bound; last eassumption.
        intros [|[|n]] Hn; (apply num_bound + lia).
    Qed.
  End value_disj.
  

End completeness. End completeness.
