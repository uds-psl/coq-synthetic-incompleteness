From Undecidability.FOL.Incompleteness Require Import FS CT.
From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
From Undecidability.Shared Require Import Dec embed_nat.

From Undecidability.FOL.Util Require Import Syntax_facts FullDeduction FullDeduction_facts FullTarski FullTarski_facts Axiomatisations FA_facts Syntax.
From Undecidability.FOL Require Import PA.

Print prv.



(* Notation for satisfying list theories *)
Notation "I ⊨=L T" := (forall psi, List.In psi T -> I ⊨= psi) (at level 20).
(* Notation for explicitely giving model *)
Notation "I ; rho '⊨' phi" := (@sat _ _ _ I _ rho phi) (at level 20, rho at next level).

(* increasing x instead of k to be able to use recursive formulae *)
(* NOTE this definition requires extensionality of the model *)
Notation "x 'i⧀' y"  := (exists k, y = (iσ x) i⊕ k) (at level 42) : PA_Notation.
(* Overwriting notation from PA.v to be useful in any way *)
Notation "x '⧀' y"  := (∃ y`[↑] == ((σ x`[↑]) ⊕ $0)) (at level 42) : PA_Notation.
(* I need another oless *)
Notation "x '⧀comm' y"  := (∃ y`[↑] == (σ $0 ⊕ x`[↑])) (at level 42) : PA_Notation.



Section sigma.
  Existing Instance PA_funcs_signature.
  Existing Instance PA_preds_signature.

  Existing Instance falsity_on.

  (* TODO need to remove ff flags from these structures to ease inductions *)

  Hypothesis LEM : forall P, P \/ ~P.

  (* Definitions stolen from Marc *)
  Inductive Δ0 : form -> Prop :=
  | Delta_fal : Δ0 ⊥
  | Delta_eq : forall t s, Δ0 (t == s)
  | Delta_lt : forall t s, Δ0 (t ⧀ s)
  | Delta_Conj : forall α β, Δ0 α -> Δ0 β -> Δ0 (α ∧ β)
  | Delta_Disj : forall α β, Δ0 α -> Δ0 β -> Δ0 (α ∨ β)
  | Delta_Impl : forall α β, Δ0 α -> Δ0 β -> Δ0 (α ~> β).

  Check exist_times.
  Fixpoint oplus_times n : term :=
    match n with
    | 0 => zero
    | 1 => $0
    | S n => oplus_times n ⊕ $n
    end.

  Inductive Δ0' : form -> Prop :=
  | Delta_id : forall α, Δ0 α -> Δ0' α
  | Delta_bounded_exist : forall α t, Δ0' α -> Δ0' (∃ ($0 ⧀ t`[↑]) ∧ α)
  | Delta_bounded_exist_comm : forall α t, Δ0' α -> Δ0' (∃ ($0 ⧀comm t`[↑]) ∧ α)
  | Delta_bounded_forall : forall α t, Δ0' α -> Δ0' (∀ $0 ⧀ t`[↑] ~> α)
  (*| Delta_bounded_exist_times : forall α n t, Δ0' α -> Δ0' (exist_times n (oplus_times n ⧀ t`[↑]) ∧ α)*).

  Inductive Σ1 : form -> Prop :=
  | Sigma_Delta : forall α, Δ0' α -> Σ1 α
  | Sigma_exists : forall α, Σ1 α -> Σ1 (∃ α).
  Inductive Π1 : form -> Prop :=
  | Pi_Delta : forall α, Δ0' α -> Π1 α
  | Pi_forall : forall α, Π1 α -> Π1 (∀ α).



  Lemma PNF_conj φ1 φ2 : Π1 φ1 -> Π1 φ2 -> exists ψ, Π1 ψ /\ Qeq ⊢C φ1 ∧ φ2 <~> ψ.
  Proof.
  Admitted.
  Lemma PNF_impl φ1 φ2 : Π1 φ1 -> Σ1 φ2 -> exists ψ, Σ1 ψ /\ Qeq ⊢C (φ1 ~> φ2) <~> ψ.
  Proof. Admitted.

  Lemma exists_compression' φ : bounded 2 φ -> Δ0' φ -> exists ψ, Δ0' ψ /\ Qeq ⊢C (∃ ψ) <~> ∃∃φ.
  Proof.
    intros Hb Hd.
    exists (∃ ($0 ⧀ $1) ∧ ∃ ($0 ⧀comm $2) ∧ φ).
    split.
    { apply (Delta_bounded_exist $0), (Delta_bounded_exist_comm $1), Hd. }
    apply CI.
    - apply II.
      eapply ExE.
      { apply Ctx; now left. }
      cbn. unfold "↑". fold ↑.
      change (List.map (subst_form ↑) Qeq) with Qeq.
      eapply ExE.
      { apply Ctx; now left. }
      cbn -[Qeq]. unfold "↑". fold ↑.
      change (List.map (subst_form ↑) Qeq) with Qeq.
      eapply ExE.
      { eapply CE2, Ctx. now left. }
      cbn -[Qeq]. unfold "↑". fold ↑.
      change (List.map (subst_form ↑) Qeq) with Qeq.
      eapply ExI with (t := $1). cbn -[Qeq].
      eapply ExI with (t := $0). cbn -[Qeq].
      eapply IE.
      2: { eapply CE2, Ctx. now left. }
      eapply Weak with (A := Qeq).
      2: { intros f H. now do 4 right. }
      apply II. rewrite !subst_comp.
      apply Ctx. left.
      rewrite <-subst_var at 1.
      eapply bounded_subst.
      + apply Hb.
      + intros [|[|k]] H; cbn; reflexivity + lia.
    - apply II.
      eapply ExE.
      { apply Ctx; now left. }
      cbn -[Qeq]. unfold "↑". fold ↑.
      change (List.map (subst_form ↑) Qeq) with Qeq.
      eapply ExE.
      { apply Ctx; now left. }
      cbn -[Qeq]. unfold "↑". fold ↑.
      change (List.map (subst_form ↑) Qeq) with Qeq.
      apply Weak with (A := (φ :: Qeq)%list).
      2: { intros ϕ [<-|H].
           - now left.
           - now do 3 right. }
      apply ExI with (t := σ $1 ⊕ $0).
      cbn -[Qeq]. unfold "↑". fold ↑.
      apply ExI with (t := $1).
      cbn -[Qeq]. unfold "↑". fold ↑.
      apply CI.
      { apply ExI with (t := $0). cbn -[Qeq].
        eapply AllE with (t := σ $1 ⊕ $0) (phi := $0 == $0).
        apply Ctx. right. now left. }

      apply ExI with (t := $0).
      cbn -[Qeq]. unfold "↑". fold ↑.
      apply CI.
      { apply ExI with (t := $1). cbn -[Qeq].
        eapply AllE with (t := σ $1 ⊕ $0) (phi := $0 == $0).
        apply Ctx. right. now left. }
      rewrite !subst_comp. erewrite bounded_subst; first instantiate (1 := var).
      + rewrite subst_var. now apply Ctx.
      + exact Hb.
      + intros [|[|k]] Hk; cbn; reflexivity + lia.
  Qed.
  Lemma exists_compression φ n : bounded n φ -> Δ0' φ ->
                                 exists ψ, Δ0' ψ /\ Qeq ⊢C (∃ ψ) <~> exist_times n φ.
  Proof.
    induction n as [|n IH] in φ |-*; intros Hb Hd.
    all: cbn [exist_times iter].
    - exists φ[↑]. cbn [exist_times iter]. admit.
  Admitted.


  Lemma Σcompleteness : forall φ, Σ1 φ -> interp_nat ⊨= φ -> Qeq ⊢C φ.
  Proof. Admitted. (* WIP by Marc *)
  Lemma Q_sound φ : Qeq ⊢C φ -> interp_nat ⊨= φ.
  Proof.
    intros H ρ. eapply soundness_class.
    - assumption.
    - eassumption.
    - intros psi HQ.
      cbn in HQ. repeat destruct HQ as [? | HQ]; subst; cbn; try congruence.
      + intros []; eauto.
      + easy.
  Qed.
End sigma.

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
    m i⧀ iμ k -> standard m.
  Proof.
    intros [d Hd]. rewrite add_rec in Hd. destruct k.
    { edestruct zero_succ. apply Hd. }
    cbn in Hd. apply succ_inj in Hd.
    assert (standard (iμ k)) as H by now eexists. rewrite Hd in H.
    now eapply standard_add in H.
  Qed.

  Lemma standard_bound (m n : M) : standard n -> m i⧀ n -> standard m.
  Proof.
    intros [n' <-]. apply standard_le.
  Qed.
  Lemma nonstandard_large (n : nat) (m : M) : ~standard m -> iμ n i⧀ m.
  Proof.
    induction n in m |-*.
    - intros H. destruct (cases m) as [-> | [m' ->]].
      + exfalso. apply H. now exists 0.
      + exists m'. now rewrite add_rec, add_zero.
    - intros H. destruct (cases m) as [-> | [m' ->]].
      + exfalso. apply H. now exists 0.
      + destruct (IHn m') as [d Hd].
        { contradict H. now rewrite <-standard_succ. }
        exists d. cbn. rewrite add_rec. congruence.
  Qed.
End Qmodel.


Section completeness.
  Existing Instance PA_funcs_signature.
  Existing Instance PA_preds_signature.

  Definition Qdec φ := Qeq ⊢C φ \/ Qeq ⊢C ¬φ.

  Existing Instance class.
  Existing Instance interp_nat.

  Hypothesis completeness : forall φ,
      Qeq ⊢C φ <-> forall (M : Type) (I : interp M) ρ, extensional I -> I ⊨=L Qeq -> ρ ⊨ φ.


  Lemma dec_completeness M (I : interp M) (QM : I ⊨=L Qeq) (Mext : extensional I) ρN ρM φ :
    Qdec φ -> interp_nat; ρN ⊨ φ <-> I; ρM ⊨ φ.
  Proof.
    intros [Hφ|Hφ]; rewrite completeness in Hφ; try assumption; split.
    - intros _. now apply Hφ.
    - intros _. apply Hφ.
      + easy.
      + auto using nat_is_Q_model.
    - intros []%Hφ.
      + easy.
      + auto using nat_is_Q_model.
    - now intros []%Hφ.
  Qed.
  Lemma sat_single_PA M (I : interp M) φ ρ k : (iμ k .: ρ) ⊨ φ <-> ρ ⊨ φ[(num k)..].
  Proof.
    replace (iμ k) with (eval ρ (num k)).
    - apply sat_single.
    - induction k; cbn; congruence.
  Qed.
  Lemma sat_single_nat φ ρ k : (k .: ρ) ⊨ φ <-> ρ ⊨ φ[(num k)..].
  Proof.
    replace k with (iμ k) at 1.
    - now rewrite sat_single_PA.
    - induction k; cbn; congruence.
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


    Definition φ1' := φ1 ∧ ∀ $0 ⧀ $2 ~> φ2[$1 .: $0 ..] ~> ⊥.
    Definition φ2' := φ2 ∧ ∀ $0 ⧀ $2 ~> φ1[$1 .: $0 ..] ~> ⊥.

    Lemma φ1_bounded_subst ρ : φ1[ρ] = φ1[ρ 0 .: (ρ 1) ..].
    Proof.
      eapply bounded_subst; first apply φ1_bounded. intros [|[|k]]; easy + lia.
    Qed.
    Lemma φ2_bounded_subst ρ : φ2[ρ] = φ2[ρ 0 .: (ρ 1) ..].
    Proof.
      eapply bounded_subst; first apply φ2_bounded. intros [|[|k]]; easy + lia.
    Qed.

    Lemma φ1'_bounded : bounded 2 φ1'.
    Proof using φ1_bounded.
      solve_bounds.
      - assumption.
      - cbn. unfold "↑". constructor. lia.
      - cbn. unfold "↑". constructor.
        admit.
      - eapply subst_bound; first eassumption.
        intros [|[|n]] H.
        + constructor. lia.
        + constructor. lia.
        + lia.
    Admitted.

    Lemma φ1_sem' x ρ : P1 x <-> exists k, interp_nat; ρ ⊨ φ1[num x .: (num k) ..].
    Proof.
      rewrite φ1_sem. cbn.
      setoid_rewrite sat_single_nat. setoid_rewrite subst_comp.
      setoid_rewrite φ1_bounded_subst. cbn.
      setoid_rewrite num_subst. reflexivity.
    Qed.
    Lemma φ2_sem' x ρ : P2 x <-> exists k, interp_nat; ρ ⊨ φ2[num x .: (num k) ..].
    Proof.
      rewrite φ2_sem. cbn.
      setoid_rewrite sat_single_nat. setoid_rewrite subst_comp.
      setoid_rewrite φ2_bounded_subst. cbn.
      setoid_rewrite num_subst. reflexivity.
    Qed.

    Lemma DR1 x : P1 x -> Qeq ⊢C ∃ φ1'[(num x)..].
    Proof.
      intros H. apply completeness. intros M I ρ Mext QM.
      assert (exists k, (fun _ => 0) ⊨ φ1[num x .: (num k) ..]) as [k Hk] by now apply φ1_sem'.
      exists (iμ k). split.
      - rewrite sat_single_PA, subst_comp, φ1_bounded_subst. cbn.
        rewrite num_subst. eapply dec_completeness; eauto.
      - cbn. intros k' [d Hd] H2.

        assert (standard k') as [k'' <-].
        { unshelve eapply standard_le; try auto. exists d. now apply Mext. }

        rewrite !sat_single_PA, !subst_comp, φ2_bounded_subst in H2. cbn in H2.
        rewrite !num_subst in H2.

        enough (P2 x) by (eapply P_disjoint; eassumption).
        eapply φ2_sem' with (ρ := fun _ => 0). exists k''. eapply dec_completeness; eauto.
    Qed.
    Lemma DR2 x : P2 x -> Qeq ⊢C ¬∃ φ1'[(num x)..].
    Proof.
      intros H. apply completeness. intros M I ρ Mext QM [k [Hk1 Hk2]].
      cbn in Hk1, Hk2. cbn.
      assert (exists k, (fun _ => 0) ⊨ φ2[num x .: (num k) ..]) as [kk Hkk] by now apply φ2_sem'.
      apply (Hk2 (iμ kk)).
      - enough (~standard k).
        { setoid_rewrite Mext. apply nonstandard_large; assumption. }
        intros [k' <-].

        rewrite sat_single_PA in Hk1. rewrite !subst_comp, φ1_bounded_subst in Hk1. cbn in Hk1.
        rewrite num_subst in Hk1.

        enough (P1 x) by (eapply P_disjoint; eassumption).
        eapply φ1_sem' with (ρ := (fun _ => 0)). exists k'. eapply dec_completeness; eauto.
      - rewrite sat_single_PA, !subst_comp, φ2_bounded_subst. cbn.
        rewrite !num_subst. eapply dec_completeness; eauto.
    Qed.
  End value_disj.

  Section value.

    Variable f : nat -> nat -> Prop.
    Hypothesis f_func : forall x y1 y2, f x y1 -> f x y2 -> y1 = y2.

    Variable T : form.
    Hypothesis T_bounded : bounded 3 T.
    Hypothesis T_decidable : forall x y k,
        Qdec (T[num x .: num y .: (num k) ..]).
    Hypothesis T_sem : forall ρ x y,
        f x y <-> interp_nat; ρ ⊨ ∃ T[num x .: (num y) ..].

    Definition T' := T ∧ ∀∀ ($1⊕$0 ⧀ $3⊕$4) ~> (¬ $1 == $3) ~> T[$2.:$1.:$0..] ~> ⊥.


    Lemma subst_T_bound (ρ : env term) :
      T[ρ] = T[ρ 0 .: ρ 1 .: (ρ 2) ..].
    Proof.
      eapply bounded_subst; first apply T_bounded.
      intros [|[|[|n]]] H; cbn; lia + easy.
    Qed.
    Lemma T_single_rho_model M (I : interp M) ρ x y k :
      ((iμ k) .: ρ) ⊨ T[num x .: (num y) ..] <-> ρ ⊨ T[num x .: num y .: (num k) ..].
    Proof.
      assert (iμ k = eval ρ (num k)) as Hk by (induction k; cbn; congruence).
      rewrite Hk at 1. rewrite sat_single, subst_comp, subst_T_bound.
      cbn. rewrite !num_subst. reflexivity.
    Qed.
    Lemma T_single_rho_nat ρ x y k :
      (k .: ρ) ⊨ T[num x .: (num y) ..] <-> ρ ⊨ T[num x .: num y .: (num k) ..].
    Proof.
      replace k with (iμ k) at 1; first apply T_single_rho_model.
      induction k; cbn; congruence.
    Qed.

    Lemma T_sem' x y ρ :
      f x y <-> exists k, interp_nat; ρ ⊨ T[num x .: num y .: (num k) ..].
    Proof.
      split.
      - intros H. apply T_sem with (ρ := ρ) in H as [k Hk].
        exists k. now apply T_single_rho_nat.
      - intros [k Hk]. eapply T_sem. exists k. apply T_single_rho_nat, Hk.
    Qed.


    Lemma VR1 x y : f x y -> Qeq ⊢C ∃T'[num x .: (num y) ..].
    Proof.
      intros Hf. apply completeness.
      intros M I ρ Mext HI.
      assert (exists k, (fun _ => 0) ⊨ T[num x .: num y .: (num k) ..]) as [k Hk] by now apply T_sem'.
      exists (iμ k). split.
      - apply T_single_rho_model. now eapply dec_completeness; eauto.
      - intros y' k' [d Hle] Hneq HT. cbn.

        cbn in Hle. rewrite !num_subst, !eval_num, Mext in Hle.

        assert (standard (iμ y i⊕ iμ k)) as Hyk.
        { rewrite add_hom; try assumption. apply num_standard. }
        rewrite Hle, !add_rec, <-standard_succ in Hyk; try assumption.
        apply standard_add in Hyk as [[[y'' <-] [k'' <-]]%standard_add [d' <-]]; try assumption.

        cbn in Hneq. rewrite Mext,!num_subst,eval_num in Hneq.
        assert (y'' <> y) as Hy''k by congruence.

        rewrite !sat_single_PA, !subst_comp, subst_T_bound in HT. cbn in HT.
        rewrite !num_subst in HT.
        eapply dec_completeness with (ρN := fun _ => 0) in HT; try eauto.

        eapply Hy''k, f_func; eapply T_sem'; eauto.
    Qed.
    Lemma VR2 x y' y : f x y -> y <> y' -> Qeq ⊢C ¬∃T'[num x .: (num y') ..].
    Proof.
      intros Hf Hy. apply completeness.
      intros M I ρ Mext HI [k [Hk1 Hk2]]. cbn.
      assert (exists k, (fun _ => 0) ⊨ T[num x .: num y .: (num k) ..]) as [kk Hkk] by now apply T_sem'.

      cbn in Hk2. apply (Hk2 (iμ y) (iμ kk)).
      - enough (iμ y i⊕ iμ kk i⧀ iμ y' i⊕ k) as [d Hd].
        { exists d. now rewrite !num_subst, eval_num, Mext.  }
        rewrite add_hom; try assumption.
        eapply nonstandard_large; try assumption.
        enough (~standard k) as Hk.
        { rewrite standard_add; try assumption. tauto. }
        intros [ks <-]. apply Hy.

        eapply f_func.
        + exact Hf.
        + eapply T_sem' with (ρ := fun _ => 0). exists ks.
          eapply dec_completeness; eauto. rewrite <-T_single_rho_model.
          apply Hk1.
      - rewrite !num_subst, eval_num, Mext. contradict Hy. now eapply iμ_inj.
      - rewrite !sat_single_PA, !subst_comp, subst_T_bound. cbn. rewrite !num_subst.
        eapply dec_completeness; eauto.
    Qed.
  End value.
End completeness.


Section Qtrichotomy.
  Existing Instance PA_funcs_signature.
  Existing Instance PA_preds_signature.

  Lemma Qdec_le x : Qeq ⊢C (num x ⧀ σ $0) ∨ ($0 ⧀ σ (num x)).
  Proof.
    apply Σcompleteness.
    - admit. (* Shold not appear here *)
    - repeat constructor.
    - cbn. intros ρ. admit.
    (* By Σcompleteness *)
  Admitted.
End Qtrichotomy.

Module value_disjoint. Section value_disjoint.
  Existing Instance PA_funcs_signature.
  Existing Instance PA_preds_signature.

  Existing Instance class.

  Variable P1 P2 : nat -> Prop.
  Hypothesis P_disjoint : forall x, P1 x -> P2 x -> False.

  Variable φ1 φ2 : form.
  Hypothesis (φ1_bounded : bounded 2 φ1) (φ2_bounded : bounded 2 φ2).
  Hypothesis (φ1_dec : forall x k, Qdec (φ1[num x .: (num k) ..]))
              (φ2_dec : forall x k, Qdec (φ2[num x .: (num k) ..])).
  Hypothesis (φ1_sem : forall x, P1 x <-> Qeq ⊢C ∃ φ1[(num x) ..])
              (φ2_sem : forall x, P2 x <-> Qeq ⊢C ∃ φ2[(num x) ..]).

  Definition φ1' := φ1 ∧ ∀ $0 ⧀ σ $2 ~> φ2[$1 .: $0 ..] ~> ⊥.
  Definition φ2' := φ2 ∧ ∀ $0 ⧀ σ $2 ~> φ1[$1 .: $0 ..] ~> ⊥.
  Lemma DR1 x : P1 x -> Qeq ⊢C ∃ φ1'[(num x)..].
  Proof.
    admit. (* by Σcompleteness *)
  Admitted.
  Lemma DR1' x : P2 x -> Qeq ⊢C ∃ φ2'[(num x)..].
  Proof.
    admit. (* by Σcompleteness *)
  Admitted.
  Lemma DR2 x : P2 x -> Qeq ⊢C ¬∃ φ1'[(num x)..].
  Proof.
    intros Hx%DR1'.
    cbn -[Qeq]. unfold "↑".
    apply II. eapply ExE.
    { eapply Ctx. eauto. }
    cbn -[Qeq].
    replace (List.map (subst_form ↑) Qeq) with Qeq by reflexivity.
    rewrite subst_comp. rewrite (φ2_bounded_subst φ2_bounded). cbn -[Qeq]. rewrite num_subst.
    eapply Weak.
    2: { instantiate (1 :=((φ1[(num x)..] ∧ (∀ (∃ σ $2 == σ $1 ⊕ $0) ~> ¬ φ2[num x .: $0..]) :: Qeq))%list).
         intros ϕ [H|H]; subst.
         - now left.
         - now do 2 right. }
    (* By Sigma1 *)
    assert (exists k, Qeq ⊢C φ2'[num x .: (num k) ..]) as [k Hk] by admit.
    cbn -[Qeq] in Hk. rewrite !num_subst in Hk. unfold "↑" in Hk.
    assert (Qeq ⊢C (num k ⧀ σ $0) ∨ ($0 ⧀ σ (num k))) by admit.
    eapply DE. { eapply Weak; first apply H. intros ϕ HQ. now right. }
    - eapply IE.
      2: { eapply (AllE (num k)). eapply CE2. apply Ctx. right. left. reflexivity. }
      cbn -[Qeq]. unfold "↑". rewrite num_subst.
      apply II.
      eapply IE; first eapply IE.
      { apply Ctx. left. reflexivity. }
      + apply Ctx. right. left. reflexivity.
      + rewrite subst_comp, (φ2_bounded_subst φ2_bounded).  cbn -[Qeq]. rewrite num_subst.
        eapply Weak. { eapply CE1, Hk. }
        now do 3 right.
    - eapply IE.
      2: { eapply (AllE $0). eapply CE2. eapply Weak; first apply Hk. intros HQ. now do 2 right. }
      cbn -[Qeq]. unfold "↑". rewrite !num_subst.
      apply II.
      eapply IE; first eapply IE.
      { apply Ctx. left. reflexivity. }
      + apply Ctx. right. left. reflexivity.
      + eapply CE1. apply Ctx. do 2 right. left.
        f_equal. rewrite !subst_comp. eapply bounded_subst.
        * apply φ1_bounded.
        * intros [|[|n]] Hn; cbn; rewrite ?num_subst; reflexivity + lia.
  Admitted.
End value_disjoint. End value_disjoint.


Section Qinsep.
  Existing Instance PA_funcs_signature.
  Existing Instance PA_preds_signature.

  Existing Instance class.

  Hypothesis LEM : forall P, P \/ ~P.

  Hypothesis completeness : forall φ,
      Qeq ⊢C φ <-> forall (M : Type) (I : interp M) ρ, extensional I -> I ⊨=L Qeq -> ρ ⊨ φ.

  Variable theta : nat -> nat -> nat -> option bool.
  Hypothesis theta_stationary : forall c, fstationary (theta c).
  Hypothesis theta_univ : forall (f : nat -> nat -> option bool), fstationary f ->
            exists c, forall x y, freturns f x y <-> freturns (theta c) x y.
  Arguments theta_univ : clear implicits.

  Hypothesis Qrepr : forall P, enumerable P -> exists φ,
        bounded 2 φ /\ (forall x k, Qdec φ[num x .: (num k) ..]) /\
          forall x ρ, P x <-> interp_nat; ρ ⊨ ∃φ[(num x)..].

  Local Definition P b := fun t => let '(c, x) := unembed t in freturns (theta c) x b.
  Local Lemma P_enumerable b :
    enumerable (P b).
  Proof.
    apply semi_decidable_enumerable.
    { exists Some. eauto. }
    unfold semi_decidable.
    exists (fun t k => let '(c, x) := unembed t in match theta c x k with
                                          | Some true =>
                                              if b then true else false
                                          | Some false =>
                                              if b then false else true
                                          | _ => false
                                          end).
    intros t. unfold P. destruct (unembed t) as [x y]; split; intros [k Hk].
    - exists k. destruct b; now rewrite Hk.
    - exists k. now destruct b, (theta x y k) as [[]|].
  Qed.
  Local Lemma P_disjoint t : P true t -> P false t -> False.
  Proof.
    unfold P. destruct (unembed t) as [x y].
    intros [k1 Hk1] [k2 Hk2].
    assert (k1 >= k2 \/ k2 >= k1) as [H|H] by lia.
    - specialize (theta_stationary Hk2 H). congruence.
    - specialize (theta_stationary Hk1 H). congruence.
  Qed.

  Lemma Qincomplete : exists φ, ~Qeq ⊢C φ /\ ~Qeq ⊢C ¬φ.
  Proof.
    unshelve edestruct guess_insep_expl_incompleteness as (s & Hs1 & Hs2).
    - exact theta.
    - apply Qfs_class, LEM.
    - apply theta_univ.
    - destruct (Qrepr (P_enumerable true)) as (φ1 & Hb1 & Hd1 & Hr1),
               (Qrepr (P_enumerable false)) as (φ0 & Hb0 & Hd0 & Hr0).

      unshelve eexists.
      { intros c x. exists (∃ (φ1' φ1 φ0)[(num (embed (c, x)))..]). apply bounded_closed.
        constructor. eapply subst_bound; first eapply φ1'_bounded; first assumption.
        intros [|[|n]] H; cbn.
        + eapply bounded_up_t; first apply num_bound. lia.
        + constructor. lia.
        + lia. }

      split.
      + intros c x Hx. cbn -[φ1' φ2']. unfold form_provable, CT.Q. cbn [proj1_sig form_neg].
        exists Qeq. split; first easy.
        eapply DR1. 2: exact P_disjoint. all: try assumption.
        unfold P. now rewrite embedP.
      + intros c x Hx. cbn -[φ1' φ2']. unfold form_provable, CT.Q. cbn [proj1_sig form_neg].
        exists Qeq. split; first easy.
        eapply DR2. 2: exact P_disjoint. all: try assumption.
        unfold P. now rewrite embedP.
    - destruct s as [φ Hc]. exists φ.
      split.
      + contradict Hs1. now exists Qeq.
      + contradict Hs2. now exists Qeq.
  Qed.
End Qinsep.
Check Qincomplete.


Section value.
  Existing Instance PA_funcs_signature.
  Existing Instance PA_preds_signature.

  Existing Instance interp_nat.

  Hypothesis LEM : forall P, P \/ ~P.


  Lemma completeness_equiv φ1 φ2 : Σ1 φ2 -> Qeq ⊢C φ1 <~> φ2 -> interp_nat ⊨= φ1 -> Qeq ⊢C φ1.
  Proof.
    intros Hs Hequiv Hnat.
    enough (Qeq ⊢C φ2) as H.
    { eapply IE; last exact H.
      eapply CE2. apply Hequiv. }
    apply Σcompleteness; try assumption.
    intros rho.
    eapply Q_sound in Hequiv; last assumption.
    cbn in Hequiv.
    apply Hequiv, Hnat.
  Qed.


  Variable (f : nat -> nat).
  Definition R x y := f x = y.

  Variable ϕΠ : form.
  Definition ϕΠ' x y := ϕΠ[num x .: (num y) ..].
  Hypothesis (ϕΠ_bounded : bounded 2 ϕΠ) (ϕΠ_Π : forall x y, Π1 (ϕΠ' x y)).


  Hypothesis ϕΠ_R : forall x y,
      (R x y -> Qeq ⊢C ϕΠ' x y) /\
      (interp_nat ⊨= ϕΠ' x y -> R x y).

  Lemma ϕΠ_R_completeness ρ x y :
    ρ ⊨ ϕΠ' x y -> R x y.
  Proof.
    intros Hρ. apply ϕΠ_R.
    intros sigma. eapply sat_closed.
    - eapply subst_bound; first exact ϕΠ_bounded.
      intros [|[|n]] H; last lia; apply num_bound.
    - apply Hρ.
  Qed.


  Lemma eval_num ρ n : eval ρ (num n) = n.
  Proof.
    induction n; cbn; congruence.
  Qed.


  Lemma CT_functional x y y' : Qeq ⊢C ϕΠ' x y ∧ ϕΠ' x y' ~> num y == num y'.
  Proof.
    apply II.
    destruct (@PNF_conj LEM (ϕΠ' x y) (ϕΠ' x y')) as (ψ1 & Hb1 & Hc1); try apply ϕΠ_Π.
    apply IE with (phi := ψ1); first last.
    { eapply IE.
      - eapply CE1. apply Weak with (A := Qeq); last auto. eapply Hc1.
      - now apply Ctx.
    }
    apply Weak with (A := Qeq); last auto.

    destruct (@PNF_impl LEM ψ1 (num y == num y')) as (ψ2 & Hs2 & Hc2).
    { assumption. }
    { repeat constructor. }

    eapply completeness_equiv; try eassumption.
    intros rho Hψ1.

    eapply Q_sound with (rho := rho) in Hc1 as [Hc1 Hc1']; last assumption.
    cbn in Hc1'. destruct (Hc1' Hψ1) as [H1 H2].
    eapply ϕΠ_R_completeness in H1. eapply ϕΠ_R_completeness in H2.
    unfold R in H1, H2.

    cbn. rewrite !eval_num.
    congruence.
  Qed.

  Lemma VR_total x y : f x = y -> Qeq ⊢C ϕΠ' x y /\ forall y', y <> y' -> Qeq ⊢C ¬ϕΠ' x y'.
  Proof.
    intros Hf%ϕΠ_R. split; first assumption.
    intros y' Hy.

    apply II.
    eapply IE with (phi := num y == num y').
    { apply Weak with (A := Qeq); last auto.
      apply Σcompleteness; first assumption.
      - repeat constructor.
      - intros ρ. cbn. rewrite !eval_num. apply Hy.
    }
    eapply IE.
    { eapply Weak with (A := Qeq); last auto. apply CT_functional. }
    eapply CI.
    - eapply Weak with (A := Qeq); eauto.
    - apply Ctx. auto.
  Qed.

End value.
