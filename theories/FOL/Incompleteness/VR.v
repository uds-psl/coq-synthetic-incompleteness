From Undecidability.FOL.Incompleteness Require Import FS CT.
From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
From Undecidability.Shared Require Import Dec embed_nat.

From Undecidability.FOL.Util Require Import Syntax_facts FullDeduction FullDeduction_facts FullTarski FullTarski_facts Axiomatisations FA_facts Syntax.
From Undecidability.FOL Require Import PA.
Import Vector.VectorNotations.

Print prv.


Section sigma.
  Existing Instance PA_funcs_signature.
  Existing Instance PA_preds_signature.

  (* TODO need to remove ff flags from these structures to ease inductions *)

  Hypothesis LEM : forall P, P \/ ~P.

  (* Definitions stolen from Marc *)
  Inductive Δ0 : form -> Prop :=
  | Delta_fal : Δ0 ⊥
  | Delta_eq : forall t s, Δ0 (t == s)
  (* | Delta_lt ff : forall t s, @Δ0 ff (t ⧀ s) *)
  | Delta_Conj : forall α β, Δ0 α -> Δ0 β -> Δ0 (α ∧ β)
  | Delta_Disj : forall α β, Δ0 α -> Δ0 β -> Δ0 (α ∨ β)
  | Delta_Impl : forall α β, Δ0 α -> Δ0 β -> Δ0 (α ~> β).

  Inductive Δ0' : form -> Prop :=
  | Delta_id : forall α, Δ0 α -> Δ0' α
  | Delta_bounded_exist : forall α, Δ0' α -> Δ0' (∃ ($0 ⧀ $1) ∧ α)
  | Delta_bounded_forall : forall α, Δ0' α -> Δ0' (∀ $0 ⧀ $1 ~> α).

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


(* Notation for satisfying list theories *)
Notation "I ⊨=L T" := (forall psi, List.In psi T -> I ⊨= psi) (at level 20).
(* Notation for explicitely giving model *)
Notation "I , rho '⊨' phi" := (@sat _ _ _ I _ rho phi) (at level 20, rho at next level).

(* increasing x instead of k to be able to use recursive formulae *)
(* NOTE this definition requires extensionality of the model *)
Notation "x 'i⧀' y"  := (exists k, y = (iσ x) i⊕ k) (at level 42) : PA_Notation.
(* Overwriting notation from PA.v to be useful in any way *)
Notation "x '⧀' y"  := (∃ y`[↑] == ((σ x`[↑]) ⊕ $0)) (at level 42) : PA_Notation.
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




Section value.
  Existing Instance PA_funcs_signature.
  Existing Instance PA_preds_signature.

  Existing Instance class.

  Existing Instance interp_nat.

  Hypothesis completeness : forall φ,
    Qeq ⊢C φ <-> forall (M : Type) (I : interp M) ρ, extensional I -> I ⊨=L Qeq -> ρ ⊨ φ.
  Hypothesis Σcompleteness : forall M (I : interp M) φ ρN ρM,
      bounded 0 φ -> Σ1 φ ->
      interp_nat, ρN ⊨ φ ->
      I, ρM ⊨ φ.
  Hypothesis Δ0decidability : forall φ, Δ0' φ -> Qeq ⊢C φ \/ Qeq ⊢C ¬φ.

  Variable f : nat -> nat -> option nat.
  Variable f_func : forall x y1 y2 k1 k2, f x k1 = Some y1 -> f x k2 = Some y2 -> y1 = y2.

  Variable T : form.
  Hypothesis T_bounded : bounded 3 T.
  (* NOTE Delta1 could suffice here, since its still decidable *)
  Hypothesis T_Δ0 : Δ0' T.
  Hypothesis T_sem : forall M (I : interp M) ρ x y,
      (exists k, f x k = Some y) <-> ρ ⊨ ∃ T[num x .: (num y) ..].
  (* T is functional in nat. This assumption is implicit in the post by saying "a T predicate",
     I guess *)
  Hypothesis T_func : forall ρ x k k' y y',
      interp_nat, ρ ⊨ T[num x .: num y .: (num k) ..] ->
      interp_nat, ρ ⊨ T[num x .: num y' .: (num k') ..] ->
      y = y' /\ k = k'.
  Hypothesis T_syn : forall x y,
      (exists k, f x k = Some y) <-> Qeq ⊢C ∃ T[num x .: num y .: $0 ..].

  Definition T' := T ∧ ∀∀ ($1⊕$0 ⧀ $3⊕$4) ~> T[$2.:$1.:$0..] ~> ⊥.

  Lemma sat_T_bound M (I : interp M) (ρ : env M) :
    ρ ⊨ T <-> (ρ 0 .: ρ 1 .: ρ 2 .: (fun _ => iO)) ⊨ T.
  Proof.
    split.
    - eapply bound_ext; first apply T_bounded.
      intros [|[|[|n]]] H; cbn; lia + easy.
    - eapply bound_ext; first apply T_bounded.
      intros [|[|[|n]]] H; cbn; lia + easy.
  Qed.
  Lemma subst_T_bound (ρ : env term) :
    T[ρ] = T[ρ 0 .: ρ 1 .: (ρ 2) ..].
  Proof.
    eapply bounded_subst; first apply T_bounded.
    intros [|[|[|n]]] H; cbn; lia + easy.
  Qed.

  Lemma sat_subst_single_nat φ (ρ : env nat) (k : nat) :
    (k .: ρ) ⊨ φ -> ρ ⊨ φ [(num k)..].
  Proof.
    rewrite <-sat_single, eval_num.
    replace (iμ k) with k; first easy.
    induction k; cbn; congruence.
  Qed.
  Lemma sat_subst_single_model M (I : interp M) φ (ρ : env M) (k : nat) :
    (iμ k .: ρ) ⊨ φ <-> ρ ⊨ φ[(num k)..].
  Proof.
    split.
    - intros H. rewrite <-sat_single. now rewrite eval_num.
    - intros H. rewrite <-sat_single in H.
      now rewrite eval_num in H.
  Qed.

  Lemma T_completeness M (I : interp M) (Mext : extensional I) (MQ : I ⊨=L Qeq) ρN ρM x y k :
    interp_nat, ρN ⊨ T[num x .: num y .: (num k) ..] <-> I, ρM ⊨ T[num x .: num y .: (num k)..].
  Proof.
    split.
    - intros H. eapply Σcompleteness.
      + eapply subst_bound; first apply T_bounded.
        intros [|[|[|n]]]; intros H'; last lia.
        all: apply num_bound.
      + admit.
      + apply H.
    - intros H. destruct Δ0decidability with (φ := T[num x .: num y .: (num k) ..]) as [HQ|HQ].
      + admit. (* TODO by substitution *)
      + eapply completeness; now auto using nat_is_Q_model.
      + eapply completeness with (I := I) in HQ; try assumption.
        exfalso. apply HQ, H.
  Admitted.
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
    (exists k, f x k = Some y) <-> exists k, interp_nat, ρ ⊨ T[num x .: num y .: (num k) ..].
  Proof.
    split.
    - intros H. eapply T_sem with (I := interp_nat) (ρ := ρ) in H.
      destruct H as [k Hk]. exists k. now apply T_single_rho_nat.
    - intros [k Hk]. eapply T_sem. exists k. apply T_single_rho_nat, Hk.
  Qed.


  Lemma VR1 x y : (exists k, f x k = Some y) -> Qeq ⊢C ∃T'[num x .: (num y) ..].
  Proof.
    intros Hf. apply completeness.
    intros M I ρ Mext HI.
    assert (exists k, (fun _ => 0) ⊨ T[num x .: num y .: (num k) ..]) as [k Hk] by now apply T_sem'.
    exists (iμ k). split.
    - apply T_single_rho_model. now eapply T_completeness, Hk.
    - intros y' k' [d Hle] HT. cbn.
      cbn in Hle. rewrite !num_subst, !eval_num, Mext in Hle.

      assert (standard (iμ y i⊕ iμ k)) as Hyk.
      { rewrite add_hom; try assumption. apply num_standard. }
      rewrite Hle, !add_rec, <-standard_succ in Hyk; try assumption.
      apply standard_add in Hyk as [[[y'' <-] [k'' <-]]%standard_add [d' <-]]; try assumption.

      assert (y + k = S y'' + k'' + d') as Hle'.
      { eapply iμ_inj; try assumption. cbn.
        rewrite <-!add_hom, <-add_rec; try assumption. }

      rewrite !sat_subst_single_model, !subst_comp, subst_T_bound in HT. cbn in HT.
      rewrite !num_subst in HT.
      eapply T_completeness in HT; try assumption.

      pose proof (T_func Hk HT). lia.
  Qed.
  Lemma VR2 x y' y : (exists k, f x k = Some y) -> y <> y' -> Qeq ⊢C ¬∃T'[num x .: (num y') ..].
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

      assert (exists k, f x k = Some y').
      { eapply T_sem' with (ρ := fun _ => 0). exists ks.
        rewrite T_completeness, <-T_single_rho_model; first apply Hk1; assumption. }

      destruct Hf, H.
      eapply f_func; eassumption.
    - rewrite !sat_subst_single_model, !subst_comp, subst_T_bound. cbn.
      rewrite !num_subst.
      eapply T_completeness, Hkk; try assumption.
  Qed.
End value.


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
Check VR_total.
