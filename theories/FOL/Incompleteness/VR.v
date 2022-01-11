From Undecidability.FOL.Incompleteness Require Import FS CT.
From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
From Undecidability.Shared Require Import Dec embed_nat.

From Undecidability.FOL.Util Require Import Syntax_facts FullDeduction FullDeduction_facts FullTarski FullTarski_facts Axiomatisations FA_facts Syntax.
From Undecidability.FOL Require Import PA.

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Section sigma.
  Existing Instance PA_funcs_signature.
  Existing Instance PA_preds_signature.

  (* Definitions stolen from Marc *)
  Inductive Δ0 : forall {ff : falsity_flag}, form -> Prop :=
  | Delta_fal : @Δ0 falsity_on ⊥
  | Delta_eq ff : forall t s, @Δ0 ff (t == s)
  (* | Delta_lt ff : forall t s, @Δ0 ff (t ⧀ s) *)
  | Delta_Conj ff : forall α β, @Δ0 ff α -> Δ0 β -> @Δ0 ff (α ∧ β)
  | Delta_Disj ff : forall α β, @Δ0 ff α -> Δ0 β -> Δ0 (α ∨ β)
  | Delta_Impl ff : forall α β, @Δ0 ff α -> Δ0 β -> Δ0 (α ~> β).

  Inductive Δ0' : forall {ff : falsity_flag}, form -> Prop :=
  | Delta_id ff : forall α, Δ0 α -> @Δ0' ff α
  (*| Delta_bounded_exist ff : forall α, @Δ0' ff α -> Δ0' (∃ ($0 ⧀ $1) ∧ α)
  | Delta_bounded_forall ff : forall α, @Δ0' ff α -> Δ0' (∀ $0 ⧀ $1 ~> α)*).

  Inductive Σ1 : forall {ff : falsity_flag}, form -> Prop :=
  | Sigma_Delta ff : forall α, Δ0' α -> @Σ1 ff α
  | Sigma_exists ff : forall α, Σ1 α -> @Σ1 ff (∃ α).
  Inductive Π1 : forall {ff : falsity_flag}, form -> Prop :=
  | Pi_Delta ff : forall α, Δ0' α -> @Π1 ff α
  | Pi_forall ff : forall α, Π1 α -> @Π1 ff (∀ α).
  Inductive Δ1 : forall {ff : falsity_flag}, form -> Prop :=
  | Delta_Sigma ff : forall α, @Σ1 ff α -> @Δ1 ff α
  | Delta_Pi ff : forall α, @Π1 ff α -> @Δ1 ff α.



  Lemma PNF_conj φ1 φ2 : Π1 φ1 -> Π1 φ2 -> exists ψ, Π1 ψ /\ Qeq ⊢C φ1 ∧ φ2 <~> ψ.
  Proof.

  Admitted.
  Lemma PNF_impl φ1 φ2 : Π1 φ1 -> Σ1 φ2 -> exists ψ, Σ1 ψ /\ Qeq ⊢C (φ1 ~> φ2) <~> ψ.
  Proof. Admitted.
End sigma.

Section value.
  Existing Instance PA_funcs_signature.
  Existing Instance PA_preds_signature.

  Existing Instance interp_nat.


  Hypothesis LEM : forall P, P \/ ~P.

  Hypothesis Σcompleteness : forall φ, Σ1 φ -> interp_nat ⊨= φ -> Qeq ⊢C φ.
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

  Lemma completeness_equiv φ1 φ2 : Σ1 φ2 -> Qeq ⊢C φ1 <~> φ2 -> interp_nat ⊨= φ1 -> Qeq ⊢C φ1.
  Proof.
    intros Hs Hequiv Hnat.
    enough (Qeq ⊢C φ2) as H.
    {
      eapply IE; last exact H.
      eapply CE2. apply Hequiv.
    }
    apply Σcompleteness; first assumption.
    intros rho.
    eapply Q_sound in Hequiv.
    cbn in Hequiv.
    apply Hequiv, Hnat.
  Qed.


  Variable (f : nat -> nat).
  Definition R x y := f x = y.

  Variable ϕΣ ϕΠ : form.
  Definition ϕΣ' x y := ϕΣ[num x .: (num y) ..].
  Definition ϕΠ' x y := ϕΠ[num x .: (num y) ..].
  Hypothesis (ϕΣ_bounded : bounded 2 ϕΣ) (ϕΣ_Σ : forall x y, Σ1 (ϕΣ' x y)).
  Hypothesis (ϕΠ_bounded : bounded 2 ϕΠ) (ϕΠ_Π : forall x y, Π1 (ϕΠ' x y)).


  Hypothesis ϕΣ_R : forall x y,
      (R x y -> Qeq ⊢C ϕΣ' x y) /\
      (Qeq ⊢C ϕΣ' x y -> interp_nat ⊨= ϕΣ' x y) /\
      (interp_nat ⊨= ϕΣ' x y -> R x y).
  Hypothesis ϕΠ_R : forall x y,
      (R x y -> Qeq ⊢C ϕΠ' x y) /\
      (Qeq ⊢C ϕΠ' x y -> interp_nat ⊨= ϕΠ' x y) /\
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
    destruct (@PNF_conj (ϕΠ' x y) (ϕΠ' x y')) as (ψ1 & Hb1 & Hc1); try apply ϕΠ_Π.
    apply IE with (phi := ψ1); first last.
    { eapply IE.
      - eapply CE1. apply Weak with (A := Qeq); last auto. eapply Hc1.
      - now apply Ctx.
    }
    apply Weak with (A := Qeq); last auto.

    destruct (@PNF_impl ψ1 (num y == num y')) as (ψ2 & Hs2 & Hc2).
    { assumption. }
    { repeat constructor. }

    eapply completeness_equiv; try eassumption.
    intros rho Hψ1.

    eapply Q_sound with (rho := rho) in Hc1 as [Hc1 Hc1'].
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
      apply Σcompleteness.
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
