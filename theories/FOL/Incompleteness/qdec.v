(* TODO deduplicate imports *)
From Undecidability.FOL.Incompleteness Require Import utils.
From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
From Undecidability.Shared Require Import Dec embed_nat.

From Undecidability.FOL.Util Require Import Syntax_facts FullDeduction FullDeduction_facts FullTarski FullTarski_facts Axiomatisations FA_facts Syntax.
From Undecidability.FOL Require Import PA.

From Undecidability.FOL.Incompleteness Require Import fol.

Require Import Undecidability.Shared.Libs.DLW.Vec.vec.

From Equations Require Import Equations DepElim.
From Undecidability.FOL.Proofmode Require Import Theories ProofMode Hoas.
Require Import String.
Open Scope string_scope.
(* copied from syntax_facts *) 
Ltac invert_bounds :=
  inversion 1; subst;
  repeat match goal with
           H : existT _ _ _ = existT _ _ _ |- _ => apply Eqdep_dec.inj_pair2_eq_dec in H; try decide equality
         end; subst.
Section Qdec.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.

  Context {p : peirce}.

  (* IDEA: potentially using typeclasses? *)
  Definition Qdec φ := forall ρ, bounded 0 φ[ρ] -> Qeq ⊢ φ[ρ] \/ Qeq ⊢ ¬φ[ρ].

  Lemma Qdec_and φ ψ : Qdec φ -> Qdec ψ -> Qdec (φ ∧ ψ).
  Proof. 
    intros Hφ Hψ ρ. invert_bounds. cbn.
    destruct (Hφ _ H4), (Hψ _ H6).
    2-4: right; fintros; fdestruct 0.
    - left. now fsplit.
    - fapply H1. ctx.
    - fapply H0. ctx.
    - fapply H0. ctx.
  Qed.
  Lemma Qdec_or φ ψ : Qdec φ -> Qdec ψ -> Qdec (φ ∨ ψ).
  Proof. 
    intros Hφ Hψ ρ. invert_bounds. cbn.
    destruct (Hφ _ H4), (Hψ _ H6).
    1-3: left; now (fleft + fright).
    right. fintros. fdestruct 0.
    - fapply H0. ctx.
    - fapply H1. ctx.
  Qed.
  Lemma Qdec_impl φ ψ : Qdec φ -> Qdec ψ -> Qdec (φ ~> ψ). 
  Proof.
    intros Hφ Hψ ρ. invert_bounds. cbn.
    destruct (Hφ _ H4), (Hψ _ H6).
    - left. fintros. fapply H1.
    - right. fintros. fapply H1. fapply 0. fapply H0.
    - left. fintros. fapply H1.
    - left. fintros. fexfalso. fapply H0. ctx.
  Qed.


  (* Lemma form_ind_falsity_on : *)
  (*   forall P : form -> Prop, *)
  (*     P falsity -> *)
  (*     (forall P0 (t : vec term (ar_preds P0)), P (atom P0 t)) -> *)
  (*     (forall (b0 : binop) (f1 : form), P f1 -> forall f2 : form, P f2 -> P (bin b0 f1 f2)) -> *)
  (*     (forall (q : quantop) (f2 : form), P f2 -> P (quant q f2)) -> *)
  (*     forall (f4 : form), P f4. *)
  (* Proof. *)
  (*   intros. specialize (form_ind (fun ff => match ff with falsity_on => P | _ => fun _ => True end)). *)
  (*   intros H'. apply H' with (f3 := falsity_on); clear H'. all: intros; try destruct b; trivial. *)
  (*   all: intuition eauto 2. *)
  (* Qed. *)

  (* TODO substitutions are wrong *)
  Lemma Q_leibniz' φ :
    Q ⊢ ∀∀ $0 == $1 ~> φ[$0..][↑] ~> φ[$1..][↑].
  Proof. Admitted.
  Lemma Q_leibniz φ x y : 
    Qeq ⊢ x == y ~> φ[x..] ~> φ[y..].
  Proof. Admitted.

  Print term.
  Inductive plus_only_term : term -> Prop :=
    | pot_zero : plus_only_term zero
    | pot_succ φ : plus_only_term φ -> plus_only_term (σ φ)
    | pot_add φ ψ : plus_only_term φ -> plus_only_term ψ -> plus_only_term (φ ⊕ ψ).

  Lemma sdgjxckvlxc t φ ψ :
    plus_only_term φ -> plus_only_term ψ ->
    interp_nat ⊨= (φ == ψ) ->
    Qeq ⊢ φ == num t ~> ψ == num t.
  Proof.
    cbn. intros P1 P2 H.
    induction P1.
  Abort.




  Lemma add_zero_swap t :
    Qeq ⊢ ∀ $0 ⊕ zero == num t ~> $0 == num t.
  Proof.
    fstart. induction t; fintros.
    - fassert (ax_cases); first ctx.
      fdestruct ("H0" x).
      + ctx.
      + fdestruct "H0".
        fexfalso. fapply (ax_zero_succ (x0 ⊕ zero)).
        frewrite <- (ax_add_rec zero x0). 
        frewrite <-"H0". fapply ax_sym. ctx.
    - rewrite num_subst.
      fassert (ax_cases); first ctx.
      fdestruct ("H0" x).
      + fexfalso. fapply (ax_zero_succ (num t)).
        frewrite <-"H". frewrite "H0".
        frewrite (ax_add_zero zero).
        fapply ax_refl.
      + fdestruct "H0".
        frewrite "H0". fapply ax_succ_congr.
        fspecialize (IHt x0). rewrite !num_subst in IHt.
        fapply IHt. fapply ax_succ_inj.
        frewrite <-(ax_add_rec zero x0).
        frewrite <- "H0". fapply "H".
  Qed.
  Lemma add_zero_num t :
    Qeq ⊢ num t ⊕ zero == num t.
  Proof.
    induction t.
    - cbn. frewrite (ax_add_zero zero). fapply ax_refl.
    - cbn. frewrite (ax_add_rec zero (num t)).
      fapply ax_succ_congr. apply IHt.
  Qed.
  Lemma add_rec_swap t :
    Qeq ⊢ ∀ ∀ $0 ⊕ σ $ 1 == σ num t ~> $0 ⊕ $1 == num t.
  Proof. Admitted.


  Lemma pless_zero_eq : Qeq ⊢ ∀ ($0 ⧀= zero) ~> $0 == zero.
  Proof.
    rewrite !pless_eq.
    fstart. fintros. fdestruct "H".
    fassert ax_cases.
    { ctx. }
    fdestruct ("H0" x).
    - fapply "H0".
    - fdestruct "H0".
      fexfalso. fapply (ax_zero_succ (x1 ⊕ x0)).
      frewrite <- (ax_add_rec x0 x1). frewrite <- "H0".
      fapply "H".
  Qed.
  Lemma pless_succ t : Qeq ⊢ ∀ ($0 ⧀= num t) ~> ($0 ⧀= σ (num t)).
  Proof. 
    induction t; fstart; fintros.
    - rewrite !pless_subst. cbn.
      fassert (x == zero).
      { fapply pless_zero_eq.  rewrite pless_subst. ctx.  }
      rewrite !pless_eq. cbn. fexists (σ zero). frewrite "H0".
      fapply ax_sym. fapply ax_add_zero.
    - 
    (* induction t. *)
    (* - intros x y. destruct x as [|x']. *)
    (*   + cbn. injection 1.  easy. *)
    (*   + cbn. destruct x' as [|x'']. *)
    (*     * cbn. discriminate. *)
    (*     * cbn. discriminate. *)
    (* - intros x y. destruct x as [|x']. *)
    (*   + cbn. injection 1. easy. *)
    (*   + cbn. injection 1. intros. f_equal. apply IHt. *)
    (*     apply H0. *)
  Admitted.
  Lemma pless_sym t : Qeq ⊢ num t ⧀= num t.
  Proof.
    rewrite !pless_eq.
    fexists zero. fapply ax_sym. apply add_zero_num.
  Qed.

  Lemma pless_sigma_neq t : Qeq ⊢ ∀ ($0 ⧀= σ(num t)) ~> ¬($0 == σ(num t)) ~> $0 ⧀= num t.
  Proof. 
    rewrite !pless_eq. 
    fstart. fintros. rewrite !num_subst.
    fdestruct "H". rewrite !num_subst.
    fassert (ax_cases); first ctx.
    fdestruct ("H1" x0).
    - fexfalso. fapply "H0". 
      pose proof (add_zero_swap (S t)). cbn in H.
      fspecialize (H x). rewrite !num_subst in H.
      fapply H. frewrite <- "H1". fapply ax_sym.
      ctx.
    - fdestruct "H1". fexists x1. rewrite num_subst.
      fapply ax_sym. pose proof (add_rec_swap t). 
      fspecialize (H x1 x). rewrite !num_subst in H.
      fapply H. frewrite <-"H1". fapply ax_sym. fapply "H".
  Qed. 

  
  Lemma Q_eqdec t : Qeq ⊢ ∀ $0 == (num t) ∨ ¬($0 == num t).
  Proof. 
    induction t; fstart; fintros.
    - fassert (ax_cases); first ctx.
      fdestruct ("H" x).
      + fleft. frewrite "H".
        fapply ax_refl.
      + fright. fdestruct "H". frewrite "H".
        fintros. fapply (ax_zero_succ x0).
        fapply ax_sym. ctx.
    - rewrite num_subst.
      fassert (ax_cases); first ctx.
      fdestruct ("H" x).
      + fright. frewrite "H".
        fapply ax_zero_succ.
      + fdestruct "H". frewrite "H".
        fspecialize (IHt x0). rewrite num_subst in IHt.
        fdestruct IHt.
        * fleft. fapply ax_succ_congr. fapply "H0".
        * fright. fintros. fapply "H0".
          fapply ax_succ_inj. fapply "H1".
  Qed.


  Fixpoint fin_conj n φ := match n with
                           | 0 => φ[(num 0) ..]
                           | S n => (fin_conj n φ) ∧ φ[(num (S n)) ..]
                           end.
  Fixpoint fin_disj n φ := match n with
                           | 0 => φ[(num 0) ..]
                           | S n => (fin_disj n φ) ∨ φ[(num (S n)) ..]
                           end.
  Lemma bounded_forall_conj φ t :
    Qeq ⊢ (∀ ($0 ⧀= (num t)) ~> φ) <~> fin_conj t φ.
  Proof.
    cbn. induction t; fstart; cbn.
    - fsplit.
      + fintros. fapply "H". rewrite pless_subst. cbn. 
        pose proof (pless_sym 0). fapply H.
      + fintros.
        fassert (x == zero).
        { fapply pless_zero_eq. fapply "H0". }
        feapply Q_leibniz.
        * feapply ax_sym. fapply "H1".
        * fapply "H".
    - fsplit.
      + fintros. fsplit.
        * fapply IHt. fintros. fapply "H". 
          pose proof (pless_succ t).
          fspecialize (H x).
          rewrite !pless_subst in *. cbn in *. rewrite !num_subst in *.
          fapply H. fapply "H0".
        * fapply "H". 
          pose proof (pless_sym (S t)). cbn in H.
          rewrite pless_subst. cbn. rewrite num_subst.
          fapply H.
      + fintros. fdestruct "H". 
        rewrite pless_subst. cbn. rewrite num_subst.
        fassert (x == σ (num t) ∨ ¬(x == σ (num t))).
        { pose proof (Q_eqdec (S t)). cbn in H.
          fspecialize (H x). rewrite !num_subst in H.
          fapply H. }
        fdestruct "H2".
        * feapply Q_leibniz.
          -- feapply ax_sym. fapply "H2".
          -- fapply "H1".
        * fdestruct IHt. fapply "H4"; first fapply "H".
          rewrite pless_subst. cbn. rewrite num_subst.
          pose proof (pless_sigma_neq t).
          fspecialize (H x). 
          rewrite !pless_subst in H. cbn in H. rewrite !num_subst in H.
          fapply H.
          -- fapply "H0".
          -- fapply "H2".
  Qed.
  Lemma bounded_exist_disj φ t :
    Qeq ⊢ (∃ ($0 ⧀= (num t)) ∧ φ) <~> fin_disj t φ.
  Proof.
    cbn. induction t; fstart; cbn.
    - fsplit.
      + fintros. do 2 fdestruct "H".  rewrite pless_subst. cbn.
        fassert (x == zero).
        { fapply pless_zero_eq. rewrite pless_subst. cbn.
          fapply "H". }
        admit.
      + fintros. fexists zero. rewrite pless_subst. cbn. fsplit.
        * pose proof (pless_sym 0). cbn in H.
          fapply H.
        * ctx.
    - fsplit.
      + fintros. do 2 fdestruct "H". rewrite pless_subst. cbn. rewrite num_subst.
        fassert (x == σ (num t) ∨ ¬(x == σ (num t))).
        { pose proof (Q_eqdec (S t)). cbn in H.
          fspecialize (H x). rewrite num_subst in H.
          fapply H. }
        fdestruct "H1".
        * fright. admit.
        * fleft. fapply IHt. fexists x. fsplit; last ctx.
          rewrite pless_subst. rewrite num_subst. cbn.
          pose proof (pless_sigma_neq t).
          fspecialize (H x). rewrite !pless_subst in H. cbn in H.
          rewrite num_subst in H.
          fapply H; ctx.
      + fintros. fdestruct "H".
        * fapply IHt in "H". fdestruct "H". fexists x. fdestruct "H".
          fsplit; last ctx.
          rewrite !pless_subst. cbn. rewrite num_subst.
          pose proof (pless_succ t). fspecialize (H x).
          rewrite !pless_subst in H. cbn in H. rewrite num_subst in H.
          fapply H. ctx.
        * fexists (σ num t). rewrite pless_subst. cbn. rewrite num_subst.
          fsplit; last ctx.
          pose proof (pless_sym (S t)). cbn in H. fapply H.
  Admitted.
  Lemma Qdec_fin_conj φ t :
    Qdec φ -> Qdec (fin_conj t φ).
  Proof.
    intros Hφ. induction t; cbn; intros ρ.
    - intros H. rewrite subst_comp in *.
      apply Hφ, H.
    - cbn. rewrite subst_comp. invert_bounds.
      destruct (Hφ _ H6), (IHt _ H4).
      + left. now fsplit.
      + right. fintros. fdestruct 0.
        fapply H1. fapply 1.
      + right. fintros. fdestruct 0.
        fapply H0. fapply 0.
      + right. fintros. fdestruct 0.
        fapply H1. fapply 1.
  Qed.
  Lemma Qdec_fin_disj φ t :
    Qdec φ -> Qdec (fin_disj t φ).
  Proof.
    intros Hφ. induction t; cbn; intros ρ.
    - intros H. rewrite subst_comp in *.
      apply Hφ, H.
    - cbn. rewrite subst_comp. invert_bounds.
      destruct (Hφ _ H6), (IHt _ H4).
      1-3: left; now (fleft + fright).
      right. fintros. fdestruct 0.
      + fapply H1. ctx.
      + fapply H0. ctx.
  Qed.
End Qdec.
