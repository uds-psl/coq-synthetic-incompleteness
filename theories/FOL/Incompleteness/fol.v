(* TODO deduplicate imports *)
From Undecidability.FOL.Incompleteness Require Import utils.
From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
From Undecidability.Shared Require Import Dec embed_nat.

From Undecidability.FOL.Util Require Import Syntax_facts FullDeduction FullDeduction_facts FullTarski FullTarski_facts Axiomatisations FA_facts Syntax.
From Undecidability.FOL Require Import PA.

Require Import Undecidability.Shared.Libs.DLW.Vec.vec.

From Equations Require Import Equations DepElim.
From Undecidability.FOL.Proofmode Require Import Theories ProofMode Hoas.
Require Import String.
Open Scope string_scope.

Section lemmas.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.

  Lemma num_subst x ρ : (num x)`[ρ] = num x.
  Proof.
    induction x; cbn; congruence.
  Qed.
End lemmas.

Section syntax.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.

  (* Notation for satisfying list theories *)
  Notation "I ⊨=L T" := (forall psi, List.In psi T -> I ⊨= psi) (at level 20).
  (* Notation for explicitely giving model *)
  (* TODO possibility: use I ⊨ rho phi, similar to Coq *)
  Notation "I ; rho '⊨' phi" := (@sat _ _ _ I _ rho phi) (at level 20, rho at next level).

  Definition pless x y := ∃ y`[↑] == (x`[↑] ⊕ $0).
  Definition pless_swap x y := ∃ y`[↑] == ($0 ⊕ x`[↑]).
  Definition pless_or x y := ∃ y`[↑] == ($0 ⊕ x`[↑]) ∨ y`[↑] == (x`[↑] ⊕ $0).
  Definition mless {M} {I : interp M} x y := exists k, y = x i⊕ k.

  Lemma pless_eq x y : pless x y = ∃ y`[↑] == (x`[↑] ⊕ $0).
  Proof. reflexivity. Qed.
  Lemma pless_subst x y ρ : (pless x y)[ρ] = pless (x`[ρ]) (y`[ρ]).
  Proof.
    rewrite !pless_eq. cbn. do 3 f_equal.
    - rewrite !subst_term_comp. reflexivity. 
    - do 3 f_equal. rewrite !subst_term_comp. reflexivity. 
  Qed.
  (* TODO add *)
  Global Opaque pless.
  (* Global Opaque pless_swap.*)
  (* Global Opaque pless_or.*)
  (*  Global Opaque mless.*)
End syntax.
(* Notations for le *)
Notation "x '⧀=' y"  := (pless x y) (at level 42) : PA_Notation.
Notation "x '⧀=comm' y"  := (pless_swap x y) (at level 42) : PA_Notation.
(* TODO remove if not needed *)
Notation "x '⧀==' y"  := (pless_or x y) (at level 42) : PA_Notation.
(* NOTE this definition requires extensionality of the model *)
Notation "x 'i⧀=' y"  := (mless x y) (at level 42) : PA_Notation.

Definition Qeq := PA.Qeq.
Global Opaque Qeq.
Lemma Qeq_def : Qeq = PA.Qeq.
Proof. reflexivity. Qed.

Section PM.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.

  Global Program Instance PA_Leibniz : Leibniz PA_funcs_signature PA_preds_signature falsity_on.
  Next Obligation. exact Eq. Defined.
  Next Obligation. exact Qeq. Defined.
  Next Obligation. fintros. fapply ax_refl. Qed.
  Next Obligation. fintros. fapply ax_sym. ctx. Qed.
  Next Obligation.
    unfold PA_Leibniz_obligation_1 in *. rename v1 into t; rename v2 into t0.
    destruct F; repeat dependent elimination t0; repeat dependent elimination t.
    - fapply ax_refl.
    - fapply ax_succ_congr. apply H1.
    - fapply ax_add_congr; apply H1.
    - fapply ax_mult_congr; apply H1.
  Qed.
  Next Obligation.
    unfold PA_Leibniz_obligation_1 in *. rename v1 into t; rename v2 into t0.
    destruct P; repeat dependent elimination t0; repeat dependent elimination t.
    - cbn in H1. split.
      + intros H2. feapply ax_trans. feapply ax_sym. apply H1. feapply ax_trans.
        apply H2. apply H1.
      + intros H2. feapply ax_trans. apply H1. feapply ax_trans. apply H2.
        fapply ax_sym. apply H1.
  Qed.


  Notation "'σh' x" := (bFunc Succ (Vector.cons bterm x 0 (Vector.nil bterm))) (at level 32) : hoas_scope.
  Notation "x '⊕h' y" := (bFunc Plus (Vector.cons bterm x 1 (Vector.cons bterm y 0 (Vector.nil bterm))) ) (at level 39) : hoas_scope.
  Notation "x '⊗h' y" := (bFunc Mult (Vector.cons bterm x 1 (Vector.cons bterm y 0 (Vector.nil bterm))) ) (at level 38) : hoas_scope. 
     Notation "x '==h' y" := (bAtom Eq (Vector.cons bterm x 1 (Vector.cons bterm y 0 (Vector.nil bterm))) ) (at level 40) : hoas_scope.
End PM.
Ltac custom_simpl := rewrite ?pless_subst; cbn; rewrite ?num_subst; cbn.

Section Qdec.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.

  Context {p : peirce}.

  Definition Qdec φ := Qeq ⊢ φ \/ Qeq ⊢ ¬φ.


  Ltac invert_bounds H :=
    inversion H; subst;
    repeat match goal with
             H : existT _ _ _ = existT _ _ _ |- _ => apply Eqdep_dec.inj_pair2_eq_dec in H; try decide equality
           end; subst.

  Lemma Qdec_and φ ψ : Qdec φ -> Qdec ψ -> Qdec (φ ∧ ψ).
  Proof.
    intros Hφ Hψ. 
    destruct Hφ as [H1|H1], Hψ as [H2|H2]; cbn.
    - left. now fsplit.
    - right. fintros. fdestruct 0. fapply H2. fapply 0.
    - right. fintros. fdestruct 0. fapply H1. fapply 1.
    - right. fintros. fdestruct 0. fapply H2. fapply 0.
  Qed.
  Lemma Qdec_or φ ψ : Qdec φ -> Qdec ψ -> Qdec (φ ∨ ψ).
  Proof.
    intros Hφ Hψ. 
    destruct Hφ as [H1|H1], Hψ as [H2|H2]; cbn.
    - left. now fleft.
    - left. now fleft.
    - left. now fright.
    - right. fintros. fdestruct 0.
      + fapply H1. ctx.
      + fapply H2. ctx.
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

  Lemma Q_leibniz φ x y : 
    Qeq ⊢ x == y ~> φ[x..] ~> φ[y..].
  Proof.
  Admitted.

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
  Proof. Admitted.


  Fixpoint fin_conj n φ := match n with
                           | 0 => φ[(num 0) ..]
                           | S n => (fin_conj n φ) ∧ φ[(num (S n)) ..]
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
End Qdec.
