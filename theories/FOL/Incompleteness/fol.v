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


(* Notation for satisfying list theories *)
Notation "I ⊨=L T" := (forall psi, List.In psi T -> I ⊨= psi) (at level 20).
(* Notation for explicitely giving model *)
Notation "I ; rho '⊨' phi" := (@sat _ _ _ I _ rho phi) (at level 20, rho at next level).

Section lemmas.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.
  Existing Instance interp_nat.

  Lemma num_subst x ρ : (num x)`[ρ] = num x.
  Proof.
    induction x; cbn; congruence.
  Qed.

  Lemma num_bound n k : bounded_t k (num n).
  Proof.
    induction n; cbn; constructor.
    - intros t []%Vectors.In_nil.
    - intros t ->%vec_singleton.
      assumption.
   Qed.

  Lemma subst_bound psi : (* TODO move to util *)
      forall sigma N B, bounded N psi -> (forall n, n < N -> bounded_t B (sigma n) ) -> bounded B (psi[sigma]).
  Proof. 
  Admitted. (* by Marc *)

  Lemma Q_sound_class φ : (forall P, P \/ ~P) -> Qeq ⊢C φ -> interp_nat ⊨= φ.
  Proof.
    intros LEM H ρ. eapply soundness_class.
    - assumption.
    - eassumption.
    - apply nat_is_Q_model.
  Qed.
  Lemma Q_sound_intu φ : Qeq ⊢I φ -> interp_nat ⊨= φ.
  Proof.
    intros H ρ. eapply soundness.
    - eassumption.
    - apply nat_is_Q_model. 
  Qed.

  Lemma iμ_eval_num M (I : interp M) k ρ : iμ k = eval ρ (num k).
  Proof.
    induction k; cbn; congruence.
  Qed.
  Lemma iμ_standard (k : nat) : iμ k = k.
  Proof.
    induction k; cbn; congruence.
  Qed.

  Lemma sat_single_PA M (I : interp M) φ ρ k : (iμ k .: ρ) ⊨ φ <-> ρ ⊨ φ[(num k)..].
  Proof.
    erewrite iμ_eval_num. apply sat_single.
  Qed.
  Lemma sat_single_nat φ ρ k : interp_nat; (k .: ρ) ⊨ φ <-> interp_nat; ρ ⊨ φ[(num k)..].
  Proof.
    erewrite <-iμ_standard at 1.
    now rewrite sat_single_PA.
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


End PM.
Global Ltac custom_simpl ::= cbn; rewrite ?pless_subst; cbn; rewrite ?num_subst; cbn.
Global Notation "'σh' x" := (bFunc Succ (Vector.cons bterm x 0 (Vector.nil bterm))) (at level 32) : hoas_scope.
Global Notation "x '⊕h' y" := (bFunc Plus (Vector.cons bterm x 1 (Vector.cons bterm y 0 (Vector.nil bterm))) ) (at level 39) : hoas_scope.
Global Notation "x '⊗h' y" := (bFunc Mult (Vector.cons bterm x 1 (Vector.cons bterm y 0 (Vector.nil bterm))) ) (at level 38) : hoas_scope. 
Global Notation "x '==h' y" := (bAtom Eq (Vector.cons bterm x 1 (Vector.cons bterm y 0 (Vector.nil bterm))) ) (at level 40) : hoas_scope.


Global Ltac invert_bounds :=
  inversion 1; subst;
  repeat match goal with
           H : existT _ _ _ = existT _ _ _ |- _ => apply Eqdep_dec.inj_pair2_eq_dec in H; try decide equality
         end; subst.

Section n.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.
  Context `{pei : peirce}.

  Lemma closed_term_is_num s : bounded_t 0 s -> { n & Qeq ⊢ s == num n }.
  Proof.
    intros H. 
    induction s using term_rect. 2: destruct F.
    - exfalso. inversion H. lia.
    - rewrite (vec_0_nil v). exists 0.
      fapply ax_refl.
    - destruct (vec_1_inv v) as [t ->]. destruct (X t) as [n Hn].
      + left.
      + revert H. invert_bounds. apply H1. left.
      + exists (S n). fapply ax_succ_congr. apply Hn.
    - destruct (vec_2_inv v) as (t1 & t2 & ->). 
      destruct (X t1, X t2) as [[n1 Hn1] [n2 Hn2]].
      + left.
      + revert H. invert_bounds. apply H1. left.
      + right. left.
      + revert H. invert_bounds. apply H1. right. left.
      + exists (n1 + n2).
        pose proof num_add_homomorphism as H'.
        refine ((fun H'' => _) (H' _ Qeq _ n1 n2)).
        2: { firstorder. }
        frewrite <-H''.
        fapply ax_add_congr; assumption.
    - destruct (vec_2_inv v) as (t1 & t2 & ->). 
      destruct (X t1, X t2) as [[n1 Hn1] [n2 Hn2]].
      + left.
      + revert H. invert_bounds. apply H1. left.
      + right. left.
      + revert H. invert_bounds. apply H1. right. left.
      + exists (n1 * n2).
        pose proof num_mult_homomorphism as H'.
        refine ((fun H'' => _) (H' _ Qeq _ n1 n2)).
        2: { firstorder. }
        frewrite <-H''.
        fapply ax_mult_congr; assumption.
  Qed.
  
End n.
