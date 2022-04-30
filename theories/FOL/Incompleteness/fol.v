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

