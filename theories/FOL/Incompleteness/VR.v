From Undecidability.FOL.Incompleteness Require Import FS CT.
From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
From Undecidability.Shared Require Import Dec embed_nat.

From Undecidability.FOL.Util Require Import Syntax_facts FullDeduction FullDeduction_facts FullTarski FullTarski_facts Axiomatisations FA_facts Syntax.
From Undecidability.FOL Require Import PA.
(* Notation for satisfying list theories *)
Notation "I ⊨=L T" := (forall psi, List.In psi T -> I ⊨= psi) (at level 20).
(* Notation for explicitely giving model *)
Notation "I ; rho '⊨' phi" := (@sat _ _ _ I _ rho phi) (at level 20, rho at next level).

(* increasing x instead of k to be able to use recursive formulae *)
(* NOTE this definition requires extensionality of the model *)
Notation "x 'i⧀' y"  := (exists k, y = (iσ x) i⊕ k) (at level 42) : PA_Notation.
(* Overwriting notation from PA.v to be useful in any way *)
(* Adding notation for <= *)
Notation "x '⧀' y"  := (∃ y`[↑] == ((σ x`[↑]) ⊕ $0)) (at level 42) : PA_Notation.
Notation "x '⧀=' y"  := (∃ y`[↑] == (x`[↑] ⊕ $0)) (at level 42) : PA_Notation.
(* I need another oless *)
Notation "x '⧀comm' y"  := (∃ y`[↑] == ($0 ⊕ x`[↑])) (at level 42) : PA_Notation.
Notation "x '⧀=comm' y"  := (∃ y`[↑] == ($0 ⊕ x`[↑])) (at level 42) : PA_Notation.


Require Import Coq.Classes.DecidableClass.
Program Instance Decidable_eq_option {X} `{Xdec : forall (x y : X), Decidable (x = y)} : forall (x y : option X), Decidable (eq x y).
Next Obligation.
  destruct x as [x|], y as [y|].
  - apply (Xdec x y).
  - exact false.
  - exact false.
  - exact true.
Defined.
Next Obligation.
  destruct x as [x|], y as [y|]; cbn.
  2-4: try easy.
  unfold Decidable_witness. destruct (Xdec x y).
  split.
  - intros H. f_equal. tauto.
  - intros [=]. tauto.
Qed.



From Equations Require Import Equations DepElim.
From Undecidability.FOL.Proofmode Require Import Theories ProofMode Hoas.
Require Import String List.
Open Scope string_scope.
Section proofmode.
  Existing Instance PA_funcs_signature.
  Existing Instance PA_preds_signature.

  (* Cannot be concrete due to bug in Proofmode *)
  Variable (p : peirce).
  (* TODO taken from DemoPA.v, need to deduplicate *)
  Program Instance PA_Leibniz : Leibniz PA_funcs_signature PA_preds_signature falsity_on.
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
End proofmode.
Notation "'σ' x" := (bFunc Succ (Vector.cons bterm x 0 (Vector.nil bterm))) (at level 32) : hoas_scope.
Notation "x '⊕' y" := (bFunc Plus (Vector.cons bterm x 1 (Vector.cons bterm y 0 (Vector.nil bterm))) ) (at level 39) : hoas_scope.
Notation "x '⊗' y" := (bFunc Mult (Vector.cons bterm x 1 (Vector.cons bterm y 0 (Vector.nil bterm))) ) (at level 38) : hoas_scope. 
Notation "x '==' y" := (bAtom Eq (Vector.cons bterm x 1 (Vector.cons bterm y 0 (Vector.nil bterm))) ) (at level 40) : hoas_scope.
Notation "x '⧀' y"  := (∃' z, y == ((σ x) ⊕ z))%hoas (at level 42) : hoas_scope.
Notation "x '⧀=' y"  := (∃' z, y == (x ⊕ z))%hoas (at level 42) : hoas_scope.
Ltac custom_simpl ::= try rewrite ?num_subst.


Section sigma.
  Existing Instance PA_funcs_signature.
  Existing Instance PA_preds_signature.

  Existing Instance falsity_on.

  Definition Qdec (φ : form) := Qeq ⊢C φ \/ Qeq ⊢C ¬ φ.

  Inductive Δ0 : form -> Prop :=
  | Delta_fal : Δ0 ⊥
  | Delta_eq : forall t s, Δ0 (t == s)
  | Delta_lt : forall t s, Δ0 (t ⧀ s)
  | Delta_le : forall t s, Δ0 (t ⧀= s)
  | Delta_Conj : forall α β, Δ0 α -> Δ0 β -> Δ0 (α ∧ β)
  | Delta_Disj : forall α β, Δ0 α -> Δ0 β -> Δ0 (α ∨ β)
  | Delta_Impl : forall α β, Δ0 α -> Δ0 β -> Δ0 (α ~> β)
  | Delta_bounded_exist : forall α t, Δ0 α -> Δ0 (∃ ($0 ⧀= t`[↑]) ∧ α)
  | Delta_bounded_exist_comm : forall α t, Δ0 α -> Δ0 (∃ ($0 ⧀=comm t`[↑]) ∧ α)
  | Delta_bounded_forall : forall α t, Δ0 α -> Δ0 (∀ $0 ⧀= t`[↑] ~> α)
  | Delta_bounded_binary_forall : forall α t, Δ0 α 
    -> Δ0 (∀ ∀ $1 ⊕ $0 ⧀= t`[↑]`[↑] ~> α).

  Inductive Σ1 : form -> Prop :=
  | Sigma_exists : forall α, Σ1 α -> Σ1 (∃ α)
  | Sigma_Delta : forall α, Δ0 α -> Σ1 α.
  Inductive Π1 : form -> Prop :=
  | Pi_forall : forall α, Π1 α -> Π1 (∀ α)
  | Pi_Delta : forall α, Δ0 α -> Π1 α.

  Lemma subst_term_up_comp s sigma : s`[↑]`[up sigma] = s`[sigma]`[↑].
  Proof.
    rewrite !subst_term_comp. now apply subst_term_ext.
  Qed.
  Lemma Δ0_subst φ sigma : Δ0 φ -> Δ0 φ[sigma].
  Proof.
    induction 1 in sigma |-*; cbn.
    all: rewrite ?subst_term_up_comp; now constructor.
  Qed.
  Lemma Σ1_subst φ sigma : Σ1 φ -> Σ1 φ[sigma].
  Proof.
    induction 1 in sigma |-*; cbn; auto using Σ1, Δ0_subst.
  Qed.

  Lemma exists_compression_2 φ : Δ0 φ -> exists ψ, Δ0 ψ /\ Qeq ⊢C (∃∃φ) <~> (∃ψ).
  Proof.
    intros Hd.
    exists (∃ ($0 ⧀= $1) ∧ ∃ ($0 ⧀=comm $2) ∧ φ[up (up (S >> var))]).
    split.
    { change $1 with ($0`[↑]). change $2 with ($1`[↑]).
      repeat constructor. apply Δ0_subst, Hd. }
    apply CI.
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
      apply ExI with (t := $1 ⊕ $0).
      cbn -[Qeq]. unfold "↑". fold ↑.
      apply ExI with (t := $1).
      cbn -[Qeq]. unfold "↑". fold ↑.
      apply CI.
      { apply ExI with (t := $0). cbn -[Qeq].
        eapply AllE with (t := $1 ⊕ $0) (phi := $0 == $0).
        apply Ctx. right. now left. }
      apply ExI with (t := $0).
      cbn -[Qeq]. unfold "↑". fold ↑.
      apply CI.
      { apply ExI with (t := $1). cbn -[Qeq].
        eapply AllE with (t := $1 ⊕ $0) (phi := $0 == $0).
        apply Ctx. right. now left. }
      rewrite !subst_comp. erewrite subst_ext; first instantiate (1 := var).
      + rewrite subst_var. now apply Ctx.
      + now intros [|[|[|n]]]; cbn.
    - apply II.
      eapply ExE.
      { apply Ctx; now left. }
      cbn -[Qeq]. unfold "↑". fold ↑.
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
      apply subst_ext. now intros [|[|[|n]]].
  Qed.

  Lemma exists_equiv φ ψ : Qeq ⊢C φ ~> ψ -> (∃φ :: Qeq) ⊢C (∃ψ).
  Proof.
    intros H. eapply ExE.
    { apply Ctx. now left. }
    cbn -[Qeq]. fexists $0. (* Including proofmode broke ExI *)
    replace (ψ[_][_]) with (ψ[var]); first last.
    { rewrite subst_comp. apply subst_ext. now intros [|k]. }
    rewrite subst_var. eapply IE.
    { eapply Weak; first apply H. now do 2 right. }
    now apply Ctx.
  Qed.

  Lemma exists_compression φ n : Δ0 φ ->
                                 exists ψ, Δ0 ψ /\ Qeq ⊢C exist_times n φ <~> ∃ ψ.
  Proof.
    intros Hd. induction n as [|n (φ' & HΔ & Hφ')].
    all: cbn [exist_times iter].
    - exists φ[↑]. split; first now apply Δ0_subst.
      apply CI.
      + apply II. fexists $0. apply Ctx. now left.
      + apply II. eapply ExE; first (apply Ctx; now left).
        apply Ctx. now left.
    - destruct (@exists_compression_2 φ' HΔ) as (ψ & HΔψ & Hψ).
      exists ψ. split; first easy.
      apply CI.
      + apply II. eapply IE.
        { eapply CE1, Weak; first apply Hψ. now right. }
        eapply exists_equiv, CE1, Hφ'.
      + apply II. eapply IE with (phi := ∃∃φ'); first last.
        { eapply IE.
          - eapply CE2, Weak; first apply Hψ. now right.
          - now apply Ctx. }
        eapply Weak with (A := Qeq); last now right.
        apply II. apply exists_equiv. eapply CE2, Hφ'.
  Qed.

  Lemma Σ1_exist_times φ : Σ1 φ -> exists n ψ, Δ0 ψ /\ φ = exist_times n ψ.
  Proof.
    induction 1 as [φ H (n & ψ & HΔ & Hψ)|φ H].
    - exists (S n), ψ. now rewrite Hψ.
    - now exists 0, φ.
  Qed.
  Lemma Σ1_compression φ : Σ1 φ -> exists ψ, Δ0 ψ /\ Qeq ⊢C φ <~> ∃ψ.
  Proof.
    intros (n & ψ & HΔ & ->)%Σ1_exist_times.
    now apply exists_compression.
  Qed.


  Lemma Q_sound φ : (forall P, P \/ ~P) -> Qeq ⊢C φ -> interp_nat ⊨= φ.
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
  Lemma bounded_subst_1 φ ρ : bounded 1 φ -> φ[ρ] = φ[(ρ 0) ..].
  Proof.
    intros H. eapply bounded_subst; first eassumption.
    intros [|k]; easy + lia.
  Qed.
  Lemma bounded_subst_2 φ ρ : bounded 2 φ -> φ[ρ] = φ[ρ 0 .: (ρ 1) ..].
  Proof.
    intros H. eapply bounded_subst; first eassumption.
    intros [|[|k]]; easy + lia.
  Qed.
  Lemma bounded_subst_3 φ ρ : bounded 3 φ -> φ[ρ] = φ[ρ 0 .: ρ 1 .: (ρ 2) ..].
  Proof.
    intros H. eapply bounded_subst; first eassumption.
    intros [|[|[|k]]]; easy + lia.
  Qed.
End sigma.

Section temp.
  Existing Instance class.
  Existing Instance PA_funcs_signature.
  Existing Instance PA_preds_signature.
  Existing Instance interp_nat.

  Hypothesis Δ0_dec : forall φ, Δ0 φ -> bounded 0 φ -> Qeq ⊢ φ \/ Qeq ⊢ ¬φ.

  Lemma Δ0_soundness_consistency (Qeq' : form -> Prop) : list_theory Qeq <<= Qeq' ->
    (~ Qeq' ⊢T ⊥) <-> (forall φ, Δ0 φ -> bounded 0 φ -> (Qeq' ⊢T φ <-> interp_nat ⊨= φ)).
  Proof.
    split.
    - intros Hconsis φ HΔ0 Hb. split.
      + intros Hφ. destruct (@Δ0_dec φ); try assumption.
        * (* soundness. *) admit.
        * assert (Qeq' ⊢T ¬φ).
          { exists Qeq. split; tauto. }
          destruct Hconsis. admit.
      + intros Hφ. destruct (@Δ0_dec φ); try assumption.
        * exists Qeq. split; assumption.
        * (* soundness in H0 *) admit.
    - intros Hsound Hconsis.
      apply (Hsound ⊥).
      + constructor.
      + solve_bounds.
      + apply Hconsis.
      + intros _. exact 0.
  Admitted.
End temp.

Section Qsat_single.
  Existing Instance PA_funcs_signature.
  Existing Instance PA_preds_signature.
  Existing Instance interp_nat.

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
End Qsat_single.
Section Qtrichotomy.
  Existing Instance PA_funcs_signature.
  Existing Instance PA_preds_signature.

  (* Cannot be concrete here due to bug in Proofmode *)
  Variable (p : peirce).

  Lemma Qdec_le x : Qeq ⊢ ∀((num x ⧀= $0) ∨ ($0 ⧀= (num x))).
  Proof.
    induction x; fstart; fintro "y".
    - fleft. fexists y. 
      (*frewrite (ax_add_rec zero y).*)
      fapply ax_sym. fapply ax_add_zero.
    - (* fdestruct (ax_cases y). *)
      fassert (ax_cases); first ctx.
      fdestruct ("H" y) as "[H|[y' H]]".
      + fright. fexists (σ (num x)). 
        change (_ :: _) with Qeq.
        feapply ax_trans.
        { feapply ax_sym. fapply ax_add_zero.  }
        fapply ax_add_congr.
        * fapply ax_sym. ctx.
        * fapply ax_refl.
      + fassert (<<(∀' y, (num x ⧀= y) ∨ (y ⧀= num x)))%hoas. (* Why << and hoas? *)
        { fstop. eapply Weak.
          - cbn -[Qeq] in IHx. unfold "↑" in IHx. rewrite num_subst in IHx. eassumption.
          - now right. }
        fdestruct ("H0" y') as "[[z Hz]|[z Hz]]".
        * fleft. fexists z. 
          feapply ax_trans; first ctx.
          feapply ax_trans; first last.
          { feapply ax_sym. feapply ax_add_rec. }
          feapply ax_succ_congr. ctx.
        * fright. fexists z. 
          feapply ax_trans.
          { feapply ax_succ_congr. ctx. }
          feapply ax_trans.
          { feapply ax_sym. feapply ax_add_rec. }
          feapply ax_add_congr.
          -- fapply ax_sym. ctx.
          -- fapply ax_refl.
  Qed.
End Qtrichotomy.

Section value_disjoint.
  Existing Instance PA_funcs_signature.
  Existing Instance PA_preds_signature.

  Hypothesis Σcompleteness : forall φ rho, bounded 0 φ -> Σ1 φ -> interp_nat;rho ⊨ φ -> Qeq ⊢I φ.

  Lemma Σ1_witness φ : Σ1 φ -> bounded 1 φ -> Qeq ⊢I ∃φ -> exists x, Qeq ⊢I φ[(num x)..].
  Proof.
    intros Hb HΣ Hφ. eapply Q_sound_intu with (rho := fun _ => 0) in Hφ as [x Hx].
    exists x. eapply Σcompleteness.
    - eapply subst_bound; first eassumption.
      intros [|n] H; last lia. apply num_bound.
    - now apply Σ1_subst.
    - rewrite <-sat_single_nat. eassumption.
  Qed.

  Variable P1 P2 : nat -> Prop.
  Hypothesis P_disjoint : forall x, P1 x -> P2 x -> False.

  Variable φ1 φ2 : form.
  Hypothesis (φ1_bounded : bounded 2 φ1) (φ2_bounded : bounded 2 φ2).
  Hypothesis (φ1_Δ0 : Δ0 φ1) (φ2_Δ0 : Δ0 φ2).
  Hypothesis (φ1_dec : forall x k, Qdec (φ1[num x .: (num k) ..]))
             (φ2_dec : forall x k, Qdec (φ2[num x .: (num k) ..])).
  Hypothesis (φ1_sem : forall x rho, P1 x <-> interp_nat;rho ⊨ ∃ φ1[(num x) ..])
             (φ2_sem : forall x rho, P2 x <-> interp_nat;rho ⊨ ∃ φ2[(num x) ..]).
  Hypothesis (φ1_syn : forall x, P1 x <-> Qeq ⊢I ∃ φ1[(num x) ..])
             (φ2_syn : forall x, P2 x <-> Qeq ⊢I ∃ φ2[(num x) ..]).

  Definition φ1' := φ1 ∧ ∀ $0 ⧀= $2 ~> φ2[$1 .: $0 ..] ~> ⊥.
  Definition φ2' := φ2 ∧ ∀ $0 ⧀= $2 ~> φ1[$1 .: $0 ..] ~> ⊥.

  Lemma φ1'_bounded : bounded 2 φ1'.
  Proof.
    repeat (solve_bounds; unfold "↑"; cbn).
    - assumption.
    - eapply subst_bound; first eassumption.
      intros [|[|k]]; cbn; solve_bounds.
  Qed.
  Lemma φ2'_bounded : bounded 2 φ2'.
  Proof.
    repeat (solve_bounds; cbn; unfold "↑").
    - assumption.
    - eapply subst_bound; first eassumption.
      intros [|[|k]]; cbn; solve_bounds.
  Qed.
  Lemma φ1'_Δ0 : Δ0 φ1'.
  Proof.
    constructor; first assumption.
    change ($2) with ($1)`[↑]. repeat constructor. now apply Δ0_subst.
  Qed.
  Lemma φ2'_Δ0 : Δ0 φ2'.
  Proof.
    constructor; first assumption.
    change ($2) with ($1)`[↑]. repeat constructor. now apply Δ0_subst.
  Qed.
    

  Lemma DR1 x : P1 x -> Qeq ⊢I ∃ φ1'[(num x)..].
  Proof.
    intros HP1. apply Σcompleteness with (rho := fun _ => 0).
    { constructor. eapply subst_bound; first apply φ1'_bounded.
      intros [|[|k]] H; cbn. 2-3: solve_bounds. 
      apply num_bound. }
    { do 2 constructor. apply Δ0_subst. apply φ1'_Δ0. }
    pose proof HP1 as H. rewrite φ1_sem in H. destruct H as [k Hk].
    cbn. exists k. split.
    - eassumption.
    - intros k' _ HP2. eapply P_disjoint; first eassumption.
      eapply φ2_sem. exists k'.
      rewrite subst_comp in HP2. erewrite bounded_subst. 1-2: eassumption.
      intros [|[|n]]; cbn.
      + now rewrite num_subst.
      + reflexivity.
      + lia.
  Qed.
  Lemma DR1' x : P2 x -> Qeq ⊢I ∃ φ2'[(num x)..].
  Proof. Admitted. (* somehow deduplicate with DR1 *)

  Lemma DR2 x : P2 x -> Qeq ⊢I ¬∃ φ1'[(num x)..].
  Proof.
    intros Hx%DR1'.
    cbn -[Qeq]. unfold "↑".
    apply II. eapply ExE.
    { eapply Ctx. eauto. }
    cbn -[Qeq].
    replace (List.map (subst_form ↑) Qeq) with Qeq by reflexivity.
    rewrite subst_comp. rewrite (bounded_subst_2 _ φ2_bounded). cbn -[Qeq]. rewrite num_subst.
    eapply Weak.
    2: { instantiate (1 :=((φ1[(num x)..] ∧ (∀ (∃ $2 == $1 ⊕ $0) ~> ¬ φ2[num x .: $0..]) :: Qeq))%list).
         intros ϕ [H|H]; subst.
         - now left.
         - now do 2 right. }
    (* By Sigma1 *)
    assert (exists k, Qeq ⊢I φ2'[num x .: (num k) ..]) as [k Hk].
    { apply Σ1_witness in Hx as [k Hk].
      - exists k. rewrite subst_comp in Hk.
        erewrite subst_ext; first apply Hk.
        intros [|[|n]]; cbn; now rewrite ?num_subst.
      - apply Σ1_subst. constructor. apply φ2'_Δ0.
      - eapply subst_bound; first apply φ2'_bounded.
        intros [|[|n]] H; cbn.
        + apply num_bound.
        + constructor. lia.
        + lia. }
    cbn -[Qeq] in Hk. rewrite !num_subst in Hk. unfold "↑" in Hk.
    assert (Qeq ⊢I (num k ⧀= $0) ∨ ($0 ⧀= (num k))).
    { pose proof (AllE _ $0 _ (Qdec_le intu k)) as H.
      cbn -[Qeq] in *. rewrite !num_subst in *.
      assumption. }
    eapply DE. { eapply Weak; first apply H. intros ϕ HQ. now right. }
    - eapply IE.
      2: { eapply (AllE _ (num k)). eapply CE2. apply Ctx. right. left. reflexivity. }
      cbn -[Qeq]. unfold "↑". rewrite num_subst.
      apply II.
      eapply IE; first eapply IE.
      { apply Ctx. left. reflexivity. }
      + apply Ctx. right. left. reflexivity.
      + rewrite subst_comp, (bounded_subst_2 _ φ2_bounded).  cbn -[Qeq]. rewrite num_subst.
        eapply Weak. { eapply CE1, Hk. }
        now do 3 right.
    - eapply IE.
      2: { eapply (AllE _ $0). eapply CE2. eapply Weak; first apply Hk. intros HQ. now do 2 right. }
      cbn -[Qeq]. unfold "↑". rewrite !num_subst.
      apply II.
      eapply IE; first eapply IE.
      { apply Ctx. left. reflexivity. }
      + apply Ctx. right. left. reflexivity.
      + eapply CE1. apply Ctx. do 2 right. left.
        f_equal. rewrite !subst_comp. eapply bounded_subst.
        * apply φ1_bounded.
        * intros [|[|n]] Hn; cbn; rewrite ?num_subst; reflexivity + lia.
  Qed.
End value_disjoint.

Section value.
  Existing Instance PA_funcs_signature.
  Existing Instance PA_preds_signature.

  Existing Instance interp_nat.

  Hypothesis Σcompleteness : forall φ rho, bounded 0 φ -> Σ1 φ -> interp_nat;rho ⊨ φ -> Qeq ⊢I φ.

  Variable f : nat -> nat -> Prop.
  Hypothesis f_func : forall x y1 y2, f x y1 -> f x y2 -> y1 = y2.

  Variable T : form.
  Hypothesis T_bounded : bounded 3 T.
  Hypothesis T_Δ0 : Δ0 T.
  Hypothesis T_sem : forall ρ x y,
      f x y <-> interp_nat; ρ ⊨ ∃ T[num x .: (num y) ..].
  Hypothesis T_syn : forall  x y,
      f x y <-> Qeq ⊢I ∃ T[num x .: (num y) ..].

  Definition T' := T ∧ ∀∀ ($1⊕$0 ⧀= $3⊕$4) ~> T[$2.:$1.:$0..] ~> $1 == $3.
  Lemma T'_Δ0 : Δ0 T'.
  Proof. 
    repeat constructor; first assumption. change ($3 ⊕ $4) with ($1 ⊕ $2)`[↑]`[↑].
    constructor. change $4 with $3`[↑].
    repeat constructor. now apply Δ0_subst.
  Qed.
  Lemma T'_bounded : bounded 3 T'.
  Proof.
    repeat (solve_bounds; unfold "↑" in *; cbn in *).
    - assumption.
    - eapply subst_bound; first eassumption.
      intros [|[|[|n]]]; cbn; solve_bounds.
  Qed.

  Lemma exists_impl_comp φ ψ : Qeq ⊢I ∃ φ[↑] ~> ψ -> Qeq ⊢I (φ ~> ∃ ψ).
  Proof.
    intros H. 
    eapply ExE; first eassumption.
    change (map _ _) with Qeq. cbn -[Qeq].
    apply II. eapply ExI with (t := $0).
    replace (ψ[_][_]) with ψ[var]; first last.
    { rewrite subst_comp. apply subst_ext.
      intros [|n]; reflexivity. }
    rewrite subst_var.
    eapply IE.
    { apply Ctx. right. now left. }
    now apply Ctx.
  Qed.

  Local Lemma FR1 x y : f x y -> Qeq ⊢I ∃ T'[num x .: (num y) ..].
  Proof.
    intros Hf.
    eapply Σcompleteness.
    { constructor. eapply subst_bound; first apply T'_bounded.
      intros [|[|[|n]]] H; cbn; solve_bounds; apply num_bound. }
    { do 2 constructor. apply Δ0_subst, T'_Δ0. }
    assert (interp_nat; (fun _ => 0) ⊨ (∃ T[num x .: (num y)..])) as [k Hk].
    { apply T_sem, Hf. }
    exists k. split.
    { apply Hk. }
    cbn. 
    repeat setoid_rewrite num_subst. repeat setoid_rewrite eval_num.
    repeat setoid_rewrite iμ_standard.
    intros y' k' _.
    rewrite !subst_comp.
    do 3 rewrite sat_single_nat. rewrite !subst_comp.
    rewrite bounded_subst_3; last assumption. cbn.
    rewrite !num_subst. intros H.
    eapply f_func; last eassumption.
    eapply T_sem. exists k'. 
    rewrite sat_single_nat. rewrite !subst_comp.
    rewrite bounded_subst_3; last assumption. cbn. rewrite !num_subst.
    eassumption.
  Qed.

  Local Lemma FR2 x y : f x y -> Qeq ⊢I (∃ T'[num x .: $1 ..]) ~> $0 == num y.
  Proof.
    intros Hx%FR1.
    apply II. eapply ExE.
    { apply Ctx. now left. }
    replace _[↑] with ($1 == num y); first last.
    { cbn. repeat f_equal. now rewrite num_subst. }
    eapply Weak.
    2: { instantiate (1 := T'[num x .: $1..] :: Qeq).
         intros ϕ [H|H]; subst.
         - now left.
         - now do 2 right. }
           Check Σ1_witness.
    assert (exists k, Qeq ⊢I T'[num x .: num y .: (num k) ..]) as [k Hk].
    { admit. }
    assert (Qeq ⊢I (((num k ⊕ num y) ⧀= ($0 ⊕ $1)) ∨ (($0 ⊕ $1) ⧀= (num k ⊕ num y)))).
    { admit. }
    eapply DE. { eapply Weak; first apply H. intros ϕ HQ. now right. }
    - eapply IE.
      2: { eapply AllE with (t := $0), CE2, Ctx. right. now left. }
      apply II.
      eapply IE.
      2: { eapply AllE with (t := $1), Ctx. now left. }
      cbn -[Qeq]. unfold "↑". 
      admit.
    - admit.
  Admitted.

  Lemma FR x y : f x y -> Qeq ⊢I ∀ (∃ T'[num x .: $1 ..]) <~> $0 == num y.
  Proof.
    intros Hf.
    apply AllI. change (map _ _) with Qeq.
    apply CI.
    - apply FR2, Hf.
    - enough (Qeq ⊢I ∃ T'[num x .: (num y) ..]) by admit.
      apply FR1, Hf.
  Admitted.
End value.

Section Qinsep.
  Existing Instance PA_funcs_signature.
  Existing Instance PA_preds_signature.

  Variable theta : nat -> nat -> nat -> option bool.

  (* "fancy" version formulated with fstationary instead of ffunctional *)
  Hypothesis theta_functional : forall c, ffunctional (theta c).
  Hypothesis theta_univ : forall (f : nat -> nat -> option bool), ffunctional f ->
            exists c, forall x y, freturns f x y <-> freturns (theta c) x y.
  Arguments theta_univ : clear implicits.

  Hypothesis Qrepr : forall P, enumerable P -> exists φ,
        bounded 2 φ /\ Σ1 φ /\
          forall x, P x <-> Qeq ⊢I φ[(num x)..].

  Local Definition P y c := freturns (theta c) c y.
  Local Lemma P_enum y : enumerable (P y).
  Proof.
    apply semi_decidable_enumerable; first eauto.
    unfold semi_decidable, semi_decider.
    exists (fun c k => decide(theta c c k = Some y)).
    intros c. split.
    - intros [k Hk]. exists k. rewrite Hk. now destruct y.
    - intros [k Hk]. exists k.
      destruct (theta c c k) as [[]|], y; cbn in *; congruence.
  Qed.
  Local Lemma P_disjoint c : P true c -> P false c -> False.
  Proof.
    intros [k1 Hk1] [k2 Hk2]. now pose proof (theta_functional Hk1 Hk2).
  Qed.

  Lemma Qincomplete : exists φ, ~Qeq ⊢I φ /\ ~Qeq ⊢I ¬φ.
  Proof.
    unshelve edestruct guess_insep_expl_incompleteness as (s & Hs1 & Hs2).
    - exact theta.
    - apply Qfs_intu.
    - apply theta_univ.
    - destruct (Qrepr (P_enum true)) as (φ1 & Hb1 & Hc1).
      destruct (Qrepr (P_enum false)) as (φ2 & Hb2 & Hc2).
      unshelve eexists.
      { intros c. exact (∃ (φ1' φ1 φ2))[(num c)..]. }
      split.
      + cbn. admit.
      + admit.
    - exists s.
      split.
      + contradict Hs1. now exists Qeq.
      + contradict Hs2. now exists Qeq.
  Admitted.
End Qinsep.
Check Qincomplete.



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

Module completeness. Section completeness.
  Existing Instance PA_funcs_signature.
  Existing Instance PA_preds_signature.


  Existing Instance class.
  Existing Instance interp_nat.

  Hypothesis completeness : forall φ,
      Qeq ⊢C φ <-> forall (M : Type) (I : interp M) ρ, extensional I -> I ⊨=L Qeq -> ρ ⊨ φ.

  Lemma Qdec_absoluteness M1 M2 (I1 : interp M1) (I2 : interp M2) (QM1 : I1 ⊨=L Qeq) (Mext1 : extensional I1) (QM2 : I2 ⊨=L Qeq) (Mext2 : extensional I2) ρ1 ρ2 φ :
    Qdec φ -> I1; ρ1 ⊨ φ -> I2; ρ2 ⊨ φ.
  Proof.
    intros [Hφ|Hφ] HI1; rewrite completeness in Hφ.
    - now apply Hφ.
    - contradict HI1. now apply Hφ.
  Qed.
  Lemma Qdec_absoluteness_nat M (I : interp M) (QM : I ⊨=L Qeq) (Mext : extensional I) ρN ρM φ :
    Qdec φ -> interp_nat; ρN ⊨ φ <-> I; ρM ⊨ φ.
  Proof.
    intros Qdec. split; intros H.
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


    Definition φ1' := φ1 ∧ ∀ $0 ⧀ $2 ~> φ2[$1 .: $0 ..] ~> ⊥.
    Definition φ2' := φ2 ∧ ∀ $0 ⧀ $2 ~> φ1[$1 .: $0 ..] ~> ⊥.

    (* Lemma φ1_bounded_subst ρ : φ1[ρ] = φ1[ρ 0 .: (ρ 1) ..]. *)
    (* Proof. *)
    (*   eapply bounded_subst; first apply φ1_bounded. intros [|[|k]]; easy + lia. *)
    (* Qed. *)
    (* Lemma φ2_bounded_subst ρ : φ2[ρ] = φ2[ρ 0 .: (ρ 1) ..]. *)
    (* Proof. *)
    (*   eapply bounded_subst; first apply φ2_bounded. intros [|[|k]]; easy + lia. *)
    (* Qed. *)

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
      - cbn. intros k' [d Hd] H2.

        assert (standard k') as [k'' <-].
        { unshelve eapply standard_le; try auto. exists d. now apply Mext. }

        rewrite !sat_single_PA, !subst_comp, bounded_subst_2 in H2; last assumption. cbn in H2.
        rewrite !num_subst in H2.

        enough (P2 x) by (eapply P_disjoint; eassumption).
        eapply φ2_sem' with (ρ := fun _ => 0). exists k''. eapply Qdec_absoluteness_nat; eauto.
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

        rewrite sat_single_PA in Hk1. rewrite !subst_comp, bounded_subst_2 in Hk1; last assumption. cbn in Hk1.
        rewrite num_subst in Hk1.

        enough (P1 x) by (eapply P_disjoint; eassumption).
        eapply φ1_sem' with (ρ := (fun _ => 0)). exists k'. eapply Qdec_absoluteness_nat; eauto.
      - rewrite sat_single_PA, !subst_comp, bounded_subst_2; last assumption. cbn.
        rewrite !num_subst. eapply Qdec_absoluteness_nat; eauto.
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
      - apply T_single_rho_model. now eapply Qdec_absoluteness_nat; eauto.
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
        eapply Qdec_absoluteness_nat with (ρN := fun _ => 0) in HT; try eauto.

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
          eapply Qdec_absoluteness_nat; eauto. rewrite <-T_single_rho_model.
          apply Hk1.
      - rewrite !num_subst, eval_num, Mext. contradict Hy. now eapply iμ_inj.
      - rewrite !sat_single_PA, !subst_comp, subst_T_bound. cbn. rewrite !num_subst.
        eapply Qdec_absoluteness_nat; eauto.
    Qed.
  End value.
End completeness. End completeness.
Section value.
  Existing Instance PA_funcs_signature.
  Existing Instance PA_preds_signature.

  Existing Instance interp_nat.

  Hypothesis LEM : forall P, P \/ ~P.

  Hypothesis Σcompleteness : forall φ, bounded 0 φ -> Σ1 φ -> interp_nat ⊨= φ -> Qeq ⊢C φ.


  Lemma completeness_equiv φ1 φ2 :
    bounded 0 φ2 -> Σ1 φ2 -> Qeq ⊢C φ1 <~> φ2 -> interp_nat ⊨= φ1 -> Qeq ⊢C φ1.
  Proof.
    intros Hb Hs Hequiv Hnat.
    enough (Qeq ⊢C φ2) as H.
    { eapply IE; last exact H.
      eapply CE2. apply Hequiv. }
    apply Σcompleteness; try assumption.
    intros rho.
    eapply Q_sound in Hequiv; last assumption.
    cbn in Hequiv.
    apply Hequiv, Hnat.
  Qed.


  Lemma PNF_conj φ1 φ2 : Π1 φ1 -> Π1 φ2 -> exists ψ, Π1 ψ /\ Qeq ⊢C φ1 ∧ φ2 <~> ψ.
  Proof.
  Admitted.
  Lemma PNF_impl φ1 φ2 : Π1 φ1 -> Σ1 φ2 -> exists ψ, Σ1 ψ /\ Qeq ⊢C (φ1 ~> φ2) <~> ψ.
  Proof. Admitted.


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
    (* TODO had to add closedness condition here *)
    (*intros rho Hψ1.

    eapply Q_sound with (rho := rho) in Hc1 as [Hc1 Hc1']; last assumption.
    cbn in Hc1'. destruct (Hc1' Hψ1) as [H1 H2].
    eapply ϕΠ_R_completeness in H1. eapply ϕΠ_R_completeness in H2.
    unfold R in H1, H2.

    cbn. rewrite !eval_num.
    congruence.*)
  (*Qed.*) Abort.

  Lemma VR_total x y : f x = y -> Qeq ⊢C ϕΠ' x y /\ forall y', y <> y' -> Qeq ⊢C ¬ϕΠ' x y'.
  Proof.
    intros Hf%ϕΠ_R. split; first assumption.
    intros y' Hy.

    apply II.
    eapply IE with (phi := num y == num y').
    { apply Weak with (A := Qeq); last auto.
      (* TODO as above *)
      (*apply Σcompleteness; first assumption.
      - repeat constructor.
      - intros ρ. cbn. rewrite !eval_num. apply Hy.
    }
    eapply IE.
    { eapply Weak with (A := Qeq); last auto. apply CT_functional. }
    eapply CI.
    - eapply Weak with (A := Qeq); eauto.
    - apply Ctx. auto.
  Qed.*) Abort.

End value.
