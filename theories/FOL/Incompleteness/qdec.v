(* TODO deduplicate imports *)
From Undecidability.FOL.Incompleteness Require Import utils.
From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
From Undecidability.Shared Require Import Dec embed_nat.

From Undecidability.FOL.Util Require Import Syntax_facts FullDeduction FullDeduction_facts FullTarski FullTarski_facts Axiomatisations FA_facts Syntax.
From Undecidability.FOL Require Import PA.

From Equations Require Import Equations.
From Undecidability.FOL.Proofmode Require Import Theories ProofMode Hoas.
From Undecidability.FOL.Incompleteness Require Import fol.

Require Import Setoid.

Require Import Undecidability.Shared.Libs.DLW.Vec.vec.

Require Import String.
Open Scope string_scope.

(** ** Arithmetical hierarchy *)
(** *** Q-decidability *)
Section Qdec.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.

  Context {p : peirce}.

  Definition Qdec φ := forall ρ, bounded 0 φ[ρ] -> Qeq ⊢ φ[ρ] \/ Qeq ⊢ ¬φ[ρ].

  Lemma Qdec_subst φ ρ : Qdec φ -> Qdec φ[ρ].
  Proof.
    intros H ρ' Hb. rewrite subst_comp. apply H.
    rewrite <-subst_comp. apply Hb.
  Qed.

  Lemma Qdec_bot : Qdec ⊥.
  Proof.
    intros ρ Hb. right. fintros. ctx.
  Qed.

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
  Lemma Qdec_eq t s : Qdec (t == s).
  Proof.
    intros ρ. cbn. invert_bounds. 
    destruct (@closed_term_is_num _ t`[ρ]) as [k1 Hk1].
    { apply H3. left. }
    destruct (@closed_term_is_num _ s`[ρ]) as [k2 Hk2].
    { apply H3. right. left. }
    assert (k1 = k2 \/ k1 <> k2) as [->|Hk] by lia; [left|right].
    all: frewrite Hk1; frewrite Hk2.
    - fapply ax_refl.
    - clear Hk1. clear Hk2. revert Hk. induction k1 in k2 |-*; intros Hk.
      + destruct k2; first congruence. cbn.
        fapply ax_zero_succ.
      + cbn. destruct k2.
        * fintros. fapply (ax_zero_succ (num k1)). fapply ax_sym. ctx.
        * cbn. fintros. assert (H' : k1 <> k2) by congruence.
          specialize (IHk1 k2 H'). fapply IHk1.
          fapply ax_succ_inj. ctx.
  Qed.



  Lemma Q_leibniz_t a x y : Qeq ⊢ x == y ~> a`[x..] == a`[y..].
  Proof.
    induction a.
    - destruct x0; cbn.
      + fintros. ctx.
      + fintros. fapply ax_refl.
    - destruct F.
      + cbn in v. rewrite (vec_0_nil v).
        fintros. fapply ax_refl.
      + cbn in v. 
        destruct (vec_1_inv v) as [z ->]. cbn.
        fintros. fapply (ax_succ_congr z`[y..] z`[x..]).
        frevert 0. fapply IH. apply Vector.In_cons_hd.
      + destruct (vec_2_inv v) as (a & b & ->).
        cbn. fintros. fapply ax_add_congr.
        all: frevert 0; fapply IH.
        * apply Vector.In_cons_hd.
        * apply Vector.In_cons_tl, Vector.In_cons_hd.
      + destruct (vec_2_inv v) as (a & b & ->).
        cbn. fintros. fapply ax_mult_congr.
        all: frevert 0; fapply IH.
        * apply Vector.In_cons_hd.
        * apply Vector.In_cons_tl, Vector.In_cons_hd.
  Qed.
  Lemma subst_up φ t1 t2 :
    φ[up t1..][t2..] = φ[t2`[↑]..][t1..].
  Proof.
    rewrite !subst_comp. apply subst_ext. intros [|[|n]]; cbn.
    + now rewrite subst_term_shift.
    + now rewrite subst_term_shift.
    + reflexivity.
  Qed.

  Lemma Q_leibniz φ x y : 
    Qeq ⊢ x == y ~> φ[x..] ~> φ[y..].
  Proof. 
    enough (Qeq ⊢ x == y ~> φ[x..] <~> φ[y..]).
    { fintros. fapply H; ctx. }
    induction φ using form_ind_subst.
    - cbn. fintros. fsplit; fintros; ctx. 
    - destruct P0. cbn in t. 
      destruct (vec_2_inv t) as (a & b & ->).
      cbn. fstart. fintros.
      fassert (a`[x..] == a`[y..]).
      { pose proof (Q_leibniz_t a x y).
        fapply H. fapply "H". }
      fassert (b`[x..] == b`[y..]).
      { pose proof (Q_leibniz_t b x y).
        fapply H. fapply "H". }
      frewrite "H0". frewrite "H1".
      fsplit; fintros; ctx.
    - fstart; fintros.
      fassert (φ1[x..] <~> φ1[y..]) by (fapply IHφ1; fapply "H").
      fassert (φ2[x..] <~> φ2[y..]) by (fapply IHφ2; fapply "H").
      destruct b0; fsplit; cbn.
      + fintros "[H2 H3]". fsplit.
        * fapply "H0". ctx.
        * fapply "H1". ctx.
      + fintros "[H2 H3]". fsplit.
        * fapply "H0". ctx.
        * fapply "H1". ctx.
      + fintros "[H2|H3]".
        * fleft. fapply "H0". ctx.
        * fright. fapply "H1". ctx.
      + fintros "[H2|H3]".
        * fleft. fapply "H0". ctx.
        * fright. fapply "H1". ctx.
      + fintros "H2" "H3". 
        fapply "H1". fapply "H2". fapply "H0". ctx.
      + fintros "H2" "H3". 
        fapply "H1". fapply "H2". fapply "H0". ctx.
    - fstart. fintros. fsplit; destruct q; cbn; fintros.
      + specialize (H (x0`[↑]..)). rewrite subst_up. fapply H.
        * ctx.
        * fspecialize ("H0" x0). rewrite subst_up. ctx.
      + fdestruct "H0". fexists x0. rewrite !subst_up.
        specialize (H (x0`[↑]..)). fapply H; ctx.
      + specialize (H (x0`[↑]..)). rewrite subst_up. fapply H.
        * ctx.
        * fspecialize ("H0" x0). rewrite subst_up. ctx.
      + fdestruct "H0". fexists x0. rewrite !subst_up.
        specialize (H (x0`[↑]..)). fapply H; ctx.
  Qed.


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
    - fassert (ax_cases); first ctx.
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
  Proof. 
    induction t; fstart; fintros y x "H".
    - fassert ax_cases as "C"; first ctx.
      fdestruct ("C" x) as "[Hx|[x' Hx']]".
      + frewrite "Hx". frewrite (ax_add_zero y).
        fapply ax_succ_inj. frewrite <-(ax_add_zero (σ y)).
        frewrite <-"H". frewrite "Hx". fapply ax_refl.
      + frewrite "Hx'". fassert ax_cases as "C"; first ctx.
        fdestruct ("C" x') as "[Hx''|[x'' Hx'']]".
        * fexfalso. fapply (ax_zero_succ y). 
          fapply ax_succ_inj. frewrite <-"H".
          frewrite "Hx'". frewrite "Hx''".
          frewrite (ax_add_rec (σ y) zero). frewrite (ax_add_zero (σ y)).
          fapply ax_refl.
        * fexfalso. fapply (ax_zero_succ (x'' ⊕ σ y)). 
          fapply ax_succ_inj. frewrite <-"H".
          frewrite "Hx'". frewrite "Hx''".
          frewrite (ax_add_rec (σ y) (σ x'')).
          frewrite (ax_add_rec (σ y) x''). fapply ax_refl.
    - fassert ax_cases as "C"; first ctx.
      fdestruct ("C" x) as "[Hx'|[x' Hx']]".
      + fapply ax_succ_inj. frewrite <-"H".
        frewrite "Hx'". frewrite (ax_add_zero y).
        frewrite (ax_add_zero (σ y)). fapply ax_refl.
      + frewrite "Hx'". frewrite (ax_add_rec y x').
        fapply ax_succ_congr. fspecialize (IHt y x').
        rewrite !num_subst in IHt. fapply IHt.
        fapply ax_succ_inj. frewrite <-(ax_add_rec (σ y) x').
        frewrite <-"Hx'". ctx.
  Qed.

  Lemma pless_zero_eq : Qeq ⊢ ∀ ($0 ⧀= zero) ~> $0 == zero.
  Proof.
    rewrite !pless_eq.
    fstart. fintros. fdestruct "H".
    fassert ax_cases.
    { ctx. }
    unfold ax_cases.
    fdestruct ("H0" x).
    - fapply "H0".
    - fdestruct "H0".
      fexfalso. fapply (ax_zero_succ (x1 ⊕ x0)).
      frewrite <- (ax_add_rec x0 x1). frewrite <- "H0".
      fapply "H".
  Qed.
  Lemma pless_swap_zero_eq : Qeq ⊢ ∀ ($0 ⧀=comm zero) ~> $0 == zero.
  Proof.
    rewrite !pless_swap_eq. 
    fstart. fintros. fdestruct "H".
    fassert ax_cases as "C"; first ctx.
    fdestruct ("C" x0) as "[Hx'|[x' Hx']]".
    - frewrite <-(ax_add_zero x). frewrite <-"Hx'".
      frewrite <-"H". frewrite "Hx'". fapply ax_refl.
    - fexfalso. fapply (ax_zero_succ (x' ⊕ x)).
      frewrite <-(ax_add_rec x x'). frewrite <-"Hx'".
      fapply "H".
  Qed.


  Lemma add_rec_swap2 t :
    Qeq ⊢ ∀∀ $0 ⊕ $1 == num t ~> $0 ⊕ (σ $1) == num (S t).
  Proof.
    induction t; fstart; fintros z x "H".
    - fassert ax_cases as "C"; first ctx. 
      fdestruct ("C" x) as "[Hx'|[x' Hx']]".
      + frewrite <-"H". frewrite "Hx'". 
        frewrite (ax_add_zero (σ z)). frewrite (ax_add_zero z).
        fapply ax_refl.
      + fexfalso. fapply (ax_zero_succ (x' ⊕ z)). frewrite <-"H".
        frewrite "Hx'". frewrite (ax_add_rec z x'). fapply ax_refl.
    - fassert ax_cases as "C"; first ctx. 
      fdestruct ("C" x) as "[Hx'|[x' Hx']]".
      + frewrite <-"H". frewrite "Hx'".
        frewrite (ax_add_zero (σ z)). frewrite (ax_add_zero z).
        fapply ax_refl.
      + frewrite "Hx'". frewrite (ax_add_rec (σ z) x').
        fapply ax_succ_congr.
        fspecialize (IHt z x'). rewrite !num_subst in IHt.
        fapply IHt. fapply ax_succ_inj.
        frewrite <-(ax_add_rec z x'). frewrite <-"Hx'".
        fapply "H".
  Qed.



  Lemma pless_succ t : Qeq ⊢ ∀ ($0 ⧀= num t) ~> ($0 ⧀= σ (num t)).
  Proof. 
    rewrite !pless_eq, !num_subst.
    fstart. fintros x "[z Hz]". fexists (σ z).
    pose proof (add_rec_swap2 t) as Hars.
    fspecialize (Hars z x). rewrite !num_subst in Hars.
    fapply ax_sym. fapply Hars. fapply ax_sym. fapply "Hz".
  Qed.
  Lemma pless_swap_succ t : Qeq ⊢ ∀ ($0 ⧀=comm num t) ~> ($0 ⧀=comm σ (num t)).
  Proof. 
    rewrite !pless_swap_eq, !num_subst.
    fstart. fintros x "[z Hz]". fexists (σ z).
    frewrite (ax_add_rec x z). fapply ax_succ_congr. ctx.
  Qed.
  Lemma pless_swap_sym t : Qeq ⊢ num t ⧀=comm num t.
  Proof.
    rewrite !pless_swap_eq.
    fexists zero. fapply ax_sym. fapply ax_add_zero.
  Qed.
  Lemma pless_sym t : Qeq ⊢ num t ⧀= num t.
  Proof.
    rewrite !pless_eq.
    fexists zero. fapply ax_sym. apply add_zero_num.
  Qed.

  Lemma pless_swap_sigma_neq t : Qeq ⊢ ∀ ($0 ⧀=comm σ(num t)) ~> ¬($0 == σ(num t)) ~> $0 ⧀=comm num t.
  Proof. 
    fstart. fintros. fdestruct "H" as "[z Hz]".
    fassert ax_cases as "C"; first ctx.
    fdestruct ("C" z) as "[Hz'|[z' Hz']]".
    - fexfalso. fapply "H0". frewrite "Hz". frewrite "Hz'".
      fapply ax_sym. fapply ax_add_zero.
    - fexists z'. fapply ax_succ_inj.
      frewrite <-(ax_add_rec x z').
      frewrite <-"Hz'". ctx.
  Qed. 
  Lemma pless_sigma_neq t : Qeq ⊢ ∀ ($0 ⧀= σ(num t)) ~> ¬($0 == σ(num t)) ~> $0 ⧀= num t.
  Proof. 
    rewrite !pless_eq. 
    fstart. fintros. fdestruct "H". custom_simpl.
    fassert (ax_cases); first ctx.
    fdestruct ("H1" x0).
    - fexfalso. fapply "H0". 
      pose proof (add_zero_swap (S t)). cbn in H.
      fspecialize (H x). rewrite !num_subst in H.
      fapply H. frewrite <- "H1". fapply ax_sym.
      ctx.
    - fdestruct "H1". fexists x1. custom_simpl.
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
    - fassert (ax_cases); first ctx.
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
        fassert (x == σ (num t) ∨ ¬(x == σ (num t))).
        { pose proof (Q_eqdec (S t)). cbn in H.
          fspecialize (H x). rewrite !num_subst in H.
          fapply H. }
        fdestruct "H2".
        * feapply Q_leibniz.
          -- feapply ax_sym. fapply "H2".
          -- fapply "H1".
        * fdestruct IHt. fapply "H4"; first fapply "H".
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
      + fintros. do 2 fdestruct "H". 
        fassert (x == zero).
        { fapply pless_zero_eq. rewrite pless_subst. cbn.
          fapply "H". }
        feapply Q_leibniz; ctx.
      + fintros. fexists zero. fsplit.
        * pose proof (pless_sym 0). cbn in H.
          fapply H.
        * ctx.
    - fsplit.
      + fintros. do 2 fdestruct "H". 
        fassert (x == σ (num t) ∨ ¬(x == σ (num t))).
        { pose proof (Q_eqdec (S t)). cbn in H.
          fspecialize (H x). rewrite num_subst in H.
          fapply H. }
        fdestruct "H1".
        * fright. feapply Q_leibniz; ctx.
        * fleft. fapply IHt. fexists x. fsplit; last ctx.
          pose proof (pless_sigma_neq t).
          fspecialize (H x). rewrite !pless_subst in H. cbn in H.
          rewrite num_subst in H.
          fapply H; ctx.
      + fintros. fdestruct "H".
        * fapply IHt in "H". fdestruct "H". fexists x. fdestruct "H".
          fsplit; last ctx.
          pose proof (pless_succ t). fspecialize (H x).
          rewrite !pless_subst in H. cbn in H. rewrite num_subst in H.
          fapply H. ctx.
        * fexists (σ num t). 
          fsplit; last ctx.
          pose proof (pless_sym (S t)). cbn in H. fapply H.
  Qed.

  Lemma bounded_exist_swap_disj φ t :
    Qeq ⊢ (∃ ($0 ⧀=comm (num t)) ∧ φ) <~> fin_disj t φ.
  Proof.
    cbn. induction t; fstart; cbn.
    - fsplit.
      + fintros. do 2 fdestruct "H". 
        fassert (x == zero).
        { fapply pless_swap_zero_eq. rewrite pless_swap_subst. cbn.
          fapply "H". }
        feapply Q_leibniz; ctx.
      + fintros. fexists zero. fsplit.
        * pose proof (pless_swap_sym 0). cbn in H.
          fapply H.
        * ctx.
    - fsplit.
      + fintros. do 2 fdestruct "H". 
        fassert (x == σ (num t) ∨ ¬(x == σ (num t))).
        { pose proof (Q_eqdec (S t)). cbn in H.
          fspecialize (H x). rewrite num_subst in H.
          fapply H. }
        fdestruct "H1".
        * fright. feapply Q_leibniz; ctx.
        * fleft. fapply IHt. fexists x. fsplit; last ctx.
          pose proof (pless_swap_sigma_neq t).
          fspecialize (H x). rewrite !pless_swap_subst in H. cbn in H.
          rewrite !pless_swap_subst. cbn.
          rewrite num_subst in *.
          fapply H; ctx.
      + fintros. fdestruct "H".
        * fapply IHt in "H". fdestruct "H". fexists x. rewrite !pless_swap_subst. cbn.
          rewrite !num_subst.
          fdestruct "H".
          fsplit; last ctx.
          pose proof (pless_swap_succ t). fspecialize (H x).
          rewrite !pless_swap_subst in H. cbn in H. rewrite num_subst in H.
          fapply H. ctx.
        * fexists (σ num t). 
          fsplit; last ctx.
          rewrite pless_swap_subst. cbn. rewrite num_subst.
          pose proof (pless_swap_sym (S t)). cbn in H. fapply H.
  Qed.
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
  Lemma bounded_t_0 t ρ :
    bounded_t 0 t -> t`[ρ] = t.
  Proof.
    intros Hb. rewrite <-subst_term_var.
    eapply bounded_subst_t; last eassumption.
    lia.
  Qed.


  Lemma subst_up2 φ t ρ : bounded_t 0 t -> φ[t..][ρ] = φ[up ρ][t..].
  Proof.
    intros Hb. rewrite !subst_comp. apply subst_ext.
    intros [|n]; cbn; unfold "↑";cbn.
    - now apply bounded_t_0. 
    - rewrite !subst_term_comp. rewrite <-subst_term_var at 1.
      apply subst_term_ext. intros [|n']; reflexivity.
  Qed.

  Lemma fin_conj_subst n φ ρ :
    (fin_conj n φ)[ρ] = fin_conj n φ[up ρ].
  Proof.
    induction n; cbn.
    - apply subst_up2. solve_bounds.
    - cbn. f_equal; first assumption.
      apply subst_up2. solve_bounds. apply num_bound.
  Qed.
  Lemma fin_conj_bound n φ :
    bounded 1 φ -> bounded 0 (fin_conj n φ).
  Proof.
    intros Hb. induction n; cbn.
    - eapply subst_bound; last eassumption.
      intros [|n]; solve_bounds.
    - cbn. constructor; first assumption.
      eapply subst_bound; last eassumption.
      intros [|n'] Hn; last lia. apply (num_bound (S n)).
  Qed.

  (* NOTE: this lemma could be strengthened to allow arbitrary terms t`[↑] in
   * place of $(S t). Unfortunately this leads to horrible substitution lemmas 
   * and boundedness inversions. *)
  Lemma Qdec_bounded_forall t φ :
    Qdec φ -> Qdec (∀ $0 ⧀= $(S t) ~> φ).
  Proof.
    intros HQdec ρ Hb. cbn. rewrite pless_subst. cbn.
    assert (bounded_t 0 (ρ t)) as Hbt.
    { cbn in Hb. rewrite pless_subst in Hb.
      inversion Hb. subst.
      apply Eqdep_dec.inj_pair2_eq_dec in H3; try decide equality. subst.
      inversion H2. subst.
      apply Eqdep_dec.inj_pair2_eq_dec in H0; try decide equality. subst.
      apply pless_invert_bound in H4 as [_ H].
      apply up_invert_bound_t. apply H. }

    destruct (closed_term_is_num Hbt) as [n Hn].

    assert (bounded 1 φ[up ρ]) as Hbφ.
    { cbn in Hb.
      inversion Hb. subst.
      apply Eqdep_dec.inj_pair2_eq_dec in H3; try decide equality. subst.
      inversion H2. subst.
      apply Eqdep_dec.inj_pair2_eq_dec in H5; try decide equality. now subst. }

    pose proof (bounded_forall_conj (φ[up ρ]) n) as H.
    destruct (@Qdec_fin_conj _ n HQdec ρ) as [Hf|Hf].
    { rewrite fin_conj_subst. now apply fin_conj_bound. }
    - left. rewrite fin_conj_subst in Hf.
      fstart. 
      fassert (∀ $0 ⧀= num n ~> φ[up ρ]).
      { fapply H. fapply Hf. }
      fintros. 
      rewrite !pless_eq. cbn. 
      do 3 try rewrite bounded_t_0; try assumption.
      rewrite num_subst. unfold "↑".
      fapply "H". fdestruct "H0". fexists x0.
      rewrite bounded_t_0; last assumption. frewrite <-"H0".
      fapply ax_sym. fapply Hn.
    - right. rewrite fin_conj_subst in Hf.
      fstart. fintros. fapply Hf.
      fapply H. 
      fintros. fapply "H".
      rewrite !pless_eq. fdestruct "H0".
      fexists x0. frewrite <-"H0". fapply Hn.
  Qed.

  Lemma fin_disj_subst n φ ρ :
    (fin_disj n φ)[ρ] = fin_disj n φ[up ρ].
  Proof.
    induction n; cbn.
    - apply subst_up2. solve_bounds.
    - cbn. f_equal; first assumption.
      apply subst_up2. solve_bounds. apply num_bound.
  Qed.
  Lemma fin_disj_bound n φ :
    bounded 1 φ -> bounded 0 (fin_disj n φ).
  Proof.
    intros Hb. induction n; cbn.
    - eapply subst_bound; last eassumption.
      intros [|n]; solve_bounds.
    - cbn. constructor; first assumption.
      eapply subst_bound; last eassumption.
      intros [|n'] Hn; last lia. apply (num_bound (S n)).
  Qed.

  Lemma Qdec_bounded_exists t φ :
    Qdec φ -> Qdec (∃ ($0 ⧀= $(S t)) ∧ φ).
  Proof.
    intros HQdec ρ Hb. cbn. rewrite pless_subst. cbn.
    assert (bounded_t 0 (ρ t)) as Hbt.
    { cbn in Hb. rewrite pless_subst in Hb.
      inversion Hb. subst.
      apply Eqdep_dec.inj_pair2_eq_dec in H3; try decide equality. subst.
      inversion H2. subst.
      apply Eqdep_dec.inj_pair2_eq_dec in H0; try decide equality. subst.
      apply pless_invert_bound in H4 as [_ H].
      apply up_invert_bound_t. apply H. }

    destruct (closed_term_is_num Hbt) as [n Hn].

    assert (bounded 1 φ[up ρ]) as Hbφ.
    { cbn in Hb.
      inversion Hb. subst.
      apply Eqdep_dec.inj_pair2_eq_dec in H3; try decide equality. subst.
      inversion H2. subst.
      apply Eqdep_dec.inj_pair2_eq_dec in H5; try decide equality. now subst. }

    pose proof (bounded_exist_disj (φ[up ρ]) n) as H.
    destruct (@Qdec_fin_disj _ n HQdec ρ) as [Hf|Hf].
    { rewrite fin_disj_subst. now apply fin_disj_bound. }
    - left. rewrite fin_disj_subst in Hf.
      fstart. 
      fassert (∃ ($0 ⧀= num n) ∧ φ[up ρ]).
      { fapply H. fapply Hf. }
      fdestruct "H". fdestruct "H".
      fexists x. fsplit; last ctx.
      rewrite !pless_eq. cbn. 
      fdestruct "H". fexists x0.
      frewrite Hn. fapply "H".
    - right. rewrite fin_disj_subst in Hf.
      fstart. fintros. fdestruct "H". fdestruct "H".
      fapply Hf. fapply H.
      fexists x. fstart. fsplit; last ctx.
      rewrite !pless_eq. cbn. fdestruct "H".
      fexists x0. frewrite <-"H". fapply ax_sym. fapply Hn.
  Qed.
  Lemma Qdec_bounded_exists_comm t φ :
    Qdec φ -> Qdec (∃ ($0 ⧀=comm $(S t)) ∧ φ).
  Proof.
    intros HQdec ρ Hb. cbn. rewrite pless_swap_subst. cbn.
    assert (bounded_t 0 (ρ t)) as Hbt.
    { cbn in Hb. rewrite pless_swap_subst in Hb.
      inversion Hb. subst.
      apply Eqdep_dec.inj_pair2_eq_dec in H3; try decide equality. subst.
      inversion H2. subst.
      apply Eqdep_dec.inj_pair2_eq_dec in H0; try decide equality. subst.
      apply pless_swap_invert_bound in H4 as [_ H].
      apply up_invert_bound_t. apply H. }

    destruct (closed_term_is_num Hbt) as [n Hn].

    assert (bounded 1 φ[up ρ]) as Hbφ.
    { cbn in Hb.
      inversion Hb. subst.
      apply Eqdep_dec.inj_pair2_eq_dec in H3; try decide equality. subst.
      inversion H2. subst.
      apply Eqdep_dec.inj_pair2_eq_dec in H5; try decide equality. now subst. }

    pose proof (bounded_exist_swap_disj (φ[up ρ]) n) as H.
    destruct (@Qdec_fin_disj _ n HQdec ρ) as [Hf|Hf].
    { rewrite fin_disj_subst. now apply fin_disj_bound. }
    - left. rewrite fin_disj_subst in Hf.
      fstart. 
      fassert (∃ ($0 ⧀=comm num n) ∧ φ[up ρ]).
      { fapply H. fapply Hf. }
      fdestruct "H". fdestruct "H".
      fexists x. fsplit; last ctx.
      rewrite !pless_swap_eq. cbn. 
      fdestruct "H". fexists x0.
      frewrite Hn. fapply "H".
    - right. rewrite fin_disj_subst in Hf.
      fstart. fintros. fdestruct "H". fdestruct "H".
      fapply Hf. fapply H.
      fexists x. fsplit; last ctx.
      rewrite !pless_swap_eq. cbn. fdestruct "H".
      fexists x0. frewrite <-"H". fapply ax_sym. fapply Hn.
  Qed.

  
End Qdec.

(** *** Sigma1 completeness *)

Section Sigma1.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.

  Context {p : peirce}.



  Inductive Σ1 : form -> Prop :=
  | Sigma_exists : forall α, Σ1 α -> Σ1 (∃ α)
  | Sigma_Delta : forall α, Qdec α -> Σ1 α.
  Inductive Π1 : form -> Prop :=
  | Pi_forall : forall α, Π1 α -> Π1 (∀ α)
  | Pi_Delta : forall α, Qdec α -> Π1 α.

  Lemma Σ1_subst φ ρ : Σ1 φ -> Σ1 φ[ρ].
  Proof.
    induction 1 as [α H IH | α H] in ρ |-*.
    - cbn. constructor. apply IH.
    - constructor. apply Qdec_subst, H.
  Qed.
  Lemma Π1_subst φ ρ : Π1 φ -> Π1 φ[ρ].
  Proof.
    induction 1 as [α H IH | α H] in ρ |-*.
    - cbn. constructor. apply IH.
    - constructor. apply Qdec_subst, H.
  Qed.

  Lemma exist_times_Σ1 n φ :
    Σ1 φ -> Σ1 (exist_times n φ).
  Proof.
    intros H. induction n.
    - easy.
    - now constructor.
  Qed.


  Lemma exists_compression_2 φ n : Qdec φ -> bounded (S (S n)) φ -> exists ψ, Qdec ψ /\ bounded (S n) ψ /\ Qeq ⊢ (∃∃φ) <~> (∃ψ).
  Proof.
    intros HQ Hb.
    exists (∃ ($0 ⧀= $1) ∧ ∃ ($0 ⧀=comm $2) ∧ φ[up (up (S >> var))]).
    repeat split.
    { apply (@Qdec_bounded_exists _ 0), (@Qdec_bounded_exists_comm _ 1).
      apply Qdec_subst, HQ. }
    { constructor. constructor.
      { rewrite pless_eq. 
        eapply (@bounded_up _ _ _ _ 2); last lia.
        repeat solve_bounds. }
      constructor. constructor.
      { eapply (@bounded_up _ _ _ _ 3); last lia.
        rewrite pless_swap_eq.
        constructor. repeat solve_bounds. }
      eapply subst_bound; last eassumption.
      intros n' H'.
      destruct n' as [|[|n']]; cbn; unfold "↑"; cbn; constructor; lia. }
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
      + now intros [|[|[|k]]]; cbn.
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
      apply subst_ext. now intros [|[|[|k]]].
  Qed.

  Lemma exists_equiv φ ψ : Qeq ⊢ φ ~> ψ -> (∃φ :: Qeq) ⊢ (∃ψ).
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

  Lemma exists_compression φ k n : bounded (n + k) φ -> Qdec φ ->
    exists ψ, Qdec ψ /\ bounded (S k) ψ /\ Qeq ⊢ exist_times n φ <~> ∃ ψ.
  Proof.
    intros Hb HQ. revert Hb. induction n as [|n IH] in k |-*.
    2: destruct n. all: cbn.
    all: intros Hb.
    - exists φ[↑]. repeat split.
      { now apply Qdec_subst. }
      { eapply subst_bound; last apply Hb. intros n H. constructor. lia. }
      apply CI.
      + apply II. fexists $0. apply Ctx. now left.
      + apply II. eapply ExE; first (apply Ctx; now left).
        apply Ctx. now left.
    - exists φ. repeat split.
      + assumption.
      + cbn. replace (k - 0) with k by lia. assumption.
      + fsplit; fintros; ctx.
    - destruct (IH (S k)) as (ψ & HQ' & Hb' & H). 
      { now replace (S n + S k) with (S (S n) + k) by lia. }
      edestruct (@exists_compression_2 ψ) as (ψ' & HΔψ & Hbψ' & Hψ).
      1-2: eassumption.
      exists ψ'. repeat split; try easy.  cbn in H.
      apply CI.
      + apply II. eapply IE.
        { eapply CE1, Weak; first apply Hψ. now right. }
        eapply exists_equiv, CE1. eassumption.
      + apply II. eapply IE with (phi := ∃∃ψ); first last.
        { eapply IE.
          - eapply CE2, Weak; first apply Hψ. now right.
          - now apply Ctx. }
        eapply Weak with (A := Qeq); last now right.
        apply II. apply exists_equiv. eapply CE2. eassumption.
  Qed.

  Lemma Σ1_exist_times φ : Σ1 φ -> exists n ψ, Qdec ψ /\ φ = exist_times n ψ.
  Proof.
    induction 1 as [φ H (n & ψ & HΔ & Hψ)|φ H].
    - exists (S n), ψ. now rewrite Hψ.
    - now exists 0, φ.
  Qed.
  Lemma bounded_exist_times φ n k : bounded (n + k) φ <-> bounded k (exist_times n φ).
  Proof.
    induction n in k |-*; split.
    - easy.
    - easy.
    - cbn. intros H. constructor. apply IHn. replace (n + S k) with (S n + k) by lia. apply H.
    - cbn. invert_bounds. replace (S (n + k)) with (n + (S k)) by lia. now apply IHn. 
  Qed.

  Lemma Σ1_compression φ n : bounded n φ -> Σ1 φ -> exists ψ, Qdec ψ /\ bounded (S n) ψ /\ Qeq ⊢ φ <~> ∃ψ.
  Proof.
    intros Hb (k & ψ & HΔ & ->)%Σ1_exist_times.
    destruct (@exists_compression ψ n k) as (ψ' & HΔ' & Hb' & H').
    all: firstorder using bounded_exist_times.
  Qed.
End Sigma1.
Section Sigma1completeness.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.

  Existing Instance intu.

  (* substitution here as its needed for the induction *)
  Lemma Σ1_completeness φ ρ : Σ1 φ -> bounded 0 φ -> interp_nat; ρ ⊨ φ -> Qeq ⊢ φ.
  Proof.
    enough (forall ρ, Σ1 φ -> bounded 0 φ[ρ] -> interp_nat ⊨= φ[ρ] -> Qeq ⊢ φ[ρ]).
    { intros HΣ Hb Hsat. rewrite <-subst_var. apply H.
      - easy.
      - now rewrite subst_var.
      - intros ρ'. rewrite subst_var. eapply sat_closed; eassumption. }
    clear ρ. intros ρ. induction 1 as [φ H IH|φ H] in ρ |-*.
    - cbn. invert_bounds.
      intros Hnat. destruct (Hnat (fun _ => 0)) as [d Hd].
      remember intu as Hintu. (* for proof mode *)
      fexists (num d). rewrite subst_comp. apply IH.
      + rewrite <-subst_comp. eapply subst_bound; last apply H4.
        intros [|n] Hn; last lia. apply num_bound.
      + intros ρ'. rewrite <-subst_comp.
        rewrite sat_single_nat in Hd.
        eapply sat_closed; last apply Hd.
        eapply subst_bound; last apply H4. 
        intros [|n] Hn; last lia. apply num_bound.
    - intros Hb Hnat.
      destruct (H ρ Hb) as [H1 | H1].
      + easy.
      + (* note: actually only requires consistency, can also be shown for classical *)
        eapply Q_sound_intu with (rho := fun _ => 0) in H1. cbn in H1.
        exfalso. apply H1. apply Hnat.
  Qed.


  Lemma Σ1_witness φ : Σ1 φ -> bounded 1 φ -> Qeq ⊢ ∃φ -> exists x, Qeq ⊢ φ[(num x)..].
  Proof.
    intros Hb HΣ Hφ. eapply Q_sound_intu with (rho := fun _ => 0) in Hφ as [x Hx].
    exists x. eapply Σ1_completeness with (ρ := fun _ => 0).
    - now apply Σ1_subst.
    - eapply subst_bound; last eassumption.
      intros [|n] H; last lia. apply num_bound.
    - eapply sat_closed; first last.
      + rewrite <-sat_single_nat. apply Hx.
      + eapply subst_bound; last eassumption.
        intros [|n] H; last lia. apply num_bound.
  Qed.

End Sigma1completeness.
