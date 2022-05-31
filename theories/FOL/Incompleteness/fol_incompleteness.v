From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
From Undecidability.Shared Require Import Dec embed_nat.

From Undecidability.FOL.Util Require Import Syntax_facts FullDeduction FullDeduction_facts FullTarski FullTarski_facts Axiomatisations FA_facts Syntax.
From Undecidability.FOL Require Import PA.
From Undecidability.FOL.Proofmode Require Import Theories ProofMode Hoas.
From Undecidability.FOL.Incompleteness Require Import formal_systems abstract_incompleteness fol qdec repr utils churchs_thesis.


From Equations Require Import Equations.
Require Import String List.


Lemma enumerable_PA_funcs : enumerable__T PA_funcs.
Proof.
  cbn. exists (fun k => match k with
    | 0 => Some Zero
    | 1 => Some Succ
    | 2 => Some Plus
    | _ => Some Mult
    end).
  intros [].
  + now exists 0.
  + now exists 1.
  + now exists 2.
  + now exists 3.
Qed.

Section fol_fs.
  Existing Instance PA_funcs_signature.
  Existing Instance PA_preds_signature.
  Hypothesis (p : peirce).

  Definition fol_fs (T : theory) (Tenum : enumerable T) (Tconsis : ~T ⊢T ⊥) : FS form (fun φ => ¬φ).
  Proof.
    apply mkFS with (P := fun φ => T ⊢T φ).
    - apply form_discrete.
    - unshelve eapply tprv_enumerable.
      + apply enumerable_PA_funcs.
      + exists (fun _ => Some Eq). intros []. now exists 0.
      + assumption.
    - intros φ [T1 [HT1 H1]] [T2 [HT2 H2]]. apply Tconsis. exists (T1 ++ T2). split.
      + intros ψ [?|?]%in_app_or; auto.
      + fapply H2. fapply H1.
  Defined.
End fol_fs.


Lemma list_theory_enumerable {Σ_funcs : funcs_signature} {Σ_preds : preds_signature} A : 
  enumerable (list_theory A).
Proof.
  exists (List.nth_error A).
  intros x. split.
  - apply List.In_nth_error.
  - intros [k Hk]. eapply List.nth_error_In, Hk.
Qed.

Section fol.
  Existing Instance PA_funcs_signature.
  Existing Instance PA_preds_signature.
  Hypothesis (p : peirce).
  Existing Instance intu.

  Variable T : theory.
  Hypothesis T_Q : list_theory Qeq ⊑ T.
  Hypothesis Tenum : enumerable T.
  Hypothesis Tconsis : ~@tprv _ _ _ p T ⊥.

  Variable theta : nat -> nat -\ bool.
  Variable theta_univ : is_universal theta.

  Hypothesis Hrepr : forall P : nat -> Prop, enumerable P ->
    exists φ, Qdec φ /\ bounded 2 φ /\ forall x ρ, P x <-> interp_nat; ρ ⊨ ∃φ[(num x)..].

  Lemma fol_incomplete' : exists φ, ~@tprv _ _ _ p T φ /\ ~@tprv _ _ _ p T (¬φ).
  Proof.
    assert (Qenum : enumerable (list_theory Qeq)) by apply list_theory_enumerable.
    assert (Qconsis : ~list_theory Qeq ⊢TI ⊥).
    { intros H.
      assert (H' : Qeq ⊢ ⊥).
      { destruct H as (Qeq' & Hc & H).
        eapply Weak.
        - apply H.
        - exact Hc. }
      eapply Q_sound_intu with (rho := fun _ => 0) in H' as []. }
    eapply insep_essential_incompleteness with (fs := fol_fs Tenum Tconsis) (fs' := @fol_fs intu (list_theory Qeq) Qenum Qconsis).
    - eapply theta_univ.
    - intros φ Hφ.
      eapply WeakT. 2: apply T_Q.
      cbn in Hφ.
      destruct Hφ as [Qeq' [Hc H]].
      exists Qeq'. split; first assumption.
      admit.
    - cbn.
      destruct (@Hrepr (fun x => theta x x ▷ true)) as [φ1 (HQ1 & Hb1 & Hφ1)].
      { admit. }
      destruct (@Hrepr (fun x => theta x x ▷ false)) as [φ2 (HQ2 & Hb2 & Hφ2)].
      { admit. }
      destruct (@weak_strong (fun x => theta x x ▷ true) 
        (fun x => theta x x ▷ false)) with (φ1 := φ1) (φ2 := φ2) as (φ & Hb & Hφ).
      + intros x H1 H2. enough (true = false) by discriminate. eapply part_functional; eassumption.
      + assumption.
      + assumption.
      + assumption.
      + assumption.
      + admit.
      + admit.
      + exists (fun x => φ[(num x)..]). intros c. split.
        * intros H. exists Qeq. split; first auto. now apply Hφ.
        * intros H. exists Qeq. split; first auto. now apply Hφ.
  Admitted.
End fol.
Section fol.
  Existing Instance PA_funcs_signature.
  Existing Instance PA_preds_signature.
  Hypothesis (p : peirce).

  Variable T : theory.
  Hypothesis T_Q : list_theory Qeq ⊑ T.
  Hypothesis Tenum : enumerable T.
  Hypothesis Tconsis : ~@tprv _ _ _ p T ⊥.

  Variable theta : nat -> nat -\ bool.
  Variable theta_univ : is_universal theta.

  Hypothesis Hrepr : forall P : nat -> Prop, enumerable P ->
    exists φ, @Σ1 intu φ /\ bounded 1 φ /\ forall x ρ, P x <-> interp_nat; (x .: ρ) ⊨ φ.

  Lemma fol_incomplete : exists φ, ~@tprv _ _ _ p T φ /\ ~@tprv _ _ _ p T (¬φ).
  Proof.
    eapply fol_incomplete'; try eassumption.
    intros P Penum. destruct (Hrepr Penum) as (ψ & HΣ & Hb & Hc).
    destruct (Σ1_compression Hb HΣ) as (ψ' & HQ & Hb' & Hc').
    exists ψ'[$1 .: $0 ..]. split; last split.
    { now apply Qdec_subst. }
    { eapply subst_bound; first eassumption. intros [|[|n]]; cbn; solve_bounds. }
    intros x ρ.
    apply Q_sound_intu with (rho := x .: ρ) in Hc'. cbn in Hc'.
    rewrite (Hc x ρ). 
    eassert (Hc'' : _ <-> _) by exact Hc'. rewrite Hc''. cbn.
    apply utils_tac.exists_equiv. intros k.
    rewrite !sat_single_nat, !subst_comp. 
    assert (H : forall phi1 phi2, phi1 = phi2 -> interp_nat; ρ ⊨ phi1 <-> interp_nat; ρ ⊨ phi2) by (now intros ? ? ->); apply H.
    eapply bounded_subst; first eassumption. 
    intros [|[|[|n]]]; cbn; rewrite ?num_subst; repeat solve_bounds.
  Qed.

End fol.

From Undecidability.H10 Require Import DPRM dio_single.
Section dprm.
  Existing Instance PA_funcs_signature.
  Existing Instance PA_preds_signature.
  Existing Instance interp_nat.

  Variable P : nat -> Prop.
  Context `{peirc : peirce}.

  Fixpoint fin_to_n k (n : Fin.t k) : nat.
  Proof.
    destruct n.
    - exact 0.
    - exact (S (fin_to_n _ n0)).
  Defined.
  Lemma fin_to_n_bound k (n : Fin.t k) :
    fin_to_n n <= k.
  Proof.
    induction n; cbn; lia.
  Qed.
  Fixpoint embed_poly n (p : dio_polynomial (Fin.t n) (Fin.t 1)) : term.
  Proof.
    destruct p.
    - exact (num n0).
    - exact $(fin_to_n t).
    - exact $n.
    - destruct d.
      + exact (embed_poly _ p1 ⊕ embed_poly _ p2).
      + exact (embed_poly _ p1 ⊗ embed_poly _ p2).
  Defined.
  Lemma embed_poly_bound n (p : dio_polynomial (Fin.t n) (Fin.t 1)) :
    bounded_t (S n) (embed_poly p).
  Proof.
    induction p; cbn.
    - apply num_bound.
    - constructor. pose proof (fin_to_n_bound v). lia.
    - solve_bounds.
    - destruct d; now solve_bounds.
  Qed.

  Fixpoint vec_pos_default {X : Type} {n : nat} (v : Vector.t X n) (d : nat -> X) k : X
    := match v with
       | Vector.nil => d k
       | Vector.cons _ x n' v' => match k with 
                                  | 0 => x
                                  | S k' => vec_pos_default v' d k'
                                  end
       end.
  Lemma vec_pos_default_fin {X : Type} {n : nat} (v : Vector.t X n) (f : Fin.t n) (d : nat -> X) :
    vec.vec_pos v f = vec_pos_default v d (fin_to_n f).
  Proof.
    induction f; depelim v; now cbn.
  Qed.
  Lemma vec_pos_default_default {X : Type} {n : nat} (v : Vector.t X n) (m : nat) (d : nat -> X) :
    d m = vec_pos_default v d (m + n).
  Proof.
    induction v; cbn.
    - f_equal. lia.
    - now replace (m + S n) with (S m + n) by lia.
  Qed.

  Lemma embed_eval n (p : dio_polynomial (Fin.t n) (Fin.t 1)) : 
    forall x ρ (v : Vector.t nat n), 
      dp_eval (vec.vec_pos v) (fun _ => x) p = eval (vec_pos_default v (x .: ρ)) (embed_poly p).
  Proof. 
    intros x ρ. induction p; intros w; cbn.
    - now rewrite nat_eval_num.
    - apply vec_pos_default_fin.
    - change n with (0 + n).
      now rewrite <-vec_pos_default_default with (m := 0).
    - destruct d; cbn; now rewrite IHp1, IHp2.
  Qed.

  Lemma vec_pos_default_append n m (v : Vector.t nat n) (w : Vector.t nat m) d k :
    vec_pos_default (Vector.append v w) d k = vec_pos_default v (vec_pos_default w d) k.
  Proof.
    induction v in k |-*; first reflexivity.
    cbn. now destruct k.
  Qed.
  Lemma vec_append1 n (v : Vector.t nat (n+1)) :
    exists k w, v = Vector.append w (Vector.cons k Vector.nil).
  Proof.
    induction n as [|n IHn].
    - do 2 depelim v. now exists h, Vector.nil.
    - cbn in v. depelim v. destruct (IHn v) as (k & w & ->). 
      now exists k, (Vector.cons h w). 
  Qed.

  Lemma sat_exist_times n ρ φ : interp_nat; ρ ⊨ exist_times n φ <-> exists w : Vector.t nat n, interp_nat; (vec_pos_default w ρ) ⊨ φ.
  Proof.
    induction n as [|n IHn] in ρ |-*; cbn.
    - split.
      + intros H. now exists Vector.nil.
      + intros [v H]. now depelim v. 
    - setoid_rewrite IHn. split. 
      + intros (k & w & Hw). replace (S n) with (n + 1) by lia.
        exists (Vector.append w (Vector.cons k Vector.nil)).
        eapply sat_ext; first apply vec_pos_default_append.
        assumption.
      + replace (S n) with (n+1) by lia.
        intros [w Hw]. 
        destruct (vec_append1 w) as (h & w' & ->).
        exists h, w'.
        eapply sat_ext in Hw.
        2: { intros x. symmetry. apply vec_pos_default_append. }
        easy.
  Qed.

  Lemma dprm_definable : dio_rec_single P -> exists φ, Σ1 φ /\ bounded 1 φ /\ forall x ρ, P x <-> interp_nat; (x .: ρ) ⊨ φ.
  Proof.
    unfold dio_rec_single.
    intros (n & p1 & p2 & H).
    exists (exist_times n (embed_poly p1 == embed_poly p2)). repeat apply conj.
    - apply exist_times_Σ1. constructor. apply Qdec_eq.
    - apply bounded_exist_times. 
      all: replace (n + 1) with (S n) by lia.
      solve_bounds; apply embed_poly_bound.
    - intros x ρ. rewrite H. clear H. 
      setoid_rewrite sat_exist_times. 
      setoid_rewrite embed_eval. cbn. reflexivity.
  Qed.

  Check mu_recursive.
  Lemma mu_recursive_definable : mu_recursive P -> exists φ, Σ1 φ /\ bounded 1 φ /\ forall x ρ, P x <-> interp_nat; (x .: ρ) ⊨ φ.
  Proof.
    intros H. apply dprm_definable. now do 3 apply DPRM_1.
  Qed.
  

End dprm.
