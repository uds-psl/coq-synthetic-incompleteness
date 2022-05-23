From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
From Undecidability.Shared Require Import Dec embed_nat.

From Undecidability.FOL.Util Require Import Syntax_facts FullDeduction FullDeduction_facts FullTarski FullTarski_facts Axiomatisations FA_facts Syntax.
From Undecidability.FOL Require Import PA.
From Undecidability.FOL.Proofmode Require Import Theories ProofMode Hoas.
From Undecidability.FOL.Incompleteness Require Import formal_systems abstract_incompleteness fol qdec repr utils churchs_thesis.


From Equations Require Import Equations DepElim.
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
  Goal forall X (p : X -> Prop), ex p -> False.
  Proof.
    induction 1.  Show Proof.

  (* TODO the current problem is that its not clear whether varphi has x or k inserted first *)
  Hypothesis Hrepr : forall P : nat -> Prop, enumerable P ->
    exists φ, Qdec φ /\ bounded 2 φ /\ forall x ρ, P x <-> interp_nat; (x.:ρ) ⊨ ∃φ.

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
      + intros x ρ. specialize (Hφ1 x ρ).
        rewrite sat_single_nat in Hφ1. cbn in Hφ1. cbn.
        admit.
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
    exists ψ'. do 2 (split; first assumption).
    intros x ρ.
    apply Q_sound_intu with (rho := x .: ρ) in Hc'. 
    rewrite (Hc x ρ). apply Hc'.
  Qed.

End fol.
