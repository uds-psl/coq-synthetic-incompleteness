From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
From Undecidability.Shared Require Import Dec embed_nat.

From Undecidability.FOL.Util Require Import Syntax_facts FullDeduction FullDeduction_facts FullTarski FullTarski_facts Axiomatisations FA_facts Syntax.
From Undecidability.FOL Require Import PA.
From Undecidability.FOL.Proofmode Require Import Theories ProofMode Hoas.
From Undecidability.FOL.Incompleteness Require Import formal_systems abstract_incompleteness fol qdec weak_strong utils epf epf_mu.

From Undecidability.H10 Require Import DPRM dio_single.

From Equations Require Import Equations.
Require Import String List.


(** * Incompleteness of first-order logic *)

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


  Section incomplete_strong_repr.
    Hypothesis (p : peirce).

    Variable theta : nat -> nat -\ bool.
    Hypothesis theta_universal : is_universal theta.

    Variable T : theory.
    Hypothesis Tenum : enumerable T.
    Hypothesis Tconsis : ~T ⊢T ⊥.

    Variable T' : theory.
    Hypothesis T'_T : T' ⊑ T.
    Hypothesis T'enum : enumerable T'.

    Variable r : nat -> form.
    Hypothesis Hrepr : 
      (forall c, theta c c ▷ true -> T' ⊢T r c) /\
      (forall c, theta c c ▷ false -> T' ⊢T ¬r c).

    Lemma fol_undecidable_strong_repr : ~decidable (fun s => T ⊢T s).
    Proof.
      assert (~T' ⊢T ⊥) as T'consis.
      { contradict Tconsis. now eapply WeakT. }
      eapply (insep_essential_undecidability) with (theta := theta) (fs := fol_fs Tenum Tconsis) (fs' := fol_fs T'enum T'consis).
      - assumption.
      - unfold extension. cbn. intros φ Hφ. now eapply WeakT.
      - exact Hrepr.
    Qed.

    Lemma fol_incomplete_strong_repr : exists n, ~T ⊢T r n /\ ~T ⊢T ¬r n.
    Proof.
      assert (~T' ⊢T ⊥) as T'consis.
      { contradict Tconsis. now eapply WeakT. }
      apply (insep_essential_incompleteness) with (theta := theta) (fs := fol_fs Tenum Tconsis) (fs' := fol_fs T'enum T'consis).
      - assumption.
      - unfold extension. cbn. intros φ Hφ. now eapply WeakT.
      - assumption.
    Qed.

  End incomplete_strong_repr.




  (** ** Weak representability from DPRM *)
  Section Q_weakly_represents.
    Existing Instance intu.
    Hypothesis mu_universal : mu_is_universal.

    Variable P : nat -> Prop.
    Hypothesis Penum : enumerable P. 
    Lemma Q_weak_repr : exists φ, bounded 1 φ /\ Σ1 φ /\ forall x, P x <-> Qeq ⊢ φ[(num x)..].
    Proof.
      destruct mu_recursive_definable with (P := P) (peirc := intu) as (φ & Hb & HΣ & Hr).
      { now apply mu_semi_decidable_enumerable. }
      exists φ. do 2 (split; first assumption).
      intros x. erewrite Hr. instantiate (1 := fun _ => 0). split.
      - intros H. eapply Σ1_completeness.
        + now apply Σ1_subst.
        + eapply subst_bound; last eassumption.
          intros [|n] Hn; last lia. apply num_bound.
        + now rewrite <-sat_single_nat.
      - intros H. rewrite sat_single_nat. eapply soundness; first eassumption.
        apply nat_is_Q_model.
    Qed.

  End Q_weakly_represents.



  (** ** Q is essentially incomplete and essentially undecidable *)
  Section Q_incomplete.
    Hypothesis mu_universal : mu_is_universal.

    Hypothesis (p : peirce).
    Existing Instance intu.

    Variable T : theory.
    Hypothesis T_Q : list_theory Qeq ⊑ T.
    Hypothesis Tenum : enumerable T.
    Hypothesis Tconsis : ~@tprv _ _ _ p T ⊥.

    Lemma theta_c_c_enumerable (theta : nat -> nat -\ bool) b : enumerable (fun c => theta c c ▷ b).
    Proof. 
      apply semi_decidable_enumerable.
      { exists (fun n => Some n). intros n. now exists n. }
      exists (fun c k => match core (theta c c) k, b with
                         | Some true, true => true
                         | Some false, false => true
                         | _, _ => false
                         end).
     intros c. split; intros [k Hk]; exists k.
     - rewrite Hk. destruct b; congruence.
     - destruct (core _ _) as [[]|], b; congruence.
    Qed. 

    Theorem Q_undecidable : ~decidable (@tprv _ _ _ p T).
    Proof.
      assert (exists f : nat -> nat -\ bool, is_universal f) as [theta theta_universal].
      { apply ct_nat_bool, CTmu, mu_universal. }
      destruct (@Q_weak_repr mu_universal (fun c => theta c c ▷ true) (theta_c_c_enumerable theta true)) as (φ1 & Hb1 & HΣ1 & Hφ1).
      destruct (@Q_weak_repr mu_universal (fun c => theta c c ▷ false) (theta_c_c_enumerable theta false)) as (φ2 & Hb2 & HΣ2 & Hφ2).
      assert (forall c, theta c c ▷ true -> theta c c ▷ false -> False) as Hdisj.
      { intros c Ht Hf. enough (true = false) by discriminate. eapply part_functional; eassumption. }
      edestruct (weak_strong Hdisj Hb1 Hb2 HΣ1 HΣ2 Hφ1 Hφ2) as (ψ & Hb & HΣ & Hψ1 & Hψ2).
      eapply (@fol_undecidable_strong_repr p theta theta_universal T Tenum Tconsis (list_theory Qeq) T_Q (list_theory_enumerable Qeq)).
      instantiate (1 := fun c => ψ[(num c)..]).
      split; intros c H.
      - exists Qeq. split; first auto.
        now apply prv_intu_class.
      - exists Qeq. split; first auto.
        now apply prv_intu_class.
    Qed.

    Theorem Q_incomplete : exists φ, bounded 0 φ /\ Σ1 φ /\ ~@tprv _ _ _ p T φ /\ ~@tprv _ _ _ p T (¬φ).
    Proof. 
      assert (exists f : nat -> nat -\ bool, is_universal f) as [theta theta_universal].
      { apply ct_nat_bool, CTmu, mu_universal. }

      destruct (@Q_weak_repr mu_universal (fun c => theta c c ▷ true) (theta_c_c_enumerable theta true)) as (φ1 & Hb1 & HΣ1 & Hφ1).
      destruct (@Q_weak_repr mu_universal (fun c => theta c c ▷ false) (theta_c_c_enumerable theta false)) as (φ2 & Hb2 & HΣ2 & Hφ2).
      assert (forall c, theta c c ▷ true -> theta c c ▷ false -> False) as Hdisj.
      { intros c Ht Hf. enough (true = false) by discriminate. eapply part_functional; eassumption. }
      edestruct (weak_strong Hdisj Hb1 Hb2 HΣ1 HΣ2 Hφ1 Hφ2) as (ψ & Hb & HΣ & Hψ1 & Hψ2).
      edestruct (@fol_incomplete_strong_repr p theta theta_universal T Tenum Tconsis (list_theory Qeq) T_Q (list_theory_enumerable Qeq)).
      { instantiate (1 := fun c => ψ[(num c)..]). cbn. 
        split; intros c H.
        - exists Qeq. split; first auto.
          now apply prv_intu_class.
        - exists Qeq. split; first auto.
          now apply prv_intu_class. }
      cbn in H. exists ψ[(num x)..]. 
      repeat apply conj.
      - eapply subst_bound; last eassumption. intros [|n] Hn; last lia. apply num_bound.
      - now apply Σ1_subst.
      - apply H.
      - apply H.
    Qed.

  End Q_incomplete.

End fol.


