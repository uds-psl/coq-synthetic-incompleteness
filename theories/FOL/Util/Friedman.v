Require Import List Lia.
From Undecidability.FOL.Util Require Import Syntax Syntax_facts FullTarski FullTarski_facts FullDeduction_facts FullDeduction.
Import Vector.VectorNotations.




Lemma size_rect {X} σ f : 
  (forall x, (forall y : X, σ y < σ x -> f y) -> f x) -> forall x, f x.
Proof.
  intros H x. apply H.
  induction (σ x).
  - intros y. now intros F % PeanoNat.Nat.nlt_0_r. 
  - intros y Hy. apply H.
    intros z Hz. apply IHn. lia.
Defined.



Section Signature.

  
 (* Assume some signature and corresponding arity functions *)
 Context {Σ_funcs : funcs_signature}.
 Context {Σ_preds : preds_signature}.

 
Section Expanded.

  (* Add one more 0-ary predicate (i.e. propositional variable) to the predicates *)
  Inductive new_preds : Type :=
    Q_ : new_preds
  | old_preds (P : Σ_preds) : new_preds. 

  Definition new_preds_ar (P : new_preds) :=
    match P with
    | Q_ => 0
    | old_preds P => ar_preds P
    end.

  Instance funcs_signature : funcs_signature :=
    {| syms := Σ_funcs ; ar_syms := ar_syms |}.

  Instance preds_signature : preds_signature :=
    {| preds := new_preds ; ar_preds := new_preds_ar |}.


  Definition Q {ff} := (@atom funcs_signature preds_signature _ ff Q_ ([])).
  Definition dn {ff} F phi : @form funcs_signature preds_signature _ ff :=
    (phi ~> F) ~> F.

  Fixpoint Friedman {ff} (phi : @form funcs_signature preds_signature _ ff) : form ff :=
    match phi with
    | falsity => Q
    | atom P v => match P with Q_ => Q | _ => dn Q (atom P v) end
    | bin Impl phi psi => (Friedman phi) ~> (Friedman psi)
    | bin Conj phi psi => (Friedman phi) ∧ (Friedman psi)
    | bin Disj phi psi => dn Q ((Friedman phi) ∨ (Friedman psi))
    | quant All phi => ∀ (Friedman phi)
    | quant Ex phi => dn Q (∃ (Friedman phi))
    end.

                      
  Notation "'Fr' f" := (Friedman f) (at level 30).
  
  Definition List_Fr {ff} Gamma := map (@Friedman ff) Gamma.
  
  Fact subst_Fr {ff} (phi : @form funcs_signature preds_signature _ ff) sigma:
    subst_form sigma (Fr phi) = Fr (subst_form sigma phi).
  Proof.
    revert sigma.
    induction phi; cbn.
    - reflexivity.
    - destruct P; reflexivity.
    - destruct b0; cbn; unfold dn, Q; congruence.
    - destruct q; cbn; intros sigma; unfold dn, Q; congruence.
  Qed.

  Fact subst_List_Fr {ff} L sigma :
    map (subst_form sigma) (map (@Friedman ff) L) = map Friedman (map (subst_form sigma) L).
  Proof.
    induction L.
    - reflexivity.
    - cbn. now rewrite IHL, subst_Fr.
  Qed.

  Lemma Fr_dn {ff} Gamma phi :
    Gamma ⊢I Fr (@dn ff Q phi) <-> Gamma ⊢I dn Q (Fr phi).
  Proof.
  Admitted.
      

  Lemma double_dn {ff} Gamma F phi :
    Gamma ⊢I @dn ff F (dn F phi) ~> dn F phi.
  Proof.
    apply II, II. eapply IE with (phi0:= _ ~> _).
    { apply Ctx; firstorder. }
    apply II. apply IE with (phi0:= phi ~> F).
    all: apply Ctx; firstorder.
  Qed.

  Lemma rm_dn {ff} Gamma F alpha beta :
    (alpha :: Gamma) ⊢I beta -> (@dn ff F alpha :: Gamma) ⊢I dn F beta.
  Proof.
    intros H.
    apply II. eapply IE with (phi:= _ ~> _).
    { apply Ctx; firstorder. }
    apply II. eapply IE with (phi:= beta).
    {apply Ctx; firstorder. }
    eapply Weak; [eassumption|firstorder].
  Qed.


  
  Lemma form_up_var0_invar {ff} (phi : @form _ _ _ ff) :
    phi[up ↑][$0..] = phi.
  Proof.
  Admitted.                             
  
  Lemma dn_forall {ff} Gamma phi :
    Gamma ⊢I @dn ff Q (∀ phi) ~> ∀ dn Q phi.
  Proof.
    apply II. constructor. apply II.
    cbn; fold Q.
    change ((∀ phi[up ↑])) with ((∀ phi)[↑]).
    eapply IE with (phi0:= _ ~> _).
    { apply Ctx; firstorder. }
    apply II.
    eapply IE with (phi0:= phi).
    { apply Ctx; firstorder. }
    cbn. rewrite <-form_up_var0_invar.
    apply AllE, Ctx; firstorder.
  Qed.
      
  
  Fixpoint form_size {ff} (phi : @form funcs_signature preds_signature _ ff) :=
    match phi with
    | falsity => 0
    | atom P v => 1
    | bin _ phi psi => S (form_size phi + form_size psi)
    | quant _ phi => S (form_size phi)
    end.

  Lemma DNE_Fr {ff} :
    forall phi Gamma, Gamma ⊢I Fr (dn Q phi) ~> @Friedman ff phi. 
  Proof.
    refine (size_rect form_size _ _). intros phi sRec.
    destruct phi; intros Gamma.
    - apply II. eapply IE; cbn.
      { apply Ctx; firstorder. }
      apply II, Ctx; firstorder.
    - destruct P.
      + apply II. eapply IE; cbn.
        {apply Ctx; firstorder. }
        apply II, Ctx; firstorder.
      + apply double_dn.
    - destruct b0; cbn.
      + apply II, CI.
        * eapply IE. apply sRec.
          {cbn; lia. }
          cbn; apply rm_dn.
          eapply CE1, Ctx; firstorder.
        * eapply IE. apply sRec.
          {cbn; lia. }
          cbn; apply rm_dn.
          eapply CE2, Ctx; firstorder.
      + apply double_dn.
      + apply II, II. eapply IE.
        apply sRec.
        {cbn; lia. }
        cbn; apply II. eapply IE with (phi:= _ ~> _).
        { apply Ctx; firstorder. }
        apply II. eapply IE with (phi:= Fr phi2).
        { apply Ctx; firstorder. }
        eapply IE with (phi:= Fr phi1); apply Ctx; firstorder.
    - destruct q.
      + cbn. apply II. apply IE with (phi0:= ∀ Fr (dn Q phi)).
        { apply II. constructor. cbn; fold Q.
          eapply IE. apply sRec; auto.
          rewrite <-form_up_var0_invar.
          apply AllE, Ctx. firstorder. }
        constructor. apply Fr_dn.
        cbn; fold Q. rewrite <- form_up_var0_invar.
        apply AllE. cbn; fold Q.
        apply imps, dn_forall.
      + apply double_dn.
  Qed.
    
  Lemma Expl_Fr {ff} Gamma phi : Gamma ⊢I Q ~> @Friedman ff phi.
  Proof.
    induction phi; cbn; apply II.
    - apply Ctx; firstorder.
    - destruct  P.
      + apply Ctx; firstorder.
      + apply II, Ctx; firstorder.
    - destruct b0.
      + apply CI; now apply imps.
      + apply II, Ctx; firstorder.
      + apply II. eapply IE. apply IHphi2.
        apply Ctx; firstorder.
    - destruct q.
      + constructor. apply imps, IHphi.
      + apply II, Ctx; firstorder.
  Qed.          
  
  Lemma Peirce_Fr {ff} Gamma phi psi : Gamma ⊢I @Friedman ff (((phi ~> psi) ~> phi) ~> phi).
  Proof.
    eapply IE. apply DNE_Fr. cbn.
    apply II. eapply IE.
    { apply Ctx; firstorder. }
    apply II. eapply IE.
    { apply Ctx; firstorder. }
    apply II. eapply IE; [apply Expl_Fr|].
    eapply IE.
    { apply Ctx; firstorder. }
    apply II. apply Ctx; firstorder.
  Qed.
    
  
  Lemma Friedman_cl_to_intu {ff} Gamma phi :
    Gamma ⊢C phi -> (List_Fr Gamma) ⊢I @Friedman ff phi.
  Proof.
    intros H. induction H; unfold List_Fr in *.
    - cbn. now constructor.
    - econstructor; eassumption.
    - cbn. constructor. now rewrite subst_List_Fr.
    - cbn in *. eapply AllE with (t0:=t) in IHprv.
      cbn in *. now rewrite subst_Fr in IHprv. 
    - cbn. apply II.
      eapply IE.
      + apply Ctx. firstorder.
      + apply Weak with (A0 := map Friedman A); [|firstorder].
        apply ExI with (t0:=t). now rewrite subst_Fr.
    - cbn in *.
      eapply IE. apply DNE_Fr. unfold dn in *; cbn.
      apply II. eapply IE.
      { eapply Weak; [apply IHprv1|firstorder]. }
      apply II. eapply IE.
      { apply Ctx; firstorder. }
      rewrite <-subst_Fr, <-subst_List_Fr in IHprv2.
      eapply ExE.
      { apply Ctx; firstorder. }
      cbn. eapply Weak.
      + apply IHprv2.
      + firstorder.
    - cbn in *.
      specialize (DNE_Fr phi (map Friedman A)) as H'.
      eapply IE; [eassumption|].
      cbn; apply II. eapply Weak; eauto.
    - now apply Ctx, in_map.
    - cbn. now apply CI.
    - cbn in *. eapply CE1; eauto.
    - cbn in *. eapply CE2; eauto.
    - cbn. apply II. eapply IE.
      + apply Ctx. firstorder.
      + apply DI1. eapply Weak; eauto.
    - cbn. apply II. eapply IE.
      + apply Ctx. firstorder.
      + apply DI2. eapply Weak; eauto.
    - eapply IE. apply DNE_Fr.
      cbn in *.
      apply II. eapply IE.
      { eapply Weak; [apply IHprv1|firstorder]. }
      apply II. eapply IE.
      { apply Ctx; firstorder. }
      apply imps in IHprv2.
      apply imps in IHprv3.
      eapply DE.
      1 : apply Ctx; firstorder.
      1,2 : apply imps; eapply Weak; [eassumption|firstorder].
    - apply Peirce_Fr.
  Qed.

    
End Expanded.
End Signature.