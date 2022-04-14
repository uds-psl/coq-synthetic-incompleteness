From Undecidability.FOL.Incompleteness Require Import FS CT.
From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
From Undecidability.Shared Require Import Dec embed_nat.

From Undecidability.FOL.Util Require Import Syntax_facts FullDeduction FullDeduction_facts FullTarski FullTarski_facts Axiomatisations FA_facts Syntax.
From Undecidability.FOL Require Import PA.

Require Import List. Import ListNotations.

Import Equations.


Section leibnitz.
    Context {p : peirce}.
    Existing Instance PA_funcs_signature.
    Existing Instance PA_preds_signature.

    Import vec.
    Lemma form_ind_falsity_on :
      forall P : form -> Prop,
        P falsity ->
        (forall P0 (t : vec term (ar_preds P0)), P (atom P0 t)) ->
        (forall (b0 : binop) (f1 : form), P f1 -> forall f2 : form, P f2 -> P (bin b0 f1 f2)) ->
        (forall (q : quantop) (f2 : form), P f2 -> P (quant q f2)) ->
        forall (f4 : form), P f4.
    Proof.
      intros. specialize (form_ind (fun ff => match ff with falsity_on => P | _ => fun _ => True end)).
      intros H'. apply H' with (f3 := falsity_on); clear H'. all: intros; try destruct b; trivial.
      all: intuition eauto 2.
    Qed.
    Lemma leibniz φ t1 t2 : Qeq ⊢ t1 == t2 -> Qeq ⊢ φ[t1..] <~> φ[t2..].
    Proof.
      revert t1 t2. induction φ using form_ind_falsity_on.
      all: intros t1 t2 Heq.
      - cbn -[Qeq]. admit.
      - destruct P0. do 3 depelim t. cbn -[Qeq].
        induction h.
        + admit.
        + destruct h0.
          * admit.
          * destruct F, f; cbn -[Qeq]; repeat depelim v; repeat depelim t.
            -- cbn -[Qeq]. admit.
            -- cbn -[Qeq]. admit.
            -- cbn -[Qeq].
        admit. 
      - destruct b0; cbn -[Qeq].
        all: admit.
      - destruct q; cbn -[Qeq].
        + apply CI.
          * apply II. apply AllI. cbn -[Qeq].
            change (map _ _) with Qeq.
            enough ( (∀ φ[up t1..][up ↑] :: Qeq) ⊢ φ[up t1..]) as H.
            { admit. }
            admit.
          * admit.
        + admit.
    Admitted.

End leibnitz.

Section d.
  Variable p : peirce.
  Definition Qdec φ := Qeq ⊢ φ \/ Qeq ⊢ ¬φ.

  Lemma Qdec_or φ ψ : Qdec φ -> Qdec ψ -> Qdec (φ ∨ ψ).
  Proof.
    intros [Hφ | Hφ] [Hψ | Hψ].
    - left. now apply DI1.
    - left. now apply DI1.
    - left. now apply DI2.
    - right. apply II. eapply DE.
      { apply Ctx. left. reflexivity. }
      + eapply IE.
        * eapply Weak; first apply Hφ. auto.
        * apply Ctx. left. reflexivity.
      + eapply IE.
        * eapply Weak; first apply Hψ. auto.
        * apply Ctx. left. reflexivity.
  Qed.

  Lemma Qdec_eq n m : Qdec (num n == num m).
  Proof.
    induction n.
    - destruct m.
      + left. fstart.
      + 
End d.
