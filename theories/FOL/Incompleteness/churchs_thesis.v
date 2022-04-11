From Undecidability.FOL.Incompleteness Require Import utils.

From Undecidability.Synthetic Require Import DecidabilityFacts.

Definition is_universal {Y : Type} (theta : nat -> nat -\ Y) :=
  forall f : nat -\ Y, exists c, forall x y, f x ▷ y <-> theta c x ▷ y.

Section ct.
  Variable (theta : nat -> nat -\ bool).
  Hypothesis theta_universal : is_universal theta.

  Lemma special_halting_undec : ~decidable (fun c => exists y, theta c c ▷ y).
  Proof.
    intros [f Hf].
    unshelve evar (g: nat -\ bool).
    { intros n. exists (fun _ => if f n then None else Some true).
      congruence. }
    edestruct (theta_universal g) as [c Hc].
    specialize (Hf c). specialize (Hc c). cbv in Hc.
    destruct (f c) eqn:H.
    - assert (exists y, theta c c ▷ y) as [y Hy] by firstorder.
      apply Hc in Hy as [y' Hy']. congruence.
    - enough (exists y, theta c c ▷ y) by firstorder congruence.
      exists true. apply Hc. eauto.
  Qed.
End ct.
