From Undecidability.FOL.Incompleteness Require Import utils formal_systems churchs_thesis.

From Undecidability.Synthetic Require Import DecidabilityFacts.

Section abstract.
  Variable (theta : nat -> nat -\ bool).
  Hypothesis theta_universal : is_universal theta.


  Section halt.
    Context {S : Type} {neg : S -> S} (fs : FS S neg).
    Hypothesis complete : complete fs.

    Hypothesis Hrepr : exists (r : nat -> S), forall c,
      (exists y, theta c c ▷ y) <-> fs ⊢F r c.

    Lemma halt_incompleteness : False.
    Proof.
      destruct Hrepr as [r Hr].
      enough (decidable (fun c => exists y, theta c c ▷ y)).
      { now eapply special_halting_undec. }
      (* TODO arguments of provable_decidable and presumably other lemmas shoudl include fs *)
      destruct (provable_decidable complete) as [f Hf].
      exists (fun c => f (r c)). intros c. unfold reflects.
      rewrite Hr. apply Hf.
    Qed.
  End halt.

End Abstract.
