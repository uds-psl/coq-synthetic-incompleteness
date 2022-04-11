From Undecidability.FOL.Incompleteness Require Import utils formal_systems churchs_thesis.

From Undecidability.Synthetic Require Import DecidabilityFacts.

Section abstract.
  Variable (theta : nat -> nat -\ bool).
  Hypothesis theta_universal : is_universal theta.


  Section halt.
    Context {S : Type} {neg : S -> S} (fs : FS S neg).
    Hypothesis prov_dec : decidable fs.(P).

    Hypothesis Hrepr : exists (r : nat -> S), forall c,
      (exists y, theta c c ▷ y) <-> fs ⊢F r c.

    Lemma halt_undecidability : False.
    Proof.
      destruct Hrepr as [r Hr].
      destruct prov_dec as [f Hf].
      enough (decidable (fun c => exists y, theta c c ▷ y)).
      { now eapply special_halting_undec. }
      (* TODO arguments of provable_decidable and presumably other lemmas shoudl include fs *)
      exists (fun c => f (r c)).
      unfold decider,reflects in *.
      intros x. rewrite <-Hf. apply Hr.
    Qed.
  End halt.
  Section halt.
    Context {S : Type} {neg : S -> S} (fs : FS S neg).

    Hypothesis Hrepr : exists (r : nat -> S), forall c,
      (exists y, theta c c ▷ y) <-> fs ⊢F r c.

    Lemma halt_incompleteness : exists s, independent fs s.
    Proof.
      destruct Hrepr as [r Hr].

      destruct fs.(P_enumerable) as [prov Hprov].
      pose proof fs.(S_discrete) as [S_eqdec]%discrete_iff.

      unshelve evar (f : nat -\ bool).
      { intros x. unshelve eexists.
        { intros k. 
          refine (match prov k with Some s => _ | None => None end).
          refine (if S_eqdec (neg (r x)) s then Some true else None). }
        cbn. intros y1 y2 k1 k2 H1 H2.
        destruct (prov k1), (prov k2); repeat destruct S_eqdec; try congruence. }

      destruct (theta_universal f) as [c Hc]. exists (r c).
      enough (fs ⊢F r c <-> fs ⊢F neg (r c)) as H.
      { split; intros H'; apply (consistent fs (r c)); tauto. }
      rewrite <-Hr. split.
      - intros [y Hy]. rewrite <-Hc in Hy.
        destruct Hy as [k Hk]. cbn in Hk.
        destruct (prov k) eqn:H; try destruct S_eqdec; try congruence.
        apply Hprov. exists k. congruence.
      - intros [k Hk]%Hprov. exists true. rewrite <-Hc. exists k.
        cbn. rewrite Hk. now destruct S_eqdec.
    Qed.
  End halt.

End abstract.
