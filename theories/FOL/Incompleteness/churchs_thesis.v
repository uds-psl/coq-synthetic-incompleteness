From Undecidability.FOL.Incompleteness Require Import utils.

From Undecidability.Synthetic Require Import DecidabilityFacts.

Local Set Implicit Arguments.
Local Unset Strict Implicit.


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


  Lemma special_halting_diverge (f : nat -\ bool) :
    (forall c, f c ▷ true -> exists y, theta c c ▷ y) -> 
    (forall c, f c ▷ false -> forall y, ~theta c c ▷ y) -> 
    exists c, forall y, ~f c ▷ y.
  Proof.
    intros H1 H2.
    unshelve evar (g: nat -\ bool).
    { intros n. exists (fun k => match (f n).(core) k with
                                 | Some true => None
                                 | Some false => Some true
                                 | None => None 
                                 end).
      intros y1 y2 k1 k2 Hk1 Hk2.
      destruct (core (f n) k1) as [[]|] eqn:Hf1, (core (f n) k2) as [[]|] eqn:Hf2.
      all: congruence. }
    destruct (theta_universal g) as [c Hc]. exists c.
    intros [] H.
    - destruct (H1 c H) as [y [k Hk]%Hc].
      cbn in Hk. destruct (core (f c) k) as [[]|] eqn:Hf; try discriminate.
      enough (true = false) by discriminate. 
      apply (@part_functional _ (f c)); firstorder.
    - eapply (H2 c H true), Hc.
      destruct H as [k Hk]. exists k. 
      cbn. now rewrite Hk.
  Qed.
  (* This can be used to show special_halting_undec, however this is tedious *)

  (* Note: function might be partial, non-conventional definition *)
  Definition strongly_separates (P1 P2 : nat -> Prop)  (f : nat -\ bool) :=
    (forall x, P1 x -> f x ▷ true) /\
    (forall x, P2 x -> f x ▷ false).



  Lemma no_recursively_separating (f : nat -> bool) : 
    (* Looks closer to required condition by destructing b *)
    ~(forall b c, theta c c ▷ b -> f c = b).
  Proof.
    intros H.
    unshelve evar (g : nat -\ bool).
    { intros c. exists (fun _ => Some (negb (f c))).
      congruence. }
    destruct (theta_universal g) as [c Hc].
    specialize (Hc c (negb (f c))).
    assert (g c ▷ (negb (f c))) as Hg.
    { exists 0. reflexivity. }
    apply Hc in Hg. specialize (H (negb (f c)) c Hg).
    now destruct (f c).
  Qed.

  Lemma recursively_separating_diverge (f : nat -\ bool):
    (forall b c, theta c c ▷ b -> f c ▷ b) ->
    exists c, forall y, ~f c ▷ y.
  Proof.
    intros H.
    unshelve evar (g : nat -\ bool).
    { intros c. unshelve eexists.
      { intros k. exact (match (f c).(core) k with
                         | Some b => Some (negb b)
                         | None => None
                         end). }
      intros y1 y2 k1 k2 Hk1 Hk2.
      destruct (core (f c) k1) as [[]|] eqn:Hf1, (core (f c) k2) as [[]|] eqn:Hf2.
      all: cbn in *; try congruence.
      all: now pose proof ((f c).(valid) _ _ _ _ Hf1 Hf2). }
    destruct (theta_universal g) as [c Hc]. exists c. 
    intros y [k Hk].
    assert (g c ▷ (negb y)) as Hg.
    { exists k. cbn. rewrite Hk. reflexivity. }
    apply Hc in Hg. specialize (H _ _ Hg).
    enough (y = negb y) by now destruct y.
    apply (@part_functional _ (f c)).
    - now exists k. 
    - assumption.
  Qed.

End ct.

