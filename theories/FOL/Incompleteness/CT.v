From Undecidability.FOL.Incompleteness Require Import FS.
From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
From Undecidability.Shared Require Import Dec embed_nat.

Require Import Lia.


Definition stationary {X} (f : nat -> option X) := forall k k' y, f k = Some y -> k' >= k -> f k' = Some y.
Definition part X := { p : nat -> option X | stationary p }.
Definition part_returns {X} (p : part X) y := exists k, proj1_sig p k = Some y.
Definition pfunc_equiv {X Y} (f g : X -> part Y) := forall x y, part_returns (f x) y <-> part_returns (g x) y.

Definition mkstat {X} (f : nat -> option X) : nat -> option X :=
  fix g k := match k with
            | 0 => f 0
            | S k => match g k with
                    | None => f (S k)
                    | Some x => Some x
                    end
            end.

Lemma mkstat_stationary {X} (f : nat -> option X) : stationary (mkstat f).
Proof.
  intros k k' y. revert k'. induction k; intros k'.
  - intros H0. induction k'.
    + easy.
    + intros ?. cbn. rewrite IHk'.
      * reflexivity.
      * lia.
  - cbn. destruct (mkstat f k) eqn:Heq.
    + intros [= ->]. induction k'.
      * lia.
      * intros H. cbn.
        assert (k' = k \/ k' > k) as [->|H1] by lia.
        -- now rewrite Heq.
        -- rewrite IHk'.  2: lia.
           reflexivity.
    + intros Heq'. induction k'.
      * lia.
      * intros H. cbn.
        assert (k' = k \/ k' > k) as [->|H1] by lia.
        -- now rewrite Heq.
        -- rewrite IHk'. 2: lia.
           reflexivity.
Qed.
Lemma stationize {X} (f : nat -> nat -> option X) :
  (forall x k1 k2 y1 y2, f x k1 = Some y1 -> f x k2 = Some y2 -> y1 = y2) -> exists g, (forall x, stationary (g x)) /\ forall x y, (exists k, g x k = Some y) <-> (exists k, f x k = Some y).
Proof.
Admitted.

Section CT.
  Definition phi_universal (phi : nat -> nat -> part nat) :=
    forall (f : nat -> nat), exists c, forall x, part_returns (phi c x) (f x).

  Definition theta_universal (theta : nat -> nat -> part nat) :=
    forall (f : nat -> part nat), exists c, pfunc_equiv f (theta c).



  Lemma phi_theta : (exists phi, phi_universal phi) <-> (exists theta, theta_universal theta).
  Proof.
    split.
    - intros (phi & Huniv).
      unshelve evar (theta : nat -> nat -> part nat).
      {
        intros c x.
        destruct (phi c x) as [f Hf].
        exists (fun k => match f k with Some (S n) => Some n | _ => None end).
        admit.
      }
      exists theta. intros f.
      unshelve evar (f' : nat -> nat).
      { intros [x k]%unembed.
        destruct (f x) as [f' Hf'].
        destruct (f' k).
        - exact (S n).
        - exact 0. }
      destruct (Huniv f') as [c Hc].
      exists c. intros x y. cbn in *.
      admit.
    - intros [theta Huniv].
      exists theta. intros f.
      unshelve evar (f' : nat -> part nat).
      { intros x. exists (fun _ => Some (f x)). congruence. }
      destruct (Huniv f') as [c Hc].
      exists c. intros x.
      specialize (Hc x (f x)).
      apply Hc.
      exists 0. reflexivity.
  Admitted.

End CT.



(* TODO sigma formulation for functions from before *)

Section CT.
  Variable theta : nat -> nat -> nat -> option nat.
  Variable theta_stationary : forall c x, stationary (theta c x).
  Variable theta_univ :
      forall (f : nat -> nat -> option nat),
        (forall x, stationary (f x)) ->
        exists c, forall x y, (exists k, f x k = Some y) <-> (exists k, theta c x k = Some y).
  Arguments theta_univ : clear implicits.

  Definition CTreturns c x y := exists n, theta c x n = Some y.
  Definition CThalts c x := exists y, CTreturns c x y.

  Lemma CTspecial_halting_undec : ~decidable (fun d => CThalts d d).
  Proof.
    intros [f Hf].
    destruct (theta_univ (fun n _ => if f n then None else Some 1)) as [c Hc].
    { congruence. }
    specialize (Hf c). specialize (Hc c).
    destruct (f c).
    - assert (CThalts c c) as [y Hy] by firstorder.
      assert (~CTreturns c c y) by intros [_ [=]]%Hc.
      contradiction.
    - enough (false = true) by congruence.
      apply Hf. exists 1. apply Hc. eauto.
  Qed.

  Section CThalt.
    Variable fs : FS.
    Hypothesis provable_decidable : decidable provable.

    Variable wrepr : nat -> nat -> sentences.
    Hypothesis Hwrepr : forall (c x : nat), CThalts c x <-> provable (wrepr c x).

    Lemma CTwrepr_dec : decidable (fun '(c, x) => CThalts c x).
    Proof.
      destruct provable_decidable as [f Hf].
      exists (fun '(c, x) => f (wrepr c x)).
      intros [c x]. unfold reflects.
      rewrite Hwrepr. apply Hf.
    Qed.

    Lemma CTwrepr : False.
    Proof.
      apply CTspecial_halting_undec.
      destruct (CTwrepr_dec) as [f Hf].
      exists (fun d => f (d, d)). firstorder.
    Qed.
  End CThalt.


  Definition CGpred (p : nat -> nat -> Prop) := forall c x,
      (CTreturns c x 0 -> p c x) /\
        (CTreturns c x 1 -> ~p c x).

  Lemma CGpred_undec p : CGpred p -> ~exists f, forall c x, p c x <-> f c x = true.
  Proof.
    intros HCG [f Hf].
    destruct (theta_univ (fun c _ => if f c c then Some 1 else Some 0)) as [c Hc].
    { congruence. }
    specialize (Hc c). specialize (Hf c c). specialize (HCG c c).
    destruct (f c c); firstorder.
  Qed.

  Section CTguess.
    Variable fs : FS.
    Hypothesis provable_decidable : decidable provable.

    (* TODO check how this notion of representability turns up in Kleene *)
    Variable repr : nat -> nat -> nat -> sentences.
    Hypothesis Hrepr : forall (c x y : nat),
        (CTreturns c x y -> provable (repr c x y)) /\
          forall y', CTreturns c x y -> y <> y' -> ~provable ((repr c x y')).

    Lemma CGpred_dec : exists f p, CGpred p /\ forall c x, p c x <-> f c x = true.
    Proof.
      apply decidable_iff in provable_decidable as [prov_dec].
      exists (fun c x => if prov_dec (repr c x 0) then true else false).
      exists (fun c x => if prov_dec (repr c x 0) then True else False).
      split.
      - intros c x. split.
        + intros Hprov % Hrepr. now destruct prov_dec.
        + intros Hret ?. destruct prov_dec. 2: easy.
          destruct (Hrepr c x 1) as [_ Hfunc].
          now apply (Hfunc 0).
      - intros c x. destruct prov_dec; easy.
    Qed.

    Lemma CTrepr : False.
    Proof.
      destruct CGpred_dec as (f & p & HCG & Hdec).
      apply (CGpred_undec HCG); eauto.
    Qed.
  End CTguess.

  Section CTexpl.
    Variable fs : FS.

    Variable repr : nat -> nat -> nat -> sentences.
    Hypothesis Hrepr : forall (c x y : nat),
        (CTreturns c x y -> provable (repr c x y)) /\
          forall y', CTreturns c x y -> y <> y' -> ~provable ((repr c x y')).

    Lemma CGexpl : exists s, ~provable s /\ ~provable (neg s).
    Proof.
      destruct provable_enumerable as [prov Hprov].
      pose proof sentences_discrete as sentences_discrete.
      apply discrete_iff in sentences_discrete as [sentences_eqdec].

      unshelve evar (f : nat -> nat -> nat -> option bool).
      { intros c x k.
        destruct (prov k) as [p|]. 2: exact None.

        destruct (sentences_eqdec p (repr c x 0)).
        1: exact (Some true).
        destruct (sentences_eqdec p (neg(repr c x 0))).
        - exact (Some false).
        - exact None. }

      unshelve evar (g : nat -> nat -> option nat).
      {
        intros c k. destruct (f c c k) as [[]|].
        - exact (Some 1).
        - exact (Some 0).
        - exact None.
      }
      destruct (@stationize _ g) as (g' & Hgstat & Hgcorr).
      {
        intros x k1 k2 y1 y2.
        unfold g, f.
        destruct (prov k1) eqn:Hk1, (prov k2) eqn:Hk2; try congruence.
        repeat destruct sentences_eqdec; try congruence; subst.
        all: destruct (consistent (repr x x 0)); apply Hprov; eauto.
      }

      destruct (theta_univ g' Hgstat) as [c Hc].
      exists (repr c c 0).
      split.
      - intros Hp.
        apply Hrepr with (c := c) (x := c) (y := 1) (y' := 0).
        + apply Hprov in Hp as [k Hk].
          apply Hc, Hgcorr. exists k.
          unfold g, f. rewrite Hk.
          destruct sentences_eqdec; congruence.
        + discriminate.
        + assumption.
      - intros Hp. unshelve eapply (consistent (repr c c 0) _ Hp).
        apply Hrepr, Hc, Hgcorr. apply Hprov in Hp as [k Hk].
        exists k. unfold g, f. rewrite Hk.
        destruct sentences_eqdec.
        + destruct (@neg_no_fixpoint2 _ (repr c c 0)); firstorder.
        + now destruct sentences_eqdec.
    Qed.
  End CTexpl.
End CT.
