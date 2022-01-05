From Undecidability.FOL.Incompleteness Require Import FS.
From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
From Undecidability.Shared Require Import Dec embed_nat.

Require Import Lia.


Notation "'Sigma' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Definition part_functional {X} (f : nat -> option X) :=
  forall k1 k2 y1 y2, f k1 = Some y1 -> f k2 = Some y2 -> y1 = y2.
Definition part_stationary {X} (f : nat -> option X) :=
  forall k k' y, f k = Some y -> k' >= k -> f k' = Some y.
Definition part_returns {X} (f : nat -> option X) x :=
  exists k, f k = Some x.
Definition part_equiv {X} (f g : nat -> option X) :=
  forall x, part_returns f x <-> part_returns g x.

Definition mkstat {X} (f : nat -> option X) : nat -> option X :=
  fix g k := match k with
            | 0 => f 0
            | S k => match f (S k) with
                    | None => g k
                    | Some x => Some x
                    end
            end.

Lemma mkstat_exists {X} (f : nat -> option X)  :
    forall k x, mkstat f k = Some x -> part_returns f x.
Proof.
  induction k; first now exists 0.
  cbn. destruct (f (S k)) as [x|] eqn:Heq. 
  - intros y [= ->]. now exists (S k).
  - assumption.
Qed.

Lemma mkstat_stationary {X} (f : nat -> option X) : 
  part_functional f -> part_stationary (mkstat f).
Proof.
  intros Hf k k' y.
  induction k in k' |-*.
  - intros H _. induction k'; first assumption.
    cbn. destruct (f (S k')) eqn:Heq; first f_equal; eauto.
  - cbn. intros H. induction k'; first lia. 
    cbn. intros Hk. destruct (f (S k')) eqn:Heq.
    + destruct (f (S k)) eqn:Heq'.
      * rewrite <-H. f_equal. eauto.
      * apply mkstat_exists in H as [j Hj].
        f_equal. eauto.
    + assert (k' = k \/ k' > k) as [->|H1] by lia.
      * rewrite Heq in H. assumption.
      * apply IHk'. lia.
Qed.
Lemma mkstat_correct {X} (f : nat -> option X) :
    part_functional f ->
    forall x, part_returns f x <-> part_returns (mkstat f) x.
Proof.
  intros Hf x. split; intros [k Hk].
  - enough (mkstat f k = Some x \/ forall k', k' <= k -> f k' = None).
    { destruct (H) as [H' | H'].
      - firstorder.
      - specialize (H' k (le_n _)). congruence.
    }
    induction k; first now left.
    destruct (f k) as [y|] eqn:Heq.
    + destruct IHk as [H|H].
      * f_equal. eauto.
      * left. cbn. now rewrite Hk.
      * specialize (H k (le_n _)). congruence.
    + cbn. rewrite Hk. now left.
  - eapply mkstat_exists. eassumption. 
Qed.

Definition ffunctional {X Y} (f : X -> nat -> option Y) :=
  forall x k1 k2 y1 y2, f x k1 = Some y1 -> f x k2 = Some y2 -> y1 = y2.
Definition fstationary {X Y} (f : X -> nat -> option Y) :=
  forall x k k' y, f x k = Some y -> k' >= k -> f x k' = Some y.
Definition freturns {X Y} (f : X -> nat -> option Y) x y :=
  exists k, f x k = Some y.
Definition fhalts {X Y} (f : X -> nat -> option Y) x :=
  exists y, freturns f x y.

Lemma stationize {X} (f : nat -> nat -> option X) :
  ffunctional f -> Sigma g, fstationary g /\ forall x y, freturns f x y <-> freturns g x y.
Proof.
  intros Hf.
  exists (fun x => mkstat (f x)).
  split.
  - intros x. apply mkstat_stationary.
    exact (Hf x). (* apply does not work here for some reason *)
  - intros x y. apply mkstat_correct. exact (Hf x).
Qed.


Section CT.
  Variable theta : nat -> nat -> nat -> option bool.

  Hypothesis theta_stationary : forall c, fstationary (theta c).
  Hypothesis theta_univ : forall (f : nat -> nat -> option bool), fstationary f ->
            exists c, forall x y, freturns f x y <-> freturns (theta c) x y.
  Arguments theta_univ : clear implicits.


  Lemma CTspecial_halting_undec : ~decidable (fun d => fhalts (theta d) d).
  Proof.
    intros [f Hf].
    destruct (theta_univ (fun n _ => if f n then None else Some true)) as [c Hc].
    { congruence. }
    specialize (Hf c). specialize (Hc c). cbv in Hc.
    destruct (f c) eqn:H.
    - assert (fhalts (theta c) c) as [y Hy] by firstorder.
      apply Hc in Hy as [y' Hy'].
      congruence.
    - enough (fhalts (theta c) c) by firstorder congruence.
      exists true. apply Hc. firstorder.
  Qed.

  Section halt.
    Variable fs : FS.
    Hypothesis complete : completeness.

    Hypothesis Hrepr : forall c, Sigma (repr : nat -> sentences),
      forall x, fhalts (theta c) x <-> provable (repr x).

    Lemma CTwrepr_dec : decidable (fun c => fhalts (theta c) c).
    Proof.
      destruct provable_decidable as [f Hf]; first assumption.
      exists (fun c => f (projT1 (Hrepr c) c)).
      intros c. unfold reflects.
      destruct Hrepr as [r Hr]. cbn.
      rewrite Hr. apply Hf.
    Qed.

    Lemma CTwrepr : False.
    Proof.
      apply CTspecial_halting_undec, CTwrepr_dec.
    Qed.
  End halt.

  Section halt_explicit.
    Variable fs : FS.

    (* Kleene indirectly mentions we can strengthen this assumption and instead drop consistency? *)
    Hypothesis Hrepr : forall c, Sigma (repr : nat -> sentences),
      forall x, fhalts (theta c) x <-> provable (repr x).
    
    Lemma CTwexpl : exists s, ~provable s /\ ~provable (neg s).
    Proof.
      destruct provable_enumerable as [prov Hprov].
      pose proof sentences_discrete as sentences_discrete.
      apply discrete_iff in sentences_discrete as [sentences_eqdec].

      unshelve evar (f : nat -> nat -> option bool).
      { intros c k.
        refine (match prov k with Some p => _ | None => None end).

        destruct (sentences_eqdec p (neg (projT1 (Hrepr c) c))).
        - exact (Some true).
        - exact None. }
      destruct (@stationize _ f) as (f' & Hfstat & Hfcorr).
      {
        intros x k1 k2 y1 y2 H1 H2.
        unfold f in H1, H2.
        destruct (prov k1) as [s1|], (prov k2) as [s2|]; try discriminate. 
        destruct (sentences_eqdec s1 _), (sentences_eqdec s2 _); congruence. }
      
      destruct (theta_univ f' Hfstat) as [c Hc].
      destruct (Hrepr c) as (r & Hr) eqn:Hreq. 

      (* sentence is equivalent to its own refutability *)
      (* by negating both sides: sentence equivalent to its own unprovability *)
      assert (fhalts (theta c) c <-> provable (neg (r c))) as H.
      { split.
        - intros H.
          destruct H as (b & Hb).
          rewrite <-Hc, <-Hfcorr in Hb.
          destruct Hb as [k Hk].
          apply Hprov. exists k.
          unfold f in Hk. destruct prov; last discriminate.
          rewrite Hreq in Hk. cbn in Hk.
          destruct sentences_eqdec; congruence.  
        - intros [k Hk]%Hprov.
          exists true. rewrite <-Hc, <-Hfcorr.
          exists k. unfold f.
          destruct prov; last discriminate.
          rewrite Hreq. cbn.
          destruct sentences_eqdec; congruence. }

      exists (r c).
      split.
      - intros Hp. apply (consistent (r c)).
        + assumption.
        + apply H, Hr, Hp.  
      - intros Hp. apply (consistent (r c)).
        + apply Hr, H, Hp.
        + assumption.   
      (* TODO is there an approach here that is closer to the one using CG? i.e., make f "solve" the halting problem under completeness
         and show it diverges on some input *) 
    Qed.
  End halt_explicit.

  Definition CGfunc (f : nat -> nat -> bool) := forall c x y,
      (freturns (theta c) x y -> f c x = y).

  Lemma CG_undec : ~exists f, CGfunc f.
  Proof.
    intros [f Hf].
    destruct (theta_univ (fun c _ => Some (negb (f c c)))) as [c Hc].
    { congruence. }
    specialize (Hc c). specialize (Hf c c).
    destruct (f c c) eqn:H.
    - enough (true = false) by discriminate.
      apply Hf, Hc. unfold freturns. rewrite H. eauto.
    - enough (false = true) by discriminate.
      apply Hf, Hc. unfold freturns. rewrite H. eauto.
  Qed.

  Section guess.
    Variable fs : FS.
    Hypothesis provable_decidable : decidable provable.

    Hypothesis Hrepr : forall c, Sigma (repr : nat -> bool -> sentences),
        forall x y, freturns (theta c) x y -> provable (repr x y) /\ provable (neg (repr x (negb y))).
    Arguments Hrepr : clear implicits.

    Lemma CG_dec : exists f, CGfunc f.
    Proof.
      apply decidable_iff in provable_decidable as [prov_dec].
      exists (fun c x => if prov_dec (projT1 (Hrepr c) x true) then true else false).
      intros c x [] Hret; destruct prov_dec as [H|H]; destruct (Hrepr c) as [r Hr]; cbn in H.
      - reflexivity.
      - contradict H. apply Hr, Hret.
      - destruct (consistent (r x (negb false))); intuition.
      - reflexivity.
    Qed.

    Lemma CTrepr : False.
    Proof.
      apply CG_undec, CG_dec.
    Qed.
  End guess.


  Section CTexpl.
    Variable fs : FS.

    Hypothesis Hrepr : forall c, Sigma (repr : nat -> bool -> sentences),
      forall x y, freturns (theta c) x y -> provable (repr x y) /\ provable (neg (repr x (negb y))).

    Lemma CGexpl : exists s, ~provable s /\ ~provable (neg s).
    Proof.
      destruct provable_enumerable as [prov Hprov].
      pose proof sentences_discrete as sentences_discrete.
      apply discrete_iff in sentences_discrete as [sentences_eqdec].

      unshelve evar (f : nat -> nat -> nat -> option bool).
      { intros c x k.
        destruct (prov k) as [p|]. 2: exact None.

        destruct (sentences_eqdec p (projT1 (Hrepr c) x true)).
        1: exact (Some true).
        destruct (sentences_eqdec p (neg(projT1 (Hrepr c) x true))).
        - exact (Some false).
        - exact None. }

      unshelve evar (g : nat -> nat -> option bool).
      {
        intros c k. destruct (f c c k) as [b|].
        - exact (Some (negb b)).
        - exact None.
      }
      destruct (@stationize _ g) as (g' & Hgstat & Hgcorr).
      {
        intros x k1 k2 y1 y2.
        unfold g, f.
        destruct (prov k1) eqn:Hk1, (prov k2) eqn:Hk2; try congruence.
        repeat destruct sentences_eqdec; try congruence; subst.
        all: destruct (consistent (projT1 (Hrepr x) x true)); apply Hprov; eauto.
      }

      destruct (theta_univ g' Hgstat) as [c Hc].
      exists (projT1 (Hrepr c) c true).
      split.
      - intros Hp.
        destruct (Hrepr c) as [r Hr] eqn:Heq; cbn in *.
        eapply consistent; first exact Hp.
        apply Hprov in Hp as [k Hk].
        apply Hr with (y := false), Hc, Hgcorr.
        exists k. unfold g, f. rewrite Hk, Heq. cbn.
        destruct sentences_eqdec; cbn; congruence.
      - intros Hp. 
        destruct (Hrepr c) as [r Hr] eqn:Heq; cbn in *.
        apply (consistent (r c true)); last assumption.
        apply Hprov in Hp as [k Hk].
        apply Hr, Hc, Hgcorr.
        exists k. unfold g, f. rewrite Hk, Heq.
        destruct sentences_eqdec.
        + destruct (@neg_no_fixpoint2 _ (r c true)); firstorder.
        + now destruct sentences_eqdec.
    Qed.
  End CTexpl.

  Section inseparable.
    Hypothesis (FS : FS).
    (* C1 and C2 must be disjoint *)
    Variable (C1 C2 : nat -> Prop).

    Hypothesis insep : forall (f : nat -> nat -> option bool),
        fstationary f ->
        (forall x, (C1 x -> exists k, f x k = Some true) /\ (C2 x -> exists k, f x k = Some false)) ->
        Sigma y, forall k, f y k = None.

    Hypothesis repr : Sigma (r1 r2 : nat -> sentences),
        forall x, (C1 x -> provable (r1 x) /\ provable (neg (r2 x))) /\
             (C2 x -> provable (neg (r1 x)) /\ provable (r2 x)).

    Lemma gasfdhjlk : Sigma s, ~provable s /\ ~provable (neg s).
    Proof.
    Abort.

  End inseparable.

  Section CTsecond.
    Variable sentences : Type.
    Variable neg : sentences -> sentences.
    Variable sentences_discrete : discrete sentences.
    Variable sentences_enumerable : enumerable__T sentences.
    Variable provable : sentences -> Prop.
    Variable provable_enumerable : enumerable provable.

    Hypothesis Hrepr : forall c, Sigma (repr : nat -> bool -> sentences),
      forall x y, freturns (theta c) x y -> provable (repr x y) /\ provable (neg (repr x (negb y))).

    Definition consistent := forall s, provable s -> provable (neg s) -> False.

    Definition search_inconsistency 
      (provable_enumerator : nat -> option sentences)
      (sentences_eqdec : sentences -> sentences -> bool) :
      nat -> nat -> option bool.
    Proof.
      intros [x y]%unembed k.
      destruct (provable_enumerator x) as [s1|]; last exact None.
      destruct (provable_enumerator y) as [s2|]; last exact None.
      exact (if sentences_eqdec s1 (neg s2) then Some true else None).
    Defined.

    Lemma inconsistency_unprovable :
      forall c, (~freturns (theta c) 0 true <-> consistent) ->
        ~provable (neg (projT1 (Hrepr c) 0 true)).
    Proof.
      intros c Hc Hprov.

    Admitted.

    Lemma incosistency_searcher : 
      exists c, (~fhalts (theta c) 0 <-> consistent).
    Proof.
      destruct provable_enumerable as [prov Hprov].
      apply discrete_iff in sentences_discrete as [sentences_discrete].
      unshelve evar (f : nat -> option bool).
      {
        refine (fun k => _).
        refine (let (x, y) := unembed k in _).
        refine (match prov x with Some s1 => _ | None => None end).
        refine (match prov y with Some s2 => _ | None => None end).
        refine (if sentences_discrete s1 (neg s2) then Some true else None).
      }
      assert (forall (k1 k2 : nat) (y1 y2 : bool), 
          f k1 = Some y1 -> f k2 = Some y2 -> y1 = y2) as Hfunc.
      { intros k1 k2 y1 y2 H1 H2. unfold f in H1, H2.
        destruct (unembed k1), (unembed k2).
        do 4 destruct prov; try do 2 destruct sentences_discrete; congruence. }
      destruct (@theta_univ (fun _ => mkstat f)) as [c Hc].
      { intros _. apply mkstat_stationary. exact Hfunc. }
      exists c. split.
      - intros Hhalts s [k1 Hk1]%Hprov [k2 Hk2]%Hprov. apply Hhalts.
        exists true. 
        rewrite <-Hc. change (part_returns (mkstat f) true).
        rewrite <-mkstat_correct; last assumption.
        exists (embed (k2, k1)). 
        unfold f. rewrite embedP.
        rewrite Hk1, Hk2.
        now destruct sentences_discrete.
      - intros H (b & Hb).
        rewrite <-Hc in Hb. change (part_returns (mkstat f) b) in Hb.
        rewrite <- mkstat_correct in Hb; last assumption.
        destruct Hb as [k Hk].
        unfold f in Hk. destruct (unembed k) as [x y].
        destruct (prov x) as [s1|] eqn:H1, (prov y) as [s2|] eqn:H2; try discriminate.
        destruct sentences_discrete; last discriminate.
        apply (H s2); apply Hprov.
        + now exists y.
        + exists x. congruence.  
    Qed.
  End CTsecond.
End CT.

Section CTrepr.
  Variable fs : FS.

  Definition weakRepr (P : nat -> Prop) :=
    exists (repr : nat -> sentences), forall x, P x <-> provable (repr x).
  Definition valueRepr (f : nat -> nat -> option bool) :=
    exists (repr : nat -> bool -> sentences),
    forall x y, (exists k, f x k = Some y) -> provable (repr x y) /\ provable (neg (repr x (negb y))).

  Lemma complete_repr_weak_value f : fstationary f ->
    completeness -> weakRepr (fun x => exists k, f x k = Some true) -> valueRepr f.
  Proof.
    intros Hstat complete [repr Hrepr].
    exists ((fun x (b : bool) => if b then repr x else neg (repr x))).
    intros x [] [k1 Hk1]; split; cbn.
    - firstorder.
    - destruct (complete (neg (repr x))); last easy.
      exfalso.
      eapply (deepen_provability); first exact H.
      apply Hrepr. eauto.
    - apply deep_provability_iff; first assumption.
      intros [k2 Hk2]%Hrepr.
      destruct (Compare_dec.le_ge_dec k1 k2) as [Hk|Hk].
      + specialize (Hstat x k1 k2 false Hk1 Hk). congruence.
      + specialize (Hstat x k2 k1 true Hk2 Hk). congruence.
    - apply deep_provability_iff; first exact complete.
      intros [k2 Hk2]%Hrepr.
      destruct (Compare_dec.le_ge_dec k1 k2) as [Hk|Hk].
      + specialize (Hstat x k1 k2 false Hk1 Hk). congruence.
      + specialize (Hstat x k2 k1 true Hk2 Hk). congruence.
  Qed.

  (* weakRepr -/> valueRepr in above sense: choose FS neg s := \False which is unprovable*)
  (* Can we do it without choosing FS? Maybe not, we need a more concrete idea on how general of a theorem we want to show (arbitraty FS? f? instead of existence of counter-examples) *)
  (* valueRepr -/> weakRepr: does not hold, although proving this (in Coq?) is
     going to be difficult *)
  (* Idea: we need to encode a hard (TM) problem into the inputs there valueRepr is free to do anything and choose provability such that semi-deciding provability already leads to a contradiction *)
  (* We _will_ have to do something related to computability because otherwise weak representability could just decide by itself whether p holds and return apropriatly *)

End CTrepr.

Check CGexpl.

From Undecidability.FOL.Util Require Import Syntax_facts FullDeduction FullDeduction_facts FullTarski FullTarski_facts Axiomatisations FA_facts.
From Undecidability.FOL Require Import PA.

Definition Q := list_theory Qeq.

Lemma list_theory_enumerable {Σ_funcs : funcs_signature} {Σ_preds : preds_signature} A : 
  enumerable (list_theory A).
Proof.
  exists (List.nth_error A).
  intros x. split.
  - apply List.In_nth_error.
  - intros [k Hk]. eapply List.nth_error_In, Hk.
Qed.

Print peirce. 

Definition Qfs_intu : FS.
Proof.
  eapply fs_fo with (T := Q) (peirce := intu).
  - apply list_theory_enumerable.
  - intros x y. decide equality.
  - cbn. exists (fun k => match k with 
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
  - intros x y. decide equality.
  - exists (fun k => Some Eq).
    intros []. now exists 0.   
  - intros H.
    eapply tsoundness with (D := nat) (I := interp_nat) (rho := fun n => 0) in H.
    + assumption.
    + (* Q is subset of satisfiable formulas *) apply nat_is_Q_model. 
Defined.
Definition Qfs_class : (forall P, P \/ ~P) -> FS.
Proof.
  intros LEM. 
  eapply fs_fo with (T := Q) (peirce := class).
  - apply list_theory_enumerable.
  - intros x y. decide equality.
  - cbn. exists (fun k => match k with 
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
  - intros x y. decide equality.
  - exists (fun k => Some Eq).
    intros []. now exists 0.   
  - intros H.
    (* might be possible without assuming LEM *)
    eapply tsoundness_class with (D := nat) (I := interp_nat) (rho := fun n => 0) in H.
    + assumption.
    + assumption.
    + apply nat_is_Q_model. 
Defined.


Section Qexpl.
  Existing Instance Qfs_intu.

  Variable theta : nat -> nat -> nat -> option bool.

  Hypothesis theta_stationary : forall c, fstationary (theta c).
  Hypothesis theta_univ : forall (f : nat -> nat -> option bool), fstationary f ->
            exists c, forall x y, freturns f x y <-> freturns (theta c) x y.
  Arguments theta_univ : clear implicits.

  Hypothesis Hrepr : forall c, Sigma (repr : nat -> bool -> sentences),
      forall x y, freturns (theta c) x y -> provable (repr x y) /\ provable (neg (repr x (negb y))).
  Lemma Qexpl : exists s, ~provable s /\ ~provable (neg s).
  Proof.
    eapply CGexpl; eassumption.
  Qed.
End Qexpl.


Goal True.
Proof.
  pose proof Qexpl.
  unfold sentences, neg, provable in H.
  unfold Qfs_intu, fs_fo in H.
  unfold form_provable, form_neg in H. cbn in H.
  Check H.
Abort.