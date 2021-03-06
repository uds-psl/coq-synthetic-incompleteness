(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*             Yannick Forster            [+]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(*                             [+] Affiliation Saarland Univ. *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith ZArith Lia List.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import utils_tac utils_list gcd prime php utils_nat.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.H10.ArithLibs 
  Require Import Zp lagrange.

From Undecidability.H10.Dio 
  Require Import dio_logic dio_single.

From Undecidability.H10 
  Require Import H10 H10_undec.

From Undecidability.H10 
  Require Import H10Z.

From Undecidability.H10.ArithLibs 
  Require Import Zp lagrange.

Require Import Undecidability.Synthetic.Definitions.

Set Default Proof Using "Type".

Local Definition inj k n := 4 * n + k.

Lemma injection_spec k1 k2 n m : k1 < 4 -> k2 < 4 -> inj k1 n = inj k2 m -> k1 = k2 /\ n = m.
Proof.
  intros. unfold inj in *. lia.
Qed.

Section pos_injs.

  Fixpoint inj0 {n} (p : pos n) : pos (n * 4).
  Proof.
    destruct p.
    - exact pos0.
    - exact (pos_right _ (inj0 _ p)).
  Defined.

  Fixpoint inj1 {n} (p : pos n) : pos (n * 4).
  Proof.
    destruct p.
    - exact pos1.
    - exact (pos_right _ (inj1 _ p)).
  Defined.

  Fixpoint inj2 {n} (p : pos n) : pos (n * 4).
  Proof.
    destruct p.
    - exact pos2.
    - exact (pos_right _ (inj2 _ p)).
  Defined.

  Fixpoint inj3 {n} (p : pos n) : pos (n * 4).
  Proof.
    destruct p.
    - exact pos3.
    - exact (pos_right _ (inj3 _ p)).
  Defined.

End pos_injs.

Arguments dp_cnst {V P}.
Arguments dp_var {V P}.
Arguments dp_par {V P}.
Arguments dp_comp {V P}.

Module dionat := dio_single.

Notation dp_sq a := (dp_comp do_mul a a).
Notation sq a := (a * a)%Z.

Fixpoint to_Z_poly E n (p : dionat.dio_polynomial (pos n) E) : dio_polynomial (pos (n * 4)) E :=
  match p with
  | dionat.dp_nat n => dp_cnst (Z.of_nat n)
  | dionat.dp_var v => dp_add (dp_sq (dp_var (inj3 v))) (dp_add (dp_sq (dp_var (inj2 v))) (dp_add (dp_sq (dp_var (inj1 v))) (dp_sq (dp_var (inj0 v)))))
  | dionat.dp_par p => dp_par p
  | dionat.dp_comp o p1 p2 => dp_comp o (to_Z_poly p1) (to_Z_poly p2)
  end.

Lemma create_sol_correct E (n : nat) (?? : pos n -> nat) (??' : pos (n * 4) -> Z) :
  (forall i : pos n, Z.of_nat (?? i) = sq (??' (inj3 i)) + sq (??' (inj2 i)) + sq (??' (inj1 i)) + sq (??' (inj0 i)))%Z ->
  forall p : dionat.dio_polynomial (pos n) E, Z.of_nat (dio_single.dp_eval ?? (fun _ : E => 0) p) = dp_eval ??' (fun _ : E => 0%Z) (to_Z_poly p).
Proof.
  intros H p. 
  induction p as [ k | v | | [] ]; cbn; auto.
  - rewrite H; ring.
  - rewrite Nat2Z.inj_add; congruence.
  - rewrite Nat2Z.inj_mul; congruence.
Qed.

Lemma create_sol_exists (n : nat) (?? : pos n -> nat) : exists (??' : pos (n * 4) -> Z),
    (forall i : pos n, Z.of_nat (?? i) = sq (??' (inj3 i)) + sq (??' (inj2 i)) + sq (??' (inj1 i)) + sq (??' (inj0 i)))%Z.
Proof.
  induction n as [ | n IHn ].
  - exists (fun _ => 0%Z); intros p; invert pos p.
  - destruct (IHn (fun j => ?? (pos_nxt j))) as [??' H'].
    cbn [mult].
    destruct (lagrange_theorem_nat (?? pos0)) as (a & b & c & d & Hl).
    exists (fun j : pos (4 + n * 4) => 
       match pos_both _ _ j with 
        | inl pos0 => a 
        | inl pos1 => b 
        | inl pos2 => c 
        | inl _    => d 
        | inr j => ??' j 
      end).
    intros p; invert pos p; auto.
    rewrite Hl; ring.
Qed.

Lemma recover_sol_exists (n : nat) (??' : pos (n * 4) -> Z) : exists (?? : pos n -> nat),
    (forall i : pos n, Z.of_nat (?? i) = sq (??' (inj3 i)) + sq (??' (inj2 i)) + sq (??' (inj1 i)) + sq (??' (inj0 i)))%Z.
Proof.
  induction n as [ | n IHn ].
  - exists (fun _ => 0); intros p; invert pos p.
  - destruct (IHn (fun j => ??' (pos_right 4 j))) as [?? H].
    unshelve eexists.
    + intros p; invert pos p.
      * exact (Z.to_nat (sq (??' (inj3 pos0)) + sq (??' (inj2 pos0)) + sq (??' (inj1 pos0)) + sq (??' (inj0 pos0)))).
      * exact (?? p).
    + intros p; invert pos p.
      * rewrite Z2Nat.id; auto.
        pose proof (Z.square_nonneg (??' pos3)).
        pose proof (Z.square_nonneg (??' pos2)).
        pose proof (Z.square_nonneg (??' pos1)).
        pose proof (Z.square_nonneg (??' pos0)).
        nia.
      * apply H.
Qed.

Lemma create_sol (n : nat) (?? : pos n -> nat) : exists ??' : pos (n * 4) -> Z,
  forall p : dionat.dio_polynomial (pos n) (pos 0), Z.of_nat (dio_single.dp_eval ?? (fun _ => 0) p) = dp_eval ??' (fun _ => 0%Z) (to_Z_poly p).
Proof.
  destruct (create_sol_exists ??) as [??'].
  exists ??'; intro; now eapply create_sol_correct.
Qed.

Lemma recover_sol (n : nat) (??' : pos (n * 4) -> Z) : exists ?? : pos n -> nat,
  forall p : dionat.dio_polynomial (pos n) (pos 0), Z.of_nat (dio_single.dp_eval ?? (fun _ => 0) p) = dp_eval ??' (fun _ => 0%Z) (to_Z_poly p).
Proof.
  destruct (recover_sol_exists ??') as [??].
  exists ??; intro; now eapply create_sol_correct.
Qed.

Opaque Zmult.

Lemma H10_H10Z : H10 ??? H10Z.
Proof.
  unshelve eexists.
  - intros (n & p & q). 
    exists (n * 4).
    exact (dp_add (to_Z_poly p) (dp_mul (dp_cnst (-1)%Z) (to_Z_poly q))).
  - intros (n & p & q).
    simpl; split; intros [ ?? H ]; simpl in *.
    + destruct (create_sol ??) as [??' H'].
      exists ??'. 
      rewrite <- !H'; lia.
    + destruct (recover_sol ??) as [??' H'].
      exists ??'; simpl.
      apply Nat2Z.inj; rewrite !H'; lia.
Qed.

Check H10_H10Z.
