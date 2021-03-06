(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Permutation Arith.

From Undecidability.ILL Require Import ILL.

Set Implicit Arguments.

Local Infix "~p" := (@Permutation _) (at level 70).

Inductive cll_connective := cll_with | cll_plus | cll_limp | cll_times | cll_par.
Inductive cll_constant := cll_1 | cll_0 | cll_bot | cll_top.
Inductive cll_modality := cll_bang | cll_qmrk | cll_neg.

Notation cll_vars := nat.

Inductive cll_form : Set :=
  | cll_var  : cll_vars -> cll_form
  | cll_cst  : cll_constant  -> cll_form
  | cll_una  : cll_modality -> cll_form -> cll_form
  | cll_bin  : cll_connective -> cll_form -> cll_form -> cll_form.

(* Symbols for cut&paste â   â  đ īš  â  â  â¸ ! âŧ âŊ â â  âĸ *)

(* These notations replace the ILL notations *)

(* Variables *)

Notation "'ÂŖ' x" := (cll_var x) (at level 1).

(* Constants *)

Notation "â" := (cll_cst cll_top).
Notation "â" := (cll_cst cll_bot).
Notation "đ" := (cll_cst cll_1).
Notation "đ" := (cll_cst cll_0).

(* Unary connectives: linear negation and modalities *)
(* ? cannot be used because it is reserved by Coq so we use âŊ instead *)

Notation "'â' x" := (cll_una cll_neg x) (at level 50, format "â x").
Notation "'!' x" := (cll_una cll_bang x) (at level 52).
Notation "'âŊ' x" := (cll_una cll_qmrk x) (at level 52).

(* Binary connectives *)

Infix "&" := (cll_bin cll_with) (at level 50).
Infix "â" := (cll_bin cll_par) (at level 50).
Infix "â" := (cll_bin cll_times) (at level 50).
Infix "â" := (cll_bin cll_plus) (at level 50).
Infix "â¸" := (cll_bin cll_limp) (at level 51, right associativity).

(* Modalities iterated over lists *)

Notation "âŧ x" := (map (cll_una cll_bang) x) (at level 60).
Notation "â x" := (map (cll_una cll_qmrk) x) (at level 60).

(* The empty list *)

Notation "â" := nil.

Local Reserved Notation "Î âĸ Î" (at level 70, no associativity).

Section S_cll_restr_without_cut.

  (* CLL rules restricted to the (!,&,-o) fragment without cut *)

  Inductive S_cll_restr : list cll_form -> list cll_form -> Prop :=

    | in_cll1_ax     : forall A,                        A::â âĸ A::â

    | in_cll1_perm  : forall Î Î Î' Î',      Î ~p Î' -> Î ~p Î' ->   Î âĸ Î 
                                           (*-----------------------------*)
                                      ->                 Î' âĸ Î'

    | in_cll1_limp_l : forall Î Î Î' Î' A B,  Î âĸ A::Î      ->   B::Î' âĸ Î'
                                           (*-----------------------------*)    
                                      ->           A â¸ B::Î++Î' âĸ Î++Î'

    | in_cll1_limp_r : forall Î Î A B,               A::Î âĸ B::Î
                                           (*-----------------------------*)
                                      ->            Î âĸ A â¸ B::Î

    | in_cll1_with_l1 : forall Î Î A B,               A::Î âĸ Î 
                                           (*-----------------------------*)
                                      ->           A&B::Î âĸ Î

    | in_cll1_with_l2 : forall Î Î A B,              B::Î âĸ Î 
                                           (*-----------------------------*)
                                      ->           A&B::Î âĸ Î
 
    | in_cll1_with_r : forall Î Î A B,        Î âĸ A::Î     ->   Î âĸ B::Î
                                           (*-----------------------------*)
                                      ->              Î âĸ A&B::Î

    | in_cll1_bang_l : forall Î A Î,                 A::Î âĸ Î
                                           (*-----------------------------*)
                                      ->            !A::Î âĸ Î

    | in_cll1_bang_r : forall Î A,                    âŧÎ âĸ A::nil               (* since ? is absent, only ??Î = nil works *)
                                           (*-----------------------------*)
                                      ->              âŧÎ âĸ !A::nil

    | in_cll1_weak_l : forall Î A Î,                   Î âĸ Î
                                           (*-----------------------------*)
                                      ->           !A::Î âĸ Î

    | in_cll1_cntr_l : forall Î A Î,             !A::!A::Î âĸ Î
                                           (*-----------------------------*)
                                      ->             !A::Î âĸ Î

  where "l âĸ m" := (S_cll_restr l m).

End S_cll_restr_without_cut.

Section S_cll_without_cut_on_ill_syntax.

  (* CLL rules restricted to the (đ,?,â) free fragment without cut 
      which shares the same formula language as ILL, but of course 
      not the same rules *)

  Inductive S_cll_2 : list cll_form -> list cll_form -> Prop :=

    | in_cll2_ax     : forall A,                        A::â âĸ A::â

    | in_cll2_perm  : forall Î Î Î' Î',      Î ~p Î' -> Î ~p Î' ->   Î âĸ Î 
                                           (*-----------------------------*)
                                      ->                 Î' âĸ Î'

    | in_cll2_limp_l : forall Î Î Î' Î' A B,  Î âĸ A::Î      ->   B::Î' âĸ Î'
                                           (*-----------------------------*)    
                                      ->           A â¸ B::Î++Î' âĸ Î++Î'

    | in_cll2_limp_r : forall Î Î A B,               A::Î âĸ B::Î
                                           (*-----------------------------*)
                                      ->            Î âĸ A â¸ B::Î

    | in_cll2_with_l1 : forall Î Î A B,               A::Î âĸ Î 
                                           (*-----------------------------*)
                                      ->           A&B::Î âĸ Î

    | in_cll2_with_l2 : forall Î Î A B,              B::Î âĸ Î 
                                           (*-----------------------------*)
                                      ->           A&B::Î âĸ Î
 
    | in_cll2_with_r : forall Î Î A B,        Î âĸ A::Î     ->   Î âĸ B::Î
                                           (*-----------------------------*)
                                      ->              Î âĸ A&B::Î

    | in_cll2_times_l : forall Î A B Î,            A::B::Î âĸ Î 
                                           (*-----------------------------*)
                                      ->            AâB::Î âĸ Î
 
    | in_cll2_times_r : forall Î Î Î' Î' A B,  Î âĸ A::Î    ->   Î' âĸ B::Î'
                                           (*-----------------------------*)
                                      ->          Î++Î' âĸ AâB::Î++Î'

    | in_cll2_plus_l :  forall Î A B Î,         A::Î âĸ Î  ->  B::Î âĸ Î 
                                           (*-----------------------------*)
                                      ->            AâB::Î âĸ Î

    | in_cll2_plus_r1 : forall Î A B Î,               Î âĸ A::Î  
                                           (*-----------------------------*)
                                      ->              Î âĸ AâB::Î

    | in_cll2_plus_r2 : forall Î A B Î,               Î âĸ B::Î  
                                           (*-----------------------------*)
                                      ->              Î âĸ AâB::Î

    | in_cll2_bot_l : forall Î Î,                     â::Î âĸ Î

    | in_cll2_top_r : forall Î Î,                      Î âĸ â::Î

    | in_cll2_unit_l : forall Î Î,                       Î âĸ Î  
                                           (*-----------------------------*)
                                        ->           đ::Î âĸ Î

    | in_cll2_unit_r :                                  â âĸ đ::â


    | in_cll2_bang_l : forall Î A Î,                 A::Î âĸ Î
                                           (*-----------------------------*)
                                      ->            !A::Î âĸ Î

    | in_cll2_bang_r : forall Î A,                    âŧÎ âĸ A::nil               (* since ? is absent, only ??Î = nil works *)
                                           (*-----------------------------*)
                                      ->              âŧÎ âĸ !A::nil

    | in_cll2_weak_l : forall Î A Î,                   Î âĸ Î
                                           (*-----------------------------*)
                                      ->           !A::Î âĸ Î

    | in_cll2_cntr_l : forall Î A Î,             !A::!A::Î âĸ Î
                                           (*-----------------------------*)
                                      ->             !A::Î âĸ Î

  where "l âĸ m" := (S_cll_2 l m).

End S_cll_without_cut_on_ill_syntax.

Section cut_free_cll.

  (* All the rules of Cut-free CLL *)

  Reserved Notation "Î âĸ Î" (at level 70, no associativity).

  Inductive S_cll : list cll_form -> list cll_form -> Prop :=

    | in_cll_ax    : forall A,                         A::â âĸ A::â

(*
    | in_cll_cut   : forall Î Î Î' Î' A,        Î âĸ A::Î    ->   A::Î' âĸ Î'
                                             (*-----------------------------*)
                                        ->           Î++Î' âĸ Î++Î'
*)

    | in_cll_perm  : forall Î Î Î' Î',        Î ~p Î'  ->  Î ~p Î'  ->  Î âĸ Î 
                                             (*-----------------------------*)
                                        ->              Î' âĸ Î'

    | in_cll_neg_l :   forall Î Î A,                    Î âĸ A::Î
                                             (*-----------------------------*)
                                        ->          âA::Î âĸ Î

    | in_cll_neg_r :   forall Î Î A,                 A::Î âĸ Î
                                             (*-----------------------------*)
                                        ->              Î âĸ âA::Î


    | in_cll_limp_l : forall Î Î Î' Î' A B,   Î âĸ A::Î      ->   B::Î' âĸ Î'
                                             (*-----------------------------*)
                                        ->         A â¸ B::Î++Î' âĸ Î++Î'

    | in_cll_limp_r : forall Î Î A B,                 A::Î âĸ B::Î
                                             (*-----------------------------*)
                                        ->            Î âĸ A â¸ B::Î

    | in_cll_with_l1 : forall Î Î A B,                  A::Î âĸ Î 
                                             (*-----------------------------*)
                                        ->           A&B::Î âĸ Î

    | in_cll_with_l2 : forall Î Î A B,                  B::Î âĸ Î 
                                             (*-----------------------------*)
                                        ->           A&B::Î âĸ Î
 
    | in_cll_with_r : forall Î Î A B,          Î âĸ A::Î     ->   Î âĸ B::Î
                                             (*-----------------------------*)
                                        ->              Î âĸ A&B::Î

    | in_cll_times_l : forall Î A B Î,               A::B::Î âĸ Î 
                                             (*-----------------------------*)
                                        ->            AâB::Î âĸ Î
 
    | in_cll_times_r : forall Î Î Î' Î' A B,   Î âĸ A::Î    ->   Î' âĸ B::Î'
                                             (*-----------------------------*)
                                        ->         Î++Î' âĸ AâB::Î++Î'

    | in_cll_par_l : forall Î Î Î' Î' A B,     A::Î âĸ Î    ->   B::Î' âĸ Î'
                                             (*-----------------------------*)
                                        ->         AâB::Î++Î' âĸ Î++Î'

    | in_cll_par_r : forall Î A B Î,                   Î âĸ A::B::Î 
                                             (*-----------------------------*)
                                        ->             Î âĸ AâB::Î

    | in_cll_plus_l :  forall Î A B Î,          A::Î âĸ Î  ->  B::Î âĸ Î 
                                             (*-----------------------------*)
                                        ->          AâB::Î âĸ Î

    | in_cll_plus_r1 : forall Î A B Î,                  Î âĸ A::Î  
                                             (*-----------------------------*)
                                        ->              Î âĸ AâB::Î

    | in_cll_plus_r2 : forall Î A B Î,                  Î âĸ B::Î  
                                             (*-----------------------------*)
                                        ->              Î âĸ AâB::Î

    | in_cll_bot_l : forall Î Î,                     â::Î âĸ Î

    | in_cll_top_r : forall Î Î,                        Î âĸ â::Î

    | in_cll_unit_l : forall Î Î,                       Î âĸ Î  
                                             (*-----------------------------*)
                                        ->           đ::Î âĸ Î

    | in_cll_unit_r :                                   â âĸ đ::â

    | in_cll_zero_l :                        (*-----------------------------*)
                                             (* *)      đ::â âĸ â

    | in_cll_zero_r : forall Î Î,                       Î âĸ Î  
                                             (*-----------------------------*)
                                        ->              Î âĸ đ::Î


    | in_cll_bang_l : forall Î A Î,                    A::Î âĸ Î
                                             (*-----------------------------*)
                                        ->            !A::Î âĸ Î

    | in_cll_bang_r : forall Î A Î,                     âŧÎ âĸ A::âÎ
                                             (*-----------------------------*)
                                        ->              âŧÎ âĸ !A::âÎ

    | in_cll_qmrk_l : forall Î A Î,                     A::âŧÎ âĸ âÎ
                                             (*-----------------------------*)
                                        ->              âŊA::âŧÎ âĸ âÎ

    | in_cll_qmrk_r : forall Î A Î,                    Î âĸ A::Î
                                             (*-----------------------------*)
                                        ->             Î âĸ âŊA::Î

    | in_cll_weak_l : forall Î A Î,                      Î âĸ Î
                                             (*-----------------------------*)
                                        ->           !A::Î âĸ Î

    | in_cll_weak_r : forall Î A Î,                      Î âĸ Î
                                             (*-----------------------------*)
                                        ->               Î âĸ âŊA::Î

    | in_cll_cntr_l : forall Î A Î,                !A::!A::Î âĸ Î
                                             (*-----------------------------*)
                                        ->             !A::Î âĸ Î

    | in_cll_cntr_r : forall Î A Î,                    Î âĸ âŊA::âŊA::Î
                                             (*-----------------------------*)
                                        ->             Î âĸ âŊA::Î

  where "Î âĸ Î" := (S_cll Î Î).

End cut_free_cll.

Definition rCLL_cf_PROVABILITY (S : _*_) := let (Î,Î) := S in S_cll_restr Î Î.
Definition CLL_cf_PROVABILITY (S : _*_) := let (Î,Î) := S in S_cll Î Î.
