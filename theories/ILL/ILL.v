(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(* Certified Undecidability of Intuitionistic Linear Logic via Binary Stack Machines and Minsky Machines. Yannick Forster and Dominique Larchey-Wendling. CPP '19. http://uds-psl.github.io/ill-undecidability/ *)

Require Import List Permutation.

Set Implicit Arguments.

(* * Intuionistic Linear Logic *)

Local Infix "~p" := (@Permutation _) (at level 70).

(* We consider four fragments of ILL:
    - the (!,-o,&) fragment with or without cut
    - full fragment with or without cut
*)

Notation ill_vars := nat.

Inductive ill_connective := ill_with | ill_limp | ill_times | ill_plus.
Inductive ill_constant := ill_1 | ill_bot | ill_top.

Inductive ill_form : Set :=
  | ill_var  : ill_vars -> ill_form
  | ill_cst  : ill_constant -> ill_form
  | ill_ban  : ill_form -> ill_form
  | ill_bin  : ill_connective -> ill_form -> ill_form -> ill_form.

(* Symbols for cut&paste â   â   đ  īš  â  â  â¸  !   âŧ  â  âĸ *)

Notation "â" := (ill_cst ill_top).
Notation "â" := (ill_cst ill_bot).
Notation "đ" := (ill_cst ill_1).

Infix "&" := (ill_bin ill_with) (at level 50).
Infix "â" := (ill_bin ill_times) (at level 50).
Infix "â" := (ill_bin ill_plus) (at level 50).
Infix "â¸" := (ill_bin ill_limp) (at level 51, right associativity).

Notation "'!' x" := (ill_ban x) (at level 52).

Notation "ÂŖ" := ill_var.

Notation "âŧ x" := (map ill_ban x) (at level 60).

Notation "â" := nil (only parsing).

Reserved Notation "l 'âĸ' x" (at level 70, no associativity).

Section S_ill_restr_without_cut.

  (* These are the SILL rules in the CPP'19 paper w/o the cut *)

  Inductive S_ill_restr : list ill_form -> ill_form -> Prop :=

    | in_ill1_ax     : forall A,                        A::â âĸ A

    | in_ill1_perm   : forall Î Î A,              Î ~p Î     ->   Î âĸ A 
                                           (*-----------------------------*)
                                        ->                 Î âĸ A

    | in_ill1_limp_l : forall Î Î A B C,         Î âĸ A      ->   B::Î âĸ C
                                           (*-----------------------------*)    
                                      ->           A â¸ B::Î++Î âĸ C

    | in_ill1_limp_r : forall Î A B,                  A::Î âĸ B
                                           (*-----------------------------*)
                                        ->            Î âĸ A â¸ B

    | in_ill1_with_l1 : forall Î A B C,               A::Î âĸ C 
                                           (*-----------------------------*)
                                      ->           A&B::Î âĸ C

    | in_ill1_with_l2 : forall Î A B C,               B::Î âĸ C 
                                           (*-----------------------------*)
                                      ->           A&B::Î âĸ C
 
    | in_ill1_with_r : forall Î A B,            Î âĸ A     ->   Î âĸ B
                                           (*-----------------------------*)
                                      ->              Î âĸ A&B

    | in_ill1_bang_l : forall Î A B,                   A::Î âĸ B
                                           (*-----------------------------*)
                                      ->              !A::Î âĸ B

    | in_ill1_bang_r : forall Î A,                    âŧÎ âĸ A
                                           (*-----------------------------*)
                                      ->              âŧÎ âĸ !A

    | in_ill1_weak : forall Î A B,                       Î âĸ B
                                           (*-----------------------------*)
                                      ->             !A::Î âĸ B

    | in_ill1_cntr : forall Î A B,                 !A::!A::Î âĸ B
                                           (*-----------------------------*)
                                      ->               !A::Î âĸ B

  where "l âĸ x" := (S_ill_restr l x).

End S_ill_restr_without_cut.

Section S_ill_restr_with_cut.

  (* These are the SILL rules in the CPP'19 paper including the cut rule *)

  Inductive S_ill_restr_wc : list ill_form -> ill_form -> Prop :=

    | in_ill2_ax     : forall A,                        A::â âĸ A

    | in_ill2_cut : forall Î Î A B,              Î âĸ A    ->   A::Î âĸ B
                                           (*-----------------------------*)    
                                      ->              Î++Î âĸ B

    | in_ill2_perm   : forall Î Î A,              Î ~p Î     ->   Î âĸ A 
                                           (*-----------------------------*)
                                        ->                 Î âĸ A

    | in_ill2_limp_l : forall Î Î A B C,         Î âĸ A      ->   B::Î âĸ C
                                           (*-----------------------------*)    
                                      ->           A â¸ B::Î++Î âĸ C

    | in_ill2_limp_r : forall Î A B,                  A::Î âĸ B
                                           (*-----------------------------*)
                                        ->            Î âĸ A â¸ B

    | in_ill2_with_l1 : forall Î A B C,               A::Î âĸ C 
                                           (*-----------------------------*)
                                      ->           A&B::Î âĸ C

    | in_ill2_with_l2 : forall Î A B C,               B::Î âĸ C 
                                           (*-----------------------------*)
                                      ->           A&B::Î âĸ C
 
    | in_ill2_with_r : forall Î A B,            Î âĸ A     ->   Î âĸ B
                                           (*-----------------------------*)
                                      ->              Î âĸ A&B

    | in_ill2_bang_l : forall Î A B,                   A::Î âĸ B
                                           (*-----------------------------*)
                                      ->              !A::Î âĸ B

    | in_ill2_bang_r : forall Î A,                    âŧÎ âĸ A
                                           (*-----------------------------*)
                                      ->              âŧÎ âĸ !A

    | in_ill2_weak : forall Î A B,                       Î âĸ B
                                           (*-----------------------------*)
                                      ->             !A::Î âĸ B

    | in_ill2_cntr : forall Î A B,                 !A::!A::Î âĸ B
                                           (*-----------------------------*)
                                      ->               !A::Î âĸ B

  where "l âĸ x" := (S_ill_restr_wc l x).

End S_ill_restr_with_cut.

Section S_ill_without_cut.

  (* These are the rules for the whole ILL, without cut *)

  Inductive S_ill : list ill_form -> ill_form -> Prop :=

    | in_ill3_ax     : forall A,                        A::â âĸ A

    | in_ill3_perm   : forall Î Î A,              Î ~p Î     ->   Î âĸ A 
                                           (*-----------------------------*)
                                        ->                 Î âĸ A

    | in_ill3_limp_l : forall Î Î A B C,         Î âĸ A      ->   B::Î âĸ C
                                           (*-----------------------------*)    
                                      ->           A â¸ B::Î++Î âĸ C

    | in_ill3_limp_r : forall Î A B,                  A::Î âĸ B
                                           (*-----------------------------*)
                                        ->            Î âĸ A â¸ B

    | in_ill3_with_l1 : forall Î A B C,               A::Î âĸ C 
                                           (*-----------------------------*)
                                      ->           A&B::Î âĸ C

    | in_ill3_with_l2 : forall Î A B C,               B::Î âĸ C 
                                           (*-----------------------------*)
                                      ->           A&B::Î âĸ C
 
    | in_ill3_with_r : forall Î A B,            Î âĸ A     ->   Î âĸ B
                                           (*-----------------------------*)
                                      ->              Î âĸ A&B

    | in_ill3_bang_l : forall Î A B,                   A::Î âĸ B
                                           (*-----------------------------*)
                                      ->              !A::Î âĸ B

    | in_ill3_bang_r : forall Î A,                    âŧÎ âĸ A
                                           (*-----------------------------*)
                                      ->              âŧÎ âĸ !A

    | in_ill3_weak : forall Î A B,                       Î âĸ B
                                           (*-----------------------------*)
                                      ->             !A::Î âĸ B

    | in_ill3_cntr : forall Î A B,                 !A::!A::Î âĸ B
                                           (*-----------------------------*)
                                      ->               !A::Î âĸ B

    | in_ill3_times_l : forall Î A B C,            A::B::Î âĸ C 
                                           (*-----------------------------*)
                                      ->            AâB::Î âĸ C
 
    | in_ill3_times_r : forall Î Î A B,          Î âĸ A    ->   Î âĸ B
                                           (*-----------------------------*)
                                      ->              Î++Î âĸ AâB

    | in_ill3_plus_l :  forall Î A B C,         A::Î âĸ C  ->  B::Î âĸ C 
                                           (*-----------------------------*)
                                      ->            AâB::Î âĸ C

    | in_ill3_plus_r1 : forall Î A B,                 Î âĸ A  
                                           (*-----------------------------*)
                                      ->              Î âĸ AâB

    | in_ill3_plus_r2 : forall Î A B,                 Î âĸ B  
                                           (*-----------------------------*)
                                      ->              Î âĸ AâB

    | in_ill3_bot_l : forall Î A,                  â::Î âĸ A

    | in_ill3_top_r : forall Î,                       Î âĸ â

    | in_ill3_unit_l : forall Î A,                    Î âĸ A  
                                           (*-----------------------------*)
                                      ->           đ::Î âĸ A

    | in_ill3_unit_r :                                â âĸ đ

  where "l âĸ x" := (S_ill l x).

End S_ill_without_cut.

Section S_ill_with_cut.

  (* These are the rules for the whole ILL, without cut *)

  Inductive S_ill_wc : list ill_form -> ill_form -> Prop :=

    | in_ill4_ax     : forall A,                        A::â âĸ A

    | in_ill4_cut : forall Î Î A B,              Î âĸ A    ->   A::Î âĸ B
                                           (*-----------------------------*)    
                                      ->              Î++Î âĸ B

    | in_ill4_perm   : forall Î Î A,              Î ~p Î     ->   Î âĸ A 
                                           (*-----------------------------*)
                                        ->                 Î âĸ A

    | in_ill4_limp_l : forall Î Î A B C,         Î âĸ A      ->   B::Î âĸ C
                                           (*-----------------------------*)    
                                      ->           A â¸ B::Î++Î âĸ C

    | in_ill4_limp_r : forall Î A B,                  A::Î âĸ B
                                           (*-----------------------------*)
                                        ->            Î âĸ A â¸ B

    | in_ill4_with_l1 : forall Î A B C,               A::Î âĸ C 
                                           (*-----------------------------*)
                                      ->           A&B::Î âĸ C

    | in_ill4_with_l2 : forall Î A B C,               B::Î âĸ C 
                                           (*-----------------------------*)
                                      ->           A&B::Î âĸ C
 
    | in_ill4_with_r : forall Î A B,            Î âĸ A     ->   Î âĸ B
                                           (*-----------------------------*)
                                      ->              Î âĸ A&B

    | in_ill4_bang_l : forall Î A B,                   A::Î âĸ B
                                           (*-----------------------------*)
                                      ->              !A::Î âĸ B

    | in_ill4_bang_r : forall Î A,                    âŧÎ âĸ A
                                           (*-----------------------------*)
                                      ->              âŧÎ âĸ !A

    | in_ill4_weak : forall Î A B,                       Î âĸ B
                                           (*-----------------------------*)
                                      ->             !A::Î âĸ B

    | in_ill4_cntr : forall Î A B,                 !A::!A::Î âĸ B
                                           (*-----------------------------*)
                                      ->               !A::Î âĸ B

    | in_ill4_times_l : forall Î A B C,            A::B::Î âĸ C 
                                           (*-----------------------------*)
                                      ->            AâB::Î âĸ C
 
    | in_ill4_times_r : forall Î Î A B,          Î âĸ A    ->   Î âĸ B
                                           (*-----------------------------*)
                                      ->              Î++Î âĸ AâB

    | in_ill4_plus_l :  forall Î A B C,         A::Î âĸ C  ->  B::Î âĸ C 
                                           (*-----------------------------*)
                                      ->            AâB::Î âĸ C

    | in_ill4_plus_r1 : forall Î A B,                 Î âĸ A  
                                           (*-----------------------------*)
                                      ->              Î âĸ AâB

    | in_ill4_plus_r2 : forall Î A B,                 Î âĸ B  
                                           (*-----------------------------*)
                                      ->              Î âĸ AâB

    | in_ill4_bot_l : forall Î A,                  â::Î âĸ A

    | in_ill4_top_r : forall Î,                       Î âĸ â

    | in_ill4_unit_l : forall Î A,                    Î âĸ A  
                                           (*-----------------------------*)
                                      ->           đ::Î âĸ A

    | in_ill4_unit_r :                                â âĸ đ

  where "l âĸ x" := (S_ill_wc l x).

End S_ill_with_cut.

Definition rILL_cf_PROVABILITY (S : _*_) := let (Î,A) := S in S_ill_restr Î A.
Definition rILL_PROVABILITY (S : _*_) := let (Î,A) := S in S_ill_restr_wc Î A. 

Definition ILL_cf_PROVABILITY (S : _*_) := let (Î,A) := S in S_ill Î A.
Definition ILL_PROVABILITY (S : _*_) := let (Î,A) := S in S_ill_wc Î A. 
