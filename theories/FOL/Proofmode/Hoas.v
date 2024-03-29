From Undecidability.FOL Require Import Syntax.Core Tarski.FullCore.
Require Import Vector.

Local Notation vec := Vector.t.


Inductive bterm `{funcs_signature} :=
  | bVar : nat -> bterm
  | bFunc : forall (f : syms), vec bterm (ar_syms f) -> bterm
  | bEmbedT : term -> bterm.

Inductive bform `{funcs_signature, preds_signature, operators, falsity_flag} :=
  | bFal : bform
  | bAtom : forall (P : preds), vec bterm (ar_preds P) -> bform
  | bBin : binop -> bform  -> bform  -> bform
  | bQuant : quantop -> (bterm -> bform)  -> bform
  | bFree : (bterm -> bform)  -> bform
  | bEmbedForm : form -> bform.

Arguments bFunc {_} _ _.
Arguments bAtom {_} {_} {_} {_} _ _.

Fixpoint conv_term `{funcs_signature} i (b : bterm) : term :=
  match b with
  | bVar m => var (i - m)
  | bEmbedT t => t
  | bFunc f v => func f (Vector.map (conv_term i) v)
  end.

Fixpoint conv `{funcs_signature, preds_signature, operators} i (phi : bform) : form :=
  match phi with
  | bFal => falsity
  | bAtom p v => atom p (Vector.map (conv_term i) v)
  | bBin op t1 t2 => bin op (conv i t1) (conv i t2)
  | bQuant op f => quant op (conv (S i) (f (bVar (S i))))
  | bFree f => conv (S i) (f (bVar (S i)))
  | bEmbedForm phi => phi
  end.

Declare Scope hoas_scope.
Delimit Scope hoas_scope with hoas.
Open Scope hoas_scope.

Notation "'Free' x .. y , p" := (bFree (fun x => .. (bFree (fun y => p)) ..)%hoas)
(at level 50, x binder, left associativity,
  format "'[' 'Free'  '/  ' x  ..  y ,  '/  ' p ']'") : hoas_scope.
Notation "'∀'' x .. y , p" := (bQuant All (fun x => .. (bQuant All (fun y => p)) ..)%hoas)
(at level 50, x binder,  left associativity,
  format "'[' '∀''  '/  ' x  ..  y ,  '/  ' p ']'") : hoas_scope.
Notation "'∃'' x .. y , p" := (bQuant Ex (fun x => .. (bQuant Ex (fun y => p)) ..)%hoas)
(at level 50, x binder, left associativity,
  format "'[' '∃''  '/  ' x  ..  y ,  '/  ' p ']'") : hoas_scope.
Notation "⊥" := (bFal) : hoas_scope.
Notation "A ∧ B" := (bBin Conj A%hoas B%hoas) (at level 41) : hoas_scope.
Notation "A ∨ B" := (bBin Disj A%hoas B%hoas) (at level 42) : hoas_scope.
Notation "A '→' B" := (bBin Impl A%hoas B%hoas) (at level 43, right associativity) : hoas_scope.
Notation "¬ A" := ((A → ⊥)%hoas) (at level 42) : hoas_scope.
Notation "A '↔' B" := ((A → B)%hoas ∧ (B → A)%hoas) (at level 43) : hoas_scope.

Definition convert `{funcs_signature, preds_signature, operators} f := (@conv _ _ _ 0 f).
Arguments convert {_ _ _} f%hoas.

Notation "<< f" := (ltac:(let y := eval cbn -[subst_form] in (convert f) in exact y)) (at level 200, only parsing).


Coercion bEmbedT : term >-> bterm.
Definition vec_term `{funcs_signature} := Vector.t term.
Definition vec_bterm `{funcs_signature} := Vector.t bterm.
Definition vec_bEmbedT' `{funcs_signature} : forall n, vec_term n -> vec_bterm n := @Vector.map term bterm bEmbedT.
Coercion vec_bEmbedT `{funcs_signature} := vec_bEmbedT'.
Coercion bEmbedForm : form >-> bform.
