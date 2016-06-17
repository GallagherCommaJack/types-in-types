Set Implicit Arguments.
Require Import Prelude.
Require Export Autosubst.Autosubst.

Variable (name : eqType).

Inductive exp : Type :=
  Bind : var -> exp
| Sort : nat -> exp
| Free : name -> exp

| Pi : exp -> {bind exp} -> exp
| Lam : exp -> {bind exp} -> exp
| App  : exp -> exp -> exp

| Sigma : exp -> {bind exp} -> exp
| S_mk : exp ->  exp -> exp
| S_p1 : exp -> exp
| S_p2 : exp -> exp

| Sum : exp -> exp -> exp
| Sum_inl : exp -> exp
| Sum_inr : exp -> exp
| Split : {bind exp} -> {bind exp} -> {bind exp} -> exp -> exp

| Unit : exp
| unit : exp

| Empty :  exp
| empty_rec : {bind exp} -> exp -> exp

| Mu : desc -> exp
| Wrap : exp -> exp
| Unwrap : exp -> exp
| mu : desc -> {bind exp} -> exp -> exp -> exp.

Infix ":>>" := Pi (at level 20).
Infix ":#>" := Lam (at level 30).
Infix ":$:" := App (at level 50).
Notation "<< a ;; b >>" := (S_mk a b).

Instance Ids_exp : Ids exp. derive. Defined.
Instance Rename_exp : Rename exp. derive. Defined.
Instance Subst_exp : Subst exp. derive. Defined.
Instance SubstLemmas_exp : SubstLemmas exp. derive. Qed.

Notation Prd A B := (Sigma A (B.[ren (+1)])).
Infix ":*:" := Prd (at level 10).

Fixpoint D_efunc (D : desc) (X : exp) : exp :=
  match D with
      d_One => Unit
    | d_Sum A B => Sum (D_efunc A X) (D_efunc B X)
    | d_Prd A B => Prd (D_efunc A X) (D_efunc B X)
    | d_Ind => X
  end.

Definition exp_dec_eq (e1 e2 : exp) : {e1 = e2} + {e1 <> e2}.
Proof.
  decide equality; match goal with [|-{?i1 = ?i2} + {_ <> _}] => destruct (i1 =P i2); [left|right] end; assumption.
Defined.

(* This is hilarious *)
Notation exp_eq := (fun e1 e2 => if exp_dec_eq e1 e2 then true else false).
(* destruct (exp_dec_eq e1 e2); [exact true|exact false]. Defined. *)

Hint Resolve andb_true_intro.
Lemma exp_eqnP : Equality.axiom exp_eq.
Proof. move=>x y. apply (iffP idP); destruct (exp_dec_eq x y); simpl; intro; congruence. Qed.

Canonical exp_eqMixin := EqMixin exp_eqnP.
Canonical exp_eqType := EqType exp exp_eqMixin.

Notation wk n := (ren (+ n)).

Section desc_exps.
  Variable (s : nat).
  Fixpoint All (d : desc) (P : {bind exp}) (e : exp) :=
    match d with 
        d_One => Unit
      | d_Ind => P.[e/]
      | d_Sum d1 d2 => Split
                        (Sort s)
                        (All d1 P.[up (wk 1)] (Bind 0))
                        (All d2 P.[up (wk 1)] (Bind 0))
                        e
      | d_Prd d1 d2 => Prd (All d1 P (S_p1 e)) (All d2 P (S_p2 e))
    end.

  Variables (P r : {bind exp}).
  Fixpoint rall (d : desc) (e : exp) :=
    match d with
        d_One => unit
      | d_Ind => r.[e/]
      | d_Sum d1 d2 => Split
                        (All (d_Sum d1 d2) P (Bind 0)) 
                        (rall d1 (Bind 0))
                        (rall d2 (Bind 0))
                        e
      | d_Prd d1 d2 => S_mk (rall d1 (S_p1 e)) (rall d2 (S_p2 e))
    end.
End desc_exps.
