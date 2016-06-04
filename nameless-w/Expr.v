Set Implicit Arguments.
Require Import Prelude.
Require Import Autosubst.Autosubst.

Variable (name : eqType).

Inductive Univ : Type := prop | set | typ.

Fixpoint Univ_beq (u1 u2 : Univ) : bool :=
  match u1,u2 with
      prop,prop|set,set|typ,typ => true
    | _,_ => false
  end.

Lemma univ_eqnP : Equality.axiom Univ_beq.
Proof. move=>x y; apply (iffP idP); unfold is_true; destruct x,y; simpl; intro; congruence. Qed.

Canonical univ_eqMixin := EqMixin univ_eqnP.
Canonical univ_eqType := EqType Univ univ_eqMixin.

Inductive exp : Type :=
  Bind : var -> exp
| Sort : Univ -> exp
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
| Split : {bind exp} -> {bind exp} -> {bind exp} -> exp

| Unit : exp
| unit : exp

| Empty :  exp
| empty_rec : {bind exp} -> exp -> exp

| Mu : desc -> exp
| Wrap : exp -> exp
| Unwrap : exp -> exp
| mu : desc -> exp -> exp -> exp -> exp.

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