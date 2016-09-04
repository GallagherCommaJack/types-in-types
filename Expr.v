Set Implicit Arguments.
Require Import Prelude.
Require Export Autosubst.Autosubst.

Set Boolean Equality Schemes.
Scheme Equality for nat.

Definition name := nat.

Inductive exp : Type :=
  Bind : var -> exp
| Sort : nat -> exp
| Free : name -> exp

| Pi : exp -> {bind 1 of exp} -> exp
(* | Lam : exp -> {bind exp} -> exp *)
| Lam : {bind 1 of exp} -> exp
| App  : exp -> exp -> exp

| Sigma : exp -> {bind exp} -> exp
| Pair__sigma : exp ->  exp -> exp
| Rec__sigma : {bind 2 of exp} -> exp -> exp

| Path : exp -> exp -> exp
| Rec__path : exp -> exp -> exp
| Refl__path : exp -> exp
 
(* | Empty :  exp *)
(* | empty_rec : exp -> exp *)

| Desc : exp
| Ind__desc : exp
| Sum__desc : exp -> exp -> exp
| Prd__desc : exp -> exp -> exp
| Unit__desc : exp
| Fix__desc : exp -> exp
| Rec__desc : exp
            -> {bind 4 of exp} -> {bind 4 of exp}
            -> exp
            -> {bind 2 of exp}
            -> exp -> exp

| Mu : exp -> exp -> exp
| Wrap__mu : exp -> exp
| Inl__mu : exp -> exp
| Inr__mu : exp -> exp
| Pair__mu : exp -> exp -> exp
| Unit__mu : exp
| Fix__mu : exp -> exp
| Rec__mu : {bind 2 of exp}
          -> {bind 2 of exp} -> {bind 2 of exp}
          -> {bind 4 of exp}
          -> exp
          -> {bind 2 of exp}
          -> exp -> exp.

Hint Resolve internal_nat_dec_lb internal_nat_dec_bl.

Lemma exp_dec_lb : forall x y, x = y -> exp_beq x y. destruct 1; induction x; simpl; f_equal; rewrite asms; auto. Qed.
Hint Resolve exp_dec_lb.

Hint Extern 1 => match goal with [H: (_ && _)        |- _] => apply andb_prop in H; destruct H end.
Hint Extern 1 => match goal with [H: (_ && _) = true |- _] => apply andb_prop in H; destruct H end.

Lemma exp_dec_bl : forall x y, exp_beq x y -> x = y. unfold is_true; induction x; destruct y; simpl; intros; 
                                               discriminate || f_equal; destr bands; auto. Qed.
Hint Resolve exp_dec_bl.  

Lemma exp_eqnP : Equality.axiom exp_beq.
Proof. intros x y; apply (iffP idP); auto. Qed.

Canonical exp_eqMixin := EqMixin exp_eqnP.
Canonical exp_eqType := EqType exp exp_eqMixin.

Instance Ids_exp : Ids exp. derive. Defined.
Instance Rename_exp : Rename exp. derive. Defined.
Instance Subst_exp : Subst exp. derive. Defined.
Instance SubstLemmas_exp : SubstLemmas exp. derive. Qed.

Tactic Notation "arewrite" := autorewrite with autosubst.

Infix ":>>" := Pi (at level 20, right associativity).
Infix ":#>" := Lam (at level 30, right associativity).
Infix ":$:" := App (at level 50, left associativity).
Notation "<< a ;; b >>" := (Pair__sigma a b).

(* Notation Prd A B := (Sigma A (B.[ren (+1)])). *)
(* Infix ":*:" := Prd (at level 10). *)

Notation wk n := (ren (+ n)).

Notation S_p1 e := (Rec__sigma (Bind 1) e).
Notation S_p2 e := (Rec__sigma (Bind 0) e).

(* Fixpoint All (d : desc) (P : {bind exp}) (e : exp) := *)
(*   match d with  *)
(*       d_One => Unit *)
(*     | d_Ind => P.[e/] *)
(*     | d_Sum d1 d2 => Split *)
(*                       (All d1 P.[up (wk 1)] (Bind 0)) *)
(*                       (All d2 P.[up (wk 1)] (Bind 0)) *)
(*                       e *)
(*     | d_Prd d1 d2 => S_rec (Prd (All d1 P.[up (wk 2)] (Bind 1)) (All d2 P.[up (wk 2)] (Bind 0))) e *)
(*   end. *)

(* Fixpoint rall (d : desc) (r : {bind exp}) (e : exp) := *)
(*   match d with *)
(*       d_One => unit *)
(*     | d_Ind => r.[e/] *)
(*     | d_Sum d1 d2 => Split *)
(*                       (* (All (d_Sum d1 d2) P (Bind 0))  *) *)
(*                       (rall d1 r.[up (wk 1)] (Bind 0)) *)
(*                       (rall d2 r.[up (wk 1)] (Bind 0)) *)
(*                       e *)
(*     | d_Prd d1 d2 => S_rec (S_mk (rall d1 r.[up (wk 2)] (Bind 1)) (rall d2 r.[up (wk 2)] (Bind 0))) e *)
(*   end. *)
