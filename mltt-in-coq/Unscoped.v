Require Export Prelude.

Inductive exp : Set :=
| var : forall(ix : nat), exp
| typ : forall(level : nat), exp

| pi : forall(A B : exp), exp
| lam : forall(A b : exp), exp
| app : forall(f x : exp), exp

| sigma : forall(A B : exp), exp
| smk : forall(B a b : exp), exp
(* Γ ⊢ p ∈ (a : A) (b : B a) -> C (smk B a b) , Γ ⊢ s ∈ σ A B ⊃ Γ ⊢ srec C p s ∈ C s *)
| srec : forall(C p s : exp), exp

| wt : forall(A B : exp), exp
(* Γ ⊢ a ∈ A , Γ ⊢ f ∈ B a -> wt A B ⊃ Γ ⊢ sup B a f ∈ wt A B *)
| sup : forall(B a f : exp), exp
(* Γ ⊢ s ∈ (a : A) (f : B a -> wt A B) (f' : (b : B a) -> C (f b)) , Γ ⊢ w ∈ wt A B ⊃ Γ ⊢ wrec C s w ∈ C w *)
| wrec : forall(C s w : exp), exp

| bool : exp
| true : exp
| false : exp
| brec : forall(C t f b : exp), exp

| top : exp
| unit : exp
| urec : forall(C u t : exp), exp

| bot : exp
| exf : forall(C f : exp), exp.

Definition exp_size (e : exp) : nat.
  induction e; [exact 1|exact 1| | | | | | | | | | | | | | | | | |];
  repeat match goal with
            [IH : nat |- _] => apply (fun x => x + IH); clear IH
         end; apply 1. Defined.

Print exp_size.
Extraction exp_size.
 (* I think this definition is pretty cool :) *)

Notation "a # b" := (smk _ a b) (at level 20, right associativity).
Infix "@" := app (at level 15, left associativity).
Notation "&" := var.

Definition and_sumor A1 A2 P1 P2 : A1 + {P1} -> A2 + {P2} -> (A1 * A2) + {P1 \/ P2}.
  repeat (destruct 1; auto). Defined.

Arguments and_sumor {A1} {A2} {P1} {P2} s1 s2.
Infix "&&t" := and_sumor (at level 500, left associativity).

Definition prop_and {A B C D} : {A} + {B} -> {C} + {D} -> {A /\ C} + {B \/ D}. 
  repeat (destruct 1; auto). Defined.
Infix "&&" := prop_and.

Local Hint Extern 1 => subst; (reflexivity || congruence).

(* would use "decide equality" but that has worse computational properties *)
Definition exp_eq_dec (e1 e2 : exp) : {e1 = e2} + {e1 <> e2}.
  generalize dependent e2; induction e1; destruct e2;
  (* off-diagonal cases *)
  try (right; inversion 1; fail);
  (* trivial cases *)
  try (left;reflexivity);
  (* vars, typs, etc *)
  match goal with [n1 : nat , n2 : nat |- _] => destruct (Nat.eq_dec n1 n2); [left|right]; eauto | _ => idtac end;
  Inster_all;
  (* everything else *)
  repeat match goal with [H1: {_} + {_} , H2: {_} + {_} |- _] => remember (prop_and H1 H2) as H12; clear HeqH12; clear H1; clear H2 end;
  destr_hyps;
  try (left; repeat match goal with [H: _ = _ |- _] => rewrite H; clear H end; reflexivity);
  try (right; injection 1; intuition).
Defined.

Infix "==" := (exp_eq_dec) (at level 50).

(* weakening and substitution have the same recursion structure - lets only write it once *)
Fixpoint vars_op (op : forall(d ix : nat), exp) (d : nat) (e : exp) : exp :=
  match e with
    | & i => op d i

    | pi a b => pi (vars_op op d a) (vars_op op (S d) b)
    | lam A b => lam (vars_op op d A) (vars_op op (S d) b)
    | (f @ x) => app (vars_op op d f) (vars_op op d x)

    | sigma a b => sigma (vars_op op d a) (vars_op op d b)
    | (smk B a b) => smk (vars_op op d B) (vars_op op d a) (vars_op op d b)
    | srec c p s => srec (vars_op op d c) (vars_op op d p) (vars_op op d s)

    | wt a b => wt (vars_op op d a) (vars_op op d b)
    | sup B a f => sup (vars_op op d B) (vars_op op d a) (vars_op op d f)
    | wrec c s w => wrec (vars_op op d c) (vars_op op d s) (vars_op op d w)

    | brec c t f b => brec (vars_op op d c) (vars_op op d t) (vars_op op d f) (vars_op op d b)
    | urec c u t => urec (vars_op op d c) (vars_op op d u) (vars_op op d t)
    | exf c f => exf (vars_op op d c) (vars_op op d f)

    | _ => e
  end.

Definition wk_var (n d ix : nat) : exp := if le_dec d ix then var (n + ix) else var ix.
Definition wk_deep (n : nat) : nat -> exp -> exp := vars_op (wk_var n).

Definition subst_var (v : exp) (d i : nat) : exp := match lt_eq_lt_dec i d with
                                                    | inleft (left _) => var i
                                                    | inleft (right _) => wk_deep d 0 v
                                                    | inright _ => var (pred i)
                                                  end.

Definition subst_deep (v : exp) : nat -> exp -> exp := vars_op (subst_var v).

Hint Unfold wk_deep subst_deep.
Notation "x |> v // d" := (subst_deep v d x) (left associativity, at level 40).

Lemma wk_var_fold : forall n, (fun d ix => if le_dec d ix then &(n + ix) else &ix) = wk_var n. reflexivity. Qed.
Lemma subst_var_fold : forall v, (fun d i => match lt_eq_lt_dec i d with
                                           | inleft (left _) => &i
                                           | inleft (right _) => wk_deep d 0 v
                                           | inright _ => &(pred i)
                                         end) = subst_var v. reflexivity. Qed.

Ltac fold_wk := repeat match goal with
                  | [|-context[vars_op (wk_var ?n)]] => replace (vars_op (wk_var n)) with (wk_deep n) by auto
                  | [|-context[fun d ix => if le_dec d ix then &(?n + ix) else &ix]] => 
                    replace (fun d ix => if le_dec d ix then &(n + ix) else &ix) with (wk_var n) by auto
                  | [H:context[vars_op (wk_var ?n)]|-_] => replace (vars_op (wk_var n)) with (wk_deep n) in H by auto
                  | [H:context[fun d ix => if le_dec d ix then &(?n + ix) else &ix]|-_] => 
                    replace (fun d ix => if le_dec d ix then &(n + ix) else &ix) with (wk_var n) in H by auto
                end.

                     (* | [|-context[fun d i => match lt_eq_lt_dec i d with *)
                     (*                       | inleft (left _) => &i *)
                     (*                       | inleft (right _) => wk_deep d 0 ?v *)
                     (*                       | inright _ => &(pred i) *)
                     (*                     end]] => *)
                     (*   replace (fun d i => match lt_eq_lt_dec i d with *)
                     (*                      | inleft (left _) => &i *)
                     (*                      | inleft (right _) => wk_deep d 0 v *)
                     (*                      | inright _ => &(pred i) *)
                     (*                    end) with (subst_var v) by auto *)

Ltac fold_subst := 
  repeat rewrite subst_var_fold in *;
  repeat match goal with
           | [|-context[vars_op (subst_var ?v)]] => replace (vars_op (subst_var v)) with (subst_deep v) by auto
           | [H:context[vars_op (subst_var ?v)]|-_] => replace (vars_op (subst_var v)) with (subst_deep v) in H by auto
         end.

Tactic Notation "unfold_ops" := unfold wk_deep,subst_deep,wk_var,subst_var in *.
Tactic Notation "fold_ops" := fold_wk; fold_subst.

