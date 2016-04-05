Require Import Coq.Program.Program List.
Import ListNotations.
Require Import Monad Tactics.
Require Import Unscoped Evaluation.

Fixpoint progress (e: exp) : list exp :=
  join
    match e with
      | pi A B => [pi <$> progress A <*> pure B; pi A <$> progress B]
      | lam A b => [lam <$> progress A <*> pure b; lam A <$> progress b]
      | app f x => [app <$> progress f <*> pure x; app f <$> progress x
                   ; match f with lam A b => pure (b |> x // 0) | _ => [] end]

      | sigma A B => [sigma <$> progress A <*> pure B; sigma A <$> progress B]
      | smk B a b => [smk <$> progress B <*> pure a <*> pure b; smk B <$> progress a <*> pure b; smk B a <$> progress b]
      | srec C p s => [srec <$> progress C <*> pure p <*> pure s; srec C <$> progress p <*> pure s; srec C p <$> progress s; 
                      match s with (a # b) => pure (p @ a @ b) | _ => [] end]

      | wt A B => [wt <$> progress A <*> pure B; wt A <$> progress B]
      | sup B a f => [sup <$> progress B <*> pure a <*> pure f; sup B <$> progress a <*> pure f; sup B a <$> progress f]
      | wrec C s w => [wrec <$> progress C <*> pure s <*> pure w; wrec C <$> progress s <*> pure w; wrec C s <$> progress w;
                      match w with
                        | (sup B a f) => pure (s @ a @ lam (B @ a) (wrec (wk_deep 1 0 C) (wk_deep 1 0 s) (wk_deep 1 0 f @ &0)))
                        | _ => []
                      end]

      | brec C t f b => [brec <$> progress C <*> pure t <*> pure f <*> pure b; brec C <$> progress t <*> pure f <*> pure b;
                        brec C t <$> progress f <*> pure b; brec C t f <$> progress b;
                        match b with true => pure t | false => pure f | _ => [] end]
      | urec C u t => [urec <$> progress C <*> pure u <*> pure t; urec C <$> progress u <*> pure t; urec C u <$> progress t;
                      match t with unit => pure u | _ => [] end]

      | exf C f => [exf <$> progress C <*> pure f; exf C <$> progress f]
      | _ => []
    end.

Lemma join_fmap_unit M `(Monad M) A B x (xs: M (A -> B)) : join ((fun f => pure (f x)) <$> xs) = ((fun f => f x) <$> xs).
  replace (fun f => pure (f x)) with (@pure M H B ∘ (fun f => f x)) by auto; rewrite hom_comp; auto. Qed.

Definition concat_unit : forall A B x xs, concat (map (fun (f: A -> B) => [f x]) xs) = map (fun f => f x) xs := join_fmap_unit list list_monad.

Definition in_concat A x xss : @In A x (concat xss) <-> exists xs, In xs xss /\ In x xs.
  induction xss; split; simpl; try (inversion 1; subst; auto); intros; try (destr_logic; auto; fail).
  - apply in_app_or in H; destr_logic; eauto. try_hyps; destr_logic; eauto.
  - destr_logic; repeat subst; apply in_or_app; try (left;eauto;fail); right.
    + apply IHxss; eauto.
Qed.

Hint Resolve in_eq.
Hint Rewrite in_concat concat_unit map_map map_app.

Theorem progress_exhaustive : forall e1 e2, e1 ==> e2 -> In e2 (progress e1).
  induction 1; intros; simpl; try (simpl in *; auto; fail); 
  (* some simplifying rewrites *)
  repeat (rewrite concat_unit || rewrite map_map || rewrite map_app); auto;
  (* now we'll elim all the simple recursive cases *)
  try (repeat 
         ((apply in_or_app; left; match goal with [|-In _ (map ?e _)] => apply in_map with (f := e) end; auto; fail)
         || (apply in_or_app; right)); fail);
  (* elim rules will then live in the last part of the list *)
  try (repeat (apply in_or_app; right); auto; fail).
Qed. 

Hint Resolve in_map_iff.
Hint Rewrite in_map_iff in_app_iff.

Hint Extern 1 => match goal with [H: In _ [] |- _] => inversion H end.

Lemma and_or_split (A B C : Prop) : (A \/ B -> C) <-> ((A -> C) /\ (B -> C)). intuition. Qed.
Hint Rewrite and_or_split.

Ltac destr_ins := repeat match goal with [H: In _ (_ ++ _)|-_] => apply in_app_or in H; destruct H end.
Theorem progress_faithful : forall e1 e2, In e2 (progress e1) -> e1 ==> e2.
  induction e1; intros e2 He2; try (inversion He2; subst); simpl in *; repeat rewrite concat_unit in He2;
  repeat (autorewrite with core in *; destr_logic); subst; eauto.
  - destruct e1_1; inversion H; subst; eauto.
  - destruct e1_3; inversion H; subst; eauto.
  - destruct e1_3; inversion H; subst; eauto.
  - destruct e1_4; inversion H; subst; eauto.
  - destruct e1_3; inversion H; subst; eauto.
Qed.

Hint Resolve progress_exhaustive progress_faithful.

Lemma progress_reflect : forall e1 e2, In e2 (progress e1) <-> e1 ==> e2. split; auto. Qed.

Hint Rewrite progress_reflect.

Definition kleisli {M} `{Monad M} {A B C} (f : A -> M B) (g : B -> M C) : A -> M C := join ∘ fmap g ∘ f.

Infix ">=>" := kleisli (at level 40, left associativity).

Definition multi_progress : nat -> exp -> list exp := nat_rect _ (fun e => [e]) (fun n f' => f' >=> progress).
Hint Unfold multi_progress.

Reserved Notation "e1 =[ n ]=> e2" (at level 50).
Inductive n_steps e1 : nat -> exp -> Prop :=
| n_stop : e1 =[0]=> e1
| n_back : forall e2 e3 n, e1 ==> e2 -> e2 =[n]=> e3 -> e1 =[S n]=> e3
where "e1 =[ n ]=> e2" := (n_steps e1 n e2).
Hint Constructors n_steps.

Lemma n_step e1 e2 e3 n : e1 =[n]=> e2 -> e2 ==> e3 -> e1 =[S n]=> e3.
  induction 1; eauto. Qed.

Hint Resolve n_step.

Theorem n_steps_iff_progress_n : forall e1 e2 n, e1 =[ n ]=> e2 <-> In e2 (multi_progress n e1).
  intros; split. 
  - induction 1; subst; simpl; eauto.
    