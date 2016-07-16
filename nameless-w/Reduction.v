Require Import Prelude.
Require Import Expr.
Require Import Scoping.

(* Fixpoint canonize e := *)
(*   match e with *)
(*     | Wrap (Unwrap e') => canonize e' *)
(*     | Unwrap (Wrap e') => canonize e' *)
(*     | Lam b => Lam (canonize b) *)
(*     | A :>> B => canonize A :>> canonize B *)
(*     | f :$: x => canonize f :$: canonize x *)
(*     | Sigma A B => Sigma (canonize A) (canonize B) *)
(*     | S_mk a b => S_mk (canonize a) (canonize b) *)
(*     | S_p1 a => S_p1 (canonize a)  *)
(*     | S_p2 b => S_p2 (canonize b) *)
(*     | Sum A B => Sum (canonize A) (canonize B) *)
(*     | Sum_inl a => Sum_inl (canonize a) *)
(*     | Sum_inr b => Sum_inr (canonize b) *)
(*     | Split a b ab => Split (canonize a) (canonize b) (canonize ab) *)
(*     | empty_rec e => empty_rec (canonize e) *)
(*     (* | Wrap e => Wrap (canonize e) *) *)
(*     (* | Unwrap e => Unwrap (canonize e) *) *)
(*     | mu D r d => mu D (canonize r) (canonize d) *)
(*     | _ => e *)
(*   end. *)
 
Notation env a := (Expr.name -> option a).
Reserved Notation "a ::> b" (at level 50).
Variable const_vals : env exp.

Inductive par_step : relation exp :=
| P_ref    : forall e, e ::> e
                    
| P_pi     : forall A A' B B', A ::> A' -> B ::> B' -> A :>> B ::> A' :>> B'
(* | P_lam    : forall A A' b b', A ::> A' -> b ::> b' -> A :#> b ::> A' :#> b' *)
| P_lam    : forall b b', b ::> b' -> Lam b ::> Lam b'
| P_app    : forall f f' a a', f ::> f' -> a ::> a' -> (f :$: a) ::> (f' :$: a')
(* | P_beta   : forall f A b a a', f ::> (A :#> b) -> a ::> a' -> (f :$: a) ::> b.[a'/] *)
| P_beta   : forall f b a a', f ::> Lam b -> a ::> a' -> (f :$: a) ::> b.[a'/]
 
| P_sig    : forall A A' B B', A ::> A' -> B ::> B' -> Sigma A B ::> Sigma A' B'
| P_smk    : forall a a' b b', a ::> a' -> b ::> b' -> S_mk a b ::> S_mk a' b'
| P_pi1    : forall s s', s ::> s' -> S_p1 s ::> S_p1 s'
| P_pi2    : forall s s', s ::> s' -> S_p2 s ::> S_p2 s'
| P_p1beta : forall s a b, s ::> S_mk a b -> S_p1 s ::> a
| P_p2beta : forall s a b, s ::> S_mk a b -> S_p2 s ::> b
 
| P_Sum    : forall A A' B B', A ::> A' -> B ::> B' -> Sum A B ::> Sum A' B'
| P_inl    : forall a a', a ::> a' -> Sum_inl a ::> Sum_inl a'
| P_inr    : forall b b', b ::> b' -> Sum_inr b ::> Sum_inr b'
(* | P_split  : forall C C' a a' b b' ab ab', C ::> C' -> a ::> a' -> b ::> b' -> ab ::> ab' -> Split C a b ab ::> Split C' a' b' ab' *)
| P_split  : forall a a' b b' ab ab',  a ::> a' -> b ::> b' -> ab ::> ab' -> Split a b ab ::> Split a' b' ab'
| P_split_l : forall ca ca' cb ab a, ca ::> ca' -> ab ::> Sum_inl a -> Split ca cb ab ::> ca'.[a/]
| P_split_r : forall ca cb cb' ab b, cb ::> cb' -> ab ::> Sum_inr b -> Split ca cb ab ::> cb'.[b/]
 
(* | P_emrec  : forall C C' e e', C ::> C' -> e ::> e' -> empty_rec C e ::> empty_rec C' e' *)
(* | P_emrec  : forall e e', e ::> e' -> empty_rec e ::> empty_rec e' *)
 
(* | P_wrap   : forall m m', m ::> m' -> Wrap m ::> Wrap m' *)
(* | P_unwrap : forall m m', m ::> m' -> Unwrap m ::> Unwrap m' *)

(* | P_wrap_unwrap : forall m m', m ::> Unwrap m' -> Wrap m ::> m' *)
(* | P_unwrap_wrap : forall m m', m ::> Wrap m' -> Unwrap m ::> m' *)
(* | P_wrap_unwrap_eta : forall m m', m ::> Wrap (Unwrap m') -> m ::> m' *)
(* | P_unwrap_wrap_eta : forall m m', m ::> Unwrap (Wrap m') -> m ::> m' *)
                                                     
(* | P_Mu : forall D, Mu D ::> D_efunc D (Mu D) *)
| P_mu : forall D r r' d d', r ::> r' -> d ::> d' -> mu D r d ::> mu D r' d'
| P_mu_rec : forall D r r' e e', r ::> r' -> e ::> e' -> mu D r e ::> (r' :$: e' :$: rall D (mu D r'.[wk 1] (Bind 0)) e')
(* | P_mu_rec : forall D P P' r r' e e', P ::> P' -> r ::> r' -> e ::> Wrap e' ->  *)
                                 (* mu D P r e ::> (r' :$: Wrap e' :$: rall P D (mu D P.[wk 1] r.[wk 1] (Bind 0)) e) *)
where "a ::> b" := (par_step a b).

Hypothesis consts_closed : forall nm e, const_vals nm = Some e -> closed e.

Fixpoint rho (e : exp) : exp :=  
  match e with
    | (A :>> B) => (rho A) :>> (rho B)
    | (Lam b) => Lam (rho b)
    | (f :$: a) => match rho f with
                    | Lam b => b.[rho a/]
                    | f' => f' :$: rho a
                  end

    | Sigma A B => Sigma (rho A) (rho B)
    | S_mk a b => S_mk (rho a) (rho b)
    | S_p1 ab => match rho ab with
                 | S_mk a b => a
                 | ab' => S_p1 ab'
               end
    | S_p2 ab => match rho ab with
                 | S_mk a b => b
                 | ab' => S_p2 ab'
                end

    | Sum A B => Sum (rho A) (rho B)
    | Sum_inl a => Sum_inl (rho a)
    | Sum_inr b => Sum_inr (rho b)
    | Split ca cb ab => match rho ab with
                         | Sum_inl a => (rho ca).[a/]
                         | Sum_inr b => (rho cb).[b/]
                         | ab' => Split (rho ca) (rho cb) ab'
                       end

    (* | empty_rec e => empty_rec (rho e) *)

    (* | Wrap m => Wrap (rho m) *)
    (* | Wrap m => match rho m with *)
    (*              | Unwrap m' => m' *)
    (*              | m' => Wrap m' *)
    (*            end *)

    (* | Unwrap m => Unwrap (rho m) *)
    (* | Unwrap m => match rho m with *)
    (*                | Wrap m' => m' *)
    (*                | m' => Unwrap m' *)
    (*              end *)

    (* | Mu D => D_efunc D (Mu D) *)
    | mu D r d => (rho r) :$: (rho d) :$: rall D (mu D (rho r).[wk 1] (Bind 0)) (rho d)

    | _ => e
  end.

Hint Constructors par_step.

Fixpoint rho_eval_to e : e ::> rho e.
Proof. induction e; simpl; try destruct match; eauto. Qed.

Hint Resolve rho_eval_to.

Tactic Notation "invert" "value" "steps" :=
  match goal with
    | [H: Bind _ ::> _ |- _] => inverts H
    | [H: Sort _ ::> _ |- _] => inverts H
    | [H: Pi _ _ ::> _ |- _] => inverts H
    | [H: Lam _ ::> _ |- _] => inverts H
    | [H: Sigma _ _ ::> _ |- _] => inverts H
    | [H: S_mk _ _ ::> _ |- _] => inverts H
    | [H: Sum _ _ ::> _ |- _] => inverts H
    | [H: Sum_inl _ ::> _ |- _] => inverts H
    | [H: Sum_inr _ ::> _ |- _] => inverts H
    | [H: Unit ::> _ |- _] => inverts H
    | [H: unit ::> _ |- _] => inverts H
    | [H: Mu _ ::> _ |- _] => inverts H
  end.

Notation spstep sigma tau := (forall v, sigma v ::> tau v).
Infix ".>>" := spstep (at level 50).

Hint Rewrite up_lift1 up_liftn.
Lemma wk_up : forall c, wk 1 >> up c = c >> wk 1. intros; autosubst. Qed.
Lemma wk_up_exp : forall e c, e.[wk 1].[up c] = e.[c].[wk 1]. intros; autosubst. Qed.
Hint Rewrite wk_up wk_up_exp.

Lemma sub_sig : forall e v c, e.[v/].[c] = e.[up c].[v.[c]/]. intros; autosubst. Qed.
Hint Rewrite sub_sig.

Hint Resolve andb_true_intro.
Hint Rewrite closed_sub_id using (auto; fail).

Definition efunc_closed : forall D e, closed e -> closed (D_efunc D e).
Proof. induction D; intros; simpl; rewrite asms; auto; simpl.
       try_hyps; clear_funs; replace (D_efunc D2 e).[wk 1] with (D_efunc D2 e) by (autorewrite with core; auto).
       eapply closed_lift; try eassumption; auto.
Qed.

Lemma sub_sig_scop : forall e sigma i j, sub_vars i j sigma -> closed_at j e -> sub_vars i.+1 j (e .: sigma).
Proof. destruct v; simpl; auto. Qed.
Hint Resolve sub_sig_scop.

Lemma sub_ids_scop : forall i, sub_vars i i ids. auto. Qed.
Hint Resolve sub_ids_scop.

Definition rall_scoped : forall D r e n, closed_at n.+1 r -> closed_at n e -> closed_at n (rall D r e).
Proof. induction D; intros; simpl; rewrite asms; auto; simpl; auto;
       apply sub_vars_corr with (i := n.+1); auto; 
       apply sub_sig_scop || apply sub_up_vars; auto.
Qed.
       
Hint Resolve efunc_closed rall_scoped.
Hint Constructors par_step.

Lemma rall_sub D : forall r e sigma, (rall D r e).[sigma] = rall D r.[up sigma] e.[sigma].
Proof. induction D; intros; auto; simpl; rewrite asms; autosubst. Qed.
  
Hint Rewrite rall_sub.   

Lemma sub_cong1 : forall e1 e2, e1 ::> e2 -> forall sigma, e1.[sigma] ::> e2.[sigma].
Proof. induction 1; intros; simpl in *;
  rewrite ?rall_sub; simpl; autorewrite with core; try constructor; solve[eauto].
Qed.

Hint Resolve sub_cong1.
Notation sstep sigma tau :=(forall v, sigma v ::> tau v).
Infix ".>>" := spstep (at level 50).

Lemma subst_up : forall c1 c2, c1 .>> c2 -> up c1 .>> up c2.
Proof. intros. destruct v; asimpl; auto. Qed.

Hint Resolve subst_up.

Lemma sub_cong2 : forall e c1 c2, c1 .>> c2 -> e.[c1] ::> e.[c2].
Proof. induction e; intros; simpl in *; try econstructor; eauto. Qed.

Hint Resolve sub_cong2.

Lemma sub_cong : forall e1 e2, e1 ::> e2 -> forall c1 c2, c1 .>> c2 -> e1.[c1] ::> e2.[c2].
Proof. induction 1; intros; simpl in *; try solve [auto];
  repeat (simpl; autorewrite with core); try solve [econstructor; eauto].
Qed.

Hint Resolve sub_cong.

Lemma sub_cons : forall e e' sigma tau, e ::> e' -> sigma .>> tau -> (e .: sigma) .>> (e' .: tau). destruct v; simpl; auto. Qed.

Lemma ids_ev : ids .>> ids. auto. Qed.
Lemma up_ev : forall sigma tau, sigma .>> tau -> up sigma .>> up tau. destruct v; simpl; auto. Qed.

Hint Resolve ids_ev up_ev sub_cons.

Lemma rall_ev D : forall r r', r ::> r' -> forall e e', e ::>  e' -> rall D r e ::> rall D r' e'. induction D; simpl; auto. Qed.

Hint Resolve rall_ev.

Lemma rho_eval_from_to e e' : e ::> e' -> e' ::> rho e.
Proof. induction 1; simpl; try (invert value steps || destruct match); eauto 10. Qed.

Tactic Notation "clear" "trivial" := 
  repeat match goal with
           | [H: True |- _] => clear H
           | [H: ?a = ?a |- _] => clear H
           | [H: ?a == ?a |- _] => clear H 
         end.
