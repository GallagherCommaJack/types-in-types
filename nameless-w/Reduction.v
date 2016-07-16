Require Import Prelude.
Require Import Expr.

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
                                                     
| P_Mu : forall D, Mu D ::> D_efunc D (Mu D)
| P_mu : forall D r r' d d', r ::> r' -> d ::> d' -> mu D r d ::> mu D r' d'
| P_mu_rec : forall D r r' e e', r ::> r' -> e ::> e' -> mu D r e ::> (r' :$: e' :$: rall D (mu D r'.[wk 1] (Bind 0)) e')
(* | P_mu_rec : forall D P P' r r' e e', P ::> P' -> r ::> r' -> e ::> Wrap e' ->  *)
                                 (* mu D P r e ::> (r' :$: Wrap e' :$: rall P D (mu D P.[wk 1] r.[wk 1] (Bind 0)) e) *)
where "a ::> b" := (par_step a b).

Hint Constructors par_step.
(* | P_unwrap_wrap_eta : forall m m', m ::> Unwrap (Wrap m') -> m ::> m' *)
Hypothesis const_wf : forall sigma nm e, const_vals nm = Some e -> e.[sigma] = e. (* constants should be closed *)

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

    | Mu D => D_efunc D (Mu D)
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

Require Import Scoping.
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
       
Lemma sub_cong1 : forall e1 e2, e1 ::> e2 -> forall sigma, e1.[sigma] ::> e2.[sigma].
Proof. induction 1; intros; simpl in *; 
       try (autorewrite with core in *; try_hyps; econstructor; eassumption || solve [auto]).
       { induction D.
         { constructor; auto. }
         { asimpl.
           replace (mu d_Ind r'.[sigma] e'.[sigma]) with (rall (mu d_Ind r'.[sigma].[wk 1] (Bind 0)) d_Ind e'.[sigma]) by autosubst.
           auto. }
         { replace (rall (mu (d_Sum D1 D2) r'.[wk 1] (Bind 0)) (d_Sum D1 D2) e').[sigma] 
           with (rall (mu (d_Sum D1 D2) r'.[wk 1] (Bind 0)).[up sigma] (d_Sum D1 D2) e'.[sigma]).
           shelve.
           asimpl.

asimpl.


Print rall.

         
Lemma par_sub_cong1 : forall e1 e2, e1 ~> e2 -> forall sigma, e1.[sigma] ~> e2.[sigma].
Proof. induction 1; intros; simpl; autorewrite with core in *; eauto. Qed.

Hint Resolve sub_cong1 par_sub_cong1.
Notation sstep sigma tau :=(forall v, sigma v ==> tau v).
Notation spstep sigma tau := (forall v, sigma v ~> tau v).
Infix ".>>" := spstep (at level 50).

Lemma subst_up : forall c1 c2, c1 .>> c2 -> up c1 .>> up c2.
Proof. intros. destruct v; asimpl; auto. Qed.

Hint Resolve subst_up.

Lemma par_sub_cong2 : forall e c1 c2, c1 .>> c2 -> e.[c1] ~> e.[c2].
Proof. induction e; intros; simpl in *; try econstructor; eauto. Qed.

Hint Resolve par_sub_cong2.

Lemma par_sub_cong : forall e1 e2, e1 ~> e2 -> forall c1 c2, c1 .>> c2 -> e1.[c1] ~> e2.[c2].
Proof. induction 1; intros; simpl in *; eauto; autorewrite with core in *; try econstructor; eauto. Qed.

Hint Resolve par_sub_cong.

Lemma sub_cong : forall e e' sigma tau, e ::> e' -> sigma .>> tau -> e.[sigma] ::> e'.[tau].
  
Admitted.

Lemma sub_cons : forall e e' sigma tau, e ::> e' -> sigma .>> tau -> (e .: sigma) .>> (e' .: tau).
Admitted.

Lemma ids_ev : ids .>> ids. auto. Qed.
Lemma up_ev : forall sigma tau, sigma .>> tau -> up sigma .>> up tau. Admitted.

Hint Resolve ids_ev up_ev sub_cons.
Hint Resolve sub_cong.

Lemma rho_eval_from_to e e' : e ::> e' -> e' ::> rho e.
Proof. induction 1; simpl; try (invert value steps || destruct match); eauto 10. Qed.

Lemma wk_up : forall c, wk 1 >> up c = c >> wk 1. intros; autosubst. Qed.
Lemma wk_up_exp : forall e c, e.[wk 1].[up c] = e.[c].[wk 1]. intros; autosubst. Qed.
Hint Rewrite wk_up wk_up_exp.

Lemma sub_sig : forall e v c, e.[v/].[c] = e.[up c].[v.[c]/]. intros; autosubst. Qed.
Hint Rewrite sub_sig.

Notation spstep sigma tau := (forall v, sigma v ::> tau v).
Infix ".>>" := spstep (at level 50).

Lemma sub_cong : forall e e' sigma tau, e ::> e' -> sigma .>> tau -> e.[sigma] ::> e'.[tau].
Admitted.

Lemma sub_cons : forall e e' sigma tau, e ::> e' -> sigma .>> tau -> (e .: sigma) .>> (e' .: tau).
Admitted.

Lemma sub_refl : forall (sigma : var -> exp), (sigma .>> sigma). eauto. Qed.
Hint Resolve sub_refl.
Lemma subst_up : forall c1 c2, c1 .>> c2 -> up c1 .>> up c2.
Proof. intros. destruct v; asimpl; eauto. Admitted.

Hint Resolve subst_up.

Hint Resolve sub_cong sub_cons.

Lemma rall_ev r r' D e e' : r ::> r' -> e ::> e' -> rall r D e ::> rall r' D e'.
  move=> Hr He. move: r r' Hr e e' He. induction D; simpl; intros; eauto 10.
Qed.
Hint Resolve rall_ev.

Notation canonize_sub sigma := (fun (v : var) => canonize (sigma v)).

Definition is_unwrap_dec e : (exists e', e = Unwrap e') \/ (forall e', e <> Unwrap e').
  destruct e; (right; discriminate) || (left; eexists; reflexivity). Qed.
Definition is_wrap_dec e : (exists e', e = Wrap e') \/ (forall e', e <> Wrap e').
  destruct e; (right; discriminate) || (left; eexists; reflexivity). Qed.

Fixpoint subterm e1 e2 : bool :=
  (e1 == e2) ||
  match e2 with
    | Pi A B => subterm e1 A || subterm e1 B
    | Lam b => subterm e1 b
    | App f x => subterm e1 f || subterm e1 x
    | Sigma A B => subterm e1 A || subterm e1 B
    | S_mk a b => subterm e1 a || subterm e1 b
    | S_p1 a => subterm e1 a
    | S_p2 b => subterm e1 b
    | Sum A B => subterm e1 A || subterm e1 B
    | Sum_inl a => subterm e1 a
    | Sum_inr b => subterm e1 b
    | Split a b ab => subterm e1 a || subterm e1 b || subterm e1 ab
    | empty_rec e => subterm e1 e
    | Wrap d => subterm e1 d
    | Unwrap d => subterm e1 d
    | mu D r d => subterm e1 r || subterm e1 d
    | _ => false
  end.

Hint Rewrite Bool.orb_false_r Bool.orb_true_iff.
Hint Rewrite Bool.andb_negb_r Bool.andb_true_iff.
Hint Resolve andb_prop Bool.orb_prop.

Hint Extern 1 => match goal with [H : (_ && _) |- _] => apply andb_prop in H; destruct H end.

Tactic Notation "clear" "trivial" := 
  repeat match goal with
           | [H: True |- _] => clear H
           | [H: ?a = ?a |- _] => clear H
           | [H: ?a == ?a |- _] => clear H 
         end.

Print Acc.
Notation strict_subterm := (fun e1 e2 => subterm e1 e2 && (e1 != e2)).
Theorem subterm_wf : well_founded strict_subterm.
  unfold well_founded.
  induction a; constructor; intros; simpl in *;
    try (autorewrite with core in *; congruence).
  { constructor. intros. simpl in *.
Theorem subterm_ind (P : exp -> Prop) : (forall e, (forall e', subterm e' e && (e' != e) -> P e') -> P e) -> P e.
  induction e; intros; 
  try (apply H; unfold is_true in *; simpl in *; autorewrite with core in *; destr_logic; congruence).
  { apply H.
    
    
    
    

destruct e'. 
    unfold is_true in *. simpl in H; autorewrite with core in *.
    destr_logic; clear trivial.
    
  { destruct e'; (vm_cmpute in H; inversion 
    
    
Fixpoint canonize_ren e : forall f, canonize e.[ren f] = (canonize e).[ren f].
  induction e; intros; try (clear canonize_ren; asimpl; f_equal; autosubst; fail).
  { destruct (is_unwrap_dec e); destruct (is_wrap_dec e); destr_logic; try (subst; simpl; auto; fail); try (exfalso; congruence).
    { simpl. destruct e; simpl; asimpl; try reflexivity. apply canonize_ren. } }
  { destruct (is_unwrap_dec e); destruct (is_wrap_dec e); destr_logic; try (subst; simpl; auto; fail); try (exfalso; congruence).
    { simpl. destruct e; simpl; asimpl; try reflexivity. apply canonize_ren. } }
Qed.    
    
simpl. destruct e; simpl; asimpl; simpl; try (f_equal; repeat rewrite canonize_ren; eauto).
    

Lemma canonize_up : forall sigma v, canonize_sub (up sigma) v = up (canonize_sub sigma) v.
  intros; simpl. induction v; asimpl; eauto.
  
  asimpl.
  
  
Lemma canonize_sub_corr : forall e sigma, canonize (e.[sigma]) = (canonize e).[canonize_sub sigma].
Proof. induction e; simpl in *; intros; asimpl; simpl; eauto.
       { rewrite IHe IHe0.

Lemma canonize_ev : forall e e', e ::> e' -> canonize e ::> canonize e'.
  induction 1; simpl in *; eauto.
  { 
Admitted.
Hint Resolve canonize_ev.

Lemma rho_eval_from e e' (p : e ::> e') : e' ::> rho e.
  induction p; simpl; try (try destruct match; eauto; fail).
  { destruct match; inversion IHp1; subst; eauto. }
  { inversion IHp; subst; auto. }
  { inversion IHp; subst; auto. }
  { inversion IHp2; subst; eauto. }
  { inversion IHp2; subst; eauto. }
  { inversion IHp2; subst; eauto 10. }
Qed.

Lemma sub_cong1 : forall e1 e2, e1 ::> e2 -> forall sigma, e1.[sigma] ::> e2.[sigma].
Proof. induction 1; intros; simpl; eauto; autorewrite with core in *; eauto.
Admitted.

Hint Resolve sub_cong1.
Notation spstep sigma tau := (forall v, sigma v ::> tau v).
Infix ".>>" := spstep (at level 50).

Lemma sub_cong2 : forall e c1 c2, c1 .>> c2 -> e.[c1] ::> e.[c2].
Proof. induction e; simpl; intros; try constructor; eauto. Qed.

Hint Resolve sub_cong2.

Lemma sub_cong : forall e1 e2, e1 ::> e2 -> forall c1 c2, c1 .>> c2 -> e1.[c1] ::> e2.[c2].
Admitted.
(* Proof. induction 1; intros; simpl in *; eauto; autorewrite with core in *; try econstructor; eauto. Qed. *)

Hint Constructors par_step.
Lemma wrap_eval : forall e1 e2, Wrap e1 ::> Wrap e2 -> e1 ::> e2.
Proof. induction e1; inversion 1; subst; try solve by inversion; eauto.
       { inversion H1; subst; simpl in *. }
       eapply P_unwrap_wrap
  induction e1; destruct e2; inversion 1; subst; eauto.

Hint Resolve sub_cong.

Fixpoint rho_eval_from e e' (p : e ::> e') : e' ::> rho e.
(* Proof. induction e; inversion 1; subst; intros; try (simpl; try destruct match; eauto using par_step; fail). *)
(*   { extend (IHe1 _ H2).  *)
(*     inversion H0; subst; simpl; match goal with [H: _ = rho _ |- _] => rewrite <- H end; *)
(*     apply sub_cong; try destruct v; eauto. } *)
(*   { extend (IHe _ H1). *)
(*     inversion H0; subst; simpl; match goal with [H: _ = rho _ |- _] => rewrite <- H end; eauto. } *)
(*   { extend (IHe _ H1).  *)
(*     inversion H0; subst; simpl; match goal with [H: _ = rho _ |- _] => rewrite <- H end; eauto. } *)
(*   { extend (IHe1 _ H5). *)
(*     inversion H0; subst; simpl; match goal with [H: _ = rho _ |- _] => rewrite <- H end; apply sub_cong; try destruct v; eauto. } *)
(*   { extend (IHe1 _ H5). *)
(*     inversion H0; subst; simpl; match goal with [H: _ = rho _ |- _] => rewrite <- H end; apply sub_cong; try destruct v; eauto. } *)simpl.
(*   { extend (IHe _ H1). *)
(*     simpl; destruct match; inversion H0; subst; eauto. *)

Proof. 
  induction p; try (simpl; try destruct match; eauto using par_step; fail).
  { simpl; inversion IHp1; subst; eauto; apply sub_cong; try destruct v; eauto. }
  { simpl; inversion IHp; subst; eauto. }
  { simpl; inversion IHp; subst; eauto. }
  { simpl; inversion IHp2; subst; eauto. apply sub_cong; try destruct v; eauto. }
  { simpl; inversion IHp2; subst; eauto. apply sub_cong; try destruct v; eauto. }
  { simpl; destruct match; eauto. inversion p; subst; eauto. }
  { simpl; destruct match; eauto. inversion p; subst; eauto. }
  { simpl. }
    
    
    