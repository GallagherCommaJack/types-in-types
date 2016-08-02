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
Hypothesis const_vals_closed : forall nm e, const_vals nm = Some e -> closed e.
Hint Resolve const_vals_closed.

Inductive par_step : relation exp :=
| P_ref    : forall e, e ::> e
| P_free   : forall nm e, const_vals nm = Some e -> Free nm ::> e

| P_pi     : forall A A' B B', A ::> A' -> B ::> B' -> A :>> B ::> A' :>> B'
(* | P_lam    : forall A A' b b', A ::> A' -> b ::> b' -> A :#> b ::> A' :#> b' *)
| P_lam    : forall b b', b ::> b' -> Lam b ::> Lam b'
| P_app    : forall f f' a a', f ::> f' -> a ::> a' -> (f :$: a) ::> (f' :$: a')
(* | P_beta   : forall f A b a a', f ::> (A :#> b) -> a ::> a' -> (f :$: a) ::> b.[a'/] *)
| P_beta   : forall u f b a a', f ::> Lam b -> a ::> a' -> u = b.[a'/] -> (f :$: a) ::> u
 
| P_sig    : forall A A' B B', A ::> A' -> B ::> B' -> Sigma A B ::> Sigma A' B'
| P_smk    : forall a a' b b', a ::> a' -> b ::> b' -> S_mk a b ::> S_mk a' b'
| P_srec   : forall r r' p p', r ::> r' -> p ::> p' -> S_rec r p ::> S_rec r' p'
| P_srec_beta : forall u r r' p a b, r ::> r' -> p ::> S_mk a b -> u = r'.[b,a/] -> S_rec r p ::> u
(* | P_pi1    : forall s s', s ::> s' -> S_p1 s ::> S_p1 s' *)
(* | P_pi2    : forall s s', s ::> s' -> S_p2 s ::> S_p2 s' *)
(* | P_p1beta : forall s a b, s ::> S_mk a b -> S_p1 s ::> a *)
(* | P_p2beta : forall s a b, s ::> S_mk a b -> S_p2 s ::> b *)
 
| P_Sum    : forall A A' B B', A ::> A' -> B ::> B' -> Sum A B ::> Sum A' B'
| P_inl    : forall a a', a ::> a' -> Sum_inl a ::> Sum_inl a'
| P_inr    : forall b b', b ::> b' -> Sum_inr b ::> Sum_inr b'
(* | P_split  : forall C C' a a' b b' ab ab', C ::> C' -> a ::> a' -> b ::> b' -> ab ::> ab' -> Split C a b ab ::> Split C' a' b' ab' *)
| P_split  : forall a a' b b' ab ab',  a ::> a' -> b ::> b' -> ab ::> ab' -> Split a b ab ::> Split a' b' ab'
| P_split_l : forall u ca ca' cb ab a, ca ::> ca' -> ab ::> Sum_inl a -> u = ca'.[a/] -> Split ca cb ab ::> u
| P_split_r : forall u ca cb cb' ab b, cb ::> cb' -> ab ::> Sum_inr b -> u = cb'.[b/] -> Split ca cb ab ::> u
 
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
| P_mu_rec : forall u D r r' e e', r ::> r' -> e ::> e' -> 
                              u = r'.[rall D (mu D r'.[upn 2 (wk 1)] (Bind 0)) e', e'/] ->
                              (* u = (r' :$: e' :$: rall D (mu D r'.[wk 1] (Bind 0)) e') -> *)
                              mu D r e ::> u
(* | P_mu_rec : forall D P P' r r' e e', P ::> P' -> r ::> r' -> e ::> Wrap e' ->  *)
                                 (* mu D P r e ::> (r' :$: Wrap e' :$: rall P D (mu D P.[wk 1] r.[wk 1] (Bind 0)) e) *)
where "a ::> b" := (par_step a b).

Hypothesis consts_closed : forall nm e, const_vals nm = Some e -> closed e.

Fixpoint rho (e : exp) : exp :=  
  match e with
    | Free nm => match const_vals nm with None => Free nm | Some e => e end
    | (A :>> B) => (rho A) :>> (rho B)
    | (Lam b) => Lam (rho b)
    | (f :$: a) => match rho f with
                    | Lam b => b.[rho a/]
                    | f' => f' :$: rho a
                  end

    | Sigma A B => Sigma (rho A) (rho B)
    | S_mk a b => S_mk (rho a) (rho b)
    | S_rec r ab => match rho ab with
                     | S_mk a b => (rho r).[b,a/]
                     | ab' => S_rec (rho r) ab'
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
    | mu D r d => (rho r).[rall D (mu D (rho r).[upn 2 (wk 1)] (Bind 0)) (rho d), (rho d)/]

    | _ => e
  end.

Hint Constructors par_step.

Lemma rho_eval_to e : e ::> rho e.
Proof. induction e; simpl; try solve[try destruct match;eauto].
  remember (const_vals n) as cn; symmetry in Heqcn.
  destruct cn; auto.
Qed.
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
Infix ".>" := spstep (at level 50).

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
  apply sub_vars_scoped with (i := n.+1); auto; 
  apply sub_sig_scop || apply sub_up_vars; auto.
Qed.

Hint Constructors par_step.

Lemma rall_sub D : forall r e sigma, (rall D r e).[sigma] = rall D r.[up sigma] e.[sigma].
Proof. induction D; intros; auto; simpl; rewrite asms; autosubst. Qed.
Hint Rewrite rall_sub.   
Hint Rewrite rall_sub : autosubst.

Hint Extern 1 (Free ?nm ::> ?e.[_]) => rewrite closed_sub_id; [constructor|eapply const_vals_closed]; eassumption.
Hint Extern 1 (const_vals ?nm = Some ?e.[_]) => rewrite closed_sub_id; try eapply const_vals_closed; eassumption.
Hint Resolve closed_sub_id.
Lemma step_cong1 : forall e1 e2, e1 ::> e2 -> forall sigma, e1.[sigma] ::> e2.[sigma].
Proof. induction 1; intros; simpl in *; subst; try solve[try econstructor; eauto; autosubst]. Qed.
Local Hint Resolve step_cong1.

Lemma step_up : forall c1 c2, c1 .> c2 -> up c1 .> up c2.
Proof. intros. destruct v; asimpl; auto. Qed.

Hint Resolve step_up.

Tactic Notation "auto" "upn" ident(n) := induction n; intros; repeat rewrite <- fold_up_upn; auto.
Lemma step_upn n : forall c1 c2, c1 .> c2 -> upn n c1 .> upn n c2. auto upn n. Qed.
Hint Resolve step_upn.

Lemma step_cong2 : forall e c1 c2, c1 .> c2 -> e.[c1] ::> e.[c2].
Proof. induction e; intros; simpl in *; try econstructor; eauto. Qed.

Local Hint Resolve step_cong2.

Lemma step_cong : forall e1 e2, e1 ::> e2 -> forall c1 c2, c1 .> c2 -> e1.[c1] ::> e2.[c2].
Proof. induction 1; intros; simpl in *; subst; auto; econstructor;
  try (eapply IHpar_step1 || eapply IHpar_step2); try (eapply step_upn || eapply step_up);
  eassumption || autosubst.
Qed.

Hint Resolve step_cong.

Lemma sub_cons : forall e e' sigma tau, e ::> e' -> sigma .> tau -> (e .: sigma) .> (e' .: tau). destruct v; simpl; auto. Qed.

Lemma ids_ev : ids .> ids. auto. Qed.
Lemma up_ev : forall sigma tau, sigma .> tau -> up sigma .> up tau. destruct v; simpl; auto. Qed.

Hint Resolve ids_ev up_ev sub_cons.

Lemma rall_ev D : forall r r', r ::> r' -> forall e e', e ::>  e' -> rall D r e ::> rall D r' e'. induction D; simpl; auto. Qed.

Hint Resolve rall_ev.

Lemma rho_eval_from_to e e' : e ::> e' -> e' ::> rho e.
Proof. induction 1; simpl; try (invert value steps || destruct match); subst; eauto 10; try solve by inversion.
  inverts H; auto.
Qed.

Hint Resolve rho_eval_from_to.

Notation conv := (clos_refl_sym_trans _ par_step).
Notation red := (clos_trans _ par_step).
Infix "<:::>" := conv (at level 50).
Infix ":::>" := red (at level 50).

Instance red_refl : Reflexive red. auto. Qed.

Local Hint Resolve t_step rst_step rst_refl.
Local Hint Resolve t_trans rst_trans rst_sym : slow.

Lemma red_Pi_l : forall A B A', A :::> A' -> Pi A B :::> Pi A' B. induction 1; eauto. Qed.
Lemma red_Pi_r : forall A B B', B :::> B' -> Pi A B :::> Pi A B'. induction 1; eauto. Qed.
Local Hint Resolve red_Pi_l red_Pi_r.

Lemma red_Pi_Pi A B A' B' : (A :::> A') -> (B :::> B') -> Pi A B :::> Pi A' B'. eauto. Qed.
Hint Resolve red_Pi_Pi.

Lemma red_Sigma_l : forall A B A', A :::> A' -> Sigma A B :::> Sigma A' B. induction 1; eauto. Qed.
Lemma red_Sigma_r : forall A B B', B :::> B' -> Sigma A B :::> Sigma A B'. induction 1; eauto. Qed.
Local Hint Resolve red_Sigma_l red_Sigma_r.
 
Lemma red_Sigma_Sigma A B A' B' : (A :::> A') -> (B :::> B') -> Sigma A B :::> Sigma A' B'. eauto. Qed.
Hint Resolve red_Sigma_Sigma.

Lemma red_Sum_l : forall A B A', A :::> A' -> Sum A B :::> Sum A' B. induction 1; eauto. Qed.
Lemma red_Sum_r : forall A B B', B :::> B' -> Sum A B :::> Sum A B'. induction 1; eauto. Qed.
Local Hint Resolve red_Sum_l red_Sum_r.

Lemma red_Sum_Sum A B A' B' : (A :::> A') -> (B :::> B') -> Sum A B :::> Sum A' B'. eauto. Qed.
Hint Resolve red_Sum_Sum.

Lemma red_Lam_Lam : forall e e', e :::> e' -> Lam e :::> Lam e'. induction 1; eauto. Qed.
Hint Resolve red_Lam_Lam.

Lemma red_Srec_l : forall r e r', r :::> r' -> S_rec r e :::> S_rec r' e. induction 1; auto; transitivity (S_rec y e); auto. Qed.
Lemma red_Srec_r : forall r e e', e :::> e' -> S_rec r e :::> S_rec r e'. induction 1; auto; transitivity (S_rec r y); auto. Qed.
Local Hint Resolve red_Srec_l red_Srec_r.
Lemma red_Srec_Srec r e r' e' : r :::> r' -> e :::> e' -> S_rec r e :::> S_rec r' e'. transitivity (S_rec r' e); auto. Qed.
Hint Resolve red_Srec_Srec.

Lemma red_Sum_inl_Sum_inl : forall e e', e :::> e' -> Sum_inl e :::> Sum_inl e'. induction 1; eauto. Qed.
Lemma red_Sum_inr_Sum_inr : forall e e', e :::> e' -> Sum_inr e :::> Sum_inr e'. induction 1; eauto. Qed.
Hint Resolve red_Sum_inl_Sum_inl red_Sum_inr_Sum_inr.

Lemma red_App_l : forall A B A', A :::> A' -> App A B :::> App A' B. induction 1; eauto. Qed.
Lemma red_App_r : forall A B B', B :::> B' -> App A B :::> App A B'. induction 1; eauto. Qed.
Local Hint Resolve red_App_l red_App_r.

Lemma red_App_App A B A' B' : (A :::> A') -> (B :::> B') -> App A B :::> App A' B'. eauto. Qed.
Hint Resolve red_App_App.

Lemma red_S_mk_l : forall A B A', A :::> A' -> S_mk A B :::> S_mk A' B. induction 1; eauto. Qed.
Lemma red_S_mk_r : forall A B B', B :::> B' -> S_mk A B :::> S_mk A B'. induction 1; eauto. Qed.
Local Hint Resolve red_S_mk_l red_S_mk_r.

Lemma red_S_mk_S_mk a b a' b' : a :::> a' -> b :::> b' -> S_mk a b :::> S_mk a' b'. eauto. Qed.
Hint Resolve red_S_mk_S_mk.

Lemma red_Split_1 a b c a' : (a :::> a') -> Split a b c :::> Split a' b c. induction 1; auto; transitivity (Split y b c); auto. Qed.
Lemma red_Split_2 a b c b' : (b :::> b') -> Split a b c :::> Split a b' c. induction 1; auto; transitivity (Split a y c); auto. Qed.
Lemma red_Split_3 a b c c' : (c :::> c') -> Split a b c :::> Split a b c'. induction 1; auto; transitivity (Split a b y); auto. Qed.
Local Hint Resolve red_Split_1 red_Split_2 red_Split_3.

Lemma red_Split_Split a b c a' b' c' : (a :::> a') -> (b :::> b') -> (c :::> c') -> Split a b c :::> Split a' b' c'.
Proof. transitivity (Split a' b c); auto; transitivity (Split a' b' c); auto. Qed.
Hint Resolve red_Split_Split.

Lemma red_mu_l D : forall A B A', A :::> A' -> mu D A B :::> mu D A' B. induction 1; auto. transitivity (mu D y B); auto. Qed.
Lemma red_mu_r D : forall A B B', B :::> B' -> mu D A B :::> mu D A B'. induction 1; auto; transitivity (mu D A y); auto. Qed.
Local Hint Resolve red_mu_l red_mu_r.

Lemma red_mu_mu D A B A' B' : (A :::> A') -> (B :::> B') -> mu D A B :::> mu D A' B'. transitivity (mu D A' B); auto. Qed.
Hint Resolve red_mu_mu.

Lemma red_Free nm e : Free nm :::> e <-> (e = Free nm) \/ (exists v, const_vals nm = Some v /\ v :::> e).
Proof. remember (Free nm).
  split; induction 1; subst; auto.
  - + inverts H; eauto.
    + intuition; subst; destr_logic; eauto.
  - destr_logic; eauto.
Qed.

Lemma red_Bind v e : Bind v :::> e <-> e = Bind v. 
Proof. remember (Bind v).
  split; induction 1; subst; auto; inversion H; subst; intuition; subst; reflexivity. 
Qed.
 
Lemma red_Sort l e : Sort l :::> e <-> e = Sort l.
Proof. remember (Sort l).
  split; induction 1; subst; auto; inversion H; subst; intuition; subst; reflexivity.
Qed.

Lemma red_Unit e : Unit :::> e <-> e = Unit.
Proof. remember Unit.
  split; induction 1; subst; auto; inversion H; subst; intuition; subst; reflexivity.
Qed.

Lemma red_unit e : unit :::> e <-> e = unit.
Proof. remember unit.
  split; induction 1; subst; auto; inversion H; subst; intuition; subst; reflexivity.
Qed.

Lemma red_Mu D e : Mu D :::> e <-> e = Mu D.
Proof. remember (Mu D).
  split; induction 1; subst; auto; inversion H; subst; intuition; subst; reflexivity.
Qed.

Hint Resolve red_Bind red_Sort red_Unit red_unit red_Mu.
Hint Rewrite red_Bind red_Sort red_Unit red_unit red_Mu.

Lemma red_Pi A B e : Pi A B :::> e <-> exists A' B', (e = Pi A' B') /\ (A :::> A') /\ (B :::> B').
Proof. split.
  { remember (A :>> B) as ab. 
    move=>Hab. move:A B Heqab.
    induction Hab; intros; subst; auto.
    { inversion H; subst; eauto 10. }
    { specialize (IHHab1 A B); intuition; destr_logic; subst.
      specialize (IHHab2 x x0); intuition; destr_logic; subst. eauto 10. } }
  { intros; destr_logic; subst; auto. }
Qed.

Lemma red_Sigma A B e : Sigma A B :::> e <-> exists A' B', (e = Sigma A' B') /\ (A :::> A') /\ (B :::> B').
Proof. split.
  { remember (Sigma A B) as ab. 
    move=>Hab. move:A B Heqab.
    induction Hab; intros; subst; auto.
    { inversion H; subst; eauto 10. }
    { specialize (IHHab1 A B); intuition; destr_logic; subst.
      specialize (IHHab2 x x0); intuition; destr_logic; subst. eauto 10. } }
  { intros; destr_logic; subst; auto. }
Qed.

Lemma red_S_mk A B e : S_mk A B :::> e <-> exists A' B', (e = S_mk A' B') /\ (A :::> A') /\ (B :::> B').
Proof. split.
  { remember (S_mk A B) as ab. 
    move=>Hab. move:A B Heqab.
    induction Hab; intros; subst; auto.
    { inversion H; subst; eauto 10. }
    { specialize (IHHab1 A B); intuition; destr_logic; subst.
      specialize (IHHab2 x x0); intuition; destr_logic; subst. eauto 10. } }
  { intros; destr_logic; subst; auto. }
Qed.

Lemma red_Sum A B e : Sum A B :::> e <-> exists A' B', (e = Sum A' B') /\ (A :::> A') /\ (B :::> B').
Proof. split.
  { remember (Sum A B) as ab. 
    move=>Hab. move:A B Heqab.
    induction Hab; intros; subst; auto.
    { inversion H; subst; eauto 10. }
    { specialize (IHHab1 A B); intuition; destr_logic; subst.
      specialize (IHHab2 x x0); intuition; destr_logic; subst. eauto 10. } }
  { intros; destr_logic; subst; auto. }
Qed.

Hint Resolve red_Pi red_Sigma red_S_mk red_Sum.
Hint Rewrite red_Pi red_Sigma red_S_mk red_Sum.

Lemma red_Lam b e : Lam b :::> e <-> exists b', (e = Lam b') /\ (b :::> b').
Proof. split.
  { remember (Lam b) as lb. move=>Hred; move: b Heqlb. induction Hred; intros; subst; eauto.
    { inversion H; subst; eauto. }
    { specialize (IHHred1 b); intuition; destr_logic; subst.
      specialize (IHHred2 x); intuition; destr_logic; subst.
      eauto. } }
  { intros; destr_logic; subst; auto. }
Qed.

Lemma red_Sum_inl b e : Sum_inl b :::> e <-> exists b', (e = Sum_inl b') /\ (b :::> b').
Proof. split.
  { remember (Sum_inl b) as lb. move=>Hred; move: b Heqlb. induction Hred; intros; subst; eauto.
    { inversion H; subst; eauto. }
    { specialize (IHHred1 b); intuition; destr_logic; subst.
      specialize (IHHred2 x); intuition; destr_logic; subst.
      eauto. } }
  { intros; destr_logic; subst; auto. }
Qed.

Lemma red_Sum_inr b e : Sum_inr b :::> e <-> exists b', (e = Sum_inr b') /\ (b :::> b').
Proof. split.
  { remember (Sum_inr b) as lb. move=>Hred; move: b Heqlb. induction Hred; intros; subst; eauto.
    { inversion H; subst; eauto. }
    { specialize (IHHred1 _ erefl); destr_logic; subst.
      specialize (IHHred2 _ erefl); destr_logic; subst.
      eauto. } }
  { intros; destr_logic; subst; auto. }
Qed.

Hint Resolve red_Lam red_Sum_inl red_Sum_inr.
Hint Rewrite red_Lam red_Sum_inl red_Sum_inr.

Lemma sred_cong1 : forall e e' sigma, e :::> e' -> e.[sigma] :::> e'.[sigma]. induction 1; eauto. Qed.
Local Hint Resolve sred_cong1.

Notation sred sigma tau := (forall i : var, sigma i :::> tau i).
Infix "..>" := sred (at level 50).

Lemma sred_ref : forall sigma, sigma ..> sigma. intros; eauto. Qed.
Lemma sub_sred : forall sigma tau, sigma ..> tau -> forall e e', e :::> e' -> (e .: sigma) ..> (e' .: tau). intros; destruct i; simpl; auto. Qed.

Lemma sred_trans : forall delta sigma tau, delta ..> sigma -> sigma ..> tau -> delta ..> tau. eauto. Qed.

Lemma up_sred : forall sigma tau, sigma ..> tau -> up sigma ..> up tau. intros; destruct i; asimpl; auto. Qed.
Hint Resolve up_sred sub_sred sred_ref.
Lemma upn_sred n : forall sigma tau, sigma ..> tau -> upn n sigma ..> upn n tau. auto upn n. Qed.
Hint Resolve upn_sred.

Lemma sred_cong2 : forall e sigma tau, sigma ..> tau -> e.[sigma] :::> e.[tau]. induction e; intros; simpl; auto. Qed.
Local Hint Resolve sred_cong2.

Lemma sred_cong : forall e e', e :::> e' -> forall sigma tau, sigma ..> tau -> e.[sigma] :::> e'.[tau]. intros. apply t_trans with (y := e.[tau]); auto. Qed.
Hint Resolve sred_cong.

Lemma red_App f a e : (f :$: a) :::> e <-> (exists f' a', e = (f' :$: a') /\ (f :::> f') /\ (a :::> a')) \/
                                             (exists b, (f :::> Lam b) /\ (b.[a/] :::> e)).
Proof. split.
  { remember (f :$: a) as fa.
    move=>Hred; move: f a Heqfa; induction Hred; intros; subst.
    { inverts H; solve[left; eauto 7 | right; eauto 10]. }
    { specialize (IHHred1 _ _ erefl).
      destr_logic; subst; [|right; eauto].
      specialize (IHHred2 _ _ erefl).
      destr_logic; subst; [left|right]; eauto 7. } }
  { intros; destr_logic; subst; auto.
    eapply t_trans with (y := Lam _ :$: a);
      [|eapply t_trans with (y := _.[a/])]; eauto. }
Qed.

Lemma red_Srec r p e : S_rec r p :::> e <-> (exists r' p', e = S_rec r' p' /\ r :::> r' /\ p :::> p') \/
                                          (exists a b, p :::> S_mk a b /\ r.[b,a/] :::> e).
Proof. split.
  { remember (S_rec r p) as srp.
    move=>Hred; move: r p Heqsrp; induction Hred; intros; subst.
    { inverts H; solve[left; eauto 7 | right; eauto 10]. }
    { specialize (IHHred1 _ _ erefl).
      destr_logic; subst; [|right; eauto].
      specialize (IHHred2 _ _ erefl).
      destr_logic; subst; [left|right]; eauto 7. } }
  { intros; destr_logic; subst; auto.
    eapply t_trans with (y := S_rec r (S_mk _ _));
      [|eapply t_trans with (y := r.[_,_/])]; eauto. }
Qed.

Lemma red_Split a b c e : Split a b c :::> e <-> (exists a' b' c', e = Split a' b' c' /\ a :::> a' /\ b :::> b' /\ c :::> c')
                                               \/ (exists a', c :::> Sum_inl a' /\ a.[a'/] :::> e)
                                               \/ (exists b', c :::> Sum_inr b' /\ b.[b'/] :::> e).
Proof. split.
  { remember (Split a b c) as sabc.
    move=>Hred; move: a b c Heqsabc; induction Hred; intros; subst.
    { inversion H; subst; try solve[left;eauto 10|right;eauto 7]. }
    { specialize (IHHred1 _ _ _ erefl).
      destr_logic; subst; try solve[right;eauto].
      specialize (IHHred2 _ _ _ erefl).
      destr_logic; subst; try solve[left;eauto 10|right;eauto 7]. } }
  { intros; destr_logic; subst; auto;
    [eapply t_trans with (y := Split a b _); [|eapply t_trans with (y := a.[_/])]|
     eapply t_trans with (y := Split a b _); [|eapply t_trans with (y := b.[_/])]]; eauto. }
Qed.

Lemma red_rall_l D r d r' : r :::> r' -> rall D r d :::> rall D r' d. induction 1; eauto. Qed.
Lemma red_rall_r D r d d' : d :::> d' -> rall D r d :::> rall D r d'. induction 1; eauto. Qed.
Local Hint Resolve red_rall_l red_rall_r.
Lemma red_rall_rall D r d r' d' : r :::> r' -> d :::> d' -> rall D r d :::> rall D r' d'. eauto. Qed.
Hint Resolve red_rall_rall.

Lemma red_mu D r d e : mu D r d :::> e <-> (exists r' d', e = mu D r' d' /\ r :::> r' /\ d :::> d') 
                                        \/ (r.[rall D (mu D r.[upn 2 (wk 1)] (Bind 0)) d, d/] :::> e).
Proof. split.
  { remember (mu D r d) as mdrd.
    move=>Hred; move: r d Heqmdrd; induction Hred; intros; subst.
    { inversion H; subst; try solve[left;eauto 7|right;eauto 10]. }
    { specialize (IHHred1 _ _ erefl).
      destr_logic; [subst|right;eauto].
      specialize (IHHred2 _ _ erefl).
      destr_logic; subst; [left;eauto 10|right].
      eapply t_trans with (y := _.[_,_/]); try eassumption; apply sred_cong; auto. } }
  { intros; destr_logic; subst; auto.
    eapply t_trans with (y := _.[_,_/]); try eassumption; eauto. }
Qed.

Hint Rewrite red_Free red_App red_Srec red_Split red_mu : beta.

Lemma red_conv : forall e e', e :::> e' -> e <:::> e'. induction 1; eauto with slow. Qed.
Hint Resolve red_conv.

Hint Resolve rho_eval_to rho_eval_from_to.
Lemma red_l_confl e1 e2 e3 : e1 ::> e2 -> e1 :::> e3 -> exists e4, e2 :::> e4 /\ e3 ::> e4.
Proof. 
  move=> He2 He3; move: e2 He2; induction He3; intros.
  { eauto 7. }
  { do 2 (try_hyps; intuition; destr_logic); clear_funs; eauto. }
Qed.
  
Lemma red_confl e1 e2 e3 : e1 :::> e2 -> e1 :::> e3 -> exists e4, e2 :::> e4 /\ e3 :::> e4.
Proof.
  move=>He2 He3; move: e3 He3; induction He2; intros.
  { extend red_l_confl; try_hyps; destr_logic; eauto. }
  { do 2 (try_hyps; intuition; destr_logic); clear_funs; eauto. }
Qed.

(* DO NOT hint resolve red_confl! slows conv_double_red a lot *)

Lemma conv_double_red : forall e1 e2, e1 <:::> e2 <-> (exists e3, e1 :::> e3 /\ e2 :::> e3).
Proof.
  split; move=>H; [|destr_logic; eauto with slow].
  induction H; try solve[eauto].
  - destr_logic; solve[eauto].
  - destr_logic. extend red_confl.
    try_hyps; clear_funs; destr_logic; solve[eauto].
Qed.

(* Hint Resolve conv_double_red. *) (* not hinting because red_confl caused problems *)
Hint Rewrite conv_double_red : unconv.

Notation sconv sigma tau := (forall i, sigma i <:::> tau i).
Infix "<..>" := sconv (at level 20).

Lemma conv_Bind_iff i j : Bind i <:::> Bind j <-> i = j. 
Proof. autorewrite with unconv; split; intros; destr_logic; autorewrite with core in *; destr_logic; subst; congruence || eauto. Qed.

Lemma conv_Sort_iff i j : Sort i <:::> Sort j <-> i = j. 
Proof. autorewrite with unconv; split; intros; destr_logic; autorewrite with core in *; destr_logic; subst; congruence || eauto. Qed.

Lemma conv_Mu_iff D1 D2 : Mu D1 <:::> Mu D2 <-> D1 = D2.
Proof. autorewrite with unconv; split; intros; destr_logic; autorewrite with core in *; destr_logic; subst; congruence || eauto. Qed.

Hint Rewrite conv_Bind_iff conv_Sort_iff conv_Mu_iff.

Lemma conv_Lam_iff b1 b2 : Lam b1 <:::> Lam b2 <-> b1 <:::> b2.
Proof. autorewrite with unconv; split; intros; destr_logic; autorewrite with core in *; destr_logic; eauto.
  subst; inversion H0; subst; eauto.
Qed.

Lemma conv_Sum_inl_iff b1 b2 : Sum_inl b1 <:::> Sum_inl b2 <-> b1 <:::> b2.
Proof. autorewrite with unconv; split; intros; destr_logic; autorewrite with core in *; destr_logic; eauto.
  subst; inversion H0; subst; eauto.
Qed.

Lemma conv_Sum_inr_iff b1 b2 : Sum_inr b1 <:::> Sum_inr b2 <-> b1 <:::> b2.
Proof. autorewrite with unconv; split; intros; destr_logic; autorewrite with core in *; destr_logic; eauto.
  subst; inversion H0; subst; eauto.
Qed.

Hint Rewrite conv_Lam_iff conv_Sum_inl_iff conv_Sum_inr_iff.

Lemma conv_Pi_iff A B A' B' : (Pi A B <:::> Pi A' B') <-> (A <:::> A' /\ B <:::> B').
Proof. autorewrite with unconv; split; intros; destr_logic; autorewrite with core in *; destr_logic; eauto.
  subst. inversion H0; subst. split; eauto.
Qed.

Lemma conv_Sigma_iff A B A' B' : (Sigma A B <:::> Sigma A' B') <-> (A <:::> A' /\ B <:::> B').
Proof. autorewrite with unconv; split; intros; destr_logic; autorewrite with core in *; destr_logic; eauto.
  subst. inversion H0; subst. split; eauto.
Qed.

Lemma conv_Sum_iff A B A' B' : (Sum A B <:::> Sum A' B') <-> (A <:::> A' /\ B <:::> B').
Proof. autorewrite with unconv; split; intros; destr_logic; autorewrite with core in *; destr_logic; eauto.
  subst. inversion H0; subst. split; eauto.
Qed.

Lemma conv_S_mk_iff A B A' B' : (S_mk A B <:::> S_mk A' B') <-> (A <:::> A' /\ B <:::> B').
Proof. autorewrite with unconv; split; intros; destr_logic; autorewrite with core in *; destr_logic; eauto.
  subst. inversion H0; subst. split; eauto.
Qed.

Hint Rewrite conv_Pi_iff conv_Sigma_iff conv_Sum_iff conv_S_mk_iff.

Lemma conv_Pi_Pi A B A' B' : A <:::> A' -> B <:::> B' -> Pi A B <:::> Pi A' B'.
Proof. autorewrite with core; auto. Qed.

Lemma conv_Sigma_Sigma A B A' B' : A <:::> A' -> B <:::> B' -> Sigma A B <:::> Sigma A' B'.
Proof. autorewrite with core; auto. Qed.

Lemma conv_Sum_Sum A B A' B' : A <:::> A' -> B <:::> B' -> Sum A B <:::> Sum A' B'.
Proof. autorewrite with core; auto. Qed.

Lemma conv_S_mk_S_mk A B A' B' : A <:::> A' -> B <:::> B' -> S_mk A B <:::> S_mk A' B'.
Proof. autorewrite with core; auto. Qed.

Lemma conv_Lam_Lam : forall b1 b2, b1 <:::> b2 -> Lam b1 <:::> Lam b2. intros; autorewrite with core; auto. Qed.

Hint Resolve conv_Pi_Pi conv_Sigma_Sigma conv_Sum_Sum conv_S_mk_S_mk conv_Lam_Lam.

Lemma conv_Srec_Srec : forall r p r' p', r <:::> r' -> p <:::> p' -> S_rec r p <:::> S_rec r' p'.
Proof. intros; autorewrite with unconv in *; destr_logic; eauto. Qed.

Hint Resolve conv_Srec_Srec.

Lemma conv_Sum_inl_Sum_inl : forall e e', e <:::> e' -> Sum_inl e <:::> Sum_inl e'. intros; autorewrite with core; auto. Qed.
Lemma conv_Sum_inr_Sum_inr : forall e e', e <:::> e' -> Sum_inr e <:::> Sum_inr e'. intros; autorewrite with core; auto. Qed.
Hint Resolve conv_Sum_inl_Sum_inl conv_Sum_inr_Sum_inr.

Lemma conv_App_App f a f' a' : (f <:::> f') -> (a <:::> a') -> ((f :$: a) <:::> (f' :$: a')).
Proof. autorewrite with unconv; intros; destr_logic; autorewrite with core in *; destr_logic; eauto. Qed.
Hint Resolve conv_App_App.

Lemma conv_Split_Split a b c a' b' c' : (a <:::> a') -> (b <:::> b') -> (c <:::> c') -> Split a b c <:::> Split a' b' c'.
Proof. autorewrite with unconv; intros; destr_logic; autorewrite with core in *; destr_logic; eauto. Qed.
Hint Resolve conv_Split_Split.

Lemma conv_mu_mu D A B A' B' : (A <:::> A') -> (B <:::> B') -> mu D A B <:::> mu D A' B'.
Proof. autorewrite with unconv; intros; destr_logic; autorewrite with core in *; destr_logic; eauto. Qed.
Hint Resolve conv_mu_mu.

Lemma sconv_cong1 sigma e1 e2 : e1 <:::> e2 -> e1.[sigma] <:::> e2.[sigma].
Proof. autorewrite with unconv; intros; destr_logic; eauto. Qed.
Hint Resolve sconv_cong1.

Lemma sconv_up sigma tau : sigma <..> tau -> up sigma <..> up tau.
Proof. intros; destruct i; asimpl; auto. Qed.
Hint Resolve sconv_up.

Lemma sconv_upn n sigma tau : sigma <..> tau -> upn n sigma <..> upn n tau. auto upn n. Qed.
Hint Resolve sconv_upn.

Lemma sconv_cong2 e : forall sigma tau, sigma <..> tau -> e.[sigma] <:::> e.[tau].
Proof. induction e; simpl; auto 10. Qed.
Hint Resolve sconv_cong2.

Lemma sconv_cong e1 e2 sigma tau : e1 <:::> e2 -> sigma <..> tau -> e1.[sigma] <:::> e2.[tau]. intros; transitivity (e1.[tau]); auto. Qed.
Hint Resolve sconv_cong.

Definition subtyp A B := (A <:::> B \/ exists i j, A <:::> Sort i /\ B <:::> Sort j /\ i < j).
Infix "::<<" := subtyp (at level 20).

Lemma conv_sort_red e i : e <:::> Sort i <-> e :::> Sort i.
Proof. split; [|auto]. autorewrite with unconv; intros; destr_logic; autorewrite with core in *; subst; auto. Qed.
(* Hint Resolve conv_sort_red. *)
Hint Rewrite conv_sort_red : unconv.

Hint Resolve red_conv.
Lemma conv_ext_l e1 e2 e3 : e1 <:::> e2 -> e2 :::> e3 -> e1 <:::> e3. eauto using clos_refl_sym_trans. Qed.
Lemma conv_ext_r e1 e2 e3 : e1 :::> e2 -> e2 <:::> e3 -> e1 <:::> e3. eauto using clos_refl_sym_trans. Qed.
Hint Resolve conv_ext_l conv_ext_r : slow.

Instance subtyp_refl : Reflexive subtyp. unfold subtyp; auto. Qed.

Hint Resolve sconv_cong1 sconv_cong2 sconv_cong.

Tactic Notation "eauto" "rst" := eauto using clos_refl_sym_trans.
Tactic Notation "eauto" "rst" integer(n) := eauto n using clos_refl_sym_trans.
Instance subtyp_trans : Transitive subtyp. 
Proof. repeat destruct 1; destr_logic; autorewrite with core in *.
  - left; eauto rst.
  - right; eauto rst 7.
  - assert (z <:::> Sort x1) by eauto using rst_trans,rst_sym.
    right; eauto 7.
  - assert (Sort x3 <:::> Sort x0) by eauto rst.
    autorewrite with core in *; subst.
    right; exists x2; exists x1; repeat split; [eauto rst|eauto rst|transitivity x0]; auto.
Qed.

Lemma subtyp_cong1 A B sigma : subtyp A B -> subtyp A.[sigma] B.[sigma]. 
Proof. destruct 1; [left|right]; destr_logic; auto.
  repeat eexists;
  match goal with [|-context[Sort ?i]] => change (Sort i) with (Sort i).[sigma] | _ => eassumption end;
  auto.
Qed.
