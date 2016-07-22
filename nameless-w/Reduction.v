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
(* | P_free   : forall nm e, const_vals nm = Some e -> Free nm ::> e                     *)

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
    (* | Free nm => match const_vals nm with None => Free nm | Some e => e end *)
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

Local Hint Resolve sub_cong1.
Notation sstep sigma tau :=(forall v, sigma v ::> tau v).
Infix ".>>" := spstep (at level 50).

Lemma subst_up : forall c1 c2, c1 .>> c2 -> up c1 .>> up c2.
Proof. intros. destruct v; asimpl; auto. Qed.

Hint Resolve subst_up.

Lemma sub_cong2 : forall e c1 c2, c1 .>> c2 -> e.[c1] ::> e.[c2].
Proof. induction e; intros; simpl in *; try econstructor; eauto. Qed.

Local Hint Resolve sub_cong2.

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

Hint Resolve rho_eval_from_to.

Notation conv := (clos_refl_sym_trans _ par_step).
Notation red := (clos_trans _ par_step).
Infix "<:::>" := conv (at level 50).
Infix ":::>" := red (at level 50).

Local Hint Resolve t_step rst_step rst_refl.
Local Hint Resolve t_trans rst_trans rst_sym : slow.

Lemma red_Pi_l : forall A B A', A :::> A' -> Pi A B :::> Pi A' B. induction 1; eauto with slow. Qed.
Lemma red_Pi_r : forall A B B', B :::> B' -> Pi A B :::> Pi A B'. induction 1; eauto with slow. Qed.
Local Hint Resolve red_Pi_l red_Pi_r.

Lemma red_Pi_Pi A B A' B' : (A :::> A') -> (B :::> B') -> Pi A B :::> Pi A' B'. eauto with slow. Qed.
Hint Resolve red_Pi_Pi.

Lemma red_Sigma_l : forall A B A', A :::> A' -> Sigma A B :::> Sigma A' B. induction 1; eauto with slow. Qed.
Lemma red_Sigma_r : forall A B B', B :::> B' -> Sigma A B :::> Sigma A B'. induction 1; eauto with slow. Qed.
Local Hint Resolve red_Sigma_l red_Sigma_r.
 
Lemma red_Sigma_Sigma A B A' B' : (A :::> A') -> (B :::> B') -> Sigma A B :::> Sigma A' B'. eauto with slow. Qed.
Hint Resolve red_Sigma_Sigma.

Lemma red_Sum_l : forall A B A', A :::> A' -> Sum A B :::> Sum A' B. induction 1; eauto with slow. Qed.
Lemma red_Sum_r : forall A B B', B :::> B' -> Sum A B :::> Sum A B'. induction 1; eauto with slow. Qed.
Local Hint Resolve red_Sum_l red_Sum_r.

Lemma red_Sum_Sum A B A' B' : (A :::> A') -> (B :::> B') -> Sum A B :::> Sum A' B'. eauto with slow. Qed.
Hint Resolve red_Sum_Sum.

Lemma red_Lam_Lam : forall e e', e :::> e' -> Lam e :::> Lam e'. induction 1; eauto with slow. Qed.
Hint Resolve red_Lam_Lam.

Lemma red_S_p1_S_p1 : forall e e', e :::> e' -> S_p1 e :::> S_p1 e'. induction 1; eauto with slow. Qed.
Lemma red_S_p2_S_p2 : forall e e', e :::> e' -> S_p2 e :::> S_p2 e'. induction 1; eauto with slow. Qed.
Hint Resolve red_S_p1_S_p1 red_S_p2_S_p2.

Lemma red_Sum_inl_Sum_inl : forall e e', e :::> e' -> Sum_inl e :::> Sum_inl e'. induction 1; eauto with slow. Qed.
Lemma red_Sum_inr_Sum_inr : forall e e', e :::> e' -> Sum_inr e :::> Sum_inr e'. induction 1; eauto with slow. Qed.
Hint Resolve red_Sum_inl_Sum_inl red_Sum_inr_Sum_inr.

Lemma red_App_l : forall A B A', A :::> A' -> App A B :::> App A' B. induction 1; eauto with slow. Qed.
Lemma red_App_r : forall A B B', B :::> B' -> App A B :::> App A B'. induction 1; eauto with slow. Qed.
Local Hint Resolve red_App_l red_App_r.

Lemma red_App_App A B A' B' : (A :::> A') -> (B :::> B') -> App A B :::> App A' B'. eauto with slow. Qed.
Hint Resolve red_App_App.

Lemma red_S_mk_l : forall A B A', A :::> A' -> S_mk A B :::> S_mk A' B. induction 1; eauto with slow. Qed.
Lemma red_S_mk_r : forall A B B', B :::> B' -> S_mk A B :::> S_mk A B'. induction 1; eauto with slow. Qed.
Local Hint Resolve red_S_mk_l red_S_mk_r.

Lemma red_S_mk_S_mk a b a' b' : a :::> a' -> b :::> b' -> S_mk a b :::> S_mk a' b'. eauto with slow. Qed.
Hint Resolve red_S_mk_S_mk.

Lemma red_Split_1 a b c a' : (a :::> a') -> Split a b c :::> Split a' b c. induction 1; eauto with slow. Qed.
Lemma red_Split_2 a b c b' : (b :::> b') -> Split a b c :::> Split a b' c. induction 1; eauto with slow. Qed.
Lemma red_Split_3 a b c c' : (c :::> c') -> Split a b c :::> Split a b c'. induction 1; eauto with slow. Qed.
Local Hint Resolve red_Split_1 red_Split_2 red_Split_3.

Lemma red_Split_Split a b c a' b' c' : (a :::> a') -> (b :::> b') -> (c :::> c') -> Split a b c :::> Split a' b' c'.
Proof. intros. apply t_trans with (y := Split a' b c); eauto with slow. Qed.
Hint Resolve red_Split_Split.

Lemma red_mu_l D : forall A B A', A :::> A' -> mu D A B :::> mu D A' B. induction 1; eauto with slow. Qed.
Lemma red_mu_r D : forall A B B', B :::> B' -> mu D A B :::> mu D A B'. induction 1; eauto with slow. Qed.
Local Hint Resolve red_mu_l red_mu_r.

Lemma red_mu_mu D A B A' B' : (A :::> A') -> (B :::> B') -> mu D A B :::> mu D A' B'. eauto with slow. Qed.
Hint Resolve red_mu_mu.

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
      specialize (IHHab2 x x0); intuition; destr_logic; subst. eauto 10 with slow. } }
  { intros; destr_logic; subst; auto. }
Qed.

Lemma red_Sigma A B e : Sigma A B :::> e <-> exists A' B', (e = Sigma A' B') /\ (A :::> A') /\ (B :::> B').
Proof. split.
  { remember (Sigma A B) as ab. 
    move=>Hab. move:A B Heqab.
    induction Hab; intros; subst; auto.
    { inversion H; subst; eauto 10. }
    { specialize (IHHab1 A B); intuition; destr_logic; subst.
      specialize (IHHab2 x x0); intuition; destr_logic; subst. eauto 10 with slow. } }
  { intros; destr_logic; subst; auto. }
Qed.

Lemma red_S_mk A B e : S_mk A B :::> e <-> exists A' B', (e = S_mk A' B') /\ (A :::> A') /\ (B :::> B').
Proof. split.
  { remember (S_mk A B) as ab. 
    move=>Hab. move:A B Heqab.
    induction Hab; intros; subst; auto.
    { inversion H; subst; eauto 10. }
    { specialize (IHHab1 A B); intuition; destr_logic; subst.
      specialize (IHHab2 x x0); intuition; destr_logic; subst. eauto 10 with slow. } }
  { intros; destr_logic; subst; auto. }
Qed.

Lemma red_Sum A B e : Sum A B :::> e <-> exists A' B', (e = Sum A' B') /\ (A :::> A') /\ (B :::> B').
Proof. split.
  { remember (Sum A B) as ab. 
    move=>Hab. move:A B Heqab.
    induction Hab; intros; subst; auto.
    { inversion H; subst; eauto 10. }
    { specialize (IHHab1 A B); intuition; destr_logic; subst.
      specialize (IHHab2 x x0); intuition; destr_logic; subst. eauto 10 with slow. } }
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
Infix ".>>>" := sred (at level 50).

Lemma sred_ref : forall sigma, sigma .>>> sigma. intros; eauto. Qed.
Lemma sub_sred : forall sigma tau, sigma .>>> tau -> forall e e', e :::> e' -> (e .: sigma) .>>> (e' .: tau). intros; destruct i; simpl; auto. Qed.

Lemma up_sred : forall sigma tau, sigma .>>> tau -> up sigma .>>> up tau. intros; destruct i; asimpl; auto. Qed.
Hint Resolve up_sred sub_sred sred_ref.

Lemma sred_cong2 : forall e sigma tau, sigma .>>> tau -> e.[sigma] :::> e.[tau]. induction e; intros; simpl; auto. Qed.
Local Hint Resolve sred_cong2.

Lemma sred_cong : forall e e', e :::> e' -> forall sigma tau, sigma .>>> tau -> e.[sigma] :::> e'.[tau]. intros. apply t_trans with (y := e.[tau]); auto. Qed.
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
    eapply t_trans with (y := Lam _ :$: a); eauto. }
Qed.

Lemma red_S_p1 p e : S_p1 p :::> e <-> (exists p', e = S_p1 p' /\ p :::> p') \/ (exists a b, p :::> S_mk a b /\ a :::> e).
Proof. split.
  { remember (S_p1 p) as sp.
    move=>Hred; move: p Heqsp; induction Hred; intros; subst.
    { inversion H; subst; solve[left; eauto 7 | right; eauto 7]. }
    { specialize (IHHred1 _ erefl).
      destr_logic; subst; [|right;eauto].
      specialize (IHHred2 _ erefl).
      destr_logic; subst; [left|right]; eauto. } }
  { intros; destr_logic; subst; auto.
    eapply t_trans with (y := S_p1 (S_mk _ _)); eauto. }
Qed.
    
Lemma red_S_p2 p e : S_p2 p :::> e <-> (exists p', e = S_p2 p' /\ p :::> p') \/ (exists a b, p :::> S_mk a b /\ b :::> e).
Proof. split.
  { remember (S_p2 p) as sp.
    move=>Hred; move: p Heqsp; induction Hred; intros; subst.
    { inversion H; subst; solve[left; eauto 7 | right; eauto 7]. }
    { specialize (IHHred1 _ erefl).
      destr_logic; subst; [|right;eauto].
      specialize (IHHred2 _ erefl).
      destr_logic; subst; [left|right]; eauto. } }
  { intros; destr_logic; subst; auto.
    eapply t_trans with (y := S_p2 (S_mk _ _)); eauto. }
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
    eapply t_trans; eauto. }
Qed.

Lemma red_rall_l D r d r' : r :::> r' -> rall D r d :::> rall D r' d. induction 1; eauto. Qed.
Lemma red_rall_r D r d d' : d :::> d' -> rall D r d :::> rall D r d'. induction 1; eauto. Qed.
Local Hint Resolve red_rall_l red_rall_r.
Lemma red_rall_rall D r d r' d' : r :::> r' -> d :::> d' -> rall D r d :::> rall D r' d'. eauto. Qed.
Hint Resolve red_rall_rall.

Lemma red_mu D r d e : mu D r d :::> e <-> (exists r' d', e = mu D r' d' /\ r :::> r' /\ d :::> d') 
                                        \/ (r :$: d :$: rall D (mu D r.[wk 1] (Bind 0)) d) :::> e.
Proof. split.
  { remember (mu D r d) as mdrd.
    move=>Hred; move: r d Heqmdrd; induction Hred; intros; subst.
    { inversion H; subst; try solve[left;eauto 7|right;eauto 10]. }
    { specialize (IHHred1 _ _ erefl).
      destr_logic; subst; try solve[right;eauto].
      specialize (IHHred2 _ _ erefl).
      destr_logic; subst; solve[right; eapply t_trans; eassumption || apply red_App_App; auto|left;eauto 10]. } }
  { intros; destr_logic; subst; auto.
    eapply t_trans with (y := _ :$: _ :$: _); try eassumption; eauto. }
Qed.

Hint Rewrite red_App red_S_p1 red_S_p2 red_Split red_mu : beta.

(* Not working for now - need to add P_free rule *)
(* Lemma red_Free nm e : Free nm :::> e <-> (e = Free nm) \/ (exists e', const_vals nm = Some e' /\ e' :::> e). *)
(* Proof. split. *)
(*   { remember (Free nm) as f.  *)
(*     induction 1; subst. *)
(*     - inversion H; subst; eauto. *)
(*     - specialize (IHclos_trans1 erefl); destr_logic; subst; eauto. } *)
(*   { destruct 1; subst; destr_logic; eauto. *)
(*     apply t_trans with (y := x); auto. } *)
(* Qed. *)