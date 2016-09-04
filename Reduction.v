Require Import Prelude.
Require Import Expr.
Require Import Scoping.

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
| P_smk    : forall a a' b b', a ::> a' -> b ::> b' -> Pair__sigma a b ::> Pair__sigma a' b'
| P_srec   : forall r r' p p', r ::> r' -> p ::> p' -> Rec__sigma r p ::> Rec__sigma r' p'
| P_srec_beta : forall u r r' p a b, r ::> r' -> p ::> Pair__sigma a b -> u = r'.[b,a/] -> Rec__sigma r p ::> u

| P_path : forall x x' y y',  x ::> x' -> y ::> y' -> Path x y ::> Path x' y'
| P_refl : forall x x', x ::> x' -> Refl__path x ::> Refl__path x'
| P_prec : forall c c' p p', c ::> c' -> p ::> p' -> Rec__path c p ::> Rec__path c' p'
| P_precr : forall c c' p x, c ::> c' -> p ::> Refl__path x -> Rec__path c p ::> c'

| P_sdesc : forall A A' B B', A ::> A' -> B ::> B' -> Sum__desc A B ::> Sum__desc A' B'
| P_pdesc : forall A A' B B', A ::> A' -> B ::> B' -> Prd__desc A B ::> Prd__desc A' B'
| P_fdesc : forall D D', D ::> D' -> Fix__desc D ::> Fix__desc D'
| P_descr : forall i i' s s' p p' u u' f f' d d',
              i ::> i' -> s ::> s' -> p ::> p' -> u ::> u' -> f ::> f' -> d ::> d' ->
              Rec__desc i s p u f d ::> Rec__desc i' s' p' u' f' d'

| P_descr_i : forall i i' s p u f d, i ::> i' -> d ::> Ind__desc -> Rec__desc i s p u f d ::> i'
| P_descr_s : forall i i' s s' p p' u u' f f' d A B e,
                i ::> i' -> s ::> s' -> p ::> p' -> u ::> u' -> f ::> f' ->
                d ::> Sum__desc A B ->
                e = s'.[Rec__desc i' s' p' u' f' B, B, Rec__desc i' s' p' u' f' A, A/] ->
                Rec__desc i s p u f d ::> e
| P_descr_p : forall i i' s s' p p' u u' f f' d A B e,
                i ::> i' -> s ::> s' -> p ::> p' -> u ::> u' -> f ::> f' ->
                d ::> Prd__desc A B ->
                e = p'.[Rec__desc i' s' p' u' f' B, B, Rec__desc i' s' p' u' f' A, A/] ->
                Rec__desc i s p u f d ::> e
| P_descr_u : forall i s p u u' f d,
                u ::> u' -> d ::> Unit__desc ->
                Rec__desc i s p u f d ::> u'
| P_descr_f : forall i i' s s' p p' u u' f f' d D e,
                i ::> i' -> s ::> s' -> p ::> p' -> u ::> u' -> f ::> f' ->
                d ::> Fix__desc D ->
                e = f'.[Rec__desc i' s' p' u' f' D,D/] ->
                Rec__desc i s p u f d ::> e

| P_mu : forall D1 D1' D2 D2', D1 ::> D1' -> D2 ::> D2' -> Mu D1 D2 ::> Mu D1' D2'
| P_wmu : forall m m', m ::> m' -> Wrap__mu m ::> Wrap__mu m'
| P_inlmu : forall a a', a ::> a' -> Inl__mu a ::> Inl__mu a'
| P_inrmu : forall b b', b ::> b' -> Inr__mu b ::> Inr__mu b'
| P_parmu : forall a a' b b', a ::> a' -> b ::> b' -> Pair__mu a b ::> Pair__mu a' b'
| P_fixmu : forall f f', f ::> f' -> Fix__mu f ::> Fix__mu f'
| P_murec : forall w w' il il' ir ir' p p' u u' f f' m m',
              w ::> w' -> il ::> il' -> ir ::> ir' -> p ::> p' -> u ::> u' -> f ::> f' ->
              m ::> m' ->
              Rec__mu w il ir p u f m ::> Rec__mu w' il' ir' p' u' f' m'
 
| P_murecw : forall w w' il il' ir ir' p p' f f' u u' m m' e,
              w ::> w' -> il ::> il' -> ir ::> ir' -> p ::> p' -> u ::> u' -> f ::> f' ->
              m ::> Wrap__mu m' ->
              e = w'.[Rec__mu w' il' ir' p' u' f' m',m'/] ->
              Rec__mu w il ir p u f m ::> e
| P_murecl : forall w w' il il' ir ir' p p' u u' f f' m l e,
              w ::> w' -> il ::> il' -> ir ::> ir' -> p ::> p' -> u ::> u' -> f ::> f' ->
              m ::> Inl__mu l ->
              e = il'.[Rec__mu w' il' ir' p' u' f' l,l/] ->
              Rec__mu w il ir p u f m ::> e
| P_murecr : forall w w' il il' ir ir' p p' u u' f f' m r e,
              w ::> w' -> il ::> il' -> ir ::> ir' -> p ::> p' -> u ::> u' -> f ::> f' ->
              m ::> Inr__mu r ->
              e = ir'.[Rec__mu w' il' ir' p' u' f' r,r/] ->
              Rec__mu w il ir p u f m ::> e
| P_murecp : forall w w' il il' ir ir' p p' u u' f f' m a b e,
              w ::> w' -> il ::> il' -> ir ::> ir' -> p ::> p' -> u ::> u' -> f ::> f' ->
              m ::> Pair__mu a b ->
              e = p'.[Rec__mu w' il' ir' p' u' f' b, b, Rec__mu w' il' ir' p' u' f' a, a/] ->
              Rec__mu w il ir p u f m ::> e
| P_murecu : forall w il ir p u u' f m,
               u ::> u' -> m ::> Unit__mu ->
               Rec__mu w il ir p u f m ::> u'
              
| P_murecf : forall w w' il il' ir ir' p p' u u' f f' m M e,
              w ::> w' -> il ::> il' -> ir ::> ir' -> p ::> p' -> u ::> u' -> f ::> f' ->
              m ::> Fix__mu M ->
              e = f'.[Rec__mu w' il' ir' p' u' f' M,M/] ->
              Rec__mu w il ir p u f m ::> e

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
    | Pair__sigma a b => Pair__sigma (rho a) (rho b)
    | Rec__sigma r ab => match rho ab with
                        | Pair__sigma a b => (rho r).[b,a/]
                        | ab' => Rec__sigma (rho r) ab'
                      end

    | Path x y => Path (rho x) (rho y)
    | Refl__path x => Refl__path (rho x)
    | Rec__path c p => match rho p with
                      | Refl__path x => (rho c)
                      | p' => Rec__path (rho c) p'
                    end
    
    | Sum__desc A B => Sum__desc (rho A) (rho B)
    | Prd__desc A B => Prd__desc (rho A) (rho B)
    | Fix__desc D => Fix__desc (rho D)

    | Rec__desc i s p u f d => 
      let i := rho i in let s := rho s in let p := rho p in let u := rho u in let f := rho f in let d := rho d in
      match d with
        | Ind__desc => i
        | Sum__desc A B => s.[Rec__desc i s p u f B, B, Rec__desc i s p u f A, A/]
        | Prd__desc A B => p.[Rec__desc i s p u f B, B, Rec__desc i s p u f A, A/]
        | Fix__desc D => f.[Rec__desc i s p u f D, D/]
        | Unit__desc => u
        | _ => Rec__desc i s p u f d
      end
                             
    | Mu D1 D2 => Mu (rho D1) (rho D2)
    | Wrap__mu m => Wrap__mu (rho m)
    | Inl__mu a => Inl__mu (rho a)
    | Inr__mu b => Inr__mu (rho b)
    | Pair__mu a b => Pair__mu (rho a) (rho b)
    | Fix__mu m => Fix__mu (rho m)

    | Rec__mu w il ir p u f m => 
      let w := rho w in let il := rho il in let ir := rho ir in let p := rho p in 
      let u := rho u in let f := rho f in let m := rho m in
      match m with
        | Wrap__mu m => w.[Rec__mu w il ir p u f m,m/]
        | Inl__mu l => il.[Rec__mu w il ir p u f l,l/]
        | Inr__mu r => ir.[Rec__mu w il ir p u f r,r/]
        | Pair__mu a b => p.[Rec__mu w il ir p u f b, b, Rec__mu w il ir p u f a, a/]
        | Unit__mu => u
        | Fix__mu d => f.[Rec__mu w il ir p u f d, d/]
        | _ => Rec__mu w il ir p u f m
      end

    | _ => e
  end.

Hint Constructors par_step.

Lemma rho_eval_to e : e ::> rho e.
Proof. induction e; simpl; try solve[try destruct match;eauto].
  remember (const_vals n) as cn; symmetry in Heqcn.
  destruct cn; auto.
Qed.
Hint Resolve rho_eval_to.

Tactic Notation "econstructor" "beta" :=
  match goal with
    | [H: context[_ ::> Lam _]         |- App _ _ ::> _] => eapply P_beta
    | [H: context[_ ::> Pair__sigma _ _] |- Rec__sigma _ _ ::> _] => eapply P_srec_beta
    | [H: context[_ ::> Refl__path _]    |- Rec__path _ _ ::> _] => eapply P_precr

    | [H: context[_ ::> Ind__desc]       |- Rec__desc _ _ _ _ _ _ ::> _] => eapply P_descr_i
    | [H: context[_ ::> Sum__desc _ _]   |- Rec__desc _ _ _ _ _ _ ::> _] => eapply P_descr_s
    | [H: context[_ ::> Prd__desc _ _]   |- Rec__desc _ _ _ _ _ _ ::> _] => eapply P_descr_p
    | [H: context[_ ::> Unit__desc]      |- Rec__desc _ _ _ _ _ _ ::> _] => eapply P_descr_u
    | [H: context[_ ::> Fix__desc _]     |- Rec__desc _ _ _ _ _ _ ::> _] => eapply P_descr_f

    | [H: context[_ ::> Wrap__mu _]      |- Rec__mu _ _ _ _ _ _ _ ::> _] => eapply P_murecw
    | [H: context[_ ::> Inl__mu _]       |- Rec__mu _ _ _ _ _ _ _ ::> _] => eapply P_murecl
    | [H: context[_ ::> Inr__mu _]       |- Rec__mu _ _ _ _ _ _ _ ::> _] => eapply P_murecr
    | [H: context[_ ::> Pair__mu _ _]    |- Rec__mu _ _ _ _ _ _ _ ::> _] => eapply P_murecp
    | [H: context[_ ::> Unit__mu]        |- Rec__mu _ _ _ _ _ _ _ ::> _] => eapply P_murecu
    | [H: context[_ ::> Fix__mu _]       |- Rec__mu _ _ _ _ _ _ _ ::> _] => eapply P_murecf
  end.

Tactic Notation "econstructor" "par" :=
  eapply P_ref + eapply P_free +
  eapply P_pi + eapply P_lam + eapply P_app +
  eapply P_sig + eapply P_smk + eapply P_srec +
  eapply P_path + eapply P_refl + eapply P_prec +
  eapply P_sdesc + eapply P_pdesc + eapply P_fdesc + eapply P_descr +
  eapply P_mu + eapply P_wmu + eapply P_inlmu + eapply P_inrmu + eapply P_parmu + eapply P_fixmu + eapply P_murec.

Tactic Notation "econstructor" "step" := econstructor beta + econstructor par.

Tactic Notation "invert" "value" "step" :=
  match goal with
    | [H: Bind _ ::> _ |- _] => inverts H
    | [H: Sort _ ::> _ |- _] => inverts H
    | [H: Pi _ _ ::> _ |- _] => inverts H
    | [H: Lam _ ::> _ |- _] => inverts H
    | [H: Sigma _ _ ::> _ |- _] => inverts H
    | [H: Pair__sigma _ _ ::> _ |- _] => inverts H
    | [H: Desc ::> _ |- _] => inverts H
    | [H: Ind__desc ::> _ |- _] => inverts H
    | [H: Sum__desc _ _ ::> _ |- _] => inverts H
    | [H: Prd__desc _ _ ::> _ |- _] => inverts H
    | [H: Unit__desc ::> _ |- _] => inverts H
    | [H: Fix__desc _ ::> _ |- _] => inverts H
    | [H: Mu _ _ ::> _ |- _] => inverts H
    | [H: Wrap__mu _ ::> _ |- _] =>  inverts H
    | [H: Inl__mu _ ::> _ |- _] => inverts H
    | [H: Inr__mu _ ::> _ |- _] => inverts H
    | [H: Pair__mu _ _ ::> _ |- _] => inverts H
    | [H: Unit__mu ::> _ |- _] => inverts H
    | [H: Fix__mu _ ::> _ |- _] => inverts H
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

Lemma sub_sig_scop : forall e sigma i j, sub_vars i j sigma -> closed_at j e -> sub_vars i.+1 j (e .: sigma).
Proof. destruct v; simpl; auto. Qed.
Hint Resolve sub_sig_scop.

Lemma sub_ids_scop : forall i, sub_vars i i ids. auto. Qed.
Hint Resolve sub_ids_scop.

(* Lemma rall_sub D : forall r e sigma, (rall D r e).[sigma] = rall D r.[up sigma] e.[sigma]. *)
(* Proof. induction D; intros; auto; simpl; rewrite asms; autosubst. Qed. *)
(* Hint Rewrite rall_sub.    *)
(* Hint Rewrite rall_sub : autosubst. *)

Hint Extern 1 (Free ?nm ::> ?e.[_]) => rewrite closed_sub_id; [constructor|eapply const_vals_closed]; eassumption.
Hint Extern 1 (const_vals ?nm = Some ?e.[_]) => rewrite closed_sub_id; try eapply const_vals_closed; eassumption.
Hint Resolve closed_sub_id.

Optimize Heap.
Lemma step_cong1 : forall e1 e2, e1 ::> e2 -> forall sigma, e1.[sigma] ::> e2.[sigma].
Proof. induction 1; intros; simpl in *; subst; try solve[try econstructor step; eauto 1; autosubst]. Optimize Proof. Qed.
Hint Resolve step_cong1.

Lemma step_up : forall c1 c2, c1 .> c2 -> up c1 .> up c2.
Proof. intros. destruct v; asimpl; auto. Qed.

Hint Resolve step_up.

Tactic Notation "auto" "upn" ident(n) := induction n; intros; repeat rewrite <- fold_up_upn; auto.
Lemma step_upn n : forall c1 c2, c1 .> c2 -> upn n c1 .> upn n c2. auto upn n. Qed.
Hint Resolve step_upn.

Lemma step_cong2 : forall e c1 c2, c1 .> c2 -> e.[c1] ::> e.[c2].
Proof. induction e; intros; simpl in *; try econstructor; eauto. Qed.

Local Hint Resolve step_cong2.
Optimize Heap.

Lemma step_cong : forall e1 e2, e1 ::> e2 -> forall c1 c2, c1 .> c2 -> e1.[c1] ::> e2.[c2].
Proof. induction 1; intros; simpl in *; subst; auto;
  econstructor step;
  try (eapply IHpar_step1 || eapply IHpar_step2 || eapply IHpar_step3 || eapply IHpar_step4
    || eapply IHpar_step5 || eapply IHpar_step6 || eapply IHpar_step7);
  try (eapply step_upn || eapply step_up); eassumption || autosubst.
  Optimize Proof.
Qed.

Optimize Heap.
Hint Resolve step_cong.

Lemma sub_cons : forall e e' sigma tau, e ::> e' -> sigma .> tau -> (e .: sigma) .> (e' .: tau). destruct v; simpl; auto. Qed.

Lemma ids_ev : ids .> ids. auto. Qed.
Lemma up_ev : forall sigma tau, sigma .> tau -> up sigma .> up tau. destruct v; simpl; auto. Qed.

Hint Resolve ids_ev up_ev sub_cons.

Lemma rho_eval_from_to e e' : e ::> e' -> e' ::> rho e.
Proof. induction 1; simpl; try (try (invert value step || destruct match); subst; eauto 10; solve by inversion).
  destruct match; inverts H; auto.
  Optimize Proof.
Qed.

Hint Resolve rho_eval_from_to.

Notation conv := (clos_refl_sym_trans _ par_step).
Notation red := (clos_trans _ par_step).
Infix "<:::>" := conv (at level 50).
Infix ":::>" := red (at level 50).

Tactic Notation "eauto" "tc" := eauto using clos_trans.
Tactic Notation "eauto" "tc" integer(n) := eauto n using clos_trans.

Lemma red_conv : forall e e', e :::> e' -> e <:::> e'. induction 1; eauto rst. Qed.
Hint Resolve red_conv.

Local Hint Resolve t_step rst_step rst_refl.
Local Hint Resolve t_trans rst_trans rst_sym : slow.

Hint Resolve rho_eval_to rho_eval_from_to.
Lemma red_l_confl e1 e2 e3 : e1 ::> e2 -> e1 :::> e3 -> exists e4, e2 :::> e4 /\ e3 ::> e4.
Proof. 
  move=> He2 He3; move: e2 He2; induction He3; intros.
  { eauto 7. }
  { do 2 (try_hyps; intuition; destr_logic); clear_funs; eauto with slow. }
Qed.
  
Lemma red_confl e1 e2 e3 : e1 :::> e2 -> e1 :::> e3 -> exists e4, e2 :::> e4 /\ e3 :::> e4.
Proof.
  move=>He2 He3; move: e3 He3; induction He2; intros.
  { extend red_l_confl; try_hyps; destr_logic; eauto with slow. }
  { do 2 (try_hyps; intuition; destr_logic); clear_funs; eauto with slow. }
Qed.

(* DO NOT hint resolve red_confl! slows conv_double_red a lot *)
(* a nice corollary of confluence is equivalence of convertibility to convergence *)
(* the convergence condition is sufficient for arbitrary relations, but only necessary for confluent ones *)
Corollary conv_double_red : forall e1 e2, e1 <:::> e2 <-> (exists e3, e1 :::> e3 /\ e2 :::> e3).
Proof.
  split; move=>H; [|destr_logic; transitivity x; eauto with slow].
  induction H; try solve[eauto].
  - destr_logic; solve[eauto].
  - destr_logic. extend red_confl.
    try_hyps; clear_funs; destr_logic; solve[eauto with slow].
Qed.

(* Hint Resolve conv_double_red. *) (* not hinting because red_confl caused problems *)
Hint Rewrite conv_double_red : unconv.

Instance red_refl : Reflexive red. eauto tc. Qed.

Lemma red_Pi_l : forall A B A', A :::> A' -> Pi A B :::> Pi A' B. induction 1; eauto tc. Qed.
Lemma red_Pi_r : forall A B B', B :::> B' -> Pi A B :::> Pi A B'. induction 1; eauto tc. Qed.
Local Hint Resolve red_Pi_l red_Pi_r.

Lemma red_Pi_Pi A B A' B' : (A :::> A') -> (B :::> B') -> Pi A B :::> Pi A' B'. transitivity (Pi A B'); eauto tc. Qed.
Hint Resolve red_Pi_Pi.

Lemma red_Sigma_l : forall A B A', A :::> A' -> Sigma A B :::> Sigma A' B. induction 1; eauto tc. Qed.
Lemma red_Sigma_r : forall A B B', B :::> B' -> Sigma A B :::> Sigma A B'. induction 1; eauto tc. Qed.
Local Hint Resolve red_Sigma_l red_Sigma_r.
 
Lemma red_Sigma_Sigma A B A' B' : (A :::> A') -> (B :::> B') -> Sigma A B :::> Sigma A' B'. transitivity (Sigma A B'); eauto tc. Qed.
Hint Resolve red_Sigma_Sigma.

Lemma red_Lam_Lam : forall e e', e :::> e' -> Lam e :::> Lam e'. induction 1; eauto tc. Qed.
Hint Resolve red_Lam_Lam.

Lemma red_Srec_l : forall r e r', r :::> r' -> Rec__sigma r e :::> Rec__sigma r' e. induction 1; auto; transitivity (Rec__sigma y e); auto. Qed.
Lemma red_Srec_r : forall r e e', e :::> e' -> Rec__sigma r e :::> Rec__sigma r e'. induction 1; auto; transitivity (Rec__sigma r y); auto. Qed.
Local Hint Resolve red_Srec_l red_Srec_r.
Lemma red_Srec_Srec r e r' e' : r :::> r' -> e :::> e' -> Rec__sigma r e :::> Rec__sigma r' e'. transitivity (Rec__sigma r' e); auto. Qed.
Hint Resolve red_Srec_Srec.

Lemma red_App_l : forall A B A', A :::> A' -> App A B :::> App A' B. induction 1; eauto tc. Qed.
Lemma red_App_r : forall A B B', B :::> B' -> App A B :::> App A B'. induction 1; eauto tc. Qed.
Local Hint Resolve red_App_l red_App_r.

Lemma red_App_App A B A' B' : (A :::> A') -> (B :::> B') -> App A B :::> App A' B'. transitivity (App A B'); eauto tc. Qed.
Hint Resolve red_App_App.

Lemma red_Pair_l : forall A B A', A :::> A' -> Pair__sigma A B :::> Pair__sigma A' B. induction 1; eauto tc. Qed.
Lemma red_Pair_r : forall A B B', B :::> B' -> Pair__sigma A B :::> Pair__sigma A B'. induction 1; eauto tc. Qed.
Local Hint Resolve red_Pair_l red_Pair_r.

Lemma red_Pair_Pair_sigma a b a' b' : a :::> a' -> b :::> b' -> Pair__sigma a b :::> Pair__sigma a' b'. transitivity (Pair__sigma a b'); eauto. Qed.

Hint Resolve red_Pair_Pair_sigma.

Lemma red_Path_l x y x' : x :::> x' -> Path x y :::> Path x' y. induction 1; eauto tc. Qed.
Lemma red_Path_r x y y' : y :::> y' -> Path x y :::> Path x y'. induction 1; eauto tc. Qed.
Local Hint Resolve red_Path_l red_Path_r.

Lemma red_Path_Path x y x' y' : x :::> x' -> y :::> y' -> Path x y :::> Path x' y'. 
Proof. transitivity (Path x' y); eauto. Qed.
Hint Resolve red_Path_Path.

Lemma red_Refl_Refl x x' : x :::> x' -> Refl__path x :::> Refl__path x'. induction 1; eauto tc. Qed.
Hint Resolve red_Refl_Refl.

Lemma red_prec_prec_l c p c' : c :::> c' -> Rec__path c p :::> Rec__path c' p. induction 1; eauto tc. Qed.
Lemma red_prec_prec_r c p p' : p :::> p' -> Rec__path c p :::> Rec__path c p'. induction 1; eauto tc. Qed.
Local Hint Resolve red_prec_prec_l red_prec_prec_r.

Lemma red_prec_prec c p c' p' : c :::> c' -> p :::> p' -> Rec__path c p :::> Rec__path c' p'.
Proof. transitivity (Rec__path c' p); eauto. Qed.
Hint Resolve red_prec_prec.

Lemma red_Fix_Fix_desc F F' : F :::> F' -> Fix__desc F :::> Fix__desc F'. induction 1; eauto tc. Qed.
Hint Resolve red_Fix_Fix_desc.

Lemma red_Sum_l A B A' : A :::> A' -> Sum__desc A B :::> Sum__desc A' B. induction 1; eauto tc. Qed.
Lemma red_Sum_r A B B' : B :::> B' -> Sum__desc A B :::> Sum__desc A B'. induction 1; eauto tc. Qed.
Hint Resolve red_Sum_l red_Sum_r.

Lemma red_Sum_Sum_desc A B A' B' : A :::> A' -> B :::> B' -> Sum__desc A B :::> Sum__desc A' B'. transitivity (Sum__desc A' B); eauto tc. Qed.
Hint Resolve red_Sum_Sum_desc.

Lemma red_Prd_l A B A' : A :::> A' -> Prd__desc A B :::> Prd__desc A' B. induction 1; eauto tc. Qed.
Lemma red_Prd_r A B B' : B :::> B' -> Prd__desc A B :::> Prd__desc A B'. induction 1; eauto tc. Qed.
Hint Resolve red_Prd_l red_Prd_r.

Lemma red_Prd_Prd_desc A B A' B' : A :::> A' -> B :::> B' -> Prd__desc A B :::> Prd__desc A' B'. transitivity (Prd__desc A' B); eauto tc. Qed.
Hint Resolve red_Prd_Prd_desc.

Lemma red_descr_descr : forall i s p u f d i' s' p' u' f' d',
                          i :::> i' -> s :::> s' -> p :::> p' -> u :::> u' -> f :::> f' -> d :::> d' ->
                          Rec__desc i s p u f d :::> Rec__desc i' s' p' u' f' d'. Admitted. (* looks basically like the above *)
Hint Resolve red_descr_descr.

Lemma red_Mu_Mu : forall D1 D2 D1' D2', D1 :::> D1' -> D2 :::> D2' -> Mu D1 D2 :::> Mu D1' D2'. Admitted.
Hint Resolve red_Mu_Mu.
Lemma red_Inl_Inl : forall e e', e :::> e' -> Inl__mu e :::> Inl__mu e'. induction 1; eauto tc. Qed.
Lemma red_Inr_Inr : forall e e', e :::> e' -> Inr__mu e :::> Inr__mu e'. induction 1; eauto tc. Qed.
Hint Resolve red_Inl_Inl red_Inr_Inr.

Lemma red_Fix_Fix_mu : forall f f', f :::> f' -> Fix__mu f :::> Fix__mu f'. induction 1; eauto tc. Qed.
Lemma red_Wrap_Wrap_mu : forall m m', m :::> m' -> Wrap__mu m :::> Wrap__mu m'. induction 1; eauto tc. Qed.
Lemma red_Pair_Pair_mu : forall a b a' b', a :::> a' -> b :::> b' -> Pair__mu a b :::> Pair__mu a' b'. Admitted.
Hint Resolve red_Fix_Fix_mu red_Wrap_Wrap_mu red_Pair_Pair_mu.

Lemma red_mur_mur : forall w il ir p u f m w' il' ir' p' u' f' m', 
                      w :::> w' -> il :::> il' -> ir :::> ir' -> p :::> p' -> u :::> u' -> f :::> f' -> m :::> m' ->
                      Rec__mu w il ir p u f m :::> Rec__mu w' il' ir' p' u' f' m'. Admitted.
Hint Resolve red_mur_mur.

Lemma red_Free nm e : Free nm :::> e <-> (e = Free nm) \/ (exists v, const_vals nm = Some v /\ v :::> e).
Proof. remember (Free nm).
  split; induction 1; subst; auto.
  - + inverts H; eauto tc.
    + intuition; subst; destr_logic; eauto tc.
  - destr_logic; transitivity x; eauto.
Qed.

Lemma red_Bind v e : Bind v :::> e <-> e = Bind v. 
Proof. remember (Bind v).
  split; induction 1; subst; auto; inversion H; subst; intuition; subst; reflexivity. 
Qed.
 
Lemma red_Sort l e : Sort l :::> e <-> e = Sort l.
Proof. remember (Sort l).
  split; induction 1; subst; auto; inversion H; subst; intuition; subst; reflexivity.
Qed.

Lemma red_Unit e : Unit__desc :::> e <-> e = Unit__desc.
Proof. remember Unit__desc.
  split; induction 1; subst; auto; inversion H; subst; intuition; subst; reflexivity.
Qed.

Lemma red_unit e : Unit__mu :::> e <-> e = Unit__mu.
Proof. remember Unit__mu.
  split; induction 1; subst; auto; inversion H; subst; intuition; subst; reflexivity.
Qed.

Lemma red_Desc e : Desc :::> e <-> e = Desc.
Proof. remember Desc.
  split; induction 1; subst; auto; inversion H; subst; intuition; subst; reflexivity.
Qed.

Hint Resolve red_Bind red_Sort red_Unit red_unit red_Desc.
Hint Rewrite red_Bind red_Sort red_Unit red_unit red_Desc.

Lemma red_Pi A B e : Pi A B :::> e <-> exists A' B', (e = Pi A' B') /\ (A :::> A') /\ (B :::> B').
Proof. split.
  { remember (A :>> B) as ab. 
    move=>Hab. move:A B Heqab.
    induction Hab; intros; subst; auto.
    { inversion H; subst; eauto 10. }
    { specialize (IHHab1 A B); intuition; destr_logic; subst.
      specialize (IHHab2 x x0); intuition; destr_logic; subst.
      repeat eexists; try reflexivity; eauto tc. } }
  { intros; destr_logic; subst; auto. }
Qed.

Lemma red_Sigma A B e : Sigma A B :::> e <-> exists A' B', (e = Sigma A' B') /\ (A :::> A') /\ (B :::> B').
Proof. split.
  { remember (Sigma A B) as ab. 
    move=>Hab. move:A B Heqab.
    induction Hab; intros; subst; auto.
    { inversion H; subst; eauto 10. }
    { specialize (IHHab1 A B); intuition; destr_logic; subst.
      specialize (IHHab2 x x0); intuition; destr_logic; subst.
      repeat eexists; try reflexivity; eauto tc. } }
  { intros; destr_logic; subst; auto. }
Qed.

Lemma red_Pair__sigma A B e : Pair__sigma A B :::> e <-> exists A' B', (e = Pair__sigma A' B') /\ (A :::> A') /\ (B :::> B').
Proof. split.
  { remember (Pair__sigma A B) as ab. 
    move=>Hab. move:A B Heqab.
    induction Hab; intros; subst; auto.
    { inversion H; subst; eauto 10. }
    { specialize (IHHab1 A B); intuition; destr_logic; subst.
      specialize (IHHab2 x x0); intuition; destr_logic; subst.
      repeat eexists; try reflexivity; eauto tc. } }
  { intros; destr_logic; subst; auto. }
Qed.

Lemma red_Prd__desc D1 D2 e : Prd__desc D1 D2 :::> e <-> exists D1' D2', (e = Prd__desc D1' D2') /\ (D1 :::> D1') /\ (D2 :::> D2').
Proof. split.
  { remember (Prd__desc D1 D2) as m; move=>Hab. move:D1 D2 Heqm.
    induction Hab; intros; subst; auto.
    { inversion H; subst; eauto 10. }
    { specialize (IHHab1 D1 D2); intuition; destr_logic; subst.
      specialize (IHHab2 x x0); intuition; destr_logic; subst.
      repeat eexists; try reflexivity; eauto tc. } }
  { intros; destr_logic; subst; auto. }
Qed.

Lemma red_Sum__desc D1 D2 e : Sum__desc D1 D2 :::> e <-> exists D1' D2', (e = Sum__desc D1' D2') /\ (D1 :::> D1') /\ (D2 :::> D2').
Proof. split.
  { remember (Sum__desc D1 D2) as m; move=>Hab. move:D1 D2 Heqm.
    induction Hab; intros; subst; auto.
    { inversion H; subst; eauto 10. }
    { specialize (IHHab1 D1 D2); intuition; destr_logic; subst.
      specialize (IHHab2 x x0); intuition; destr_logic; subst.
      repeat eexists; try reflexivity; eauto tc. } }
  { intros; destr_logic; subst; auto. }
Qed.

Lemma red_Mu D1 D2 e : Mu D1 D2 :::> e <-> exists D1' D2', (e = Mu D1' D2') /\ (D1 :::> D1') /\ (D2 :::> D2').
Proof. split.
  { remember (Mu D1 D2) as m; move=>Hab. move:D1 D2 Heqm.
    induction Hab; intros; subst; auto.
    { inversion H; subst; eauto 10. }
    { specialize (IHHab1 D1 D2); intuition; destr_logic; subst.
      specialize (IHHab2 x x0); intuition; destr_logic; subst.
      repeat eexists; try reflexivity; eauto tc. } }
  { intros; destr_logic; subst; auto. }
Qed.

Lemma red_Pair__mu D1 D2 e : Pair__mu D1 D2 :::> e <-> exists D1' D2', (e = Pair__mu D1' D2') /\ (D1 :::> D1') /\ (D2 :::> D2').
Proof. split.
  { remember (Pair__mu D1 D2) as m; move=>Hab. move:D1 D2 Heqm.
    induction Hab; intros; subst; auto.
    { inversion H; subst; eauto 10. }
    { specialize (IHHab1 D1 D2); intuition; destr_logic; subst.
      specialize (IHHab2 x x0); intuition; destr_logic; subst.
      repeat eexists; try reflexivity; eauto tc. } }
  { intros; destr_logic; subst; auto. }
Qed.

Hint Resolve red_Pi red_Sigma red_Pair__sigma red_Prd__desc red_Sum__desc red_Mu red_Pair__mu.
Hint Rewrite red_Pi red_Sigma red_Pair__sigma red_Prd__desc red_Sum__desc red_Mu red_Pair__mu.

Lemma red_Lam b e : Lam b :::> e <-> exists b', (e = Lam b') /\ (b :::> b').
Proof. split.
  { remember (Lam b) as lb. move=>Hred; move: b Heqlb. induction Hred; intros; subst; eauto.
    { inversion H; subst; eauto. }
    { specialize (IHHred1 b); intuition; destr_logic; subst.
      specialize (IHHred2 x); intuition; destr_logic; subst.
      eauto tc. } }
  { intros; destr_logic; subst; auto. }
Qed.

Lemma red_Fix__desc D e : Fix__desc D :::> e <-> exists D', (e = Fix__desc D') /\ (D :::> D').
Proof. split.
  { remember (Fix__desc D) as lD. move=>Hred; move: D HeqlD. induction Hred; intros; subst; eauto.
    { inversion H; subst; eauto. }
    { specialize (IHHred1 D); intuition; destr_logic; subst.
      specialize (IHHred2 x); intuition; destr_logic; subst.
      eauto tc. } }
  { intros; destr_logic; subst; auto. }
Qed.

Lemma red_Fix__mu c e : Fix__mu c :::> e <-> exists c', (e = Fix__mu c') /\ (c :::> c').
Proof. split.
  { remember (Fix__mu c) as lc. move=>Hred; move: c Heqlc. induction Hred; intros; subst; eauto.
    { inversion H; subst; eauto. }
    { specialize (IHHred1 c); intuition; destr_logic; subst.
      specialize (IHHred2 x); intuition; destr_logic; subst.
      eauto tc. } }
  { intros; destr_logic; subst; auto. }
Qed.

Lemma red_Wrap__mu m e : Wrap__mu m :::> e <-> exists m', (e = Wrap__mu m') /\ (m :::> m').
Proof. split.
  { remember (Wrap__mu m) as lm. move=>Hred; move: m Heqlm. induction Hred; intros; subst; eauto.
    { inversion H; subst; eauto. }
    { specialize (IHHred1 m); intuition; destr_logic; subst.
      specialize (IHHred2 x); intuition; destr_logic; subst.
      eauto tc. } }
  { intros; destr_logic; subst; auto. }
Qed.

Lemma red_Inl__mu b e : Inl__mu b :::> e <-> exists b', (e = Inl__mu b') /\ (b :::> b').
Proof. split.
  { remember (Inl__mu b) as lb. move=>Hred; move: b Heqlb. induction Hred; intros; subst; eauto.
    { inversion H; subst; eauto. }
    { specialize (IHHred1 b); intuition; destr_logic; subst.
      specialize (IHHred2 x); intuition; destr_logic; subst.
      eauto tc. } }
  { intros; destr_logic; subst; auto. }
Qed.

Lemma red_Inr__mu b e : Inr__mu b :::> e <-> exists b', (e = Inr__mu b') /\ (b :::> b').
Proof. split.
  { remember (Inr__mu b) as lb. move=>Hred; move: b Heqlb. induction Hred; intros; subst; eauto.
    { inversion H; subst; eauto. }
    { specialize (IHHred1 _ erefl); destr_logic; subst.
      specialize (IHHred2 _ erefl); destr_logic; subst.
      eauto tc. } }
  { intros; destr_logic; subst; auto. }
Qed.

Hint Resolve red_Lam red_Fix__desc red_Fix__mu red_Wrap__mu red_Inl__mu red_Inr__mu.
Hint Rewrite red_Lam red_Fix__desc red_Fix__mu red_Wrap__mu red_Inl__mu red_Inr__mu.

Lemma sred_cong1 : forall e e' sigma, e :::> e' -> e.[sigma] :::> e'.[sigma]. induction 1; eauto tc. Qed.
Local Hint Resolve sred_cong1.

Notation sred sigma tau := (forall i : var, sigma i :::> tau i).
Infix "..>" := sred (at level 50).

Lemma sred_ref : forall sigma, sigma ..> sigma. intros; eauto. Qed.
Lemma sub_sred : forall sigma tau, sigma ..> tau -> forall e e', e :::> e' -> (e .: sigma) ..> (e' .: tau). intros; destruct i; simpl; auto. Qed.

Lemma sred_trans : forall delta sigma tau, delta ..> sigma -> sigma ..> tau -> delta ..> tau. eauto tc. Qed.

Lemma up_sred : forall sigma tau, sigma ..> tau -> up sigma ..> up tau. intros; destruct i; asimpl; auto. Qed.
Hint Resolve up_sred sub_sred sred_ref.
Lemma upn_sred n : forall sigma tau, sigma ..> tau -> upn n sigma ..> upn n tau. auto upn n. Qed.
Hint Resolve upn_sred.

(* CURRENT POINT *)
Lemma sred_cong2 : forall e sigma tau, sigma ..> tau -> e.[sigma] :::> e.[tau]. induction e; intros; simpl; auto. 

Qed.
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
      destr_logic; subst; [|right; eauto tc].
      specialize (IHHred2 _ _ erefl).
      destr_logic; subst; [left|right]; eauto tc 7. } }
  { intros; destr_logic; subst; auto.
    eapply t_trans with (y := Lam _ :$: a);
      [|eapply t_trans with (y := _.[a/])]; eauto. }
Qed.

Lemma red_Srec r p e : Rec__sigma r p :::> e <-> (exists r' p', e = Rec__sigma r' p' /\ r :::> r' /\ p :::> p') \/
                                          (exists a b, p :::> Pair__sigma a b /\ r.[b,a/] :::> e).
Proof. split.
  { remember (Rec__sigma r p) as srp.
    move=>Hred; move: r p Heqsrp; induction Hred; intros; subst.
    { inverts H; solve[left; eauto 7 | right; eauto 10]. }
    { specialize (IHHred1 _ _ erefl).
      destr_logic; subst; [|right; eauto tc].
      specialize (IHHred2 _ _ erefl).
      destr_logic; subst; [left|right]; eauto tc 7. } }
  { intros; destr_logic; subst; auto.
    eapply t_trans with (y := Rec__sigma r (Pair__sigma _ _));
      [|eapply t_trans with (y := r.[_,_/])]; eauto. }
Qed.

Hint Rewrite red_Free red_App red_Srec : beta.
(* let's see if we actually need the red_*rec lemmas - decent chance we will for some progress lemmas *)

Notation sconv sigma tau := (forall i, sigma i <:::> tau i).
Infix "<..>" := sconv (at level 20).

Lemma sconv_cong1 sigma e1 e2 : e1 <:::> e2 -> e1.[sigma] <:::> e2.[sigma].
Proof. autorewrite with unconv; intros; destr_logic; eauto. Qed.
Hint Resolve sconv_cong1.

Lemma sconv_up sigma tau : sigma <..> tau -> up sigma <..> up tau.
Proof. intros; destruct i; asimpl; auto. Qed.
Hint Resolve sconv_up.

Lemma sconv_upn n sigma tau : sigma <..> tau -> upn n sigma <..> upn n tau. auto upn n. Qed.
Hint Resolve sconv_upn.

Optimize Heap.
Lemma sconv_cong2 e : forall sigma tau, sigma <..> tau -> e.[sigma] <:::> e.[tau].
Proof. induction e; simpl; intros; auto;
  repeat match goal with 
           | [IH: forall sigma tau, sigma <..> tau -> _, H: ?sigma <..> ?tau |- _]
             => pose proof (IH _ _ H); pose proof (IH _ _ (sconv_up _ _ H));
               pose proof (IH _ _ (sconv_upn 2 _ _ H)); pose proof (IH _ _ (sconv_upn 4 _ _ H));
               clear IH
         end;
  autorewrite with unconv in *; destr_logic; eauto.
Qed.
Hint Resolve sconv_cong2.

Lemma sconv_cong e1 e2 sigma tau : e1 <:::> e2 -> sigma <..> tau -> e1.[sigma] <:::> e2.[tau]. intros; transitivity (e1.[tau]); auto. Qed.
Hint Resolve sconv_cong.

(* Lemma conv_Bind_iff i j : Bind i <:::> Bind j <-> i = j.  *)
(* Proof. autorewrite with unconv; split; intros; destr_logic; autorewrite with core in *; destr_logic; subst; congruence || eauto. Qed. *)

(* Lemma conv_Sort_iff i j : Sort i <:::> Sort j <-> i = j.  *)
(* Proof. autorewrite with unconv; split; intros; destr_logic; autorewrite with core in *; destr_logic; subst; congruence || eauto. Qed. *)

(* Lemma conv_Mu_iff D1 D2 : Mu D1 <:::> Mu D2 <-> D1 = D2. *)
(* Proof. autorewrite with unconv; split; intros; destr_logic; autorewrite with core in *; destr_logic; subst; congruence || eauto. Qed. *)

(* Hint Rewrite conv_Bind_iff conv_Sort_iff conv_Mu_iff. *)

(* Lemma conv_Lam_iff b1 b2 : Lam b1 <:::> Lam b2 <-> b1 <:::> b2. *)
(* Proof. autorewrite with unconv; split; intros; destr_logic; autorewrite with core in *; destr_logic; eauto. *)
(*   subst; inversion H0; subst; eauto. *)
(* Qed. *)

(* Lemma conv_Inl__mu_iff b1 b2 : Inl__mu b1 <:::> Inl__mu b2 <-> b1 <:::> b2. *)
(* Proof. autorewrite with unconv; split; intros; destr_logic; autorewrite with core in *; destr_logic; eauto. *)
(*   subst; inversion H0; subst; eauto. *)
(* Qed. *)

(* Lemma conv_Inr__mu_iff b1 b2 : Inr__mu b1 <:::> Inr__mu b2 <-> b1 <:::> b2. *)
(* Proof. autorewrite with unconv; split; intros; destr_logic; autorewrite with core in *; destr_logic; eauto. *)
(*   subst; inversion H0; subst; eauto. *)
(* Qed. *)

(* Hint Rewrite conv_Lam_iff conv_Inl__mu_iff conv_Inr__mu_iff. *)

(* Lemma conv_Pi_iff A B A' B' : (Pi A B <:::> Pi A' B') <-> (A <:::> A' /\ B <:::> B'). *)
(* Proof. autorewrite with unconv; split; intros; destr_logic; autorewrite with core in *; destr_logic; eauto. *)
(*   subst. inversion H0; subst. split; eauto. *)
(* Qed. *)

(* Lemma conv_Sigma_iff A B A' B' : (Sigma A B <:::> Sigma A' B') <-> (A <:::> A' /\ B <:::> B'). *)
(* Proof. autorewrite with unconv; split; intros; destr_logic; autorewrite with core in *; destr_logic; eauto. *)
(*   subst. inversion H0; subst. split; eauto. *)
(* Qed. *)

(* Lemma conv_Sum_iff A B A' B' : (Sum A B <:::> Sum A' B') <-> (A <:::> A' /\ B <:::> B'). *)
(* Proof. autorewrite with unconv; split; intros; destr_logic; autorewrite with core in *; destr_logic; eauto. *)
(*   subst. inversion H0; subst. split; eauto. *)
(* Qed. *)

(* Lemma conv_Pair__sigma_iff A B A' B' : (Pair__sigma A B <:::> Pair__sigma A' B') <-> (A <:::> A' /\ B <:::> B'). *)
(* Proof. autorewrite with unconv; split; intros; destr_logic; autorewrite with core in *; destr_logic; eauto. *)
(*   subst. inversion H0; subst. split; eauto. *)
(* Qed. *)

(* Hint Rewrite conv_Pi_iff conv_Sigma_iff conv_Sum_iff conv_Pair__sigma_iff. *)

(* Lemma conv_Pi_Pi A B A' B' : A <:::> A' -> B <:::> B' -> Pi A B <:::> Pi A' B'. *)
(* Proof. autorewrite with core; auto. Qed. *)

(* Lemma conv_Sigma_Sigma A B A' B' : A <:::> A' -> B <:::> B' -> Sigma A B <:::> Sigma A' B'. *)
(* Proof. autorewrite with core; auto. Qed. *)

(* Lemma conv_Sum_Sum A B A' B' : A <:::> A' -> B <:::> B' -> Sum A B <:::> Sum A' B'. *)
(* Proof. autorewrite with core; auto. Qed. *)

(* Lemma conv_Pair__sigma_Pair__sigma A B A' B' : A <:::> A' -> B <:::> B' -> Pair__sigma A B <:::> Pair__sigma A' B'. *)
(* Proof. autorewrite with core; auto. Qed. *)

(* Lemma conv_Lam_Lam : forall b1 b2, b1 <:::> b2 -> Lam b1 <:::> Lam b2. intros; autorewrite with core; auto. Qed. *)

(* Hint Resolve conv_Pi_Pi conv_Sigma_Sigma conv_Sum_Sum conv_Pair__sigma_Pair__sigma conv_Lam_Lam. *)

(* Lemma conv_Srec_Srec : forall r p r' p', r <:::> r' -> p <:::> p' -> Rec__sigma r p <:::> Rec__sigma r' p'. *)
(* Proof. intros; autorewrite with unconv in *; destr_logic; eauto. Qed. *)

(* Hint Resolve conv_Srec_Srec. *)

(* Lemma conv_Inl__mu_Inl__mu : forall e e', e <:::> e' -> Inl__mu e <:::> Inl__mu e'. intros; autorewrite with core; auto. Qed. *)
(* Lemma conv_Inr__mu_Inr__mu : forall e e', e <:::> e' -> Inr__mu e <:::> Inr__mu e'. intros; autorewrite with core; auto. Qed. *)
(* Hint Resolve conv_Inl__mu_Inl__mu conv_Inr__mu_Inr__mu. *)

(* Lemma conv_App_App f a f' a' : (f <:::> f') -> (a <:::> a') -> ((f :$: a) <:::> (f' :$: a')). *)
(* Proof. autorewrite with unconv; intros; destr_logic; autorewrite with core in *; destr_logic; eauto. Qed. *)
(* Hint Resolve conv_App_App. *)

(* Lemma conv_Split_Split a b c a' b' c' : (a <:::> a') -> (b <:::> b') -> (c <:::> c') -> Split a b c <:::> Split a' b' c'. *)
(* Proof. autorewrite with unconv; intros; destr_logic; autorewrite with core in *; destr_logic; eauto. Qed. *)
(* Hint Resolve conv_Split_Split. *)

(* Lemma conv_mu_mu D A B A' B' : (A <:::> A') -> (B <:::> B') -> mu D A B <:::> mu D A' B'. *)
(* Proof. autorewrite with unconv; intros; destr_logic; autorewrite with core in *; destr_logic; eauto. Qed. *)
(* Hint Resolve conv_mu_mu. *)

(* Definition subtyp A B := (A <:::> B \/ exists i j, A <:::> Sort i /\ B <:::> Sort j /\ i < j). *)
(* Infix "::<<" := subtyp (at level 20). *)

(* Lemma conv_sort_red e i : e <:::> Sort i <-> e :::> Sort i. *)
(* Proof. split; [|auto]. autorewrite with unconv; intros; destr_logic; autorewrite with core in *; subst; auto. Qed. *)
(* (* Hint Resolve conv_sort_red. *) *)
(* Hint Rewrite conv_sort_red : unconv. *)

(* Hint Resolve red_conv. *)
(* Lemma conv_ext_l e1 e2 e3 : e1 <:::> e2 -> e2 :::> e3 -> e1 <:::> e3. eauto using clos_refl_sym_trans. Qed. *)
(* Lemma conv_ext_r e1 e2 e3 : e1 :::> e2 -> e2 <:::> e3 -> e1 <:::> e3. eauto using clos_refl_sym_trans. Qed. *)
(* Hint Resolve conv_ext_l conv_ext_r : slow. *)

(* Instance subtyp_refl : Reflexive subtyp. unfold subtyp; auto. Qed. *)

(* Hint Resolve sconv_cong1 sconv_cong2 sconv_cong. *)

(* Instance subtyp_trans : Transitive subtyp.  *)
(* Proof. repeat destruct 1; destr_logic; autorewrite with core in *. *)
(*   - left; eauto rst. *)
(*   - right; eauto rst 7. *)
(*   - assert (z <:::> Sort x1) by eauto using rst_trans,rst_sym. *)
(*     right; eauto 7. *)
(*   - assert (Sort x3 <:::> Sort x0) by eauto rst. *)
(*     autorewrite with core in *; subst. *)
(*     right; exists x2; exists x1; repeat split; [eauto rst|eauto rst|transitivity x0]; auto. *)
(* Qed. *)

(* Lemma subtyp_cong1 A B sigma : subtyp A B -> subtyp A.[sigma] B.[sigma].  *)
(* Proof. destruct 1; [left|right]; destr_logic; auto. *)
(*   repeat eexists; *)
(*   match goal with [|-context[Sort ?i]] => change (Sort i) with (Sort i).[sigma] | _ => eassumption end; *)
(*   auto. *)
(* Qed. *)

Lemma closed_step e e' n : e ::> e' -> closed_at n e -> closed_at n e'.
Proof.
  move=> He'; move: n; induction He'; simpl in *; intros; subst;
  autounfold in *; destr bands;
  try solve[repeat (apply andb_true_intro; split); auto|
  match goal with [H:  closed_at (?m.+1 + ?n) ?e = true
                    ,IH: context[closed_at _ ?e = true -> closed_at _ ?e' = true]
                    |-   context[?e'.[_]]] => 
                    apply cons_scoped with (i := (m + n)) end;
    [intro v; repeat match goal with [|-context[_ .: _]] => destruct v; simpl end; auto| |];
    simpl; autounfold; autorewrite with core; firstorder].

  - apply closed_lift with (i := 0); [|apply const_vals_closed with (nm := nm)]; auto.
  - apply cons_scoped with (i := n); auto.
Qed.

Hint Resolve closed_step.
