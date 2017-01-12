Require Import Prelude.
Require Import Autosubst.Autosubst.

Tactic Notation "arewrite" := autorewrite with autosubst.
Hint Rewrite Bool.andb_true_iff Bool.andb_false_iff Bool.orb_true_iff Bool.orb_false_iff : bool.

Set Boolean Equality Schemes.
Set Decidable Equality Schemes.
Scheme Equality for nat.

Inductive exp : Type :=
| Typ : exp

| Pi : exp -> {bind exp} -> exp
| Lam : exp -> {bind exp} -> exp
| App : exp -> exp -> exp

(* | Sig : exp -> {bind exp} -> exp *)
(* | Pair : exp -> exp -> exp *)
(* | Srec : {bind exp} -> {bind 2 of exp in exp} -> exp -> exp *)

| Var : var -> exp
(* | W : exp -> {bind exp} -> exp *)
(* | Sup : exp -> {bind exp} -> exp *)
(* | Wrec : {bind exp} -> {bind 3 of exp in exp} -> exp -> exp *)

(* | Top : exp *)
(* | Unit : exp *)
(* | Trec : {bind exp} -> exp -> exp -> exp *)

(* | Bot : exp *)
(* | Exfal : {bind exp} -> exp -> exp *)

(* | Bool : exp *)
(* | Brec : {bind exp} -> exp -> exp -> exp -> exp *)

(* | Path : exp -> exp -> exp -> exp *)
(* | Refl : exp -> exp -> exp *)
(* | Prec : exp -> {bind exp} -> exp -> exp -> exp *)
.

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

Notation "( && b )" := (fun b' => b' && b).
Fixpoint closed_at (l : nat) (e : exp) : bool.
Proof.
  destruct e; 
  repeat match goal with
           | [i : var |- _] => exact: (i < l)
           | [e : {bind ?n of exp} |- _] => apply (&& closed_at (n + l) e); clear e
           | [e : exp |- _] => apply (&& closed_at l e); clear e
           | _ => exact: true
         end.
Defined.

(* While we're at it *)
Ltac mk_size T f :=
  simpl in *; repeat match goal with [e : T |- _] => apply f in e; apply (+ e) | _ => exact: 1 end.
      
Fixpoint term_size (e : exp) : nat.
  destruct e; mk_size exp term_size.
Defined.

Infix ":>>" := Pi (at level 20, right associativity).
Infix ":#>" := Lam (at level 30, right associativity).
Infix ":$:" := App (at level 50, left associativity).

Reserved Notation "a ::> b" (at level 50).
(* Variable const_vals : env exp. *)
(* Hypothesis const_vals_closed : forall nm e, const_vals nm = Some e -> closed e. *)
(* Hint Resolve const_vals_closed. *)

Inductive par_step : relation exp :=
| P_ref    : forall e, e ::> e
(* | P_free   : forall nm e, const_vals nm = Some e -> Free nm ::> e *)

| P_pi     : forall A A' B B', A ::> A' -> B ::> B' -> A :>> B ::> A' :>> B'
(* | P_lam    : forall A A' b b', A ::> A' -> b ::> b' -> A :#> b ::> A' :#> b' *)
| P_lam    : forall A A' b b', A ::> A' -> b ::> b' -> A :#> b ::> A' :#> b'
| P_app    : forall f f' a a', f ::> f' -> a ::> a' -> (f :$: a) ::> (f' :$: a')
(* | P_beta   : forall f A b a a', f ::> (A :#> b) -> a ::> a' -> (f :$: a) ::> b.[a'/] *)
| P_beta   : forall u A f b a a', f ::> A :#> b -> a ::> a' -> u = b.[a'/] -> (f :$: a) ::> u
where "a ::> b" := (par_step a b).

Hint Constructors par_step.

Fixpoint rho (e : exp) : exp :=
  match e with
    | A :>> B => rho A :>> rho B
    | A :#> b => rho A :#> rho b
    | f :$: x => match rho f with
                  | (_ :#> b) => b.[rho x/]
                  | _ => rho f :$: rho x
                end
    | _ => e
  end.

Notation conv := (clos_refl_sym_trans _ par_step).
Notation red := (clos_trans _ par_step).
Infix "<:::>" := conv (at level 50).
Infix ":::>" := red (at level 50).

Fixpoint dget (i : nat) (Gamma : seq exp) : exp :=
  match Gamma with
    | T :: Gamma => match i with 0 => T | S i => dget i Gamma end.[ren (+1)]
    | _ => Var 0
  end.

Inductive is_type (Gamma : seq exp) : exp -> Prop := 
| T_typ : is_type Gamma Typ
| T_pi : forall A B, is_type Gamma A -> is_type (A :: Gamma) B -> is_type Gamma (A :>> B)
| T_ht : forall T, has_type Gamma T Typ -> is_type Gamma T
with has_type (Gamma : seq exp) : relation exp := 
| T_pi_t : forall A B, has_type Gamma A Typ -> has_type (A :: Gamma) B Typ -> has_type Gamma (A :>> B) Typ
| T_lam : forall A B b, is_type Gamma A -> has_type (A :: Gamma) b B -> has_type Gamma (A :#> b) (A :>> B)
| T_app : forall A B f a, has_type Gamma f (A :>> B) -> has_type Gamma a A -> forall u, u = B.[a/] -> has_type Gamma (f :$: a) u
| T_var : forall i, i < size Gamma -> forall u, u = dget i Gamma -> has_type Gamma (Var i) u
| T_conv : forall a A A', A <:::> A' -> has_type Gamma a A -> has_type Gamma a A'
.
Notation "'[' C '|+' e ':<' t ']'" := (has_type C e t) (at level 20).
Notation "'[' C '|+' T ']'" := (is_type C T) (at level 20).

Hint Constructors is_type has_type.

Scheme m_is_type_ind  := Induction for is_type  Sort Prop
with   m_has_type_ind := Induction for has_type Sort Prop.

Combined Scheme typing_ind from m_is_type_ind, m_has_type_ind.

(* PROOFS *)
Lemma rho_direct : forall e, e ::> rho e. induction e; simpl; try destruct match; eauto. Qed.
Hint Resolve rho_direct.

Lemma step_sub_cong1 : forall e1 e2, e1 ::> e2 -> forall sigma, e1.[sigma] ::> e2.[sigma].
Proof. induction 1; simpl; intros; econstructor; subst; eauto; autosubst. Qed.

Hint Resolve step_sub_cong1.

Notation spstep sigma tau := (forall v, sigma v ::> tau v).
Infix ".>" := spstep (at level 50).

Lemma step_up : forall c1 c2, c1 .> c2 -> up c1 .> up c2.
Proof. intros; destruct v; asimpl; auto. Qed.
Hint Resolve step_up.

Tactic Notation "auto" "upn" ident(n) := induction n; intros; repeat rewrite <- fold_up_upn; auto.
Lemma step_upn n : forall c1 c2, c1 .> c2 -> upn n c1 .> upn n c2. auto upn n. Qed.
Hint Resolve step_upn.

Lemma step_sub_cong2 : forall e c1 c2, c1 .> c2 -> e.[c1] ::> e.[c2].
Proof. induction e; intros; simpl in *; try econstructor; eauto. Qed.

Local Hint Resolve step_sub_cong2.

Lemma step_sub_cong : forall e1 e2, e1 ::> e2 -> forall c1 c2, c1 .> c2 -> e1.[c1] ::> e2.[c2].
Proof. induction 1; simpl; intros; eauto.
  econstructor; [apply IHpar_step1|apply IHpar_step2|]; eauto; subst; autosubst.
Qed.

Local Hint Resolve step_sub_cong.

Lemma sub_cons : forall e e' sigma tau, e ::> e' -> sigma .> tau -> (e .: sigma) .> (e' .: tau). destruct v; simpl; auto. Qed.
Hint Resolve sub_cons.  

Lemma rho_indirect : forall e e',  e ::> e' -> e' ::> rho e. 
Proof. induction 1; simpl; eauto.
  { subst; destruct match; eauto. }
  { subst; inverts IHpar_step1; eauto. }
Qed.

Hint Resolve rho_indirect rho_direct.

Tactic Notation "eauto" "tc" := eauto using clos_trans.
Tactic Notation "eauto" "tc" integer(n) := eauto n using clos_trans.

Lemma red_conv : forall e e', e :::> e' -> e <:::> e'. induction 1; eauto rst. Qed.
Hint Resolve red_conv.

Local Hint Resolve t_step rst_step rst_refl.
Local Hint Resolve t_trans rst_trans rst_sym : slow.

Lemma red_l_fill a b c : a ::> b -> a :::> c -> exists d, b :::> d /\ c ::> d.
Proof. move=> Hb Hc; move: b Hb; induction Hc; intros; eauto.
  { exists (rho x); eauto. }
  { try_hyps; destr_logic; try_hyps; destr_logic; eauto tc. }
Qed.

Theorem red_confl a b c : a :::> b -> a :::> c -> exists d, b :::> d /\ c :::> d.
Proof. move=> Hb Hc; move: c Hc; induction Hb; intros.
  { destruct (red_l_fill _ _ _ H Hc); firstorder. }
  { try_hyps; destr_logic; try_hyps; destr_logic; eauto tc. }
Qed. 

Theorem conv_double_red a b : a <:::> b <-> (exists c, a :::> c /\ b :::> c).
Proof. split.
  { induction 1; destr_logic; eauto tc.
    destruct (red_confl _ _ _ H4 H1). 
    destr_logic; exists x2; split; eauto tc. }
  { intros; destr_logic; eauto rst. }
Qed.

Hint Rewrite conv_double_red : unconv.

(* SUBSTITUTIONS *)
Notation upnren := (fun n => iterate upren n).

Hint Resolve iterate_S iterate_0.
Hint Rewrite ltn_add2l.
Notation mono sigma := (forall i j, i < j -> sigma i < sigma j).
Lemma upren_mono_less : forall v sigma, mono sigma -> upren sigma v <= sigma v. induction v; simpl; intros; auto. Qed.
Lemma wk_mono : forall k, mono (+k). intros; autorewrite with core; auto. Qed.
Lemma upren_mono : forall sigma, mono sigma -> mono (upren sigma). destruct i,j; solve by inversion || simpl; eauto. Qed.

Lemma iterate_preserves A P (f : A -> A) : (forall a, P a -> P (f a)) -> forall n a, P a -> P (iterate f n a).
Proof. induction n; eauto. Qed.
  
Hint Resolve upren_mono_less wk_mono upren_mono.
Hint Rewrite upren_mono_less wk_mono upren_mono.

Lemma upnren_mono : forall n sigma, mono sigma -> mono (upnren n sigma). intros n sigma. apply iterate_preserves; auto. Qed.
Hint Resolve upnren_mono.
Lemma upnren_mono_less : forall n v sigma, mono sigma -> upnren n sigma v <= sigma v.
Proof. induction n; intros; rewrite ?iterate_S; auto. transitivity (upnren n sigma v); auto. Qed.
Hint Resolve upnren_mono_less.

Hint Rewrite up_upren_n_internal up_upren_internal using now auto 0 : ren.
Hint Resolve up_upren_n_internal up_upren_internal.
Hint Resolve andb_true_intro.

Notation sub_eq sigma tau := (forall v, sigma v = tau v).
Lemma up_resp_eq : forall sigma tau, sub_eq sigma tau -> sub_eq (up sigma) (up tau). destruct v; asimpl; rewrite asms; auto. Qed.
Hint Resolve up_resp_eq.

Lemma upn_resp_eq n : forall sigma tau, sub_eq sigma tau -> sub_eq (upn n sigma) (upn n tau). 
Proof. induction n; intros; auto.
  repeat match goal with [|-context[upn ?n.+1 ?sigma ?v]] => change (upn n.+1 sigma v) with (up (upn n sigma) v) end.
  auto.
Qed.
Hint Resolve upn_resp_eq.

Lemma sub_vars_tms : forall e sigma tau, sub_eq sigma tau -> e.[sigma] = e.[tau]. induction e; intros; simpl; f_equal; eauto. Qed.
Hint Resolve sub_vars_tms.
Hint Rewrite sub_vars_tms using assumption.

Canonical sub_eq_refl : Reflexive (fun (sigma tau : var -> exp) => sub_eq sigma tau). constructor. Qed.

Hint Rewrite sub_vars_tms using auto.
Hint Resolve sub_vars_tms.

(* SCOPING *)
Notation closed := (closed_at 0).

Notation closed_sub l sigma := (forall i, i < l -> sigma i = Var i).
Lemma closed_up : forall l sigma, closed_sub l sigma -> closed_sub l.+1 (up sigma).
Proof. intros. destruct i; asimpl; eauto. rewrite asms; eauto. Qed.
Hint Resolve closed_up.

Lemma closed_upn : forall n l sigma, closed_sub l sigma -> closed_sub (n + l) (upn n sigma).
Proof. induction n; intros; asimpl; auto.
  replace (upn n.+1 sigma i) with (up (upn n sigma) i) by autosubst.
  destruct i; asimpl; erewrite asms; try eassumption; auto.
Qed.
Hint Resolve closed_upn.

Hint Rewrite Bool.orb_false_r Bool.orb_true_iff.
Hint Rewrite Bool.andb_negb_r Bool.andb_true_iff.
Hint Resolve andb_prop Bool.orb_prop.

(* This proof is gross for stupid reasons - fix later *)
Hint Resolve andb_true_intro.
Lemma closed_lift : forall e i j, i <= j -> closed_at i e -> closed_at j e.
Proof. induction e; intros; simpl in *; try reflexivity; unfold is_true in *;
  apply leq_trans with (n := i) ||
  destr bands;
  erewrite asms; auto.
Qed.

(* Hint Resolve le_pred le_S_n le_0_n le_n_S. *)
(* Hint Rewrite leq_subLR leq_subr leq_sub2r ltnS. *)

Lemma closed_under : forall i j sigma, i <= j -> closed_sub j sigma -> closed_sub i sigma.
Proof. induction i; intros; solve by inversion || eauto using leq_trans. Qed.

Lemma closed_at_sub_id : forall e i sigma, closed_sub i sigma -> closed_at i e -> e.[sigma] = e.
Proof. induction e; intros i sigma Hsig;
  intros; simpl in *; auto;
  autounfold in *; autorewrite with core in *;
  destr_logic; erewrite asms; eauto.
Qed.

Hint Rewrite closed_at_sub_id using assumption || now auto.

Lemma sub_0 : forall sigma, closed_sub 0 sigma. intros; solve by inversion. Qed.
Hint Resolve sub_0.

Notation sub_vars i j sigma := (forall v, v < i -> closed_at j (sigma v)).

Notation closed_ren i j xi := (forall v, v < i -> xi v < j).
Lemma ren_upren : forall i j xi, closed_ren i j xi -> closed_ren i.+1 j.+1 (upren xi).
Proof. destruct v; simpl; intros; firstorder. Qed.
Hint Resolve ren_upren.

Lemma ren_upnren n : forall i j xi, closed_ren i j xi -> closed_ren (n + i) (n + j) (upnren n xi).
Proof. induction n; intros; rewrite ?iterate_0 ?iterate_S; auto.
  apply ren_upren with (i := n + i); firstorder.
Qed.
Hint Resolve ren_upnren.  

(* Hint Rewrite @iterate_S @iterate_0 : autosubst. *)

Lemma ren_closed_corr e : forall i j xi, closed_ren i j xi -> closed_at i e -> closed_at j e.[ren xi].
Proof. induction e; simpl; intros; autounfold in *; destr bands; auto; asimpl.
  all: autorewrite with bool in *; split; auto.
  all: try eapply IHe0; try apply ren_upren; eauto.
Qed.

Hint Resolve ren_closed_corr.

Notation wk i := (ren (+i)).
Lemma ren_wk_scoped : forall i j, closed_ren i (j + i) (+j). auto. Qed.
Hint Resolve ren_wk_scoped.
Lemma wk_scoped i j e : closed_at i e -> closed_at (j + i) e.[wk j]. eapply ren_closed_corr; auto. Qed.
Hint Resolve wk_scoped.
Lemma wk1_scoped i e  : closed_at i e -> closed_at i.+1 e.[wk 1]. change i.+1 with (1 + i); auto. Qed.
Hint Resolve wk1_scoped.

Lemma up_vars : forall i j sigma, sub_vars i j sigma -> sub_vars i.+1 j.+1 (up sigma).
Proof. intros. destruct v; asimpl; auto. Qed.

Hint Resolve up_vars.

Lemma wk_vars : forall i, sub_vars i i.+1 (wk 1). auto. Qed.

Lemma upn_vars n : forall i j sigma, sub_vars i j sigma -> sub_vars (n + i) (n + j) (upn n sigma).
Proof. induction n; auto. destruct v; simpl; intros; auto.
  asimpl; apply wk1_scoped; eapply IHn; eassumption.
Qed.

Hint Resolve up_vars upn_vars wk_vars.

Lemma sub_vars_scoped : forall e i j sigma, sub_vars i j sigma -> closed_at i e -> closed_at j e.[sigma].
Proof. move=>e i j sigma Hs He.
  move: i He j sigma Hs.
  induction e; intros; simpl; try (erewrite asms; auto;
  try (apply upn_vars || apply up_vars);
  solve [simpl in *; unfold is_true in *; destr bands; eassumption || auto]).  
Qed.

Hint Resolve sub_vars_scoped.

Lemma closed_sub_id : forall e sigma, closed e -> e.[sigma] = e.
Proof. intros; apply closed_at_sub_id with (i := 0); intros; solve by inversion || auto. Qed.

Lemma cons_vars_scoped e sigma i j : sub_vars i j sigma -> closed_at j e -> sub_vars i.+1 j (e .: sigma). intros; destruct v; simpl; auto. Qed.
Hint Resolve cons_vars_scoped.

Lemma cons_scoped sigma i j v e : sub_vars i j sigma -> closed_at j v -> closed_at i.+1 e -> closed_at j e.[v .: sigma].
Proof. intros; eapply sub_vars_scoped; eassumption || apply cons_vars_scoped; auto. Qed.
Hint Resolve cons_scoped.

Lemma cons_id_scoped i v e : closed_at i v -> closed_at i.+1 e -> closed_at i e.[v/]. 
Proof. apply cons_scoped with (i := i); auto. Qed.
Hint Resolve cons_id_scoped.

(* SUBSTITUTION TYPING *)
Notation "'[' D '|+' sigma '+|' G ']'" := (forall x, x < size G -> [D |+ sigma x :< (dget x G).[sigma]]) (at level 20).

Lemma sub_cons_var sigma e E Gamma Delta : [Delta |+ sigma +| Gamma] -> 
                               [Delta |+ e :< E.[sigma]] -> 
                               [Delta |+ e .: sigma +| E :: Gamma].
Proof. intros; destruct x; asimpl; eauto. Qed.

Hint Constructors has_type.
Lemma sub_id_ref : forall Gamma, [Gamma |+ ids +| Gamma]. intros; asimpl; auto. Qed.
Lemma sub_wk_var : forall Gamma A, [A :: Gamma |+ wk 1 +| Gamma]. intros; asimpl; constructor; auto. Qed.

Hint Resolve sub_id_ref sub_wk_var sub_cons_var.

Lemma dget_nth : forall Gamma n, n <  size Gamma -> dget n Gamma = (nth (ids 0) Gamma n).[wk n.+1].
  induction Gamma; simpl.
  { inversion 1. }
  { intros. destruct n; simpl; auto. 
    rewrite IHGamma; autosubst. }
Qed.
  
Functional Scheme sub_ind := Induction for minus Sort Prop.

Lemma upren_dget Gamma Delta xi A : (forall v, v < size Gamma -> (dget v Gamma).[ren xi] = dget (xi v) Delta) -> 
                           forall v, v < (size Gamma).+1 -> (dget v (A :: Gamma)).[ren (upren xi)] = dget (upren xi v) (A.[ren xi] :: Delta).
Proof. simpl in *; intros; destruct v; asimpl; auto. rewrite <- H; autosubst. Qed.
Hint Resolve upren_dget.

Lemma conv_sub_cong1 : forall a b sigma, a <:::> b -> a.[sigma] <:::> b.[sigma].
Proof. induction 1; eauto rst. Qed.

Hint Resolve conv_sub_cong1.

Check typing_ind.

Ltac pop_prems Hyp tac step last :=
  match type of Hyp with
    | (?P -> ?Q) => 
      let Prem := fresh "Prem" 
      in (assert (Prem : P); [tac|specialize (Hyp Prem); step; pop_prems Hyp tac step last])
    | _ => last
  end.
                         
Tactic Notation "pop" "prems" ident(H) tactic(tac) tactic(step) tactic(last) := pop_prems H tac step last.
Tactic Notation "pop" "prems" ident(H) tactic(tac) tactic(step) := pop_prems H tac step idtac.
Tactic Notation "pop" "prems" ident(H) tactic(tac) := pop_prems H tac idtac idtac.
Tactic Notation "pop" "prems" ident(H) := pop_prems H idtac idtac idtac.
      
Lemma upren_wk e r : e.[wk 1].[ren (upren r)] = e.[ren r].[wk 1]. autosubst. Qed.

Lemma ty_renaming_aux Gamma Delta xi :
  closed_ren (size Gamma) (size Delta) xi
  -> (forall v, v < size Gamma -> (dget v Gamma).[ren xi] <:::> dget (xi v) Delta)
  -> (forall A, [Gamma |+ A] -> [Delta |+ A.[ren xi]])
    /\ (forall a A, [Gamma |+ a :< A] -> [Delta |+ a.[ren xi] :< A.[ren xi]]).
  intros Hcxi Htxi.
  pose proof (typing_ind
                (fun Gamma A Ha => forall Delta xi, closed_ren (size Gamma) (size Delta) xi
                                   -> (forall v, v < size Gamma -> (dget v Gamma).[ren xi] <:::> dget (xi v) Delta)
                                   -> [Gamma |+ A]
                                   -> [Delta |+ A.[ren xi]])
                (fun Gamma a A Hge => forall Delta xi, closed_ren (size Gamma) (size Delta) xi
                                      -> (forall v, v < size Gamma -> (dget v Gamma).[ren xi] <:::> dget (xi v) Delta)
                                      -> [Gamma |+ a :< A]
                                      -> [Delta |+ a.[ren xi] :< A.[ren xi]])) as IP.
  specialize IP with (Gamma := Gamma); simpl in IP. (* make the IP *)
  pop prems IP (clear Hcxi Htxi IP Gamma Delta xi; intros; auto) (clear Prem) firstorder.
  Focus 4. subst; econstructor; eauto; autosubst. (* app *)
  Focus 4. subst; apply T_conv with (A := dget (xi i) Delta); eauto rst. (* var *)
  Focus 4. apply T_conv with (A := A.[ren xi]); eauto rst.           (* conv *)
  (* binders *)
  all: constructor; auto; asimpl.
  all: apply H0; auto; destruct v; simpl; eauto; try autosubst; intros.
  all: rewrite upren_wk; eauto.
Qed.

Lemma ren_eq_vars Delta Gamma xi :
  [Delta |+ ren xi +| Gamma] <-> 
  (closed_ren (size Gamma) (size Delta) xi) /\ (forall v, v < size Gamma -> (dget v Gamma).[ren xi] <:::> dget (xi v) Delta).
Proof. split; intros.
  { assert (forall v, v < size Gamma -> (xi v < size Delta) /\ (dget v Gamma).[ren xi] <:::> dget (xi v) Delta); intros; [|firstorder].
    pose proof (H v H0).
    remember (ren xi v) as rv.
    remember (dget v Gamma).[ren xi] as dg.
    assert (Hdg : dg <:::> (dget v Gamma).[ren xi]) by (subst; reflexivity); clear Heqdg.
    move: v H0 Heqrv Hdg.
    induction H1; intros; subst; try solve by inversion.
    { inverts Heqrv. split; [auto|reflexivity]. }
    { specialize (IHhas_type H v H2).
      assert (A <:::> (dget v Gamma).[ren xi]) by eauto rst.
      intuition; eauto rst. } }
  { apply T_conv with (A := dget (xi x) Delta); [|constructor]; firstorder. }
Qed.

Lemma ty_renaming Gamma Delta xi :
  [Delta |+ ren xi +| Gamma] ->
  (forall A, [Gamma |+ A] -> [Delta |+ A.[ren xi]]) /\ (forall a A, [Gamma |+ a :< A] -> [Delta |+ a.[ren xi] :< A.[ren xi]]).
Proof. rewrite ren_eq_vars. intros.
  assert (closed_ren (size Gamma) (size Delta) xi) by firstorder.
  assert (forall v, v < size Gamma -> (dget v Gamma).[ren xi] <:::> dget (xi v) Delta) by firstorder.
  auto using ty_renaming_aux.
Qed.

Lemma ty_renaming_term Gamma a A Delta xi :
  [Delta |+ ren xi +| Gamma] ->
  [ Gamma |+ a :< A ] ->
  [ Delta |+ a.[ren xi] :< A.[ren xi]].
Proof. firstorder using ty_renaming. Qed.

Lemma ty_renaming_typ Gamma A Delta xi :
  [Delta |+ ren xi +| Gamma] ->
  [ Gamma |+ A ] ->
  [ Delta |+ A.[ren xi]].
Proof. firstorder using ty_renaming. Qed.

Hint Resolve ty_renaming_term ty_renaming_typ.

Hint Rewrite size_cat.

Lemma ren_wk_typed Gamma Delta : [Gamma ++ Delta |+ wk (size Gamma) +| Delta].
Proof. rewrite ren_eq_vars; split; intros.
  { autorewrite with core; auto. }
  { repeat rewrite dget_nth; autorewrite with core; auto. 
    rewrite <- nth_drop; rewrite drop_size_cat; auto.
    autosubst. }
Qed.
Hint Resolve ren_wk_typed.

Lemma wk_typed_term : forall Gamma Delta e T, [Delta |+ e :< T] -> [Gamma ++ Delta |+ e.[wk (size Gamma)] :< T.[wk (size Gamma)]]. eauto. Qed.
Lemma wk_typed_typ : forall Gamma Delta T, [Delta |+ T] -> [Gamma ++ Delta |+ T.[wk (size Gamma)]]. eauto. Qed.
Hint Resolve wk_typed_term wk_typed_typ.

Lemma wk1_typed_term A Gamma e T : [Gamma |+ e :< T] -> [A :: Gamma |+ e.[wk 1] :< T.[wk 1]]. apply wk_typed_term with (Gamma := A :: nil). Qed.
Lemma wk1_typed_typ A Gamma T : [Gamma |+ T] -> [A :: Gamma |+ T.[wk 1]]. apply wk_typed_typ with (Gamma := A :: nil). Qed.
Hint Resolve wk1_typed_term wk1_typed_typ.

Lemma up_typed : forall A Delta Sigma sigma, [Delta |+ sigma +| Sigma] -> [A.[sigma] :: Delta |+ up sigma +| A :: Sigma ].
Proof. intros. destruct x; simpl.
  { constructor; autosubst. }
  { asimpl. replace (dget x Sigma).[sigma >> wk 1] with (dget x Sigma).[sigma].[wk 1] by autosubst. auto. }
Qed.

Hint Resolve up_typed.
Theorem T_subst Gamma Delta sigma : [Delta |+ sigma +| Gamma] ->
                        (forall A, [Gamma |+ A] -> [Delta |+ A.[sigma]]) /\
                        (forall a A, [Gamma |+ a :< A] -> [Delta |+ a.[sigma] :< A.[sigma]]).
Proof. pose proof (typing_ind (fun Gamma A Ha => forall sigma Delta, [Delta |+ sigma +| Gamma] -> [Delta |+ A.[sigma]])
                         (fun Gamma a A Ha => forall sigma Delta, [Delta |+ sigma +| Gamma] -> [Delta |+ a.[sigma] :< A.[sigma]])).
  rename H into IP.
  pop prems IP (econstructor; simpl; subst; eauto; autosubst) (clear Prem).
  firstorder.
Qed.

Lemma T_subst_term sigma Gamma Delta a A : [Delta |+ sigma +| Gamma] -> [Gamma |+ a :< A] -> [Delta |+ a.[sigma] :< A.[sigma]]. 
Proof. firstorder using T_subst. Qed.

Lemma T_subst_typ sigma Gamma Delta A : [Delta |+ sigma +| Gamma] -> [Gamma |+ A] -> [Delta |+ A.[sigma]]. 
Proof. firstorder using T_subst. Qed.

Hint Resolve T_subst_term T_subst_typ.

(* SUBJECT REDUCTION THEOREMS *)
Theorem step_scoped a b : a ::> b -> forall i, closed_at i a -> closed_at i b.
Proof. autounfold; induction 1; simpl; intros; autorewrite with bool in *; firstorder.
  subst; apply cons_id_scoped; auto.
  pose proof (IHpar_step1 i H2); simpl in *; destr bands; auto.
Qed.

Lemma red_pi1 A A' B : A :::> A' -> Pi A B :::> Pi A' B. induction 1; intros; eauto tc. Qed.
Lemma red_pi2 A B B' : B :::> B' -> Pi A B :::> Pi A B'. induction 1; intros; eauto tc. Qed.
Hint Resolve red_pi2 red_pi1.

Lemma red_pi A B A' B' : A :::> A' -> B :::> B' -> Pi A B :::> Pi A' B'. intros; transitivity (Pi A' B); eauto. Qed.
Hint Resolve red_pi.

Lemma red_lam1 A A' B : A :::> A' -> Lam A B :::> Lam A' B. induction 1; intros; eauto tc. Qed.
Lemma red_lam2 A B B' : B :::> B' -> Lam A B :::> Lam A B'. induction 1; intros; eauto tc. Qed.
Hint Resolve red_lam2 red_lam1.

Lemma red_lam A B A' B' : A :::> A' -> B :::> B' -> Lam A B :::> Lam A' B'. intros; transitivity (Lam A' B); eauto. Qed.
Hint Resolve red_lam.

Lemma red_app1 A A' B : A :::> A' -> App A B :::> App A' B. induction 1; intros; eauto tc. Qed.
Lemma red_app2 A B B' : B :::> B' -> App A B :::> App A B'. induction 1; intros; eauto tc. Qed.
Hint Resolve red_app2 red_app1.

Lemma red_app A B A' B' : A :::> A' -> B :::> B' -> App A B :::> App A' B'. intros; transitivity (App A' B); eauto. Qed.
Hint Resolve red_app.

Ltac clear_list idents :=
  match idents with (?x, ?xs) => move: x; clear_list xs | ?x => move: x || idtac end.
Ltac refeqs := repeat match goal with [H: _ = _ -> _ |- _] => specialize (H erefl) end.

Ltac step_lemma_left form idents :=
  let f := fresh "f" in let eq := fresh "Heqf" in let Hf := fresh "Hf" in
  remember form as f eqn:eq; move=> Hf;
  move: eq; clear_list idents; induction Hf; intros; subst;
  [match goal with [H : form ::> _ |- _] => inverts H end; repeat eexists; eauto
  |do 2 (try_hyps; refeqs; destr_logic); subst; repeat eexists; eauto tc].

Ltac step_lemma form idents := split; [step_lemma_left form idents|intros;destr_logic;subst;eauto tc].

Lemma step_from_pi e A B : Pi A B :::> e <-> exists A' B', A :::> A' /\ B :::> B' /\ e = Pi A' B'. step_lemma (Pi A B) (A,B). Qed.
Lemma step_from_lam e A b : Lam A b :::> e <-> exists A' b', A :::> A' /\ b :::> b' /\ e = Lam A' b'. step_lemma (Lam A b) (A, b). Qed.
Lemma step_from_var e v : Var v :::> e <-> e = Var v. step_lemma (Var v) v. Qed.
Lemma step_from_typ e : Typ :::> e <-> e = Typ. step_lemma Typ e. Qed.

Hint Rewrite step_from_pi step_from_lam step_from_var step_from_var step_from_typ : inversions.

Ltac conv_uniformity_lemmas form :=
  intros; split; intros; autorewrite with unconv in *; destr_logic;
  [autorewrite with inversions in *; destr_logic; subst;
   match goal with [H: _=_ |- _] => inverts H end;split
  |eexists (form _ _)]; eauto.

Lemma pi_conv_pi : forall A B A' B', Pi A B <:::> Pi A' B' <-> (A <:::> A') /\ (B <:::> B'). conv_uniformity_lemmas Pi. Qed.
Hint Rewrite pi_conv_pi : invtyp.

Lemma lam_conv_lam : forall A B A' B', Lam A B <:::> Lam A' B' <-> (A <:::> A') /\ (B <:::> B'). conv_uniformity_lemmas Lam. Qed.
Hint Rewrite lam_conv_lam : invtyp.

Lemma red_subst : forall e a b, a :::> b -> e.[a/] :::> e.[b/].
Proof. induction 1; eauto tc. Qed.
Hint Resolve red_subst.

Lemma step_from_app e f x : f :$: x :::> e -> (exists f' x', f :::> f' /\ x :::> x' /\ e = f' :$: x') \/
                                             (exists A b, f :::> A :#> b /\ b.[x/] :::> e).
Proof. remember (f :$: x) as fx.
  move=> Hfx; move: f x Heqfx; induction Hfx; intros; subst.
  { inverts H; [left|left|right]; repeat eexists; eauto. }
  { specialize (IHHfx1 f x0 erefl).
    destr_logic; intuition; subst.
    { specialize (IHHfx2 x x1 erefl); destr_logic; subst;
      [left|right]; repeat eexists; eauto tc. }
    { right; repeat eexists; eauto tc. } }
Qed.

(* Typing inversions *)
Lemma Pi_ht_inv Gamma A B T : [Gamma |+ A :>> B :< T] <-> ([Gamma |+ A :< Typ] /\ [A :: Gamma |+ B :< Typ] /\ Typ <:::> T).
Proof. split.
  { move=> Hab; remember (A :>> B) as pab; move: A B Heqpab; induction Hab; intros; try solve by inversion.
    { inversion Heqpab; subst; eauto. }
    { subst. specialize (IHHab _ _ erefl). intuition; eauto rst. } }
  { firstorder; eapply T_conv; eauto rst. }
Qed.
  
Hint Rewrite Pi_ht_inv : invtyp.
Lemma Pi_it_inv Gamma A B : [Gamma |+ A :>> B] <-> ([Gamma |+ A] /\ [A :: Gamma |+ B]).
Proof. split; inversion 1; subst; eauto. autorewrite with invtyp in *; intuition. Qed.

Hint Rewrite Pi_it_inv : invtyp.

Lemma Lam_ht_inv Gamma A b T : [Gamma |+ A :#> b :< T] <-> (exists B, [Gamma |+ A] /\ [A :: Gamma |+ b :< B] /\ A :>> B <:::> T).
Proof. split.
  { move=> Hab; remember (A :#> b) as pab; move: A b Heqpab; induction Hab; intros; try solve by inversion.
    { inversion Heqpab; subst; eauto. }
    { subst. specialize (IHHab _ _ erefl).
      firstorder; eexists; intuition; eauto rst. } }
  { firstorder; eapply T_conv; eauto rst. }
Qed.

Hint Rewrite Lam_ht_inv : invtyp.

Lemma Lam_not_it Gamma f x : ~ [Gamma |+ f :#> x].
Proof. inversion 1; subst. 
  autorewrite with invtyp in *; destr_logic.
  autorewrite with unconv in *; destr_logic.
  autorewrite with inversions in *; destr_logic; subst; solve by inversion.
Qed.
  
Lemma App_ht_inv Gamma f x T : 
  [Gamma |+ f :$: x :< T] <-> (exists A B, [Gamma |+ f :< A :>> B] /\ [Gamma |+ x :< A] /\ B.[x/] <:::> T).
Proof. split.
  { move=> Hfx; remember (f :$: x) as afx; move: f x Heqafx; induction Hfx; intros; try solve by inversion.
    { inversion Heqafx; subst; eauto. }
    { subst. specialize (IHHfx _ _ erefl).
      firstorder; eexists; intuition; eauto rst. } }
  { firstorder; eapply T_conv; eauto rst. }
Qed.

Hint Rewrite App_ht_inv : invtyp.

Lemma App_it_inv Gamma f x : [Gamma |+ f :$: x] <-> (exists A B, [Gamma |+ f :< A :>> B] /\ [Gamma |+ x :< A] /\ B.[x/] <:::> Typ).
Proof. split.
  { inversion 1; subst. autorewrite with invtyp in *; firstorder. }
  { firstorder; eauto. }
Qed.

Hint Rewrite App_it_inv : invtyp.
Print exp.
Lemma Var_ht_inv Gamma i T :
  [Gamma |+ Var i :< T] <-> (i < size Gamma /\ dget i Gamma <:::> T).
Proof. split.
  { move=> Hvi; remember (Var i) as vi; move: i Heqvi; induction Hvi; intros; try solve by inversion.
    { split; inversion Heqvi; subst; auto. }
    { split; [firstorder|]; subst. destruct (IHHvi i erefl); eauto rst. } }
  { intuition; eapply T_conv; eauto rst. }
Qed.

Hint Rewrite Var_ht_inv : invtyp.

Lemma Var_it_inv Gamma i : [Gamma |+ Var i] <-> (i < size Gamma /\ dget i Gamma <:::> Typ).
Proof. split; inversion 1; subst; constructor; autorewrite with invtyp in *; intuition. Qed.

Hint Rewrite Var_it_inv : invtyp.

(* TODO: *)
(* Subject reduction *)
(* Interpreter *)
(* Normalizer? *)
(* Add more constructs *)

(* Things we need to prove subject reduction: *)
(* 1) pi : A <-> A = Typ, lam : A <-> A <:::> pi, etc *)
(* Check! *)
(* 2) Gamma <:::> Delta -> Gamma |+ id +| Delta *)
(* uh, can we just define it that way? I feel like that's easier *)
(* 3) Gamma |+ id +| Delta <-> exists C1 C2, Gamma = C1 ++ C2 /\  *)
(* Things we need for an interpreter: *)
(* 1) replace a bunch of theorems with mutual ones including typing *)
(* 2) "interprets to" relation *) 
(* 3) proof that "interprets to" is functional *)

(* Constructs that should be added, in order: *)
(* 1) Sigma *)
(* 2) W + assorted datatypes *)
(* 3) Equality *)

Notation "Gamma :+ Delta" := ([Gamma |+ ids +| Delta]) (at level 50).
Notation conv_con := (fun Gamma Delta => Gamma :+ Delta).
Lemma conv_con_cong_typ Gamma Delta (A : exp) : Gamma :+ Delta -> [Delta |+ A] -> [Gamma |+ A].
Proof. intros; replace A with A.[ids] by autosubst; eauto. Qed.
Lemma conv_con_cong_term Gamma Delta (a A : exp) : Gamma :+ Delta -> [Delta |+ a :< A] -> [Gamma |+ a :< A].
Proof. intros; replace A with A.[ids]; replace a with a.[ids]; eauto; autosubst. Qed.
Hint Resolve conv_con_cong_term conv_con_cong_typ.

Instance conv_con_refl : Reflexive conv_con. constructor; auto; asimpl; auto. Qed.
Instance conv_con_trans : Transitive conv_con. 
Proof. move=> Gamma Delta Sigma H1 H2 x Hx.
  specialize (H2 x Hx).
  autorewrite with invtyp in *; destr_logic; try_hyps; clear_funs.
  autorewrite with invtyp in *; destr_logic; split; auto.
  asimpl in *; eauto rst.
Qed.

Ltac conv_back e := apply T_conv with (A := e).

Lemma conv_cons : forall A A' Gamma Delta, A <:::> A' -> Gamma :+ Delta -> (A' :: Gamma) :+ (A :: Delta).
Proof. simpl; destruct x; simpl; intros; asimpl; auto. 
  conv_back (A'.[wk 1]); eauto rst.
  change (ids x.+1) with (ids x).[wk 1].
  replace (dget x Delta).[wk 1] with (dget x Delta).[ids].[wk 1] by autosubst.
  apply wk1_typed_term; auto.
Qed.

Lemma conv_cons_const : forall A A' Gamma, A <:::> A' -> (A' :: Gamma) :+ (A :: Gamma). intros; apply conv_cons with (Delta := Gamma); auto. Qed.
Hint Resolve conv_cons conv_cons_const.
Hint Resolve Lam_not_it.

Theorem step_typed a b : a ::> b -> forall Gamma, (forall T, [Gamma |+ a :< T] -> [Gamma |+ b :< T]) /\ ([Gamma |+ a] -> [Gamma |+ b]).
Proof with eauto using conv_con_cong_typ, conv_con_cong_term. 
  induction 1; intros; auto; autorewrite with invtyp in *; destr_logic.
  { assert ((A' :: Gamma) :+ (A :: Gamma)) by auto.
    specialize (IHpar_step1 Gamma); specialize (IHpar_step2 (A :: Gamma)).
    split; intros.
    { autorewrite with invtyp in *; destr_logic; repeat split; [firstorder| |firstorder]... }
    { destr_logic; split; [firstorder|]... } }
  { assert ((A' :: Gamma) :+ (A :: Gamma)) by auto.
    split; intros; autorewrite with invtyp in *; destr_logic.
    { eexists; repeat split; auto.
      firstorder.
      eapply conv_con_cong_term; try eassumption; eapply IHpar_step2; eauto.
      transitivity (A :>> x); eauto rst. }
    { contradict H2; auto. } }
  { specialize (IHpar_step1 Gamma); specialize (IHpar_step2 Gamma).
    split; intros.
    { autorewrite with invtyp in *; destr_logic.
      repeat eexists; eauto.
      transitivity (x0.[a/]); eauto rst. }
    { destr_logic; repeat eexists; eauto.
      transitivity (x0.[a/]); eauto rst. } }
  { specialize (IHpar_step1 Gamma); specialize (IHpar_step2 Gamma).
    split; intros; subst.
    { autorewrite with invtyp in *; destr_logic.
      try_hyps; clear_funs.
      do 2 (autorewrite with invtyp in *; destr_logic).
      conv_back (x1.[a'/]); [transitivity (x0.[a/]); [transitivity (x0.[a'/])|]; eauto rst|].
      apply T_subst with (Gamma := A :: Gamma); [|auto].
      simpl; destruct x2; simpl; intros; asimpl; [conv_back x|]; eauto rst. }
    { constructor; destr_logic.
      try_hyps; clear_funs. do 2 (autorewrite with invtyp in *; destr_logic).
      conv_back (x1.[a'/]); [transitivity (x0.[a/]); [transitivity (x0.[a'/])|]; eauto rst|].
      apply T_subst with (Gamma := A :: Gamma); [|auto].
      simpl; destruct x2; simpl; intros; asimpl; [conv_back x|]; eauto rst. } }
Qed.


(* INTERPRETATION *)

(* Inductive interprets_to__Type (gamma : env) : exp -> Type -> Prop := *)
(* | I_pi : forall a b A B, interprets_to__Type gamma a A -> interprets_to__Type (extend gamma A) b B -> interprets_to__Type (A ::> B) *)
(* | I_typ : interprets_to__Type gamma Typ Type *)
(* | I_tmty : interprets_to__Tm gamma e Type T -> interprets_to__Type gamma e T *)
(* with interprets_to__Tm (gamma : env) : exp -> forall (A : Type), A -> Prop := *)
(* | I_tytm : interprets_to__Type gamma e T -> interprets_to__Tm gamma e Type T *)
(* | I_lam : interprets_to__Type gamma a A -> interprets_to__Tm (extend gamma A) b B b__o : interprets_to__Tm (Lam a b) (forall a, B a) (fun a => b__o a) *)