Require Import Unscoped Scoping Typing Evaluation.

Lemma nf_dec : forall t, {nf t} + {~ nf t}.
  induction t; destr_hyps; (left;constructor;assumption) || (right; inversion 1; subst; contradiction).
Defined.

Print exp.
Definition is_var (e : exp) : Prop := match e with & _ => True | _ => False end.

Hint Unfold is_var.

Lemma eval_typ : forall n T, typ n ===> T <-> T = typ n.
  intros n T; remember (typ n); split; induction 1; subst; auto.
  inversion H.
Qed.

Lemma eval_bool : forall T, bool ===> T <-> T = bool.
  remember bool; split; induction 1; subst; auto.
  inversion H.
Qed.

Lemma eval_top : forall T, top ===> T <-> T = top.
  remember top; split; induction 1; subst; auto.
  inversion H.
Qed.  

Lemma eval_bot : forall T, bot ===> T <-> T = bot.
  remember bot; split; induction 1; subst; auto.
  inversion H.
Qed.  

Hint Rewrite eval_typ eval_bool eval_top eval_bot.

Lemma progress_wt Gamma t T : Gamma ⊢ t ∈ T -> nf t \/ exists t', t ==> t'.
Admitted.

Print nf.

Lemma no_vars : forall n T, ~ ([] ⊢ & n ∈ T).
Admitted.

Tactic Notation "solve" "by" "inversion" := 
  match goal with [H: _|-_] => solve [inversion H] end.


Tactic Notation "confls" hyp(H) := 
  apply ty_var_confl in H || apply ty_typ_confl in H
                          || apply ty_pi_confl in H
                          || apply ty_sg_confl in H
                          || apply ty_wt_confl in H
                          || apply ty_bool_confl in H
                          || apply ty_top_confl in H
                          || apply ty_bot_confl in H
                          || apply ty_true_confl in H
                          || apply ty_false_confl in H
                          || apply ty_unit_confl in H
                          || apply ty_lam_confl in H
                          || apply ty_sup_confl in H
                          || apply ty_smk_confl in H
                          || apply ty_app_confl in H
                          || apply ty_srec_confl in H
                          || apply ty_urec_confl in H
                          || apply ty_brec_confl in H
                          || apply ty_urec_confl in H
                          || apply ty_exf_confl in H.
    
Lemma exf_bot Gamma c f T : Gamma ⊢ exf c f ∈ T -> Gamma ⊢ f ∈ bot.
  remember (exf c f). 
  intro Ht; generalize dependent f; generalize c. clear c.
  induction Ht; intros; subst; try (solve by inversion).
  - inversion Heqe; subst; assumption.
  - eauto.
  - eauto.
Qed.

Lemma nopf : forall t, nf t -> ~ ([] ⊢ t ∈ bot).
  induction 1;
  try (let H := fresh in intro H; confls H; destr_logic; rewrite eval_bot in *; solve by inversion). 
  - intro H1. apply exf_bot in H1. auto.
Qed.

Require Import List.

Lemma lookup_in {A : Type} (Gamma : list A) : forall i p, In (lookup_lt Gamma <<i,p>>) Gamma.
  induction Gamma; destruct i; intros; simpl in *; auto; omega.
Qed.

Lemma wk_inj : forall t n m t', wk_deep n m t = wk_deep n m t' <-> t = t'.
  split; [generalize dependent t'; generalize n m|intros; congruence].
  induction t; unfold wk_deep; destruct t'; simpl;
  try match goal with [|-context[wk_var _ _]] => unfold wk_var; simpl end;
  destr_choices; inversion 1; auto; fold_ops; f_equal;
  eapply IHt1 || eapply IHt2 || eapply IHt3 || eapply IHt4 || omega; eassumption.
Qed.  
