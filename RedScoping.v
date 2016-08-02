Require Import Prelude.
Require Import Expr Scoping Reduction.
Notation ren_scop xi i j := (forall v, v < i -> xi v < j).

Lemma All_sub D : forall sigma C e, (All D C e).[sigma] = All D C.[up sigma] e.[sigma].
Proof. induction D; intros; simpl; rewrite asms; autosubst. Qed.

Hint Resolve All_sub.
Hint Rewrite All_sub.
Hint Rewrite All_sub : autosubst.

Lemma closed_step e e' n : e ::> e' -> closed_at n e -> closed_at n e'.
Proof. move=> He'; move: n; induction He'; simpl in *; intros; subst;
  autounfold in *; destr bands;
  try solve[repeat (apply andb_true_intro; split); auto|apply cons_id_scoped || apply cons2_id_scoped; firstorder].  
  - apply closed_lift with (i := 0); try eapply Reduction.const_vals_closed; eassumption || auto.
  - apply cons2_id_scoped; auto.
    apply rall_scoped; simpl; auto; autorewrite with core.
    apply sub_vars_scoped with (i := (2 + n)); auto.
    intros; change (ren (iterate upren 2 (+1)) v) with (Bind (upnren 2 (+1) v)); simpl; auto.
    pose proof (ren_upnren 2 n n.+1 (+1)); firstorder.
Qed.

Hint Resolve closed_step.
