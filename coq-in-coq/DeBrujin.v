Require Import Unscoped.
Require Import Omega.

Lemma wk_beneath_wk : forall e d1 d2 n1 n2, d1 <= d2 -> wk_deep n1 d1 (wk_deep n2 d2 e) = wk_deep n2 (n1 + d2) (wk_deep n1 d1 e).
  induction e; unfold_ops; simpl; fold_ops; intros; try reflexivity;
  try rewrite IHe1; try rewrite IHe2; try rewrite IHe3; try rewrite IHe4; try (repeat f_equal; omega).
  - destr_choices; f_equal; omega.
Qed.

Lemma wk_above_wk : forall e d1 d2 n1 n2, d1 >= n2 + d2 -> wk_deep n1 d1 (wk_deep n2 d2 e) = wk_deep n2 d2 (wk_deep n1 (d1 - n2) e).
  induction e; unfold_ops; simpl; fold_ops; intros; try reflexivity;
  try rewrite IHe1; try rewrite IHe2; try rewrite IHe3; try rewrite IHe4; try (repeat f_equal; omega).
  - destr_choices; f_equal; omega.
Qed.

Lemma wk_deep_wk : forall e d1 d2 n1 n2, d2 <= d1 <= n2 + d2 -> wk_deep n1 d1 (wk_deep n2 d2 e) = wk_deep (n1 + n2) d2 e.
  induction e; unfold_ops; simpl; fold_ops; intros; try reflexivity;
  try rewrite IHe1; try rewrite IHe2; try rewrite IHe3; try rewrite IHe4; try (repeat f_equal; omega).
  - destr_choices; f_equal; omega.
Qed.

Lemma wk_0_eq : forall e d, wk_deep 0 d e = e.
  unfold_ops; induction e; simpl; intros; repeat f_equal; eauto.
  - destruct (le_dec d ix); f_equal; omega.
Qed.

Hint Rewrite wk_0_eq wk_deep_wk.

Lemma subst_lift_same : forall e v d n, wk_deep (S n) d e |> v // d = wk_deep n d e.
  induction e; unfold wk_deep in *; unfold subst_deep in *; simpl; intros; f_equal; auto.
  - unfold wk_var; destr_goal_if; unfold subst_var; destr_choices; f_equal; omega.
Qed.  

Lemma subst_lift_gap : forall e v d1 d2 n, d2 <= d1 <= n + d2 -> wk_deep (S n) d2 e |> v // d1 = wk_deep n d2 e.
  unfold wk_deep, subst_deep; induction e; simpl; intros; f_equal; auto; try omega.
  - unfold_ops; destr_choices; f_equal; omega.
  (* pi and lam didn't work for some reason *)
  - apply IHe2; omega.
  - apply IHe2; omega.
Qed.

Lemma subst_var_lift : forall i v d1 d2 n, d1 >= d2 -> 
  wk_deep n d2 (subst_var v d1 i) = subst_deep v (n + d1) (wk_var n d2 i).
  unfold subst_deep,wk_deep,subst_var,wk_var; intros;
  destr_choices; f_equal; try apply wk_deep_wk (* pi and lambda need some special handling *); omega. Qed.

Hint Resolve wk_deep_wk subst_var_lift.

Lemma lift_below_subst : forall e v d1 d2 n, d1 <= d2 -> wk_deep n d1 (e |> v // d2) = (wk_deep n d1 e) |> v // (n + d2).
  unfold subst_deep,wk_deep; induction e; intros; simpl; fold_ops; auto; try rewrite plus_n_Sm;
  f_equal; try apply IHe1; try apply IHe2; try apply IHe3; try apply IHe4; omega.
Qed.

Lemma lift_above_subst : forall e v d1 d2 n, d1 > d2 -> 
  wk_deep n d1 (e |> v // d2) = wk_deep n (S d1) e |> wk_deep n (d1 - d2) v // d2.
  unfold_ops; induction e; intros; simpl; try (f_equal; auto; omega); fold_ops.
  - unfold_ops; destr_choices; f_equal; fold_ops; try apply wk_above_wk; omega.
  - f_equal; [apply IHe1|apply IHe2]; omega.
  - f_equal; [apply IHe1|apply IHe2]; omega.
Qed.

Lemma lift_above_subst_n : forall e v d1 d2 n, d1 >= n + d2 -> 
  wk_deep n d1 (e |> v // d2) = wk_deep n (S d1) e |> wk_deep n (d1 - d2) v // d2.
  unfold_ops; induction e; intros; simpl; try (f_equal; auto; omega); fold_ops.
  - unfold_ops; destr_choices; f_equal; fold_ops; try apply wk_above_wk; omega.
  - f_equal; [apply IHe1|apply IHe2]; omega.
  - f_equal; [apply IHe1|apply IHe2]; omega.
Qed.

Lemma lift_subst_same_depth : forall e v n d, wk_deep n d (e |> v // d) = wk_deep n (S d) e |> wk_deep n 0 v // d.
  induction e; unfold wk_deep,subst_deep; simpl; fold_ops; intros; fold_ops;
  try rewrite IHe1; try rewrite IHe2; try rewrite IHe3; try rewrite IHe4; try (f_equal;auto;fail).
  - unfold_ops; destr_choices; fold_ops; repeat rewrite wk_deep_wk; f_equal; omega.
Qed.

Lemma subst_above_subst : forall e3 e1 e2 d1 d2, d1 <= d2 -> 
  e3 |> e1 // d1 |> e2 // d2 = (e3 |> e2 // S d2) |> (e1 |> e2 // (d2 - d1)) // d1.
  
  induction e3; unfold subst_deep; simpl; intros; fold_ops; try (f_equal; auto; omega).
  - unfold_ops; destr_choices; fold_ops; f_equal; try omega.
    + rewrite lift_below_subst; f_equal; omega.
    + rewrite subst_lift_gap; f_equal; omega.
  - f_equal; [apply IHe3_1|replace (d2 - d1) with (S d2 - S d1) by omega; apply IHe3_2]; omega.
  - f_equal; [apply IHe3_1|replace (d2 - d1) with (S d2 - S d1) by omega; apply IHe3_2]; omega.
Qed.

Lemma subst_above_push : forall e3 e1 e2 d,        
  e3 |> e2 // 0 |> e1 // d = e3 |> e1 // S d |> e2 |> e1 // d // 0.
  intros; rewrite subst_above_subst; repeat f_equal; omega. Qed.

 