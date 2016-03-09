Set Implicit Arguments.
Require Import Unscoped.
Require Import DeBrujin.
Require Import Omega.

Reserved Notation "a ~> b" (at level 50).

Inductive par_red : exp -> exp -> Prop :=
| par_ref : forall e, e ~> e

| par_pi : forall e1 e1' e2 e2', e1 ~> e1' -> e2 ~> e2' -> pi e1 e2 ~> pi e1' e2'
| par_lam : forall e1 e1' e2 e2', e1 ~> e1' -> e2 ~> e2' -> lam e1 e2 ~> lam e1' e2'
| par_app : forall e1 e1' e2 e2', e1 ~> e1' -> e2 ~> e2' -> (e1 @ e2) ~> (e1' @ e2')
| par_app_lam : forall e1 e2 e3 e4 e5, e1 ~> lam e2 e3 -> e4 ~> e5 -> e1 @ e4 ~> e3 |> e5 // 0

| par_sg : forall e1 e1' e2 e2', e1 ~> e1' -> e2 ~> e2' -> sigma e1 e2 ~> sigma e1' e2'
| par_smk : forall e1 e1' e2 e2' e3 e3', e1 ~> e1' -> e2 ~> e2' -> e3 ~> e3' -> smk e1 e2 e3 ~> smk e1' e2' e3'
| par_srec : forall e1 e1' e2 e2' e3 e3', e1 ~> e1' -> e2 ~> e2' -> e3 ~> e3' -> srec e1 e2 e3 ~> srec e1' e2' e3'
| par_srec_smk : forall e1 e2 e2' e3 e4 e5 e6, e2 ~> e2' -> e3 ~> smk e4 e5 e6
                                          -> srec e1 e2 e3 ~> e2' @ e5 @ e6

| par_wt : forall e1 e1' e2 e2', e1 ~> e1' -> e2 ~> e2' -> wt e1 e2 ~> wt e1' e2'
| par_sup : forall e1 e1' e2 e2' e3 e3', e1 ~> e1' -> e2 ~> e2' -> e3 ~> e3' -> sup e1 e2 e3 ~> sup e1' e2' e3'
| par_wrec : forall e1 e1' e2 e2' e3 e3', e1 ~> e1' -> e2 ~> e2' -> e3 ~> e3' -> wrec e1 e2 e3 ~> wrec e1' e2' e3'
| par_wrec_sup : forall e1 e1' e2 e2' e3 e4 e5 e6, e1 ~> e1' -> e2 ~> e2' -> e3 ~> sup e4 e5 e6
                 -> wrec e1 e2 e3 ~> e2' @ e5 @ (lam (e4 @ e5) (wrec (wk_deep 1 0 e1') (wk_deep 1 0 e2') (wk_deep 1 0 e6 @ &0)))

| par_brec : forall e1 e1' e2 e2' e3 e3' e4 e4', e1 ~> e1' -> e2 ~> e2' -> e3 ~> e3' -> e4 ~> e4' -> brec e1 e2 e3 e4 ~> brec e1' e2' e3' e4'
| par_brec_true : forall e1 e1' e2 e2' e3 e3' e4, e1 ~> e1' -> e2 ~> e2' -> e3 ~> e3' -> e4 ~> true
                                             -> brec e1 e2 e3 e4 ~> e2'
| par_brec_false : forall e1 e1' e2 e2' e3 e3' e4, e1 ~> e1' -> e2 ~> e2' -> e3 ~> e3' -> e4 ~> false
                                              -> brec e1 e2 e3 e4 ~> e3'

| par_urec : forall e1 e1' e2 e2' e3 e3', e1 ~> e1' -> e2 ~> e2' -> e3 ~> e3' -> urec e1 e2 e3 ~> urec e1' e2' e3'
| par_urec_unit : forall e1 e1' e2 e2' e3, e1 ~> e1' -> e2 ~> e2' -> e3 ~> unit -> urec e1 e2 e3 ~> e2'

| par_exf : forall e1 e1' e2 e2', e1 ~> e1' -> e2 ~> e2' -> exf e1 e2 ~> exf e1' e2'
where "a ~> b" := (par_red a b).

Reserved Notation "a ==> b" (at level 50).
Inductive step : exp -> exp -> Prop :=
| step_pi1 : forall e1 e1' e2, e1 ==> e1' -> pi e1 e2 ==> pi e1' e2
| step_pi2 : forall e1 e2 e2', e2 ==> e2' -> pi e1 e2 ==> pi e1 e2'
| step_lam1 : forall e1 e1' e2, e1 ==> e1' -> lam e1 e2 ==> lam e1' e2
| step_lam2 : forall e1 e2 e2', e2 ==> e2' -> lam e1 e2 ==> lam e1 e2'
| step_app1 : forall e1 e1' e2, e1 ==> e1' -> app e1 e2 ==> app e1' e2
| step_app2 : forall e1 e2 e2', e2 ==> e2' -> app e1 e2 ==> app e1 e2'
| step_app_lam : forall e1 e2 e3, (lam e1 e2) @ e3 ==> e2 |> e3 // 0

| step_sg1 : forall e1 e1' e2, e1 ==> e1' -> sigma e1 e2 ==> sigma e1' e2
| step_sg2 : forall e1 e2 e2', e2 ==> e2' -> sigma e1 e2 ==> sigma e1 e2'
| step_smk1 : forall e1 e1' e2 e3, e1 ==> e1' -> smk e1 e2 e3 ==> smk e1' e2 e3
| step_smk2 : forall e1 e2 e2' e3, e2 ==> e2' -> smk e1 e2 e3 ==> smk e1 e2' e3
| step_smk3 : forall e1 e2 e3 e3', e3 ==> e3' -> smk e1 e2 e3 ==> smk e1 e2 e3'
| step_srec1 : forall e1 e1' e2 e3, e1 ==> e1' -> srec e1 e2 e3 ==> srec e1' e2 e3
| step_srec2 : forall e1 e2 e2' e3, e2 ==> e2' -> srec e1 e2 e3 ==> srec e1 e2' e3
| step_srec3 : forall e1 e2 e3 e3', e3 ==> e3' -> srec e1 e2 e3 ==> srec e1 e2 e3'
| step_srec_smk : forall e1 e2 e3 e4 e5, srec e1 e2 (smk e3 e4 e5) ==> e2 @ e4 @ e5

| step_wt1 : forall e1 e1' e2, e1 ==> e1' -> wt e1 e2 ==> wt e1' e2
| step_wt2 : forall e1 e2 e2', e2 ==> e2' -> wt e1 e2 ==> wt e1 e2'
| step_sup1 : forall e1 e1' e2 e3, e1 ==> e1' -> sup e1 e2 e3 ==> sup e1' e2 e3
| step_sup2 : forall e1 e2 e2' e3, e2 ==> e2' -> sup e1 e2 e3 ==> sup e1 e2' e3
| step_sup3 : forall e1 e2 e3 e3', e3 ==> e3' -> sup e1 e2 e3 ==> sup e1 e2 e3'
| step_wrec1 : forall e1 e1' e2 e3, e1 ==> e1' -> wrec e1 e2 e3 ==> wrec e1' e2 e3
| step_wrec2 : forall e1 e2 e2' e3, e2 ==> e2' -> wrec e1 e2 e3 ==> wrec e1 e2' e3
| step_wrec3 : forall e1 e2 e3 e3', e3 ==> e3' -> wrec e1 e2 e3 ==> wrec e1 e2 e3'
| step_wrec_sup : forall e1 e2 e3 e4 e5, wrec e1 e2 (sup e3 e4 e5) 
                                ==> e2 @ e4 @ (lam (e3 @ e4) (wrec (wk_deep 1 0 e1) (wk_deep 1 0 e2) (wk_deep 1 0 e5 @ &0)))

| step_brec1 : forall e1 e1' e2 e3 e4, e1 ==> e1' -> brec e1 e2 e3 e4 ==> brec e1' e2 e3 e4
| step_brec2 : forall e1 e2 e2' e3 e4, e2 ==> e2' -> brec e1 e2 e3 e4 ==> brec e1 e2' e3 e4
| step_brec3 : forall e1 e2 e3 e3' e4, e3 ==> e3' -> brec e1 e2 e3 e4 ==> brec e1 e2 e3' e4
| step_brec4 : forall e1 e2 e3 e4 e4', e4 ==> e4' -> brec e1 e2 e3 e4 ==> brec e1 e2 e3 e4'
| step_brec_true : forall e1 e2 e3, brec e1 e2 e3 true ==> e2
| step_brec_false : forall e1 e2 e3, brec e1 e2 e3 false ==> e3

| step_urec1 : forall e1 e1' e2 e3, e1 ==> e1' -> urec e1 e2 e3 ==> urec e1' e2 e3
| step_urec2 : forall e1 e2 e2' e3, e2 ==> e2' -> urec e1 e2 e3 ==> urec e1 e2' e3
| step_urec3 : forall e1 e2 e3 e3', e3 ==> e3' -> urec e1 e2 e3 ==> urec e1 e2 e3'
| step_urec_unit : forall e1 e2, urec e1 e2 unit ==> e2

| step_exf1 : forall e1 e1' e2, e1 ==> e1' -> exf e1 e2 ==> exf e1' e2
| step_exf2 : forall e1 e2 e2', e2 ==> e2' -> exf e1 e2 ==> exf e1 e2'
where "a ==> b" := (step a b).

Hint Constructors step par_red.

Lemma step_par : forall e1 e2, e1 ==> e2 -> e1 ~> e2.
  induction 1; eauto. Qed.

Hint Resolve step_par.

Ltac destr_sumors := match goal with [H: _ + {_} |- _] => destruct H end.
Ltac destr_exists := match goal with [H: exists _,_ |- _] => destruct H | [H: {_ | _} |- _] => destruct H end.

Require Import Relation_Definitions.
Require Import Relation_Operators.

(* typing will depend on evaluation, so preservation will have to wait until we've proved Church-Rosser *)

Lemma wk_par_cong : forall e1 e2 n d, e1 ~> e2 -> wk_deep n d e1 ~> wk_deep n d e2.
  intros e1 e2 n d He; generalize dependent d; generalize dependent n;
  induction He; unfold wk_deep; simpl; intros; try (econstructor;eauto;fail); fold_ops.
  (* lam_app and wrec, troublesome as always *)
  - destruct d; [rewrite lift_subst_same_depth|rewrite lift_above_subst; [|omega]]; eauto.
  - repeat rewrite wk_above_wk with (n1 := n) (d1 := S d); [|omega|omega|omega].
    replace (wk_var n (S d) 0) with (&0) by auto; simpl; replace (d - 0) with d by omega.
    eauto.
Qed.  

Hint Resolve wk_par_cong.

Lemma par_eq : forall e1 e2 e3, e1 ~> e2 -> e2 = e3 -> e1 ~> e3.
  induction 2; eauto. Qed.

Lemma subst1_par_cong : forall e1 e2, e1 ~> e2 -> forall e3 n, e1 |> e3 // n ~> e2 |> e3 // n.
  induction 1; unfold subst_deep; simpl; intros; fold_ops; eauto. 
  - replace (subst_deep e0 n (subst_deep e5 0 e3)) with (subst_deep (subst_deep e0 n e5) 0 (subst_deep e0 (S n) e3));
    [|rewrite subst_above_push]; eauto.
  - replace (S n) with (1 + n); repeat rewrite <- lift_below_subst; eauto; omega.
Qed.

Lemma subst2_par_cong : forall e3 e1 e2 n, e1 ~> e2 -> e3 |> e1 // n ~> e3 |> e2 // n.
  unfold subst_deep; induction e3; simpl; intros; try (econstructor;eauto;omega).
  - unfold_ops; destr_choices; eauto.
Qed.

Hint Resolve subst1_par_cong subst2_par_cong.

Lemma subst12_par_cong : forall e1 e2, e1 ~> e2 -> forall e3 e4 n, e3 ~> e4 -> e1 |> e3 // n ~> e2 |> e4 // n.
  induction 1; unfold subst_deep; simpl; intros; fold_ops; try (unfold_ops; simpl in *; try econstructor; eauto; fail).
  - eapply subst2_par_cong; eauto.
  - rewrite subst_above_push; eauto.
  - replace (S n) with (1 + n); repeat rewrite <- lift_below_subst; eauto; omega.
Qed.

Hint Resolve subst12_par_cong.

Ltac invert_atom_steps := 
  repeat match goal with
           | [H: ?e1 ~> ?e2 |- _] => atomic e2; (tryif atomic e1 then fail else (inversion H; subst; clear H))
           | [H: ?e1 ==> ?e2 |- _] => atomic e2; (tryif atomic e1 then fail else (inversion H; subst; clear H))
         end.

Lemma par_diamond : forall e1 e2 e3, e1 ~> e2 -> e1 ~> e3 -> exists e4, e2 ~> e4 /\ e3 ~> e4.
Proof with eauto.
  intros e1 e2 e3 He2 He3; generalize dependent e3; induction He2; intros;
  try (inversion He3; subst; try_hyps; clear_funs; destr_logic; eauto; fail).
  - inversion He3; subst; try_hyps; clear_funs; destr_logic; invert_atom_steps; eauto.
  - inversion He3; subst; try (try_hyps; clear_funs; destr_logic; invert_atom_steps; eauto; fail).
    + specialize (IHHe2_1 _ H1); specialize (IHHe2_2 _ H3).
      destruct IHHe2_1 as [e1' He1]; destruct IHHe2_2 as [e2' He2]; destr_logic.
      inversion H2; subst; inversion H4; subst; eauto.
  - inversion He3; subst; try (try_hyps; clear_funs; destr_logic; invert_atom_steps; eauto; fail).
    + specialize (IHHe2_2 _ H3); specialize (IHHe2_3 _ H4); destr_logic; invert_atom_steps; eauto.
      * exists (x0 @ e8 @ e9); eauto.
      * exists (x0 @ e2'1 @ e3'0); eauto.
  - inversion He3; subst; try (try_hyps; clear_funs; destr_logic; invert_atom_steps; eauto; fail).
    + specialize (IHHe2_1 _ H4); specialize (IHHe2_2 _ H5); destr_logic; invert_atom_steps; eauto.
      * exists (x0 @ e5 @ e6); eauto. 
      * exists (x0 @ e2'1 @ e3'0); eauto.
    + specialize (IHHe2_1 _ H3); specialize (IHHe2_2 _ H4); destr_logic; invert_atom_steps; eauto.
      * exists (x0 @ e11 @ e12); inversion H; subst; split; eauto.
      * exists (x0 @ e2'1 @ e3'); inversion H; subst; split; eauto.
  - inversion He3; clear He3; subst; try (try_hyps; clear_funs; destr_logic; invert_atom_steps; eauto; fail).
    + specialize (IHHe2_1 _ H2); specialize (IHHe2_2 _ H4); specialize (IHHe2_3 _ H5).
      destruct IHHe2_1 as [e1'' He1], IHHe2_2 as [e2'' He2], IHHe2_3 as [e3'' He3].
      destr_logic; invert_atom_steps; eexists; (split; [eapply par_wrec_sup; eassumption|]); repeat econstructor; eauto.
  - inversion He3; clear He3; subst; try (try_hyps; clear_funs; destr_logic; invert_atom_steps; eauto; fail).
    + specialize (IHHe2_1 _ H2); specialize (IHHe2_2 _ H4); specialize (IHHe2_3 _ H5).
      destruct IHHe2_1 as [e1'' He1]; destruct IHHe2_2 as [e2'' He2]; destruct IHHe2_3 as [e3'' He3];
      destr_logic; invert_atom_steps;
      eexists; (split; [|eapply par_wrec_sup; eassumption]); repeat econstructor; try apply wk_par_cong; assumption.
    + specialize (IHHe2_1 _ H2); specialize (IHHe2_2 _ H4); specialize (IHHe2_3 _ H5);
      destruct IHHe2_1 as [e1'' He1]; destruct IHHe2_2 as [e2'' He2]; destruct IHHe2_3 as [e3'' He3];
      destruct He3 as [He31 He32]; inversion He31; subst; inversion He32; subst; destr_logic;
      eexists; split; repeat (eapply par_app || eapply par_lam || eapply par_wrec);
      try apply wk_par_cong; try eassumption; eauto.
  - inversion He3; clear He3; subst; try (try_hyps; clear_funs; destr_logic; invert_atom_steps; eauto; fail);
    try_hyps; clear_funs; destr_logic; 
    match goal with [H: true ~> _ |- _] => inversion H; subst | [H: false ~> _ |- _] => inversion H; subst end; eauto.
  - inversion He3; clear He3; subst; try_hyps; clear_funs; destr_logic; invert_atom_steps; eauto;
    repeat match goal with [H: true ~> _ |- _] => inversion H; subst; clear H | [H: false ~> _ |- _] => inversion H; subst; clear H end;
    eauto.
  - inversion He3; clear He3; subst; try_hyps; clear_funs; destr_logic; invert_atom_steps; eauto;
    repeat match goal with [H: true ~> _ |- _] => inversion H; subst; clear H | [H: false ~> _ |- _] => inversion H; subst; clear H end;
    eauto.
  - inversion He3; clear He3; subst; try_hyps; clear_funs; destr_logic; invert_atom_steps; eauto;
    repeat match goal with [H: unit ~> _ |- _] => inversion H; subst end; eauto.
  - inversion He3; clear He3; subst; try_hyps; clear_funs; destr_logic; invert_atom_steps; eauto;
    repeat match goal with [H: unit ~> _ |- _] => inversion H; subst; clear H end; eauto.
Qed.

Infix "~~>" := (clos_trans exp par_red) (at level 50).
Hint Constructors clos_trans.

Hint Resolve par_diamond.

Lemma par_left_fill : forall e1 e2 e3, e1 ~> e2 -> e1 ~~> e3 -> exists e4, e2 ~~> e4 /\ e3 ~> e4.
  intros e1 e2 e3 He2 He3; generalize dependent e2; induction He3; intros.
  - destruct (par_diamond H He2); destr_logic; eauto.
  - try_hyps; destr_logic; try_hyps; destr_logic; eauto.
Qed.

Lemma par_confluent : forall e1 e2 e3, e1 ~~> e2 -> e1 ~~> e3 -> exists e4, e2 ~~> e4 /\ e3 ~~> e4.
  intros e1 e2 e3 He2 He3; generalize dependent e3; induction He2; intros.
  - destruct (par_left_fill H He3); destr_logic; eauto.
  - try_hyps; destr_logic; try_hyps; destr_logic; eauto.
 Qed.

Infix "===>" := (clos_refl_trans_1n exp step) (at level 50).
Hint Constructors clos_refl_trans_1n.

Lemma rtc_rtc : forall A R e1 e2 e3, clos_refl_trans_1n A R e1 e2 -> clos_refl_trans_1n A R e2 e3 -> clos_refl_trans_1n A R e1 e3.
  induction 1; eauto. Qed.

Lemma pi_rtc_cong : forall e1 e1', e1 ===> e1' -> forall e2 e2', e2 ===> e2' -> pi e1 e2 ===> pi e1' e2'.
  repeat induction 1; intros; eauto; eapply rtc_rtc; eauto. Qed.

Lemma lam_rtc_cong : forall e1 e1', e1 ===> e1' -> forall e2 e2', e2 ===> e2' -> lam e1 e2 ===> lam e1' e2'.
  repeat induction 1; intros; eauto; eapply rtc_rtc; eauto. Qed.

Lemma app_rtc_cong : forall e1 e1', e1 ===> e1' -> forall e2 e2', e2 ===> e2' -> app e1 e2 ===> app e1' e2'.
  repeat induction 1; intros; eauto; eapply rtc_rtc; eauto. Qed.

Lemma sg_rtc_cong : forall e1 e1', e1 ===> e1' -> forall e2 e2', e2 ===> e2' -> sigma e1 e2 ===> sigma e1' e2'.
  repeat induction 1; intros; eauto; eapply rtc_rtc; eauto. Qed.

Lemma smk_rtc_cong : forall e1 e1', e1 ===> e1' -> forall e2 e2', e2 ===> e2' -> forall e3 e3', e3 ===> e3' -> smk e1 e2 e3 ===> smk e1' e2' e3'.
  repeat induction 1; intros; eauto; eapply rtc_rtc; eauto. Qed.

Lemma srec_rtc_cong : forall e1 e1', e1 ===> e1' -> forall e2 e2', e2 ===> e2' -> forall e3 e3', e3 ===> e3' -> srec e1 e2 e3 ===> srec e1' e2' e3'.
  repeat induction 1; intros; eauto; eapply rtc_rtc; eauto. Qed.

Lemma wt_rtc_cong : forall e1 e1', e1 ===> e1' -> forall e2 e2', e2 ===> e2' -> wt e1 e2 ===> wt e1' e2'.
  repeat induction 1; intros; eauto; eapply rtc_rtc; eauto. Qed.

Lemma sup_rtc_cong : forall e1 e1', e1 ===> e1' -> forall e2 e2', e2 ===> e2' -> forall e3 e3', e3 ===> e3' -> sup e1 e2 e3 ===> sup e1' e2' e3'.
  repeat induction 1; intros; eauto; eapply rtc_rtc; eauto. Qed.

Lemma wrec_rtc_cong : forall e1 e1', e1 ===> e1' -> forall e2 e2', e2 ===> e2' -> forall e3 e3', e3 ===> e3' -> wrec e1 e2 e3 ===> wrec e1' e2' e3'.
  repeat induction 1; intros; eauto; eapply rtc_rtc; eauto. Qed.

Lemma urec_rtc_cong : forall e1 e1', e1 ===> e1' -> forall e2 e2', e2 ===> e2' -> forall e3 e3', e3 ===> e3' -> urec e1 e2 e3 ===> urec e1' e2' e3'.
  repeat induction 1; intros; eauto; eapply rtc_rtc; eauto. Qed.

Lemma brec_rtc_cong : forall e1 e1', e1 ===> e1' -> forall e2 e2', e2 ===> e2' ->
                      forall e3 e3', e3 ===> e3' -> forall e4 e4', e4 ===> e4' -> brec e1 e2 e3 e4 ===> brec e1' e2' e3' e4'.
  repeat induction 1; intros; eauto; eapply rtc_rtc; eauto. Qed.

Lemma exf_rtc_cong : forall e1 e1', e1 ===> e1' -> forall e2 e2', e2 ===> e2' -> exf e1 e2 ===> exf e1' e2'.
  repeat induction 1; intros; eauto; eapply rtc_rtc; eauto. Qed.

Hint Resolve pi_rtc_cong lam_rtc_cong app_rtc_cong sg_rtc_cong smk_rtc_cong srec_rtc_cong.
Hint Resolve wt_rtc_cong sup_rtc_cong wrec_rtc_cong urec_rtc_cong brec_rtc_cong exf_rtc_cong.

Lemma par_step_rtc : forall e1 e2, e1 ~> e2 -> e1 ===> e2.
  induction 1; eauto; eapply rtc_rtc;
  [eapply app_rtc_cong| |eapply srec_rtc_cong| |eapply wrec_rtc_cong| |
   eapply brec_rtc_cong| |eapply brec_rtc_cong| |eapply urec_rtc_cong|];
  eauto. Qed.

Hint Resolve par_step_rtc.

Lemma step_rtc_equiv : forall e1 e2, e1 ~~> e2 <-> e1 ===> e2.
  split; induction 1; eauto. eapply rtc_rtc; eauto. Qed.

Hint Resolve step_rtc_equiv.

Lemma step_confluent : forall e1 e2 e3, e1 ===> e2 -> e1 ===> e3 -> exists e4, e2 ===> e4 /\ e3 ===> e4.
  intros e1 e2 e3 H1 H2. 
  apply step_rtc_equiv in H1; apply step_rtc_equiv in H2.
  destruct (par_confluent H1 H2) as [x H]; destruct H.
  exists x; split; apply step_rtc_equiv; eauto.
Qed.

Lemma step_pi_pi e1 e2 e3 : pi e1 e2 ==> e3 -> exists e4 e5, e3 = pi e4 e5.
  inversion 1; eauto. Qed.

Ltac invert_nonatomics :=
  repeat match goal with [H: ?e1 = ?e2 |- _] => tryif (atomic e1 || atomic e2) then fail else inversion H; subst; clear H end.

Lemma eval_pi_pi e1 e2 e3 (p : pi e1 e2 ===> e3) : exists e4 e5, e3 = pi e4 e5 /\ e1 ===> e4 /\ e2 ===> e5.
  remember (pi e1 e2) as p12; generalize dependent e2; generalize dependent e1.
  induction p; intros; subst; [eauto|].
  - inversion H; subst.
    + specialize (IHp e1' e2 eq_refl); destr_logic; subst; repeat eexists; eauto.
    + specialize (IHp e1 e2' eq_refl); destr_logic; subst; repeat eexists; eauto.
Qed.

Lemma eval_lam_lam e1 e2 e3 (p : lam e1 e2 ===> e3) : exists e4 e5, e3 = lam e4 e5 /\ e1 ===> e4 /\ e2 ===> e5.
  remember (lam e1 e2) as p12; generalize dependent e2; generalize dependent e1.
  induction p; intros; subst; [eauto|].
  - inversion H; subst.
    + specialize (IHp e1' e2 eq_refl); destr_logic; subst; repeat eexists; eauto.
    + specialize (IHp e1 e2' eq_refl); destr_logic; subst; repeat eexists; eauto.
Qed.

Lemma eval_sg_sg e1 e2 e3 (p : sigma e1 e2 ===> e3) : exists e4 e5, e3 = sigma e4 e5 /\ e1 ===> e4 /\ e2 ===> e5.
  remember (sigma e1 e2) as p12; generalize dependent e2; generalize dependent e1.
  induction p; intros; subst; [eauto|].
  - inversion H; subst.
    + specialize (IHp e1' e2 eq_refl); destr_logic; subst; repeat eexists; eauto.
    + specialize (IHp e1 e2' eq_refl); destr_logic; subst; repeat eexists; eauto.
Qed.

Lemma eval_wt_wt e1 e2 e3 (p : wt e1 e2 ===> e3) : exists e4 e5, e3 = wt e4 e5 /\ e1 ===> e4 /\ e2 ===> e5.
  remember (wt e1 e2) as p12; generalize dependent e2; generalize dependent e1.
  induction p; intros; subst; [eauto|].
  - inversion H; subst.
    + specialize (IHp e1' e2 eq_refl); destr_logic; subst; repeat eexists; eauto.
    + specialize (IHp e1 e2' eq_refl); destr_logic; subst; repeat eexists; eauto.
Qed.

Lemma eval_exf_exf e1 e2 e3 (p : exf e1 e2 ===> e3) : exists e4 e5, e3 = exf e4 e5 /\ e1 ===> e4 /\ e2 ===> e5.
  remember (exf e1 e2) as p12; generalize dependent e2; generalize dependent e1.
  induction p; intros; subst; [eauto|].
  - inversion H; subst.
    + specialize (IHp e1' e2 eq_refl); destr_logic; subst; repeat eexists; eauto.
    + specialize (IHp e1 e2' eq_refl); destr_logic; subst; repeat eexists; eauto.
Qed.

Lemma eval_smk_smk e1 e2 e3 e4 (p : smk e1 e2 e3 ===> e4) : exists e5 e6 e7, e4 = smk e5 e6 e7 /\ e1 ===> e5 /\ e2 ===> e6 /\ e3 ===> e7.
  remember (smk e1 e2 e3) as p12; generalize dependent e3; generalize dependent e2; generalize dependent e1.
  induction p; intros; subst; [repeat eexists; eauto|].
  - inversion H; subst.
    + specialize (IHp e1' e2 e3 eq_refl); destr_logic; subst; repeat eexists; eauto.
    + specialize (IHp e1 e2' e3 eq_refl); destr_logic; subst; repeat eexists; eauto.
    + specialize (IHp e1 e2 e3' eq_refl); destr_logic; subst; repeat eexists; eauto.
Qed.

Lemma eval_sup_sup e1 e2 e3 e4 (p : sup e1 e2 e3 ===> e4) : exists e5 e6 e7, e4 = sup e5 e6 e7 /\ e1 ===> e5 /\ e2 ===> e6 /\ e3 ===> e7.
  remember (sup e1 e2 e3) as p12; generalize dependent e3; generalize dependent e2; generalize dependent e1.
  induction p; intros; subst; [repeat eexists; eauto|].
  - inversion H; subst.
    + specialize (IHp e1' e2 e3 eq_refl); destr_logic; subst; repeat eexists; eauto.
    + specialize (IHp e1 e2' e3 eq_refl); destr_logic; subst; repeat eexists; eauto.
    + specialize (IHp e1 e2 e3' eq_refl); destr_logic; subst; repeat eexists; eauto.
Qed.

Lemma subst_step_cong : forall e1 e1' e2 e2' d, e1 ===> e1' -> e2 ===> e2' -> e1 |> e2 // d ===> e1' |> e2' // d.
  repeat induction 1; [eauto| | |];
  match goal with [H: _ ==> _|-_] => extend (step_par H) end;
  try (repeat match goal with 
           | [H: ?e1 ~> ?e2 |- ?e1 |> _ // _ ===> _ |> _ // _] => 
             eapply subst1_par_cong in H; eapply par_step_rtc in H; eapply rtc_rtc; [eapply H|]
           | [H: ?e1 ~> ?e2 |- _ |> ?e1 // _ ===> _ |> _ // _] => 
             eapply subst2_par_cong in H; eapply par_step_rtc in H; eapply rtc_rtc; [eapply H|]
         end; eauto; fail).
  eapply rtc_rtc; [apply par_step_rtc; apply subst1_par_cong|apply IHclos_refl_trans_1n]; eauto.
Qed.

Lemma eval_app e1 e2 e3 (p: e1 @ e2 ===> e3) : (exists e4 e5, e3 = e4 @ e5 /\ e1 ===> e4 /\ e2 ===> e5) 
                                               \/ (exists e4 e5, e1 ===> lam e4 e5 /\ e5 |> e2 // 0 ===> e3).
  remember (e1 @ e2) as e12; generalize dependent e2; generalize dependent e1; 
  induction p; intros; subst; [left;eauto|].
  - inversion H; subst; eauto; destruct (IHp _ _ eq_refl);
    destr_logic; [left|right|left|right]; subst; repeat eexists; eauto.
    + eapply rtc_rtc; [eapply subst_step_cong|eassumption]; eauto.
Qed.

Lemma eval_srec e1 e2 e3 e4 (p : srec e1 e2 e3 ===> e4) : 
  (exists e5 e6 e7, e4 = srec e5 e6 e7 /\ e1 ===> e5 /\ e2 ===> e6 /\ e3 ===> e7)
  \/ (exists e5 e6 e7, e3 ===> smk e5 e6 e7 /\ e2 @ e6 @ e7 ===> e4).
  remember (srec e1 e2 e3) as e12; generalize dependent e3; generalize dependent e2; generalize dependent e1; 
  induction p; intros; subst; [left;repeat eexists;eauto|].
  - inversion H; subst; eauto; try destruct (IHp _ _ _ eq_refl);
    destr_logic; subst; try (left; repeat eexists; eauto; fail); right; repeat eexists; eauto.
Qed.

Lemma eval_wrec e1 e2 e3 e4 (p : wrec e1 e2 e3 ===> e4) : 
  (exists e5 e6 e7, e4 = wrec e5 e6 e7 /\ e1 ===> e5 /\ e2 ===> e6 /\ e3 ===> e7)
  \/ (exists e5 e6 e7, e3 ===> sup e5 e6 e7 /\ 
                 e2 @ e6 @ lam (e5 @ e6) (wrec (wk_deep 1 0 e1) (wk_deep 1 0 e2) (wk_deep 1 0 e7 @ &0)) ===> e4).
  remember (wrec e1 e2 e3) as e12; generalize dependent e3; generalize dependent e2; generalize dependent e1; 
  induction p; intros; subst; [left;repeat eexists;eauto|].
  - inversion H; subst; eauto; try destruct (IHp _ _ _ eq_refl);
    destr_logic; subst; try (left; repeat eexists; eauto; fail); 
    right; repeat eexists; eassumption || eauto;
    (eapply rtc_rtc; [|eassumption]);
    repeat (apply app_rtc_cong || apply lam_rtc_cong || apply wrec_rtc_cong); eauto.
Qed.

Lemma eval_brec e1 e2 e3 e4 e5 (p: brec e1 e2 e3 e4 ===> e5) :
  (exists e6 e7 e8 e9, e5 = brec e6 e7 e8 e9 /\ e1 ===> e6 /\ e2 ===> e7 /\ e3 ===> e8 /\ e4 ===> e9)
  \/ (e4 ===> true /\ e2 ===> e5) \/ (e4 ===> false /\ e3 ===> e5).
  remember (brec e1 e2 e3 e4) as e12; 
  generalize dependent e4; generalize dependent e3; generalize dependent e2; generalize dependent e1; 
  induction p; intros; subst; [left;repeat eexists;eauto|].
  - inversion H; subst; eauto; try destruct (IHp _ _ _ _ eq_refl);
    destr_logic; subst; try (left; repeat eexists; eauto; fail); 
    right; repeat eexists; eassumption || eauto.
Qed.

Lemma eval_urec e1 e2 e3 e4 (p: urec e1 e2 e3 ===> e4) :
  (exists e5 e6 e7, e4 = urec e5 e6 e7 /\ e1 ===> e5 /\ e2 ===> e6 /\ e3 ===> e7)
  \/ (e3 ===> unit /\ e2 ===> e4).
  remember (urec e1 e2 e3) as e12; generalize dependent e3; generalize dependent e2; generalize dependent e1; 
  induction p; intros; subst; [left;repeat eexists;eauto|].
  - inversion H; subst; eauto; try destruct (IHp _ _ _ eq_refl);
    destr_logic; subst; try (left; repeat eexists; eauto; fail); 
    right; repeat eexists; eassumption || eauto.
Qed.

Definition is_normal e : Prop := forall e', ~ e ==> e'.

Hint Unfold is_normal.

Theorem normal_forms_unique : forall e1 e2 e3, is_normal e2 -> is_normal e3 -> e1 ===> e2 -> e1 ===> e3 -> e2 = e3.
  intros e1 e2 e3 He2 He3 Hs1 Hs2.
  assert (H: exists e4, e2 ===> e4 /\ e3 ===> e4) by (apply step_confluent with (e1 := e1); auto).
  destruct H as [e4 He4]; destruct He4 as [Hc1 Hc2]; destruct Hc1; destruct Hc2; auto;
  unfold is_normal in *; try_hyps; contradiction.
Qed.

Inductive nf : exp -> Prop :=
| nf_var : forall i, nf (&i)
| nf_typ : forall n, nf (typ n)
| nf_pi : forall A B, nf A -> nf B -> nf (pi A B)
| nf_sg : forall A B, nf A -> nf B -> nf (sigma A B)
| nf_wt : forall A B, nf A -> nf B -> nf (wt A B)
| nf_bool : nf bool
| nf_top : nf top
| nf_bot : nf bot
| nf_lam : forall A b, nf A -> nf b -> nf (lam A b)
| nf_smk : forall B a b, nf B -> nf a -> nf b -> nf (smk B a b)
| nf_sup : forall B a f, nf B -> nf a -> nf f -> nf (sup B a f)
| nf_true : nf true
| nf_false : nf false
| nf_unit : nf unit
| nf_exf : forall B f, nf B -> nf f -> nf (exf B f).

Lemma nf_normal : forall e, nf e -> is_normal e.
  unfold is_normal; induction 1; inversion 1; subst; try_hyps; contradiction. Qed.

