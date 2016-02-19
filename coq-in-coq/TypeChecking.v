Require Import Unscoped.
Infix "==" := (exp_eq_dec) (at level 50).

Open Scope type_scope.

Definition and_sumor A1 A2 P1 P2 : A1 + {P1} -> A2 + {P2} -> (A1 * A2) + {P1 \/ P2}.
  repeat destruct 1; auto. Defined.

Arguments and_sumor {A1} {A2} {P1} {P2} s1 s2.
Infix "&&" := and_sumor.

Lemma typ_uq Gamma e T1 T2 : Gamma ⊢ e ∈ T1 -> Gamma ⊢ e ∈ T2 -> T1 = T2.
  intro Ht1; generalize dependent T2; induction Ht1; inversion 1; subst; intros;
  repeat match goal with [IH: forall T, ?Gamma ⊢ ?A ∈ T -> ?T1 = T, H : ?Gamma ⊢ ?A ∈ ?T2 |- _] => apply IH in H; inversion H; subst end;
  try reflexivity.
  - unfold lookup_wk; f_equal; apply lookup_irrel.
Qed.

Definition prop_and {A B C D} : {A} + {B} -> {C} + {D} -> {A /\ C} + {B \/ D}. auto. Qed.
Infix "&p&" := prop_and (at level 500, left associativity).

Local Hint Extern 1 => inversion 1; subst.
Local Hint Extern 1 => econstructor; eassumption.

Ltac assert_uqs :=
  repeat match goal with
           | [H1 : ?Gamma ⊢ ?e ∈ ?T1 , H2 : ?Gamma ⊢ ?e ∈ ?T2 |- _]
             => assert (T1 = T2) by (eapply typ_uq; eassumption); subst; clear H2
         end.

Ltac assert_uqs_inv :=
  repeat match goal with
           | [H1 : ?Gamma ⊢ ?e ∈ ?T1 , H2 : ?Gamma ⊢ ?e ∈ ?T2 |- _]
             => assert (H:T1 = T2) by (eapply typ_uq; eassumption); inversion H; subst; clear H2
         end.

Local Hint Extern 1 => assert_uqs.

Theorem ty_check e : forall Gamma, {T | has_type Gamma e T} + {forall T, ~has_type Gamma e T}.
  induction e; intros;
  (* make var do the right thing *)
  try (destruct (lt_dec ix (length Gamma)) as [Hg|nHg];
       [left; exists (lookup_wk Gamma (exist _ ix Hg)); auto
       |right; inversion 1; subst; contradiction]);
  (* trivial cases *)
  try (left; repeat econstructor; eassumption; fail); try (right; inversion 1; assert_uqs; congruence; fail);
  (* pi, lam, sigma, wt *)
  try (destruct (IHe1 Gamma) as [T1 | nT1]; destruct (IHe2 (Gamma ▻ e1)) as [T2 | nT2];
       try (right; inversion 1; eapply nT1 || eapply nT2; eassumption);
       destruct T1 as [T1 Ht1]; try destruct T2 as [T2 Ht2];
       destruct T1; try (right; inversion 1; subst; assert_uqs; congruence; fail);
       destruct T2; try (right; inversion 1; subst; assert_uqs; congruence; fail);
       left; repeat econstructor; eassumption).
  (* app *)
  - destruct (IHe1 Gamma) as [T1 | nT1]; destruct (IHe2 Gamma) as [T2 | nT2];
    try destruct T1 as [T1 Ht1]; try destruct T2 as [T2 Ht2];
    try (right; inversion 1; eapply nT1 || eapply nT2; eassumption).
    + destruct T1; try (right; inversion 1; subst; assert_uqs; congruence; fail).
      destruct (T2 == T1_1); [left|right; inversion 1; assert_uqs; congruence]; subst; repeat econstructor; eassumption.
  (* smk *)
  - destruct (IHe2 Gamma) as [T2 | nT2]; destruct (IHe3 Gamma) as [T3 | nT3];
    try (right; inversion 1; eapply nT2 || eapply nT3; eassumption);
    destruct T2 as [T2 Ht2]; destruct T3 as [T3 Ht3].
    destruct (T3 == subst_deep e2 0 e1); subst;
    [left; repeat econstructor; eassumption|right; inversion 1; subst; assert_uqs; congruence].
  (* srec *)
  - destruct (IHe3 Gamma) as [T3 | nT3]; [|right; inversion 1; eapply nT3; eassumption].
    destruct T3 as [T3 Ht3]; destruct T3; try (right; inversion 1; assert_uqs; congruence).
    destruct (IHe2 (Gamma ▻ T3_1 ▻ T3_2)) as [T2|nT2]; [destruct T2 as [T2 Ht2]|].
    + destruct (T2 == subst_deep (smk T3_2 (&1) (&0)) 0 (wk_deep 2 1 e1)).
      * left; subst; repeat econstructor; eassumption.
      * right; inversion 1; subst; assert_uqs; inversion H0; subst; assert_uqs; congruence.
    + right; inversion 1; subst; assert_uqs; inversion H0; subst; eapply nT2; eassumption.
  (* sup *)
  - destruct (IHe2 Gamma) as [T2|nT2]; [|right; inversion 1; eapply nT2; eassumption].
    destruct T2 as [T2 Ht2]; destruct (IHe1 (Gamma ▻ T2)) as [T1|nT1]; [|right; inversion 1; assert_uqs; eapply nT1; eassumption].
    destruct T1 as [T1 Ht1]; destruct T1; try (right; inversion 1; assert_uqs; congruence).
    destruct (IHe3 (Gamma ▻ subst_deep e2 0 e1)) as [T3|nT3]; [|right; inversion 1; assert_uqs; eapply nT3; eassumption].
    destruct T3 as [T3 Ht3]; destruct (T3 == wk_at 0 (wt T2 e1)); [|right; inversion 1; assert_uqs;congruence].
    + left; subst; repeat econstructor; eassumption.
  (* wrec *)
  - destruct (IHe3 Gamma) as [T3|nT3]; [|right; inversion 1; eapply nT3; eassumption].
    destruct T3 as [T3 Ht3].
    destruct T3; try (right; inversion 1; assert_uqs; congruence).
    destruct (IHe2 (Gamma ▻ T3_1 ▻ pi T3_2 (wk_deep 2 0 (wt T3_1 T3_2)) ▻ wk_at 1 T3_2)) as [T2|nT2];
      [|right; inversion 1; assert_uqs; inversion H6; subst; assert_uqs; eapply nT2; eauto].
    destruct T2 as [T2 Ht2]; destruct (T2 == subst_deep (&1 @ &0) 0 (wk_deep 3 1 e1));
      [subst; left; repeat econstructor; eassumption
      |right; inversion 1; subst; assert_uqs; inversion H0; subst; assert_uqs; congruence].
  (* brec *)
  - destruct (IHe2 Gamma) as [T2|nT2]; destruct (IHe3 Gamma) as [T3|nT3]; destruct (IHe4 Gamma) as [T4|nT4];
    try (right; inversion 1; assert_uqs; eapply nT2 || eapply nT3 || eapply nT4; eassumption);
    destruct T2 as [T2 Ht2]; destruct T3 as [T3 Ht3]; destruct T4 as [T4 Ht4];
    destruct T4 , (T2 == subst_deep true 0 e1) , (T3 == subst_deep false 0 e1);
    try (right; inversion 1; assert_uqs; congruence);
    subst; left; repeat econstructor; eassumption.
  (* urec *)
  - destruct (IHe2 Gamma) as [T2|nT2]; destruct (IHe3 Gamma) as [T3|nT3];
    try (right; inversion 1; assert_uqs; eapply nT2 || eapply nT3; eassumption);
    destruct T2 as [T2 Ht2]; destruct T3 as [T3 Ht3];
    destruct T3 , (T2 == subst_deep unit 0 e1); try (right; inversion 1; assert_uqs; congruence);
    subst; left; repeat econstructor; eassumption.
  (* exf *)
  - destruct (IHe1 (Gamma ▻ bot)) as [T1|nT1]; destruct (IHe2 Gamma) as [T2|nT2];
    try (right; inversion 1; assert_uqs; eapply nT1 || eapply nT2; eassumption);
    destruct T1 as [T1 Ht1]; destruct T2 as [T2 Ht2];
    destruct T1; try (right; inversion 1; assert_uqs; congruence);
    (* separately because case explosion = bad *)
    destruct T2; try (right; inversion 1; assert_uqs; congruence);
    subst; left; repeat econstructor; eassumption.
Defined.
