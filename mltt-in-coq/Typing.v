(* imports *)
Require Import Omega Coq.Program.Program Coq.Program.Tactics.
Require Import Unscoped Evaluation DeBrujin.

Set Implicit Arguments.

Definition con := list exp.

Program Definition lookup_wk (Gamma : con) (i : {x | x < length Gamma}) := wk_deep (S i) 0 (lookup_lt Gamma i).

(* Program Definition lookup_wk_scoped_subset (Gamma : {gamma | scoped_con gamma}) i : scoped_at (length Gamma) (lookup_wk Gamma i) := *)
(*   wk_scoped (lookup_lt Gamma i) (length Gamma - S i) _ (S i) 0. *)

(* (* split for nicer proof terms *) *)
(* Lemma lookup_wk_scoped (Gamma : con) (p : scoped_con Gamma) : forall i, scoped_at (length Gamma) (lookup_wk Gamma i). *)
(*   apply (lookup_wk_scoped_subset (exist _ Gamma p)). Qed. *)

(* Hint Resolve lookup_wk_scoped. *)

Infix "▻" := (fun Gamma a => cons a Gamma) (at level 50, left associativity).
Infix "-->" := (fun a b => pi a (wk_deep 1 0 b)) (at level 20, right associativity).

Reserved Notation "Gamma ⊢ t ∈ T" (at level 85).

Inductive has_type (Gamma: con) : exp -> exp -> Prop :=
| ty_var : forall i p, Gamma ⊢ & i ∈ lookup_wk Gamma << i , p >>

| ty_set : forall n, Gamma ⊢ typ n ∈ typ (S n)
(* (* for now, how about no? *)
| ty_cumulative : forall A n, Gamma ⊢ A ∈ typ n
                       -> Gamma ⊢ A ∈ typ (S n)

| ty_pi_prop : forall A P n, Gamma ⊢ A ∈ (typ n)
                      -> Gamma ▻ A ⊢ P ∈ prop
                      -> Gamma ⊢ pi A P ∈ prop
*)
| ty_pi_typ : forall A B n m, Gamma ⊢ A  ∈ typ n
                       -> Gamma ▻ A ⊢ B ∈ typ m
                       -> Gamma ⊢ pi A B ∈ typ (max n m)

| ty_sg_typ : forall A B n m, Gamma ⊢ A ∈ typ n
                       -> Gamma ⊢ B ∈ (pi A (typ m))
                       -> Gamma ⊢ sigma A B ∈ typ (max n m)

| ty_wt_typ : forall A B n m, Gamma ⊢ A ∈ typ n
                       -> Gamma ⊢ B ∈ (pi A (typ m))
                       -> Gamma ⊢ wt A B ∈ typ (max n m)

| ty_bool : Gamma ⊢ bool ∈ typ 0
| ty_top : Gamma ⊢ top ∈ typ 0
| ty_bot : Gamma ⊢ bot ∈ typ 0

| ty_lam : forall A n B b, Gamma ⊢ A ∈ typ n
                    -> Gamma ▻ A ⊢ b ∈ B
                    -> Gamma ⊢ lam A b ∈ pi A B

| ty_app : forall A B f a, Gamma ⊢ f ∈ pi A B
                    -> Gamma ⊢ a ∈ A
                    -> Gamma ⊢ f @ a ∈ B |> a // 0

| ty_smk : forall A B a b, Gamma ⊢ a ∈ A
                    -> Gamma ⊢ b ∈ B @ a
                    -> Gamma ⊢ smk B a b ∈ sigma A B

| ty_srec : forall A B C f s, Gamma ⊢ f ∈ pi A (pi (wk_deep 1 0 B @ &0) (wk_deep 2 0 C @ (smk (wk_deep 2 0 B) (&1) (&0))))
                       -> Gamma ⊢ s ∈ sigma A B
                       -> Gamma ⊢ srec C f s ∈ C @ s

| ty_sup : forall A B n a f, Gamma ⊢ B ∈ pi A (typ n)
                      -> Gamma ⊢ a ∈ A
                      -> Gamma ⊢ f ∈ ((B @ a) --> wt A B)
                      -> Gamma ⊢ sup B a f ∈ wt A B

| ty_wrec : forall C A B f w,
              Gamma ⊢ f ∈ pi A (pi (pi (wk_deep 1 0 B @ &0) (wk_deep 2 0 (wt A B)))
                             (pi (pi (wk_deep 2 0 B @ &1) 
                                   (wk_deep 3 0 C @ (&1 @ &0)))
                                (wk_deep 3 0 C @ sup (wk_deep 3 0 B) (&2) (&1))))
            -> Gamma ⊢ w ∈ wt A B
            -> Gamma ⊢ wrec C f w ∈ C @ w
| ty_true : Gamma ⊢ true ∈ bool
| ty_false : Gamma ⊢ false ∈ bool
| ty_brec : forall C t f b, 
              Gamma ⊢ t ∈ C @ true
            -> Gamma ⊢ f ∈ C @ false
            -> Gamma ⊢ b ∈ bool
            -> Gamma ⊢ brec C t f b ∈ C @ b

| ty_unit : Gamma ⊢ unit ∈ top
| ty_urec : forall C u t, Gamma ⊢ u ∈ C @ unit
                   -> Gamma ⊢ t ∈ top
                   -> Gamma ⊢ urec C u t ∈ C @ t

| ty_exf : forall C n f, Gamma ⊢ C ∈ (bot --> typ n)
                  -> Gamma ⊢ f ∈ bot
                  -> Gamma ⊢ exf C f ∈ C @ f

| ty_step_to : forall e t1 t2, t1 ==> t2 -> Gamma ⊢ e ∈ t1 -> Gamma ⊢ e ∈ t2
| ty_step_from : forall e t1 t2, t1 ==> t2 -> Gamma ⊢ e ∈ t2 -> Gamma ⊢ e ∈ t1
where "Gamma ⊢ t ∈ T" := (has_type Gamma t T).

Hint Constructors has_type.

Hint Rewrite List.app_length.

Lemma lookup_plus_option A : forall (Delta Gamma : list A) i, lookup_con Gamma i = lookup_con (Delta ++ Gamma) (⟦Delta⟧ + i).
  induction Delta; intros; auto.
  - rewrite IHDelta; simpl; destruct (lookup_con (Delta ++ Gamma) (⟦Delta⟧ + i)); auto. 
Qed.

Definition wk_ix n d i : nat := if le_dec d i then n + i else i.

Lemma lookup_plus_option2 A (Gamma Delta delta: list A) : forall i,
  lookup_con (Gamma ++ Delta) i = lookup_con (Gamma ++ delta ++ Delta) (wk_ix ⟦delta⟧ ⟦Gamma⟧ i).
  intro i. unfold wk_ix. destruct (le_dec ⟦Gamma⟧ i) as [Hle|Hnle].
  - generalize dependent i; induction Gamma; intros; simpl in *.
    + apply lookup_plus_option.
    + destruct i; [omega|rewrite <- plus_n_Sm]. 
      assert(H: ⟦Gamma⟧ <= i) by omega; specialize (IHGamma i H); clear H.
      destruct (lookup_con (Gamma ++ Delta) i) , (lookup_con (Gamma ++ delta ++ Delta) (⟦delta⟧ + i)); inversion IHGamma; subst; auto.
  - generalize dependent i; induction Gamma; intros; simpl in *; [omega|destruct i]; auto.
    assert(H: ~ ⟦Gamma⟧ <= i) by omega; specialize (IHGamma i H);
    destruct (lookup_con (Gamma ++ Delta) i) , (lookup_con (Gamma ++ delta ++ Delta) i); inversion IHGamma; subst; auto.      
Qed.
    
Hint Resolve lookup_plus_option lookup_plus_option2.
Hint Rewrite lookup_plus_option lookup_plus_option2.

Program Definition lookup_plus_ty A (Gamma Delta : list A) := forall i, lookup_lt Gamma i = lookup_lt (Delta ++ Gamma) (⟦Delta⟧ + i).
Next Obligation. rewrite List.app_length. omega. Qed.

(* this is complicated because chained reasoning that can only come together at the very end *)
Lemma lookup_plus A (Gamma Delta : list A) : lookup_plus_ty Gamma Delta.
  unfold lookup_plus_ty; intro i.
  assert (Hob: ⟦Delta⟧ + `i < ⟦Delta ++ Gamma⟧) by (rewrite  List.app_length; destruct i; simpl; omega).
  assert (H:Some (lookup_lt Gamma i) = Some (lookup_lt (Delta ++ Gamma) (exist _ (⟦Delta⟧ + `i) Hob)))
    by (repeat rewrite <- lookup_lt_con; apply lookup_plus_option).
  inversion H as [H']; rewrite H'; apply lookup_irrel; reflexivity.
Qed.

Program Definition wk_ix_lt A delta Gamma {Delta:list A} (ix: {i | i < ⟦Gamma ++ Delta⟧}) : {i | i < ⟦Gamma ++ delta ++ Delta⟧} := wk_ix ⟦delta⟧ ⟦Gamma⟧ ix.
Obligation 1. repeat rewrite List.app_length in *; unfold wk_ix; destr_choices; omega. Qed.

Lemma lookup_plus2 A (Gamma Delta delta : list A) : forall i, lookup_lt (Gamma ++ Delta) i = lookup_lt (Gamma ++ delta ++ Delta) (wk_ix_lt delta Gamma i).
  unfold wk_ix_lt; intro i.
  assert (Hob: wk_ix ⟦delta⟧ ⟦Gamma⟧ (` i) < ⟦Gamma++delta++Delta⟧)
   by (destruct i; simpl in *; repeat rewrite List.app_length in *; unfold wk_ix; destr_choices; omega).
  assert (H:Some (lookup_lt (Gamma ++ Delta) i) = Some (lookup_lt (Gamma ++ delta ++ Delta) (exist _ (wk_ix ⟦delta⟧ ⟦Gamma⟧ (`i)) Hob)))
   by (repeat rewrite <- lookup_lt_con; apply lookup_plus_option2).
  inversion H as [H']; rewrite H'; apply lookup_irrel; reflexivity.
Qed.

Hint Resolve lookup_plus lookup_plus2.
Hint Rewrite lookup_plus lookup_plus2.

Lemma wk_ix_deep : forall n d i, wk_deep n d (&i) = &(wk_ix n d i).
  unfold wk_deep,wk_var,wk_ix; intros; destr_choices; f_equal; omega. Qed.

Lemma wk_ix_lt_eq A : forall Gamma delta Delta i, ` (@wk_ix_lt A delta Gamma Delta i) = wk_ix ⟦delta⟧ ⟦Gamma⟧ (` i).
  reflexivity. Qed.

Inductive wf_con : con -> Prop :=
| wf_nil : wf_con nil
| wf_cons : forall Gamma A n, wf_con Gamma -> Gamma ⊢ A ∈ (typ n) -> wf_con (Gamma ▻ A).

Hint Constructors wf_con.

Lemma typ_conv : forall Gamma e t1 t2, t1 ===> t2 -> Gamma ⊢ e ∈ t1 <-> Gamma ⊢ e ∈ t2.
    induction 1; split; intros; auto.
    - apply IHclos_refl_trans_1n; eauto.
    - eapply ty_step_from; [eassumption|]. eapply IHclos_refl_trans_1n; auto.
Qed.

Lemma ty_var_confl Gamma i T : Gamma ⊢ & i ∈ T -> exists T' p, lookup_wk Gamma << i , p >> ===> T' /\ T ===> T'.
  remember (& i) as i'; induction 1; inversion Heqi'; subst.
  - eexists; eauto.
  - destruct (IHhas_type eq_refl) as [t1' Ht]; destr_logic.
    assert (exists t2', t2 ===> t2' /\ t1' ===> t2') by (apply step_confluent with (e1 := t1); eauto).
    destr_logic; repeat eexists; [eapply rtc_rtc|]; eassumption.
  - destruct (IHhas_type eq_refl); destr_logic; eauto.
Qed.

Lemma ty_typ_confl Gamma n T : Gamma ⊢ typ n ∈ T -> T ===> typ (S n).
  remember (typ n) as tn; induction 1; inversion Heqtn; subst; auto; specialize (IHhas_type eq_refl); eauto.
  - assert (exists t2', t2 ===> t2' /\ typ (S n) ===> t2') by (apply step_confluent with (e1 := t1); eauto).
    destruct H2 as [t2' Ht2']; destruct Ht2' as [Ht2' Htyp]; destruct Htyp as [|y z Htyp Ht']; eauto; inversion Htyp.
Qed.

Lemma ty_pi_confl Gamma A B T : Gamma ⊢ pi A B ∈ T -> exists n m, (Gamma ⊢ A ∈ typ n) /\ (Gamma ▻ A ⊢ B ∈ typ m) /\ T ===> typ (max n m).
  remember (pi A B) as pab; induction 1; inversion Heqpab; subst; eauto; 
  destruct (IHhas_type eq_refl) as [n Hn]; destruct Hn as [m Hnm]; destruct Hnm as [Ha Hbt]; destruct Hbt as [Hb Ht];
  exists n; exists m; repeat split; eauto.
  - assert (exists t2', t2 ===> t2' /\ typ (max n m) ===> t2') by (apply step_confluent with (e1 := t1); eauto).
    destruct H2 as [t2' Ht2']; destruct Ht2' as [Ht2' Htyp]; destruct Htyp as [|y z Htyp Ht']; eauto; inversion Htyp.
Qed.

Lemma ty_sg_confl Gamma A B T : Gamma ⊢ sigma A B ∈ T -> exists n m, (Gamma ⊢ A ∈ typ n) /\ (Gamma ⊢ B ∈ pi A (typ m)) /\ T ===> typ (max n m).
  remember (sigma A B) as pab; induction 1; inversion Heqpab; subst; eauto; 
  destruct (IHhas_type eq_refl) as [n Hn]; destruct Hn as [m Hnm]; destruct Hnm as [Ha Hbt]; destruct Hbt as [Hb Ht];
  exists n; exists m; repeat split; eauto.
  - assert (exists t2', t2 ===> t2' /\ typ (max n m) ===> t2') by (apply step_confluent with (e1 := t1); eauto).
    destruct H2 as [t2' Ht2']; destruct Ht2' as [Ht2' Htyp]; destruct Htyp as [|y z Htyp Ht']; eauto; inversion Htyp.
Qed.

Lemma ty_wt_confl Gamma A B T : Gamma ⊢ wt A B ∈ T -> exists n m, (Gamma ⊢ A ∈ typ n) /\ (Gamma ⊢ B ∈ pi A (typ m)) /\ T ===> typ (max n m).
  remember (wt A B) as pab; induction 1; inversion Heqpab; subst; eauto; 
  destruct (IHhas_type eq_refl) as [n Hn]; destruct Hn as [m Hnm]; destruct Hnm as [Ha Hbt]; destruct Hbt as [Hb Ht];
  exists n; exists m; repeat split; eauto.
  - assert (exists t2', t2 ===> t2' /\ typ (max n m) ===> t2') by (apply step_confluent with (e1 := t1); eauto).
    destruct H2 as [t2' Ht2']; destruct Ht2' as [Ht2' Htyp]; destruct Htyp as [|y z Htyp Ht']; eauto; inversion Htyp.
Qed.

Lemma ty_bool_confl Gamma T : Gamma ⊢ bool ∈ T -> T ===> typ 0.
  remember bool as b; induction 1; inversion Heqb; subst; eauto; specialize (IHhas_type eq_refl).
  - assert (exists t2', t2 ===> t2' /\ typ 0 ===> t2') by (apply step_confluent with (e1 := t1); eauto).
    destruct H2 as [t2' Ht2']; destruct Ht2' as [Ht2' Htyp]; destruct Htyp as [|y z Htyp Ht']; eauto; inversion Htyp.
Qed.  

Lemma ty_top_confl Gamma T : Gamma ⊢ top ∈ T -> T ===> typ 0.
  remember top as b; induction 1; inversion Heqb; subst; eauto; specialize (IHhas_type eq_refl).
  - assert (exists t2', t2 ===> t2' /\ typ 0 ===> t2') by (apply step_confluent with (e1 := t1); eauto).
    destruct H2 as [t2' Ht2']; destruct Ht2' as [Ht2' Htyp]; destruct Htyp as [|y z Htyp Ht']; eauto; inversion Htyp.
Qed.  

Lemma ty_bot_confl Gamma T : Gamma ⊢ bot ∈ T -> T ===> typ 0.
  remember bot as b; induction 1; inversion Heqb; subst; eauto; specialize (IHhas_type eq_refl).
  - assert (exists t2', t2 ===> t2' /\ typ 0 ===> t2') by (apply step_confluent with (e1 := t1); eauto).
    destruct H2 as [t2' Ht2']; destruct Ht2' as [Ht2' Htyp]; destruct Htyp as [|y z Htyp Ht']; eauto; inversion Htyp.
Qed.

Lemma ty_true_confl Gamma T : Gamma ⊢ true ∈ T -> T ===> bool.
  remember true as b; induction 1; inversion Heqb; subst; eauto; specialize (IHhas_type eq_refl).
  - assert (exists t2', t2 ===> t2' /\ bool ===> t2') by (apply step_confluent with (e1 := t1); eauto).
    destruct H2 as [t2' Ht2']; destruct Ht2' as [Ht2' Htyp]; destruct Htyp as [|y z Htyp Ht']; eauto; inversion Htyp.
Qed.

Lemma ty_false_confl Gamma T : Gamma ⊢ false ∈ T -> T ===> bool.
  remember false as b; induction 1; inversion Heqb; subst; eauto; specialize (IHhas_type eq_refl).
  - assert (exists t2', t2 ===> t2' /\ bool ===> t2') by (apply step_confluent with (e1 := t1); eauto).
    destruct H2 as [t2' Ht2']; destruct Ht2' as [Ht2' Htyp]; destruct Htyp as [|y z Htyp Ht']; eauto; inversion Htyp.
Qed.

Lemma ty_unit_confl Gamma T : Gamma ⊢ unit ∈ T -> T ===> top.
  remember unit as b; induction 1; inversion Heqb; subst; eauto; specialize (IHhas_type eq_refl).
  - assert (exists t2', t2 ===> t2' /\ top ===> t2') by (apply step_confluent with (e1 := t1); eauto).
    destruct H2 as [t2' Ht2']; destruct Ht2' as [Ht2' Htyp]; destruct Htyp as [|y z Htyp Ht']; eauto; inversion Htyp.
Qed.

Lemma wk_step_cong e1 e2 n d : e1 ==> e2 -> wk_deep n d e1 ===> wk_deep n d e2. auto. Qed.
Lemma wk_eval_cong e1 e2 n d : e1 ===> e2 -> wk_deep n d e1 ===> wk_deep n d e2. 
  induction 1; eauto; eapply rtc_rtc; [eapply wk_step_cong|]; eassumption. Qed.

Hint Resolve wk_eval_cong.

Lemma con_var_cong Gamma T i t1 t2 (Ht : t1 ===> t2) : t1 :: Gamma ⊢ &i ∈ T <-> t2 :: Gamma ⊢ &i ∈ T.
  remember (&i) as ix; split; intro Hi.
  - generalize dependent t2; remember (t1 :: Gamma) as gamma; induction Hi; inversion Heqgamma; inversion Heqix; subst; intros.
    + destruct i; unfold lookup_wk; simpl.
      * eapply typ_conv; [eapply wk_eval_cong;eassumption|].
        replace (⟦ t1 :: Gamma ⟧) with (⟦ t2 :: Gamma ⟧) in p by auto;
        replace (wk_deep 1 0 t2) with (lookup_wk (t2 :: Gamma) <<0, p>>) by auto.
        constructor.
      * rewrite <- lookup_cons with (a := t2). unfold fsu; erewrite lookup_irrel; [apply ty_var|auto].
    + specialize (IHHi eq_refl eq_refl). 
Admitted.

Lemma con_cons_cong e : forall t1 t2, t1 ===> t2 -> forall Gamma T, (t1 :: Gamma) ⊢ e ∈ T <-> (t2 :: Gamma) ⊢ e ∈ T.
  induction e; intros; eauto.
  - split; inversion 1; subst; auto.
    + induction ix.
Admitted.

Hint Resolve con_cons_cong.
Hint Rewrite con_cons_cong.

Lemma ty_lam_confl Gamma e1 e2 T : Gamma ⊢ lam e1 e2 ∈ T -> exists A B, T ===> pi A B /\ (Gamma ▻ A ⊢ e2 ∈ B) /\ e1 ===> A.
  intro Ht; remember (lam e1 e2) as lae; induction Ht; inversion Heqlae; subst; [repeat eexists;eauto| |];
  destruct (IHHt eq_refl) as [A Hb]; destruct Hb as [B Hab]; destruct Hab as [He2 Het];
  destruct Het as [He1 HT]; clear IHHt;
  assert (Ht3: exists t3, t2 ===> t3 /\ pi A B ===> t3) by (eapply step_confluent; [|eassumption]; eauto);
  destruct Ht3 as [t3 Ht3]; destruct Ht3 as [H23 Hpi]; destr_logic; [|repeat eexists; eauto].
  - extend (eval_pi_pi Hpi); destr_logic; subst; destr_logic.
    repeat eexists; [eassumption| |].
    + erewrite <- con_cons_cong; [|eassumption];erewrite <- typ_conv; eassumption.
    + eapply rtc_rtc; eassumption.
Qed.

Lemma ty_sup_confl Gamma e1 e2 e3 T : 
  Gamma ⊢ sup e1 e2 e3 ∈ T -> exists A B, T ===> wt A B /\ e1 ===> B /\ (Gamma ⊢ e2 ∈ A) /\ (Gamma ⊢ e3 ∈ (B @ e2 --> wt A B)).
  intro Ht; remember (sup e1 e2 e3) as sae; induction Ht; inversion Heqsae; subst; [repeat eexists;eauto| |];
  destruct (IHHt eq_refl) as [A Hb]; destruct Hb as [B Hab]; destruct Hab as [Ht1 He]; destruct He as [Heb He3];
  assert (Ht3: exists t3, t2 ===> t3 /\ wt A B ===> t3) by (eapply step_confluent; [|eassumption]; eauto);
  destruct Ht3 as [t3 Ht3]; destruct Ht3 as [H23 Hwt];
  extend (eval_wt_wt Hwt); destr_logic; subst;
  (repeat eexists;
   [eassumption || eauto
   |eapply rtc_rtc; eauto
   |erewrite <- typ_conv; eauto
   |erewrite <- typ_conv; [eassumption|apply pi_rtc_cong; [apply app_rtc_cong|]; eauto]]).
Qed.

Lemma ty_smk_confl Gamma e1 e2 e3 T : 
  Gamma ⊢ smk e1 e2 e3 ∈ T -> exists A B, T ===> sigma A B /\ e1 ===> B /\ (Gamma ⊢ e2 ∈ A) /\ (Gamma ⊢ e3 ∈ B @ e2).
  intro Ht; remember (smk e1 e2 e3) as sae; induction Ht; inversion Heqsae; subst; [repeat eexists; eauto| |];
  destruct (IHHt eq_refl) as [A Hb]; destruct Hb as [B Hab]; destruct Hab as [Ht1 He]; destruct He as [Heb He3];
  assert (Ht3: exists t3, t2 ===> t3 /\ sigma A B ===> t3) by (eapply step_confluent; [|eassumption]; eauto);
  destruct Ht3 as [t3 Ht3]; destruct Ht3 as [H23 Hsg];
  extend (eval_sg_sg Hsg); destr_logic; subst;
  (repeat eexists;
   [eassumption || eauto
   |eapply rtc_rtc; eauto
   |erewrite <- typ_conv; eauto
   |erewrite <- typ_conv; [eassumption|apply app_rtc_cong]; eauto]).
Qed.

(* Lemma preservation : forall e1 e2, e1 ~> e2 -> forall Gamma t, Gamma ⊢ e1 ∈ t -> Gamma ⊢ e2 ∈ t. *)

Hint Resolve ty_var_confl ty_typ_confl.
Hint Resolve ty_top_confl ty_bot_confl ty_bool_confl.
Hint Resolve ty_true_confl ty_false_confl ty_unit_confl.

Lemma ty_app_confl Gamma f x T : Gamma ⊢ f @ x ∈ T -> exists A B T', (Gamma ⊢ f ∈ pi A B) /\ (Gamma ⊢ x ∈ A) /\ B |> x // 0 ===> T' /\ T ===> T'.
  intro Ht; remember (f @ x) as fx; induction Ht; inversion Heqfx; subst; [repeat eexists; eauto| |];
  destruct (IHHt eq_refl) as [A Hb]; destruct Hb as [B Ht']; destruct Ht' as [T' Ht'];
  destr_logic; clear_funs;
  assert (Ht3: exists t3, t2 ===> t3 /\ B |> x // 0 ===> t3)
    by (assert (Ht2: exists t3', T' ===> t3' /\ t2 ===> t3') by (apply step_confluent with (e1 := t1); eauto);
        destr_logic; eexists; split; [|eapply rtc_rtc]; eauto);
  destr_logic; repeat eexists; repeat split; try eassumption; eauto.
Qed.

Lemma ty_srec_confl Gamma C s p T : 
  Gamma ⊢ srec C s p ∈ T -> exists T', C @ p ===> T' /\ T ===> T'.
  intro Ht; remember (srec C s p) as fx; induction Ht; inversion Heqfx; subst; [repeat eexists; eauto| |];
  destruct (IHHt eq_refl) as [T' Ht']; 
  destr_logic; clear_funs;
  assert (Ht3: exists t3, t2 ===> t3 /\ C @ p ===> t3)
    by (assert (Ht2: exists t3', T' ===> t3' /\ t2 ===> t3') by (apply step_confluent with (e1 := t1); eauto);
        destr_logic; eexists; split; [|eapply rtc_rtc]; eauto);
  destr_logic; repeat eexists; try eassumption; eauto.
Qed.

Lemma ty_wrec_confl Gamma C s w T :
  Gamma ⊢ wrec C s w ∈ T -> exists T', C @ w ===> T' /\ T ===> T'.
  intro Ht; remember (wrec C s w) as fx; induction Ht; inversion Heqfx; subst; [repeat eexists; eauto| |];
  destruct (IHHt eq_refl) as [T' Ht']; destr_logic; clear_funs;
  assert (Ht3: exists t3, t2 ===> t3 /\ C @ w ===> t3)
    by (assert (Ht2: exists t3', T' ===> t3' /\ t2 ===> t3') by (apply step_confluent with (e1 := t1); eauto);
        destr_logic; eexists; split; [|eapply rtc_rtc]; eauto);
  destr_logic; repeat eexists; try eassumption; eauto.
Qed.

Lemma ty_brec_confl Gamma C t f b T : Gamma ⊢ brec C t f b ∈ T -> exists T', C @ b ===> T' /\ T ===> T'.
  intro Ht; remember (brec C t f b) as fx; induction Ht; inversion Heqfx; subst; [repeat eexists; eauto| |];
  destruct (IHHt eq_refl) as [T' Ht']; destr_logic; eauto.
  assert (Ht3: exists t3, t2 ===> t3 /\ C @ b ===> t3)
    by (assert (HT2: exists T'', T' ===> T'' /\ t2 ===> T'') by (apply step_confluent with (e1 := t1); eauto);
        destr_logic; eexists; split; [|eapply rtc_rtc]; eauto).
  destr_logic; eauto.
Qed.

Lemma ty_urec_confl Gamma C u t T : Gamma ⊢ urec C u t ∈ T -> exists T', C @ t ===> T' /\ T ===> T'.
  intro Ht; remember (urec C u t) as fx; induction Ht; inversion Heqfx; subst; [repeat eexists; eauto| |];
  destruct (IHHt eq_refl) as [T' Ht']; destr_logic; eauto.
  assert (Ht3: exists t3, t2 ===> t3 /\ C @ t ===> t3)
    by (assert (HT2: exists T'', T' ===> T'' /\ t2 ===> T'') by (apply step_confluent with (e1 := t1); eauto);
        destr_logic; eexists; split; [|eapply rtc_rtc]; eauto).
  destr_logic; eauto.
Qed.

Lemma ty_exf_confl Gamma C f T : Gamma ⊢ exf C f ∈ T -> exists T', C @ f ===> T' /\ T ===> T'.
  intro Ht; remember (exf C f) as fx; induction Ht; inversion Heqfx; subst; [repeat eexists; eauto| |];
  destruct (IHHt eq_refl) as [T' Ht']; destr_logic; eauto.
  assert (Ht3: exists t3, t2 ===> t3 /\ C @ f ===> t3)
    by (assert (HT2: exists T'', T' ===> T'' /\ t2 ===> T'') by (apply step_confluent with (e1 := t1); eauto);
        destr_logic; eexists; split; [|eapply rtc_rtc]; eauto).
  destr_logic; eauto.
Qed.

Lemma typ_confluent : forall Gamma e t1, Gamma ⊢ e ∈ t1 -> forall t2, Gamma ⊢ e ∈ t2 -> exists t3, t1 ===> t3 /\ t2 ===> t3.
  induction 1; intros t' Ht'; eauto.
  - apply ty_var_confl in Ht'; destr_logic; unfold lookup_wk; erewrite lookup_irrel; eauto.
  - apply ty_pi_confl in Ht'; destr_logic; try_hyps; destr_logic; clear_funs;
    repeat match goal with [H: pi _ _ ===> _|-_] => extend (eval_pi_pi H) end; destr_logic; subst;
    repeat match goal with [H: typ _ ===> _|-_] => inversion H as [|y z H']; clear H; [subst|inversion H'] end;
    repeat match goal with [H: ?e1 = ?e2 |- _] => tryif (atomic e1; atomic e2) then fail else inversion H; subst; clear H end;
    eauto.
  - apply ty_sg_confl in Ht'; destr_logic; try_hyps; destr_logic; clear_funs;
    repeat match goal with [H: pi _ _ ===> _|-_] => extend (eval_pi_pi H) end; destr_logic; subst;
    repeat match goal with [H: typ _ ===> _|-_] => inversion H as [|y z H']; clear H; [subst|inversion H'] end;
    repeat match goal with [H: ?e1 = ?e2 |- _] => tryif (atomic e1; atomic e2) then fail else inversion H; subst; clear H end;
    eauto.
  - apply ty_wt_confl in Ht'; destr_logic; try_hyps; destr_logic; clear_funs;
    repeat match goal with [H: pi _ _ ===> _|-_] => extend (eval_pi_pi H) end; destr_logic; subst;
    repeat match goal with [H: typ _ ===> _|-_] => inversion H as [|y z H']; clear H; [subst|inversion H'] end;
    repeat match goal with [H: ?e1 = ?e2 |- _] => tryif (atomic e1; atomic e2) then fail else inversion H; subst; clear H end;
    eauto.
  - destruct (ty_lam_confl Ht') as [A' Hb]; destruct Hb as [B' Hab']; destruct Hab' as [Ha' Hb']; destruct Hb' as [Hb' Haa'].
    erewrite <- con_cons_cong in Hb'; [|eassumption].
    destruct (IHhas_type2 _ Hb') as [B'' Hbb]; destruct Hbb as [Hbb'' Hb'b''].
    eexists; split; [eapply pi_rtc_cong|eapply rtc_rtc]; eauto.
  - destruct (ty_app_confl Ht'); destr_logic.
    extend (IHhas_type1 _ H1). extend (IHhas_type2 _ H2).
    destr_logic.
    repeat match goal with [H: pi _ _ ===> _|-_] => extend (eval_pi_pi H) end; destr_logic; subst;
    repeat match goal with [H: ?e1 = ?e2 |- _] => tryif (atomic e1; atomic e2) then fail else inversion H; subst; clear H end.
    assert (Hx': exists x', x5 |> a // 0 ===> x' /\ x1 ===> x')
      by (apply step_confluent with (e1 := x0 |> a // 0); [apply subst_step_cong|]; assumption || auto).
    destruct Hx' as [x' Hx']; destr_logic; exists x'; split; eapply rtc_rtc; try eapply subst_step_cong; eauto.
  - destruct (ty_smk_confl Ht'); destr_logic. try_hyps; destr_logic; clear_funs.
    exists (sigma x3 x0); split; [|eapply rtc_rtc]; eauto.
  - eapply ty_srec_confl; eassumption.
  - destruct (ty_sup_confl Ht'); destr_logic. try_hyps; destr_logic; clear_funs.
    exists (wt x4 x0); split; [|eapply rtc_rtc]; eauto.
  - eapply ty_wrec_confl; eassumption.
  - eapply ty_brec_confl; eassumption.
  - eapply ty_urec_confl; eassumption.
  - eapply ty_exf_confl; eassumption.
  - apply IHhas_type in Ht'; destr_logic.
    assert (H3:exists t'', x ===> t'' /\ t2 ===> t'') by (eapply step_confluent; [eapply H1|eauto]).
    destruct H3 as [t'' H3]; exists t''; destr_logic; split; [|eapply rtc_rtc]; eauto.
  - apply IHhas_type in Ht'; destr_logic; eauto.
Qed.
