(* imports *)
Require Import Omega Coq.Program.Program Coq.Program.Tactics.
Require Import Unscoped Scoping Evaluation DeBrujin.

(* notations *)
Open Scope list_scope.
Infix "==" := (exp_eq_dec) (at level 50).
Notation "⟦ xs ⟧" := (length xs).

(* Program things *)
Set Shrink Obligations.
Unset Transparent Obligations.
Set Hide Obligations.
Obligation Tactic := program_simpl; simpl in *; try omega.

Set Implicit Arguments.

Fixpoint lookup_con {A} (Gamma: list A) (i : nat) : option A :=
  match Gamma , i with
    | nil , _ => None
    | (X :: Gamma) , 0 => Some X
    | (X :: Gamma) , S n => match lookup_con Gamma n with
                         | Some T => Some T
                         | None => None
                       end
  end.

Lemma lookup_iff_ge {A} : forall Gamma i, @lookup_con A Gamma i = None <-> ⟦Gamma⟧ <= i.
  induction Gamma; destruct i; simpl; split; intros; eauto; try omega.
  - inversion H.
  - specialize (IHGamma i). destruct (lookup_con Gamma i); [inversion H|apply IHGamma in H]; omega.
  - specialize (IHGamma i). assert(H': length Gamma <= i) by omega. apply IHGamma in H'. rewrite H'. auto.
Qed.

Lemma lookup_iff_lt {A} : forall Gamma i, i < ⟦Gamma⟧ <-> exists a : A, lookup_con Gamma i = Some a.
  split.
  - remember (lookup_con Gamma i) as lgi; destruct lgi; [eauto|].
    assert (⟦Gamma⟧ <= i) by (apply lookup_iff_ge; auto); omega.
  - destruct (le_lt_dec ⟦Gamma⟧ i) as [Hle|Hlt]; [apply lookup_iff_ge in Hle|auto]; destruct 1; congruence.
Qed.

Program Fixpoint lookup_lt {A} (Gamma : list A) (i : {x | x < length Gamma}) : A :=
  match Gamma , i with
    | nil , _ => False_rect _ _
    | (x :: xs) , 0   => x
    | (x :: xs) , S n => lookup_lt xs n
  end.

Lemma lookup_irrel A (Gamma : list A) : forall i j, `i = `j -> lookup_lt Gamma i = lookup_lt Gamma j.
  induction Gamma; destruct i as [i Hi]; destruct j as [j Hj]; simpl in *; destruct 1; 
  [exfalso; omega|destruct i]; eauto. Qed.

Hint Rewrite lookup_irrel.

Program Definition fsu {n} : {x | x < n} -> {x | x < S n} := S.

Lemma lookup_cons A Gamma i : forall a, @lookup_lt A (a :: Gamma) (fsu i) = lookup_lt Gamma i.
  destruct i as [i Hi]; simpl; intros; apply lookup_irrel; reflexivity. Qed.

Hint Rewrite lookup_cons.

Theorem lookup_scoped (Gamma : con) (Hg : scoped_con Gamma) :
  forall i (Hi : i < length Gamma), scoped_at (length Gamma - S i) (lookup_lt Gamma (exist _ i Hi)).
  Hint Rewrite <- minus_n_O.
  induction Hg; try (inversion Hi; fail); intros.
  - destruct i; simpl in *; [rewrite <- minus_n_O; auto|apply IHHg].
Qed.

Lemma lookup_lt_con A (Gamma : list A) : forall i, lookup_con Gamma (`i) = Some (lookup_lt Gamma i).
  induction Gamma; intro i; simpl in i; destruct i as [i Hi]; [omega|]; destruct i; [reflexivity|].
  assert (H: i < length Gamma) by omega; specialize (IHGamma (exist _ i H)); simpl in *; 
  rewrite IHGamma; f_equal; apply lookup_irrel; auto.
Qed.  
  
Hint Resolve lookup_scoped.

Program Definition lookup_wk (Gamma : con) (i : {x | x < length Gamma}) := wk_deep (S i) 0 (lookup_lt Gamma i).

Program Definition lookup_wk_scoped_subset (Gamma : {gamma | scoped_con gamma}) i : scoped_at (length Gamma) (lookup_wk Gamma i) :=
  wk_scoped (lookup_lt Gamma i) (length Gamma - S i) _ (S i) 0.

(* split for nicer proof terms *)
Lemma lookup_wk_scoped (Gamma : con) (p : scoped_con Gamma) : forall i, scoped_at (length Gamma) (lookup_wk Gamma i).
  apply (lookup_wk_scoped_subset (exist _ Gamma p)). Qed.

Hint Resolve lookup_wk_scoped.

Infix "▻" := (fun Gamma a => cons a Gamma) (at level 50, left associativity).
Infix "-->" := (fun a b => pi a (wk_deep 1 0 b)) (at level 20, right associativity).

Reserved Notation "Gamma ⊢ t ∈ T" (at level 85).

Inductive has_type (Gamma: con) : exp -> exp -> Prop :=
| ty_var : forall i, Gamma ⊢ & (` i) ∈ lookup_wk Gamma i

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

| ty_srec : forall A B C f s, Gamma ⊢ f ∈ pi A (pi (wk_deep 1 0 B @ &0) (C @ (smk (wk_deep 2 0 B) (&1) (&0))))
                       -> Gamma ⊢ s ∈ sigma A B
                       -> Gamma ⊢ srec C f s ∈ C @ s

| ty_sup : forall A B n a f, Gamma ⊢ B ∈ pi A (typ n)
                      -> Gamma ⊢ a ∈ A
                      -> Gamma ⊢ f ∈ ((B @ a) --> wt A B)
                      -> Gamma ⊢ sup B a f ∈ wt A B

| ty_wrec : forall C A B f w,
              Gamma ⊢ f ∈ pi A (pi (wk_deep 1 0 B @ &0 --> wk_deep 1 0 (wt A B))
                             ((pi (wk_deep 2 0 B @ &1) (wk_deep 3 0 C @ (&1 @ &0)))
                                --> wk_deep 3 0 C @ sup (wk_deep 3 0 B) (&2) (&1)))
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

Lemma wk_typed e : forall T Gamma Delta, Gamma ++ Delta ⊢ e ∈ T -> forall delta, Gamma ++ delta ++ Delta ⊢ wk_deep ⟦delta⟧ ⟦Gamma⟧ e ∈ wk_deep ⟦delta⟧ ⟦Gamma⟧ T.
(* (* yuck - we'll just admit this for now *)
  induction e; inversion 1; subst; intros.
  - rewrite wk_ix_deep. unfold wk_ix. destruct (le_dec ⟦Gamma⟧ (`i)) as [Hle|Hnle].
    + unfold lookup_wk in *. rewrite lookup_plus2 with (delta := delta) in *. unfold wk_ix_lt; unfold wk_ix; simpl.
      assert (H0: ⟦delta⟧ + `i < ⟦Gamma ++ delta ++ Delta ⟧) by (clear H; destruct i; simpl in *; repeat rewrite List.app_length in *; omega).
      erewrite lookup_irrel; [|instantiate (j := exist _ (⟦delta⟧+(`i)) H0); simpl; destr_choices; omega].
      rewrite wk_deep_wk; [|omega]. rewrite <- plus_n_Sm.
      destruct i as [i Hi]; simpl in *.
      replace (wk_deep (S (⟦ delta ⟧ + i)) 0
       (lookup_lt (Gamma ++ delta ++ Delta)
          (exist (fun x : nat => x < ⟦ Gamma ++ delta ++ Delta ⟧)
             (⟦ delta ⟧ + i) H0))) with (lookup_wk (Gamma ++ delta ++ Delta) (exist _ (⟦delta⟧+i) H0)) by auto. 
      replace (& (⟦ delta ⟧ + i)) with (& (` (exist (fun i => i < ⟦Gamma ++ delta ++ Delta⟧) (⟦delta⟧+i) H0))) by auto.
      apply ty_var.
    + *) Admitted.

Inductive wf_con : con -> Prop :=
| wf_nil : wf_con nil
| wf_cons : forall Gamma A n, wf_con Gamma -> Gamma ⊢ A ∈ (typ n) -> wf_con (Gamma ▻ A).

Hint Constructors wf_con.

Lemma typ_conv : forall Gamma e t1 t2, t1 ===> t2 -> Gamma ⊢ e ∈ t1 <-> Gamma ⊢ e ∈ t2.
    induction 1; split; intros; auto.
    - apply IHclos_refl_trans_1n; eauto.
    - eapply ty_step_from; [eassumption|]. eapply IHclos_refl_trans_1n; auto.
Qed.

Lemma ty_var_congr Gamma i T : Gamma ⊢ & (` i) ∈ T -> exists T', lookup_wk Gamma i ===> T' /\ T ===> T'.
  remember (& (` i)) as i'; induction 1; inversion Heqi'; subst.
  - unfold lookup_wk; rewrite H0; erewrite lookup_irrel; eauto.
  - destruct (IHhas_type i eq_refl) as [t1' Ht]; destruct Ht;
    assert (exists t2', t2 ===> t2' /\ t1' ===> t2') by (apply step_confluent with (e1 := t1); eauto);
    destr_logic; eexists; split; [eapply rtc_rtc|]; eassumption.
  - destruct (IHhas_type i eq_refl) as [t1' Ht]; destruct Ht; eauto.
Qed.

Lemma ty_typ_congr Gamma n T : Gamma ⊢ typ n ∈ T -> T ===> typ (S n).
  remember (typ n) as tn; induction 1; inversion Heqtn; subst; auto; specialize (IHhas_type eq_refl); eauto.
  - assert (exists t2', t2 ===> t2' /\ typ (S n) ===> t2') by (apply step_confluent with (e1 := t1); eauto).
    destruct H2 as [t2' Ht2']; destruct Ht2' as [Ht2' Htyp]; destruct Htyp as [|y z Htyp Ht']; eauto; inversion Htyp.
Qed.

Lemma ty_pi_congr Gamma A B T : Gamma ⊢ pi A B ∈ T -> exists n m, (Gamma ⊢ A ∈ typ n) /\ (Gamma ▻ A ⊢ B ∈ typ m) /\ T ===> typ (max n m).
  remember (pi A B) as pab; induction 1; inversion Heqpab; subst; eauto; 
  destruct (IHhas_type eq_refl) as [n Hn]; destruct Hn as [m Hnm]; destruct Hnm as [Ha Hbt]; destruct Hbt as [Hb Ht];
  exists n; exists m; repeat split; eauto.
  - assert (exists t2', t2 ===> t2' /\ typ (max n m) ===> t2') by (apply step_confluent with (e1 := t1); eauto).
    destruct H2 as [t2' Ht2']; destruct Ht2' as [Ht2' Htyp]; destruct Htyp as [|y z Htyp Ht']; eauto; inversion Htyp.
Qed.

Lemma ty_sg_congr Gamma A B T : Gamma ⊢ sigma A B ∈ T -> exists n m, (Gamma ⊢ A ∈ typ n) /\ (Gamma ⊢ B ∈ pi A (typ m)) /\ T ===> typ (max n m).
  remember (sigma A B) as pab; induction 1; inversion Heqpab; subst; eauto; 
  destruct (IHhas_type eq_refl) as [n Hn]; destruct Hn as [m Hnm]; destruct Hnm as [Ha Hbt]; destruct Hbt as [Hb Ht];
  exists n; exists m; repeat split; eauto.
  - assert (exists t2', t2 ===> t2' /\ typ (max n m) ===> t2') by (apply step_confluent with (e1 := t1); eauto).
    destruct H2 as [t2' Ht2']; destruct Ht2' as [Ht2' Htyp]; destruct Htyp as [|y z Htyp Ht']; eauto; inversion Htyp.
Qed.

Lemma ty_wt_congr Gamma A B T : Gamma ⊢ wt A B ∈ T -> exists n m, (Gamma ⊢ A ∈ typ n) /\ (Gamma ⊢ B ∈ pi A (typ m)) /\ T ===> typ (max n m).
  remember (wt A B) as pab; induction 1; inversion Heqpab; subst; eauto; 
  destruct (IHhas_type eq_refl) as [n Hn]; destruct Hn as [m Hnm]; destruct Hnm as [Ha Hbt]; destruct Hbt as [Hb Ht];
  exists n; exists m; repeat split; eauto.
  - assert (exists t2', t2 ===> t2' /\ typ (max n m) ===> t2') by (apply step_confluent with (e1 := t1); eauto).
    destruct H2 as [t2' Ht2']; destruct Ht2' as [Ht2' Htyp]; destruct Htyp as [|y z Htyp Ht']; eauto; inversion Htyp.
Qed.

Lemma ty_bool_congr Gamma T : Gamma ⊢ bool ∈ T -> T ===> typ 0.
  remember bool as b; induction 1; inversion Heqb; subst; eauto; specialize (IHhas_type eq_refl).
  - assert (exists t2', t2 ===> t2' /\ typ 0 ===> t2') by (apply step_confluent with (e1 := t1); eauto).
    destruct H2 as [t2' Ht2']; destruct Ht2' as [Ht2' Htyp]; destruct Htyp as [|y z Htyp Ht']; eauto; inversion Htyp.
Qed.  

Lemma ty_top_congr Gamma T : Gamma ⊢ top ∈ T -> T ===> typ 0.
  remember top as b; induction 1; inversion Heqb; subst; eauto; specialize (IHhas_type eq_refl).
  - assert (exists t2', t2 ===> t2' /\ typ 0 ===> t2') by (apply step_confluent with (e1 := t1); eauto).
    destruct H2 as [t2' Ht2']; destruct Ht2' as [Ht2' Htyp]; destruct Htyp as [|y z Htyp Ht']; eauto; inversion Htyp.
Qed.  

Lemma ty_bot_congr Gamma T : Gamma ⊢ bot ∈ T -> T ===> typ 0.
  remember bot as b; induction 1; inversion Heqb; subst; eauto; specialize (IHhas_type eq_refl).
  - assert (exists t2', t2 ===> t2' /\ typ 0 ===> t2') by (apply step_confluent with (e1 := t1); eauto).
    destruct H2 as [t2' Ht2']; destruct Ht2' as [Ht2' Htyp]; destruct Htyp as [|y z Htyp Ht']; eauto; inversion Htyp.
Qed.

Lemma ty_true_congr Gamma T : Gamma ⊢ true ∈ T -> T ===> bool.
  remember true as b; induction 1; inversion Heqb; subst; eauto; specialize (IHhas_type eq_refl).
  - assert (exists t2', t2 ===> t2' /\ bool ===> t2') by (apply step_confluent with (e1 := t1); eauto).
    destruct H2 as [t2' Ht2']; destruct Ht2' as [Ht2' Htyp]; destruct Htyp as [|y z Htyp Ht']; eauto; inversion Htyp.
Qed.

Lemma ty_false_congr Gamma T : Gamma ⊢ false ∈ T -> T ===> bool.
  remember false as b; induction 1; inversion Heqb; subst; eauto; specialize (IHhas_type eq_refl).
  - assert (exists t2', t2 ===> t2' /\ bool ===> t2') by (apply step_confluent with (e1 := t1); eauto).
    destruct H2 as [t2' Ht2']; destruct Ht2' as [Ht2' Htyp]; destruct Htyp as [|y z Htyp Ht']; eauto; inversion Htyp.
Qed.

Lemma ty_unit_congr Gamma T : Gamma ⊢ unit ∈ T -> T ===> top.
  remember unit as b; induction 1; inversion Heqb; subst; eauto; specialize (IHhas_type eq_refl).
  - assert (exists t2', t2 ===> t2' /\ top ===> t2') by (apply step_confluent with (e1 := t1); eauto).
    destruct H2 as [t2' Ht2']; destruct Ht2' as [Ht2' Htyp]; destruct Htyp as [|y z Htyp Ht']; eauto; inversion Htyp.
Qed.

Lemma wk_step_congr e1 e2 n d : e1 ==> e2 -> wk_deep n d e1 ===> wk_deep n d e2. auto. Qed.
Lemma wk_eval_congr e1 e2 n d : e1 ===> e2 -> wk_deep n d e1 ===> wk_deep n d e2. 
  induction 1; eauto; eapply rtc_rtc; [eapply wk_step_congr|]; eassumption. Qed.

Hint Resolve wk_eval_congr.

Lemma con_var_congr Gamma T i t1 t2 (Ht : t1 ===> t2) : t1 :: Gamma ⊢ &i ∈ T <-> t2 :: Gamma ⊢ &i ∈ T.
  remember (&i) as ix; split; intro Hi.
  - generalize dependent t2. remember (t1 :: Gamma) as gamma. induction Hi; inversion Heqgamma; inversion Heqix; subst; intros.
    + destruct i0 as [i Hi]; simpl in *.
      destruct i; unfold lookup_wk; simpl.
      * eapply typ_conv; [eapply wk_eval_congr;eassumption|].
        replace (&0) with (&(` (exist (fun n => n < S (length Gamma)) 0 Hi))) by auto;
        replace (wk_deep 1 0 t2) with (lookup_wk (t2 :: Gamma) (exist _ 0 Hi)) by auto;
        constructor.
      * replace (&(S i)) with (& (` (exist (fun n => n < ⟦t2 :: Gamma⟧) (S i) Hi))) by auto.
        rewrite <- lookup_cons with (a := t2). unfold fsu. erewrite lookup_irrel. apply ty_var. auto.
    + specialize (IHHi eq_refl eq_refl).
Admitted.

Lemma con_cons_congr1 e : forall t1 t2, t1 ===> t2 -> forall Gamma T, (t1 :: Gamma) ⊢ e ∈ T <-> (t2 :: Gamma) ⊢ e ∈ T.
  induction e; intros; eauto.
  - split; inversion 1; subst; auto.
    + destruct i as [i Hi]; induction i.
Admitted.

Hint Resolve con_cons_congr1.
Hint Rewrite con_cons_congr1.

Lemma ty_lam_congr Gamma e1 e2 T : Gamma ⊢ lam e1 e2 ∈ T -> exists A B, T ===> pi A B /\ (Gamma ▻ A ⊢ e2 ∈ B) /\ e1 ===> A.
  intro Ht; remember (lam e1 e2) as lae; induction Ht; inversion Heqlae; subst; [repeat eexists;eauto| |];
  destruct (IHHt eq_refl) as [A Hb]; destruct Hb as [B Hab]; destruct Hab as [He2 Het];
  destruct Het as [He1 HT]; clear IHHt;
  assert (Ht3: exists t3, t2 ===> t3 /\ pi A B ===> t3) by (eapply step_confluent; [|eassumption]; eauto);
  destruct Ht3 as [t3 Ht3]; destruct Ht3 as [H23 Hpi]; destr_logic; [|repeat eexists; eauto].
  - extend (eval_pi_pi Hpi); destr_logic; subst; destr_logic.
    repeat eexists; [eassumption| |].
    + erewrite <- con_cons_congr1; [|eassumption];erewrite <- typ_conv; eassumption.
    + eapply rtc_rtc; eassumption.
Qed.

Lemma ty_sup_congr Gamma e1 e2 e3 T : 
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

Lemma ty_smk_congr Gamma e1 e2 e3 T : 
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

Hint Resolve ty_var_congr ty_typ_congr.
Hint Resolve ty_pi_congr ty_sg_congr ty_wt_congr.
Hint Resolve ty_lam_congr ty_sup_congr ty_smk_congr.
Hint Resolve ty_top_congr ty_bot_congr ty_bool_congr.
Hint Resolve ty_true_congr ty_false_congr ty_unit_congr.

Lemma typ_confluent : forall Gamma e t1, Gamma ⊢ e ∈ t1 -> forall t2, Gamma ⊢ e ∈ t2 -> exists t3, t1 ===> t3 /\ t2 ===> t3.
  induction 1; intros t' Ht'; eauto.
  - apply ty_pi_congr in Ht'; destr_logic; try_hyps; destr_logic; clear_funs;
    repeat match goal with [H: pi _ _ ===> _|-_] => extend (eval_pi_pi H) end; destr_logic; subst;
    repeat match goal with [H: typ _ ===> _|-_] => inversion H as [|y z H']; clear H; [subst|inversion H'] end;
    repeat match goal with [H: ?e1 = ?e2 |- _] => tryif (atomic e1; atomic e2) then fail else inversion H; subst; clear H end;
    eauto.
  - apply ty_sg_congr in Ht'; destr_logic; try_hyps; destr_logic; clear_funs;
    repeat match goal with [H: pi _ _ ===> _|-_] => extend (eval_pi_pi H) end; destr_logic; subst;
    repeat match goal with [H: typ _ ===> _|-_] => inversion H as [|y z H']; clear H; [subst|inversion H'] end;
    repeat match goal with [H: ?e1 = ?e2 |- _] => tryif (atomic e1; atomic e2) then fail else inversion H; subst; clear H end;
    eauto.
  - apply ty_wt_congr in Ht'; destr_logic; try_hyps; destr_logic; clear_funs;
    repeat match goal with [H: pi _ _ ===> _|-_] => extend (eval_pi_pi H) end; destr_logic; subst;
    repeat match goal with [H: typ _ ===> _|-_] => inversion H as [|y z H']; clear H; [subst|inversion H'] end;
    repeat match goal with [H: ?e1 = ?e2 |- _] => tryif (atomic e1; atomic e2) then fail else inversion H; subst; clear H end;
    eauto.
  - apply ty_lam_congr in Ht'. shelve (* doesn't quite work - needs the correct context shift *).
  (* not dealing with more cases for now *)
Admitted.

Theorem preservation : forall Gamma e1 e2 T, e1 ===> e2 -> Gamma ⊢ e1 ∈ T <-> Gamma ⊢ e2 ∈ T.
Admitted.

(* this induction principle won't quite work - should be a fixpoint, but not yet sure what the measure should be *)
(* => would be wrong since there are nonterminating (but untyped) programs... hmmm... *)

Theorem ty_normal : forall Gamma e T, Gamma ⊢ e ∈ T -> exists e', e ===> e' /\ is_normal e'.
  induction 1; auto; try (eexists; split; eauto; inversion 1; fail).
  - destr_logic; exists (pi x0 x); split; [apply pi_rtc_cong|inversion 1; subst]; unfold is_normal in *; try_hyps; eauto.
  - destr_logic; exists (sigma x0 x); split; [apply sg_rtc_cong|inversion 1; subst]; unfold is_normal in *; try_hyps; eauto.
  - destr_logic; exists (wt x0 x); split; [apply wt_rtc_cong|inversion 1; subst]; unfold is_normal in *; try_hyps; eauto.
  - destr_logic; exists (lam x0 x); split; [apply lam_rtc_cong|inversion 1; subst]; unfold is_normal in *; try_hyps; eauto.
Admitted.

Theorem ty_check : forall Gamma e, {T | Gamma ⊢ e ∈ T} + {forall T, ~ (Gamma ⊢ e ∈ T)}.
Admitted.