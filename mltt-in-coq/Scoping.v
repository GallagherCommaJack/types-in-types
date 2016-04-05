Require Export Unscoped Evaluation Typing.

(* Scoping relation and DeBrujin lemmas live here *)
Inductive scoped_at (n : nat) : exp -> Prop :=
| scope_var : forall i, i < n -> scoped_at n (& i)

| scope_typ : forall m, scoped_at n (typ m)

| scope_pi : forall a b, scoped_at n a -> scoped_at (S n) b -> scoped_at n (pi a b)
| scope_lam : forall A b, scoped_at n A -> scoped_at (S n) b -> scoped_at n (lam A b)
| scope_app : forall f x, scoped_at n f -> scoped_at n x -> scoped_at n (f @ x)

| scope_sigma : forall a b, scoped_at n a -> scoped_at n b -> scoped_at n (sigma a b)
| scope_smk : forall B a b, scoped_at n B -> scoped_at n a -> scoped_at n b -> scoped_at n (smk B a b)
| scope_srec : forall c p s, scoped_at n c -> scoped_at n p -> scoped_at n s -> scoped_at n (srec c p s)

| scope_wt : forall a b, scoped_at n a -> scoped_at n b -> scoped_at n (wt a b)
| scope_sup : forall B a f, scoped_at n B -> scoped_at n a -> scoped_at n f -> scoped_at n (sup B a f)
| scope_wrec : forall c s w, scoped_at n c -> scoped_at n s -> scoped_at n w -> scoped_at n (wrec c s w)

| scope_bool : scoped_at n bool
| scope_true : scoped_at n true
| scope_false : scoped_at n false
| scope_brec : forall c t f b, scoped_at n c -> scoped_at n t -> scoped_at n f -> scoped_at n b -> scoped_at n (brec c t f b)

| scope_top : scoped_at n top
| scope_unit : scoped_at n unit
| scope_urec : forall c u t, scoped_at n c -> scoped_at n u -> scoped_at n t -> scoped_at n (urec c u t)

| scope_bot : scoped_at n bot
| scope_exf : forall c f, scoped_at n c -> scoped_at n f -> scoped_at n (exf c f).

Hint Resolve lt_dec.

Hint Constructors scoped_at.
Hint Constructors sumbool.

Definition scope_check_at (n : nat) (e : exp) : {scoped_at n e} + {~ scoped_at n e}.
  (* Local Hint Extern 5 => match goal with [H : scoped_at _ _ |- _] => inversion H end. *)
  generalize dependent n; induction e; intro n;
  try (destruct (lt_dec ix n); [left|right]; auto; inversion 1; auto);
  Inster_all; destr_hyps; try (left; constructor; eassumption); right; inversion 1; subst; auto.
Defined.

Fixpoint count_free (e : exp) : nat :=
  match e with
    | & i => S i

    | pi a b => max (count_free a) (pred (count_free b))
    | lam A b => max (count_free A) (pred (count_free b))
    | (f @ x) => max (count_free f) (count_free x)

    | sigma a b => max (count_free a) (count_free b)
    | (smk B a b) => max (max (count_free B) (count_free a)) (count_free b)
    | srec c p s => max (max (count_free c) (count_free p)) (count_free s)

    | wt a b => max (count_free a) (count_free b)
    | sup B a f => max (max (count_free B) (count_free a)) (count_free f)
    | wrec c s w => max (max (count_free c) (count_free s)) (count_free w)

    | brec c t f b => max (max (max (count_free c) (count_free t)) (count_free f)) (count_free b)
    | urec c u t => max (max (count_free c) (count_free u)) (count_free t)
    | exf c f => max (count_free c) (count_free f)
    
    | _ => 0
  end.

Lemma scoped_at_lift (e : exp) n (p : scoped_at n e) : forall m, n <= m -> scoped_at m e.
  induction p; intros; constructor; try (apply IHp || apply IHp1 || apply IHp2 || apply IHp3 || apply IHp4); omega.
Qed.

Hint Resolve scoped_at_lift.
Hint Resolve Nat.le_max_l Nat.le_max_r.

Hint Extern 1 (?n <= max ?n ?m) => apply Nat.le_max_l.

Lemma le_S_pred : forall n, n <= S (pred n). intro; omega. Qed.
Lemma S_max_pred : forall n m, S (max n m) = max (S n) (S m). induction n; induction m; auto. Qed.

Hint Rewrite S_max_pred.

Ltac SMax := repeat match goal with
                      | [ |- context[S (max _ _)] ] => rewrite S_max_pred
                    end.

Lemma max_trans_l : forall d n m, d <= n -> d <= max n m. intros; eapply le_trans; eauto. Qed.
Lemma max_trans_r : forall d n m, d <= m -> d <= max n m. intros; eapply le_trans; eauto. Qed.

Hint Resolve max_trans_l max_trans_r.
Ltac le_max :=
  match goal with
    | [|- ?d <= max ?n ?m] => (eapply max_trans_l; try le_max; omega; fail) || (eapply max_trans_r; try le_max; omega; fail)
  end.

Theorem scoped_at_count (e : exp) : scoped_at (count_free e) e.
  Local Hint Resolve le_n_S.
  Local Hint Resolve le_S_pred.
  Local Hint Extern 1 => SMax.
  induction e; intros;
  try (constructor; simpl in *; omega);
  try (constructor; simpl; SMax; (eapply scoped_at_lift; [eassumption|le_max])).
Qed.

Lemma max_le_eq_l : forall n m, n <= m -> max n m = m.
  induction n; induction m; inversion 1; subst; simpl; eauto.
  - f_equal; apply IHn; omega.
Qed.

Lemma max_le_eq_r : forall n m, n <= m -> max m n = m.
  induction n; induction m; inversion 1; subst; simpl; eauto.
  - f_equal; apply IHn; omega.
Qed.

Lemma max_refl : forall n, max n n = n. intros; apply max_le_eq_l; eauto. Qed.

Hint Rewrite max_le_eq_l max_le_eq_r max_refl.
Local Hint Resolve max_le_eq_l max_le_eq_r max_refl.

Lemma max_left_right : forall n m, (max n m = n) \/ (max n m = m).
  intros; destruct (lt_eq_lt_dec n m) as [Hle|Hgt]; [destruct Hle as [Hlt|Heq]|]; subst;
  [right;apply max_le_eq_l|right;apply max_refl|left;apply max_le_eq_r]; omega. Qed.

Lemma max_le_trans : forall n m d, n <= d -> m <= d -> max n m <= d.
  intros; destruct (max_left_right n m) as [Hn|Hm]; [rewrite Hn|rewrite Hm]; eauto. Qed.

Local Hint Resolve max_le_trans.

(* well, at least this was easy *)
Theorem count_free_least (e : exp) : forall n, scoped_at n e -> count_free e <= n.
  induction 1; simpl in *; repeat apply max_le_trans; omega. Qed.

(* Weaking and Subst lemmas *)
Theorem wk_scoped (e : exp) n (p : scoped_at n e) : forall m d, scoped_at (m + n) (wk_deep m d e).
  induction p; intros; unfold wk_deep in *; simpl; try constructor; simpl; repeat rewrite plus_n_Sm; auto.
  - unfold wk_var; simpl; destruct (le_dec d i); constructor; omega.
Qed.

Hint Resolve wk_scoped.

Lemma wk_0_scoped e m n (p : scoped_at n e) : scoped_at (m + n) (wk_deep m 0 e). auto. Qed.
Lemma wk_1_scoped e n (p : scoped_at n e) : scoped_at (S n) (wk_deep 1 0 e). replace (S n) with (1 + n) by auto; auto. Qed.

Lemma subst_scoped_pred (e : exp) n (p : scoped_at n e) :
  forall d v, d < n -> scoped_at (n - S d) v -> scoped_at (pred n) (e |> v // d).
  induction p; intros d v Hd Hv; (destruct n; simpl in *; [exfalso;omega|]);
  try constructor;
  (* try applying all the IH's *)
  try (apply IHp; [omega|auto]); try (apply IHp1; [omega|auto]);
  try (apply IHp2; [omega|auto]); try (apply IHp3; [omega|auto]); try (apply IHp4; [omega|auto]).
  (* vars, the always special case *)
  - unfold subst_deep; unfold subst_var; simpl; destruct (lt_eq_lt_dec i d) as [Hle|Hgt]; [destruct Hle as [Hlt|_]|];
    [constructor|replace n with (d + (n - d)) by omega; apply wk_scoped|constructor]; [omega|auto|omega].
Qed.

Theorem subst_scoped (e : exp) n (p : scoped_at (S n) e) :
  forall d v, d <= n -> scoped_at (n - d) v -> scoped_at n (e |> v // d).
  replace n with (pred (S n)) by omega; intros; apply subst_scoped_pred; auto. Qed.

Hint Resolve subst_scoped.

Theorem subst_0_scoped (e : exp) n (p : scoped_at (S n) e) v : scoped_at n v -> scoped_at n (e |> v // 0).
  intro H. replace n with (n - 0) in H by omega. apply subst_scoped; auto; omega. Qed.

Definition con := list exp.
Open Scope list_scope.

Inductive scoped_con : con -> Prop :=
| scope_nil : scoped_con nil
| scope_cons : forall Gamma X, scoped_con Gamma -> scoped_at (length Gamma) X -> scoped_con (X :: Gamma).

Hint Constructors scoped_con.

Lemma unwk_scoped : forall e n m d, d <= m -> scoped_at (n + m) (wk_deep n d e) -> scoped_at m e.
  induction e; intros n m d Hd He; simpl in *; try (
  (* dispatch trivial cases *)
  try (repeat constructor; auto; fail);
  (* var case takes some special handling *)
  try (unfold wk_deep in *; unfold wk_var in *; simpl in *; destruct (le_dec d ix));
  (* invert and split obligations *)
  inversion He; subst; constructor; simpl in *; repeat rewrite plus_n_Sm in *;
  (* try all the IH's *)
  try eapply (IHe1 n); try eapply (IHe2 n); try eapply (IHe3 n); try eapply (IHe4 n);
  (* finish the job *)
  try eassumption; omega).
Qed.

Hint Resolve unwk_scoped.

Lemma unsubst_scoped : forall e v d n, d <= n -> scoped_at n (e |> v // d) -> scoped_at (S n) e.
  induction e; unfold subst_deep; simpl; intros v d n Hd He; fold_ops; auto;
  try (inversion He; subst; constructor; eauto; fail).
  - constructor; unfold_ops; destruct (lt_eq_lt_dec ix d) as [Hle|Hgt]; [destruct Hle|]; inversion He; omega.
Qed.

Lemma unsubst_0_scoped : forall e v n, scoped_at n (e |> v // 0) -> scoped_at (S n) e.
  intros e v n He; apply unsubst_scoped in He; try rewrite <- minus_n_O; try assumption; omega. Qed.

Lemma wk_above_scope : forall e n1 n2 d, n1 <= d -> scoped_at n1 e -> wk_deep n2 d e = e.
  intros e n1 n2 d Hd He; generalize dependent n2; generalize dependent d; induction He;
  unfold wk_deep; simpl; try reflexivity; intros; fold_ops; f_equal; auto; try omega.
  - unfold_ops; simpl; destr_choices; f_equal; omega.
Qed.

Lemma subst_above_scope : forall e n v d, n <= d -> scoped_at n e -> e |> v // d = e.
  intros e n1 n2 d Hd He; generalize dependent n2; generalize dependent d; induction He;
  unfold subst_deep; simpl; try reflexivity; intros; fold_ops; f_equal; auto; try omega.
  - unfold_ops; simpl; destr_choices; f_equal; omega.
Qed.

(* Evaluation preserves scope *)
Ltac invert_atom_scopes :=
  match goal with [H: scoped_at _ ?e |- _] => tryif atomic e then fail else (inversion H; subst; clear H) end.

Lemma step_scoped : forall e1 e2, e1 ==> e2 -> forall n, scoped_at n e1 -> scoped_at n e2.
  induction 1; auto; intros; repeat invert_atom_scopes; try_hyps; repeat (constructor;(omega || auto));
  try apply subst_0_scoped; try apply wk_1_scoped; assumption.
Qed.

Hint Resolve step_scoped.

Lemma scoped_S : forall e n, scoped_at n e -> scoped_at (S n) e.
  induction 1; auto. Qed.

Hint Resolve scoped_S.

Theorem eval_scoped : forall e1 e2, e1 ===> e2 -> forall n, scoped_at n e1 -> scoped_at n e2.
  induction 1; auto; intros n Hn.
  - apply IHclos_refl_trans_1n; eauto.
Qed.

Hint Resolve eval_scoped.

Theorem lookup_scoped (Gamma : con) (Hg : scoped_con Gamma) :
  forall i (Hi : i < length Gamma), scoped_at (length Gamma - S i) (lookup_lt Gamma (exist _ i Hi)).
  Hint Rewrite <- minus_n_O.
  induction Hg; try (inversion Hi; fail); intros.
  - destruct i; simpl in *; [rewrite <- minus_n_O; auto|apply IHHg].
Qed.

(* can't believe this is necessary... *)
Lemma scope_eq : forall n m, n = m -> forall e, scoped_at n e <-> scoped_at m e. induction 1; split; eauto. Qed.

Theorem typed_implies_scoped : forall Gamma t T, scoped_con Gamma -> Gamma ⊢ t ∈ T -> scoped_at (length Gamma) T /\ scoped_at (length Gamma) t.
Proof with try eassumption.
  intros Gamma t T Hg.
  induction 1; auto; simpl in *; try (repeat constructor; auto; fail);
  try (destruct (IHhas_type Hg) as [IH1 IH2]);
  try (destruct (IHhas_type1 Hg) as [IH11 IH12]); try (destruct (IHhas_type2 Hg) as [IH21 IH22]);
  try (destruct (IHhas_type3 Hg) as [IH31 IH32]); try (destruct (IHhas_type4 Hg) as [IH41 IH42]);
  try (destruct (IHhas_type2 (scope_cons _ _ Hg IH12)) as [IH21 IH22]);
  try (split; repeat constructor; auto; omega).
  - split; [|constructor;omega]. unfold lookup_wk. simpl.
    assert (H: ⟦ Gamma ⟧ = S i + (⟦ Gamma ⟧ - S i)) by omega.
    extend wk_0_scoped; extend lookup_scoped; eapply scope_eq; eauto.
  (* app is weird *)
  - split; try (constructor; auto).
    + unfold lookup_wk; inversion IH11; subst; apply subst_0_scoped...
  - inversion IH21; subst; split; constructor; auto.
  (* recursion principles will take special handling *)
  - inversion IH21; subst. inversion IH11; subst. inversion H6; subst. inversion H8; subst.
    split; constructor; auto; apply unwk_scoped with (n := 2) (d := 0); auto; omega.
  - inversion IH11; subst. inversion H4; subst. inversion H6; subst. inversion H8; subst.
    split; constructor; auto; eapply unwk_scoped with (n := 3) (d := 0); eauto; omega.
  - inversion IH11; subst; split; constructor; auto.
  - inversion IH11; subst; split; constructor; auto.
  - split; auto. eapply step_scoped; eauto.
  - split; auto. (* Ack! this is no longer true *)
Admitted.

Theorem wf_implies_scoped : forall Gamma, wf_con Gamma -> scoped_con Gamma.
  induction 1; constructor; try eapply typed_implies_scoped; eassumption. Qed.

