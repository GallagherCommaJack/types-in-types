Require Export Arith.

Inductive exp : Set :=
| var : forall(ix : nat), exp
| typ : forall(level : nat), exp

| pi : forall(A B : exp), exp
| lam : forall(A b : exp), exp
| app : forall(f x : exp), exp

| sigma : forall(A B : exp), exp
| smk : forall(a b : exp), exp
| srec : forall(C p s : exp), exp

| wt : forall(A B : exp), exp
| sup : forall(a f : exp), exp
| wrec : forall(C s w : exp), exp

| bool : exp
| true : exp
| false : exp
| brc : forall(C t f b : exp), exp

| top : exp
| unit : exp
| urec : forall(C u t : exp), exp

| bot : exp
| exf : forall(C f : exp), exp.

Hint Resolve Nat.eq_dec.

Definition exp_size (e : exp) : nat.
  induction e;
  repeat match goal with
           | [IH : nat |- _] => apply (fun x => x + IH); clear IH
         end; apply 0. Defined.
 (* I think this definition is pretty cool :) *)

Definition exp_eq_dec (e1 e2 : exp) : {e1 = e2} + {e1 <> e2}.
  decide equality. Qed.

Infix "#" := smk (at level 100, right associativity).
Infix "@" := app (at level 500, left associativity).
Notation "&" := var.

Inductive scoped_at (n : nat) : exp -> Prop :=
| scope_var : forall i, i < n -> scoped_at n (& i)

| scope_typ : forall m, scoped_at n (typ m)

| scope_pi : forall a b, scoped_at n a -> scoped_at (S n) b -> scoped_at n (pi a b)
| scope_lam : forall A b, scoped_at n A -> scoped_at (S n) b -> scoped_at n (lam A b)
| scope_app : forall f x, scoped_at n f -> scoped_at n x -> scoped_at n (f @ x)

| scope_sigma : forall a b, scoped_at n a -> scoped_at (S n) b -> scoped_at n (sigma a b)
| scope_smk : forall a b, scoped_at n a -> scoped_at n b -> scoped_at n (a # b)
| scope_srec : forall c p s, scoped_at (S n) c -> scoped_at (2 + n) p -> scoped_at n s
                       -> scoped_at n (srec c p s)

| scope_wt : forall a b, scoped_at n a -> scoped_at (S n) b -> scoped_at n (wt a b)
| scope_sup : forall a f, scoped_at n a -> scoped_at (S n) f -> scoped_at n (sup a f)
| scope_wrec : forall c s w, scoped_at (S n) c -> scoped_at (3 + n) s -> scoped_at n w
                       -> scoped_at n (wrec c s w)

| scope_bool : scoped_at n bool
| scope_true : scoped_at n true
| scope_false : scoped_at n false
| scope_brc : forall c t f b, scoped_at (S n) c -> scoped_at n t -> scoped_at n f -> scoped_at n b
                         -> scoped_at n (brc c t f b)

| scope_top : scoped_at n top
| scope_unit : scoped_at n unit
| scope_urec : forall c u t, scoped_at (S n) c -> scoped_at n u -> scoped_at n t
                       -> scoped_at n (urec c u t)

| scope_bot : scoped_at n bot
| scope_exf : forall c f, scoped_at (S n) c -> scoped_at n f -> scoped_at n (exf c f).

Hint Resolve lt_dec.

Hint Constructors scoped_at.
Hint Constructors sumbool.

Ltac destr_sums :=
  repeat match goal with
           | [ H : {_} + {_} |- _ ] => destruct H
         end.

Ltac Inster_all := repeat
  match goal with
    | [ H : forall x : ?T, _ |- _ ] =>
      let x := fresh "x" in
      evar (x : T);
        let x' := eval unfold x in x in
            clear x; specialize (H x')
  end.

Definition scope_check_at (n : nat) (e : exp) : {scoped_at n e} + {~ scoped_at n e}.
  (* Local Hint Extern 5 => match goal with [H : scoped_at _ _ |- _] => inversion H end. *)
  generalize dependent n; induction e; intro n;
  try (destruct (lt_dec ix n); [left|right]; auto; inversion 1; auto);
  Inster_all; destr_sums; try (left; constructor; eassumption); right; inversion 1; subst; auto.
Qed.

Fixpoint count_free (e : exp) : nat :=
  match e with
    | & i => S i
    | pi a b => max (count_free a) (pred (count_free b))
    | sigma a b => max (count_free a) (pred (count_free b))
    | wt a b => max (count_free a) (pred (count_free b))

    | lam A b => max (count_free A) (pred (count_free b))
    | (f @ x) => max (count_free f) (count_free x)

    | (a # b) => max (count_free a) (count_free b)
    | srec c p s => max (max (pred (count_free c)) (pred (pred (count_free p)))) (count_free s)

    | sup a f => max (count_free a) (pred (count_free f))
    | wrec c s w => max (max (pred (count_free c)) (pred (pred (pred (count_free s))))) (count_free w)

    | brc c t f b => max (max (max (pred (count_free c)) (count_free t)) (count_free f)) (count_free b)
    | urec c u t => max (max (pred (count_free c)) (count_free u)) (count_free t)
    | exf c f => max (pred (count_free c)) (count_free f)
    
    | _ => 0
  end.

Require Import Omega.

Lemma scoped_at_lift (e : exp) n (p : scoped_at n e) : forall m, n <= m -> scoped_at m e.
  induction p; intros; constructor; try apply IHp; try apply IHp1; try apply IHp2; try apply IHp3; try apply IHp4; omega.
Qed.

Print scoped_at_lift.
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
Hint Resolve max_le_eq_l max_le_eq_r max_refl.

Lemma max_left_right : forall n m, (max n m = n) \/ (max n m = m).
  intros; destruct (lt_eq_lt_dec n m) as [Hle|Hgt]; [destruct Hle as [Hlt|Heq]|]; subst;
  [right;apply max_le_eq_l|right;apply max_refl|left;apply max_le_eq_r]; omega. Qed.

Lemma max_le_trans : forall n m d, n <= d -> m <= d -> max n m <= d.
  intros; destruct (max_left_right n m) as [Hn|Hm]; [rewrite Hn|rewrite Hm]; eauto. Qed.

Hint Resolve max_le_trans.

(* well, at least this was easy *)
Theorem count_free_least (e : exp) : forall n, scoped_at n e -> count_free e <= n.
  induction 1; simpl in *; repeat apply max_le_trans; try omega. Qed. 

(* And now for something completely different... *)
Fixpoint vars_op (op : forall(ix d : nat), exp) (d : nat) (e : exp) : exp :=
  match e with
    | & i => op i d

    | pi a b => pi (vars_op op d a) (vars_op op (S d) b)
    | sigma a b => sigma (vars_op op d a) (vars_op op (S d) b)
    | wt a b => wt (vars_op op d a) (vars_op op (S d) b)

    | lam A b => lam (vars_op op d A) (vars_op op (S d) b)
    | (f @ x) => app (vars_op op d f) (vars_op op d x)

    | (a # b) => smk (vars_op op d a) (vars_op op d b)
    | srec c p s => srec (vars_op op (S d) c) (vars_op op (2 + d) p) (vars_op op d s)

    | sup a f => sup (vars_op op d a) (vars_op op (S d) f)
    | wrec c s w => wrec (vars_op op (S d) c) (vars_op op (3 + d) s) (vars_op op d w)

    | brc c t f b => brc (vars_op op (S d) c) (vars_op op d t) (vars_op op d f) (vars_op op d b)
    | urec c u t => urec (vars_op op (S d) c) (vars_op op d u) (vars_op op d t)
    | exf c f => exf (vars_op op (S d) c) (vars_op op d f)

    | _ => e
  end.

Definition wk_var (n ix d : nat) : exp := if le_dec d ix then var (n + ix) else var ix.
Definition wk_deep (n : nat) : nat -> exp -> exp := vars_op (wk_var n).

Hint Unfold vars_op wk_var wk_deep.

Theorem wk_scoped (e : exp) n (p : scoped_at n e) : forall m d, scoped_at (m + n) (wk_deep m d e).
  induction p; intros; unfold wk_deep in *; simpl; try constructor; simpl; repeat rewrite plus_n_Sm; auto.
  - unfold wk_var; simpl; destruct (le_dec d i); constructor; omega.
Qed.

Hint Resolve wk_scoped.

Definition subst_var (v : exp) (i d : nat) : exp := match lt_eq_lt_dec i d with
                                                    | inleft (left _) => var i
                                                    | inleft (right _) => wk_deep d 0 v
                                                    | inright _ => var (pred i)
                                                  end.

Definition subst_deep (v : exp) : nat -> exp -> exp := vars_op (subst_var v).

Transparent vars_op.
Transparent subst_deep.
Transparent subst_var.
Notation "e [ x / i ]" := (subst_deep x i e) (at level 300).

Hint Unfold subst_deep subst_var.

Lemma subst_scoped_pred (e : exp) n (p : scoped_at n e) :
  forall d v, d < n -> scoped_at (n - S d) v -> scoped_at (pred n) (subst_deep v d e).
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
  forall d v, d <= n -> scoped_at (n - d) v -> scoped_at n (subst_deep v d e).
  replace n with (pred (S n)) by omega; intros; apply subst_scoped_pred; auto. Qed.

Hint Resolve subst_scoped.

Theorem subst_0_scoped (e : exp) n (p : scoped_at (S n) e) v : scoped_at n v -> scoped_at n (subst_deep v 0 e).
  intro H. replace n with (n - 0) in H by omega. apply subst_scoped; auto; omega. Qed.

Definition con := list exp.
Open Scope list_scope.

Inductive scoped_con : con -> Prop :=
| scope_nil : scoped_con nil
| scope_cons : forall Gamma X, scoped_con Gamma -> scoped_at (length Gamma) X -> scoped_con (X :: Gamma).

Hint Constructors scoped_con.

Require Import Coq.Program.Wf.

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

Lemma unsubst_scoped : forall e v d n, d <= n -> scoped_at (n - d) v -> scoped_at n (subst_deep v d e) -> scoped_at (S n) e.
  induction e; intros v d n Hd Hv He; unfold subst_deep in *; simpl in *;
  (* var case always takes some special care *)
  try (unfold subst_var in *; simpl in *;
       destruct (lt_eq_lt_dec ix d) as [Hle|Hgt]; [destruct Hle as [Hlt|Heq]|]; inversion He; constructor; omega);
  (* invert things and split *)
  inversion He; subst; repeat constructor;
  (* try all IH's *)
  try eapply (IHe v); try eapply (IHe1 v); try eapply (IHe2 v); try eapply (IHe3 v); try eapply (IHe4 v);
  match goal with
    (* use ordering cases to instantiate d *)
    | [|- _ <= _] => repeat (try apply Hd; apply le_n_S in Hd)
    | _ => assumption (* otherwise it'll just be a piece of He *)
 end.
Qed.

Lemma unsubst_scoped_O : forall e v n, scoped_at n v -> scoped_at n (subst_deep v 0 e) -> scoped_at (S n) e.
  intros e v n Hv He; apply unsubst_scoped in He; try rewrite <- minus_n_O; try assumption; omega. Qed.


Fixpoint lookup_con {A} (Gamma : list A) (i : nat) : A + {i >= length Gamma} :=
  match Gamma , i with
    | nil , _ => inright (Peano.le_0_n i)
    | (X :: Gamma) , 0 => inleft X
    | (X :: Gamma) , S n => match lookup_con Gamma n with
                         | inleft T => inleft T
                         | inright p => inright (le_n_S _ _ p)
                       end
  end.

Program Fixpoint lookup_lt {A} (Gamma : list A) (i : {x | x < length Gamma}) : A :=
  match Gamma , i with
    | nil , _ => False_rect _ _
    | (x :: xs) , 0   => x
    | (x :: xs) , S n => lookup_lt xs n
  end.

Obligation 1. inversion H. Qed.
Obligation 2. exact (le_S_n _ _ H). Defined.

Print lookup_lt.

Lemma lookup_irrel A (Gamma : list A) : forall i p q, lookup_lt Gamma (exist _ i p) = lookup_lt Gamma (exist _ i q).
  induction Gamma; [simpl;intros;exfalso;omega|]; destruct i; intros; simpl; eauto.
Qed.

Hint Rewrite lookup_irrel.

Lemma lookup_cons A Gamma i : forall a, @lookup_lt A (a :: Gamma) (fsu i) = lookup_lt Gamma i.
  destruct i as [i Hi]; simpl; erewrite lookup_irrel; reflexivity. Qed.

Hint Rewrite lookup_cons.

Lemma lookup_lt_con A (Gamma : list A) : forall (i : nat) (Hi : i < length Gamma), lookup_con Gamma i = inleft (lookup_lt Gamma (exist _ i Hi)).
  induction Gamma; destruct i; try (inversion Hi; fail); auto; intros.
  - simpl; rewrite IHGamma with (Hi := (le_S_n _ _ Hi)); reflexivity.
Qed.

Theorem lookup_scoped (Gamma : con) (Hg : scoped_con Gamma) :
  forall i (Hi : i < length Gamma), scoped_at (length Gamma - S i) (lookup_lt Gamma (exist _ i Hi)).
  Hint Rewrite <- minus_n_O.
  induction Hg; try (inversion Hi; fail); intros.
  - destruct i; simpl in *; [rewrite <- minus_n_O; auto|apply IHHg with (Hi := le_S_n _ _ Hi)].
Qed.

Hint Resolve lookup_scoped.

Program Definition lookup_wk (Gamma : con) (i : {x | x < length Gamma}) := wk_deep (S i) 0 (lookup_lt Gamma i).

Check wk_scoped.
Program Definition lookup_wk_scoped_prog (Gamma : {gamma | scoped_con gamma}) i : scoped_at (length Gamma) (lookup_wk Gamma i) :=
  wk_scoped (lookup_lt Gamma i) (length Gamma - S i) _ (S i) 0.

Obligation 2. omega. Qed.

(* split for nicer proof terms *)
Lemma lookup_wk_scoped (Gamma : con) (p : scoped_con Gamma) : forall i, scoped_at (length Gamma) (lookup_wk Gamma i).
  apply (lookup_wk_scoped_prog (exist _ Gamma p)). Qed.

Hint Resolve lookup_wk_scoped.

Definition wk_n n := wk_deep n 0.
Definition wk_at n := wk_deep 1 n.

Definition prop := typ 0.
Definition set := typ 1.

Print list.
Infix "," := (fun Gamma a => cons a Gamma) (at level 50, left associativity).
Infix "-->" := (fun a b => pi a (wk_at 0 b)) (at level 100, right associativity).

Inductive has_type (Gamma : con) : exp -> exp -> Prop :=
| ty_var : forall i p, has_type Gamma (var i) (lookup_wk Gamma (exist _ i p))

| ty_set : forall n, has_type Gamma (typ n) (typ (S n))

| ty_cumulative : forall A n, has_type Gamma A (typ n)
                       -> has_type Gamma A (typ (S n))

| ty_pi_prop : forall A P n, has_type Gamma A (typ n)
                      -> has_type (Gamma , A) P prop
                      -> has_type Gamma (pi A P) prop

| ty_pi_typ : forall A B n m, has_type Gamma A (typ n)
                       -> has_type (Gamma , A) B (typ m)
                       -> has_type Gamma (pi A B) (typ (max n m))

| ty_sg_typ : forall A B n m, has_type Gamma A (typ n)
                       -> has_type (Gamma , A) B (typ m)
                       -> has_type Gamma (sigma A B) (typ (max n m))

| ty_wt_typ : forall A B n m, has_type Gamma A (typ n)
                       -> has_type (Gamma , A) B (typ m)
                       -> has_type Gamma (wt A B) (typ (max n m))

| ty_bool : has_type Gamma bool set
| ty_top : has_type Gamma top prop
| ty_bot : has_type Gamma top bot

| ty_lam : forall A n B b, has_type Gamma A (typ n)
                    -> has_type (Gamma , A) b B
                    -> has_type Gamma (lam A b) (pi A B)

| ty_app : forall A B f a, has_type Gamma f (pi A B)
                    -> has_type Gamma a A
                    -> has_type Gamma (f @ a) (subst_deep a 0 B)

| ty_smk : forall A B a b, has_type Gamma a A
                    -> has_type Gamma b (subst_deep a 0 B)
                    -> has_type Gamma (a # b) (sigma A B)

| ty_srec : forall A B C f s, has_type (Gamma , A , B) f (subst_deep (& 1 # & 0) 0 (wk_deep 2 1 C))
                      -> has_type Gamma s (sigma A B)
                      -> has_type Gamma (srec C f s) (subst_deep s 0 C)

| ty_sup : forall A B n a f, has_type Gamma a A
                      -> has_type (A :: Gamma) B (typ n)
                      -> has_type (subst_deep a 0 B :: Gamma) f (wk_at 0 (wt A B))
                      -> has_type Gamma (sup a f) (wt A B)

| ty_wrec : forall C A B f w,
             has_type (Gamma , A , (pi B (wk_deep 2 0 (wt A B))) , wk_at 1 B) f (subst_deep (& 1 @ & 0) 0 (wk_deep 3 1 C))
           -> has_type Gamma w (wt A B)
           -> has_type Gamma (wrec C f w) (subst_deep w 0 C)

| ty_true : has_type Gamma true bool
| ty_false : has_type Gamma false bool
| ty_brc : forall C t f b, has_type Gamma t (subst_deep true 0 C)
                    -> has_type Gamma f (subst_deep false 0 C)
                    -> has_type Gamma b bool
                    -> has_type Gamma (brc C t f b) (subst_deep b 0 C)

| ty_unit : has_type Gamma unit top
| ty_urec : forall C u t, has_type Gamma u (subst_deep unit 0 C)
                   -> has_type Gamma t top
                   -> has_type Gamma (urec C u t) (subst_deep t 0 C)

| ty_exf : forall C n f, has_type (bot :: Gamma) C (typ n)
                  -> has_type Gamma f bot
                  -> has_type Gamma (exf C f) (subst_deep f 0 C).

Notation "Gamma ⊢ t ∈ T" := (has_type Gamma t T) (at level 10).
Hint Constructors has_type.

Inductive wf_con : con -> Prop :=
| wf_nil : wf_con nil
| wf_cons : forall Gamma A n, wf_con Gamma -> Gamma ⊢ A ∈ (typ n) -> wf_con (Gamma , A).

Hint Constructors wf_con.

Theorem typed_implies_scoped : forall Gamma t T, scoped_con Gamma -> Gamma ⊢ t ∈ T -> scoped_at (length Gamma) T /\ scoped_at (length Gamma) t.
Proof with eassumption.
  intros Gamma t T Hg.
  induction 1; auto; simpl in *; try (repeat constructor; auto; fail);
  try (destruct (IHhas_type Hg) as [IH1 IH2]);
  try (destruct (IHhas_type1 Hg) as [IH11 IH12]); try (destruct (IHhas_type2 Hg) as [IH21 IH22]);
  try (destruct (IHhas_type3 Hg) as [IH31 IH32]); try (destruct (IHhas_type4 Hg) as [IH41 IH42]);
  try (destruct (IHhas_type2 (scope_cons _ _ Hg IH12)) as [IH21 IH22]);
  try (split; repeat constructor; auto; fail).
  (* app is weird *)
  - split; try (constructor; auto).
    + inversion IH11; subst; apply subst_0_scoped...
  - split; try (constructor;auto); eapply unsubst_scoped_O; [|eassumption]...
  (* recursion principles will take special handling *)
  - inversion IH21; subst. assert (Hg' : scoped_con (B :: A :: Gamma)) by auto. destruct (IHhas_type1 Hg') as [IH11 IH12].
    assert (IHC : scoped_at (S(length Gamma)) C).
      + apply unwk_scoped with (n := 2) (d := 1); [omega|eapply unsubst_scoped]; try eassumption.
        * omega.
        * constructor; constructor; omega.
    + split; auto.
      * apply subst_0_scoped...
  (* oh, and so will sup *)
  - destruct (IHhas_type2 (scope_cons _ _ Hg IH11)) as [IH21 IH22].
    assert (Hg'' : scoped_con (subst_deep a 0 B :: Gamma)).
      constructor; [|apply subst_0_scoped]...
    destruct (IHhas_type3 Hg''); split; auto.
  (* now for the /really/ fun one, wrec *)
  - inversion IH21; subst.
    assert (Hg' : scoped_con (wk_at 1 B :: pi B (wk_deep 2 0 (wt A B)) :: A :: Gamma)).
      constructor; [constructor ;[constructor|]|];
      [| |simpl; constructor; try assumption;
          replace (S (S (length Gamma))) with (2 + length Gamma) by omega;
          apply wk_scoped; constructor
       | simpl; replace (S (S (length Gamma))) with (1 + S(length Gamma)) by omega; apply wk_scoped]...
    destruct (IHhas_type1 Hg') as [IH11 IH12].
    assert (Hc : scoped_at (S (length Gamma)) C). 
      apply unsubst_scoped_O in IH11; [|constructor;constructor;omega].
      apply unwk_scoped with (n := 3) (d := 1); [omega|]...
    split; [apply subst_0_scoped|constructor]...
  - assert (Hc : scoped_at (S (length Gamma)) C).
      eapply unsubst_scoped_O; [|eassumption]; auto.
    split; [apply subst_0_scoped|constructor]...
  - assert (Hc : scoped_at (S (length Gamma)) C).
      eapply unsubst_scoped_O; [|eassumption]; auto.
    split; [apply subst_0_scoped|constructor]...
  - destruct (IHhas_type1 (scope_cons _ _ Hg (scope_bot _))) as [IH11 IH12].
    split; [apply subst_0_scoped|constructor]...
Qed. (* seems like it ought to be possible to automate more of that, but for now I'll just leave it be *)

Theorem wf_implies_scoped : forall Gamma, wf_con Gamma -> scoped_con Gamma.
  induction 1; constructor; try eapply typed_implies_scoped; eassumption. Qed.