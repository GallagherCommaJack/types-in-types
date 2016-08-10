Require Export Relation_Definitions Relation_Operators Coq.Classes.RelationClasses.
Require Export Coq.Program.Program.
Require Export mathcomp.ssreflect.all_ssreflect.
Require Export Tactics.
Require Export MonadLib.
Require Export Fin.
(* notations *)

Open Scope seq_scope.
Notation "⟦ xs ⟧" := (size xs).
Notation "<< x , y >>" := (exist _ x y).

(* Program things *)
Set Shrink Obligations.
Unset Transparent Obligations.
Set Hide Obligations.
Obligation Tactic := program_simpl; try (simpl in *; auto; solve by inversion).

Set Implicit Arguments.

(* Hint Rewrite ltnNge. *)
Hint Unfold is_true.
Hint Rewrite Bool.negb_involutive Bool.negb_true_iff.
Hint Extern 1 => match goal with [H1 : ?p = true, H2 : ?p = false |- _] => exfalso; congruence end.

Program Fixpoint lookup_lt {A} (Gamma : seq A) (i : fin ⟦Gamma⟧) : A :=
  match Gamma , i with
    | nil , _ => False_rect _ _
    | (x :: xs) , 0   => x
    | (x :: xs) , S n => lookup_lt xs n
  end.

Lemma lookup_irrel A (Gamma : seq A) : forall i j, `i = `j -> lookup_lt Gamma i = lookup_lt Gamma j.
Proof.
  induction Gamma; move=>[i Hi]; destruct j; simpl in *; destruct 1;
  [exfalso; auto|destruct i]; eauto.
Qed.

Hint Rewrite lookup_irrel.

Program Definition fsu {n} : fin n -> fin (S n) := S.

Lemma lookup_cons A Gamma i : forall a, @lookup_lt A (a :: Gamma) (fsu i) = lookup_lt Gamma i.
Proof. destruct i as [i Hi]; simpl; intros; apply lookup_irrel; reflexivity. Qed.

Hint Rewrite lookup_cons.

Hint Rewrite ltn0.
Hint Extern 1 => match goal with [H:_<0|-_] => exfalso; rewrite ltn0; apply H end.
Hint Extern 3 False => apply Bool.diff_true_false. 

Local Hint Unfold lt.

(* Relation stuff *)

Local Hint Constructors clos_trans clos_refl_trans_1n.

Lemma rtc_rtc : forall A R e1 e2 e3, clos_refl_trans_1n A R e1 e2 -> clos_refl_trans_1n A R e2 e3 -> clos_refl_trans_1n A R e1 e3.
Proof. induction 1; eauto. Qed.

Instance clos_trans_transitive A R : Transitive (clos_trans A R) := t_trans _ _.
Instance clos_refl_trans_preorder A R : PreOrder (clos_refl_trans A R). split; eauto using clos_refl_trans. Qed.
Instance clos_refl_sym_trans_equivalence A R : Equivalence (clos_refl_sym_trans A R). split; eauto using clos_refl_sym_trans. Qed.

Hint Extern 1 (reflect (_ = _) (_ == _)) => apply eqP.
Instance eqType_beq_equivalence (E : eqType) : Equivalence (fun e1 e2 : E => e1 == e2).
Proof. split; unfold Reflexive; unfold Symmetric; unfold Transitive; intros.
  - rewrite (reflect_iff (x = x)); eauto. 
  - erewrite (reflect_iff (x = y)) in H; auto; rewrite (reflect_iff (y = x)); auto.
  - erewrite (reflect_iff (x = y)) in H; auto.
    erewrite (reflect_iff (y = z)) in H0; auto.
    rewrite (reflect_iff (x = z)); solve[auto|congruence].    
Qed.

Instance leq_preorder : PreOrder (fun x y => x <= y).
Proof. split; unfold Reflexive; unfold Transitive; intros; conv_to_prop; omega. Qed.
  
Instance ltn_preorder : Transitive (fun x y => x < y).
Proof. unfold Transitive; intros; conv_to_prop; omega. Qed.

(* inductive type schemas *)

(* W types *)
Inductive W (A : Type) (B : A -> Type) : Type :=
  sup : forall a, (B a -> W B) -> W B.

(* ADT's *)
Set Boolean Equality Schemes.
Set Decidable Equality Schemes.

Inductive desc : Type := 
  d_One | d_Ind
| d_Sum of desc of desc
| d_Prd of desc of desc.

Hint Resolve andb_true_intro.
Hint Resolve internal_desc_dec_bl internal_desc_dec_lb.

Lemma desc_eqnP : Equality.axiom desc_beq.
Proof. move=>x y. apply (iffP idP); auto. Qed.

Canonical desc_eqMixin := EqMixin desc_eqnP.
Canonical desc_eqType := EqType desc desc_eqMixin.

(* ADT functors *)
Fixpoint desc_func (D : desc) (X : Type) : Type :=
  match D with
      d_One => True
    | d_Ind => X
    | d_Sum A B => desc_func A X + desc_func B X
    | d_Prd A B => desc_func A X * desc_func B X
  end.

Definition dfmap D A B (f : A -> B) : desc_func D A -> desc_func D B. induction D; cbn; intuition. Defined.
Hint Resolve dfmap.
Program Instance desc_functor D : Functor (desc_func D) := Build_Functor _ (dfmap D) _ _.
Solve Obligations with induction D; simpl; intros; auto; destruct x; simpl; congruence.

(* fixpoint taker *)
Inductive D_mu D : desc -> Type :=
| D_sum_inl : forall D1 D2, D_mu D D1 -> D_mu D (d_Sum D1 D2)
| D_sum_inr : forall D1 D2, D_mu D D2 -> D_mu D (d_Sum D1 D2)
| D_prd : forall D1 D2, D_mu D D1 -> D_mu D D2 -> D_mu D (d_Prd D1 D2)
| D_unit : D_mu D d_One
| D_wrap : D_mu D D -> D_mu D d_Ind.

Hint Constructors D_mu.
Notation mu D := (D_mu D D).

(* proof of iso-recursivity *)
Definition unwrap D1 D2 : D_mu D1 D2 -> desc_func D2 (mu D1).
Proof. move: D1; induction D2; simpl; intros; auto; inverts H; auto. Defined.

Definition wrap D1 D2 : desc_func D2 (mu D1) -> D_mu D1 D2. 
Proof. move: D1; induction D2; simpl; intros; auto; intuition. Defined.

Lemma wrap_unwrap D1 D2 : forall d, wrap D1 D2 (unwrap d) = d.
Proof. induction d; simpl; f_equal; auto. Qed.

Lemma unwrap_wrap D1 D2 : forall d, unwrap (wrap D1 D2 d) = d.
Proof. move:D1; induction D2; intros; trivial;
  destruct d; simpl in *; cbn; congruence.
Qed.

Fixpoint RAll_aux D1 D2 (P : mu D1 -> Type) : desc_func D2 (mu D1) -> Type :=
  match D2 with
    | d_One => fun _ => True
    | d_Ind => fun d => P d
    | d_Sum D21 D22 => fun d => match d with inl a => RAll_aux D21 P a | inr b => RAll_aux D22 P b end
    | d_Prd D21 D22 => fun d => let (a,b) := d in prod (RAll_aux D21 P a) (RAll_aux D22 P b)
  end.

Definition all_aux D1 (P : mu D1 -> Type) (p : forall d, P d) : forall D2 d2, RAll_aux D2 P d2.
Proof. induction D2; simpl; try destruct d2; intuition. Defined.

Definition RAll D1 D2 (P : mu D1 -> Type) : D_mu  D1 D2 -> Type := fun d => RAll_aux D2 P (unwrap d).
Definition all D1 D2 (P : mu D1 -> Type) (p : forall d, P d) : forall (d : D_mu D1 D2), RAll P d :=
  fun d => all_aux P p D2 (unwrap d).

Definition mu_comb_aux D1 D2 (C : mu D1 -> Type) (c : forall d, RAll C d -> C d) : forall (d : D_mu D1 D2), RAll C d.
Proof. induction d; cbv; intros; intuition. Defined.

Definition mu_comb D (C : mu D -> Type) (c : forall d, RAll C d -> C d) d : C d := c d (mu_comb_aux C c d).

(* alternately, we can make mu as a recursive predicate over an ADT *)
Inductive mexp : Type :=
| inl__m : mexp -> mexp
| inr__m : mexp -> mexp
| pair__m : mexp -> mexp -> mexp
| unit__m : mexp
| wrap__m : mexp -> mexp.

Fixpoint mu__mexp D (d : desc) (m : mexp) : bool :=
  match d,m with
    | d_Prd d1 d2, pair__m a b => mu__mexp D d1 a && mu__mexp D d2 b
    | d_Sum d1 d2, inl__m a => mu__mexp D d1 a
    | d_Sum d1 d2, inr__m b => mu__mexp D d2 b
    | d_One, unit__m => true
    | d_Ind, wrap__m d => mu__mexp D D d
    | _,_ => false
  end.
  
(* Inductive mu__mexp D : desc -> mexp -> Type := *)
Section mu__mexp.
  Variables (D D1 D2 : desc) (d1 d2 : mexp).
  Lemma T_inl : mu__mexp D D1 d1 -> mu__mexp D (d_Sum D1 D2) (inl__m d1). cbn; auto. Qed.
  Lemma T_inr : mu__mexp D D2 d2 -> mu__mexp D (d_Sum D1 D2) (inr__m d2). cbn; auto. Qed.
  Lemma T_pair : mu__mexp D D1 d1 -> mu__mexp D D2 d2 -> mu__mexp D (d_Prd D1 D2) (pair__m d1 d2). cbn; auto. Qed.
  Lemma T_unit : mu__mexp D d_One unit__m. cbn; auto. Qed.
  Lemma T_wrap : forall d, mu__mexp D D d -> mu__mexp D d_Ind (wrap__m d). cbn; auto. Qed.
End mu__mexp.

Hint Resolve T_inl T_inr T_pair T_unit T_wrap.
Hint Constructors mexp.
Notation D_mexp D1 D2 := {m : mexp | mu__mexp D1 D2 m}.

Section mu__texp.
  Program Definition inl__t D D1 D2 (d1 : D_mexp D D1) : D_mexp D (d_Sum D1 D2) := inl__m d1.
  Program Definition inr__t D D1 D2 (d2 : D_mexp D D2) : D_mexp D (d_Sum D1 D2) := inr__m d2.
  Program Definition pair__t D D1 D2 (d1 : D_mexp D D1) (d2 : D_mexp D D2) : D_mexp D (d_Prd D1 D2) := pair__m d1 d2.
  Program Definition unit__t D : D_mexp D d_One := unit__m.
  Program Definition wrap__t D (d : D_mexp D D) : D_mexp D d_Ind := wrap__m d.
End mu__texp.

Hint Resolve inl__t inr__t pair__t unit__t wrap__t.

Definition mexp_of_mu D1 D2 : D_mu D1 D2 -> D_mexp D1 D2.
Proof. induction 1; eauto. Defined.

Set Transparent Obligations.
Definition mu_of_mexp_aux D1 D2 (d : mexp) (Hd : mu__mexp D1 D2 d) : D_mu D1 D2.
Proof. move:D2 Hd; induction d; destruct D2; simpl; intros; 
  autounfold in *; destr bands; discriminate || auto. Defined.

Definition mu_of_mexp {D1 D2} (d : D_mexp D1 D2) : D_mu D1 D2 := mu_of_mexp_aux _ _ (`d) (proj2_sig d).
Hint Unfold mu_of_mexp.

Lemma bool_subset_eq_compat X (P : pred X) : forall (x1 x2 : {x | P x}), ` x1 = `x2 -> x1 = x2.
Proof. destruct x1,x2; simpl; intros; subst; f_equal; apply bool_irrelevance. Qed.

Lemma mexp_of_mu_of_mexp D1 D2 : forall (d : D_mexp D1 D2) , mexp_of_mu (mu_of_mexp d) = d.
Proof. intros; unfold mu_of_mexp; destruct d as [d Hd]; simpl. apply bool_subset_eq_compat; simpl.
  move: D2 Hd; induction d; destruct D2; simpl; intros;
  solve[discriminate|try destruct match; simpl; f_equal; auto]. Qed.

Lemma mu_of_mexp_of_mu D1 D2 : forall (d : D_mu D1 D2) , mu_of_mexp (mexp_of_mu d) = d.
Proof. induction d; trivial; simpl; repeat match goal with [H:context[mexp_of_mu ?d] |- _] => destruct (mexp_of_mu d) end;
  subst; unfold mu_of_mexp; simpl; try destruct match; solve[repeat f_equal;apply bool_irrelevance]. Qed.
