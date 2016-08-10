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

(* Inductive desc_prop (X : Type) : desc -> Type -> Prop := *)
(*   d_One : forall D, desc_prop X D True *)
(* | d_Ind : desc_prop X Ind X *)
(* | d_Sum : forall A B xA xB, desc_prop X A xA -> desc_prop X B xB -> desc_prop X (Sum A B) (xA + xB) *)
(* | d_Prd : forall A B xA xB, desc_prop X A xA -> desc_prop X B xB -> desc_prop X (Prd A B) (xA * xB). *)

(* Theorem desc_func_corr : forall D X, desc_prop X D (desc_func D X). *)
(* Proof. induction D; intros; eauto using desc_prop. Qed. *)

(* Sanity check, not including in final thing *)
(* Theorem desc_func_dec : forall D X, (forall (x y : X), {x = y} + {x <> y}) ->  *)
(*                                forall (d1 d2 : desc_func D X), {d1 = d2} + {d1 <> d2}. *)
(* Proof. induction D; simpl; intros X dX;  *)
(*        assumption || decide equality || destruct d1,d2; eauto. *)
(* Qed. *)


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
