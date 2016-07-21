Require Export Coq.Program.Program.
Require Export Tactics.
Require Export MonadLib.
Require Export mathcomp.ssreflect.all_ssreflect.
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

Fixpoint lookup_con {A} (Gamma: seq A) (i : nat) : option A :=
  match Gamma , i with
    | nil , _ => None
    | (X :: Gamma) , 0 => Some X
    | (X :: Gamma) , S n => match lookup_con Gamma n with
                         | Some T => Some T
                         | None => None
                       end
  end.

Lemma lookup_iff_ge A : forall Gamma i, ⟦Gamma⟧ <= i <-> @lookup_con A Gamma i = None.
  induction Gamma; destruct i; simpl; split; intros; auto; try solve by inversion.
  - specialize (IHGamma i). assert(H': size Gamma <= i) by auto. apply IHGamma in H'. rewrite H'. auto.
  - specialize (IHGamma i). destruct (lookup_con Gamma i); [inversion H|apply IHGamma in H]; auto.
Qed.

Hint Rewrite lookup_iff_ge.
(* Hint Rewrite ltnNge. *)
Hint Unfold is_true.
Hint Rewrite Bool.negb_involutive Bool.negb_true_iff.
Hint Extern 1 => match goal with [H1 : ?p = true, H2 : ?p = false |- _] => exfalso; congruence end.

Lemma lookup_iff_lt {A} : forall Gamma i, i < ⟦Gamma⟧ <-> exists a : A, lookup_con Gamma i = Some a.
Proof.
  split.
  - remember (lookup_con Gamma i) as lgi; destruct lgi; [eauto|].
    assert (⟦Gamma⟧ <= i) by (apply lookup_iff_ge; auto).
    autounfold in *; rewrite ltnNge; autorewrite with core in *; auto.
  - move=>[a H]; remember (⟦ Gamma ⟧ <= i) as lgi; destruct lgi;
         [assert (⟦Gamma⟧ <= i) by auto|autounfold];
         rewrite ltnNge; autorewrite with core in *; [congruence|auto].
Qed.

Require Export Fin.

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
Hint Extern 1 False => apply Bool.diff_true_false. 

Local Hint Unfold lt.
Tactic Notation "destruct" "match" := match goal with [|-context[match ?e with _ => _ end]] => destruct e end.
Lemma lookup_lt_con A (Gamma : seq A) : forall (i : fin ⟦Gamma⟧), lookup_con Gamma (`i) = Some (lookup_lt Gamma i).
Proof.
  induction Gamma; destruct i as [i Hi]; simpl in *; [exfalso;auto|destruct i];
  reflexivity || rewrite <- IHGamma; simpl in *; destruct match; auto.
Qed.  

(* Relation stuff *)

Require Export Relation_Definitions Relation_Operators.
Hint Constructors clos_trans clos_refl_trans_1n.

Lemma rtc_rtc : forall A R e1 e2 e3, clos_refl_trans_1n A R e1 e2 -> clos_refl_trans_1n A R e2 e3 -> clos_refl_trans_1n A R e1 e3.
Proof. induction 1; eauto. Qed.

Inductive W (A : Type) (B : A -> Type) : Type :=
  sup : forall a, (B a -> W B) -> W B.

Set Boolean Equality Schemes.
Set Decidable Equality Schemes.
Inductive desc : Type := 
  d_One | d_Ind
| d_Sum of desc of desc
| d_Prd of desc of desc.

Fixpoint desc_func (D : desc) (X : Type) : Type :=
  match D with
      d_One => True
    | d_Ind => X
    | d_Sum A B => desc_func A X + desc_func B X
    | d_Prd A B => desc_func A X * desc_func B X
  end.

Example Seq (D : desc) : desc := d_Sum d_One (d_Prd D d_Ind).
Definition desc_dec_eq (e1 e2 : desc) : {e1 = e2} + {e1 <> e2}.
Proof.  decide equality. Defined.

(* This is hilarious *)

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
