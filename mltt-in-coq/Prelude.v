Require Export Arith Omega.
Require Export Coq.Program.Program.
Require Export Tactics Monad.

(* notations *)
Open Scope list_scope.
Notation "⟦ xs ⟧" := (length xs).
Notation "<< x , y >>" := (exist _ x y).

(* Program things *)
Set Shrink Obligations.
Unset Transparent Obligations.
Set Hide Obligations.
Obligation Tactic := program_simpl; try (simpl in *; omega).

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

Lemma lookup_lt_con A (Gamma : list A) : forall i, lookup_con Gamma (`i) = Some (lookup_lt Gamma i).
  induction Gamma; intro i; simpl in i; destruct i as [i Hi]; [omega|]; destruct i; [reflexivity|].
  assert (H: i < length Gamma) by omega; specialize (IHGamma (exist _ i H)); simpl in *; 
  rewrite IHGamma; f_equal; apply lookup_irrel; auto.
Qed.  

(* Relation stuff *)

Require Export Relation_Definitions Relation_Operators.
Hint Constructors clos_trans clos_refl_trans_1n.

Lemma rtc_rtc : forall A R e1 e2 e3, clos_refl_trans_1n A R e1 e2 -> clos_refl_trans_1n A R e2 e3 -> clos_refl_trans_1n A R e1 e3.
  induction 1; eauto. Qed.
