Require Export Subset.
Require Export Arith.

Set Implicit Arguments.

Definition fin (n : nat) : Set := { i : nat | i < n }.
Definition mk_fin {n : nat} (ix : nat) (p : ix < n) : fin n := exist _ ix p.
Arguments mk_fin {n} ix p.

Hint Constructors le.
Hint Resolve le_pred le_S_n le_0_n le_n_S.

Theorem none_lt_0 : forall n, ~(n < 0).
  induction n; inversion 1. Qed.

Hint Extern 1 =>
  match goal with
      | [ _ : ?n < 0 |- _ ] => exfalso; eapply none_lt_0; eassumption
 end.   

Lemma nofin0 : fin 0 -> False.
  destruct 1; eauto. Qed.

Ltac nof0 :=
  match goal with
    | [ f : fin 0 |- _ ] => exfalso; apply (nofin0 f)
  end.

Ltac destr_fins :=
  repeat match goal with [ f : fin _ |- _ ] => destruct f end.

Hint Resolve nofin0.

Require Import Omega.
Local Hint Extern 1 => destr_fins; simpl in *; omega.
Program Definition fze {n} : fin (S n) := mk_fin 0 _.
Program Definition fsu {n} (f : fin n) : fin (S n) := mk_fin (S f) _.
Program Definition flsu {n} (f : fin n) : fin (S n) := mk_fin f _.

Lemma sig_flsu n (f : fin n) : proj1_sig (flsu f) = proj1_sig f.
  destruct f; reflexivity. Qed.

Hint Rewrite sig_flsu.

Ltac Snle_0 :=
  match goal with
    | [ H : S _ <= 0 |- _ ] => exfalso; inversion H
  end.

Ltac Snlt_1 := 
  match goal with
    | [ H : S _ < 1 |- _ ] => exfalso; inversion H; Snle_0
  end.

Local Hint Extern 1 => Snle_0.
Local Hint Extern 1 => Snlt_1.

Program Definition finvert {n} (f : fin n) : fin n := mk_fin (n - S f) _.

Lemma finv_eq n : forall (f : fin (S n)), proj1_sig f + proj1_sig (finvert f) = n. eauto. Qed.
