Require Export Tactics.
Require Export mathcomp.ssreflect.all_ssreflect.
Require Export Coq.Program.Program.
Set Implicit Arguments.

(* Program things *)
Set Shrink Obligations.
Unset Transparent Obligations.
Set Hide Obligations.
Obligation Tactic := program_simpl; try (simpl in *; solve by inversion || auto).

Notation fin n := {i : nat | i < n}.
Definition mk_fin {n : nat} (ix : nat) (p : ix < n) : fin n := exist _ ix p.
Arguments mk_fin {n} ix p.

Hint Constructors le.
Hint Resolve le_pred le_S_n le_0_n le_n_S.

Hint Rewrite ltn0.

Hint Extern 1 =>
  match goal with
      | [ _ : ?n < 0 |- _ ] => exfalso; eapply ltn0; eassumption
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

Program Definition fze {n} : fin (S n) := mk_fin 0 _.
Program Definition fsu {n} (f : fin n) : fin (S n) := mk_fin (S f) _.
Program Definition flsu {n} (f : fin n) : fin (S n) := mk_fin f _.

Lemma sig_flsu n (f : fin n) : ` (flsu f) = ` f.
Proof. destruct f; reflexivity. Qed.

Hint Rewrite sig_flsu.

Ltac Snle_0 :=
  match goal with
    | [ H : S _ <= 0 |- _ ] => exfalso; inversion H
  end.

Ltac Snlt_1 := 
  match goal with
    | [ H : S _ < 1 |- _ ] => exfalso; inversion H; Snle_0
  end.

Local Hint Extern 1 => destr_fins.
Local Hint Extern 1 => Snle_0.
Local Hint Extern 1 => Snlt_1.


Hint Rewrite leq_subLR leq_subr leq_sub2r ltnS.
Hint Rewrite subnKC subSS.
Program Definition finvert {n} (f : fin n) : fin n := mk_fin (n - S f) _.
Next Obligation. destruct n; [auto|clear H]; autorewrite with core in *; auto. Qed.

Lemma finv_eq n : forall (f : fin  n.+1), ` f + ` (finvert f) = n.
Proof. destruct f; simpl; autorewrite with core in *; auto. Qed.
