Require Import Prelude.
Require Import Expr.

(* This is the right way to define functions :) *)
Notation "( && b )" := (fun b' => b' && b).
Fixpoint closed_at (l : nat) (e : exp) : bool.
Proof.
  destruct e; 
  repeat match goal with
           | [i : var |- _] => exact: (i < l)
           | [e : {bind exp} |- _] => apply (closed_at l.+1) in e; apply (&& e)
           | [e : exp |- _] => apply (closed_at l) in e; apply (&& e)
           | _ => exact: true
         end.
Defined.

(* While we're at it *)
Ltac mk_size T f :=
  repeat match goal with [e : T |- _] => apply f in e; apply (+ e) | _ => exact: 1 end.
      
Fixpoint term_size (e : exp) : nat.
  destruct e; mk_size exp term_size.
Defined.

Notation closed := (closed_at 0).

Notation closed_sub l sigma := (forall i, i < l -> sigma i = Bind i).
Lemma closed_up : forall l sigma, closed_sub l sigma -> closed_sub l.+1 (up sigma).
  intros. destruct i; asimpl; eauto. rewrite H; eauto. Qed.

Tactic Notation "destr" "bands" := 
  repeat match goal with
           | [H: _ && _|-_] => apply andb_prop in H; destruct H
           | [H: _ && _ = true |- _] => apply andb_prop in H; destruct H
         end.

(* This proof is gross for stupid reasons - fix later *)
Hint Resolve andb_true_intro.
Lemma closed_lift : forall e i j, i <= j -> closed_at i e -> closed_at j e.
  induction e; intros; simpl in *; try reflexivity; unfold is_true in *;
  apply leq_trans with (n := i) ||
    (destr bands;
    repeat match goal with [H : forall i j : nat, _ |- _] => extend (H i j); extend (H i.+1 j.+1) end);
    auto 10.
Qed.

(* Hint Resolve le_pred le_S_n le_0_n le_n_S. *)
(* Hint Rewrite leq_subLR leq_subr leq_sub2r ltnS. *)

Lemma closed_under : forall i j sigma, i <= j -> closed_sub j sigma -> closed_sub i sigma.
Proof. induction i; intros; try solve by inversion. apply H0. eapply leq_trans; eauto. Qed.

Hint Resolve closed_up.
Lemma closed_at_sub_id : forall e i sigma, closed_sub i sigma -> closed_at i e -> e.[sigma] = e.
  induction e; intros i sigma Hsig; extend (closed_up _ _ Hsig); 
  intros; simpl in *; unfold is_true in *;
  repeat match goal with [H : _ && _ = true |- _] => apply andb_prop in H; destr_ands end;
  f_equal; eauto.
Qed.

Hint Rewrite closed_at_sub_id using assumption.

Lemma sub_0 : forall sigma, closed_sub 0 sigma. intros; solve by inversion. Qed.

Notation sub_vars i j sigma := (forall v, v < i -> closed_at j (sigma v)).

Hint Rewrite ltn_add2l.
Notation upnren := (fun n => iterate upren n).

Hint Resolve iterate_S iterate_0.

Notation mono sigma := (forall i j, i < j -> sigma i < sigma j).
Lemma upren_mono_less : forall v sigma, mono sigma -> upren sigma v <= sigma v. induction v; simpl; intros; auto. Qed.
Lemma wk_mono : forall k, mono (+k). intros; autorewrite with core; auto. Qed.
Lemma upren_mono : forall sigma, mono sigma -> mono (upren sigma). destruct i,j; try solve by inversion; simpl; autorewrite with core in *; auto. Qed.

Lemma iterate_preserves A P (f : A -> A) : (forall a, P a -> P (f a)) -> forall n a, P a -> P (iterate f n a).
Proof. induction n; intros; rewrite ?iterate_S ?iterate_0; auto. Qed.
  
Hint Resolve upren_mono_less wk_mono upren_mono.
Hint Rewrite upren_mono_less wk_mono upren_mono.

Lemma upnren_mono : forall n sigma, mono sigma -> mono (upnren n sigma). intros n sigma. apply iterate_preserves; auto. Qed.
Hint Resolve upnren_mono.
Lemma upnren_mono_less : forall n v sigma, mono sigma -> upnren n sigma v <= sigma v.
Proof. induction n; intros; rewrite ?iterate_S; auto. transitivity (upnren n sigma v); auto. Qed.
Hint Resolve upnren_mono_less.

Hint Rewrite Bool.orb_false_r Bool.orb_true_iff.
Hint Rewrite Bool.andb_negb_r Bool.andb_true_iff.
Hint Resolve andb_prop Bool.orb_prop.

Hint Rewrite up_upren_n_internal up_upren_internal using auto.
Hint Resolve up_upren_n_internal up_upren_internal.
Hint Resolve andb_true_intro.

Notation sub_eq sigma tau := (forall v, sigma v = tau v).
Lemma up_resp_eq : forall sigma tau, sub_eq sigma tau -> sub_eq (up sigma) (up tau). destruct v; asimpl; f_equal; auto. Qed.
Hint Resolve up_resp_eq.
Lemma sub_vars_tms : forall e sigma tau, sub_eq sigma tau -> e.[sigma] = e.[tau]. induction e; intros; simpl; f_equal; auto. Qed.
Canonical sub_eq_refl : reflexive (var -> exp) (fun sigma tau => sub_eq sigma tau). constructor. Qed.

Hint Rewrite sub_vars_tms using auto.
Hint Resolve sub_vars_tms.

Notation closed_ren i j xi := (forall v, v < i -> xi v < j).
Lemma ren_upren : forall i j xi, closed_ren i j xi -> closed_ren i.+1 j.+1 (upren xi).
Proof. destruct v; simpl; intros; firstorder. Qed.
Hint Resolve ren_upren.

Lemma ren_closed_corr e : forall i j xi, closed_ren i j xi -> closed_at i e -> closed_at j e.[ren xi].
Proof. induction e; simpl; intros; autounfold in *; destr bands;
  try solve[auto|   (* this would just be eauto, but it seems to be broken with closed_at *)
            asimpl; repeat (apply andb_true_intro; split);
            eapply IHe || eapply IHe0 || eapply IHe1 || eapply IHe2;
            eassumption || apply ren_upren; auto].
Qed.
Hint Resolve ren_closed_corr.

Lemma ren_wk_scoped : forall i j, closed_ren i (j + i) (+j). auto. Qed.
Hint Resolve ren_wk_scoped.
Lemma wk_scoped i j e : closed_at i e -> closed_at (j + i) e.[wk j]. eapply ren_closed_corr; auto. Qed.
Hint Resolve wk_scoped.
Lemma wk1_scoped i e  : closed_at i e -> closed_at i.+1 e.[wk 1]. change i.+1 with (1 + i); auto. Qed.
Hint Resolve wk1_scoped.
(* Lemma wk_upn : forall e d i j, closed_at d e -> closed_at (i + d) e.[upn j (wk i)]. *)
(* Proof *)
(*   move=>e d i j.  *)
(*   replace e.[upn j (wk i)] with e.[ren (upnren j (+ i))] by (apply sub_vars_tms; autorewrite with core; auto). *)
(*   move:d i j. *)
(*   induction e; intros; auto; *)
(*   try (unfold is_true in *; simpl in *; autorewrite with core in *; destr_logic;  *)
(*        try (rewrite <- iterate_S; replace (i + d).+1 with (i + d.+1)); *)
(*        auto; fail). *)
(*   { simpl in *. induction j; simpl.  *)
(*     { unfold iterate; simpl. autorewrite with core in *; auto. } *)
(*     { rewrite iterate_S. destruct v; simpl in *. *)
(*       { destruct j; unfold iterate in *; simpl in *; induction i; auto. } *)
(*       { assert ((upnren j (+i) v) <= i + v) by auto. *)
(*         assert (i + v.+1 < i + d) by (autorewrite with core; auto). *)
(*         replace (i + v.+1) with ((i + v).+1) in H1 by auto. *)
(*         apply leq_ltn_trans with (n := (i + v).+1); auto. }} *)
(*   } *)
(* Qed. *)

(* Hint Resolve wk_upn. *)

Lemma up_vars : forall i j sigma, sub_vars i j sigma -> sub_vars i.+1 j.+1 (up sigma).
Proof. intros. destruct v; asimpl; auto. Qed.

Lemma wk_vars : forall i, sub_vars i i.+1 (wk 1). auto. Qed.

Hint Resolve up_vars wk_vars.
Tactic Notation "htry" :=
  repeat match goal with
             [H: ?P -> _, H2 : ?P |- _] => extend (H H2)
           | [H1: forall e, _, H2 : _ |- _] =>
             extend (H1 _ H2) || extend (H1 _ _ H2)
         end.

Lemma sub_vars_scoped : forall e i j sigma, sub_vars i j sigma -> closed_at i e -> closed_at j e.[sigma].
Proof. move=>e i j sigma Hs He.
  move: i He j sigma Hs.
  induction e; intros; simpl; rewrite asms; auto;
  simpl in *; unfold is_true in *; destr bands; try apply up_vars; eassumption || auto.
Qed.

Hint Resolve sub_vars_scoped.

Lemma closed_sub_id : forall e sigma, closed e -> e.[sigma] = e.
Proof. intros; apply closed_at_sub_id with (i := 0); intros; solve by inversion || auto. Qed.

Lemma cons_vars_scoped e sigma i j : sub_vars i j sigma -> closed_at j e -> sub_vars i.+1 j (e .: sigma). intros; destruct v; simpl; auto. Qed.
Hint Resolve cons_vars_scoped.
Lemma cons_scoped sigma i j v e : sub_vars i j sigma -> closed_at j v -> closed_at i.+1 e -> closed_at j e.[v .: sigma].
Proof. intros; eapply sub_vars_scoped; eassumption || apply cons_vars_scoped; auto. Qed.
Hint Resolve cons_scoped.

Lemma cons_id_scoped i v e : closed_at i v -> closed_at i.+1 e -> closed_at i e.[v/]. 
Proof. apply cons_scoped with (i := i); auto. Qed.
Hint Resolve cons_id_scoped.

(* Axiom consts_wf : forall nm t, const_tys nm = Some t -> closed t. *)
(* Axiom conv_sub : forall sigma t t', conv t t' -> conv t.[sigma] t'.[sigma]. *)

(* Theorem sub_welldef sigma Delta Gamma : [Delta |+ sigma +| Gamma] -> forall t T, [Gamma |+ t :< T] -> [Delta |+ t.[sigma] :< T.[sigma]]. *)
