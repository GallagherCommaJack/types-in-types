Require Import Coq.Program.Program Coq.Classes.RelationClasses Omega.
Require Import mathcomp.ssreflect.all_ssreflect.
Require Import Relation_Definitions Relation_Operators.
Require Export Omega.
Ltac destr_sums :=
  match goal with
    | [ H :  _  + {_} |- _ ] => destruct H
    | [ H :  _  +  _  |- _ ] => destruct H
    | [ H : {_} + {_} |- _ ] => destruct H
  end.

Ltac destr_ors := match goal with [H: _\/_|-_] => destruct H end.
Ltac destr_ands := match goal with [H: _/\_|-_] => destruct H end.
Ltac destr_prods := match goal with [H: {_|_}|-_] => destruct H | [H: _*_|-_] => destruct H end.
Ltac destr_exists := match goal with [H: exists _,_ |- _] => destruct H end.
Ltac destr_logic := repeat (destr_exists || destr_ands || destr_ors).
Ltac destr_safe := repeat (destr_prods || destr_sums).
Ltac destr_hyps := destr_safe; destr_logic.

Ltac Inster_all := repeat
  match goal with
    | [ H : forall x : ?T, _ |- _ ] =>
      let x := fresh "x" in
      evar (x : T);
        let x' := eval unfold x in x in
            clear x; specialize (H x')
  end.

Ltac destr_goal_if :=
  match goal with 
    | [|- context[if ?c then _ else _]] => 
      let C := fresh "C" in
      remember c as C; destruct C; simpl
  end.

Ltac destr_goal_sum :=
  match goal with
    | [|- context[?s]] => match type of s with
                            | _ + _ => destruct s
                            | {_} + {_} => destruct s
                            | _ + {_} => destruct s
                          end
  end.

Tactic Notation "destr_choices" := repeat (destr_goal_if || destr_goal_sum; simpl).

Ltac notHyp P :=
  match goal with
    | [ _ : P |- _ ] => fail 1
    | _ =>
      match P with
        | ?P1 /\ ?P2 => first [ notHyp P1 | notHyp P2 | fail 2 ]
        | _ => idtac
      end
  end.

Ltac extend pf :=
  let t := type of pf in
    notHyp t; generalize pf; intro.

Ltac try_hyps := 
  repeat match goal with
           | [IH: forall e, ?P e -> _ , H: ?P _ |- _] => extend (IH H) || extend (IH _ H)
           | [IH: ?P -> _ , H: ?P |- _] => extend (IH H) 
           | [IH: ?P <-> ?Q, H: ?P |- _] => extend (proj1 IH H)
           | [IH: ?P <-> ?Q, H: ?Q |- _] => extend (proj2 IH H)
           | [H: forall (e : ?T), _ , e : ?T |- _] => extend (H e)
         end.

Ltac clear_funs :=
  repeat match goal with [H: forall e, _ |- _] => clear H | [H: _ -> _ |- _] => clear H | [H: _ <-> _ |- _] => clear H end.

Tactic Notation "test" tactic(tac) := tryif tac then fail "success" else fail "failure".
Tactic Notation "not" tactic(tac) := tryif tac then fail else idtac.

(** [atomic x] is the same as [idtac] if [x] is a Variable or hypothesis, but is [fail 0] if [x] has internal structure. *)
Ltac atomic x :=
  match x with
    | _ => is_evar x; fail 1 x "is not atomic (evar)"
    | ?f _ => fail 1 x "is not atomic (Application)"
    | (fun _ => _) => fail 1 x "is not atomic (fun)"
    | forall _, _ => fail 1 x "is not atomic (forall)"
    | let x := _ in _ => fail 1 x "is not atomic (let in)"
    | match _ with _ => _ end => fail 1 x "is not atomic (match)"
    | _ => is_fix x; fail 1 x "is not atomic (fix)"
    | context[?E] => (* catch-all *) (not constr_eq E x); fail 1 x "is not atomic (has subterm" E ")"
    | _ => idtac
  end.

Tactic Notation "solve_by_inversion_step" tactic(t) :=
  match goal with [H : _ |- _] => solve [ inversion H; subst; t ] end
    || fail "goal is not solvable by inversion".

Tactic Notation "solve" "by" "inversion" "1" :=
  solve_by_inversion_step idtac.
Tactic Notation "solve" "by" "inversion" "2" :=
  solve_by_inversion_step (solve by inversion 1).
Tactic Notation "solve" "by" "inversion" "3" :=
  solve_by_inversion_step (solve by inversion 2).
Tactic Notation "solve" "by" "inversion" :=
  solve by inversion 1.

Tactic Notation "inverts" ident(H) := inversion H; clear H; subst.

Tactic Notation "rewrite" "assumption" ident(H) := rewrite H; try assumption.
Tactic Notation "rewrite" "asms" := repeat match goal with [H:_|-_] => rewrite assumption H end.

Tactic Notation "destr" "bands" := 
  repeat match goal with
           | [H: _ && _|-_] => apply andb_prop in H; destruct H
           | [H: _ && _ = true |- _] => apply andb_prop in H; destruct H
         end.

Tactic Notation "htry" :=
  repeat match goal with
             [H: ?P -> _, H2 : ?P |- _] => extend (H H2)
           | [H1: forall e, _, H2 : _ |- _] =>
             extend (H1 _ H2) || extend (H1 _ _ H2)
         end.

Tactic Notation "eauto" "rst" := eauto using clos_refl_sym_trans.
Tactic Notation "eauto" "rst" integer(n) := eauto n using clos_refl_sym_trans.

Hint Resolve ltP leP eqP.
Lemma reflect_iff P p : reflect P p -> p <-> P. destruct 1; split; auto; congruence. Qed.
Hint Rewrite reflect_iff using solve [eauto] : bprop.
Hint Rewrite <- reflect_iff using solve [eauto] : unprop.
Ltac conv_to_prop := autorewrite with bprop in *.
Ltac conv_from_prop := autorewrite with unprop in *.

Ltac bdestruct X :=
  let H := fresh in 
  let e := fresh "e" in
  evar (e: Prop); assert (H: reflect e X); subst e;
  [eauto
  | destruct H as [H|H]].

Tactic Notation "destruct" "match" := match goal with [|-context[match ?e with _ => _ end]] => destruct e end.
