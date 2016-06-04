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
