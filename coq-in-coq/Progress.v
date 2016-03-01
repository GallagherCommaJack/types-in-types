Require Import Unscoped Evaluation.
Theorem progress : forall e, {e' | e ==> e'} + {forall e', ~e ==> e'}.
  induction e; repeat (destr_sumors; try (destr_exists; left; eauto)); 
  try (right; inversion 1; subst; try_hyps; contradiction);
  match goal with
    | [|-context[?e1 @ ?e2]] => destruct e1
    | [|-context[srec _ _ ?e3]] => destruct e3
    | [|-context[wrec _ _ ?e3]] => destruct e3
    | [|-context[urec _ _ ?e3]] => destruct e3
    | [|-context[brec _ _ _ ?e4]] => destruct e4
  end;        
  match goal with
    | [|-context[lam _ ?b @ ?e2]] => left; exists (b |> e2 // 0); auto
    | [|-context[srec _ ?e2 (?a # ?b)]] => left; exists (e2 @ a @ b); auto
    | [|-context[wrec _ ?e2 (sup _ ?a ?f)]] => left; eauto
    | [|-context[urec _ ?u unit]] => left; exists u; auto
    | [|-context[brec _ ?t ?f true]] => left; exists t; auto
    | [|-context[brec _ _ ?f false]] => left; exists f; auto
    | _ => right; inversion 1; subst; try_hyps; contradiction
  end.
Qed.
