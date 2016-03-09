Require Import Tactics.
Require Import Coq.Program.Program.

Class Functor (F: Type -> Type) := {
    fmap : forall{A B}, (A -> B) -> F A -> F B
  ; hom_id : forall{A}(x: F A), fmap id x = x
  ; hom_comp : forall{A B C}(f: A -> B)(g: B -> C)(x: F A), fmap (g ∘ f) x = fmap g (fmap f x)
}.

Infix "<$>" := fmap (left associativity, at level 25).

Class Monad (M: Type -> Type) := {
    functor :> Functor M
  ; pure : forall{A}, A -> M A
  ; join : forall{A}, M (M A) -> M A
  ; pure_nat : forall{A B}(f: A -> B)(a: A), fmap f (pure a) = pure (f a)
  ; join_nat : forall{A B}(f: A -> B)(x: M(M A)), join (fmap (fmap f) x) = fmap f (join x)
  ; join_pure_l : forall{A}(x: M A), join (pure x) = x
  ; join_pure_r : forall{A}(x: M A), join (fmap pure x) = x
  ; join_assoc : forall{A}(x: M(M(M A))), join (join x) = join (fmap join x)
}.

Hint Resolve hom_id hom_comp pure_nat join_nat join_pure_l join_pure_r join_assoc.

Definition bind {M} `{Monad M} {A B} (f: A -> M B) : M A -> M B := join ∘ fmap f.
Infix ">>=" := (flip bind) (left associativity, at level 50).
Definition mapp {M} `{Monad M} {A B} (mf: M (A -> B)) : M A -> M B := fun a => mf >>= fun f => fmap f a.
Infix "<*>" := mapp (left associativity, at level 25).


(* Instances *)

Definition option_fmap A B (f: A -> B) x : option B := match x with None => None | Some a => Some (f a) end.
Local Obligation Tactic := program_simpl; match goal with [x: option _|-_] => destruct x; auto end.
Program Instance option_functor : Functor option := {
    fmap := option_fmap
}.

Definition option_join A x : option A := match x with None => None | Some a => a end.

Program Instance option_monad : Monad option := {
    pure := @Some
  ; join := option_join
}.

Open Scope list_scope.
Local Obligation Tactic := program_simpl.
Program Instance list_functor : Functor list := { fmap := List.map }.
Obligation 1. induction x as [|x xs]; auto. simpl; f_equal; assumption. Qed.
Obligation 2. induction x as [|x xs]; auto. simpl; f_equal; assumption. Qed.

Local Hint Resolve List.concat_map List.app_nil_r.

Program Instance list_monad : Monad list := { pure A a := [ a ] ; join := List.concat }.
Next Obligation. induction x; simpl; f_equal; assumption. Qed.
Next Obligation. induction x; [|simpl;rewrite List.concat_app]; f_equal; assumption. Qed.

Local Hint Extern 1 => destr_sums.
Local Obligation Tactic := auto; program_simpl; auto.
Program Instance sumor_functor (P: Prop) : Functor (fun A => A + {P}).
Program Instance sumor_monad (P: Prop) : Monad (fun A => A + {P}).

Program Instance sum_functor_r (A: Type) : Functor (sum A).
Program Instance sum_monad_r (A: Type) : Monad (sum A).

Program Instance sum_functor_l (A: Type) : Functor (fun B => sum B A).
Program Instance sum_monad_l (A: Type) : Monad (fun B => sum B A).

Program Instance hom_functor (A: Type) : Functor (fun B => A -> B).
Program Instance hom_monad (A: Type) : Monad (fun B => A -> B).

Program Instance prod_functor_r (A: Type) : Functor (prod A).
Program Instance prod_functor_l (A: Type) : Functor (fun B => prod B A).

Notation "x <- e ; e'" := (e >>= fun x => e') (right associativity, at level 60).