Require Export Fin.
Require Import Omega.

Hint Resolve le_plus_l le_plus_r le_plus_trans.
Set Implicit Arguments.

Inductive exp (depth : nat) : Set :=
| var : fin depth -> exp depth
(* universes *)
| prop : exp depth
| set : nat -> exp depth
(* pi types *)
| pi : exp depth -> exp (S depth) -> exp depth
| lam : exp (S depth) -> exp depth
| app : exp depth -> exp depth -> exp depth
(* sigma types *)
| sg : exp depth -> exp (S depth) -> exp depth
| prd : exp depth -> exp depth -> exp depth
| src : exp (S depth) -> exp (2 + depth) -> exp depth -> exp depth
(* w types *)
| wt : exp depth -> exp (S depth) -> exp depth
| sup : exp depth -> exp (S depth) -> exp depth
| wrc : exp (S depth) -> exp (3 + depth) -> exp depth -> exp depth
(* concrete types *)
(* booleans *)
| bool : exp depth
| true : exp depth
| false : exp depth
| brc : exp (S depth) -> exp depth -> exp depth -> exp depth -> exp depth
(* top *)
| top : exp depth
| unt : exp depth
| trc : exp (S depth) -> exp depth -> exp depth -> exp depth
(* bottom *)
| bot : exp depth
| exf : exp (S depth) -> exp depth -> exp depth.

(* Does horrible things to definitional equalities due to big proof terms *)
(*
Local Hint Extern 1 => destr_fins; simpl in *.
Local Hint Extern 1 => omega.
*)

Arguments prop {depth}.
Arguments set {depth} n.
Arguments bool {depth}.
Arguments true {depth}.
Arguments false {depth}.
Arguments top {depth}.
Arguments unt {depth}.
Arguments bot {depth}.

Fixpoint size {n} (e : exp n) : nat :=
  match e with
    | var v => 2
    | set n => 2

    | pi a b => 1 + size a + size b
    | lam b => 1 + size b
    | app f x => 1 + size f + size x

    | sg a b => 1 + size a + size b
    | prd a b => 1 + size a + size b
    | src c f p => 1 + size c + size f + size p

    | wt a b => 1 + size a + size b
    | sup a f => 1 + size a + size f
    | wrc c s w => 1 + size c + size s + size w
    
    | brc c t f b => 1 + size c + size t + size f + size b
    | trc c t u => 1 + size c + size t + size u
    | exf c f => 1 + size c + size f

    | _ => 1
  end.

Program Fixpoint m_lift_deep n {dep} (ix : nat) (t : exp dep) : exp (n + dep) :=
  match t with
    | var v => if le_dec ix v then var (n + v) else var v

    | prop => prop
    | set n => set n

    | pi a b => pi (m_lift_deep n ix a) (m_lift_deep n (S ix) b)
    | lam b => lam (m_lift_deep n (S ix) b)
    | app f x => app (m_lift_deep n ix f) (m_lift_deep n ix x)

    | sg a b => sg (m_lift_deep n ix a) (m_lift_deep n (S ix) b)
    | prd a b => prd (m_lift_deep n ix a) (m_lift_deep n ix b)
    | src c f p => src (m_lift_deep n (S ix) c) (m_lift_deep n (2 + ix) f) (m_lift_deep n ix p)

    | wt a b => wt (m_lift_deep n ix a) (m_lift_deep n (S ix) b)
    | sup a f => sup (m_lift_deep n ix a) (m_lift_deep n (S ix) f)
    | wrc c s w => wrc (m_lift_deep n (S ix) c) (m_lift_deep n (3 + ix) s) (m_lift_deep n ix w)

    | bool => bool
    | true => true
    | false => false
    | brc c t f b => brc (m_lift_deep n (S ix) c) (m_lift_deep n ix t) (m_lift_deep n ix f) (m_lift_deep n ix b)

    | top => top
    | unt => unt
    | trc c t u => trc (m_lift_deep n (S ix) c) (m_lift_deep n ix t) (m_lift_deep n ix u)

    | bot => bot
    | exf c f => exf (m_lift_deep n (S ix) c) (m_lift_deep n ix f)
  end.

Program Fixpoint subst_deep {n} (d : fin (S n)) (v : exp (finvert d)) (e : exp (S n)) : exp n :=
  match e with
    | var i => match lt_eq_lt_dec d i with
                | inleft (left Hlt) => var (pred i)
                | inleft (right Heq) => m_lift_deep d 0 v
                | inright Hgt => var i
              end

    | prop => prop
    | set n => set n

    | pi a b => pi (subst_deep d v a) (subst_deep (fsu d) v b)
    | lam b => lam (subst_deep (fsu d) v b)
    | app f x => app (subst_deep d v f) (subst_deep d v x)

    | sg a b => sg (subst_deep d v a) (subst_deep (S d) v b)
    | prd a b => prd (subst_deep d v a) (subst_deep d v a)
    | src c f p => src (subst_deep (fsu d) v c) (subst_deep (fsu (fsu d)) v f) (subst_deep d v p)

    | wt a b => wt (subst_deep d v a) (subst_deep (fsu d) v b)
    | sup a f => sup (subst_deep d v a) (subst_deep (fsu d) v f)
    | wrc c s w => wrc (subst_deep (fsu d) v c) (subst_deep (fsu (fsu (fsu d))) v s) (subst_deep d v w)

    | bool => bool
    | true => true
    | false => false
    | brc c t f b => brc (subst_deep (fsu d) v c) (subst_deep d v t) (subst_deep d v f) (subst_deep d v b)

    | top => top
    | unt => unt
    | trc c t u => trc (subst_deep (fsu d) v c) (subst_deep d v t) (subst_deep d v u)

    | bot => bot
    | exf c f => exf (subst_deep (fsu d) v c) (subst_deep d v f)
  end.

Notation "e [ v / i ]" := (subst_deep i v e) (at level 300).

Inductive con : nat -> Set :=
| nil : con 0
| cons : forall {n} (Gamma : con n), exp n -> con (S n).

Program Fixpoint lookup {n} (i : fin n) (Gamma : con n) : exp (n - S i) :=
  match Gamma with
    | nil => False_rect _ _
    | cons Gamma' X => match i with
                        | 0 => X
                        | S i' => lookup (mk_fin i' _) Gamma'
                      end
  end.


