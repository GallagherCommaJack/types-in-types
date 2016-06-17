Require Import Prelude.
Require Import Expr.

Notation env a := (Expr.name -> option a).
Variable (const_tys : env exp).
Variable (conv : relation exp).

Fixpoint dget {T} `{Ids T} `{Subst T} (Gamma : list T) (n : var) {struct n} : T :=
  match Gamma, n with
    | [::], _ => ids 0
    | A :: _, 0 => A.[wk 1]
    | _ :: Gamma, n.+1 => (dget Gamma n).[wk 1]
  end.

Reserved Notation "'[' C '|+' e ':<' t ']'" (at level 20).
Reserved Notation "'[' C '|+' T ']'" (at level 20).
Reserved Notation "'[' C '|+' ']'" (at level 20). 
Open Scope list_scope.
(* Definition max (i j : Univ) := match i,j with typ,_|_,typ => typ | _,_ => set end. *)
Definition imax (i j : nat) := match j with 0 => 0 | _ => max i j end.

(* Fixpoint has_type (Gamma : list exp) (e T : exp) : Prop *)
(*   match e,T with *)
(*     | Bind i,_ => (i < length Gamma) /\ (dget Gamma i = T) *)
(*     | Free nm,_ => const_tys nm = Some *)
(*     | Sort i, Sort j => i < j *)
(*     | (A :>> B), Sort k => exists i j, [Gamma |+ A :< Sort i] /\ [A :: Gamma |+ B :< Sort j] /\ imax i j < k *)
(*     | (Sigma A B), Sort k => exists i j, [Gamma |+ A :< Sort i] /\ [A :: Gamma |+ B :< Sort j] /\ imax i j < k *)
(*     | (Sum A B), Sort k => exists i j, [Gamma |+ A :< Sort i] /\ [Gamma |+ B :< Sort j] /\ i < k /\ j < k *)
(*   end *)
(* where "[ C |+ e :< t ]" := (has_type C e T). *)
Inductive has_type (Gamma : list exp) : exp ->  exp -> Prop :=
  T_bind : forall i, i < length Gamma -> [Gamma |+ Bind i :< dget Gamma i]
| T_free : forall nm t, const_tys nm = Some t -> [Gamma |+ Free nm :< t]
| T_sort : forall s, [Gamma |+ Sort s :< Sort s.+1]
(* | T_cumu : forall i j, [Gamma |+ i :< Sort j] -> [Gamma |+ i :< Sort j.+1] *)
(* | T_set : [Gamma |+ Sort set :< Sort typ] *)
| T_pi : forall A B u1 u2, [Gamma |+ A :< Sort u1] -> [(A :: Gamma) |+ B :< Sort u2] -> [Gamma |+ (A :>> B) :< Sort (imax u1 u2)]
| T_lam : forall A B b, [(A :: Gamma) |+ b :< B] -> [Gamma |+ (A :#> b) :< (A :>> B)]
| T_app : forall A B f a, [Gamma |+ f :< (A :>> B)] -> [Gamma |+ a :< A] -> [Gamma |+ (f :$: a) :< B.[a/]]
| T_sig :  forall A B u1 u2, [Gamma |+ A :< Sort u1] -> [(A :: Gamma) |+ B :< Sort u2] -> [Gamma |+ Sigma A B :< Sort (imax u1 u2)]
| T_smk : forall A B a b, [Gamma |+ a :< A] -> [Gamma |+ b :< B.[a/]] -> [Gamma |+ S_mk a b :< Sigma A B]
| T_p1  : forall A B s, [Gamma |+ s :< Sigma A B] -> [Gamma |+ S_p1 s :< A]
| T_p2  : forall A B s, [Gamma |+ s :< Sigma A B] -> [Gamma |+ S_p2 s :< B.[S_p1 s/]]

(* | T_sum : forall A B u1 u2, [Gamma |+ A :< Sort u1] -> [Gamma |+ B :< Sort u2] -> [Gamma |+ Sum A B :< Sort (max u1 u2)] *)
| T_inl : forall A B a, [Gamma |+ a :< A] -> [Gamma |+ Sum_inl a :< Sum A B]
| T_inr : forall A B b, [Gamma |+ b :< B] -> [Gamma |+ Sum_inr b :< Sum A B]
| T_split : forall P A B a b ab,
            forall n, [(Sum A B :: Gamma) |+ P :< Sort n] ->
              (* [(Sum A B :: Gamma) |+ P] -> *) 
                 [(    A   :: Gamma) |+ a              :< P.[Sum_inl (Bind 0) .: wk 1]] ->
                 [(      B :: Gamma) |+ b              :< P.[Sum_inr (Bind 0) .: wk 1]] ->
                 [            Gamma  |+ Split P a b ab :< P.[ab/]]
                     
(* | T_Unit : [Gamma |+ Unit :< Sort set] *)
| T_unit : [Gamma |+ unit :< Unit]

(* | T_Mu  : forall D, [Gamma |+ Mu D :< Sort set] *)
| T_Wrap : forall d D, [Gamma |+ d :< D_efunc D (Mu D)] -> [Gamma |+ Wrap d :< Mu D]
| T_Unwrap : forall d D, [Gamma |+ d :< Mu D] -> [Gamma |+ Unwrap d :< D_efunc D (Mu D)]
| T_mu : forall D C a d, 
         forall n, [(Mu D :: Gamma) |+ C :< Sort n] ->
           (* [(Mu D :: Gamma) |+ C] -> *)
              [Gamma   |+ a :< (D_efunc D (Mu D) :>> All n D C.[up (wk 1)] (Bind 0) :>> C.[Wrap (Bind 1) .: wk 2])] ->
              [Gamma   |+ d :< Mu D] ->
              [Gamma   |+ mu D C a d :< C.[d/]]

| T_conv : forall A A', conv A A' -> forall a, [Gamma |+ a :< A] -> [Gamma |+ a :< A']
where "[ C |+ e :< t ]" := (has_type C e t).
(* with is_type (Gamma : list exp) : exp -> Prop := *)
(*   T_typ : forall e, [Gamma |+ e :< Typ] -> [Gamma |+ e] *)
(* | T_pi : forall A B, [Gamma |+ A] -> [(A :: Gamma) |+ B] -> [Gamma |+ Pi A B] *)
(* | T_sig : forall A B, [Gamma |+ A] -> [(A :: Gamma) |+ B] -> [Gamma |+ Sigma A B] *)
(* | T_sum : forall A B, [Gamma |+ A] -> [Gamma |+ B] -> [Gamma |+ Sum A B] *)
(* | T_Mu : forall D, [Gamma |+ Mu D] *)
(* where "[ C |+ T ]" := (is_type C T). *)

Notation "[ Delta |+ sigma +| Gamma ]" := (forall x, x < size Gamma -> [Delta |+ sigma x :< (dget Gamma x).[sigma]]) (at level 20).

Lemma sub_cons_typed sigma e E Gamma Delta : [Delta |+ sigma +| Gamma] -> 
                                             [Delta |+ e :< E.[sigma]] -> 
                                             [Delta |+ e .: sigma +| E :: Gamma].
Proof. intros; destruct x; asimpl; eauto. Qed.