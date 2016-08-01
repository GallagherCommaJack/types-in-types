Require Import Prelude.
Require Import Expr.
Require Import Scoping.
Hint Resolve leP ltP eqP.

Fixpoint map_with_ix {A B} (f : nat -> A -> B) (xs : seq A) : seq B :=
  match xs with
      [] => []
    | x :: xs' => f 0 x :: map_with_ix (fun n a => f n.+1 a) xs'
  end.

Lemma map_with_ix_funext {A B} xs : forall (f g : nat -> A -> B), (forall n a, f n a = g n a) -> map_with_ix f xs = map_with_ix g xs.
  induction xs; intros; simpl; f_equal; auto. Qed.
Hint Rewrite @map_with_ix_funext using solve [eauto].
Hint Rewrite @iterate_S @iterate_0.

Ltac bdestruct X :=
  let H := fresh in 
  let e := fresh "e" in
  evar (e: Prop); assert (H: reflect e X); subst e;
  [eauto
  | destruct H as [H|H]].

Require Import Omega.

Lemma reflect_iff P p : reflect P p -> p <-> P. destruct 1; split; auto; congruence. Qed.
Hint Rewrite reflect_iff using solve [eauto] : bprop.
Hint Rewrite <- reflect_iff using solve [eauto] : unprop.
Ltac conv_to_prop := autorewrite with bprop in *.
Ltac conv_from_prop := autorewrite with unprop in *.

Goal forall x y z, x < y -> y < z -> x < z. intros. conv_to_prop. omega. Qed.

Notation env a := (Expr.name -> option a).
Variable (const_tys : env exp).
Variable (conv : relation exp).

(* Notation dget Gamma n := (nth (ids 0) Gamma n).[wk n.+1]. *)
Fixpoint dget {T} `{Ids T} `{Subst T} (Gamma : seq T) (n : var) {struct n} : T :=
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
(*     | Bind i,_ => (i < size Gamma) /\ (dget Gamma i = T) *)
(*     | Free nm,_ => const_tys nm = Some *)
(*     | Sort i, Sort j => i < j *)
(*     | (A :>> B), Sort k => exists i j, [Gamma |+ A :< Sort i] /\ [A :: Gamma |+ B :< Sort j] /\ imax i j < k *)
(*     | (Sigma A B), Sort k => exists i j, [Gamma |+ A :< Sort i] /\ [A :: Gamma |+ B :< Sort j] /\ imax i j < k *)
(*     | (Sum A B), Sort k => exists i j, [Gamma |+ A :< Sort i] /\ [Gamma |+ B :< Sort j] /\ i < k /\ j < k *)
(*   end *)
(* where "[ C |+ e :< t ]" := (has_type C e T). *)

Inductive has_type (Gamma : seq exp) : exp ->  exp -> Prop :=
  T_bind : forall i, i < size Gamma -> [Gamma |+ Bind i :< dget Gamma i]
| T_free : forall nm t, const_tys nm = Some t -> [Gamma |+ Free nm :< t]
| T_sort : forall s, [Gamma |+ Sort s :< Sort s.+1]
| T_cumu : forall i j, [Gamma |+ i :< Sort j] -> [Gamma |+ i :< Sort j.+1]
(* | T_set : [Gamma |+ Sort set :< Sort typ] *)
| T_pi : forall A B u1 u2, [Gamma |+ A :< Sort u1] -> [(A :: Gamma) |+ B :< Sort u2] -> [Gamma |+ (A :>> B) :< Sort (imax u1 u2)]
| T_lam : forall A B b, [(A :: Gamma) |+ b :< B] -> [Gamma |+ (Lam b) :< (A :>> B)]
| T_app : forall A B f a, [Gamma |+ f :< (A :>> B)] -> [Gamma |+ a :< A] -> [Gamma |+ (f :$: a) :< B.[a/]]
| T_sig :  forall A B u1 u2, [Gamma |+ A :< Sort u1] -> [(A :: Gamma) |+ B :< Sort u2] -> [Gamma |+ Sigma A B :< Sort (imax u1 u2)]
| T_smk : forall A B a b, [Gamma |+ a :< A] -> [Gamma |+ b :< B.[a/]] -> [Gamma |+ S_mk a b :< Sigma A B]
| T_p1  : forall A B s, [Gamma |+ s :< Sigma A B] -> [Gamma |+ S_p1 s :< A]
| T_p2  : forall A B s, [Gamma |+ s :< Sigma A B] -> [Gamma |+ S_p2 s :< B.[S_p1 s/]]

(* | T_sum : forall A B u1 u2, [Gamma |+ A :< Sort u1] -> [Gamma |+ B :< Sort u2] -> [Gamma |+ Sum A B :< Sort (max u1 u2)] *)
| T_inl : forall A B a, [Gamma |+ a :< A] -> [Gamma |+ Sum_inl a :< Sum A B]
| T_inr : forall A B b, [Gamma |+ b :< B] -> [Gamma |+ Sum_inr b :< Sum A B]
| T_split : forall P A B a b ab,
            (* forall n, [(Sum A B :: Gamma) |+ P :< Sort n] -> *)
              (* [(Sum A B :: Gamma) |+ P] -> *) 
                 [(    A   :: Gamma) |+ a              :< P.[Sum_inl (Bind 0) .: wk 1]] ->
                 [(      B :: Gamma) |+ b              :< P.[Sum_inr (Bind 0) .: wk 1]] ->
                 (* [            Gamma  |+ Split P a b ab :< P.[ab/]] *)
                 [            Gamma  |+ Split a b ab   :< P.[ab/]]
                     
(* | T_Unit : [Gamma |+ Unit :< Sort set] *)
| T_unit : [Gamma |+ unit :< Unit]

(* | T_Mu  : forall D, [Gamma |+ Mu D :< Sort set] *)
(* | T_Wrap : forall d D, [Gamma |+ d :< D_efunc D (Mu D)] -> [Gamma |+ Wrap d :< Mu D] *)
(* | T_Unwrap : forall d D, [Gamma |+ d :< Mu D] -> [Gamma |+ Unwrap d :< D_efunc D (Mu D)] *)
| T_mu : forall D C a d, 
         forall n, [(Mu D :: Gamma) |+ C :< Sort n] ->
           (* [(Mu D :: Gamma) |+ C] -> *)
              [Gamma   |+ a :< (Mu D :>> (All D C.[up (wk 1)] (Bind 0) :>> C.[Bind 1 .: wk 2]))] ->
              [Gamma   |+ d :< Mu D] ->
              [Gamma   |+ mu D a d :< C.[d/]]

| T_conv : forall A A', conv A A' -> forall a, [Gamma |+ a :< A] -> [Gamma |+ a :< A']
where "[ C |+ e :< t ]" := (has_type C e t).

(* Fixpoint has_type_rec (Gamma : list exp) (e : exp) (T : exp) : Prop := *)
(*   match e with *)
(*     | Bind i => (i < ⟦Gamma⟧) /\ conv T (dget Gamma i) *)
(*     | Free nm => exists t, const_tys nm = Some t /\ conv T t *)
(*     | Sort i => exists j, i < j /\ conv T (Sort j) *)
(*     | A :>> B => exists i j k, has_type_rec Gamma A (Sort i) /\ has_type_rec (A :: Gamma) B (Sort j) /\ k > imax i j /\ conv T (Sort k) *)
(*     | Lam b => exists A B, has_type_rec (A :: Gamma) b B /\ conv T (A :>> B) *)
(*     | _ => False *)
(*   end. *)
(* with is_type (Gamma : list exp) : exp -> Prop := *)
(*   T_typ : forall e, [Gamma |+ e :< Typ] -> [Gamma |+ e] *)
(* | T_pi : forall A B, [Gamma |+ A] -> [(A :: Gamma) |+ B] -> [Gamma |+ Pi A B] *)
(* | T_sig : forall A B, [Gamma |+ A] -> [(A :: Gamma) |+ B] -> [Gamma |+ Sigma A B] *)
(* | T_sum : forall A B, [Gamma |+ A] -> [Gamma |+ B] -> [Gamma |+ Sum A B] *)
(* | T_Mu : forall D, [Gamma |+ Mu D] *)
(* where "[ C |+ T ]" := (is_type C T). *)

Notation "[ Delta |+ sigma +| Gamma ]" := (forall x, x < size Gamma -> [Delta |+ sigma x :< (dget Gamma x).[sigma]]) (at level 20).

Lemma sub_cons_var sigma e E Gamma Delta : [Delta |+ sigma +| Gamma] -> 
                                             [Delta |+ e :< E.[sigma]] -> 
                                             [Delta |+ e .: sigma +| E :: Gamma].
Proof. intros; destruct x; asimpl; eauto. Qed.

Hint Constructors has_type.
Lemma sub_id_ref : forall Gamma, [Gamma |+ ids +| Gamma]. intros; asimpl; auto. Qed.
Lemma sub_wk_var : forall Gamma A, [A :: Gamma |+ wk 1 +| Gamma]. intros; asimpl; constructor; auto. Qed.

Hint Resolve sub_id_ref sub_wk_var sub_cons_var.

Lemma dget_nth : forall Gamma n, n <  size Gamma -> dget Gamma n = (nth (ids 0) Gamma n).[wk n.+1].
  induction Gamma; simpl.
  { inversion 1. }
  { intros. destruct n; simpl; auto. 
    rewrite IHGamma; autosubst. }
Qed.
  
Functional Scheme sub_ind := Induction for minus Sort Prop.

Notation ren_scop xi i j := (forall v, v < i -> xi v < j).

Lemma All_sub D : forall sigma C e, (All D C e).[sigma] = All D C.[up sigma] e.[sigma].
  induction D; intros; simpl; rewrite asms; 
  try replace C.[up (wk 1)].[up (up sigma)] with C.[up sigma].[up (wk 1)]; autosubst. Qed.

Hint Resolve All_sub.
Hint Rewrite All_sub.


Lemma ty_renaming xi Gamma Delta a A :
  [ Gamma |+ a :< A ] ->
  ren_scop xi (size Gamma) (size Delta) ->
  (forall v, v < size Gamma -> (dget Gamma v).[ren xi] = dget Delta (xi v)) ->
  [ Delta |+ a.[ren xi] :< A.[ren xi]].
Proof. move=>Ha; move:xi Delta; induction Ha; simpl; intros; try solve[eauto].
       { rewrite H1; auto. }
       { admit. }                (* needs closure properties for env *)
       { asimpl. constructor; try solve[eauto].
         apply IHHa2; intros; simpl in *; auto.
         destruct v; simpl; solve[eauto].
         destruct v; asimpl; auto.
         rewrite <- H0; autosubst. }
       { asimpl. constructor; try solve[eauto].
         apply IHHa; intros; simpl in *; auto.
         destruct v; simpl; solve[eauto].
         destruct v; asimpl; auto.
         rewrite <- H0; autosubst. }
       { replace B.[a/].[ren xi] with B.[up (ren xi)].[a.[ren xi]/] by autosubst.
         econstructor; solve[eauto]. }
       { asimpl. constructor; try solve[eauto].
         apply IHHa2; intros; simpl in *; auto.
         destruct v; simpl; solve[eauto].
         destruct v; asimpl; auto.
         rewrite <- H0; autosubst. }
       { asimpl; constructor; auto.
         replace B.[ren (upren xi)].[a.[ren xi]/] with B.[a/].[ren xi] by autosubst; solve[eauto]. }
       { replace B.[S_p1 s/].[ren xi] with B.[up (ren xi)].[S_p1 s.[ren xi]/] by autosubst.
         apply T_p2 with (A := A.[ren xi]); auto. apply IHHa; auto. }
       { asimpl.
         replace P.[ab.[ren xi] .: ren xi] with P.[ren (upren xi)].[ab.[ren xi]/] by autosubst.
         apply T_split with (A := A.[ren xi]) (B := B.[ren xi]);
         match goal with [|- context[P.[?x].[?t .: ?r]]] => 
                         replace P.[x].[t .: r] with P.[t .: r].[x] by autosubst end.
         { apply IHHa1; intros; destruct v; simpl in *; auto.
           - apply H; auto.
           - replace A.[wk 1].[ren (upren xi)] with A.[ren xi].[wk 1] by autosubst; reflexivity.
           - rewrite <- H0; autosubst. }
         { apply IHHa2; intros; destruct v; simpl in *; auto.
           - apply H; auto.
           - replace B.[wk 1].[ren (upren xi)] with B.[ren xi].[wk 1] by autosubst; reflexivity.
           - rewrite <- H0; autosubst. } }
       { replace C.[d/].[ren xi] with C.[ren (upren xi)].[d.[ren xi]/] by autosubst.
         specialize (IHHa1 (upren xi) (Mu D :: Delta)). specialize (IHHa2 xi Delta H H0). specialize (IHHa3 xi Delta H H0).
         simpl in *. rewrite All_sub in IHHa2.
         econstructor; auto.
         - apply IHHa1; auto; destruct v; simpl in *; intros; auto; apply H || rewrite <- H0; autosubst.           
         - asimpl; asimpl in IHHa2; exact IHHa2. }
       { admit. }               (* needs conv sub props *)
Admitted.
(* CURRENT POINT *)
Lemma wk_i_up_jk : forall i j k, sub_eq (wk i >> upn j (wk k)) (upn (j - i) (wk k) >> wk i).
  intros i j.
  refine (sub_ind (fun j i ij => forall k, sub_eq (wk i >> upn j (wk k)) (upn ij (wk k) >> wk i)) _ _ _ j i); 
    intros; subst.
  { asimpl; f_equal; omega. }
  { autosubst. }
  { replace ((wk l.+1 >> upn k.+1 (wk k0)) v) with ((wk l >> upn k (wk k0)) v).[wk 1] by autosubst.
    rewrite H; autosubst. }
Qed.

Hint Resolve wk_i_up_jk.

(* Hint Rewrite sub_vars_tms using solve[eauto]. *)

Lemma closed_upn : forall i j sigma, closed_sub j sigma -> closed_sub (i + j) (upn i sigma).
  induction i; move=>j sigma; rewrite ?iterate_S; solve[eauto]. Qed.

Hint Resolve closed_upn.

Lemma wk_ty A Gamma e T : [Gamma |+ e :< T] -> [A :: Gamma |+ e.[wk 1] :< T.[wk 1]]. intros; apply ty_renaming with (Gamma := Gamma); auto. Qed.
Hint Resolve wk_ty.

Lemma up_ty A Gamma Delta sigma : [Gamma |+ sigma +| Delta] -> [A.[sigma] :: Gamma |+ up sigma +| A :: Delta].
Proof. destruct x; simpl; intros; auto; asimpl; rewrite <- subst_comp; try constructor; auto. Qed.
Hint Resolve up_ty.

Hint Extern 1 (_.[_] = _.[_]) => autosubst.

Lemma sub_var_cor : forall e Delta T, [Delta |+ e :< T] -> forall sigma Gamma, [Gamma |+ sigma +| Delta] -> [Gamma |+ e.[sigma] :< T.[sigma]].
Proof. induction 1; simpl; intros; auto;
  asimpl; rewrite <- ?subst_comp;
  try solve [eauto].
  { admit. }               (* free vars need closure properties *)
  { replace B.[a.[sigma] .: sigma] with B.[up sigma].[a.[sigma]/]; solve[eauto]. }
  { econstructor; try replace B.[up sigma].[a.[sigma]/] with B.[a/].[sigma]; solve[auto]. }
  { replace B.[S_p1 s.[sigma] .: sigma] with B.[up sigma].[S_p1 s.[sigma]/]; solve[eauto]. }
  { replace P.[ab.[sigma] .: sigma] with P.[up sigma].[ab.[sigma]/] by autosubst. 
    econstructor. 
    { specialize (IHhas_type1 (up sigma)). asimpl in *. auto. }
    { specialize (IHhas_type2 (up sigma)). asimpl in *. auto. } }
  { replace C.[d.[sigma] .: sigma] with C.[up sigma].[d.[sigma]/]; auto. econstructor; try solve[eauto].
    { eapply IHhas_type1. destruct x; intros.
      { asimpl. constructor; auto. }
      { asimpl; rewrite <- subst_comp; auto. } }
    { replace C.[up sigma].[Bind 1 .: wk 2] with C.[Bind 1 .: wk 2].[up (up sigma)] by autosubst.
      replace C.[up sigma].[up (wk 1)] with C.[up (wk 1)].[up (up sigma)] by autosubst.
      replace (Mu D :>> (All D C.[up (wk 1)].[up (up sigma)] (Bind 0) :>> C.[Bind 1 .: wk 2].[up (up sigma)]))
      with (Mu D :>> (All D C.[up (wk 1)] (Bind 0) :>> C.[Bind 1 .: wk 2]).[up sigma]) 
        by (asimpl; rewrite All_sub; autosubst).
      eauto. } }
  { admit. }               (* conv property *)
Admitted.

Hint Resolve sub_var_cor.
(* Notation "x .[ sigma ]" := (map (fun y => y.[sigma]) x). *)
Hint Rewrite <- subst_comp.

Lemma sub_comp_cor Gamma Delta Sigma delta sigma : [Gamma |+ delta +| Delta] -> [Delta |+ sigma +| Sigma] -> [Gamma |+ sigma >> delta +| Sigma].
Proof. intros; asimpl; autorewrite with core; solve[eauto]. Qed.

Require Import Reduction.

Notation conv_con Gamma Delta := (size Gamma = size Delta /\ forall i, conv (dget Delta i) (dget Gamma i)). 

Hypothesis step_conv : forall e e', e ::> e' -> conv e e'.
Hypothesis step_back_conv : forall e e', e ::> e' -> conv e' e.
Hypothesis conv_refl : forall e, conv e e.
Hypothesis conv_trans : forall e e' e'', conv e e' -> conv e' e'' -> conv e e''.
Hypothesis conv_symm : forall e e', conv e e' -> conv e' e.
Hypothesis conv_sub_congr1 : forall e e' sigma, conv e e' -> conv e.[sigma] e'.[sigma].
Hypothesis conv_sub_congr : forall e e' sigma tau, sigma .>> tau -> conv e.[sigma] e'.[tau].
Hint Resolve conv_refl conv_sub_congr1.
Hint Resolve step_conv.

Lemma lam_pi Gamma A B b : [Gamma |+ Lam b :< A :>> B] -> [A :: Gamma |+ b :< B].
Proof. remember (Lam b) as lb; remember (A :>> B) as ab.
  induction 1; inversion Heqlb; inversion Heqab; subst; auto.
(* Hint Extern 1 (conv (dget (?A :: ?Delta) ?i) (dget (?A' :: ?Gamma) ?i)) => destruct i; simpl. *)
Theorem preservation Gamma Delta e e' T : conv_con Gamma Delta -> e ::> e' -> [Gamma |+ e :< T] -> [Delta |+ e' :< T].
Proof. move=>Hgd He' He. move: e' He' Delta Hgd. 
  induction He; simpl; intros; destruct Hgd as [Hl Hi]; inverts He'; try (try econstructor; solve[eauto]).
  Local Hint Extern 1 (conv (dget (?A :: ?Delta) ?i) (dget (?A' :: ?Gamma) ?i)) => destruct i; simpl.
  Hint Resolve step_back_conv.
  { constructor. apply IHHe1; auto. apply IHHe2; auto; simpl; split; auto. }
  { constructor. apply IHHe1; auto. apply IHHe2; auto. simpl; split; auto. }
  { constructor. apply IHHe; auto. simpl; split; auto. }
  { constructor. apply IHHe; auto. simpl; split; auto. }
  { apply T_conv with (A := B.[a'/]); auto. apply T_app with (A := A); auto. }
  { apply T_conv with (A := B.[a'/]); auto. 
    assert (H: [Delta |+ Lam b :< (A :>> B)]) by auto.
    - eapply sub_var_cor; try eassumption. inversion H; subst; try eassumption. 
    - 