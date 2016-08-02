Require Import Prelude.
Require Import Expr Scoping Reduction RedScoping. 

Notation typ := exp.
Notation con := (seq exp).

Hint Resolve subtyp_cong1.
Hint Resolve leP ltP eqP.

Variable const_tys : env exp.
(* Variable (conv : relation exp). *)

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
  T_bind : forall i u, i < size Gamma -> u = dget Gamma i -> [Gamma |+ Bind i :< u]
| T_free : forall nm t, const_tys nm = Some t -> [Gamma |+ Free nm :< t]
| T_sort : forall s, [Gamma |+ Sort s :< Sort s.+1]
(* | T_cumu : forall i j, [Gamma |+ i :< Sort j] -> [Gamma |+ i :< Sort j.+1] *)
(* | T_set : [Gamma |+ Sort set :< Sort typ] *)
| T_pi : forall A B l1 l2, [Gamma |+ A :< Sort l1] -> [(A :: Gamma) |+ B :< Sort l2] -> [Gamma |+ (A :>> B) :< Sort (imax l1 l2)]
| T_lam : forall A B b, [(A :: Gamma) |+ b :< B] -> [Gamma |+ (Lam b) :< (A :>> B)]
| T_app : forall A B f a u, [Gamma |+ f :< (A :>> B)] -> [Gamma |+ a :< A] -> u = B.[a/] -> [Gamma |+ (f :$: a) :< u]
| T_sig : forall A B l1 l2, [Gamma |+ A :< Sort l1] -> [(A :: Gamma) |+ B :< Sort l2] -> [Gamma |+ Sigma A B :< Sort (imax l1 l2)]
| T_smk : forall A B a b u, [Gamma |+ a :< A] -> 
                       u = B.[a/] -> [Gamma |+ b :< u] ->
                       [Gamma |+ S_mk a b :< Sigma A B]
| T_srec : forall C A B r p u1 u2, 
             u1 = C.[S_mk (Bind 1) (Bind 0) .: wk 2] -> [B :: A :: Gamma |+ r :< u1] -> 
             [Gamma |+ p :< Sigma A B] -> 
             u2 = C.[p/] -> [Gamma |+ S_rec r p :< u2]
(* | T_p1  : forall A B s, [Gamma |+ s :< Sigma A B] -> [Gamma |+ S_p1 s :< A] *)
(* | T_p2  : forall A B s, [Gamma |+ s :< Sigma A B] -> [Gamma |+ S_p2 s :< B.[S_p1 s/]] *)

(* | T_sum : forall A B l1 l2, [Gamma |+ A :< Sort l1] -> [Gamma |+ B :< Sort l2] -> [Gamma |+ Sum A B :< Sort (max l1 l2)] *)
| T_inl : forall A B a, [Gamma |+ a :< A] -> [Gamma |+ Sum_inl a :< Sum A B]
| T_inr : forall A B b, [Gamma |+ b :< B] -> [Gamma |+ Sum_inr b :< Sum A B]
| T_split : forall P A B a b ab u1 u2 u3,
              u1 = P.[Sum_inl (Bind 0) .: wk 1] -> [(A :: Gamma) |+ a :< u1] ->
              u2 = P.[Sum_inr (Bind 0) .: wk 1] -> [(B :: Gamma) |+ b :< u2] ->
              u3 = P.[ab/] -> [Gamma |+ Split a b ab :< u3]
                     
(* | T_Unit : [Gamma |+ Unit :< Sort set] *)
| T_unit : [Gamma |+ unit :< Unit]

(* | T_Mu  : forall D, [Gamma |+ Mu D :< Sort set] *)
(* | T_Wrap : forall d D, [Gamma |+ d :< D_efunc D (Mu D)] -> [Gamma |+ Wrap d :< Mu D] *)
(* | T_Unwrap : forall d D, [Gamma |+ d :< Mu D] -> [Gamma |+ Unwrap d :< D_efunc D (Mu D)] *)
| T_mu : forall D C r d u1 u2 u3, 
         forall n, [(Mu D :: Gamma) |+ C :< Sort n] ->
           (* [(Mu D :: Gamma) |+ C] -> *)
              u1 = All D C.[up (wk 1)] (Bind 0) -> 
              u2 = C.[Bind 1 .: wk 2] ->
              [u1 :: Mu D :: Gamma |+ r :< u2] ->
              [Gamma   |+ d :< Mu D] ->
              u3 = C.[d/] ->
              [Gamma   |+ mu D r d :< u3]

(* | T_conv : forall A A', conv A A' -> forall a, [Gamma |+ a :< A] -> [Gamma |+ a :< A'] *)
| T_wrap   : forall D d, [Gamma |+ d :< D_efunc D (Mu D)] -> [Gamma |+ d :< Mu D]
| T_unwrap : forall D d u, [Gamma |+ d :< Mu D] -> u = D_efunc D (Mu D) -> [Gamma |+ d :< u]
| T_subty : forall a A A', A ::<< A' -> [Gamma |+ a :< A] -> [Gamma |+ a :< A']
where "[ C |+ e :< t ]" := (has_type C e t).

Hypothesis const_tys_vals : forall nm t e, const_tys nm = Some t /\ Reduction.const_vals nm = Some e -> [nil |+ e :< t].

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

Hypothesis const_tys_closed : forall nm e, const_tys nm = Some e -> closed e.

Hint Resolve const_tys_closed.
Hint Resolve efunc_closed.
Hint Resolve red_conv sred_cong1.

Lemma upren_dget Gamma Delta xi A : (forall v, v < size Gamma -> (dget Gamma v).[ren xi] = dget Delta (xi v)) -> 
                           forall v, v < (size Gamma).+1 -> (dget (A :: Gamma) v).[ren (upren xi)] = dget (A.[ren xi] :: Delta) (upren xi v).
Proof. simpl in *; intros; destruct v; asimpl; auto. rewrite <- H; autosubst. Qed.
Hint Resolve upren_dget.

Lemma ty_renaming xi Gamma Delta a A :
  [ Gamma |+ a :< A ] ->
  ren_scop xi (size Gamma) (size Delta) ->
  (forall v, v < size Gamma -> (dget Gamma v).[ren xi] = dget Delta (xi v)) ->
  [ Delta |+ a.[ren xi] :< A.[ren xi]].
Proof. move=>Ha; move:xi Delta; induction Ha; simpl; intros; try solve[subst;auto].
  { rewrite closed_sub_id; try eapply const_tys_closed; eassumption || auto. }
  { asimpl. constructor; try solve[eauto].
    apply IHHa2; intros; simpl in *; auto.
    eapply ren_upren; eassumption. }
  { asimpl; constructor.
    apply IHHa; intros; simpl in *; try eapply ren_upren; eassumption || auto. }
  { subst; econstructor; solve[autosubst|eauto]. }
  { constructor; try solve[eauto]; asimpl.
    apply IHHa2; intros; simpl in *; auto.
    eapply ren_upren; eassumption. }
  { subst; econstructor; try (eapply IHHa1 || eapply IHHa2; eassumption).
    autosubst. }
  { eapply T_srec with (C := C.[up (ren xi)]) (u1 := u1.[upn 2 (ren xi)]).
    { subst; autosubst. }
    { rewrite up_upren_n_internal; auto. eapply IHHa1.
      { simpl. intros. change (size Delta).+2 with (2 + size Delta). eapply ren_upnren; try eassumption. }
      { repeat rewrite iterate_S; rewrite iterate_0; auto. } }
    { simpl in *. rewrite <- up_upren_internal; auto. }
    { subst. autosubst. } }
  { asimpl; eapply T_split with (A := A.[ren xi]) (B := B.[ren xi]) (P := P.[up (ren xi)]). 
    shelve.
    { eapply IHHa1; intros; destruct v; simpl in *; auto.
      - apply H2; auto.
      - autosubst.
      - rewrite <- H3; autosubst. }
    shelve.
    { apply IHHa2; intros; destruct v; simpl in *; auto.
      - apply H2; auto.
      - autosubst.
      - rewrite <- H3; autosubst. } 
    Unshelve. subst; autosubst. subst; autosubst. subst; autosubst. }
  { specialize (IHHa1 (upren xi) (Mu D :: Delta)); specialize (IHHa2 (upnren 2 xi) (u1.[up (ren xi)] :: Mu D :: Delta)); 
    specialize (IHHa3 xi Delta); simpl in *; intuition.
    apply T_mu with (C := C.[up (ren xi)]) (u1 := u1.[up (ren xi)]) (u2 := u2.[upn 2 (ren xi)]) (n := n); 
      try solve [subst;autosubst|auto].
    { asimpl. eapply IHHa1; simpl; apply ren_upren || apply upren_dget; auto. }
    { rewrite up_upren_n_internal; auto. 
      apply IHHa2; repeat rewrite ?iterate_S ?iterate_0; simpl;
      repeat apply ren_upren; auto.
      rewrite up_upren_internal; auto.
      change (size Gamma).+2 with (size (Mu D :: Gamma)).+1.
      repeat (apply upren_dget; simpl); auto. } }
  { apply T_wrap.
    replace (D_efunc D (Mu D)) with (D_efunc D (Mu D)).[ren xi]; auto. }
  { simpl in *; apply T_unwrap with (D := D); auto.
    subst; apply closed_sub_id; auto. }
  { eauto. }
Qed.

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
Proof. induction i; move=>j sigma; rewrite ?iterate_S; solve[eauto]. Qed.

Hint Resolve closed_upn.

Lemma wk_ty A Gamma e T : [Gamma |+ e :< T] -> [A :: Gamma |+ e.[wk 1] :< T.[wk 1]]. intros; apply ty_renaming with (Gamma := Gamma); auto. Qed.
Hint Resolve wk_ty.
Lemma wk2_ty_eq A B Gamma e T u : [Gamma |+ e :< T] -> u = T.[wk 2] -> [A :: B :: Gamma |+ e.[wk 2] :< u].
Proof. intros; subst; apply ty_renaming with (Gamma := Gamma); intros; asimpl; auto.  Qed.
Hint Resolve wk2_ty_eq.
Lemma wk2_ty A B Gamma e T : [Gamma |+ e :< T] -> [A :: B :: Gamma |+ e.[wk 2] :< T.[wk 2]].
Proof. intros; subst; apply ty_renaming with (Gamma := Gamma); intros; asimpl; auto.  Qed.
Hint Resolve wk2_ty.

Lemma up_ty A Gamma Delta sigma : [Gamma |+ sigma +| Delta] -> [A.[sigma] :: Gamma |+ up sigma +| A :: Delta].
Proof. destruct x; simpl; intros; auto; asimpl; rewrite <- subst_comp; try constructor; auto. Qed.
Hint Resolve up_ty.

Hint Extern 1 (_.[_] = _.[_]) => autosubst.

Lemma sub_var_cor : forall e Delta T, [Delta |+ e :< T] -> forall sigma Gamma, [Gamma |+ sigma +| Delta] -> [Gamma |+ e.[sigma] :< T.[sigma]].
Proof. induction 1; simpl; intros; auto;
  asimpl; rewrite <- ?subst_comp; simpl in *;
  try solve [subst;auto].
  { rewrite closed_sub_id; try eapply const_tys_closed; eassumption || eauto. }
  { eapply T_app; subst; eauto. }
  { eapply T_smk; try eapply IHhas_type2; subst; auto. }
  { eapply T_srec with (A := A.[sigma]) (B := B.[up sigma]) (C := C.[up sigma]). shelve.
    { eapply IHhas_type1.
      destruct x; intros; auto; asimpl.
      - constructor; autosubst.
      - destruct x; asimpl.
        +  constructor; autosubst.
        + rewrite <- subst_comp; auto. }
    { eapply IHhas_type2; auto. }
    Unshelve. subst; autosubst. subst; autosubst. }
  { eapply T_split with (P := P.[up sigma]) (A := A.[sigma]) (B := B.[sigma]). shelve.
    { specialize (IHhas_type1 (up sigma)). asimpl in *. auto. }
    shelve.
    { specialize (IHhas_type2 (up sigma)). asimpl in *. auto. } 
    Unshelve. subst; autosubst. subst; autosubst. subst; autosubst. }
  { eapply T_mu with (C := C.[up sigma]).
    { eapply IHhas_type1. destruct x; intros.
      { asimpl. constructor; auto. }
      { asimpl; rewrite <- subst_comp; auto. } }
    shelve. shelve.
    { eapply IHhas_type2.
      destruct x; intros.
      { asimpl. rewrite <- subst_comp. constructor; simpl; auto. }
      { destruct x; asimpl.
        { constructor; auto. }
        { eapply wk2_ty_eq; eauto. } } }
    { auto. }
    Unshelve. subst; autosubst. subst; autosubst. subst; autosubst. }
  { apply T_wrap.
    replace (D_efunc D (Mu D)) with (D_efunc D (Mu D)).[sigma]; auto. }
  { eapply T_unwrap; auto.
    subst; apply closed_sub_id; auto. }
  { eauto. }
Qed.

Hint Resolve sub_var_cor.
(* Notation "x .[ sigma ]" := (map (fun y => y.[sigma]) x). *)
Hint Rewrite <- subst_comp.

Lemma sub_comp_cor Gamma Delta Sigma delta sigma : [Gamma |+ delta +| Delta] -> [Delta |+ sigma +| Sigma] -> [Gamma |+ sigma >> delta +| Sigma].
Proof. intros; asimpl; autorewrite with core; solve[eauto]. Qed.

Lemma conv_Pi A B A' B' : (A :>> B) <:::> (A' :>> B') <-> (A <:::> A') /\ (B <:::> B').
Proof. split; autorewrite with unconv; intros; destr_logic;eauto.
  autorewrite with core in *; destr_logic; subst.
  inverts H0. split; eexists; eauto. 
Qed.

Hint Rewrite conv_Pi.

Lemma T_conv Gamma e A B : A <:::> B -> [Gamma |+ e :< B] -> [Gamma |+ e :< A].
Proof. intros; eapply T_subty; try (constructor; symmetry); eassumption. Qed.

(* Lemma typed_closed Gamma e E : [Gamma |+ e :< E] -> closed_at (size Gamma) e. *)
(* Proof. induction 1; simpl in *; repeat (apply andb_true_intro; split); auto 10. Qed. *)

(* Print exp. *)

(* (* Hint Extern 1 (conv (dget (?A :: ?Delta) ?i) (dget (?A' :: ?Gamma) ?i)) => destruct i; simpl. *) *)
(* (* Theorem preservation Gamma Delta e e' T : conv_con Gamma Delta -> e ::> e' -> [Gamma |+ e :< T] -> [Delta |+ e' :< T]. *) *)
(* (* Proof. move=>Hgd He' He. move: e' He' Delta Hgd.  *) *)
(* (*   induction He; simpl; intros; destruct Hgd as [Hl Hi]; inverts He'; try (try econstructor; solve[eauto]). *) *)
(* (*   Local Hint Extern 1 (conv (dget (?A :: ?Delta) ?i) (dget (?A' :: ?Gamma) ?i)) => destruct i; simpl. *) *)
(* (*   Hint Resolve step_back_conv. *) *)
(* (*   { constructor. apply IHHe1; auto. apply IHHe2; auto; simpl; split; auto. } *) *)
(* (*   { constructor. apply IHHe1; auto. apply IHHe2; auto. simpl; split; auto. } *) *)
(* (*   { constructor. apply IHHe; auto. simpl; split; auto. } *) *)
(* (*   { constructor. apply IHHe; auto. simpl; split; auto. } *) *)
(* (*   { apply T_conv with (A := B.[a'/]); auto. apply T_app with (A := A); auto. } *) *)
(* (*   { apply T_conv with (A := B.[a'/]); auto.  *) *)
(* (*     assert (H: [Delta |+ Lam b :< (A :>> B)]) by auto. *) *)
(* (*     - eapply sub_var_cor; try eassumption. inversion H; subst; try eassumption.  *) *)