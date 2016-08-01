Require Import Prelude.
Require Import Expr. 
Require Import Scoping. 
Require Import Reduction.

Notation typ := exp.
Notation con := (seq exp).
Inductive subtyp : typ -> typ -> Prop :=
| sub_conv : forall T1 T2, T1 <:::> T2 -> subtyp T1 T2
| sub_cumu : forall T1 l1 l2 T2, T1 <:::> (Sort l1) -> T2 <:::> (Sort l2) -> l1 < l2 -> subtyp T1 T2.

Hint Constructors subtyp.
Infix "::<" := subtyp (at level 20).

Hint Resolve sub_conv.
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
  T_bind : forall i, i < size Gamma -> [Gamma |+ Bind i :< dget Gamma i]
| T_free : forall nm t, const_tys nm = Some t -> [Gamma |+ Free nm :< t]
| T_sort : forall s, [Gamma |+ Sort s :< Sort s.+1]
(* | T_cumu : forall i j, [Gamma |+ i :< Sort j] -> [Gamma |+ i :< Sort j.+1] *)
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
                 [            Gamma  |+ ab             :< Sum A B] ->
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

(* | T_conv : forall A A', conv A A' -> forall a, [Gamma |+ a :< A] -> [Gamma |+ a :< A'] *)
| T_wrap   : forall D d, [Gamma |+ d :< D_efunc D (Mu D)] -> [Gamma |+ d :< Mu D]
| T_unwrap : forall D d, [Gamma |+ d :< Mu D] -> [Gamma |+ d :< D_efunc D (Mu D)]
| T_subty : forall a A A', A ::< A' -> [Gamma |+ a :< A] -> [Gamma |+ a :< A']
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

Notation ren_scop xi i j := (forall v, v < i -> xi v < j).

Lemma All_sub D : forall sigma C e, (All D C e).[sigma] = All D C.[up sigma] e.[sigma].
  induction D; intros; simpl; rewrite asms; 
  try replace C.[up (wk 1)].[up (up sigma)] with C.[up sigma].[up (wk 1)]; autosubst. Qed.

Hint Resolve All_sub.
Hint Rewrite All_sub.

Hypothesis const_tys_closed : forall nm e, const_tys nm = Some e -> closed e.

Hint Resolve const_tys_closed.
Hint Resolve efunc_closed.
Hint Resolve red_conv sred_cong1.

Lemma conv_sub1 a b sigma : a <:::> b -> a.[sigma] <:::> b.[sigma]. 
Proof. autorewrite with unconv; intros; destr_logic; eauto. Qed.
Hint Resolve conv_sub1.

Lemma subty_sub1 A A' sigma : A ::< A' -> A.[sigma] ::< A'.[sigma].
Proof. induction 1; simpl in *; eauto using subtyp. 
       assert (T1.[sigma] <:::> (Sort l1).[sigma]) by auto.
       assert (T2.[sigma] <:::> (Sort l2).[sigma]) by auto.
       eauto.
Qed.
Hint Resolve subty_sub1.

Lemma ty_renaming xi Gamma Delta a A :
  [ Gamma |+ a :< A ] ->
  ren_scop xi (size Gamma) (size Delta) ->
  (forall v, v < size Gamma -> (dget Gamma v).[ren xi] = dget Delta (xi v)) ->
  [ Delta |+ a.[ren xi] :< A.[ren xi]].
Proof. move=>Ha; move:xi Delta; induction Ha; simpl; intros; try solve[eauto].
       { rewrite H1; auto. }
       { rewrite closed_sub_id; try eapply const_tys_closed; eassumption || auto. }
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
                         replace P.[x].[t .: r] with P.[t .: r].[x] by autosubst | _ => apply IHHa3; solve[auto] end.
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
       { apply T_wrap.
         replace (D_efunc D (Mu D)) with (D_efunc D (Mu D)).[ren xi]; auto. }
       { simpl in *. replace (D_efunc D (Mu D)).[ren xi] with (D_efunc D (Mu D)); auto.
         symmetry. apply closed_sub_id; auto. }
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

Lemma up_ty A Gamma Delta sigma : [Gamma |+ sigma +| Delta] -> [A.[sigma] :: Gamma |+ up sigma +| A :: Delta].
Proof. destruct x; simpl; intros; auto; asimpl; rewrite <- subst_comp; try constructor; auto. Qed.
Hint Resolve up_ty.

Hint Extern 1 (_.[_] = _.[_]) => autosubst.

Lemma sub_var_cor : forall e Delta T, [Delta |+ e :< T] -> forall sigma Gamma, [Gamma |+ sigma +| Delta] -> [Gamma |+ e.[sigma] :< T.[sigma]].
Proof. induction 1; simpl; intros; auto;
  asimpl; rewrite <- ?subst_comp;
  try solve [eauto].
  { rewrite closed_sub_id; try eapply const_tys_closed; eassumption || eauto. }
  { replace B.[a.[sigma] .: sigma] with B.[up sigma].[a.[sigma]/]; solve[eauto]. }
  { econstructor; try replace B.[up sigma].[a.[sigma]/] with B.[a/].[sigma]; solve[auto]. }
  { replace B.[S_p1 s.[sigma] .: sigma] with B.[up sigma].[S_p1 s.[sigma]/]; solve[eauto]. }
  { replace P.[ab.[sigma] .: sigma] with P.[up sigma].[ab.[sigma]/] by autosubst. 
    econstructor. 
    { specialize (IHhas_type1 (up sigma)). asimpl in *. auto. }
    { specialize (IHhas_type2 (up sigma)). asimpl in *. auto. } 
    { apply IHhas_type3; auto. } }
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
  { apply T_wrap.
    replace (D_efunc D (Mu D)) with (D_efunc D (Mu D)).[sigma]; auto. }
  { simpl in *; replace (D_efunc D (Mu D)).[sigma] with (D_efunc D (Mu D)); auto.
    symmetry; apply closed_sub_id; auto. }
Qed.

Hint Resolve sub_var_cor.
(* Notation "x .[ sigma ]" := (map (fun y => y.[sigma]) x). *)
Hint Rewrite <- subst_comp.

Lemma sub_comp_cor Gamma Delta Sigma delta sigma : [Gamma |+ delta +| Delta] -> [Delta |+ sigma +| Sigma] -> [Gamma |+ sigma >> delta +| Sigma].
Proof. intros; asimpl; autorewrite with core; solve[eauto]. Qed.

Lemma conv_pi_pi A B A' B' : (A :>> B) <:::> (A' :>> B') <-> (A <:::> A') /\ (B <:::> B').
Proof. split; autorewrite with unconv; intros; destr_logic;eauto.
       autorewrite with core in *; destr_logic; subst.
       inverts H0. split; eexists; eauto. 
Qed.

Hint Rewrite conv_pi_pi.

Lemma T_conv Gamma e A B : A <:::> B -> [Gamma |+ e :< B] -> [Gamma |+ e :< A].
Proof. intros; eapply T_subty; try (constructor; symmetry); eassumption. Qed.

Lemma closed_step e e' n : e ::> e' -> closed_at n e -> closed_at n e'.
Proof. move=> He'; move: n; induction He'; simpl in *; intros;
       autounfold in *; autorewrite with core in *; destr_logic;
       try solve[repeat (apply andb_true_intro; split); auto].
       - apply closed_lift with (i := 0); try eapply Reduction.const_vals_closed; eassumption || auto.
       - apply cons_id_scoped; auto.
       - htry; clear_funs. autorewrite with core in *; intuition.
       - htry; clear_funs. autorewrite with core in *; intuition.
       - htry; clear_funs. apply cons_id_scoped; auto.
       - apply cons_id_scoped; auto.
       - repeat split; auto.
         apply rall_scoped; simpl; auto.
         autounfold; autorewrite with core; intuition.
         apply wk1_scoped; auto.
Qed.

Hint Resolve closed_step.

(* TODO: Prove backward lemmas *)
Lemma closed_wk1_back e n : closed_at n.+1 e.[wk 1] -> closed_at n e. Admitted.
(* this one might be too strong - not sure *)
Lemma closed_sub_back e a n : closed_at n e.[a/] -> closed_at n.+1 e /\ closed_at n a. Admitted.
Hint Resolve closed_wk1_back closed_sub_back.
Lemma closed_red e e' n : e :::> e' -> closed_at n e -> closed_at n e'.
Proof. induction 1; intros; auto. eapply closed_step; eassumption. Qed.
Hint Resolve closed_red.

(* Lemma closed_conv e1 e2 n : e1 <:::> e2 -> closed_at n e1 -> closed_at n e2. *)
(* Proof. induction 1; auto. eapply closed_step; eassumption.  *)
       
(* Lemma subty_closed n A B : A ::< B -> closed_at n A -> closed_at n B.  *)
(* Proof. induction 1; intros; auto. *)
(* Lemma lam_pi Gamma A B b : [Gamma |+ Lam b :< A :>> B] -> [A :: Gamma |+ b :< B]. *)
(* Proof. remember (Lam b) as lb; remember (A :>> B) as ab. *)
(*        (* assert (Lam b <:::> lb) by (subst; auto). *) *)
(*        assert (Hc : A :>> B <:::> ab) by (subst; auto). *)
(*        clear Heqab. move=>Hab;move:b Heqlb A B Hc. *)
(*        induction Hab; intros; try solve by inversion. *)
(*        { autorewrite with core in*; destr_logic. *)
(*          inverts Heqlb. *)
(*          replace b0 with b0.[ids] by autosubst. replace B0 with B0.[ids] by autosubst. *)
(*          apply sub_var_cor with (Delta := A :: Gamma). *)
(*          - eapply T_subty; eassumption || constructor; auto using symmetry. *)
(*          - destruct x; intros; asimpl. *)
(*            + eapply T_subty; eassumption || constructor; simpl; auto using symmetry. *)
(*            + constructor; auto. } *)
(*        { autorewrite with unconv in *; destr_logic. *)
(*          apply red_Pi in H; apply red_Mu in H0; destr_logic; subst; congruence. } *)
(*        { exfalso. clear IHHab Heqlb d b Hab d Gamma. *)
(*          autorewrite with unconv in *; destr_logic. *)
(*          apply red_Pi in H; destr_logic; subst. *)
(*          destruct D; simpl in *;  *)
(*          [apply red_Unit in H0|apply red_Mu in H0|apply red_Sum in H0|apply red_Sigma in H0]; *)
(*          destr_logic; congruence. } *)
(*        { subst. specialize (IHHab _  erefl). *)
(*          assert (Haba' : A0 :>> B <:::> A). transitivity A'; auto using symmetry. *)
(* by (eapply rst_trans; [|symmetry]; eassumption). *)
(*          specialize (IHHab _ _ Haba'). *)
(*          auto. } *)
(* Qed. *)

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