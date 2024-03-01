(* A version of FMapList but using regular OrderedTypes *)
From Coq Require Import FMapInterface List Orders.



Module Orders_to_OrderedType(OTF: OrderedTypeFull) <: OrderedType.OrderedType.
  Import OTF.
  (* Print OrderedTypeFull. *)
  (* Module Type
 OrderedTypeFull =
 Sig
   Parameter t : Type.
   Parameter eq : t -> t -> Prop.
   Parameter eq_equiv : Equivalence eq.
   Parameter lt : t -> t -> Prop.
   Parameter lt_strorder : StrictOrder lt.
   Parameter lt_compat : Proper (eq ==> eq ==> iff) lt.
   Parameter compare : t -> t -> comparison.
   Parameter compare_spec :
     forall x y : t, CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
   Parameter eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
   Parameter le : t -> t -> Prop.
   Parameter le_lteq : forall x y : t, le x y <-> lt x y \/ eq x y.
 End *)
  Definition t := t.
  Definition eq := eq.
  Definition lt := lt.
  (* Create HintDb orders_hints. *)
  #[global]
   Hint Unfold t eq lt : ordered_type.
  Lemma eq_refl :
    forall x,
      eq x x.
  Proof.
    intros. reflexivity.
  Defined.

  Lemma eq_sym : forall x y : t, eq x y -> eq y x.
  Proof.
    intros. destruct (eq_dec y x).
    eassumption.
    pose proof eq_equiv.
    inversion H0.
    unfold Symmetric in Equivalence_Symmetric.
    eapply Equivalence_Symmetric. eassumption.
  Defined.

  Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof.
    intros.
    pose proof eq_equiv. inversion H1.
    unfold Transitive in *.
    eapply Equivalence_Transitive; eauto.
  Defined.
  

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    intros. pose proof lt_strorder. inversion H1.
    unfold Transitive in StrictOrder_Transitive.
    eauto with ordered_type.
  Defined.
  
  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    intros. pose proof lt_strorder. inversion H0.
    unfold Irreflexive in StrictOrder_Irreflexive.
    pose proof lt_compat. unfold iff in H1. unfold Proper in H1.
    unfold respectful in H1.
    unfold not. intros.
    specialize (H1 x y H2).
    pose proof (eq_equiv). inversion H3. unfold Symmetric in Equivalence_Symmetric. specialize (Equivalence_Symmetric _ _ H2).
    specialize (H1 _ _ Equivalence_Symmetric).
    unfold Reflexive in StrictOrder_Irreflexive. unfold complement in StrictOrder_Irreflexive.
    destruct H1.
    unfold Transitive in StrictOrder_Transitive.
    specialize (H1 H).
    specialize (StrictOrder_Transitive _ _ _ H H1).
    eauto.
  Defined.

  Lemma compare : forall x y : t, Compare lt eq x y.
  Proof.
    intros. pose proof (eq_dec x y). destruct H.
    - eapply EQ. eassumption.
    - pose proof le_lteq. pose proof lt_compat.
      unfold Proper in H0. unfold iff in H0. unfold respectful in H0.
      pose proof compare_spec.
      specialize (H1 x y).
      destruct (compare x y) eqn:C.
      + eapply EQ. inversion H1. congruence.
      + econstructor. inversion H1. eassumption.
      + eapply GT. inversion H1. eassumption.
  Defined.

  Definition eq_dec := eq_dec.
  #[global]
   Hint Unfold eq_dec : ordered_type.
  
  

  #[global]
   Hint Immediate eq_sym : ordered_type.
  #[global]
   Hint Resolve eq_refl eq_trans lt_not_eq lt_trans : ordered_type.
End Orders_to_OrderedType.

    

Module OtherOTFFacts(OTF: OrderedTypeFull).
  Import OTF.
  Module OTOTF := Orders_to_OrderedType(OTF).
  Import OTOTF.
  Lemma otf_compare_same :
    forall (a: OTF.t),
      OTF.compare a a = Eq.
  Proof.
    pose proof (OTF.compare_spec).
    intros a.
    specialize (H a a).
    destruct (OTF.compare a a) eqn:C.
    reflexivity.
    pose proof (OTF.lt_strorder).
    inversion H0.
    inversion H. eapply StrictOrder_Irreflexive in H1.
    inversion H1.
    inversion H.
    pose proof (OTF.lt_strorder).
    inversion H1. eapply StrictOrder_Irreflexive in H0. inversion H0.
  Defined.

  Lemma otf_eq_compare_eq :
    forall (x y: OTF.t),
      OTF.eq x y ->
      OTF.compare x y = Eq.
  Proof.
    intros. pose proof (OTF.compare_spec).
    pose proof (OTF.lt_compat).
    pose proof (OTF.lt_strorder).
    inversion H2.
    unfold Proper, respectful, iff in H1.
    specialize (H0 x y).
    destruct (OTF.compare x y).
    - reflexivity.
    - inversion H0.
      pose proof (eq_refl y).
      pose proof (H1' := H1).
      specialize (H1 _ _ H _ _ H4).
      destruct H1. eapply H1 in H3. eapply StrictOrder_Irreflexive in H3. inversion H3.
    - inversion H0.
      pose proof (eq_refl x).
      specialize (H1 _ _ H _ _ H4).
      destruct H1. eapply H5 in H3. eapply StrictOrder_Irreflexive in H3. inversion H3.
  Defined.
  

  Lemma otf_compare_sym :
    forall (x y: OTF.t),
      OTF.compare x y = Eq ->
      OTF.compare y x = Eq.
  Proof.
    pose proof (OTF.compare_spec).
    pose proof (H' := H).
    intros. specialize (H x y). rewrite H0 in H.
    inversion H.
    eapply eq_sym in H1.
    specialize (H' y x).
    destruct (OTF.compare y x) eqn:C.
    reflexivity.
    inversion H'.
    pose proof (OTF.lt_compat).
    unfold Proper, respectful, iff in H3.
    specialize (H3 _ _ H1).
    eapply eq_sym in H1.
    specialize (H3 _ _ H1).
    pose proof (OTF.lt_strorder).
    inversion H4. destruct H3.
    pose proof (H6 := H2).
    eapply H3 in H2.
    specialize (StrictOrder_Transitive _ _ _ H2 H6).
    eapply StrictOrder_Irreflexive in StrictOrder_Transitive. inversion StrictOrder_Transitive.
    eapply otf_eq_compare_eq in H1. rewrite H1 in C. inversion C.
  Defined.

  Lemma otf_lt_not_sym :
    forall (x y: OTF.t),
      OTF.lt x y ->
      OTF.lt y x ->
      False.
  Proof.
    pose proof (OTF.lt_strorder).
    intros. inversion H.
    specialize (StrictOrder_Transitive _ _ _ H0 H1).
    eapply StrictOrder_Irreflexive. eassumption.
  Defined.

  Lemma otf_eq_lt_false :
    forall (x y: OTF.t),
      OTF.eq x y ->
      OTF.compare y x = Lt ->
      False.
  Proof.
    intros. pose proof (OTF.lt_strorder).
    inversion H1.
    pose proof (OTF.lt_compat).
    unfold Proper, iff, respectful in H2.
    specialize (H2 _ _ H).
    pose proof (OTF.compare_spec).
    specialize (H3 y x). rewrite H0 in H3.
    inversion H3.
    eapply eq_sym in H.
    specialize (H2 _ _ H).
    destruct H2. specialize (H5 H4).
    eapply otf_lt_not_sym; eassumption.
  Defined.
  

  Lemma otf_gt_implies_lt :
    forall (x y: OTF.t),
      OTF.compare x y = Gt <-> OTF.compare y x = Lt.
  Proof.
    intros. pose proof (OTF.compare_spec).
    pose proof (OTF.lt_compat).
    pose proof (OTF.lt_strorder).
    inversion H1. pose proof (H2 := H0).
    unfold Proper, respectful, iff in H0, H2.
    pose proof (H3 := H).
    specialize (H x y).
    split; intros.
    - rewrite H4 in H. inversion H.
      Check CompLt.
      Check (OTF.lt y x).
      specialize (H3 y x).
      destruct (OTF.compare y x) eqn:C.
      + eapply otf_compare_sym in C.
        rewrite C in H4. inversion H4.
      + reflexivity.
      + inversion H3.
        pose proof (otf_lt_not_sym _ _ H5 H6). inversion H7.
    - destruct (OTF.compare x y); inversion H.
      + pose proof (otf_eq_lt_false _ _ H5). eapply H6 in H4. inversion H4.
      + specialize (H3 y x).
        rewrite H4 in H3. inversion H3. pose proof (otf_lt_not_sym _ _ H5 H6). inversion H7.
      + reflexivity.
  Defined.
  


  Lemma otf_compare_trans :
    forall (x y z: OTF.t),
      OTF.compare x y = Lt -> OTF.compare y z = Lt -> OTF.compare x z = Lt.
  Proof.
    pose proof (OTF.lt_strorder).
    pose proof (OTF.compare_spec).
    intros. specialize (H0 x y).
    inversion H.
    unfold Transitive in StrictOrder_Transitive.
    rewrite H1 in H0. inversion H0; subst; clear H0.
    pose proof (OTF.compare_spec y z).
    pose proof (OTF.compare_spec x z).
    rewrite H2 in H0. inversion H0.
    specialize (StrictOrder_Transitive _ _ _ H3 H5).
    destruct (OTF.compare x z) eqn:C.
    - inversion H4. pose proof (OTF.lt_compat).
      pose proof (C2 := H7).
      unfold Proper, respectful, iff in H7, C2.
      specialize (H7 _ _ H6).
      eapply eq_sym in H6.
      specialize (H7 _ _ H6).
      destruct H7. eapply H7 in StrictOrder_Transitive.
      pose proof (eq_refl z).
      specialize (C2 _ _ H9). specialize (C2 _ _ H6).
      destruct C2. eapply H11 in StrictOrder_Transitive.
      eapply StrictOrder_Irreflexive in StrictOrder_Transitive.
      inversion StrictOrder_Transitive.
    - reflexivity.
    - inversion H. unfold Transitive in StrictOrder_Transitive0.
      inversion H4. pose proof (otf_lt_not_sym _ _ StrictOrder_Transitive H6). inversion H7.
  Defined.

    Lemma otf_compare_eq_trans :
    forall (x y z: OTF.t),
      OTF.compare x y = Eq ->
      OTF.compare y z = Eq ->
      OTF.compare x z = Eq.
  Proof.
    intros.
    pose proof (OTF.compare_spec).
    pose proof (H2 := H1).
    specialize (H2 x y). specialize (H1 y z).
    rewrite H in H2. rewrite H0 in H1.
    inversion H1. inversion H2.
    pose proof (OTF.compare_spec x z).
    pose proof (eq_trans _ _ _ H4 H3).
    eapply eq_sym in H6.
    destruct (OTF.compare x z) eqn:C.
    reflexivity.
    
    pose proof (otf_eq_lt_false _ _ H6 C).
    inversion H7.
    eapply otf_gt_implies_lt in C.
    eapply eq_sym in H6.
    pose proof (otf_eq_lt_false _ _ H6 C).
    inversion H7.
  Defined.
    
    

  Lemma otf_eq_lt :
    forall (a b c: OTF.t),
      OTF.compare a b = Eq ->
      OTF.compare b c = Lt ->
      OTF.compare a c = Lt.
  Proof.
    pose proof (OTF.compare_spec).
    pose proof (H0 := H).
    pose proof (H1 := H).
    intros. specialize (H a b). specialize (H0 b c).
    rewrite H2 in H. rewrite H3 in H0. inversion H. inversion H0.
    pose proof (OTF.lt_compat). unfold Proper, respectful, iff in H6.
    pose proof (C := H6).
    specialize (H6 _ _ H4).
    specialize (H6 _ _ (eq_refl c)).
    destruct H6.
    eapply H7 in H5.
    specialize (H1 a c). destruct (OTF.compare a c); inversion H1.
    - specialize (C _ _ H8). specialize (C _ _ (eq_refl c)).
      eapply C in H5.
      pose proof (OTF.lt_strorder). inversion H9. eapply StrictOrder_Irreflexive in H5. inversion H5.
    - reflexivity.
    - pose proof (otf_lt_not_sym _ _ H5 H8). inversion H9.
  Defined.

  Lemma otf_eq_lt_right :
    forall (a b c: OTF.t),
      OTF.compare a b = Lt ->
      OTF.compare b c = Eq ->
      OTF.compare a c = Lt.
  Proof.
    pose proof (OTF.compare_spec).
    pose proof (H0 := H).
    pose proof (H1 := H).
    intros. specialize (H a b). specialize (H0 b c).
    rewrite H2 in H. rewrite H3 in H0. inversion H. inversion H0.
    pose proof (OTF.lt_compat). unfold Proper, respectful, iff in H6.
    pose proof (C := H6).
    eapply eq_sym in H5.
    specialize (H6 _ _ (eq_refl a)).
    specialize (H6 _ _ H5).
    eapply H6 in H4.
    specialize (H1 a c).
    destruct (OTF.compare a c) eqn:C'.
    - inversion H1. pose proof (otf_eq_lt_false).
      epose proof (eq_trans _ _ _ H7 H5).
      eapply eq_sym in H9.
      specialize (H8 _ _ H9). eapply H8 in H2. inversion H2.
    - reflexivity.
    - eapply (otf_gt_implies_lt) in C'.
      pose proof (OTF.compare_spec c a). rewrite C' in H7.
      inversion H7. pose proof (otf_lt_not_sym _ _ H4 H8). inversion H9.
  Defined.
    
  Lemma otf_compare_eq_eq :
    forall (x y: OTF.t),
      OTF.compare x y = Eq ->
      OTF.eq x y.
  Proof.
    intros. pose proof (OTF.compare_spec).
    pose proof (OTF.lt_compat).
    pose proof (OTF.lt_strorder).
    specialize (H0 x y). rewrite H in H0. inversion H0. eassumption.
  Defined.
End OtherOTFFacts.

Module OTF_to_OT_Facts(OTF: OrderedTypeFull).
  Module OT := Orders_to_OrderedType(OTF).
  Module OtherFacts := OtherOTFFacts(OTF).
  Import OtherFacts.

  Lemma OTF_OT_compare :
    forall (a b: OTF.t) ,
      OTF.compare a b = 
        match OT.compare a b with
        | OrderedType.LT _ => Lt
        | OrderedType.EQ _ => Eq
        | OrderedType.GT _ => Gt
        end.
  Proof.
    intros.
    destruct (OTF.compare a b) eqn:C;
    unfold OT.compare;
      destruct (OTF.eq_dec a b) eqn:E.
    - reflexivity.
    - eapply otf_compare_eq_eq in C. congruence.
    - pose proof (otf_eq_lt_false).
      pose proof (e1 := e).
      eapply OTOTF.eq_sym in e1.
      specialize (H _ _ e1 C). inversion H.
    - match goal with
      | [ |- _ = match ?a with | LT _ => Lt | EQ _ => Eq | GT _ => Gt end ] =>
          remember a as B
      end. destruct B. reflexivity.
      unfold OT.eq in e. congruence.
      unfold OT.lt in l.
      pose proof (OTF.compare_spec a b). rewrite C in H. inversion H.
      pose proof (otf_lt_not_sym _ _ H0 l). inversion H1.
    - eapply otf_gt_implies_lt in C. pose proof (otf_eq_lt_false _ _ e C).
      inversion H.
    - match goal with
      | [ |- _ = match ?a with | LT _ => Lt | EQ _ => Eq | GT _ => Gt end ] =>
          remember a as B
      end. destruct B.
      + pose proof (COMP := OTF.compare_spec a b). rewrite C in COMP. inversion COMP.
        pose proof (otf_lt_not_sym _ _ l H).
        inversion H0.
      + unfold OT.eq in e. congruence.
      + reflexivity.
  Defined.

  Lemma OT_to_OTF_match :
    forall (a b : OTF.t) (T: Type) (x y z: T),
      match OTF.compare a b with
      | Lt => x
      | Eq => y
      | Gt => z
      end =
      match OT.compare a b with
      | OrderedType.LT _ => x
      | OrderedType.EQ _ => y
      | OrderedType.GT _ => z
      end.
  Proof.
    intros. rewrite OTF_OT_compare.
    destruct (OT.compare a b); reflexivity.
  Defined.
  Lemma OT_to_OTF_match_eq_refl :
    forall (a :OTF.t) (T: Type) (x y z: T),
      match OT.compare a a with
      | OrderedType.LT _ => x
      | OrderedType.EQ _ => y
      | OrderedType.GT _ => z
      end = y.
  Proof. intros.
         rewrite <- OT_to_OTF_match.
         rewrite otf_compare_same. reflexivity.
  Defined.
End OTF_to_OT_Facts.




Module List_as_OTF(OTF: OrderedTypeFull) <: OrderedTypeFull.
  Print OrderedTypeFull.
  Module OTOTF := Orders_to_OrderedType(OTF).
  Import OTOTF.
  Module OtherFacts := OtherOTFFacts(OTF).
  Import OtherFacts.

  Definition t := list OTF.t.
  #[global]
  Hint Transparent t : ordered_type.
  Fixpoint eq (l1 l2: t) : Prop :=
    match l1 with
    | nil =>
        nil = l2
    | cons hd tl =>
        match l2 with
        | cons hd' tl' =>
            OTF.eq hd hd' /\ eq tl tl'
        | _ => False
        end
    end.
  Lemma eq_equiv : Equivalence eq.
  Proof.
    econstructor; unfold Reflexive, Symmetric, Transitive; induction x; intros; simpl.
    - reflexivity.
    - split; [ eapply eq_refl | ]. eassumption.
    - simpl in H. subst. reflexivity.
    - simpl in H. destruct y. inversion H.
      simpl. destruct H. split.
      + eapply eq_sym. eauto.
      + eauto.
    - simpl in H. subst. simpl in H0. subst.
      reflexivity.
    - simpl in H. destruct y. inversion H.
      destruct H. simpl in H0. destruct z.
      inversion H0. destruct H0.
      split.
      + eapply eq_trans; eauto.
      + eauto.
  Defined.

  Fixpoint compare (l1 l2: t) :=
    match l1 with
    | nil => match l2 with
            | nil => Eq
            | _ => Lt
            end
    | hd :: tl =>
        match l2 with
        | hd' :: tl' =>
            match OTF.compare hd hd' with
            | Eq => compare tl tl'
            | Lt => Lt
                (* match compare tl tl' with *)
                   (* | Lt => Lt *)
            | Gt => Gt
            end
        | nil => Gt
        end
    end.
  Definition lt (l1 l2: t) := compare l1 l2 = Lt.
  (* Fixpoint lt (l1 l2: t) := *)
  (*   match l1 with *)
  (*   | nil => *)
  (*       match l2 with *)
  (*       | _ :: _ => True *)
  (*       | _ => False *)
  (*       end *)
  (*   | hd :: tl => *)
  (*       match l2 with *)
  (*       | hd' :: tl' => *)
  (*           OTF.lt hd hd' /\ lt tl tl' *)
  (*       | _ => False *)
  (*       end *)
  (*   end. *)

  

  Lemma compare_eq_refl :
    forall (a: t),
      compare a a = Eq.
  Proof.
    induction a; intros.
    - reflexivity.
    - simpl. rewrite (otf_compare_same).
      eassumption.
  Defined.


  
  Lemma lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof.
    unfold Proper, iff, respectful.
    intros.
    split; intros.
    - revert H1 H0. revert x0 y0. revert H. revert y. induction x; intros.
      + simpl in H. subst. destruct x0; inversion H1.
        simpl in H0. destruct y0. inversion H0. econstructor.
      + destruct y. inversion H. destruct y0.
        simpl in H1. destruct x0. inversion H1. simpl in H0. inversion H0.
        simpl in H. destruct H.
        destruct x0; inversion H0.
        unfold lt in *. simpl. simpl in *.
        destruct H0. clear H3 H4.
        destruct (OTF.compare a t2) eqn:C.
        * eapply otf_compare_eq_eq in C.
          pose proof (eq_trans _ _ _ C H0).
          eapply eq_sym in H. epose proof (eq_trans _ _ _ H H3).
          eapply otf_eq_compare_eq in H4. rewrite H4. eauto.
        * pose proof (otf_eq_lt).
          pose proof (otf_eq_lt_right).
          eapply otf_eq_compare_eq in H0.
          specialize (H4 _ _ _ C H0).
          eapply otf_eq_compare_eq in H. eapply otf_compare_sym in H.
          specialize (H3 _ _ _ H H4). rewrite H3. reflexivity.
        * inversion H1.
    -  revert H1 H0. revert x0 y0. revert H. revert y. induction x; intros.
       + simpl in H. subst. simpl in H1. destruct y0. inversion H1.
         destruct x0. inversion H0. econstructor.
       + destruct x0. inversion H0. subst. destruct y. inversion H1.
         inversion H1.
         simpl.
         simpl in H. destruct y; inversion H. clear H.
         unfold lt in *. simpl in H0. destruct y0; inversion H0.
         clear H0. simpl in H1.
         destruct (OTF.compare t1 t2) eqn:C.
         * simpl. eapply otf_compare_eq_eq in C.
           epose proof (eq_trans _ _ _ H2 C).
           eapply eq_sym in H. epose proof (eq_trans _ _ _ H0 H).
           eapply otf_eq_compare_eq in H5. rewrite H5. eapply IHx; eauto.
         * pose proof otf_eq_lt.
           eapply otf_eq_compare_eq in H2. specialize (H0 _ _ _ H2 C).
           eapply eq_sym in H.
           eapply otf_eq_compare_eq in H.
           pose proof (otf_eq_lt_right).
           specialize (H5 _ _ _ H0 H).
           simpl. rewrite H5. reflexivity.
         * inversion H1.
  Defined.

  Lemma lt_strorder : StrictOrder lt.
  Proof.
    econstructor.
    - unfold Irreflexive. unfold Reflexive, complement.
      intros.
      revert H. induction x; intros.
      + inversion H.
      + unfold lt in H. simpl in H.
        

        rewrite otf_compare_same in H. rewrite compare_eq_refl in H. inversion H.
    - unfold Transitive. induction x; intros.
      + simpl in H. destruct y; try congruence.
        simpl in H0; destruct z; try congruence.
        inversion H0. destruct H0.
        simpl. econstructor.
      + destruct z.
        * inversion H0. destruct y. inversion H2. inversion H2.
        * unfold lt in *. destruct y. inversion H.
          simpl.
          simpl in H. destruct (OTF.compare a t1) eqn:C1.
          -- simpl in H0. destruct (OTF.compare t1 t0) eqn:C2.
             ++ pose proof (OTF.lt_strorder).
                inversion H1. unfold Transitive in StrictOrder_Transitive.
                destruct (OTF.compare a t0) eqn:C3.
                eauto.
                reflexivity.
                pose proof (otf_compare_eq_trans _ _ _ C1 C2).
                congruence.
             ++ pose proof (otf_eq_lt).
                specialize (H1 _ _ _ C1 C2).
                rewrite H1. reflexivity.
             ++ inversion H0.
          -- simpl in H0. destruct (OTF.compare t1 t0) eqn:C2.
             ++ pose proof (otf_eq_lt_right).
                specialize (H1 _ _ _ C1 C2).
                rewrite H1. reflexivity.
             ++ pose proof (otf_compare_trans).
                specialize (H1 _ _ _ C1 C2).
                rewrite H1. reflexivity.
             ++ inversion H0.
          -- inversion H.
  Defined.

                
  
   Lemma compare_spec :
     forall x y : t, CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
    induction x; intros.
    - simpl. destruct y; simpl.
      + econstructor. reflexivity.
      + econstructor. econstructor.
    - simpl. destruct y. econstructor. econstructor.
      destruct (OTF.compare a t0) eqn:C.
      + specialize (IHx y).
        inversion IHx; econstructor.
        * split; eauto.
          pose proof (OTF.compare_spec).
          specialize (H1 a t0).
          rewrite C in H1. inversion H1.
          assumption.
        * unfold lt. simpl.

          rewrite C. congruence.
        * unfold lt. simpl. eapply otf_compare_sym in C.
          rewrite C. eapply H0.
      + econstructor. unfold lt. simpl. rewrite C. reflexivity.
      + econstructor. unfold lt. simpl.
        eapply otf_gt_implies_lt in C. rewrite C. reflexivity.
  Defined.
          
        
  Lemma eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof.
    induction x; intros.
    - destruct y; simpl; try (left; congruence); try (right; congruence).
    - destruct y; [ right | ].
      + unfold not. intros. inversion H.
      + simpl.
        destruct (IHx y).
        * destruct (OTF.eq_dec a t0).
          left; split; eassumption.
          right. unfold not.  intros. destruct H. eapply n. eassumption.
        * right. unfold not. intros. destruct H. eapply n in H0. eassumption.
  Defined.
  Definition le (l1 l2: t) :=
    lt l1 l2 \/ eq l1 l2.
  
  Lemma le_lteq : forall x y : t, le x y <-> lt x y \/ eq x y.
  Proof.
    unfold le. split; intros; eassumption.
  Defined.
End List_as_OTF.

Module List_as_OT(OT: OrderedTypeFull) <: OrderedType.OrderedType.
  Module OTF := List_as_OTF(OT).
  Include Orders_to_OrderedType(OTF).
End List_as_OT.

Require Import OrdersEx.

Module Pair_as_OTF(O1 O2: OrderedTypeFull) <: OrderedTypeFull.
  Include PairOrderedType O1 O2.

  Definition le (p1 p2: t) :=
    lt p1 p2 \/ eq p1 p2.
    (* match p1, p2 with *)
    (* | (a1, b1), (a2, b2) => *)
        (* O1.le a1 a2 \/ (O1.eq a1 a2 /\ O2.le b1 b2) *)
    (* end. *)


  Definition le_lteq : forall x y, le x y <-> lt x y \/ eq x y.
  Proof.
    intros.
    pose proof (O1.le_lteq).
    pose proof (O2.le_lteq).
    unfold le. unfold lt. unfold eq. unfold relation_disjunction. unfold RelationPairs.RelProd. unfold RelationPairs.RelCompFun. unfold relation_conjunction. unfold predicate_intersection. unfold predicate_union. unfold pointwise_extension.
    split; intros; eauto.
  Defined.

  

   
                                                   
  

End Pair_as_OTF.


