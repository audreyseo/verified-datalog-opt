From Coq Require Import  List String Arith Psatz DecidableTypeEx OrdersEx Program.Equality FMapList FMapWeakList MSetWeakList.

From VeriFGH Require Import OrdersFunctor DatalogProps StringOrders.
(* RelOrdered. *)

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.


Module Ground_Types_as_OTF <: Orders.UsualOrderedTypeFull.
  Import String_OTF.
  Module MoreString := OtherOTFFacts(String_OTF).
  Definition t := ground_types.
  Definition eq := @Logic.eq t.
  Definition eq_equiv : RelationClasses.Equivalence eq := RelationClasses.eq_equivalence.
  

  Definition lt (g1 g2: ground_types) :=
    match g1, g2 with
    | NAT n1, NAT n2 => Nat.lt n1 n2
    | STR s1, STR s2 =>
        String_as_OT.lt s1 s2
    | NAT _, STR _ => True
    | STR _, NAT _ => False
    end.

  Definition le (g1 g2: ground_types) :=
    match g1, g2 with
    | NAT n1, NAT n2 => Nat.le n1 n2
    | STR s1, STR s2 =>
        String_OTF.le s1 s2
    | NAT _, STR _ => True
    | STR _, NAT _ => False
    end.

  (* Lemma compare : *)
  (*   forall (g1 g2: t), *)
  (*     OrderedType.Compare lt eq g1 g2. *)

  Definition compare (g1 g2: ground_types) :=
    match g1, g2 with
    | NAT n1, NAT n2 => Nat.compare n1 n2
    | STR s1, STR s2 => String_as_OT.compare s1 s2
    | NAT _, STR _ => Lt
    | STR _, NAT _ => Gt
    end.

  

  #[global]
   Instance lt_strorder : RelationClasses.StrictOrder lt.
  Proof.
    econstructor.
    - unfold RelationClasses.Irreflexive.
      unfold RelationClasses.Reflexive.
      unfold RelationClasses.complement.
      destruct x; intros.
      + simpl in H. eapply Nat.lt_irrefl in H. eassumption.
      + simpl in H. pose proof String_as_OT.lt_strorder.
        inversion H0. unfold RelationClasses.Irreflexive in StrictOrder_Irreflexive. unfold RelationClasses.Reflexive in StrictOrder_Irreflexive. unfold RelationClasses.complement in StrictOrder_Irreflexive. eapply StrictOrder_Irreflexive in H. eauto.
    - unfold RelationClasses.Transitive.
      intros.
      destruct x, z.
      + simpl in H. destruct y; simpl in H; subst.
        eapply Nat.lt_trans. eassumption. eassumption.
        inversion H0.
      + destruct y; simpl in H, H0. reflexivity.
        reflexivity.
      + destruct y; simpl in H, H0; contradiction.
      + destruct y; simpl in H, H0; try congruence; try contradiction.
        simpl.
        enough (forall s2 s3, String_as_OT.lt s2 s3 <-> OrderedTypeEx.String_as_OT.lt s2 s3).
        rewrite H1. 
        eapply OrderedTypeEx.String_as_OT.lt_trans.
        rewrite <- H1. eassumption. rewrite <- H1. eassumption.
        unfold String_as_OT.lt. unfold OrderedTypeEx.String_as_OT.lt.
        induction s2; intros.
        * simpl. split; intros.
          destruct s3. inversion H1.
          econstructor.
          inversion H1. reflexivity.
        * simpl. split; intros.
          -- destruct s3. inversion H1.
             destruct (Ascii_as_OT.compare a a0) eqn:A.
             ++ eapply OrderedTypeEx.Ascii_as_OT.cmp_eq in A. subst a.
                eapply OrderedTypeEx.String_as_OT.lts_tail.
                eapply IHs2. eauto.
             ++ econstructor. eapply OrderedTypeEx.Ascii_as_OT.cmp_lt_nat. eassumption.
             ++ inversion H1.
          -- destruct s3; intros. inversion H1.
             inversion H1; subst.
             ++ assert (a0 = a0) by reflexivity.
                eapply OrderedTypeEx.Ascii_as_OT.cmp_eq in H2.
                rewrite String_OTF.ascii_compare_same_as_ascii_ot_compare in H2. rewrite String_OTF.ascii_compare_same_as_ascii_ot_compare. rewrite H2.
                eapply IHs2. eassumption.
             ++ eapply OrderedTypeEx.Ascii_as_OT.cmp_lt_nat in H3.
                rewrite String_OTF.ascii_compare_same_as_ascii_ot_compare in *.
                rewrite H3. reflexivity.
  Defined.

  #[global]
   Instance lt_compat : Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq iff)) lt.
  Proof.
    unfold Morphisms.Proper. unfold Morphisms.respectful. unfold iff.
    induction x; intros.
    - inversion H; subst.
      split; intros.
      + inversion H0. subst x.
        assumption.
      + inversion H0. subst x. eassumption.
    - inversion H; subst. inversion H0; subst.
      split; intros; eassumption.
  Defined.

  

  Lemma compare_spec :
    forall (x y: t),
      CompSpec eq lt x y (compare x y).
  Proof.
    induction x; intros; unfold CompSpec; simpl.
    - destruct y.
      + simpl.
        destruct (n ?= n0) eqn:C; econstructor.
        * eapply Nat.compare_eq in C.
          rewrite C. reflexivity.
        * unfold Nat.lt. eapply nat_compare_Lt_lt in C. assumption.
        * eapply nat_compare_Gt_gt in C. unfold gt in C. assumption.
      + econstructor. econstructor.
    - destruct y; simpl in *. econstructor. econstructor.
      destruct (String_as_OT.compare s s0) eqn:C; econstructor.
      + eapply OrderedTypeEx.String_as_OT.cmp_eq in C. subst. reflexivity.
      + eapply OrderedTypeEx.String_as_OT.cmp_lt in C.
        unfold OrderedTypeEx.String_as_OT.lt in C.
        inversion C. subst. econstructor.
        unfold String_as_OT.lt. simpl.
        rewrite String_OTF.ascii_compare_same_as_ascii_ot_compare.
        rewrite <- String_OTF.ascii_compare_same_as_ascii_ot_compare.
        rewrite ascii_compare_eq.
        inversion H. simpl. reflexivity.
        eapply ordered_type_string_lt in H2.
        simpl.
        rewrite ascii_compare_eq.
        pose proof (String_as_OT.compare_spec s3 s4).
        destruct (String_as_OT.compare s3 s4).
        inversion H5.
        pose proof (MoreString.otf_eq_lt_false').
        specialize (H7 _ _ H6).
        specialize (H7 H2). contradiction.
        reflexivity.
        inversion H5.
        pose proof (MoreString.otf_lt_not_sym _ _ H2 H6).
        contradiction.
        simpl. rewrite String_OTF.ascii_compare_same_as_ascii_ot_compare.
        eapply OrderedTypeEx.Ascii_as_OT.cmp_lt_nat in H2.
        unfold OrderedTypeEx.Ascii_as_OT.cmp in H2. rewrite H2.
        reflexivity.
        unfold String_as_OT.lt. simpl.
        eapply OrderedTypeEx.Ascii_as_OT.cmp_lt_nat in H.
        unfold OrderedTypeEx.Ascii_as_OT.cmp in H.
        rewrite ascii_compare_same_as_ascii_ot_compare. rewrite H. reflexivity.
      + unfold String_as_OT.lt.
        eapply MoreString.otf_gt_implies_lt. eassumption.
  Defined.

  
  Lemma eq_dec :
    forall (x y: t),
      { x = y} + { x <> y}.
  Proof.
    destruct x, y; try (right; congruence).
    - destruct (Nat.eq_dec n n0) eqn:EQ; try (right; congruence); left; congruence.
    - destruct (String_as_OT.eq_dec s s0) eqn:EQ; try (right; congruence); left; congruence.
  Defined.
  

  Lemma le_lteq :
    forall x y,
      le x y <-> lt x y \/ eq x y.
  Proof.
    destruct x, y; split; intros.
    - simpl in H.
      destruct (Nat.le_lteq n n0). eapply H0 in H. destruct H; [ | subst ].
      + left. eapply H.
      + right. reflexivity.
    - simpl in H. eapply (Nat.le_lteq).
      destruct H.
      + left. eapply H.
      + right. inversion H. reflexivity.
    - simpl in H. left. simpl. assumption.
    - simpl. econstructor.
    - simpl. simpl in H. left. eauto.
    - simpl in H. destruct H; inversion H.
    - simpl in H.
      eapply String_OTF.le_lteq in H. destruct H.
      + left. eapply H.
      + right. inversion H. reflexivity.
    - simpl. simpl in H. destruct H.
      + eapply String_OTF.le_lteq. left. assumption.
      + eapply String_OTF.le_lteq. right. inversion H. reflexivity.
  Defined.
  
  Lemma eq_refl :
    forall x,
      eq x x.
  Proof.
    intros. reflexivity.
  Defined.

  Lemma eq_sym :
    forall x y,
      eq x y ->
      eq y x.
  Proof.
    intros.
    inversion H. reflexivity.
  Defined.

  Lemma eq_trans :
    forall x y z,
      eq x y ->
      eq y z ->
      eq x z.
  Proof.
    intros. inversion H. inversion H0. reflexivity.
  Defined.

  
  
  
  
  Lemma lt_trans :
    forall x y z,
      lt x y ->
      lt y z ->
      lt x z.
  Proof.
    intros.  destruct x, y, z; simpl in *; try eassumption.
    - eapply Nat.lt_trans; eassumption.
    - inversion H0.
    - inversion H.
    - eapply ordered_type_string_lt.
      eapply ordered_type_string_lt in H, H0.
      eapply OrderedTypeEx.String_as_OT.lt_trans; eassumption.
  Defined.

  Lemma lt_not_eq :
    forall x y,
      lt x y ->
      x <> y.
  Proof.
    destruct x; intros.
    destruct y; simpl in H; unfold lt in H.
    unfold not. intros. inversion H0.
    eapply Nat.lt_neq in H. congruence.
    unfold not. intros. inversion H0.
    destruct y. simpl in H. inversion H.
    simpl in H. unfold not. intros.
    eapply ordered_type_string_lt in H.
    eapply OrderedTypeEx.String_as_OT.lt_not_eq in H.
    unfold not in H. inversion H0.
    eapply H in H2. congruence.
  Defined.
  
  
  
End Ground_Types_as_OTF.


Module String_GT_OT := Pair_as_OTF(String_OTF) (Ground_Types_as_OTF).

Module gset.
  Module RawSets := MSetWeakList.Make(String_GT_OT).
  Include RawSets.
  
  (* Print fold. *)

  Definition replace (name: String_OTF.t) (grounding: Ground_Types_as_OTF.t) (s: t) : t :=
    let (s', replaced) :=
      fold (fun (elmt: String_GT_OT.t) (acc: t * bool) =>
              match acc with
              | (s_acc, replaced_yet) =>
                  if replaced_yet then
                    (add elmt s_acc, replaced_yet)
                  else
                    let (n1, g1) := elmt in
                    if String_OTF.eq_dec n1 name then
                      (add (name, grounding) s_acc, true)
                    else
                      (add elmt s_acc, false)
              end)
           s
           (empty, false) in
    s'.

  (* Check In. *)

  Definition In_dec : forall (x: elt) (s: t), { In x s } + { ~ (In x s) }.
  Proof.
    pose proof elements_spec1.
    pose proof SetoidList.InA_dec.
    specialize (X String_GT_OT.t String_GT_OT.eq String_GT_OT.eq_dec).
    intros.
    unfold elt in *. unfold String_GT_OT.t in *.
    specialize (X x (elements s)).
    specialize (H s x).
    destruct H.
    destruct X.
    - eapply H in i. left. assumption.
    - right. unfold not; intros. eapply H0 in H1. unfold String_GT_OT.eq in n. eapply n in H1. contradiction.
  Defined.

  (* Lemma In_fold_spec : *)
  (*   forall (s: t) (fst: string * ground_types) *)
  (*     (n: string) (g: ground_types), *)
  (*     In  *)
  (*
  Lemma In_fold_acc :
    forall (s: list String_GT_OT.t) (s': t) (n: string) (g: ground_types),
      In (n, g)
    (let (s', _) :=
       fold_left
         (fun (a0 : t * bool) (e0 : elt) =>
          let (s_acc, replaced_yet) := a0 in
          if replaced_yet
          then (add e0 s_acc, replaced_yet)
          else
           let (n1, _) := e0 in
           if String_OTF.eq_dec n1 n
           then (add (n, g) s_acc, true)
           else (add e0 s_acc, false)) s (add (n, g) s', true) in
     s').
  Proof.
    induction s; intros.
    - simpl. eapply add_spec. left. reflexivity.
    - simpl.
      pose proof (String_GT_OT.eq_dec a (n, g)).
      destruct H eqn:Heq.
      

  Lemma replace_spec_in :
    forall (s: t) (n: string) (g g': ground_types),
      In (n, g) s -> In (n, g') (replace n g' s).
  Proof.
    destruct s. unfold Raw.t in *. unfold Raw.elt in *. unfold Raw.Ok in *.
    induction this0; intros.
    - inversion H.
    - inversion H; unfold RelationPairs.RelProd in *; unfold RelationClasses.relation_conjunction in  *; unfold RelationPairs.RelCompFun in *; unfold RelationClasses.predicate_intersection in *; unfold RelationClasses.pointwise_extension in *; subst.
      + destruct H1. simpl in H0, H1.
        unfold replace.
        (* unfold fold. *)
        (* unfold Raw.fold. *)
        (* Set Printing All. *)
        (* Print fold_spec. *)
        rewrite fold_spec.
        simpl.
        assert (a = (n, g)).
        rewrite H0. rewrite H1.
        eapply injective_projections; simpl; reflexivity.
        rewrite H2.
        destruct (String_OTF.eq_dec n n) eqn:E; try congruence.
        subst.
        
        
        
      inversion H.
      inversion is_ok0.

  Fixpoint replace (name: String_OTF.t) (grounding: Ground_Types_as_OTF.t) (s: t) : t :=
    match s with
    | nil => (name, grounding) :: nil
    | (n1, g1) :: s' =>
        if String_OTF.eq_dec n1 name then
          (name, grounding) :: s'
        else
          (n1, g1) :: (replace name grounding s')
    end.
*)
End gset.
