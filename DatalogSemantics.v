From Coq Require Import  List String Arith Psatz DecidableTypeEx OrdersEx Program.Equality FMapList MSetWeakList.

From VeriFGH Require Import OrdersFunctor DatalogProps StringOrders RelOrdered.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.



Module RelSemantics.
  Import rset.

  

    Module Ground_Types_as_OTF <: Orders.OrderedTypeFull.
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

      Lemma ascii_compare_eq :
        forall (a: Ascii.ascii),
          Ascii_as_OT.compare a a = Eq.
      Proof.
        intros.
        destruct a. destruct b, b0, b1, b2, b3, b4, b5, b6; simpl; reflexivity.
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
            admit.
      Admitted.
            
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

      Lemma ordered_type_string_lt :
        forall (x y: string),
          OrderedTypeEx.String_as_OT.lt x y <->
            String_as_OT.lt x y.
      Proof.
        induction x; intros; split; intros.
        - unfold String_as_OT.lt. simpl. inversion H. reflexivity.
        - unfold String_as_OT.lt in H. unfold OrderedTypeEx.String_as_OT.lt.
          destruct y; simpl in *.
          inversion H. econstructor.
        - inversion H; subst.
          + unfold String_as_OT.lt. simpl. rewrite ascii_compare_eq.
            eapply IHx. eauto.
          + unfold String_as_OT.lt. simpl.
            (* rewrite String_OTF.ascii_compare_same_as_ascii_ot_compare. *)
            eapply OrderedTypeEx.Ascii_as_OT.cmp_lt_nat in H3.
            rewrite String_OTF.ascii_compare_same_as_ascii_ot_compare in *.
            rewrite H3. reflexivity.
        - destruct y. unfold String_as_OT.lt in H. simpl in H. inversion H.
          destruct (Ascii.compare a a0) eqn:C.
          + eapply OrderedTypeEx.Ascii_as_OT.cmp_eq in C. subst a.
            
            eapply OrderedTypeEx.String_as_OT.lts_tail. eapply IHx.
            unfold String_as_OT.lt in *. simpl in H.
            rewrite String_OTF.ascii_compare_same_as_ascii_ot_compare in H.
            rewrite ascii_compare_eq in H.
            rewrite H. reflexivity.
          + econstructor. eapply OrderedTypeEx.Ascii_as_OT.cmp_lt_nat.
            eassumption.
          + unfold String_as_OT.lt in H. simpl in H.
            destruct (Ascii_as_OT.compare a a0) eqn:C'; subst.
            rewrite String_OTF.ascii_compare_same_as_ascii_ot_compare in C'.
            rewrite C' in C. inversion C.
            rewrite String_OTF.ascii_compare_same_as_ascii_ot_compare in C'. congruence.
            rewrite String_OTF.ascii_compare_same_as_ascii_ot_compare in C'.
            inversion H.
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
    

    Module Ground_Type_as_OT := Orders_to_OrderedType(Ground_Types_as_OTF).
    Module String_as_OT := Orders_to_OrderedType(String_OTF).
    Module List_Ground_Type_as_OTF := OrdersFunctor.List_as_OTF(Ground_Types_as_OTF).
    Module List_List_Ground_Type_as_OTF := OrdersFunctor.List_as_OTF(List_Ground_Type_as_OTF).

    Module List_Ground_Type_as_OT := OrdersFunctor.List_as_OT(List_List_Ground_Type_as_OTF).

    
    Module ground_maps := FMapList.Make_ord(String_as_OT) (List_Ground_Type_as_OT).
  

    Structure rel_grounding: Type :=
      MkRelGrounding {
          r: rel;
          arg_types: Vector.t ground_types (num_args r);
        }.

    Print ground_maps.

    Print ground_maps.Data.

    Print ground_maps.MapS.
    
    (* Definition rel_grounding_assoc  *)
    
    Print ground_maps.MapS.In.
    
    
    Structure grounding: Type :=
      MkGrounding {
          edbs: rset.t;
          grounds: ground_maps.t;
          edbs_is_edb: forall (r: rel), In r edbs -> rtype r = edb;
          grounded: forall (r: rel), In r edbs <-> exists g, ground_maps.MapS.find (name r) grounds = Some g;
          groundings_are_fine :
          forall (r: rel) lg,
            In r edbs <->
            (ground_maps.MapS.find (name r) grounds = Some lg ->
            Forall (fun g => (num_args r) = Datatypes.length g) lg);
          
        }.

    Structure iter_grounding : Type :=
      MkIterGrounding {
          iter_rels : rset.t;
          iter_grounds: ground_maps.t;
          iter_grounded: forall (r: rel), In r iter_rels <-> exists g, ground_maps.MapS.find (name r) iter_grounds = Some g;
          iter_groundings_are_fine :
          (forall (r: rel) lg,
              In r iter_rels <->
              (ground_maps.MapS.find (name r) iter_grounds = Some lg ->
              Forall (fun g => num_args r = Datatypes.length g) lg));
        }.

    Definition grounding_to_iter_grounding : grounding -> iter_grounding.
    Proof.
      intros. destruct X.
      eapply (MkIterGrounding edbs0 grounds0
                              grounded0 groundings_are_fine0).
    Defined.

    Print ground_maps.


  (*
    Lemma String_as_OT_compare_eq_refl :
      forall (T: Type) s (a b c: T),
        match String_as_OT.compare s s with
        | OrderedType.GT _ => a
        | OrderedType.EQ _ => b
        | OrderedType.LT _ => c
        end = b.
    Proof.
      intros T. induction s; intros.
      - simpl. reflexivity.
      - 
        unfold String_as_OT.compare.
        destruct (String_OTF.eq_dec (String a s) (String a s)) eqn:H.
        reflexivity.
        simpl.
        congruence.
    Defined.

  Module StringOther := OtherOTFFacts(String_OTF).
  Module String_OTF_to_OT := OTF_to_OT_Facts(String_OTF).

  Lemma String_compares :
    forall (s1 s2: string),
      String_OTF.compare s1 s2 = OrdersEx.String_as_OT.compare s1 s2.
  Proof.
    induction s1; intros.
    - simpl. destruct s2; simpl; reflexivity.
    - simpl. destruct s2. reflexivity.
      destruct (Ascii_as_OT.compare a a0); reflexivity.
  Defined.
      

    Definition add_to_iter_grounding (key: rel) (elmt: list (list (list ground_types))) (ig: iter_grounding) : iter_grounding.
    Proof.
      destruct ig.
      (* assert (elt). *)
      (* eapply key. *)
      pose proof (IG := MkIterGrounding (add key iter_rels0)).
      specialize (IG (ground_maps.MapS.add (name key) elmt iter_grounds0)).
      assert ((forall r : rel,
        In r (add key iter_rels0) <->
        exists g : list (list (list ground_types)),
          ground_maps.MapS.find (elt:=list (list (list ground_types)))
            (name r) (ground_maps.MapS.add (name key) elmt iter_grounds0) =
            Some g)).
      {
        clear IG. clear iter_groundings_are_fine0.
        revert iter_grounded0. revert iter_rels0.
        destruct iter_grounds0.
        induction this0; intros; split; intros.
        - assert (forall r: rel, In r iter_rels0 -> False).
          {
            intros.
            eapply iter_grounded0 in H0. destruct H0.
            unfold ground_maps.MapS.find in H0. unfold ground_maps.MapS.Raw.find in H0. simpl in H0. inversion H0.
          }
          Print rset.
          assert (choose iter_rels0 = None).
          {
            destruct (choose iter_rels0) eqn:CHOOSE.
            pose proof (C' := CHOOSE).
            eapply choose_spec1 in C'.
            eapply H0 in C'. inversion C'.
            reflexivity.
          }
          eapply choose_spec2 in H1.
          pose proof (ADD := add_spec). eapply ADD in H.
          destruct H.
          rewrite H. exists elmt.
          unfold ground_maps.MapS.find. unfold ground_maps.MapS.Raw.find. simpl.
          rewrite String_OTF_to_OT.OT_to_OTF_match_eq_refl. reflexivity.
          eapply H1 in H. inversion H.
        - specialize (iter_grounded0 r0).
          eapply add_spec.
          destruct (rel_dec r0 key).
          + left. eassumption.
          + right. eapply iter_grounded0.
            destruct H. exists x.
            unfold ground_maps.MapS.add in H. simpl in H.
            Set Printing All.
        - inversion sorted. specialize (IHthis0 H2). subst.
          pose proof (ADD := add_spec). eapply ADD in H. destruct H.
          + subst. exists elmt.
            unfold ground_maps.MapS.find.
            unfold ground_maps.MapS.Raw.find.
            simpl. destruct a.
            rewrite <- String_OTF_to_OT.OT_to_OTF_match. fold String_OTF.compare.
            destruct (String_OTF.compare (name key) s) eqn:COMP;
              [ rewrite <- String_OTF_to_OT.OT_to_OTF_match; try (fold String_OTF.compare; rewrite StringOther.otf_compare_same) .. | ].
            reflexivity. reflexivity.
            rewrite <- String_OTF_to_OT.OT_to_OTF_match. fold String_OTF.compare.
            rewrite COMP.
            unfold ground_maps.MapS.Raw.add.
            destruct this0.
            rewrite String_OTF_to_OT.OT_to_OTF_match_eq_refl. reflexivity.
            specialize (IHthis0 iter_rels0).
            specialize (IHthis0 
            
            
          
          
          pose proof (ADD := add_spec). eapply ADD in H.
          destruct H.
          + subst. rewrite <- String_OTF_to_OT.OT_to_OTF_match. fold String_OTF.compare. exists elmt.
            rewrite StringOther.otf_compare_same. reflexivity.
          + specialize (iter_grounded0 r0 H). destruct iter_grounded0.
            exists x.
        intros.
        Print rset.
        pose proof (ADD := add_spec).
        eapply ADD in H.
        destruct H.
        - exists elmt.
          Print ground_maps.MapS.Raw.
          unfold ground_maps.MapS.find.
          erewrite ground_maps.MapS.Raw.find_equation.
          unfold ground_maps.MapS.this. simpl.
          unfold ground_maps.MapS.Raw.add.
          unfold ground_maps.MapS.this.
          destruct (iter_grounds0).
          destruct this0.
          + simpl. destruct (String_as_OT.compare (name r0) (name key)).
            rewrite H in l. eapply String_as_OT.lt_not_eq in l.
            pose proof String_as_OT.eq_refl (name key).
            eapply l in H0. inversion H0.
            reflexivity.
            rewrite H in l. eapply String_as_OT.lt_not_eq in l.
            pose proof (String_as_OT.eq_refl (name key)).
            eapply l in H0. inversion H0.
          + rewrite H in *. simpl.
            destruct p. destruct (String_as_OT.compare (name key) s).
            pose proof (OrderedTypeEx.String_as_OT.cmp_eq).
            specialize (H0 (name key) (name key)).
            destruct H0. specialize (H1 (eq_refl _)).
            rewrite String_as_OT_compare_eq_refl. reflexivity.
            rewrite String_as_OT_compare_eq_refl. reflexivity.
            destruct this0.
            * simpl.
              pose proof String_as_OT.compare_spec.
              specialize (H0 (name key) s).
              
              destruct (OrdersEx.String_as_OT.compare (name key) s).
              inversion H0.
              
              unfold OrdersEx.String_as_OT.eq in H1.
              unfold String_as_OT.lt in l0.
              pose proof (String_OTF.compare_spec).
              specialize (H2 s (name key)).
              (* eapply StringOther.otf_eq_compare_eq in H1. *)
              (* fold String_OTF.compare in H1. *)
              (* unfold String_as_OT.compare. *)
              (* eapply StringOther.otf_compare_sym in H1. *)
              fold String_OTF.compare in H1.
              pose proof (StringOther.otf_eq_lt_false).
              fold String_OTF.compare in H3.
              (* eapply StringOther.otf_compare_eq_eq in H1. *)
              specialize (H3 _ _ H1).
              eapply H3 in l0. inversion l0.
              unfold String_as_OT.lt in l0.
              eapply StringOther.otf_gt_implies_lt in l0.
              fold String_OTF.compare in l0.
              inversion H0.
              unfold OrdersEx.String_as_OT.lt in H1.
              pose proof (String_compares).
              specialize (H2 (name key) s).
              rewrite H1 in l0.
              inversion l0.
              unfold String_as_OT.lt in l0.
              inversion H0.
              unfold OrdersEx.String_as_OT.lt in H1.
              pose proof (String_compares s (name key)).
              rewrite <- String_OTF_to_OT.OT_to_OTF_match.
              fold (String_OTF.compare).
              eapply StringOther.otf_gt_implies_lt in l0.
              fold (String_OTF.compare) in l0.
              rewrite l0.
              erewrite <- String_OTF_to_OT.OT_to_OTF_match.
              fold (String_OTF.compare).
              rewrite StringOther.otf_compare_same. reflexivity.
            * rewrite <- String_OTF_to_OT.OT_to_OTF_match. fold (String_OTF.compare).
              unfold String_as_OT.lt in l0.
              eapply StringOther.otf_gt_implies_lt in l0.
              fold String_OTF.compare in l0. rewrite l0.
              destruct p.
              rewrite <- String_OTF_to_OT.OT_to_OTF_match. fold String_OTF.compare.
              destruct (String_OTF.compare (name key) s0) eqn:C.
              simpl. rewrite <- String_OTF_to_OT.OT_to_OTF_match.
              fold (String_OTF.compare).
              rewrite StringOther.otf_compare_same. reflexivity.
              simpl.
              rewrite <- String_OTF_to_OT.OT_to_OTF_match.
              fold String_OTF.compare.
              rewrite StringOther.otf_compare_same.
              reflexivity.
              simpl.
              rewrite <- String_OTF_to_OT.OT_to_OTF_match.
              fold String_OTF.compare.
              rewrite C.
              destruct this0. simpl.
              rewrite <- String_OTF_to_OT.OT_to_OTF_match.
              fold String_OTF.compare.
              rewrite StringOther.otf_compare_same.
              reflexivity.
              destruct p. rewrite <- String_OTF_to_OT.OT_to_OTF_match. fold String_OTF.compare.
              destruct (String_OTF.compare (name key) s1) eqn:C'.
                
              
              admit.
            * unfold String_as_OT.lt in l0.
              
      
    
    
    
    

    Section RuleSemantics.
      Hypothesis (r: rule).
      Print rset.
      Print ground_maps.MapS.

      

      Definition evaluate_rule (ig: iter_grounding) (r: rule) :=
        let grels := iter_rels ig in
        let igrounds := iter_grounds ig in
        let igrounded := iter_grounded ig in
        let igroundingsfine := iter_groundings_are_fine ig in
        match r with
        | rule_def_empty hd =>
            let n := name hd in
            if mem (name hd) grels then
              ig
            else
              MkIterGrounding (add n grels)
                              (ground_maps.MapS.add n (cons (@nil ground_types) nil) igrounds)
        | rule_def hd body =>
        | rule_def_exists hd exists_vars body =>
        end

    
  
  Section Hypothesis (prog: program).
  

  
    (* 
      Theorem magic_sets_optimization_okay :
      answer1 = semantics of program1 ->
answer2 = semantics of program2 ->
answer1 = answer2.
 *)
*)
