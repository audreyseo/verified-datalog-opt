From Coq Require Import List String Arith Psatz.

From VeriFGH Require Import DatalogProps DatalogSemantics GroundMaps MonotonicityTheorems.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.


Import RelSemantics.

Module GroundingNotation.
  Coercion NAT : nat >-> ground_types.
  Coercion STR : string >-> ground_types.
End GroundingNotation.


Module TransitiveClosureProgram.
  Import GroundingNotation.

  Section RelDecls.
    Let R x y := mk_rel "R" (x :: y :: nil) edb.
    Let T x y := mk_rel "T" (x :: y :: nil) idb.
    Let A x := mk_rel "A" (x :: nil) idb.

    (* We want to encode the following programs:

P1:
t(x,y) = r(x,y)
t(x,y) = t(x,z),r(z,y)
a(y) = t('1',y)

P2:
a(y) = R('1',y)
a(y) = a(x),r(x,y)

     *)

    Let Txy := T "x" "y".
    Let Txz := T "x" "z".

    Declare Scope rel_scope.
    Delimit Scope rel_scope with rel.

    Notation "{ r :- }" := (rule_def_empty r) : rel_scope.
    Notation "{ r :- x } " := (rule_def r (x :: nil)) : rel_scope.
    Notation "{ r :- x ; y ; .. ; z }" := (rule_def r (cons x (cons y .. (cons z nil) ..))) : rel_scope.

    Eval compute in ({ Txy :- (R "x" "y") })%rel.
    Local Open Scope rel_scope.

    Let Txy1 := { Txy :- (R "x" "y") }.

    Let Txy2 := { Txy :- Txz ; (R "z" "y") }.

    Let Ay := { (A "y") :- (mk_rel_ground "T" ("x" :: "y" :: nil) (("x", STR "1") :: nil) idb ) }.

    Let Ay1 := { (A "y") :- (mk_rel_ground "R" ("x" :: "y" :: nil) (("x", STR "1") :: nil) idb) }.
    
    Let Ay2 := { (A "y") :- (A "x"); (R "x" "y") }.

    Declare Scope string_sets_scope.
    Delimit Scope string_sets_scope with ssets.
    Notation "'s{' x '}s'" := (string_sets.add x string_sets.empty) : string_sets_scope.
    Notation "'s{' x ; y ; .. ; z '}s'" := (string_sets.add x (string_sets.add y .. (string_sets.add z string_sets.empty) ..)) : string_sets_scope.
    Eval compute in s{ "x"; "y"; "z" }s%ssets.

    Definition program1 :=
      DlProgram s{ "T" }s%ssets
                s{ "R" }s%ssets
                (A "y")
                (Txy1 :: Txy2 :: Ay :: nil).

    Definition program2 :=
      DlProgram s{ "A" }s%ssets
                s{ "R" }s%ssets
                (A "y")
                (Ay1 :: Ay2 :: nil).

    Definition program2' :=
      DlProgram s{ "A" }s%ssets
                s{ "R" }s%ssets
                (A "y")
                (Ay1 :: nil).

    Let G := ground_maps.add "R" ( ( STR "1" :: STR "2" :: nil)
                                                     ::
                                                     (STR "1" :: STR "3" :: nil) :: nil) (GroundMaps.ground_maps.empty (list (list ground_types))).

    Let G' := GroundMaps.ground_maps.add "T" nil G.
    Let G'' := GroundMaps.ground_maps.add "A" nil G'.
    Let G2 := GroundMaps.ground_maps.add "A" nil G.

    (* Let monotones := Eval compute in rules_to_monotone_op (rules program1). *)

    Let p1 := Eval compute in program_to_monotone_ops program1.
    Let p2 := Eval compute in program_to_monotone_ops program2.
    Import GroundMapsHelpers.

    Lemma transitive_closure_rules_same :
      forall (g g' g'': gm_type),
        ground_maps.In "A" g ->
        ground_maps.In "R" g ->
        ground_maps.In "T" g ->
        rule_semantics g p1 g' ->
        rule_semantics g p2 g'' ->
        ground_maps.find "A" g' = ground_maps.find "A" g''.
    Proof.
      intros g g' g''.
      intros P. revert g''.
      induction P; intros.
      - invs H.
        destruct g. simpl in H4. invc H4.
        invc H2. invc H17. invc H21. invc H25. invc H17. invc H12. invc H11.
        invc H3. invc H31. invc H35. invc H26. invc H25. invc H12. invc H7. invc H28. invc H34. invc H26. invc H35. invc H28.
        simpl in H25. Opaque proj_relation join_relations assign_vars_to_tuples select_relation. simpl in *.
        invc H17. invc H36. invc H34. simpl in *.
        repeat match goal with
        | [ H: ground_maps.find (elt:=gt_set_type) _ _ = Some _ |- _ ] =>
            eapply ground_maps.find_2 in H
               end.
        eapply ground_maps.add_3 in H26; try congruence.
        pose proof (ground_maps_MapsTo_det _ _ _ _ H7 H26).
        subst. clear H26.
        eapply ground_maps.add_3 in H4; try congruence.
        eapply ground_maps.add_3 in H17; try congruence.
        assert (v7 = v3) by (eapply ground_maps_MapsTo_det; eauto).
        subst. clear H17.
        symmetry in H33.
        eapply ground_maps.find_2 in H33.
        eapply ground_maps_MapsTo_add_iff in H33. destruct H33.
        destruct H2. subst.
        symmetry in H29. eapply ground_maps.find_2 in H29.
        assert (old_tuples2 = v10) by (eapply ground_maps_MapsTo_det; eauto).
        subst. clear H29.
        assert (v3 = v8) by (eapply ground_maps_MapsTo_det; eauto).
        subst. clear H12. invc H8. simpl in H17.
        eapply ground_maps.find_2 in H17.
        eapply ground_maps.add_3 in H17; try congruence.
        eapply ground_maps.add_3 in H17; try congruence.
        assert (v3 = v8) by (eapply ground_maps_MapsTo_det; eauto).
        subst. clear H17.
        symmetry in H23, H19. eapply ground_maps.find_2 in H23, H19.
        eapply ground_maps_MapsTo_add_iff in H23.
        destruct H23. destruct H3. subst. destruct y.
        eapply ground_maps_eqke_inversion in H5. destruct H5; subst.
        unfold ground_maps.MapsTo in H25. simpl in H25.
        eapply ground_maps_raw_MapsTo_cons_iff in H25.
        destruct H25.
        + destruct H5; subst.
          symmetry in H15. eapply ground_maps.find_2 in H15.
          assert (old_tuples = g).
          eapply ground_maps_MapsTo_det; eauto.
          subst.
          eapply ground_maps.add_3 in H19; try congruence.
          assert (old_tuples0 = v11) by (eapply ground_maps_MapsTo_det; eauto).
          subst.
          assert (ground_maps.find (elt:=gt_set_type) "A"
    (ground_maps.add "T"
       (ListSet.set_union List_Ground_Type_as_OTF.eq_dec new_tuples1
          (ListSet.set_union List_Ground_Type_as_OTF.eq_dec new_tuples0
             v11))
       (ground_maps.add "T"
          (ListSet.set_union List_Ground_Type_as_OTF.eq_dec new_tuples0
             v11)
          (ground_maps.add "A"
             (ListSet.set_union List_Ground_Type_as_OTF.eq_dec new_tuples
                g)
             {|
               ground_maps.this := ("A", g) :: l;
               ground_maps.NoDup := NoDup
             |}))) = Some ((ListSet.set_union List_Ground_Type_as_OTF.eq_dec new_tuples
                                              g))).
          {eapply ground_maps.find_1. eapply ground_maps.add_2. congruence.
           eapply ground_maps.add_2. congruence.
           eapply ground_maps.add_1. congruence.
          }
          rewrite H8.
          assert (ground_maps.find (elt:=gt_set_type) "A"
    (ground_maps.add "A"
       (ListSet.set_union List_Ground_Type_as_OTF.eq_dec new_tuples3
          (ListSet.set_union List_Ground_Type_as_OTF.eq_dec new_tuples2 g))
       (ground_maps.add "A"
          (ListSet.set_union List_Ground_Type_as_OTF.eq_dec new_tuples2 g)
          {|
            ground_maps.this := ("A", g) :: l; ground_maps.NoDup := NoDup
          |})) = Some (ListSet.set_union List_Ground_Type_as_OTF.eq_dec new_tuples3
                                         (ListSet.set_union List_Ground_Type_as_OTF.eq_dec new_tuples2 g))).
          {eapply ground_maps.find_1. eapply ground_maps.add_1. reflexivity.
          }
          rewrite H12.
          f_equal.
          eapply list_set_equality.
          simpl. split; intros.
          * eapply ListSet.set_union_iff in H17.
            eapply ListSet.set_union_iff.
            destruct H17.
            -- replace (In x new_tuples) with (match 
        anonymize_tuples
          (Vector.to_list (Vector.cons string "y" 0 (Vector.nil string)))
          v with
                                                | Some a => In x a
                                                | None => False
                                                end) in H17.
               destruct (anonymize_tuples
            (Vector.to_list (Vector.cons string "y" 0 (Vector.nil string)))
            v) eqn:Anon.
               (* Set Printing All. *)
               unfold OrdersEx.String_as_OT.t in *.
               rewrite <- H13 in Anon.
               invs Anon.
               rename H4 into Ris.
               rename H7 into Tis.
               clear H8 H12.
               clear Anon.
               clear H15.
               clear Txy Txz Txy1 Txy2 Ay Ay1 Ay2.
               clear A T.
               clear H5.
               clear H14 H3 H18 H11.
               clear H9. clear H19. clear H2.
               remember ((assign_vars_to_tuples
                {|
                  name := "R";
                  num_args := 2;
                  args :=
                    Vector.cons string "x" 1
                      (Vector.cons string "y" 0 (Vector.nil string));
                  grounded_args := ("x", STR "1") :: nil;
                  rtype := idb
                |} v8)) as R'.
               remember ((assign_vars_to_tuples
                {|
                  name := "A";
                  num_args := 1;
                  args := Vector.cons string "x" 0 (Vector.nil string);
                  grounded_args := nil;
                  rtype := idb
                |} g)) as A.
               (* Set Printing All. *)
               unfold OrdersEx.String_as_OT.t in *.
               rewrite <- HeqA in H32.
               remember ((assign_vars_to_tuples
                {|
                  name := "T";
                  num_args := 2;
                  args :=
                    Vector.cons string "x" 1
                      (Vector.cons string "y" 0 (Vector.nil string));
                  grounded_args := ("x", STR "1") :: nil;
                  rtype := idb
                |} v11)) as T.
               unfold OrdersEx.String_as_OT.t in *.
               remember ((assign_vars_to_tuples
                {|
                  name := "T";
                  num_args := 2;
                  args :=
                    Vector.cons string "x" 1
                      (Vector.cons string "z" 0 (Vector.nil string));
                  grounded_args := nil;
                  rtype := idb
                |} v11)) as T'.
               unfold OrdersEx.String_as_OT.t in *.
               rewrite <- HeqT' in H22.
               clear R.
               remember ((assign_vars_to_tuples
                {|
                  name := "R";
                  num_args := 2;
                  args :=
                    Vector.cons string "x" 1
                      (Vector.cons string "y" 0 (Vector.nil string));
                  grounded_args := nil;
                  rtype := edb
                |} v8)) as R.
               unfold OrdersEx.String_as_OT.t in *.
               rewrite <- HeqR in H32, H21.
               replace (In x new_tuples3) with (match (option_map (fun h' =>
In x h'
                                                                  ) (Some new_tuples3)) with
                                                | Some h => h
                                                | None => False
                                                end) by reflexivity.
               rewrite H30.
               replace (In x (ListSet.set_union List_Ground_Type_as_OTF.eq_dec new_tuples2 g)) with
                 (match (option_map (fun a => ListSet.set_union List_Ground_Type_as_OTF.eq_dec a g) (Some new_tuples2)) with
                  | Some h => In x h
                  | None => False
                  end) by reflexivity.
               replace (anonymize_tuples _ v6) with
                 (option_bind (anonymize_tuples (Vector.to_list (Vector.cons string "y" 0 (Vector.nil string))))  (Some v6)
                 ) by reflexivity.
               rewrite <- H31.
               rewrite H27.
               replace (In x l0) with
                 (match (option_map (In x) (Some l0)) with
                  | Some h => h
                  | None => False
                  end) in H17.
               rewrite H13 in H17.
               replace (anonymize_tuples _ v) with
                 (option_bind (anonymize_tuples (Vector.to_list (Vector.cons string "y" 0 (Vector.nil string)))) (Some v)) in H17.
               rewrite <- H24 in H17.
               rewrite HeqT in H17.
               rewrite HeqR'.
               replace ((anonymize_tuples
         (Vector.to_list (Vector.cons string "y" 0 (Vector.nil string)))
         v5)) with (option_bind (anonymize_tuples
         (Vector.to_list (Vector.cons string "y" 0 (Vector.nil string)))
                                ) (Some v5)) by reflexivity.
               rewrite <- H32.
               rewrite HeqA. rewrite HeqR.
               
                 
                       
                 
        
          
        invs H32. invs H37.
        clear Ay Ay1 Ay2. clear A.
        match goal with
        | [ |- ?a = ?b ] =>
            destruct (a) eqn:A;
            destruct (b) eqn:B
        end.
        + eapply ground_maps.find_2 in A, B.
          eapply ground_maps_raw_MapsTo_add_iff in A, B.
          destruct A, B.
          * destruct H4. congruence.
          * destruct H7. congruence.
          * destruct H4. destruct H7.
            eapply ground_maps_raw_MapsTo_add_iff in H8.
            destruct H8.
            destruct H8. congruence.
            destruct H8.
            unfold ground_maps.add in H31.
            simpl in H31.
            destruct y.
            destruct (String_as_OT.eq_dec "A" s).
            -- clear e.
               eapply ground_maps_raw_MapsTo_cons_iff in H31.
               destruct H31.
               ++ destruct H31. subst.
                  f_equal. eapply list_set_equality.
                  simpl. intros.
                  split; intros.
                  ** eapply ListSet.set_union_iff in H9.
                     eapply ListSet.set_union_iff.
                     destruct H9.
                     left.
                     clear H10.
                     destruct A. destruct H10. invs H10.
                     destruct H10. invs H29.
                     invs H40.
                     invc H44.
                     simpl in H39.
                     eapply ground_maps.find_2 in H39.
                     pose proof (proj_relation_adequacy).
                     remember ((select_relation "x" "1"
             (assign_vars_to_tuples
                {|
                  name := "R";
                  num_args := 2;
                  args :=
                    Vector.cons string "x" 1
                      (Vector.cons string "y" 0 (Vector.nil string));
                  grounded_args := ("x", STR "1") :: nil;
                  rtype := idb
                |} v4))) as v5.
                     assert (v3 = map (@rev (string * ground_types)) (map (@rev (string * ground_types)) v3)).
                     clear. induction v3.
                     { simpl. reflexivity.
                     }
                     { simpl. rewrite rev_involutive. f_equal.
                       eauto.
                     }
                     rewrite H38 in H42.
                     symmetry in H42.
                     eapply H36 in H42.
                     symmetry in H30. eapply ground_maps.find_2 in H30.
                     invc H11.
                     invc H45. invc H48. simpl in H43.
                     eapply ground_maps.find_2 in H43.
                     clear H36.
                     eapply ground_maps.add_3 in H39; try congruence.
                     pose proof (ground_maps_MapsTo_det).
                     specialize (H11 _ _ _ old_tuples2 H).
                     specialize (H11 H30). subst.
                     clear H. clear H35 H37.
                     clear H40. clear H34.
                     clear H32.
                     
                     eapply proj_relation_adequacy in H42.
        invs H16.
        symmetry in H14. eapply ground_maps.find_2 in H14.
        eapply ground_maps_MapsTo_add_iff in H14. destruct H14.
        + destruct H0. subst. invs H8.
          invs H10. invs H17.
          eapply ground_maps.find_2 in H3. simpl in H3.
          eapply ground_maps.add_3 in H3.
    

    Lemma transitive_closure_same :
      forall (g g' g'': gm_type),
        program_semantics g p1 g' ->        
        ground_maps.In "R" g ->
        ground_maps.find "R" g <> Some nil ->
        ground_maps.find "A" g = Some nil ->
        ground_maps.find "T" g = Some nil ->
        
        program_semantics g p2 g'' ->
        ground_maps.Equal g' g''.
    Proof.
      clear G' G'' G2 G.
      clear Txy Txz Txy1 Txy2 Ay Ay1 Ay2.
      clear T A. clear R.
      intros g g' g'' P.
      revert g''. induction P; intros.
      - invs H5.
        + eapply ground_maps_eq_refl.
        + pose proof (rule_semantics_det).
          
          
      destruct g.
      induction this; intros.
      - 
      
      
      unfold program1. unfold program2. induction fuel; intros.
      - unfold program_semantics_eval in *. simpl in *. exists 0. simpl.
        intros. inversion H2. inversion H3. subst.
        unfold Equal. reflexivity.
      - unfold program_semantics_eval in *. simpl in *.
        unfold Vector.to_list in IHfuel.
        unfold Vector.to_list in H2.
        rewrite H1 in H2.
        unfold assign_vars_to_tuples in H2. simpl in H2.
        destruct (find (elt:=list (list ground_types)) "T"
                   (mapi
                      (fun (k : key)
                         (e : ListSet.set List_Ground_Type_as_OTF.t) =>
                       if string_dec k "A"
                       then
                        ListSet.set_union List_Ground_Type_as_OTF.eq_dec
                          (ListSet.empty_set List_Ground_Type_as_OTF.t) e
                       else e) g)) eqn:D; [ | inversion H2].
        destruct (find (elt:=list (list ground_types)) "R"
                   (mapi
                      (fun (k : key)
                         (e : ListSet.set List_Ground_Type_as_OTF.t) =>
                       if string_dec k "A"
                       then
                        ListSet.set_union List_Ground_Type_as_OTF.eq_dec
                          (ListSet.empty_set List_Ground_Type_as_OTF.t) e
                       else e) g)) eqn:D'; [ | inversion H2].
        destruct (proj_relation ("x" :: "y" :: nil)
             (join_relations ("z" :: nil)
                (fold_left
                   (fun (acc : ListSet.set (list (string * ground_types)))
                      (elmt : list ground_types) =>
                    match
                      variable_list_groundings_to_assoc_list Txz elmt
                    with
                    | Some l =>
                        ListSet.set_add str_gt_list_ot.eq_dec l acc
                    | None => acc
                    end) l (ListSet.empty_set tup_type))
                (fold_left
                   (fun (acc : ListSet.set (list (string * ground_types)))
                      (elmt : list ground_types) =>
                    match
                      variable_list_groundings_to_assoc_list 
                        (R "z" "y") elmt
                    with
                    | Some l =>
                        ListSet.set_add str_gt_list_ot.eq_dec l acc
                    | None => acc
                    end) l0 (ListSet.empty_set tup_type)))) eqn:D''.
        + unfold proj_relation in H2.
          remember ((fold_left
                   (fun (acc : ListSet.set (list (string * ground_types)))
                      (elmt : list ground_types) =>
                    match
                      variable_list_groundings_to_assoc_list Txz elmt
                    with
                    | Some l =>
                        ListSet.set_add str_gt_list_ot.eq_dec l acc
                    | None => acc
                    end) l (ListSet.empty_set tup_type))) as fold1.
          remember ((fold_left
                   (fun (acc : ListSet.set (list (string * ground_types)))
                      (elmt : list ground_types) =>
                    match
                      variable_list_groundings_to_assoc_list 
                        (R "z" "y") elmt
                    with
                    | Some l =>
                        ListSet.set_add str_gt_list_ot.eq_dec l acc
                    | None => acc
                    end) l0 (ListSet.empty_set tup_type))) as fold2.
          simpl in H2.
          destruct (ListSet.set_fold_left
             (fun (acc : option (ListSet.set tup_type)) (elmt : tup_type)
              =>
              match proj_tuples ("x" :: "y" :: nil) elmt with
              | Some tup =>
                  option_map (ListSet.set_add str_gt_list_ot.eq_dec tup)
                    acc
              | None => None
              end)
             (join_relations ("z" :: nil)
                             fold1 fold2)) eqn:D1; [ | inversion H2].
          destruct (anonymize_tuples ("x" :: "y" :: nil)) eqn:D2; [ | inversion H2].
          destruct (find (elt:=list (list ground_types)) "R"
                 (mapi
                    (fun (k : key)
                       (e : ListSet.set List_Ground_Type_as_OTF.t) =>
                     if string_dec k "T"
                     then
                      ListSet.set_union List_Ground_Type_as_OTF.eq_dec l1
                        e
                     else e)
                    (mapi
                       (fun (k : key)
                          (e : ListSet.set List_Ground_Type_as_OTF.t) =>
                        if string_dec k "A"
                        then
                         ListSet.set_union List_Ground_Type_as_OTF.eq_dec
                           (ListSet.empty_set List_Ground_Type_as_OTF.t) e
                        else e) g))) eqn:D3; [ | inversion H2].
          destruct (ListSet.set_fold_left
             (fun (acc : option (ListSet.set tup_type)) (elmt : tup_type)
              =>
              match proj_tuples ("x" :: "y" :: nil) elmt with
              | Some tup =>
                  option_map (ListSet.set_add str_gt_list_ot.eq_dec tup)
                    acc
              | None => None
              end)
             (fold_left
                (fun (acc : ListSet.set (list (string * ground_types)))
                   (elmt : list ground_types) =>
                 match
                   variable_list_groundings_to_assoc_list (R "x" "y") elmt
                 with
                 | Some l => ListSet.set_add str_gt_list_ot.eq_dec l acc
                 | None => acc
                 end) l2 (ListSet.empty_set tup_type))) eqn:D4; [ | inversion H2].
          destruct (match anonymize_tuples ("x" :: "y" :: nil) s1 with
         | Some new_tuples =>
             Some
               (mapi
                  (fun (k : key)
                     (e : ListSet.set List_Ground_Type_as_OTF.t) =>
                   if string_dec k "T"
                   then
                    ListSet.set_union List_Ground_Type_as_OTF.eq_dec
                      new_tuples e
                   else e)
                  (mapi
                     (fun (k : key)
                        (e : ListSet.set List_Ground_Type_as_OTF.t) =>
                      if string_dec k "T"
                      then
                       ListSet.set_union List_Ground_Type_as_OTF.eq_dec l1
                         e
                      else e)
                     (mapi
                        (fun (k : key)
                           (e : ListSet.set List_Ground_Type_as_OTF.t) =>
                         if string_dec k "A"
                         then
                          ListSet.set_union List_Ground_Type_as_OTF.eq_dec
                            (ListSet.empty_set List_Ground_Type_as_OTF.t)
                            e
                         else e) g)))
         | None => None
         end) eqn:D5; [ | inversion H2].
          
             (Some (ListSet.empty_set tup_type))) eqn:D1; [ | inversion H2].
          

          destruct (proj_relation ("x" :: "y" :: nil)
             (join_relations ("z" :: nil)
                (fold_left
                   (fun (acc : ListSet.set (list (string * ground_types)))
                      (elmt : list ground_types) =>
                    match
                      variable_list_groundings_to_assoc_list Txz elmt
                    with
                    | Some l =>
                        ListSet.set_add str_gt_list_ot.eq_dec l acc
                    | None => acc
                    end) l (ListSet.empty_set tup_type))
                (fold_left
                   (fun (acc : ListSet.set (list (string * ground_types)))
                      (elmt : list ground_types) =>
                    match
                      variable_list_groundings_to_assoc_list 
                        (R "z" "y") elmt
                    with
                    | Some l =>
                        ListSet.set_add str_gt_list_ot.eq_dec l acc
                    | None => acc
                    end) l0 (ListSet.empty_set tup_type)))) eqn:D'''.
          inversion D''. subst.
          
          remember ( proj_relation ("x" :: "y" :: nil)
                                   (join_relations ("z" :: nil) fold1 fold2)) as p1.

          unfold proj_relation in H2. simpl in H2.
          destruct ( ListSet.set_fold_left
             (fun (acc : option (ListSet.set tup_type)) (elmt : tup_type)
              =>
              match proj_tuples ("x" :: "y" :: nil) elmt with
              | Some tup =>
                  option_map (ListSet.set_add str_gt_list_ot.eq_dec tup)
                    acc
              | None => None
              end) (join_relations ("z" :: nil) fold1 fold2)) eqn:D1; [ | inversion H2].
          erewrite D''' in H2.
      
      destruct g. induction this0; intros.
      - inversion H. simpl in H3.
        inversion H3.
      -  unfold program_semantics_eval in *. simpl in *.
         
      

    (* Let meaning := program_semantics_eval G2 program2' 1. *)

    (* Let find_meaning (m: option GroundMaps.ground_maps.t) x := match m with *)
                            (* | Some m' => GroundMaps.ground_maps.MapS.find x m' *)
                            (* | None => None *)
                                                               (* end. *)

    (* Eval compute in (find_meaning meaning "R"). *)

      (* Let monotones' := *)
      (*       Eval compute in *)
      (*       List.fold_left *)
      (*         (fun (acc: list (string * monotone_ops)) (elmt: string * (list (option monotone_ops))) => *)
      (*            let (name, oms) := elmt in *)
      (*            List.fold_left (fun (acc': list (string * monotone_ops)) *)
      (*                              (elmt: option monotone_ops) => *)
                                   
      (*                              match elmt with *)
      (*                              | Some m => *)
      (*                                  (name, m) :: acc' *)
      (*                              | None => *)
      (*                                  acc *)
      (*                              end) *)
      (*                           oms *)
      (*                           acc *)
      (*         ) *)
      (*         monotones *)
      (*         nil. *)

    (* Print monotones'. *)

    (* Let meaning := Eval compute in program_semantics_eval G'' program1 1. *)
    
    
    (* Let meaning := Eval compute in program_semantics_eval G'' (Txy) monotones' 2. *)

    (*  Let find_meaning x := match meaning with *)
    (*                         | Some m => GroundMaps.ground_maps.MapS.find x m *)
    (*                         | None => None *)
    (*                        end. *)
    (* Eval compute in (find_meaning "T"). *)

    
  End RelDecls.
End TransitiveClosureProgram.
