From Coq Require Import List String Arith Psatz.

From VeriFGH Require Import DatalogProps DatalogSemantics MoreOrders MonotonicityTheorems JoinHelpers GroundMapsHelpers.

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

P2:
t(x,y) = r(x,y)
t(x,y) = r(x,z), t(z,y)

     *)

    Let Txy := T "x" "y".
    Let Txz := T "x" "z".

    Declare Scope rel_scope.
    Delimit Scope rel_scope with rel.

    Notation "{ r :- }" := (rule_def_empty r) : rel_scope.
    Notation "{ r :- x } " := (rule_def r (x :: nil)) : rel_scope.
    Notation "{ r :- x ; y ; .. ; z }" := (rule_def r (cons x (cons y .. (cons z nil) ..))) : rel_scope.
    Print rule_def_exists.
    Notation "{ r 'exists' a :- x ; y ; .. ; z }" := (rule_def_exists r (string_sets.add a string_sets.empty) (cons x (cons y .. (cons z nil)  .. ))) : rel_scope.
    Notation "{ r 'exists'  a ; b ; .. ; c  :- x ; y ; .. ; z }" := (rule_def_exists r (string_sets.add a (string_sets.add b .. (string_sets.add c (string_sets.empty)) .. ) ) (cons x (cons y .. ( cons z nil ) .. ))) : rel_scope.
    Local Open Scope rel_scope.

    Let Txy1 := { (T "x" "y") :- (R "x" "y") }.
    Let P1_Txy2 := { (T "x" "y") exists "z" :- (T "x" "z"); R "z" "y" }.
    Let P2_Txy2 := { T "x" "y" exists "z" :- R "x" "z"; T "z" "y" }.

    Declare Scope string_sets_scope.
    Delimit Scope string_sets_scope with ssets.
    Notation "'s{' x '}s'" := (string_sets.add x string_sets.empty) : string_sets_scope.
    Notation "'s{' x ; y ; .. ; z '}s'" := (string_sets.add x (string_sets.add y .. (string_sets.add z string_sets.empty) ..)) : string_sets_scope.
    Eval compute in s{ "x"; "y"; "z" }s%ssets.
    Print DlProgram.
    Arguments DlProgram (idbs edbs)%ssets answer rules%list_scope.

    Let p1 := DlProgram s{ "T" }s%ssets s{ "R" }s%ssets Txy (Txy1 :: P1_Txy2 :: nil).
    Let p2 := DlProgram s{ "T" }s%ssets s{ "R" }s %ssets Txy (Txy1 :: P2_Txy2 :: nil).

    Let m1 := program_to_monotone_ops p1.
    Let m2 := program_to_monotone_ops p2.

    Require Import Program.Equality.

    Import ListSet.
    Print join_tuples.

     Lemma ground_maps_find_some_same :
      forall (s: string) (g: gm_type) l l',
      ground_maps.find (elt:=gt_set_type) s
                       (ground_maps.add s l g) = Some l' ->
      l = l'.
    Proof.
      intros.
      eapply ground_maps.find_2 in H.
      eapply ground_maps_MapsTo_add_iff in H. destruct H.
      - destruct H. subst. reflexivity.
      - destruct H. congruence.
    Qed.

    Lemma ground_maps_find_some_diff :
      forall (s s': string) (g: gm_type) l l',
        s <> s' ->
        ground_maps.find (elt:=gt_set_type) s
                         (ground_maps.add s' l g) = Some l' ->
        ground_maps.find (elt:=gt_set_type) s
                         g = Some l'.
    Proof.
      intros.
      eapply ground_maps.find_2 in H0. eapply ground_maps_MapsTo_add_iff in H0; destruct H0; match goal with
                                                                                             | [ H: _ /\ _ |- _ ] => destruct H
                                                                                             end; try congruence.
      eapply ground_maps.find_1. eauto.
    Qed.

    Lemma rule_semantics_same :
      forall g g' g'',
        rule_semantics g m1 g' ->
        rule_semantics g m2 g'' ->
        g' = g''.
    Proof.
      destruct g. induction this; intros.
      - unfold m1, m2 in *.
        unfold p1, p2 in *. unfold program_to_monotone_ops in *. simpl in *.
        invs H. invs H12. invs H17. invs H0. invs H22. invs H27.
        simpl in H20. unfold ground_maps.find in H20. simpl in H20. congruence.
      - unfold m1, m2 in *. unfold program_to_monotone_ops, p1, p2 in *.
        simpl in *.
        invs H. invs H12. invs H17. invs H0. invs H22. invs H27.
        assert (NT: Some new_tuples = Some new_tuples1).
        { rewrite H18. rewrite H8.
          invc H14. invc H6. invc H14.
          invc H21. invc H29. invc H4. invc H28. invc H30.
          Opaque proj_relation join_relations assign_vars_to_tuples.
          simpl in *.
          repeat match goal with
                 | [ H: ?x = Some _, H': ?x = Some _ |- _ ] =>
                     rewrite H' in H;
                     invc H
                 end.
          enough (Some v1 = Some v).
          invc H1. reflexivity.
          rewrite <- H24. rewrite <- H26.
          f_equal.
          (* True by some combination of renaming and commutativity *)
          admit.
        }
        invc NT.
        assert (OT1: Some old_tuples = Some old_tuples1).
        {
          rewrite H20. rewrite H10. reflexivity.
        }
        invc OT1.
        f_equal. f_equal.
        + enough (Some new_tuples0 = Some new_tuples2). invc H1.
          reflexivity.
          rewrite H23. rewrite H13.
          invc H19. match goal with
                    | [ |- anonymize_tuples ?x _ = _ ] =>
                        remember (x) as V
                    end.
          replace (anonymize_tuples V v2) with
            (option_bind (anonymize_tuples V)
                         (Some v2)) by reflexivity.
          rewrite <- H24.
          replace (anonymize_tuples V v0) with
            (option_bind (anonymize_tuples V)
                         (Some v0)) by reflexivity.
          invc H9. rewrite <- H26.
          invc H19.
          f_equal. f_equal.
          invc H4.
          f_equal.
          simpl in H9.
          eapply ground_maps_find_some_diff in H9.
          simpl in H3. eapply ground_maps_find_some_diff in H3.
          rewrite H9 in H3. invc H3. reflexivity.
          congruence.
          congruence.
        + enough (Some old_tuples0 = Some old_tuples2).
          invc H1. reflexivity.
          rewrite H25. rewrite H15.
          f_equal.
    Admitted.
          

    Lemma join_tuples_cons :
      forall (jvs: list string) (t1 t2: tup_type) (s: string) (g: ground_types),
        jvs <> nil ->
        join_tuples jvs ((s, g) :: t1) t2 = option_map (cons (s, g)) (join_tuples jvs t1 t2).
    Proof.
      induction jvs; intros.
      - congruence.
      - destruct jvs.
        + remember (join_tuples (a :: nil) t1 t2) as J.
          simpl in HeqJ.
          destruct (check_join_vars (a :: nil) t1 t2) eqn:C.
          pose proof join_relations_symmetric.
    Admitted.
          (* * Ltac destruct_hyp_match' H := *)
              (* let Htype := type of H in *)
              (* match Htype with *)
              (* | _ = match ?a with *)
                    (* | Some _ => _ *)
                    (* | None => _ *)
                    (* end => *)
                  (* let D := fresh "D" in *)
                  (* destruct (a) eqn:D; try congruence *)
              (* end. *)
            (* destruct_hyp_match' HeqJ. *)
            (* -- destruct_hyp_match' HeqJ. *)
               (* ++ destruct_hyp_match' HeqJ. *)
                  (* rewrite HeqJ. simpl. *)
                  (* remember (check_join_vars (a :: nil) ((s, g) :: t1) t2) as CJ. *)
                  (* unfold check_join_vars in HeqCJ. *)
                  
                  (* simpl in HeqCJ. *)
                  

    (* Lemma join_tuples_commutative : *)
    (*   forall (jvs: list string) (t1 t2: tup_type), *)
    (*     join_tuples jvs t1 t2 = join_tuples jvs t2 t1. *)
    (* Proof. *)
    (*   induction t1; intros.                           *)
    (*   - unfold join_tuples. *)
    (*     induction jvs. *)
    (*     + simpl. *)
    (*       destruct_match_goal'. *)
    (*       rewrite app_nil_r. reflexivity. *)
    (*       reflexivity. *)
    (*     + unfold check_join_vars. simpl. *)
    (*       assert (fold_left *)
    (*   (fun (acc : bool) (_ : string) => if acc then false else false) jvs *)
    (*   false = false). *)
    (*       { clear. *)
    (*         induction jvs; intros. *)
    (*         - simpl. reflexivity. *)
    (*         - simpl. eauto. *)
    (*       } *)
    (*       assert (fold_left *)
    (*                 (fun (acc : bool) (elmt : string) => *)
    (*                    if acc *)
    (*                    then match assoc_lookup t2 elmt with *)
    (*                         | Some _ | _ => false *)
    (*                         end *)
    (*                    else false) jvs false = false). *)
    (*       {clear. induction jvs; intros; simpl; eauto. *)
    (*       } *)
    (*       rewrite H. *)
    (*       destruct (assoc_lookup t2 a) eqn:T2. *)
          
    (*       rewrite H0. reflexivity. *)
    (*       rewrite H0. reflexivity. *)
    (*   - simpl. unfold check_join_vars. *)
        
          

    (* Lemma join_relations_commutative : *)
    (*   forall (jvs: list string) (l1 l2: ListSet.set tup_type), *)
    (*     join_relations jvs l1 l2 = join_relations jvs l2 l1. *)
    (* Proof. *)
    (*   induction l1; intros. *)
    (*   - Opaque join_tuples. simpl. *)
    (*     induction l2. *)
    (*     + simpl. reflexivity. *)
    (*     + simpl. eauto. *)
    (*   - simpl. *)
    (*     revert IHl1. revert l1. induction l2; intros. *)
    (*     + simpl. specialize (IHl1 nil). *)
    (*       unfold join_relations in IHl1. simpl in IHl1. eauto. *)
    (*     + simpl. destruct (join_tuples jvs a a0) eqn:B. *)
   

    Lemma program_semantics_terminates :
      forall g g' m,
        program_semantics g m g' ->
        exists g'',
          program_semantics g'' m g' /\
            ground_maps.Equal g'' g'.
    Proof.
      intros g g' m. intros P. induction P; intros.
      - eapply ground_maps_equality in H0.
        subst. exists g'. split.
        + econstructor. eassumption. eapply ground_maps_eq_refl.
        + eapply ground_maps_eq_refl.
      - eapply IHP.
    Qed.

    Lemma left_right_recursion_same_general :
      forall g g' g'',
        program_semantics g m1 g' ->
        program_semantics g m2 g'' ->
        g' = g''.
    Proof.
      intros g g' g'' P.
      revert g''. dependent induction P; intros.
      - invs H1.
        + fold m1 in H.
          pose proof (rule_semantics_same).
          specialize (H4 _ _ _ H H2).
          subst. reflexivity.
        + fold m1 in H.
          pose proof (rule_semantics_same _ _ _ H H2).
          subst. eapply H3 in H0. contradiction.
      - unfold p1 in IHP.
        fold m1 in H, P.
        specialize (IHP eq_refl).
        invs H1.
        + pose proof (rule_semantics_same _ _ _ H H2).
          subst. eapply H0 in H3. contradiction.
        + pose proof (rule_semantics_same _ _ _ H H2).
          subst.
          specialize (IHP _ H4).
          eauto.
    Qed.
                        


    Lemma left_right_recursion_same :
      forall g g' g'',
        program_semantics g m1 g' ->
        program_semantics g m2 g'' ->
        ground_maps.find "T" g' = ground_maps.find "T" g''.
    Proof.
      intros.
      pose proof (left_right_recursion_same_general _ _ _ H H0).
      subst. reflexivity.
    Qed.
(*    intros.
      invs H; invs H0.
      - pose proof (rule_semantics_same).
        specialize (H5 _ _ _ H1 H3).
        subst. reflexivity.
      - pose proof (rule_semantics_same).
        specialize (H6 _ _ _ H1 H3).
        subst.
        eapply H4 in H2.
        contradiction.
      - pose proof (rule_semantics_same).
        specialize (H6 _ _ _ H1 H4).
        subst. eapply H2 in H5. contradiction.
      - pose proof (rule_semantics_same).
        specialize (H7 _ _ _ H1 H4).
        subst.


      
      intros g g' g''.
      intros P. revert g''.
      dependent induction P; intros.
      - invs H1.
        eapply ground_maps_equality in H0, H3.
        subst.
        reflexivity.
        eapply ground_maps_equality in H0. subst.
        unfold p1 in H. unfold program_to_monotone_ops in H. simpl in H.
        unfold m2 in *. unfold program_to_monotone_ops in *.
        simpl in *.
        invs H. invs H2.
        invs H20. invc H25. invc H17. invc H7.
        invc H12. invc H8. invs H15.
        invc H30.
        invc H19.
        invc H25.
        remember ((Vector.to_list
             (Vector.cons string "x" 1
                          (Vector.cons string "y" 0 (Vector.nil string))))) as V.
        (* Set Printing All. *)
        unfold OrdersEx.String_as_OT.t  in *.
        rewrite <- HeqV in H29.
        replace (proj_relation V (assign_vars_to_tuples (R "x" "y") v6)) with
          (option_bind (fun b => proj_relation V (assign_vars_to_tuples (R "x" "y") b)) (Some v6)) in H29.
        rewrite <- H8 in H29. clear H8. clear v6.
        remember ((Vector.to_list (args (T "x" "y")))) as Vl.
        unfold OrdersEx.String_as_OT.t in *.
        rewrite <- HeqVl in H26.
        replace (anonymize_tuples Vl v4) with
          (option_bind (anonymize_tuples Vl) (Some v4)) in H26 by reflexivity.
        rewrite <- H29 in H26. clear H29.
        symmetry in H28. eapply ground_maps.find_2 in H28.
        unfold ground_maps.MapsTo in H28.
        eapply GroundMapsHelpers.ground_maps_raw_MapsTo_add_iff in H28. destruct H28.
        + destruct H0. subst.
          invc H17.
          invc H27. invc H29.
          invc H9. invc H27. invc H28. invc H31.
          simpl in H17, H19, H9, H25. rewrite H17 in H25. invc H25.
          rewrite H19 in H9. invc H9.
          Opaque proj_relation join_relations assign_vars_to_tuples.
          unfold Vector.to_list in *.
          assert (Vs: Some v = Some v0).
          { rewrite <- H29. rewrite <- H24.
            f_equal.
            rewrite join_relations_symmetric.
            admit.
          }
          invs Vs.
          rewrite <- H18 in H13. invc H13.
          rewrite <- H11 in H16. invc H16. clear H10. clear H0. clear Vs.
          clear H12. clear H14.
          replace (anonymize_tuples
          ((fix fold_right_fix
              (n : nat) (v : Vector.t string n) (b : list string) {struct
               v} : list string :=
              match v with
              | Vector.nil _ => b
              | Vector.cons _ a n0 w => a :: fold_right_fix n0 w b
              end) (num_args (T "x" "y")) (args (T "x" "y")) nil) v1) with
            (option_bind (anonymize_tuples
          ((fix fold_right_fix
              (n : nat) (v : Vector.t string n) (b : list string) {struct
               v} : list string :=
              match v with
              | Vector.nil _ => b
              | Vector.cons _ a n0 w => a :: fold_right_fix n0 w b
              end) (num_args (T "x" "y")) (args (T "x" "y")) nil)) (Some v1)) in H21 by reflexivity. rewrite <- H22 in H21.
          replace ((proj_relation ("x" :: "y" :: nil)
                                  (assign_vars_to_tuples (R "x" "y") v3))) with
            (option_bind (fun v =>
                            (proj_relation ("x" :: "y" :: nil)
                                           (assign_vars_to_tuples (R "x" "y") v))) (Some v3)) in H21 by reflexivity.
          rewrite <- H6 in H21.
          replace (anonymize_tuples
          ((fix fold_right_fix
              (n : nat) (v : Vector.t string n) (b : list string) {struct
               v} : list string :=
              match v with
              | Vector.nil _ => b
              | Vector.cons _ a n0 w => a :: fold_right_fix n0 w b
              end) (num_args (T "x" "y")) (args (T "x" "y")) nil) v0) with
            (option_bind (anonymize_tuples
          ((fix fold_right_fix
              (n : nat) (v : Vector.t string n) (b : list string) {struct
               v} : list string :=
              match v with
              | Vector.nil _ => b
              | Vector.cons _ a n0 w => a :: fold_right_fix n0 w b
              end) (num_args (T "x" "y")) (args (T "x" "y")) nil)) (Some v0)) in H11 by reflexivity.
          rewrite <- H29 in H11.
          assert (ground_maps.find (elt:=gt_set_type) "T"
    (ground_maps.add "T"
       (set_union List_Ground_Type_as_OTF.eq_dec new_tuples2
          (set_union List_Ground_Type_as_OTF.eq_dec new_tuples old_tuples0))
       (ground_maps.add "T"
          (set_union List_Ground_Type_as_OTF.eq_dec new_tuples old_tuples0)
          g')) = ground_maps.find (elt:=gt_set_type) "T"
    (ground_maps.add "T"
       (set_union List_Ground_Type_as_OTF.eq_dec new_tuples2
          (set_union List_Ground_Type_as_OTF.eq_dec new_tuples old_tuples0))
       g')).
          {
            match goal with
            | [ |- ?x = ?y ] =>
                let X := fresh "X" in
                let Y := fresh "Y" in
                remember (x) as X;
                remember (y) as Y;
                destruct X; destruct Y
            end.
            - symmetry in HeqX, HeqY. eapply ground_maps.find_2 in HeqX, HeqY.
              eapply ground_maps_MapsTo_add_iff in HeqX, HeqY.
              destruct HeqX; destruct HeqY; try match goal with
                                            | [ H: "T" <> "T" /\ _ |- _ ] =>
                                                destruct H; congruence
                                                end.
              destruct H0, H5.
              subst. reflexivity.
            - (* this is a contradiction, there should be some way to prove it. likely a lemma would be good. *)
              admit.
            - (* same *)
              admit.
            - reflexivity.
          }
          rewrite H7.
          invc H4.
          * invc H5. invc H31. invc H35.
            invc H16. invc H10. invc H14.
            eapply ground_maps_equality in H8.
            simpl in H9.
            eapply ground_maps.find_2 in H9.
            eapply ground_maps.add_3 in H9; try congruence.
            eapply ground_maps.add_3 in H9; try congruence.
            eapply ground_maps.add_3 in H9; try congruence.
            eapply ground_maps.find_1 in H9.
            unfold gt_set_type in *. unfold set in *.
            unfold List_Ground_Type_as_OTF.t in *.
            rewrite H9 in H17.
            invc H17.
            rewrite H19 in H18. invc H18.
            symmetry in H23. eapply ground_maps.find_2 in H23.
            eapply ground_maps_MapsTo_add_iff in H23;
              destruct H23; try match goal with
                                | [ H: "T" <> "T" /\ _ |- _ ] =>
                                    destruct H; congruence
                                end.
            invc H16. invc H18. invc H27.
            simpl in H16. simpl in H14.
            eapply ground_maps.find_2 in H14, H16.
            eapply ground_maps_MapsTo_add_iff in H14, H16;
              destruct H14, H16;
              try match goal with
                  | [ H : "T" <> "T" /\ _ |- _ ] =>
                      destruct H; congruence
                  | [ H: "R" = "T" /\ _ |- _ ] =>
                      destruct H; congruence
                  end.
            destruct H5, H10. subst.
            eapply ground_maps.add_3 in H14; try congruence.
            eapply ground_maps.find_1 in H14.
            rewrite H14 in H9. invc H9.
            clear H5 H10. clear H12.
            rewrite H19 in *.
            clear H13. destruct H4. invc H5. clear H9.
            rewrite <- H19.
            assert ((ground_maps.find (elt:=list (list ground_types))
                (name (R "x" "y"))
                (ground_maps.add "T"
                   (set_union List_Ground_Type_as_OTF.eq_dec new_tuples v6)
                   g')) = ground_maps.find "R" g').
            simpl.
            destruct (ground_maps.find (elt:=list (list ground_types)) "R"
    (ground_maps.add "T"
                     (set_union List_Ground_Type_as_OTF.eq_dec new_tuples v6) g')) eqn:RT.
            eapply ground_maps.find_2 in RT.
            eapply ground_maps_MapsTo_add_iff in RT;
              destruct RT;
              try match goal with
                  | [ H: "R" = "T" /\ _ |- _ ] =>
                      destruct H; congruence
                  end.
            destruct H5.
            symmetry. eapply ground_maps.find_1. eauto.
            eapply ground_maps.find_2 in H14.
            eapply ground_maps.add_2 in H14.
            eapply ground_maps.find_1 in H14. erewrite H14 in RT.
            congruence.
            congruence.
            unfold List_Ground_Type_as_OTF.t in *. unfold set in *.
            rewrite H5 in H26.
            rewrite H5 in H21.
            rewrite <- H26 in H21. invc H21.
            replace (anonymize_tuples (Vector.to_list (args (T "x" "y"))) v2) with (option_bind (anonymize_tuples (Vector.to_list (args (T "x" "y")))) (Some v2)) in H30 by reflexivity.
            rewrite <- H31 in H30.
            clear H31. clear v2.
            symmetry in H33. eapply ground_maps.find_2 in H33.
            eapply ground_maps_MapsTo_add_iff in H33;
              destruct H33;
              try match goal with
                  | [ H: "T" <> "T" /\ _ |- _ ] =>
                      destruct H; congruence
                  end.
            destruct H9. subst.
            clear H9.
            replace (anonymize_tuples (Vector.to_list (args (T "x" "y"))) v) with (option_bind (anonymize_tuples (Vector.to_list (args (T "x" "y")))) (Some v)) in H25 by reflexivity. rewrite <- H32 in H25.
            clear H32. clear v.
            replace ((proj_relation ("x" :: "y" :: nil)
                                    (assign_vars_to_tuples (R "x" "y") v7))) with
              (option_bind (fun v => (proj_relation ("x" :: "y" :: nil)
                                                 (assign_vars_to_tuples (R "x" "y") v))) (Some v7)) in H30 by reflexivity.
            rewrite <- H14 in H30.
            replace (proj_relation ("x" :: "y" :: nil) (join_relations ("z" :: nil)
                (assign_vars_to_tuples (T "x" "z") v6)
                (assign_vars_to_tuples (R "z" "y") v7))) with
              (option_bind (proj_relation ("x" :: "y" :: nil))
                 (option_map_map (fun a b =>
                 (join_relations ("z" :: nil)
                (assign_vars_to_tuples (T "x" "z") a)
                (assign_vars_to_tuples (R "z" "y") b)))
                                 (Some v6) (Some v7))) in H11 by reflexivity.
            rewrite <-  H14 in *.
            rewrite <- H19 in *.
            pose proof (rule_semantics_det).
            specialize (H9 _ _ _ _ H20 H15).
            rewrite <- H9 at 1. reflexivity.
          * invc H5. invc H32. invc H36. invc H25. invc H12. invc H16. invc H25. invc H36. invc H28.
            simpl in *.
            repeat match goal with
                   | [ H: ground_maps.find (elt:=gt_set_type) ?x (ground_maps.add ?x _ _) = Some _ |- _ ] =>
                       eapply ground_maps_find_some_same in H
                   end.
            subst.
            repeat match goal with
                   | [ H: ground_maps.find (elt:=gt_set_type) ?x (ground_maps.add ?y _ _ ) = Some _ |- _ ] =>
                       eapply ground_maps_find_some_diff in H;
                       try congruence
                   end.
            rewrite H16 in H10. invc H10.
            repeat match goal with
                   | [H: Some _ = ground_maps.find (elt:=gt_set_type) ?x (ground_maps.add ?x _ _ ) |- _ ] =>
                       symmetry in H
                   | [ H: ground_maps.find (elt:=gt_set_type) ?x (ground_maps.add ?x _ _) = Some _ |- _ ] =>
                       eapply ground_maps_find_some_same in H;
                       symmetry in H
                   end.
            subst.
            repeat match goal with
                   | [ H: ?a = Some _, H': ?a = Some _ |- _ ] =>
                       rewrite H' in H; invc H
                   end.
            invs H15. invs H34. invc H17.
            invc H22.
            simpl in H10. eapply ground_maps_find_some_diff in H10.
             repeat match goal with
                   | [ H: ?a = Some _, H': ?a = Some _ |- _ ] =>
                       rewrite H' in H; invc H
                    end.
            clear H12.
            pose proof (rule_semantics_det _ _ _ _ H15 H20).
            rewrite <- H4 in H9. rewrite <- H4 in *.
            pose proof (ground_maps_eq_refl g').
            eapply H3 in H5. contradiction.
            congruence.
        + destruct H0. congruence.
        + eapply (ground_maps.NoDup g').
        + simpl. reflexivity.
      - unfold p1 in IHP. simpl in IHP. unfold Txy, Txy1, P1_Txy2 in *.
        specialize (IHP eq_refl).
        
        assert (program_semantics g (program_to_monotone_ops p1) g'').
        {
          eapply program_step_continue.
          eauto. eauto. eauto.
        }
        invs H1.
        
            
            (* unfold ground_maps.Equal in H8. *)
          rewrite H0. clear H0.
          
          negate_negated H3.
          rewrite <- H7 at 1.
          unfold ground_maps.Equal. intros. 
          
            
          
          
        
        invc H26.
        invc H1.
        + invc H. invc H31.
          invc H35.
          replace (ground_maps.find (elt:=gt_set_type) "T"
    (ground_maps.add "T"
       (ListSet.set_union List_Ground_Type_as_OTF.eq_dec new_tuples2
          old_tuples2)
       (ground_maps.add "T"
          (ListSet.set_union List_Ground_Type_as_OTF.eq_dec new_tuples
                             old_tuples) g''))) with
            (option_bind (fun b => ground_maps.find (elt:=gt_set_type) "T"
    (ground_maps.add "T"
       (ListSet.set_union List_Ground_Type_as_OTF.eq_dec new_tuples2 old_tuples2) (ground_maps.add "T" (ListSet.set_union List_Ground_Type_as_OTF.eq_dec b
                                                                                                                          old_tuples) g''))) (Some new_tuples)) by reflexivity.
          
 *)
    End RelDecls.
End TransitiveClosureProgram.
