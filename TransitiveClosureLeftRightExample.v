From Coq Require Import List String Arith Psatz.

From VeriFGH Require Import DatalogProps DatalogSemantics GroundMaps MonotonicityTheorems JoinHelpers GroundMapsHelpers.

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

    (* TODO *)
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
          

    (* Don't need to prove *)
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
    End RelDecls.
End TransitiveClosureProgram.
