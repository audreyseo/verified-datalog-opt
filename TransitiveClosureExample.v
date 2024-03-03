From Coq Require Import List String Arith Psatz.

From VeriFGH Require Import DatalogProps DatalogSemantics MoreOrders.

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

    Let G := MoreOrders.ground_maps.MapS.add "R" ( ( STR "1" :: STR "2" :: nil)
                                                     ::
                                                     (STR "1" :: STR "3" :: nil) :: nil) (MoreOrders.ground_maps.MapS.empty (list (list ground_types))).

    Let G' := MoreOrders.ground_maps.MapS.add "T" nil G.
    Let G'' := MoreOrders.ground_maps.MapS.add "A" nil G'.
    Let G2 := MoreOrders.ground_maps.MapS.add "A" nil G.

    (* Let monotones := Eval compute in rules_to_monotone_op (rules program1). *)
    Import ground_maps.MapS.

    Lemma transitive_closure_same :
      forall (fuel: nat) (g g' g'': ground_maps.t),
        ground_maps.MapS.In "R" g ->
        ground_maps.MapS.find "A" g = Some nil ->
        ground_maps.MapS.find "T" g = Some nil ->
        Some g' = RelSemantics.program_semantics_eval g program1 fuel ->
        exists fuel',
          Some g'' = RelSemantics.program_semantics_eval g program2 fuel' ->
          ground_maps.MapS.Equal g' g''.
    Proof.
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

    (* Let find_meaning (m: option MoreOrders.ground_maps.t) x := match m with *)
                            (* | Some m' => MoreOrders.ground_maps.MapS.find x m' *)
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
    (*                         | Some m => MoreOrders.ground_maps.MapS.find x m *)
    (*                         | None => None *)
    (*                        end. *)
    (* Eval compute in (find_meaning "T"). *)

    
  End RelDecls.
End TransitiveClosureProgram.
