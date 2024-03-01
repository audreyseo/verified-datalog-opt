From Coq Require Import  List String Arith Psatz DecidableTypeEx OrdersEx Program.Equality FMapList FMapWeakList MSetWeakList Lists.ListSet.

From VeriFGH Require Import OrdersFunctor DatalogProps StringOrders RelOrdered OrderedGroundTypes.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.



Module RelSemantics.
  Import rset.

  

  

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

  Inductive monotone_ops :=
  | UNIT
  | ATOM (R: rel)
  | UNION (m1 m2: monotone_ops)
  | PROJ (proj_vars: list string) (m: monotone_ops)
  | JOIN (join_vars: string_sets.t) (m1 m2: monotone_ops).

  Definition option_bind {A B: Type} (f: A -> option B) (a: option A) :=
    match a with
    | Some a' => f a'
    | None => None
    end.

  Fixpoint monotone_vars (m: monotone_ops) (res: option string_sets.t) :=
    match m with
    | UNIT => Some (string_sets.empty)
    | ATOM R =>
        option_map (string_sets.union (vector_to_string_set (args R))) res
    | UNION m1 m2 => monotone_vars m2 (monotone_vars m1 res)
    | PROJ proj_vars m => Some (list_to_string_set proj_vars)
    | JOIN join_vars m1 m2 => monotone_vars m2 (monotone_vars m1 res)
    end.

  (* We'll assume that atoms in a rule are ordered such that you can join them from left to right, i.e.,
   * A(a, b), B(b, c, d), C(c, d, e f) -> JOIN { c, d } (JOIN { b } A(a, b) B(b, c, d)) C(c, d, e, f) 
   * This is probably not true in general (may need to split in half for example) but it's convenient
   *)
  Fixpoint rule_to_monotone_op_helper (rels: list rel) (res: option monotone_ops) :=
    match rels with
    | nil => res
    | hd :: rst =>
        let hd_args := vector_to_string_set (args hd) in
        let m_args := option_bind (fun r => monotone_vars r (Some string_sets.empty)) res in
        match m_args, res with
        | Some m_args', Some res' =>
            let j_args := string_sets.inter hd_args m_args' in
            rule_to_monotone_op_helper rst (Some (JOIN j_args res' (ATOM hd)))
        | _, _ => None
        end
    end.
  Definition rule_to_monotone_op (rels: list rel) :=
    match rels with
    | hd :: rst =>
        rule_to_monotone_op_helper rst (Some (ATOM hd))
    | nil => Some UNIT
    end.

  Fixpoint rels_to_rules (R: string) (rules: list rule) :=
    match rules with
    | hd :: rst =>
        match hd with
        | rule_def_empty rule_hd =>
            nil
        | rule_def rule_hd rule_body =>
            if String_OTF.eq_dec (name rule_hd) R then
              (rule_hd, rule_body) :: (rels_to_rules R rst)
            else
              rels_to_rules R rst
        | rule_def_exists rule_hd rule_exists rule_body =>
            if String_OTF.eq_dec (name rule_hd) R then
              (rule_hd, rule_body) :: (rels_to_rules R rst)
            else
              rels_to_rules R rst
        end
    | _ => nil
    end.

  Definition get_head (r: rule) :=
    match r with
    | rule_def_empty r' => r'
    | rule_def r' _ => r'
    | rule_def_exists r' _ _ => r'
    end.

  Print rset.Raw.

  Definition rules_to_monotone_op (rules: list rule) :=
    let heads := List.fold_left (fun acc elmt =>
                                   string_sets.add (name elmt) acc)
                                (List.map get_head rules)
                                string_sets.empty
    in
    let heads_rules := List.map (fun elmt =>
                                   (elmt, rels_to_rules elmt rules))
                                (string_sets.elements heads) in
    let m_heads := List.map
                     (fun elmt =>
                        match elmt with
                        | (name, name_rules) =>
                            (name,
                              List.map
                                (fun elmt' =>
                                   match elmt' with
                                   | (hd, body) =>
                                       option_map (PROJ (Vector.to_list (args hd))) (rule_to_monotone_op body)
                                   end)
                                name_rules)
                        end)
                     heads_rules in
    m_heads.
  
  Check rules_to_monotone_op.

  Module str_gt_list_ot := List_as_OT(String_GT_OT).


  Fixpoint evaluate_monotone_op (mapping: string -> option gset.t) (m: monotone_ops): option (ListSet.set (list String_GT_OT.t)) :=
    match m with
    | UNIT => None
    | ATOM R =>
        match mapping (name R) with
        | Some gts => Some (ListSet.set_add str_gt_list_ot.eq_dec gts ListSet.empty_set)
        | _ => None
        end
    | UNION m1 m2 =>
        let m1_eval := evaluate_monotone_op mapping m1 in
        let m2_eval := evaluate_monotone_op mapping m2 in
        match m1_eval, m2_eval with
        | Some t1, Some t2 =>
            Some (ListSet.set_union str_gt_list_ot.eq_dec t1 t2)
        | _, _ => None
        end
    | PROJ pvs m =>
        None
    end.
        let m_eval := evaluate_monotone_op mapping m in
        
        
        

        
        
        

        (* Fixpoint immediate_consequence_operator  *)

        (*          Fixpoint naive_evaluation  *)
                 

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
