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
  (* Module List_List_Ground_Type_as_OTF := OrdersFunctor.List_as_OTF(List_Ground_Type_as_OTF). *)

  Module List_Ground_Type_as_OT := OrdersFunctor.List_as_OT(List_Ground_Type_as_OTF).

  
  Module ground_maps := FMapList.Make_ord(String_as_OT) (List_Ground_Type_as_OT).

  Structure rel_grounding: Type :=
    MkRelGrounding {
        r: rel;
        arg_types: Vector.t ground_types (num_args r);
      }.

  
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

  Inductive monotone_ops :=
  | UNIT
  | ATOM (R: rel)
  | UNION (m1 m2: monotone_ops)
  | PROJ (proj_vars: list string) (m: monotone_ops)
  | JOIN (join_vars: list string) (m1 m2: monotone_ops).

  Definition option_bind {A B: Type} (f: A -> option B) (a: option A) :=
    match a with
    | Some a' => f a'
    | None => None
    end.

  Fixpoint monotone_vars (m: monotone_ops) (res: option (set string)) :=
    match m with
    | UNIT => Some (empty_set _)
    | ATOM R =>
        option_map (set_union string_dec (Vector.to_list (args R))) res
    | UNION m1 m2 => monotone_vars m2 (monotone_vars m1 res)
    | PROJ proj_vars m => Some (fold_left (fun acc elmt => set_add string_dec elmt acc) proj_vars (empty_set string))
    | JOIN join_vars m1 m2 => monotone_vars m2 (monotone_vars m1 res)
    end.

  (* We'll assume that atoms in a rule are ordered such that you can join them from left to right, i.e.,
   * A(a, b), B(b, c, d), C(c, d, e f) -> JOIN { c, d } (JOIN { b } A(a, b) B(b, c, d)) C(c, d, e, f) 
   * This is probably not true in general (may need to split in half for example) but it's convenient
   *)
  Definition list_to_list_set (l: list string) :=
    fold_left (fun acc elmt => set_add string_dec elmt acc) l (empty_set string).
  
  Fixpoint rule_to_monotone_op_helper (rels: list rel) (res: option monotone_ops) :=
    match rels with
    | nil => res
    | hd :: rst =>
        let hd_args := list_to_list_set (Vector.to_list (args hd)) in
        let m_args := option_bind (fun r => monotone_vars r (Some (empty_set string))) res in
        match m_args, res with
        | Some m_args', Some res' =>
            let j_args := set_inter string_dec hd_args m_args' in
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

  Fixpoint list_fold2 {A B C: Type} (f: C -> A -> B -> C) (res: C) (l1: list A) (l2: list B): option C :=
    match l1 with
    | nil => match l2 with
            | nil => Some res
            | _ => None
            end
    | hd :: tl =>
        match l2 with
        | hd' :: tl' =>
            list_fold2 f (f res hd hd') tl tl'
        | _ => None
        end
    end.

  Lemma list_fold2_some :
    forall (A B C: Type) (l1 : list A) (l2:list B) (f: C -> A -> B -> C) (init: C) ,
      Datatypes.length l1 = Datatypes.length l2 ->
      exists res,
        list_fold2 f init l1 l2 = Some res.
  Proof.
    induction l1; intros.
    - simpl in H.
      destruct l2; inversion H.
      exists init. reflexivity.
    - destruct l2; simpl in H; inversion H. simpl.
      specialize (IHl1 l2 f (f init a b)). eapply IHl1. eassumption.
  Defined.
      

  Definition variable_list_groundings_to_assoc_list (R: rel) (g: list ground_types) :=
    let rargs := Vector.to_list (args R) in
    list_fold2 (fun acc arg_name gt =>
                  (arg_name, gt) :: acc
               )
               nil
               rargs g.

  Fixpoint assoc_lookup (l: list (string * ground_types)) (elmt: string) :=
    match l with
    | nil => None
    | (hd_name, hd_gt) :: tl =>
        if string_dec elmt hd_name then
          Some hd_gt
        else assoc_lookup tl elmt
    end.

  Definition check_join_vars (jvs: list string) (assoc1 assoc2: list (string * ground_types)) :=
    List.fold_left (fun (acc: bool) (elmt: string) =>
                      if acc then
                        let a1 := assoc_lookup assoc1 elmt in
                        let a2 := assoc_lookup assoc2 elmt in
                        match a1, a2 with
                        | Some g1, Some g2 =>
                            if Ground_Types_as_OTF.eq_dec g1 g2 then
                              true
                            else false
                        | _, _ => false
                        end
                      else false)
                   jvs
                   true.

  Definition get_vars_set (assoc: list (string * ground_types)) :=
    List.fold_left (fun (acc: string_sets.t) (elmt: string * ground_types) =>
                      let (e1, e2) := elmt in
                      string_sets.add e1 acc)
                   assoc
                   string_sets.empty.

  Module str_gt_list_ot := List_as_OT(String_GT_OT).

  Definition tup_type : Type := list (string * ground_types).
  Definition tup_entry : Type := string * ground_types.

  Definition proj_tuples (pvs: list string) (assoc: tup_type) :=
    List.fold_left (fun acc (elmt: string) =>
                      match assoc_lookup assoc elmt with
                      | Some gt => option_map (cons (elmt, gt)) acc
                      | None => None
                      end)
                   pvs
                   (Some nil).
  
  
  Definition join_tuples (jvs: list string) (assoc1 assoc2: list (string * ground_types)) :=
    if check_join_vars jvs assoc1 assoc2 then
      let jv_set := list_to_string_set jvs in
      let assoc1_vars := string_sets.diff (get_vars_set assoc1) jv_set in
      let assoc2_vars := string_sets.diff (get_vars_set assoc2) jv_set in
      let first_vars := 
        string_sets.fold (fun elmt acc =>
                            match assoc_lookup assoc1 elmt with
                            | Some g =>
                                option_map (cons (elmt, g)) acc
                            | None => None
                            end)
                         assoc1_vars
                         (Some nil) in
      let joined :=
        string_sets.fold (fun elmt acc =>
                            match assoc_lookup assoc1 elmt with
                            | Some g =>
                                option_map (cons (elmt, g)) acc
                            | None => None
                            end)
                         jv_set
                         (Some nil) in
      let second_vars :=
        string_sets.fold (fun elmt acc =>
                            match assoc_lookup assoc2 elmt with
                            | Some g =>
                                option_map (cons (elmt, g)) acc
                            | None => None
                            end)
                         assoc2_vars
                         (Some nil) in
      match first_vars, joined, second_vars with
      | Some fv, Some jv, Some sv =>
          Some (fv ++ jv ++ sv)
      | _, _, _ => None
      end
    else None.
  
  
    
                  
  
  Definition join_relations (jvs: list string) (v1 v2: ListSet.set tup_type) :=
    set_fold_left (fun (acc: ListSet.set tup_type) (elmt: (tup_type * tup_type)) =>
                           let (t1, t2) := elmt in
                           match join_tuples jvs t1 t2 with
                           | Some tup => set_add str_gt_list_ot.eq_dec tup acc
                           | None => acc
                           end)
                        (set_prod v1 v2)
                        (@empty_set tup_type).

  Definition proj_relation (pvs: list string) (v: ListSet.set tup_type) :=
    set_fold_left (fun (acc: option (ListSet.set tup_type)) (elmt: tup_type) =>
                     match proj_tuples pvs elmt with
                     | Some tup => option_map (set_add str_gt_list_ot.eq_dec tup) acc
                     | None => None
                     end)
                  v
                  (Some (@empty_set tup_type)).

  Definition assign_vars_to_tuples (R: rel) (v: list (list ground_types)) :=
    List.fold_left (fun acc elmt =>
                      match variable_list_groundings_to_assoc_list R elmt with
                      | Some l => set_add str_gt_list_ot.eq_dec l acc
                      | None => acc
                      end)
                   v
                   (@empty_set tup_type).
                        
  Inductive monotone_op_semantics : ground_maps.t -> monotone_ops -> (ListSet.set tup_type) -> Prop :=
  | atom_semantics :
    forall (R: rel) (g: ground_maps.t) (v: list (list ground_types)),
      ground_maps.MapS.find (name R) g = Some v ->
      monotone_op_semantics g (ATOM R) (assign_vars_to_tuples R v)
  | join_semantics :
    forall (g: ground_maps.t) (m1 m2: monotone_ops)
      (jvs: list string) (v1 v2 v: (ListSet.set tup_type)),
      monotone_op_semantics g m1 v1 ->
      monotone_op_semantics g m2 v2 ->
      v = join_relations jvs v1 v2 ->
      monotone_op_semantics g (JOIN jvs m1 m2) v
  | union_semantics :
    forall (g: ground_maps.t) (m1 m2: monotone_ops)
      (v1 v2 v: ListSet.set tup_type),
      monotone_op_semantics g m1 v1 ->
      monotone_op_semantics g m2 v2 ->
      v = set_union str_gt_list_ot.eq_dec v1 v2 ->
      monotone_op_semantics g (UNION m1 m2) v
  | proj_semantics :
    forall (g: ground_maps.t) (m: monotone_ops)
      (pvs: list string) (v v': ListSet.set tup_type),
      monotone_op_semantics g m v ->
      proj_relation pvs v = Some v' ->
      monotone_op_semantics g (PROJ pvs m) v'.

  Fixpoint monotone_op_semantics_eval
           (g: ground_maps.t)
           (m: monotone_ops) : option (ListSet.set tup_type) :=
    match m with
    | UNIT => None
    | ATOM R =>
        match ground_maps.MapS.find (name R) g with
        | Some v =>
            Some (assign_vars_to_tuples R v)
        | None => None
        end
    | JOIN jvs m1 m2 =>
        match monotone_op_semantics_eval g m1,
          monotone_op_semantics_eval g m2 with
        | Some v1, Some v2 =>
            Some (join_relations jvs v1 v2)
        | _, _ => None
        end
    | UNION m1 m2 =>
        match monotone_op_semantics_eval g m1,
          monotone_op_semantics_eval g m2 with
        | Some v1, Some v2 =>
            Some (set_union str_gt_list_ot.eq_dec v1 v2)
        | _, _ => None
        end
    | PROJ pvs m =>
        match monotone_op_semantics_eval g m with
        | Some v =>
            proj_relation pvs v
        | None => None
        end
    end.
               

  
  Eval compute in ground_maps.t.

  Fixpoint anonymize_tuple
           (names: list string)
           (t: tup_type) : option (list ground_types) :=
    match names with
    | hd :: tl => match assoc_lookup t hd with
                | Some g => option_map (cons g) (anonymize_tuple tl t)
                | None => None
                end
    | nil => Some nil
    end.

  Definition anonymize_tuples
             (names: list string)
             (v: ListSet.set tup_type) : option (list (list ground_types)) :=
    set_fold_right (fun elmt acc =>
                      match anonymize_tuple names elmt with
                      | Some t =>
                          option_map (set_add List_Ground_Type_as_OTF.eq_dec t) acc
                      | None => None
                      end)
                   v
                   (Some (@empty_set List_Ground_Type_as_OTF.t)).


  Inductive rule_semantics : ground_maps.t -> list (string * monotone_ops) -> ground_maps.t -> Prop :=
  | nil_rules_semantics :
    forall (g: ground_maps.t),
      rule_semantics g nil g
  | cons_rules_semantics :
    forall (g g' g'': ground_maps.t)
      (v: ListSet.set tup_type)
      (rel_name: string)
      (m: monotone_ops) (R: rel)
      (new_tuples: list (list ground_types))
      (rst: list (string * monotone_ops)),
      name R = rel_name ->
      monotone_op_semantics g m v ->
      Some new_tuples = anonymize_tuples (Vector.to_list (args R)) v ->
      g' = ground_maps.MapS.mapi
             (fun k e =>
                if string_dec k rel_name then
                  ListSet.set_union List_Ground_Type_as_OTF.eq_dec
                                    new_tuples e
                else e)
             g ->
      rule_semantics g' rst g'' ->
      rule_semantics g ((rel_name, m) :: rst) g''.

  Fixpoint rule_semantics_eval
           (g: ground_maps.t)
           (R: rel)
           (rulez: list (string * monotone_ops)) : option ground_maps.t :=
    match rulez with
    | nil => Some g
    | (n, m) :: rst_rules =>
        if string_dec (name R) n then
          match monotone_op_semantics_eval g m with
          | Some v =>
              match anonymize_tuples (Vector.to_list (args R)) v with
              | Some new_tuples =>
                  let g' :=
                    ground_maps.MapS.mapi
                      (fun k e =>
                         if string_dec k (name R) then
                           ListSet.set_union List_Ground_Type_as_OTF.eq_dec
                                             new_tuples e
                         else e)
                      g in
                  rule_semantics_eval g' R rst_rules
              | None => None
              end
          | None => None
          end
        else rule_semantics_eval g R rst_rules
    end.

  Fixpoint program_semantics_eval
           (g: ground_maps.t)
           (R: rel)
           (rulez: list (string * monotone_ops))
           (fuel: nat) : option ground_maps.t :=
    match fuel with
    | 0 => Some g
    | S fuel' =>
        match rule_semantics_eval g R rulez with
        | Some g' =>
            program_semantics_eval g' R rulez fuel'
        | None => None
        end

    end.
                      
  Section SemanticsExamples.
    Section GraphEdges.
      Let G :=
            ground_maps.MapS.add
              "E"
              ( (NAT 1 :: NAT 2 :: nil)
                  ::
                  (NAT 2 :: NAT 3 :: nil) ::
                  (NAT 3 :: NAT 4 :: nil) :: nil)
              (ground_maps.MapS.empty (list (list ground_types))).
      Let G' := ground_maps.MapS.add "R" nil G.
      Let Rxy := mk_rel "R" ("x" :: "y" :: nil) idb.
      Let Exy := mk_rel "E" ("x" :: "y" :: nil) edb.
      Let Ezy := mk_rel "E" ("z" :: "y" :: nil) edb.
      Let Rxz := mk_rel "R" ("x" :: "z" :: nil) idb.

      Let z_set := string_sets.add "z" string_sets.empty.
      
      Let Rxy_rule1 := rule_def Rxy (Exy :: nil).
      Let Rxy_rule2 := rule_def_exists Rxy z_set (Rxz :: Ezy :: nil).

      Let edb_set := string_sets.add "E" string_sets.empty.
      Let idb_set := string_sets.add "R" string_sets.empty.
      
      Let GraphProgram := DlProgram idb_set edb_set Rxy (Rxy_rule1 :: Rxy_rule2 :: nil).
      Let monotones := Eval compute in rules_to_monotone_op (rules GraphProgram).
      Print monotones.

      Let monotones' :=
            Eval compute in
            List.fold_left
              (fun (acc: list (string * monotone_ops)) (elmt: string * (list (option monotone_ops))) =>
                 let (name, oms) := elmt in
                 List.fold_left (fun (acc': list (string * monotone_ops))
                                   (elmt: option monotone_ops) =>
                                   
                                   match elmt with
                                   | Some m =>
                                       (name, m) :: acc'
                                   | None =>
                                       acc
                                   end)
                                oms
                                acc
              )
              monotones
              nil.

      Let meaning := Eval compute in program_semantics_eval G' Rxy monotones' 2.

      Let find_meaning x := match meaning with
                            | Some m => ground_maps.MapS.find x m
                            | None => None
                            end.

      Eval compute in (find_meaning "R").
    End GraphEdges.
  End SemanticsExamples.
End RelSemantics.
