From Coq Require Import  List String Arith Psatz DecidableTypeEx OrdersEx Program.Equality FMapList FMapWeakList MSetWeakList Lists.ListSet.

From VeriFGH Require Import OrdersFunctor DatalogProps StringOrders RelOrdered OrderedGroundTypes MoreOrders RelDecidable.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.



Module RelSemantics.
  Import rset.

  
  Inductive monotone_ops :=
  | UNIT
  | ATOM (R: rel)
  | SELECT (var: string) (val: ground_types) (m: monotone_ops) (* allow for basic selections, \sigma, and also is a desugaring of atoms like a('1', y), which was easier to implement than changing how atoms worked *)
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
    | SELECT v _ m => option_map (set_add string_dec v) (monotone_vars m res)
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

  Definition wrap_in_grounding (m: monotone_ops) (g: list (string * ground_types)) :=
    List.fold_left (fun acc (elmt: string * ground_types) =>
                      let (n, v) := elmt in
                      SELECT n v acc)
                   g
                   m.
  
  Fixpoint rule_to_monotone_op_helper (rels: list rel) (res: option monotone_ops) :=
    match rels with
    | nil => res
    | hd :: rst =>
        let hd_args := list_to_list_set (Vector.to_list (args hd)) in
        let m_args := option_bind (fun r => monotone_vars r (Some (empty_set string))) res in
        let groundeds := grounded_args hd in
        match m_args, res with
        | Some m_args', Some res' =>
            let j_args := set_inter string_dec hd_args m_args' in
            rule_to_monotone_op_helper
              rst
              (Some (wrap_in_grounding (JOIN j_args res' (ATOM hd)) groundeds))
                 (* (List.fold_left (fun acc (elmt: string * ground_types) => *)
                                       (* let (n, v) := elmt in *)
                                       (* SELECT n v acc) *)
                                    (* groundeds *)
                                    (* (JOIN j_args res' (ATOM hd)))) *)
        | _, _ => None
        end
    end.
  Definition rule_to_monotone_op (rels: list rel) :=
    match rels with
    | hd :: rst =>
        let groundeds := grounded_args hd in
        rule_to_monotone_op_helper rst (Some (wrap_in_grounding (ATOM hd) groundeds))
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

  Definition get_heads_sset (rules: list rule) :=
    List.fold_left (fun acc elmt =>
                      string_sets.add (name elmt) acc)
                   (List.map get_head rules)
                   string_sets.empty.

  Definition get_heads (rules: list rule) :=
    List.fold_left (fun acc elmt =>
                      set_add rel_dec elmt acc)
                   (List.map get_head rules)
                   (empty_set rel).
    (* List.map (fun elmt => rels_to_rules elmt rules) (string_sets.elements (get_heads_sset rules)). *)

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
                                       (hd, option_map (PROJ (Vector.to_list (args hd))) (rule_to_monotone_op body))
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

  Definition select_tuples (n: string) (v: ground_types) (assoc: tup_type) :=
    List.fold_left (fun acc (elmt: string * ground_types) =>
                      let (n', g) := elmt in
                      if string_dec n n' then
                        if Ground_Types_as_OTF.eq_dec v g then
                          option_map (cons elmt) acc
                        else None
                      else option_map (cons elmt) acc)
                   assoc
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
  
  Definition tt_set_prod (v1 v2: tt_set.t) :=
    list_prod (tt_set.elements v1) (tt_set.elements v2).
  
  
  
  Definition join_relations (jvs: list string) (v1 v2: tt_set.t) :=
    List.fold_left (fun (acc: tt_set.t) (elmt: (tup_type * tup_type)) =>
                           let (t1, t2) := elmt in
                           match join_tuples jvs t1 t2 with
                           | Some tup => tt_set.add tup acc
                           | None => acc
                           end)
                        (tt_set_prod v1 v2)
                        (tt_set.empty).

  Definition select_relation_f (n: string) (g: ground_types) (elmt: tup_type) (acc: tt_set.t) :=
    match select_tuples n g elmt with
    | Some tup => tt_set.add tup acc
    | None => acc
    end.

  Arguments select_relation_f _ _ / _ _.

  Definition select_relation (n: string) (g: ground_types) (v: tt_set.t) :=
    tt_set.fold (select_relation_f n g)
                  v
                  (tt_set.empty).
  Arguments select_relation / _ _ _.

  Definition proj_relation (pvs: list string) (v: tt_set.t) :=
    tt_set.fold (fun (elmt: tup_type) (acc: option tt_set.t) =>
                     match proj_tuples pvs elmt with
                     | Some tup => option_map (tt_set.add tup) acc
                     | None => None
                     end)
                  v
                  (Some (tt_set.empty)).

  Arguments proj_relation / _ _.

  Definition assign_vars_to_tuples (R: rel) (v: list (list ground_types)) :=
    List.fold_left (fun acc elmt =>
                      match variable_list_groundings_to_assoc_list R elmt with
                      | Some l => tt_set.add l acc
                      | None => acc
                      end)
                   v
                   (tt_set.empty).
  Arguments assign_vars_to_tuples / _ _.

  Print ground_maps.

  Definition gt_set_type := list (list ground_types).

  Definition gm_empty := ground_maps.empty gt_set_type.

  Definition gm_type := ground_maps.t gt_set_type.

                        
  Inductive monotone_op_semantics : gm_type -> monotone_ops -> tt_set.t -> Prop :=
  | atom_semantics :
    forall (R: rel) (g: gm_type) (v: list (list ground_types)),
      ground_maps.find (name R) g = Some v ->
      monotone_op_semantics g (ATOM R) (assign_vars_to_tuples R v)
  | select_semantics :
    forall (g: gm_type) (v v': tt_set.t) (n: string) (gt: ground_types) (m: monotone_ops),
      monotone_op_semantics g m v ->
      v' = select_relation n gt v ->
      monotone_op_semantics g (SELECT n gt m) v'
  | join_semantics :
    forall (g: gm_type) (m1 m2: monotone_ops)
      (jvs: list string) (v1 v2 v: (tt_set.t)),
      monotone_op_semantics g m1 v1 ->
      monotone_op_semantics g m2 v2 ->
      v = join_relations jvs v1 v2 ->
      monotone_op_semantics g (JOIN jvs m1 m2) v
  | union_semantics :
    forall (g: gm_type) (m1 m2: monotone_ops)
      (v1 v2 v: tt_set.t),
      monotone_op_semantics g m1 v1 ->
      monotone_op_semantics g m2 v2 ->
      v = tt_set.union v1 v2 ->
      monotone_op_semantics g (UNION m1 m2) v
  | proj_semantics :
    forall (g: gm_type) (m: monotone_ops)
      (pvs: list string) (v v': tt_set.t),
      monotone_op_semantics g m v ->
      proj_relation pvs v = Some v' ->
      monotone_op_semantics g (PROJ pvs m) v'.

  Fixpoint monotone_op_semantics_eval
           (g: gm_type)
           (m: monotone_ops) : option (tt_set.t) :=
    match m with
    | UNIT => None
    | ATOM R =>
        match ground_maps.find (name R) g with
        | Some v =>
            Some (assign_vars_to_tuples R v)
        | None => None
        end
    | SELECT n gt m =>
        match monotone_op_semantics_eval g m with
        | Some v =>
            Some (select_relation n gt v)
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
            Some (tt_set.union v1 v2)
        | _, _ => None
        end
    | PROJ pvs m =>
        match monotone_op_semantics_eval g m with
        | Some v =>
            proj_relation pvs v
        | None => None
        end
    end.

  Lemma monotone_op_semantics_det :
    forall (m: monotone_ops) (g: gm_type) (v v': tt_set.t),
      monotone_op_semantics g m v ->
      monotone_op_semantics g m v' ->
      v = v'.
  Proof.
    induction m; intros.
    - inversion H.
    - inversion H. inversion H0. subst.
      rewrite H7 in H3. inversion H3. reflexivity.
    - inversion H. inversion H0. subst.
      f_equal. eapply IHm; eassumption.
    - inversion H. inversion H0. subst. f_equal; eauto.
    - inversion H. inversion H0. subst.
      specialize (IHm _ _ _ H4 H10). subst. rewrite H12 in H6. inversion H6. reflexivity.
    - inversion H. inversion H0. subst.
      f_equal; eauto.
  Qed.

  Lemma monotone_op_semantics_adequacy :
    forall (m: monotone_ops) (g: gm_type) (v: tt_set.t),
      Some v = monotone_op_semantics_eval g m <->
        monotone_op_semantics g m v.
  Proof.
    induction m; intros; split; intros.
    - simpl in H. inversion H.
    - inversion H.
    - simpl in H.
      match goal with
      | [ H: Some _ = match ?x with | Some v => _ | None => None end |- _ ] =>
          destruct (x) eqn:X; inversion H
      end.
      econstructor. eassumption.
    - inversion H. simpl. rewrite H2. reflexivity.
    - simpl in H.
      Ltac destruct_hyp_match :=
        match goal with
        | [H: Some _ = match ?x with | Some _ => _ | None => None end |- _ ] =>
            let Xfresh := fresh "X" in
            destruct (x) eqn:Xfresh; inversion H
        end.
      destruct_hyp_match.
      symmetry in X. eapply IHm in X.
      econstructor; eauto.
    - Ltac destruct_goal_match :=
        match goal with
        | [ |- Some _ = match ?x with | Some _ => _ | None => None end ] =>
            let Xfresh := fresh "X" in
            destruct (x) eqn:Xfresh; subst
        end.
      simpl. destruct_goal_match.
      + inversion H. subst. eapply IHm in H5.
        rewrite <- H5 in X. inversion X. reflexivity.
      + inversion H. subst. eapply IHm in H5. rewrite X in H5. congruence.
    - simpl in H.
      match goal with
      | [H: Some _ = match ?x with | Some _ => _ | None => None end |- _ ] =>
          destruct (x) eqn:X; inversion H
      end.
      
      destruct_hyp_match.
      subst.
      econstructor; eauto.
      eapply IHm1. congruence.
      eapply IHm2. congruence.
    - inversion H. subst. simpl.
      

      destruct_goal_match.
      + destruct_goal_match.
        * f_equal. eapply IHm1 in H2. eapply IHm2 in H4.
          rewrite <- H2 in X. rewrite <- H4 in X0.
          inversion X. inversion X0. reflexivity.
        * eapply IHm2 in H4. rewrite <- H4 in X0. inversion X0.
      + eapply IHm1 in H2. rewrite <- H2 in X. inversion X.
    - simpl in H. destruct_hyp_match.
      econstructor. eapply IHm. symmetry. eassumption. simpl. 
      congruence.
    - simpl. inversion H. subst. destruct_goal_match.
      symmetry in X.
      eapply IHm in X.
      pose proof (monotone_op_semantics_det _ _ _ _ H3 X). subst.
      simpl in *.
      congruence.
      eapply IHm in H3. rewrite X in H3. congruence.
    - simpl in H. destruct_hyp_match. destruct_hyp_match.
      econstructor; eauto.
      eapply IHm1. congruence.
      eapply IHm2. congruence.
    - inversion H. subst. eapply IHm1 in H4. eapply IHm2 in H6.
      simpl. rewrite <- H4. rewrite <- H6. reflexivity.
  Qed.

  
  (* Eval compute in ground_maps.t. *)

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
             (v: tt_set.t) : option (list (list ground_types)) :=
    tt_set.fold (fun elmt acc =>
                      match anonymize_tuple names elmt with
                      | Some t =>
                          option_map (set_add List_Ground_Type_as_OTF.eq_dec t) acc
                      | None => None
                      end)
                   v
                   (Some (@empty_set List_Ground_Type_as_OTF.t)).

  Arguments tt_set.fold [A]%type_scope f%function_scope s _ /.

  Check ground_maps.mapi.

  
  Lemma ground_maps_t_to_ground_maps_maps_t :
    gm_type = ground_maps.t gt_set_type.
  Proof.
    reflexivity.
  Defined.

  Print ground_maps.

  (* Inductive mapi_rel (f: ground_maps.key -> gt_set_type -> gt_set_type) : gm_type -> gm_type -> Prop := *)
  (* | mapi_rel_nil : *)
  (*   mapi_rel f gm_empty gm_empty *)
  (* | mapi_rel_cons : *)
  (*   forall (g g': gm_type) (k: ground_maps.key) (e: gt_set_type), *)
      
                                                                                           
      

  Inductive rule_semantics : gm_type -> list (string * rel * monotone_ops) -> gm_type -> Prop :=
  | nil_rules_semantics :
    forall (g: gm_type),
      rule_semantics g nil g
  | cons_rules_semantics :
    forall (g g' g'': gm_type)
      (v: tt_set.t)
      (rel_name: string)
      (m: monotone_ops) (R: rel)
      (new_tuples old_tuples: list (list ground_types))
      (rst: list (string * rel * monotone_ops)),
      name R = rel_name ->
      monotone_op_semantics g m v ->
      Some new_tuples = anonymize_tuples (Vector.to_list (args R)) v ->
      Some old_tuples = ground_maps.find rel_name g ->
      g' = ground_maps.add rel_name (ListSet.set_union List_Ground_Type_as_OTF.eq_dec new_tuples old_tuples) g ->

        (* ground_maps.mapi *)
             (* (fun k e => *)
                (* if string_dec k rel_name then *)
                  (* ListSet.set_union List_Ground_Type_as_OTF.eq_dec *)
                                    (* new_tuples e *)
                (* else e) *)
             (* g -> *)
      rule_semantics g' rst g'' ->
      rule_semantics g ((rel_name, R, m) :: rst) g''.

  Fixpoint rule_semantics_eval
           (g: gm_type)
           (R: rel)
           (rulez: list (string * monotone_ops)) : option gm_type :=
    match rulez with
    | nil => Some g
    | (n, m) :: rst_rules =>
        if string_dec (name R) n then
          match monotone_op_semantics_eval g m with
          | Some v =>
              match anonymize_tuples (Vector.to_list (args R)) v, ground_maps.find n g with
              | Some new_tuples, Some old_tuples =>
                  let g' := ground_maps.add n (ListSet.set_union List_Ground_Type_as_OTF.eq_dec new_tuples old_tuples) g in
                    (* ground_maps.MapS.mapi *)
                      (* (fun k e => *)
                         (* if string_dec k (name R) then *)
                           (* ListSet.set_union List_Ground_Type_as_OTF.eq_dec *)
                                             (* new_tuples e *)
                         (* else e) *)
                      (* g in *)
                  rule_semantics_eval g' R rst_rules
              | _, _ => None
              end
          | None => None
          end
        else rule_semantics_eval g R rst_rules
    end.

  Fixpoint rule_semantics_eval'
           (g: gm_type)
           (rulez: list (string * rel * monotone_ops)) : option gm_type :=
    match rulez with
    | nil => Some g
    | (n, R, m) :: rst_rules =>
        if string_dec (name R) n then
          match monotone_op_semantics_eval g m with
          | Some v =>
              match anonymize_tuples (Vector.to_list (args R)) v, ground_maps.find n g with
              | Some new_tuples, Some old_tuples =>
                  let g' := ground_maps.add n (ListSet.set_union List_Ground_Type_as_OTF.eq_dec new_tuples old_tuples) g in
                    (* ground_maps.MapS.mapi *)
                      (* (fun k e => *)
                         (* if string_dec k (name R) then *)
                           (* ListSet.set_union List_Ground_Type_as_OTF.eq_dec *)
                                             (* new_tuples e *)
                         (* else e) *)
                      (* g in *)
                  rule_semantics_eval' g' rst_rules
              | _, _ => None
              end
              (* match anonymize_tuples (Vector.to_list (args R)) v with *)
              (* | Some new_tuples => *)
              (*     let g' := *)
              (*       ground_maps.MapS.mapi *)
              (*         (fun k e => *)
              (*            if string_dec k n then *)
              (*              ListSet.set_union List_Ground_Type_as_OTF.eq_dec *)
              (*                                new_tuples e *)
              (*            else e) *)
              (*         g in *)
              (*     rule_semantics_eval' g' rst_rules *)
              (* | None => None *)
              (* end *)
          | None => None
          end
        else rule_semantics_eval' g rst_rules
    end.

  Lemma rule_semantics_det :
    forall (rules: list (string * rel * monotone_ops)) (g g1 g2: gm_type),
      rule_semantics g rules g1 ->
      rule_semantics g rules g2 ->
      g1 = g2.
  Proof.
    induction rules; intros.
    - inversion H. inversion H0. subst. reflexivity.
    - inversion H. subst. inversion H0. subst.
      eapply IHrules. eassumption.
      epose proof (monotone_op_semantics_det _ _ _ _ H4 H9).
      subst.
      rewrite <- H5 in H12. inversion H12. subst.
      rewrite <- H6 in H14. inversion H14. subst. eassumption.
  Qed.

  Lemma rule_semantics_adequacy :
    forall (rules: list (string * rel * monotone_ops)) (g g': gm_type),
      Forall (fun elmt =>
                match elmt with
                | (n, r, m) => n = name r
                end) rules ->
      Some g' = rule_semantics_eval' g rules <->
        rule_semantics g rules g'.
  Proof.
    induction rules; intros; split; intros.
    - inversion H0. econstructor.
    - inversion H0. subst. reflexivity.
    - simpl in H0. destruct a.  destruct p. destruct (string_dec (name r) s).
      + destruct_hyp_match. destruct_hyp_match.
        destruct_hyp_match.
        econstructor. eassumption.
        eapply monotone_op_semantics_adequacy. symmetry in X. eassumption.
        symmetry in X0. eassumption.
        
        3: eapply IHrules in H3; inversion H; try eassumption.
        2: reflexivity.
        symmetry in X1. eassumption.
      + inversion H. congruence.
    - inversion H0. subst. inversion H. subst.
      simpl. destruct (string_dec (name R) (name R)); try congruence.
      clear e.
      destruct_goal_match.
      + destruct_goal_match.
        * destruct_goal_match.
          -- eapply IHrules in H10.
             eapply monotone_op_semantics_adequacy in H4.
             rewrite <- H4 in X. inversion X. subst.
             clear X. rewrite X0 in H5. inversion H5. subst.
             inversion H6. subst. eassumption.
             eassumption.
          -- inversion H6.
        * eapply monotone_op_semantics_adequacy in H4. rewrite X in H4. inversion H4. subst. rewrite X0 in H5. congruence.
      + eapply monotone_op_semantics_adequacy in H4. rewrite X in H4. congruence.
  Qed.

  (* States of reaching fixpoint:
     have fuel -> run another iter -> maps are the same -> end
                                   -> maps are not the same -> continue
     don't have fuel -> fail


   *)

  Inductive program_semantics : gm_type -> list (string * rel * monotone_ops) -> gm_type -> Prop :=
  | program_step_done :
    forall (g g': gm_type) (rulez: list (string * rel * monotone_ops)),
      rule_semantics g rulez g' ->
      ground_maps.Equal g g' ->
      program_semantics g rulez g
  | program_step_continue :
    forall (g g' g'': gm_type) (rulez: list (string * rel * monotone_ops)),
      (* program_semantics g g' rulez g'' -> *)
      rule_semantics g rulez g' ->
      program_semantics g' rulez g'' ->
      program_semantics g rulez g''.


  Ltac invs H := inversion H; subst.
  Ltac invc H := inversion H; subst; clear H.

  Lemma tt_set_eq_refl :
    forall (v v': tt_set.t),
      v = v' ->
      tt_set.Equal v v'.
  Proof.
    intros. subst. unfold tt_set.Equal. intros; split; intros; eassumption.
  Qed.

  Print select_relation.

  Print tt_set.Raw.fold.
  Arguments tt_set.Raw.fold [B]%type_scope f%function_scope _ _ /.

  Lemma tt_set_fold_In_init :
    forall (v init: tt_set.t) (f: tup_type -> tt_set.t -> tt_set.t),
      (forall (t: tup_type) (v': tt_set.t),
          tt_set.Subset v' (f t v')) ->
      forall init',
        tt_set.Subset init init' ->
        tt_set.Subset init (tt_set.fold f v init').
  Proof.
    destruct v. rename this0 into v. induction v; intros; simpl.
    - unfold tt_set.fold. unfold tt_set.Raw.fold. simpl. unfold tt_set.Subset; intros; eauto.
    - unfold tt_set.fold. unfold tt_set.Raw.fold. simpl.
      unfold tt_set.fold in IHv. unfold tt_set.Raw.fold in IHv. simpl in IHv.
      invs is_ok0. specialize (IHv H4). eapply IHv.
      eassumption.
      specialize (H a init').
      unfold tt_set.Subset in *.
      intros. eapply H. eapply H0. eassumption.
  Qed.

  Definition monotone (f: tup_type -> tt_set.t -> tt_set.t) :=
    forall (t: tup_type) (v: tt_set.t),
      tt_set.Subset v (f t v).

  Arguments monotone f /.
      
      

  Lemma tt_set_fold_In :
    forall (v: tt_set.t) (f: tup_type -> tt_set.t -> tt_set.t) (f': tup_type -> option tup_type) (init: tt_set.t) (t t': tup_type),
      tt_set.In t v ->
      f' t = Some t' ->
      tt_set.In t' (f t init) ->
      monotone f ->
      (* (forall (t'': tup_type) (v'': tt_set.t), tt_set.Subset v'' (f t'' v'')) -> *)
      tt_set.In t' (tt_set.fold f v init).
  Proof.
    intros v. destruct v. rename this0 into v. induction v; simpl; intros.
    - inversion H.
    - invs is_ok0.
      specialize (IHv H6).
      specialize (IHv f f').
      unfold tt_set.In. unfold tt_set.Raw.In.
      unfold tt_set.fold. unfold tt_set.Raw.fold. simpl.
      unfold tt_set.In in IHv. unfold tt_set.Raw.In in IHv. simpl in IHv. unfold tt_set.fold in IHv. unfold tt_set.Raw.fold in IHv. simpl in IHv.
      invs H.
      + specialize (H2 t' (Basics.flip f init a)).
        unfold Basics.flip in H2.
        unfold tt_set.Subset in H2.
        pose proof (tt_set_fold_In_init).
        simpl in H3.
        unfold tt_set.Subset in H3.
        admit.
  Admitted.
        
        
      
      
  Lemma tt_set_fold_equal :
    forall (v v': tt_set.t) (A: Type) (f: tup_type -> tt_set.t -> tt_set.t) (init: tt_set.t),
      tt_set.Equal v v' ->
      tt_set.Equal (tt_set.fold f v init) (tt_set.fold f v' init).
  Proof.
    intros v. destruct v. induction this0; intros.
    - unfold tt_set.Equal in H. unfold tt_set.fold. unfold tt_set.Raw.fold. simpl.
      destruct v'.
      destruct this0.
      + simpl. reflexivity.
      + simpl.
        specialize (H e).
        destruct H.
        assert (tt_set.In e {| tt_set.this := e :: this0; tt_set.is_ok := is_ok1 |}).
        {
          unfold tt_set.In. unfold tt_set.Raw.In. econstructor. reflexivity.
        }
        eapply H0 in H1. inversion H1.
    - unfold tt_set.fold. unfold tt_set.Raw.fold. simpl.
      inversion is_ok0. subst.
      unfold tt_set.Raw.Ok in is_ok0.
      specialize (IHthis0 H3).
      destruct v'. destruct this1.
      + simpl. unfold tt_set.Equal in H. unfold tt_set.In in H.
        simpl in H. assert (tt_set.Raw.In a (a :: this0)) by (econstructor; reflexivity).
        eapply H in H0. inversion H0.
      + simpl. inversion is_ok1. subst.
        specialize (IHthis0 {| tt_set.this := this1; tt_set.is_ok := H5 |}).
        unfold tt_set.fold in IHthis0. unfold tt_set.Raw.fold in IHthis0. simpl in IHthis0.
        unfold tt_set.Equal.
        
        admit.
  Admitted.
        


  Lemma monotone_op_semantics_det' :
    forall (m: monotone_ops) (g g': gm_type) (v v': tt_set.t),
      ground_maps.Equal g g' ->
      monotone_op_semantics g m v ->
      monotone_op_semantics g' m v' ->
      tt_set.Equal v v'.
  Proof.
    induction m; unfold ground_maps.Equal; intros.
    - inversion H0.
    - inversion H0. inversion H1. subst.
      rewrite H in H4. rewrite H8 in H4. invs H4.
      eapply tt_set_eq_refl. reflexivity.
    - invs H0. invs H1. specialize (IHm _ _ _ _ H H7 H8).
      
      unfold select_relation.
      unfold assign_vars_to_tuples in *.
      admit.
  Admitted.
    

  Lemma rule_semantics_det' :
    forall (rulez: list (string * rel * monotone_ops)) (g g' g0 g0': gm_type),
      ground_maps.Equal g g' ->
      rule_semantics g rulez g0 ->
      rule_semantics g' rulez g0' ->
      ground_maps.Equal g0 g0'.
  Proof.
    induction rulez; intros.
    - inversion H0. inversion H1. subst. eassumption.
    - inversion H0. inversion H1. subst. inversion H12; subst; clear H12.
      admit.
  Admitted.
      

  Lemma program_semantics_det :
    forall (g g' g'': gm_type) (rulez: list (string * rel * monotone_ops)),
      program_semantics g rulez g' ->
      program_semantics g rulez g'' ->
      ground_maps.Equal g' g''.
  Proof.
    intros g g' g'' rulez P.
    revert g''. dependent induction P; intros.
    - inversion H1; subst.
      + unfold ground_maps.Equal. intros; reflexivity.
      + unfold ground_maps.Equal in *. intros. rewrite H0.
        pose proof (rule_semantics_det _ _ _ _ H H2). subst.
        admit.
  Admitted.
        
      
      
  Definition program_semantics_eval_loop_body (g: gm_type) (rulez: list (string * rel * monotone_ops)): option gm_type :=
    let new_g := rule_semantics_eval' g rulez in
    (* List.fold_left (fun g'' R => *)
    (* match g'' with *)
    (* | Some g' => *)
    (* rule_semantics_eval' g' R rulez *)
    (* | None => None *)
    (* end) *)
    (* rulez *)
    (* (Some g) in *)
    new_g.
    (* match new_g with *)
    (* | Some g' => *)
    (*     if ground_maps.equal List_Ground_Type_as_OT.eqb g g' then *)
    (*       Some g *)
    (*     else program_semantics_eval_helper g' rulez fuel' *)
    (* | None => None *)
    (* end *)

  Fixpoint program_semantics_eval_helper
           (g: gm_type)
           (* (rels: list rel) *)
           (rulez: list (string * rel * monotone_ops))
           (fuel: nat) : option gm_type :=
    match fuel with
    | 0 => None
    | S fuel' =>
        let new_g := rule_semantics_eval' g rulez in
          (* List.fold_left (fun g'' R => *)
                            (* match g'' with *)
                            (* | Some g' => *)
                                (* rule_semantics_eval' g' R rulez *)
                            (* | None => None *)
                            (* end) *)
                         (* rulez *)
                         (* (Some g) in *)
        match new_g with
        | Some g' =>
            if ground_maps.equal List_Ground_Type_as_OT.eqb g g' then
              Some g
            else program_semantics_eval_helper g' rulez fuel'
        | None => None
        end
    end.

  Fixpoint run_program_without_fixpoint (g: gm_type)
           (rulez: list (string * rel * monotone_ops))
           (fuel: nat) : option gm_type :=
    match fuel with
    | 0 => Some g
    | S fuel' =>
        match program_semantics_eval_loop_body g rulez with
        | Some g' =>
            run_program_without_fixpoint g' rulez fuel'
        | None => None
        end
    end.

  Definition program_to_monotone_ops (p: program): list (string * rel * monotone_ops) :=
    let monotones := (rules_to_monotone_op (rules p)) in
    let monotones' :=
      (List.fold_left
         (fun (acc: list (string * rel * monotone_ops)) (elmt: string * (list (rel * (option monotone_ops)))) =>
            let (name, oms) := elmt in
            List.fold_left (fun (acc': list (string * rel * monotone_ops))
                              (elmt_pair: rel * option monotone_ops) =>
                              let (hd, elmt) := elmt_pair in
                              match elmt with
                              | Some m =>
                                  (name, hd, m) :: acc'
                              | None =>
                                  acc
                              end)
                           oms
                           acc
         )
         monotones
         nil) in
    monotones'.

  Definition program_semantics_eval_single_iter
             (g: gm_type)
             (p: program) : option gm_type :=
    let monotones' := program_to_monotone_ops p in
    program_semantics_eval_loop_body g monotones'.
    (* program_semantics_eval_helper g monotones' 1. *)


  Definition program_semantics_eval_without_fixpoint (g: gm_type) (p: program) (fuel: nat) : option gm_type :=
    let monotones' := program_to_monotone_ops p in
    run_program_without_fixpoint g monotones' fuel.
      

  Definition program_semantics_eval
             (g: gm_type)
             (p: program)
             (fuel: nat) : option gm_type :=
    let monotones' := program_to_monotone_ops p in
    let heads := get_heads (rules p) in
    program_semantics_eval_helper g monotones' fuel.
    
                      
  Section SemanticsExamples.
    Section GraphEdges.
      Let G :=
            ground_maps.add
              "E"
              ( (NAT 1 :: NAT 2 :: nil)
                  ::
                  (NAT 2 :: NAT 3 :: nil) ::
                  (NAT 3 :: NAT 4 :: nil) :: nil)
              gm_empty.
      Let G' := ground_maps.add "R" nil G.
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

      Let meaning := Eval compute in program_semantics_eval_without_fixpoint G' GraphProgram 2.
      Let find_meaning (meaning: option gm_type) x := match meaning with
                            | Some m => ground_maps.find x m
                            | None => None
                                                      end.

      Print meaning.

      Let r_meaning := Eval compute in find_meaning meaning "R".
      Let e_meaning := Eval compute in find_meaning meaning "E".

      Print r_meaning.
      Print e_meaning.

      Let meaning' := Eval compute in (match meaning with
                                       | Some m => program_semantics_eval_without_fixpoint m GraphProgram 2
                                       | None => None
                                       end).
      Print meaning'.
      Let r_meaning' := Eval compute in find_meaning meaning' "R".
      Print r_meaning'.

      (* Eval compute in (match meaning with *)
      (*                  | Some m => Some (ground_maps.MapS.elements m) *)
      (*                  | None => None *)
      (*                  end). *)

      (* Print ground_maps.MapS. *)

      (* Let fresh_meaning := Eval compute in match r_meaning, e_meaning with *)
      (*                      | Some r', Some e' => *)
      (*                          Some (ground_maps.MapS.add "R" r' (ground_maps.MapS.add "E" e' (ground_maps.MapS.empty (list (list ground_types))))) *)
      (*                      | _, _ => None *)
      (*                      end. *)

      (* (* Let fresh_meaning := match meaning with *) *)
      (* (*                      | Some m => *) *)
      (* (*                          Some (ground_maps.MapS.fold (fun key elmt acc => *) *)
      (* (*                                               ground_maps.MapS.add key elmt acc) *) *)
      (* (*                                                m *) *)
      (* (*                                                (ground_maps.MapS.empty (list (list ground_types)))) *) *)
      (* (*                      | None => None *) *)
      (* (*                      end. *) *)

      (* Let meaning' := Eval compute in (match fresh_meaning with *)
      (*                                  | Some m => program_semantics_eval_single_iter m GraphProgram *)
      (*                                  | None => None *)
      (*                                  end). *)

      (* Let find_meaning' x := match meaning' with *)
      (*                       | Some m => ground_maps.MapS.find x m *)
      (*                       | None => None *)
                            (* end. *)

      (* Eval compute in (match find_meaning' "R" with *)
      (*                  | Some m => *)
      (*                      if Nat.leb 1 Datatypes.length m then *)
      (*                        nth_error m 0 *)
      (*                      else None *)
      (*                  | None => None *)
      (*                  end *)
      (*                 ). *)
    End GraphEdges.
  End SemanticsExamples.
End RelSemantics.
