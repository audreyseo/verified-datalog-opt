From Coq Require Import  List String Arith Psatz DecidableTypeEx OrdersEx Program.Equality FMapList FMapWeakList MSetWeakList Lists.ListSet.

From VeriFGH Require Import OrdersFunctor DatalogProps StringOrders RelOrdered OrderedGroundTypes GroundMaps RelDecidable.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.

Ltac invs H := inversion H; subst.
Ltac invc H := inversion H; subst; clear H.


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
  Arguments proj_tuples pvs assoc /.

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

  Arguments select_tuples n v assoc /.
  
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
  Arguments join_tuples jvs assoc1 assoc2 /.
  
  Definition join_relations (jvs: list string) (v1 v2: ListSet.set tup_type) :=
    List.fold_left (fun (acc: ListSet.set tup_type) (elmt: (tup_type * tup_type)) =>
                           let (t1, t2) := elmt in
                           match join_tuples jvs t1 t2 with
                           | Some tup => set_add str_gt_list_ot.eq_dec tup acc
                           | None => acc
                           end)
                        (set_prod v1 v2)
                        (@empty_set tup_type).
  Arguments join_relations jvs v1 v2 /.

  Definition select_relation_f (n: string) (g: ground_types) (acc: ListSet.set tup_type) (elmt: tup_type)  :=
    match select_tuples n g elmt with
    | Some tup => set_add str_gt_list_ot.eq_dec tup acc
    | None => acc
    end.

  Arguments select_relation_f _ _ / _ _.

  Definition select_relation (n: string) (g: ground_types) (v: ListSet.set tup_type) :=
    set_fold_left (select_relation_f n g)
                  v
                  (@empty_set tup_type).
  Arguments select_relation / _ _ _.

  Definition proj_relation (pvs: list string) (v: ListSet.set tup_type) :=
    set_fold_left (fun (acc: option (ListSet.set tup_type)) (elmt: tup_type)  =>
                     match proj_tuples pvs elmt with
                     | Some tup => option_map (set_add str_gt_list_ot.eq_dec tup) acc
                     | None => None
                     end)
                  v
                  (Some (@empty_set tup_type)).

  Arguments proj_relation / _ _.

  Definition tup_empty_set := @empty_set tup_type.
  Arguments tup_empty_set /.
  Definition tup_set: Type := ListSet.set tup_type.
  Arguments tup_set /.

  (* Definition proj_tuples (pvs: list string) (assoc: tup_type) :=
    List.fold_left (fun acc (elmt: string) =>
                      match assoc_lookup assoc elmt with
                      | Some gt => option_map (cons (elmt, gt)) acc
                      | None => None
                      end)
                   pvs
                   (Some nil). *)
  Inductive assoc_lookup_rel : tup_type -> string -> ground_types -> Prop :=
  | assoc_lookup_done :
    forall (x: string) (elmt: ground_types) (assoc: tup_type),
      assoc_lookup_rel ((x, elmt) :: assoc) x elmt
  | assoc_lookup_continue :
    forall (x y: string) (elmt elmt': ground_types) (assoc: tup_type),
      x <> y ->
      assoc_lookup_rel assoc y elmt' ->
      assoc_lookup_rel ((x, elmt) :: assoc) y elmt'.

  Lemma assoc_lookup_adequacy :
    forall (tt: tup_type) (s: string) (g: ground_types),
      assoc_lookup_rel tt s g <->
        Some g = assoc_lookup tt s.
  Proof.
    induction tt; intros; split; intros.
    - inversion H.
    - inversion H.
    - invs H.
      + simpl. destruct (string_dec s s) eqn:H'; try congruence.
      + simpl. destruct (string_dec s x) eqn:H'; try congruence.
        eapply IHtt. eassumption.
    - simpl in H. destruct a. destruct (string_dec s s0) eqn:H'; subst.
      + invs H. econstructor.
      + eapply assoc_lookup_continue. congruence. eapply IHtt; eauto.
  Qed.
  
      
  Inductive proj_tuples_rel : list string -> tup_type -> tup_type -> Prop :=
  | proj_tuples_done :
    forall (assoc: tup_type),
    (* forall (t res: tup_type) (s: string) (g: ground_types), *)
      (* assoc_lookup_rel t s g -> *)
      proj_tuples_rel nil assoc nil 
  | proj_tuples_step :
    forall (pvs: list string) (assoc res: tup_type) (s: string) (g: ground_types),
      assoc_lookup_rel assoc s g ->
      proj_tuples_rel pvs assoc res ->
      proj_tuples_rel (s :: pvs) assoc ((s, g) :: res).


        
  Definition list_set_subset {T: Type} (v v': ListSet.set T) :=
    forall (x: T),
      set_In x v -> set_In x v'.
  Arguments list_set_subset {T}%type_scope v v'/.

  Definition list_set_equal {T: Type} (v v': ListSet.set T) :=
    forall (x: T),
      set_In x v <-> set_In x v'.
  Arguments list_set_equal {T}%type_scope v v' /.

  Lemma list_set_eq_refl {T: Type}:
    forall (v v': ListSet.set T),
      v = v' ->
      list_set_equal v v'.
  Proof.
    intros. simpl. subst. split; intros; eauto.
  Qed.
  Axiom list_set_equality :
    forall (T: Type) (x1 x2: ListSet.set T),
      list_set_equal x1 x2 ->
      x1 = x2.
  
      

  Inductive proj_relation_rel : list string -> tup_set -> tup_set -> Prop :=
  | proj_rel_nil :
    forall (pvs: list string),
      proj_relation_rel pvs tup_empty_set tup_empty_set
  | proj_rel_cons_skip :
    forall (pvs: list string) (s: string) (t' t'': tup_type) (t1 t2: tup_set),
      proj_tuples_rel pvs t' t'' ->
      proj_relation_rel pvs t1 t2 ->
      proj_relation_rel pvs (t' :: t1) (t'' :: t2).

  Print proj_relation.

        
                                

  Definition assign_vars_to_tuples (R: rel) (v: list (list ground_types)) :=
    List.fold_left (fun acc elmt =>
                      match variable_list_groundings_to_assoc_list R elmt with
                      | Some l => set_add str_gt_list_ot.eq_dec l acc
                      | None => acc
                      end)
                   v
                   (@empty_set tup_type).
  Arguments assign_vars_to_tuples / _ _.

  Print ground_maps.

  Definition gt_set_type := list (list ground_types).

  Definition gm_empty := ground_maps.empty gt_set_type.

  Definition gm_type := ground_maps.t gt_set_type.

                        
  Inductive monotone_op_semantics : gm_type -> monotone_ops -> ListSet.set tup_type -> Prop :=
  | atom_semantics :
    forall (R: rel) (g: gm_type) (v: list (list ground_types)),
      ground_maps.find (name R) g = Some v ->
      monotone_op_semantics g (ATOM R) (assign_vars_to_tuples R v)
  | select_semantics :
    forall (g: gm_type) (v v': ListSet.set tup_type) (n: string) (gt: ground_types) (m: monotone_ops),
      monotone_op_semantics g m v ->
      v' = select_relation n gt v ->
      monotone_op_semantics g (SELECT n gt m) v'
  | join_semantics :
    forall (g: gm_type) (m1 m2: monotone_ops)
      (jvs: list string) (v1 v2 v: (ListSet.set tup_type)),
      monotone_op_semantics g m1 v1 ->
      monotone_op_semantics g m2 v2 ->
      v = join_relations jvs v1 v2 ->
      monotone_op_semantics g (JOIN jvs m1 m2) v
  | union_semantics :
    forall (g: gm_type) (m1 m2: monotone_ops)
      (v1 v2 v: ListSet.set tup_type),
      monotone_op_semantics g m1 v1 ->
      monotone_op_semantics g m2 v2 ->
      v = set_union str_gt_list_ot.eq_dec v1 v2 ->
      monotone_op_semantics g (UNION m1 m2) v
  | proj_semantics :
    forall (g: gm_type) (m: monotone_ops)
      (pvs: list string) (v v': ListSet.set tup_type),
      monotone_op_semantics g m v ->
      proj_relation pvs v = Some v' ->
      monotone_op_semantics g (PROJ pvs m) v'.

  Fixpoint monotone_op_semantics_eval
           (g: gm_type)
           (m: monotone_ops) : option (ListSet.set tup_type) :=
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
    set_fold_left (fun acc elmt =>
                      match anonymize_tuple names elmt with
                      | Some t =>
                          option_map (set_add List_Ground_Type_as_OTF.eq_dec t) acc
                      | None => None
                      end)
                   v
                   (Some (@empty_set List_Ground_Type_as_OTF.t)).

  (* Arguments set_fold_left [A]%type_scope f%function_scope s _ /. *)

  Check ground_maps.mapi.

  
  Lemma ground_maps_t_to_ground_maps_maps_t :
    gm_type = ground_maps.t gt_set_type.
  Proof.
    reflexivity.
  Defined.

  Print ground_maps.
      

  Inductive rule_semantics : gm_type -> list (string * rel * monotone_ops) -> gm_type -> Prop :=
  | nil_rules_semantics :
    forall (g: gm_type),
      rule_semantics g nil g
  | cons_rules_semantics :
    forall (g g' g'': gm_type)
      (v: ListSet.set tup_type)
      (rel_name: string)
      (m: monotone_ops) (R: rel)
      (new_tuples old_tuples: list (list ground_types))
      (rst: list (string * rel * monotone_ops)),
      name R = rel_name ->
      monotone_op_semantics g m v ->
      Some new_tuples = anonymize_tuples (Vector.to_list (args R)) v ->
      Some old_tuples = ground_maps.find rel_name g ->
      g' = ground_maps.add rel_name (ListSet.set_union List_Ground_Type_as_OTF.eq_dec new_tuples old_tuples) g ->
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
                  rule_semantics_eval' g' rst_rules
              | _, _ => None
              end
          | None => None
          end
        else rule_semantics_eval' g rst_rules
    end.

  

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
      ~ (ground_maps.Equal g g') ->
      program_semantics g' rulez g'' ->
      program_semantics g rulez g''.





  

  Definition fold_left_fun_monotone_gen {A B: Type} (f: B -> A -> B) (B_to_set: B -> option (set tup_type)) :=
    forall (a: A) (v': B),
      match (B_to_set v'), (B_to_set (f v' a)) with
      | Some v'', Some v''' => list_set_subset v'' v'''
      | Some v'', None => False
      | _, _ => True
      end.
  Arguments fold_left_fun_monotone_gen {A B}%type f B_to_set /.

  
  Definition option_list_subset {B: Type} (B_to_set: B -> option (set tup_type)) (s1 s2: B) :=
    match (B_to_set s1), (B_to_set s2) with
    | Some s1', Some s2' => list_set_subset s1' s2'
    | _, _ => False
    end.

  Arguments option_list_subset {B}%type_scope B_to_set s1 s2 /.

  (* Lemma option_fold_left_monotone {A B: Type} : *)
  (*   forall (f: B -> A -> B) (B_to_set : B -> option (set tup_type)) (v: set A) (B_empty_set init: B), *)
  (*     B_to_set B_empty_set = Some (empty_set tup_type) -> *)
  (*   forall (x: tup_type), *)
  (*     fold_left_fun_monotone_gen f B_to_set -> *)
  (*     match B_to_set (set_fold_left f v init) with *)
  (*     | Some b' => set_In x b' *)
  (*     | _ => False *)
  (*     end -> *)
  (*     match B_to_set init with *)
  (*     | Some init' => set_In x init' *)
  (*     | _ => False *)
  (*     end \/ *)
  (*       match B_to_set (set_fold_left f v B_empty_set) with *)
  (*       | Some b' => set_In x b' *)
  (*       | _ => False *)
  (*       end. *)
  (* Proof. *)
  (*   intros f B_to_set v. induction v; intros. *)
  (*   - simpl in H1. destruct (B_to_set init) eqn:B'; try inversion H1. *)
  (*     simpl in H0. *)
  (*     destruct (B_to_set (set_fold_left f nil B_empty_set)) eqn:B''. *)
  (*     + left. assumption. *)
  (*     + left. assumption. *)
  (*   - simpl in H1. simpl. eapply IHv with (B_empty_set := B_empty_set) in H1; try eassumption. *)
  (*     destruct H1. *)
  (*     + simpl. destruct (B_to_set (f init a)) eqn:B''; try inversion H1. *)
  (*       simpl in H0. *)
  (*       pose proof (H2 := H0 a init). *)
  (*       specialize (H0 a init). *)
  (*       destruct (B_to_set init). *)
  (*       * rewrite B'' in H0.  *)
  (* destruct (B_to_set init) eqn:B'. *)
  
  Definition fold_left_fun_monotone {A : Type} (f: set tup_type -> A -> set tup_type) :=
    forall (a: A) (v: set tup_type),
      list_set_subset v (f v a).

  

  Arguments fold_left_fun_monotone {A}%type_scope f /.

  

        
      
      
  Definition program_semantics_eval_loop_body (g: gm_type) (rulez: list (string * rel * monotone_ops)): option gm_type :=
    let new_g := rule_semantics_eval' g rulez in
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

  
  Definition ground_map_Subset (g1 g2: gm_type) :=
    (forall (x: string),
        ground_maps.In x g1 ->
        ground_maps.In x g2) /\
      (forall (x: string) (l1 l2: List_Ground_Type_as_OT.t),
          ground_maps.find x g1 = Some l1 ->
          ground_maps.find x g2 = Some l2 ->
          list_set_subset l1 l2).
  Arguments ground_map_Subset g1 g2 /.

  
  Fixpoint assoc_lookup_gen {T: Type} (l: list (string * T)) (s: string) : option T :=
        match l with
        | nil => None
        | (hd1, hd2) :: tl =>
            if string_dec hd1 s then
              Some hd2
            else assoc_lookup_gen tl s
        end.
      
        
      
      
      

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

      Let meaning := Eval compute in program_semantics_eval_without_fixpoint G' GraphProgram 2.


      
            
      
      Let find_meaning (meaning: option gm_type) x :=
            Eval compute in
            match meaning with
            | Some m => assoc_lookup_gen (ground_maps.this m) x
            | None => None
            end.

      Let r_meaning := Eval compute in find_meaning meaning "R".
      Let e_meaning := Eval compute in find_meaning meaning "E".
      Transparent proj_tuples.
      Eval compute in r_meaning.
      Eval compute in e_meaning.

      Let meaning' := Eval compute in (match meaning with
                                       | Some m => program_semantics_eval_without_fixpoint m GraphProgram 1
                                       | None => None
                                       end).
      Print meaning'.
      Let r_meaning' := Eval compute in find_meaning meaning' "R".
      Eval compute in r_meaning'.

    End GraphEdges.
  End SemanticsExamples.
End RelSemantics.

