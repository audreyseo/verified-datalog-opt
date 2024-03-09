From Coq Require Import  List String Arith Psatz DecidableTypeEx OrdersEx Program.Equality FMapList FMapWeakList MSetWeakList Lists.ListSet.

From VeriFGH Require Import DatalogSemantics.
From VeriFGH Require Import OrdersFunctor DatalogProps StringOrders RelOrdered OrderedGroundTypes GroundMaps RelDecidable.
Require Export HelperTactics.

Import RelSemantics.

Lemma app_eq_nil {A: Type} :
  forall (l1 l2: list A),
    l1 ++ l2 = nil ->
    l1 = nil /\ l2 = nil.
Proof.
  destruct l1; intros.
  - simpl in H. invs H. split; reflexivity.
  - simpl in H. inversion H.
Qed.

Lemma rev_eq_nil {A: Type}:
  forall (l: list A),
    rev l = nil -> l = nil.
Proof.
  destruct l; intros.
  - reflexivity.
  - simpl in H. eapply app_eq_nil in H. destruct H. congruence.
Qed.


Lemma app_cons_comm {A: Type} :
  forall (l l': list A) (a: A),
    l ++ a :: l' = (l ++ a :: nil) ++ l'.
Proof.
  induction l; simpl; intros.
  - reflexivity.
  - rewrite IHl. reflexivity.
Qed.

Lemma proj_tuples_fold_None :
  forall (pvs: list string) (assoc: tup_type),
    fold_left
      (fun (acc : option tup_type) (elmt : string) =>
         match assoc_lookup assoc elmt with
         | Some gt => option_map (cons (elmt, gt)) acc
         | None => None
         end) pvs None = None.
Proof.
  induction pvs; intros.
  - reflexivity.
  - simpl. destruct (assoc_lookup assoc a); eapply IHpvs.
Qed.

Lemma proj_tuples_fold :
  forall (pvs: list string) (init: tup_type) (assoc: tup_type),
    fold_left (fun (acc: option tup_type) (elmt: string) =>
                 match assoc_lookup assoc elmt with
                 | Some gt => option_map (cons (elmt, gt)) acc
                 | None => None
                 end)
              pvs
              (Some init) =
      match (fold_left (fun (acc: option tup_type) (elmt: string) =>
                          match assoc_lookup assoc elmt with
                          | Some gt => option_map (cons (elmt, gt)) acc
                          | None => None
                          end)
                       pvs
                       (@Some (tup_type) nil)) with
      | Some f' => Some (f' ++ init)
      | None => None
      end.
Proof.
  induction pvs; intros.
  - simpl. reflexivity.
  - simpl. destruct (assoc_lookup assoc a) eqn:A.
    + erewrite IHpvs.
      erewrite IHpvs.
      destruct_match_goal'.
      * erewrite IHpvs in X.
        symmetry. destruct_match_goal'.
        -- destruct (fold_left
                       (fun (acc : option tup_type) (elmt : string) =>
                          match assoc_lookup assoc elmt with
                          | Some gt => option_map (cons (elmt, gt)) acc
                          | None => None
                          end) pvs (Some nil)) eqn:X1.
           (* Set Printing All. *)
           unfold tup_type in X0, X1.
           rewrite X1 in X0.
           rewrite <- app_nil_end in X0.
           invc X0.
           Definition option_map_map {A' B' C': Type} (f: A' -> B' -> C') (a: option A') (b: option B') : option C' :=
             match a, b with
             | Some a', Some b' => Some (f a' b')
             | _, _ => None
             end.
           replace (Some (t ++ init)) with (option_map_map (@app (string * ground_types)) (Some t) (Some init)) by reflexivity.
           rewrite <- X.
           replace ((a, g) :: init) with (((a, g) :: nil) ++ init) by reflexivity.
           (* Set Printing All. *)
           (* rewrite <- app_comm_cons. *)
           (* Set Printing All. *)
           rewrite app_assoc.
           replace (Some ((t0 ++ (a, g) :: nil) ++ init)) with
             (option_map_map (@app (string * ground_types))
                             (Some ((t0 ++ (a, g) :: nil)))
                             (Some init)) by reflexivity.
           f_equal.
           ++ unfold tup_type. rewrite X1. reflexivity.
           ++ rewrite app_cons_comm.
              f_equal. f_equal; eauto.
              assert (Some t = Some (t0 ++ (a, g ) :: nil)).
              rewrite <- X.
              (* Set Printing All. *)
              unfold tup_type in X0, X1.
              rewrite X1 in X0.
              inversion X0.
              invs H.
              reflexivity.
        -- unfold tup_type in *.
           destruct (fold_left
                       (fun (acc : option (list (string * ground_types)))
                          (elmt : string) =>
                          match assoc_lookup assoc elmt with
                          | Some gt => option_map (cons (elmt, gt)) acc
                          | None => None
                          end) pvs (Some nil)) eqn:X1.
           inversion X0.
           inversion X.
      * rewrite IHpvs in X.
        destruct (fold_left
                    (fun (acc : option tup_type) (elmt : string) =>
                       match assoc_lookup assoc elmt with
                       | Some gt => option_map (cons (elmt, gt)) acc
                       | None => None
                       end) pvs (Some nil)) eqn:X0.
        (* Set Printing All. *)
        unfold tup_type in *.
        rewrite X0.
        rewrite X0 in X. inversion X.
        unfold tup_type in *. rewrite X0. reflexivity.
    + clear IHpvs. clear A.
      revert init. revert assoc. induction pvs; intros.
      * simpl. reflexivity.
      * simpl.
        destruct (assoc_lookup assoc a0).
        -- erewrite <- IHpvs. reflexivity.
        -- erewrite <- IHpvs. reflexivity.
Qed.


Lemma Some_append {A: Type} :
  forall (l1 l2: list A),
    Some (l1 ++ l2) = option_map_map (@app A) (Some l1) (Some l2).
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma proj_tuples_fold_None' :
  forall (pvs: list string) (assoc init: tup_type),
    fold_left
      (fun (acc : option (list (string * ground_types))) (elmt : string)
       =>
         match assoc_lookup assoc elmt with
         | Some gt => option_map (cons (elmt, gt)) acc
         | None => None
         end) pvs (Some init) = None ->
    proj_tuples pvs assoc = None.
Proof.
  induction pvs; intros.
  - simpl in H. inversion H.
  - simpl. simpl in H.
    destruct (assoc_lookup assoc a) eqn:A.
    + eapply IHpvs in H.
      rewrite proj_tuples_fold.
      simpl in H. unfold tup_type in *. rewrite H. reflexivity.
    + rewrite proj_tuples_fold_None. reflexivity.
Qed.


Lemma proj_tuples_append :
  forall (pvs pvs': list string) (s: string) (g: ground_types) (res res' assoc: tup_type),
    proj_tuples (pvs ++ pvs') assoc =
      match (proj_tuples pvs assoc), proj_tuples pvs' assoc with
      | Some res, Some res' =>
          Some (res' ++ res)
      | _, _ => None
      end.
Proof.
  induction pvs; intros.
  - simpl. destruct_match_goal'.
    + rewrite <- app_nil_end. reflexivity.
    + reflexivity.
  - destruct (proj_tuples (a :: pvs) assoc) eqn:X.
    + rewrite <- app_nil_l with (l := pvs) in X.
      rewrite app_comm_cons in X.
      specialize (IHpvs pvs').
      specialize (IHpvs s g res res' assoc).
      destruct (proj_tuples pvs' assoc) eqn:P.
      * destruct (proj_tuples pvs assoc) eqn:P'.
        -- simpl. simpl in X. destruct (assoc_lookup assoc a) eqn:A.
           ++ rewrite proj_tuples_fold.
              rewrite proj_tuples_fold in X.
              unfold tup_type in *.
              replace (fold_left
                         (fun (acc : option (list (string * ground_types))) (elmt : string) =>
                            match assoc_lookup assoc elmt with
                            | Some gt => option_map (cons (elmt, gt)) acc
                            | None => None
                            end) (pvs ++ pvs') (Some nil)) with (proj_tuples (pvs ++ pvs') assoc) by reflexivity.
              rewrite IHpvs.
              
              rewrite <- app_assoc.
              rewrite Some_append.
              rewrite Some_append at 1.
              rewrite Some_append.
              f_equal.
              simpl. rewrite <- X.
              destruct_match_goal'.
              replace (fold_left
                         (fun (acc : option (list (string * ground_types)))
                            (elmt : string) =>
                            match assoc_lookup assoc elmt with
                            | Some gt => option_map (cons (elmt, gt)) acc
                            | None => None
                            end) pvs (Some nil)) with (proj_tuples pvs assoc) in X0 by reflexivity.
              rewrite X0 in P'. invs P'. reflexivity.
              inversion X.
           ++ rewrite proj_tuples_fold_None in X. inversion X.
        -- simpl in X.
           destruct (assoc_lookup assoc a) eqn:A.
           ++ rewrite proj_tuples_fold in X.
              simpl in P'. unfold tup_type in *. rewrite P' in X. inversion X.
           ++ rewrite proj_tuples_fold_None in X. inversion X.
      * simpl in X. pose proof (PROJ := proj_tuples_fold).
        unfold tup_type in *.
        destruct (assoc_lookup assoc a) eqn:A.
        rewrite PROJ in X.
        fold (proj_tuples pvs assoc) in X.
        destruct (proj_tuples pvs assoc).
        simpl. rewrite A.
        rewrite proj_tuples_fold.
        simpl in IHpvs.
        unfold tup_type in *. rewrite IHpvs. reflexivity.
        inversion X.
        rewrite proj_tuples_fold_None in X. invs X.
    + simpl. destruct (assoc_lookup assoc a) eqn:A.
      * rewrite proj_tuples_fold.
        unfold proj_tuples in *. unfold tup_type in *. rewrite IHpvs.
        simpl in X.
        rewrite A in X.
        pose proof (PROJ := proj_tuples_fold_None').
        unfold tup_type in *. simpl in PROJ. erewrite PROJ. reflexivity.
        eapply proj_tuples_fold_None' in X.
        simpl in X. unfold tup_type in *. rewrite X. reflexivity.
        eassumption. eassumption.
        eassumption. eassumption.
      * rewrite proj_tuples_fold_None. reflexivity.
Qed.







Lemma proj_tuples_cons :
  forall (pvs: list string) (s: string) (g: ground_types) (res assoc: tup_type),
    proj_tuples (s :: pvs) assoc =
      match (proj_tuples pvs assoc), assoc_lookup assoc s with
      | Some res, Some g =>
          Some (res ++ ((s, g) :: nil))
      | _, _ => None
      end.
Proof.
  intros.
  replace (s :: pvs) with ((s :: nil) ++ pvs) by reflexivity.
  rewrite proj_tuples_append; try eassumption.
  destruct (proj_tuples (s :: nil) assoc) eqn:P.
  - destruct (proj_tuples pvs assoc) eqn:P'.
    + simpl in P. destruct (assoc_lookup assoc s) eqn:A.
      * invs P. reflexivity.
      * invs P.
    + reflexivity.
  - simpl in P. destruct (assoc_lookup assoc s). inversion P.
    destruct (proj_tuples pvs assoc); reflexivity.
Qed.



Lemma proj_tuples_adequacy :
  forall (pvs: list string) (assoc tt: tup_type),
    proj_tuples_rel pvs assoc tt <->
      Some (rev tt) = proj_tuples pvs assoc.
Proof.
  induction pvs; intros; split; intros.
  - invs H. simpl. reflexivity.
  - simpl in H. invs H.
    destruct tt; invs H1.
    econstructor.
    eapply app_eq_nil in H2. destruct H2. inversion H2.
    
  - invs H. eapply IHpvs in H5. simpl.
    eapply assoc_lookup_adequacy in H2.
    rewrite <- H2. 
    match goal with
    | [ |- @Some ?tipe ?x = _ ] =>
        replace (@Some tipe x) with (option_map_map (@app (string * ground_types)) (Some (rev res)) ((Some ((a, g) :: nil)))) by reflexivity
    end.
    rewrite H5.
    pose proof (proj_tuples_append).
    specialize (H0 (a :: nil) pvs).
    specialize (H0 a g assoc res assoc).
    simpl in H0.
    rewrite <- H2 in H0.
    rewrite H0. simpl.
    rewrite <- H0. unfold option_map_map.
    symmetry.
    destruct_match_goal'.
    + eassumption.
    + eassumption.
  - simpl in H. destruct (assoc_lookup assoc a) eqn:A.
    + rewrite proj_tuples_fold in H.
      unfold tup_type in *.
      replace (fold_left (fun (acc : option (list (string * ground_types))) (elmt : string) =>
                            match assoc_lookup assoc elmt with
                            | Some gt => option_map (cons (elmt, gt)) acc
                            | None => None
                            end) pvs (Some nil)) with (proj_tuples pvs assoc) in H by reflexivity.
      destruct (proj_tuples pvs assoc) eqn:P.
      * invs H.
        assert (rev (rev tt) = (rev (l ++ (a, g) :: nil))) by (f_equal; eauto).
        rewrite rev_involutive in H0. rewrite H0.
        rewrite rev_app_distr.
        simpl. econstructor.
        eapply assoc_lookup_adequacy. congruence.
        eapply IHpvs.
        rewrite rev_involutive. congruence.
      * invs H.
    + rewrite proj_tuples_fold_None in H. invs H.
Qed.

Lemma set_inter_subset_empty :
  forall v' a init,
    set_inter str_gt_list_ot.eq_dec (a :: v') init =
      empty_set str_gt_list_ot.t ->
    set_inter str_gt_list_ot.eq_dec v' init =
      empty_set str_gt_list_ot.t.
Proof.
  induction v'; intros.
  - reflexivity.
  - simpl in H. destruct (set_mem str_gt_list_ot.eq_dec a0 init) eqn:A0; try congruence.
    + inversion H.
    + destruct (set_mem str_gt_list_ot.eq_dec a init) eqn:A; try congruence.
      * inversion H.
      * simpl.
        rewrite A. eassumption.
Qed.


Lemma set_inter_elements {A: Type} :
  forall (Aeq_dec : forall (a1 a2: A), { a1 = a2 } + { a1 <> a2 }) l1 l2 a,
    set_In a (set_inter Aeq_dec l1 l2) <->
      set_In a l1 /\ set_In a l2.
Proof.
  induction l1; intros; split; intros.
  - simpl in H. inversion H.
  - destruct H. invs H.
  - simpl in H. destruct (set_mem Aeq_dec a l2) eqn:A'.
    + eapply set_mem_correct1 in A'.
      simpl in H. destruct H.
      * subst. split.
        -- simpl. left. reflexivity.
        -- eassumption.
      * eapply IHl1 in H. destruct H.
        split; simpl.
        -- right. eassumption.
        -- eassumption.
    + eapply IHl1 in H. destruct H. split; simpl.
      * right. eassumption.
      * eassumption.
  - simpl in H. destruct H.
    destruct H.
    + simpl. subst. eapply set_mem_correct2 in H0. erewrite H0.
      simpl. left. reflexivity.
    + simpl. destruct (set_mem Aeq_dec a l2) eqn:A'.
      * simpl. right. eapply IHl1; eauto.
      * eapply IHl1; eauto.
Qed.



Lemma set_inter_empty :
  forall v' a init,
    set_inter str_gt_list_ot.eq_dec v' (a :: init) =
      empty_set str_gt_list_ot.t ->
    ~ (set_In a v').
Proof.
  induction v'; intros.
  - unfold not; intros. inversion H0.
  - simpl. unfold not. intros.
    destruct H0.
    + subst. simpl in H.
      destruct (str_gt_list_ot.eq_dec a0 a0); try congruence.
      invs H.
    + eapply set_inter_subset_empty in H.
      assert (set_In a0 (a0 :: init)).
      {
        simpl. left. reflexivity.
      }
      assert (set_In a0 (set_inter str_gt_list_ot.eq_dec v' (a0 :: init))).
      {
        eapply set_inter_elements; split; eauto.
      }
      rewrite H in H2. invs H2.
Qed.



Lemma proj_relation_init :
  forall (init v: tup_set) (pvs: list string) v' a l,
    Some v' = proj_relation pvs (a :: v) ->
    set_inter str_gt_list_ot.eq_dec v' init =
      empty_set str_gt_list_ot.t ->
    proj_tuples pvs a = Some l ->
    init ++ l :: nil = set_add str_gt_list_ot.eq_dec l init.
Proof.
  induction init; intros; simpl.
  - reflexivity.
  - destruct (str_gt_list_ot.eq_dec l a).
    + eapply set_inter_empty in H0.
      unfold str_gt_list_ot.eq in e.
      subst.
      Opaque proj_tuples.
      simpl in H.
      rewrite H1 in H.
      eapply list_set_equality.
      simpl. intros.
      split; intros.
      * pose proof (str_gt_list_ot.eq_dec a x). destruct H3.
        -- destruct H2.
           ++ left. eassumption.
           ++ invs e. left. reflexivity.
        -- destruct H2. congruence.
           right. eapply in_app_or in H2.
           destruct H2.
           ++ eassumption.
           ++ simpl in H2. destruct H2; try congruence.
              contradiction.
      * destruct H2.
        -- left. eauto.
        -- right. eapply in_or_app. left. eauto.
    + erewrite IHinit; eauto.
      pose proof (set_inter_empty).
      specialize (H2 v' a init).
      specialize (H2 H0).
      eapply list_set_equality.
      simpl. intros. split; intros.
      * eapply set_inter_elements in H3. destruct H3.
        assert (set_In x (a :: init)).
        {
          simpl. right. eassumption.
        }
        pose proof (@set_inter_elements tup_type).
        specialize (H6 str_gt_list_ot.eq_dec v' (a :: init)).
        specialize (H6 x). destruct H6.
        assert (set_In x v' /\ set_In x (a :: init)) by (split; eauto).
        eapply H7 in H8.
        (* Set Printing All. *)
        unfold str_gt_list_ot.t in *. unfold tup_type in *.
        rewrite H0 in H8.
        inversion H8.
      * inversion H3.
Qed.

(* TODO *)
Lemma proj_relation_fold_Some :
  forall v pvs v' init,
    Some v' =
      set_fold_left
        (fun (acc : option (set tup_type)) (elmt : tup_type) =>
           match proj_tuples pvs elmt with
           | Some tup => option_map (set_add str_gt_list_ot.eq_dec tup) acc
           | None => None
           end) v (Some init) ->
    exists v'',
      Some v'' = proj_relation pvs v.
Proof.
Admitted.

Lemma proj_relation_fold_None :
  forall v pvs,
    set_fold_left
      (fun (acc : option (set tup_type)) (elmt : tup_type) =>
         match proj_tuples pvs elmt with
         | Some tup => option_map (set_add str_gt_list_ot.eq_dec tup) acc
         | None => None
         end) v None = None.
Proof.
  induction v; intros.
  - simpl. reflexivity.
  - simpl. destruct (proj_tuples pvs a); eauto.
Qed.



Lemma proj_relation_fold :
  forall (v v' init: tup_set) (pvs: list string),
    Some v' = proj_relation pvs v ->
    (* set_inter (str_gt_list_ot.eq_dec) v' init = empty_set str_gt_list_ot.t -> *)
    set_fold_left (fun (acc : option (set tup_type)) (elmt : tup_type) =>
                     match proj_tuples pvs elmt with
                     | Some tup => option_map (set_add str_gt_list_ot.eq_dec tup) acc
                     | None => None
                     end) v (Some (init)) =
      match set_fold_left (fun (acc : option (set tup_type)) (elmt : tup_type) =>
                             match proj_tuples pvs elmt with
                             | Some tup => option_map (set_add str_gt_list_ot.eq_dec tup) acc
                             | None => None
                             end) v (Some (empty_set tup_type)) with
      | Some f' => Some (init ++ f')
      | None => None
      end.
Proof.
  induction v; intros.
  - simpl. unfold empty_set.
    rewrite app_nil_r. eauto.
  - Opaque proj_tuples. simpl.
    simpl in H.
    destruct (proj_tuples pvs a).
    + rewrite <- H.
      pose proof (PROJ := proj_relation_fold_Some).
      specialize (PROJ v pvs v' (l :: nil) H).
      destruct PROJ as (v'' & PROJ).
      erewrite IHv; eauto.
      destruct (set_fold_left
                  (fun (acc : option (set tup_type)) (elmt : tup_type) =>
                     match proj_tuples pvs elmt with
                     | Some tup => option_map (set_add str_gt_list_ot.eq_dec tup) acc
                     | None => None
                     end) v (Some (empty_set tup_type))) eqn:F.
      -- f_equal.
         eapply list_set_equality.
         simpl. intros.
         split; intros.
         ++ eapply in_app_or in H0.
            eapply in_or_app.
            destruct H0.
            ** eapply set_add_elim in H0.
               destruct H0; subst.
               --- right.
                   erewrite IHv in H.
                   rewrite F in H. invs H. left. eauto.
                   symmetry in F. eapply F.
               --- left. eauto.
            ** erewrite IHv in H. rewrite F in H. invs H. right. right. eauto.
               symmetry in F. eapply F.
         ++ eapply in_app_or in H0. eapply in_or_app.
            destruct H0.
            ** left. eapply set_add_iff. right. eauto.
            ** erewrite IHv in H. rewrite F in H.
               invs H.
               invs H0.
               --- left. eapply set_add_iff. left. eauto.
               --- right. eauto.
               --- symmetry in F. eauto.
      -- pose proof (proj_relation_fold_Some).
         specialize (H0 v pvs v' (l :: nil)).
         specialize (H0 H).
         destruct H0.
         erewrite IHv in H. rewrite F in H. invs H.
         eapply proj_relation_fold_Some in H.
         eapply H0.
    + rewrite proj_relation_fold_None. reflexivity.
Qed.


Lemma proj_relation_adequacy :
  forall (t1 t2: tup_set)  (pvs: list string),
    proj_relation_rel pvs t1 t2 <->
      Some (map (@rev (string * ground_types)) t2) = proj_relation pvs t1.
Proof.
  split.
  - intros P. induction P; intros.
    + simpl. reflexivity.
    + simpl.
      eapply proj_tuples_adequacy in H. rewrite <- H.
      symmetry.
      erewrite proj_relation_fold; eauto.
      fold (proj_relation pvs t1). rewrite <- IHP. simpl.
      f_equal.
  - revert pvs. revert t2. induction t1; intros.
    + simpl in H. invs H. unfold empty_set in H1.
      destruct t2. econstructor. simpl in H1. invs H1.
    + simpl in H.
      destruct (proj_tuples pvs a) eqn:PROJ.
      * symmetry in PROJ.
        pose proof (PROJ' := proj_relation_fold_Some).
        specialize (PROJ' _ _ _ _ H).
        destruct PROJ' as (v'' & PROJ').
        erewrite proj_relation_fold in H.
        (* specialize (PROJ' _ _ _ _ H). *)
        destruct (set_fold_left
                    (fun (acc : option (set tup_type)) (elmt : tup_type) =>
                       match proj_tuples pvs elmt with
                       | Some tup =>
                           option_map (set_add str_gt_list_ot.eq_dec tup) acc
                       | None => None
                       end) t1 (Some (empty_set tup_type))) eqn:V.
        -- invs H.
           destruct t2.
           simpl in H1. invs H1.
           simpl in H1. invs H1.
           econstructor.
           Local Open Scope string_scope.
           eapply "R".
           eapply proj_tuples_adequacy. eauto.
           eapply IHt1. symmetry. eauto.
        -- invs H.
        --  eauto.
      * rewrite proj_relation_fold_None in H. invs H.
Qed.

Lemma monotone_op_semantics_det :
  forall (m: monotone_ops) (g: gm_type) (v v': ListSet.set tup_type),
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
  forall (m: monotone_ops) (g: gm_type) (v: ListSet.set tup_type),
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
    
    destruct_hyp_match.
    symmetry in X. eapply IHm in X.
    econstructor; eauto.
  - 
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
  - Opaque join_tuples join_relations.
    simpl in H. destruct_hyp_match. destruct_hyp_match.
    econstructor; eauto.
    eapply IHm1.
    congruence.
    eapply IHm2. congruence.
  - inversion H. subst. eapply IHm1 in H4. eapply IHm2 in H6.
    simpl. rewrite <- H4. rewrite <- H6. reflexivity.
Qed.


