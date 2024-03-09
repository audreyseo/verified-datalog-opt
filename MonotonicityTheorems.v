From Coq Require Import  List String Arith Psatz DecidableTypeEx OrdersEx Program.Equality FMapList FMapWeakList MSetWeakList Lists.ListSet.

From VeriFGH Require Import DatalogSemantics.
From VeriFGH Require Import OrdersFunctor DatalogProps StringOrders RelOrdered OrderedGroundTypes GroundMaps RelDecidable GroundMapsHelpers.

Require Export RuleSemanticsTheorems.

Import RelSemantics.


Lemma set_fold_left_subset {A B: Type} :
  forall (f: B -> A -> B) (B_to_set: B -> option (set tup_type)) (v: set A) (init: B),
    fold_left_fun_monotone_gen f B_to_set ->
    (* (forall (a: A) (v': B), match (B_to_set v'), (B_to_set (f v' a)) with *)
    (*                    | Some v'', Some v''' => list_set_subset v'' v''' *)
    (*                    | Some v'', None => False *)
    (*                    | _, _ => True *)
    (*                    end) -> *)
    match (B_to_set init), (B_to_set ((set_fold_left f v init))) with
    | Some i, Some s => list_set_subset i s
    | _, _ => True
    end.
Proof.
  induction v; simpl; intros; simpl.
  - simpl. destruct (B_to_set init) eqn:i; eauto.
  - simpl. simpl in *.
    specialize (IHv (f init a)).
    specialize (IHv H). eauto.
    specialize (H a init).
    destruct (B_to_set init) eqn:I; destruct (B_to_set (set_fold_left f v (f init a))) eqn:I'; eauto.
    destruct (B_to_set (f init a)) eqn:I''.
    + intros. eapply IHv. eauto.
    + inversion H.
Qed.

Lemma set_fold_left_subset' {A: Type} :
  forall (f: set tup_type -> A -> set tup_type) (v: set A) (init: set tup_type),
    fold_left_fun_monotone f ->
    list_set_subset init (set_fold_left f v init).
Proof.
  intros.
  pose proof (set_fold_left_subset f (fun a => Some a)).
  specialize (H0 v init).
  simpl in H0.
  unfold list_set_subset. intros. eapply H0. unfold fold_left_fun_monotone in H.
  intros. eapply H. eassumption. eassumption.
Qed.




Lemma in_select_tuples_fold :
  forall (v v0: ListSet.set tup_type) (x: tup_type),
  forall var val,
    List.In x v0 ->
    List.In x
            (set_fold_left
               (fun (acc : set tup_type) (elmt : tup_type) =>
                  match select_tuples var val elmt with
                  | Some tup => set_add str_gt_list_ot.eq_dec tup acc
                  | None => acc
                  end) v v0).
Proof.
  induction v; intros.
  - simpl. eassumption.
  - Opaque select_tuples. simpl. eapply IHv.
    destruct (select_tuples var val a) eqn:S.
    +
eapply set_add_intro1. eassumption.
+ eassumption.
Qed.

Lemma in_select_tuples_fold2 :
  forall (v v0: ListSet.set tup_type) (x: tup_type),
  forall var val tup,
    List.In x v ->
    Some tup = select_tuples var val x ->
    List.In tup (set_fold_left
                   (fun (acc : set tup_type) (elmt : tup_type) =>
                      match select_tuples var val elmt with
                      | Some tup => set_add str_gt_list_ot.eq_dec tup acc
                      | None => acc
                      end) v v0).
Proof.
  induction v; intros.
  - inversion H.
  - simpl in H. destruct H.
    + simpl. unfold set_fold_left.
      eapply in_select_tuples_fold.
      subst.
rewrite <- H0. eapply set_add_intro2. reflexivity.
+ simpl. unfold set_fold_left.
eapply IHv. eassumption. eassumption.
Qed.

(* I wouldn't normally admit something like this, but if we don't run into any really terrible things...this might make it a bit easier. *)
Axiom ground_maps_equality :
  forall (g g': gm_type),
    ground_maps.Equal g g' ->
    g = g'.


Lemma program_semantics_det :
  forall (g g' g'': gm_type) (rulez: list (string * rel * monotone_ops)),
    program_semantics g rulez g' ->
    program_semantics g rulez g'' ->
    g' = g''.
Proof.
  intros g g' g'' rulez P.
  revert g''. dependent induction P; intros.
  - inversion H1; subst.
    + reflexivity.
    + pose proof (rule_semantics_det _ _ _ _ H H2). subst.
      eapply H3 in H0. inversion H0.
  - invs H1.
    + eapply ground_maps_equality in H3. subst.
      pose proof (rule_semantics_det _ _ _ _ H2 H).
      subst.
      assert (ground_maps.Equal (elt:=gt_set_type) g' g') by (intros; split; intros; eauto).
      eapply H0 in H3. contradiction.
    + pose proof (rule_semantics_det _ _ _ _ H H2). subst.
      eapply IHP.
      eassumption.
Qed.


(* Not extremely necessary, also ended up being grosser than I thought *)
Lemma ground_maps_Equal_implies_equal :
  forall (g g': gm_type),
    ground_maps.Equal (elt:=gt_set_type) g g' <->
      ground_maps.equal List_Ground_Type_as_OT.eqb g g' = true.
Proof.
  destruct g. rename this into g. induction g; split; intros.
  - eapply ground_maps_equality in H. invs H.
    unfold ground_maps.equal. simpl. reflexivity.
  - destruct g'. destruct this.
    + unfold ground_maps.Equal. intros. reflexivity.
    + unfold ground_maps.equal in H. simpl in H. unfold ground_maps.Raw.equal in H. simpl in H.
      unfold ground_maps.Raw.submap in H. simpl in H. destruct p.
      assert False.
      revert H. induction this; intros.
      * inversion H.
      * simpl in H. destruct a. eapply IHthis in H. contradiction.
        invs NoDup0.
        econstructor.
        -- unfold not. intros. negate_negated H2.
           right. eauto.
           eapply H2 in Y. contradiction.
        -- invs H3. eauto.
      * contradiction.
  - eapply ground_maps_equality in H. invs H.
    Print ground_maps.
    eapply ground_maps.equal_1.
    unfold ground_maps.Equivb. unfold ground_maps.Raw.Equivb. split; try split; intros; eauto.
    pose proof (ground_maps_MapsTo_det).
    unfold ground_maps.MapsTo in H2.
    specialize (H2 {| ground_maps.this := a :: g; ground_maps.NoDup := NoDup |}).
    simpl in H2.
    simpl in H, H1.
    specialize (H2 _ _ _ H H1).
    subst.
    unfold List_Ground_Type_as_OT.eqb.
    destruct (List_Ground_Type_as_OT.Inner.eq_dec e' e'). reflexivity. congruence.
  - destruct g'. destruct this.
    + unfold ground_maps.equal in H. unfold ground_maps.Raw.equal in H. simpl in H.
      eapply Bool.andb_true_iff in H. destruct H. unfold ground_maps.Raw.submap in H.
      simpl in H. destruct a.
      assert False.
      clear IHg. clear NoDup0.
      clear H0. induction g.
      simpl in H. invs H.
      simpl in H. destruct a.
      eapply IHg.
      pose proof NoDup_setoid_cons_subsets.
      specialize (H0 _ _ _ NoDup).
      destruct H0.
      eauto.
      eauto.
      contradiction.
    + unfold ground_maps.equal in H. unfold ground_maps.Raw.equal in H. simpl in H.
      eapply Bool.andb_true_iff in H.
      destruct H.
      unfold ground_maps.Raw.submap in H, H0.
      simpl in H, H0. destruct p. destruct a.
      unfold ground_maps.Equal. intros.
      unfold ground_maps.find. simpl.
      destruct (String_as_OT.eq_dec y s0); destruct (String_as_OT.eq_dec y s).
      * subst.
        destruct (andb (ground_maps.Raw.check
            (fun e' e : list (list ground_types) =>
             List_Ground_Type_as_OT.eqb e e') s g0 
            ((s, g1) :: g)) true) eqn:A1;
        destruct (andb (ground_maps.Raw.check List_Ground_Type_as_OT.eqb s g1
                                              ((s, g0) :: this)) true) eqn:A2.
        -- eapply Bool.andb_true_iff in A2, A1.
           destruct A2, A1.
           unfold ground_maps.Raw.check in H1.
           simpl in H1. destruct (String_as_OT.eq_dec s s); try congruence.
           clear H. clear e. clear H2. clear H0 H4 H3. clear NoDup0. clear this. clear IHg. clear NoDup.
           revert H1. revert g0. induction g1; intros.
           ++ unfold List_Ground_Type_as_OT.eqb in *.
              destruct (List_Ground_Type_as_OT.Inner.eq_dec nil g0).
              subst. reflexivity.
              congruence.
           ++ unfold List_Ground_Type_as_OT.eqb in *.
              destruct (List_Ground_Type_as_OT.Inner.eq_dec (a :: g1) g0); try congruence.
        -- eapply Bool.andb_false_iff in A2. destruct A2; try congruence.
           enough (ground_maps.Raw.fold
        (fun (k : ground_maps.Raw.key) (e : list (list ground_types))
           (b : bool) =>
         (ground_maps.Raw.check List_Ground_Type_as_OT.eqb k e
                                ((s, g0) :: this) && b)%bool) g false = false).
           rewrite H2 in H. congruence.
           admit.
        -- eapply Bool.andb_false_iff in A1. destruct A1; try congruence.
           enough (ground_maps.Raw.fold
         (fun (k : ground_maps.Raw.key) (e : list (list ground_types))
            (b : bool) =>
          (ground_maps.Raw.check
             (fun e' e0 : list (list ground_types) =>
              List_Ground_Type_as_OT.eqb e0 e') k e 
             ((s, g1) :: g) && b)%bool) this false = false).
           rewrite H2 in H0. congruence.
           admit.
        -- enough (ground_maps.Raw.fold
        (fun (k : ground_maps.Raw.key) (e : list (list ground_types))
           (b : bool) =>
         (ground_maps.Raw.check List_Ground_Type_as_OT.eqb k e
                                ((s, g0) :: this) && b)%bool) g false = false).
           rewrite H1 in H. congruence.
           admit.
      * subst.
        enough (andb (ground_maps.Raw.check List_Ground_Type_as_OT.eqb s0 g1
                                            ((s, g0) :: this)) true = true).
        unfold ground_maps.Raw.check in H1.
        simpl in H1. destruct (String_as_OT.eq_dec s0 s); try congruence.
        destruct (ground_maps.Raw.find (elt:= list (list ground_types)) s0 this) eqn:F.
        unfold gt_set_type. rewrite F.
        eapply Bool.andb_true_iff in H1. destruct H1.
        enough (List_Ground_Type_as_OT.eqb g1 l = true -> g1 = l).
        eapply H3 in H1. subst. reflexivity.
        admit.
        simpl in H1. congruence.
        admit.
      * subst.
        enough ((ground_maps.Raw.check
            (fun e' e : list (list ground_types) =>
             List_Ground_Type_as_OT.eqb e e') s g0 
            ((s0, g1) :: g) && true)%bool = true).
        eapply Bool.andb_true_iff in H1.
        destruct H1.
        unfold ground_maps.Raw.check in H1.
        simpl in H1. destruct (String_as_OT.eq_dec s s0); try congruence.
        destruct (ground_maps.Raw.find (elt:= list (list ground_types)) s g) eqn:F.
        unfold gt_set_type. rewrite F. unfold List_Ground_Type_as_OT.eqb in H1.
        destruct (List_Ground_Type_as_OT.Inner.eq_dec l g0). subst. reflexivity.
        congruence.
        congruence.
        admit.
      * f_equal.
        invs NoDup. invs NoDup0.
        enough (ground_maps.Equal ({| ground_maps.this := g;
                                     ground_maps.NoDup := H4 |})
                                  ({| ground_maps.this := this;
                                     ground_maps.NoDup := H6 |})).
        eapply ground_maps_equality in H1. invs H1. reflexivity.
        unfold ground_maps.Equal.
        intros.
        enough (ground_maps.equal List_Ground_Type_as_OT.eqb
                                  {| ground_maps.this := g; ground_maps.NoDup := H4 |}
                                  {| ground_maps.this := this; ground_maps.NoDup := H6 |} = true).
        eapply IHg in H1.
        eapply H1.
        unfold ground_maps.equal. unfold ground_maps.Raw.equal.
        unfold ground_maps.Raw.submap.
        eapply Bool.andb_true_iff.
        split.
        -- admit.           
Admitted.

(* not extremely necessary *)
Lemma ground_maps_NEqual_implies_nequal :
  forall (g g': gm_type),
    ~ ground_maps.Equal (elt:=gt_set_type) g g' <->
      ground_maps.equal List_Ground_Type_as_OT.eqb g g' = false.
Proof.
Admitted.


Lemma program_semantics_adequacy' :
  forall (rulez: list (string * rel * monotone_ops)) (g g': gm_type),
    Forall
      (fun elmt : OrdersEx.String_as_OT.t * rel * monotone_ops =>
         let (y, _) := elmt in let (n, r) := y in n = name r) rulez ->

    program_semantics g rulez g' ->
    exists fuel,
      program_semantics_eval_helper g rulez fuel = Some g'.
Proof.
  intros rulez g g' F P.
  dependent induction P; intros.
  - exists 1. simpl.
    eapply rule_semantics_adequacy in H; try eassumption. rewrite <- H.
    eapply ground_maps_Equal_implies_equal in H0. rewrite H0. reflexivity.
  - specialize (IHP F). destruct IHP as (fuel & IHP).
    exists (S fuel).
    simpl.
    eapply rule_semantics_adequacy in H; eauto.
    rewrite <- H.
    eapply ground_maps_NEqual_implies_nequal in H0. rewrite H0.
    eassumption.
Qed.

Lemma program_semantics_adequacy :
  forall (fuel: nat) (rulez: list (string * rel * monotone_ops)) (g g': gm_type),
    Forall
      (fun elmt : OrdersEx.String_as_OT.t * rel * monotone_ops =>
         let (y, _) := elmt in let (n, r) := y in n = name r) rulez ->

    program_semantics_eval_helper g rulez fuel = Some g' ->
    program_semantics g rulez g'.
Proof.
  induction fuel; intros rulez g g' F P.
  - simpl in P. inversion P.
  - simpl in P.
    symmetry in P. destruct_hyp_match.
    destruct (ground_maps.equal List_Ground_Type_as_OT.eqb g g0) eqn:E.
    + eapply ground_maps_Equal_implies_equal in E.
      invc P.
      eapply ground_maps_equality in E. subst.
      econstructor. eapply rule_semantics_adequacy; eauto.
      split; intros; eauto.
    + eapply ground_maps_NEqual_implies_nequal in E.
      eapply program_step_continue.
      * eapply rule_semantics_adequacy; eauto.
      * eassumption.
      * eapply IHfuel; eauto.
Qed.

Lemma fold_left_construction :
  forall v1 v1' init R,
    fold_left
      (fun (acc : set str_gt_list_ot.t) (elmt : list ground_types) =>
         match variable_list_groundings_to_assoc_list R elmt with
         | Some l => set_add str_gt_list_ot.eq_dec l acc
         | None => acc
         end) v1 init = v1' ->
    v1' = init ++ (fold_left
                     (fun (acc : set str_gt_list_ot.t) (elmt : list ground_types) =>
                        match variable_list_groundings_to_assoc_list R elmt with
                        | Some l => set_add str_gt_list_ot.eq_dec l acc
                        | None => acc
                        end) v1 nil).
Proof.
  induction v1; intros.
  - simpl in H. subst. simpl. rewrite app_nil_r. reflexivity.
  - simpl in H. eapply IHv1 in H. rewrite H.
    symmetry.
    match goal with
    | [ |- _ = match ?x with
              | Some _ => _
              | None => init
              end ++ _ ] =>
        destruct (x) eqn:X
    end.
    + simpl. rewrite X.
      match goal with
      | [ |- init ++ ?a = _ ] =>
          remember (a) as y
      end.
      symmetry in Heqy.
      eapply IHv1 in Heqy. subst.
      eapply list_set_equality.
      simpl. intros.
      split; intros.
      * eapply in_app_or in H. destruct H.
        -- eapply in_or_app. left. eapply set_add_iff. right. eassumption.
        -- simpl in H. destruct H.
           ++ subst. eapply in_or_app. left. eapply set_add_iff. left. reflexivity.
           ++ eapply in_or_app. right. eassumption.
      * eapply in_app_or in H. destruct H.
        -- eapply set_add_elim in H. destruct H.
           ++ subst. eapply in_or_app. right. simpl. left. reflexivity.
           ++ eapply in_or_app. left. eauto.
        -- eapply in_or_app. right. simpl. right. eassumption.
    + simpl. rewrite X. reflexivity.
Qed.

Lemma assign_vars_to_tuples_monotone :
  forall (R: rel) (v1 v2: list (list ground_types)) (v1' v2': tup_set),
    list_set_subset v1 v2 ->
    assign_vars_to_tuples R v1 = v1' ->
    assign_vars_to_tuples R v2 = v2' ->
    list_set_subset v1' v2'.
Proof.
  intros R. induction v1; intros.
  - simpl in H0. invs H0. simpl. intros. invs H0.
  - simpl in H.
    assert (set_In a v2).
    {
      eapply H. left. reflexivity.
    }
    assert (list_set_subset v1 v2).
    {
      simpl. intros. eapply H. right. eassumption.
    }
    simpl in H0.
    destruct (variable_list_groundings_to_assoc_list R a) eqn:A.
    pose proof (fold_left_construction).
    specialize (H4 _ _ _ _ H0). rewrite H4. rewrite <- H1. simpl. intros.
    destruct H5.
    + subst.
      assert (v2 = a :: v2).
      {
        (* this normally wouldn't be possible but since we're treating these kinds of lists as sets, this is "fine" *)
        eapply list_set_equality.
        simpl. split; intros.
        - destruct (List_Ground_Type_as_OTF.eq_dec a x0).
          invs e. left. reflexivity.
          right. eassumption.
        - destruct H0; subst; eassumption.
      }
      rewrite H0. clear H0.
      simpl. rewrite A.
      match goal with
      | [ |- set_In _ ?a] =>
          remember (a) as A1
      end.
      symmetry in HeqA1.
      eapply fold_left_construction in HeqA1.
      subst.
      eapply in_or_app.
      left. simpl. left. reflexivity.
    + unfold empty_set.
      eapply IHv1. eapply H3. reflexivity. reflexivity.
      eassumption.
    + unfold empty_set in H0. rewrite <- H0.
      simpl. intros.
      rewrite <- H1. simpl. eapply IHv1. eapply H3. reflexivity. reflexivity.
      eapply H4.
Qed.

Lemma select_relation_fold_app :
  forall v init var val,
    set_fold_left (select_relation_f var val) v init =
      init ++ set_fold_left (select_relation_f var val) v nil.
Proof.
  induction v; intros.
  - simpl. rewrite app_nil_r. reflexivity.
  - Opaque select_relation_f.
    simpl. rewrite IHv. symmetry. rewrite IHv. symmetry.
    eapply list_set_equality.
    simpl. split; intros; eapply in_app_or in H.
    + destruct H.
      * 
        Transparent select_relation_f.
        Opaque select_tuples.
        simpl in H.
        match goal with
        | [ H: List.In x (match ?y with | Some _ => _ | None => init end) |- _ ] =>
            destruct (y) eqn:Y
        end.
        -- simpl.
           rewrite Y.
           eapply in_or_app.
           eapply set_add_elim in H. destruct H; subst.
           ++ right. eapply in_or_app. left. left; reflexivity.
           ++ left. eassumption.
        -- eapply in_or_app. left. eassumption.
      * eapply in_or_app. right. eapply in_or_app. right. eassumption.
    + simpl. destruct (select_tuples var val a) eqn:Y.
      * simpl in H. rewrite Y in H.
        eapply in_or_app. destruct H.
        -- left. eapply set_add_iff. right. eassumption.
        -- eapply in_app_or in H. destruct H.
           ++ left. eapply set_add_iff. left. simpl in H. destruct H; try congruence. contradiction.
           ++ right. eassumption.
      * eapply in_or_app. destruct H.
        -- left. eassumption.
        -- eapply in_app_or in H. simpl in H. rewrite Y in H. simpl in H.
           destruct H; try contradiction.
           right. eassumption.
Qed.



Lemma select_relation_monotone :
  forall v v0 var val,
    list_set_subset v v0 ->
    list_set_subset (select_relation var val v) (select_relation var val v0).
Proof.
  induction v; intros.
  - simpl. intros. invs H0.
  - Opaque select_relation_f.
    unfold select_relation. simpl. intros.
    rewrite select_relation_fold_app in H0.
    assert (v0 = a :: v0).
    {
      simpl in H. eapply list_set_equality.
      simpl. split; intros.
      - right. eassumption.
      - destruct H1; subst.
        + eapply H. left. reflexivity.
        + eassumption.
    }
    rewrite H1.
    simpl. rewrite select_relation_fold_app.
    
    eapply in_or_app.
    eapply in_app_or in H0. destruct H0.
    + left. Transparent select_relation_f. simpl in H0. simpl.
      destruct (select_tuples var val a) eqn:Y. clear H1.
      * eapply H0.
      * invs H0.
    + clear H1. right. eapply IHv.
      * simpl. intros. eapply H. simpl. right. eassumption.
      * eapply H0.
Qed.

Lemma proj_relation_fold_None' :
  forall v init proj_vars,
    set_fold_left
      (fun (acc : option (set tup_type)) (elmt : tup_type) =>
         match proj_tuples proj_vars elmt with
         | Some tup => option_map (set_add str_gt_list_ot.eq_dec tup) acc
         | None => None
         end) v (Some init) = None <->
      proj_relation proj_vars v = None.
Proof.
  induction v; split; intros.
  - simpl in H. invs H.
  - simpl in H. invs H.
  - Opaque proj_tuples. simpl in H. destruct (proj_tuples proj_vars a) eqn:A.
    + unfold tup_type in *. eapply IHv in H. simpl.
      rewrite A. eapply IHv. eassumption.
    + simpl. rewrite A. rewrite H. reflexivity.
  - simpl in H. simpl. destruct (proj_tuples proj_vars a) eqn:A.
    + eapply IHv in H. eapply IHv. eassumption.
    + eassumption.
Qed.

Lemma proj_relation_fold_None :
  forall v proj_vars,
    set_fold_left
      (fun (acc : option (set tup_type)) (elmt : tup_type) =>
         match proj_tuples proj_vars elmt with
         | Some tup => option_map (set_add str_gt_list_ot.eq_dec tup) acc
         | None => None
         end) v None = None.
Proof.
  induction v; intros.
  - reflexivity.
  - simpl. destruct (proj_tuples proj_vars a).
    + rewrite IHv. reflexivity.
    + rewrite IHv. reflexivity.
Qed.


Lemma proj_tuples_fold_app :
  forall v v1 init proj_vars,
    set_fold_left
      (fun (acc : option (set tup_type)) (elmt : tup_type) =>
         match proj_tuples proj_vars elmt with
         | Some tup => option_map (set_add str_gt_list_ot.eq_dec tup) acc
         | None => None
         end) v (Some init) = Some v1 ->
    Some v1 = option_map_map (@app (tup_type))
                             (Some init)
                             (proj_relation proj_vars v).
Proof.
  induction v; intros.
  - simpl in H. invs H. simpl. unfold empty_set. rewrite app_nil_r. reflexivity.
  - simpl in H. destruct (proj_tuples proj_vars a) eqn:A.
    + eapply IHv in H.
      simpl. rewrite A.
      destruct_goal_match.
      * eapply IHv in X. replace (Some (init ++ s)) with (option_map_map (app (A:= tup_type)) (Some init) (Some s)) by reflexivity.
        rewrite H. rewrite X.
        Opaque proj_relation.
        simpl.
        destruct (proj_relation proj_vars v) eqn:P.
        -- f_equal. eapply list_set_equality.
           simpl. split; intros.
           ++ eapply in_app_or in H0. eapply in_or_app.
              destruct H0.
              ** eapply set_add_iff in H0. destruct H0; subst.
                 --- right. left; eauto.
                 --- left. eauto.
              ** right. right; eauto.
           ++ eapply in_app_or in H0. eapply in_or_app.
              destruct H0.
              ** left. eapply set_add_iff. right. eassumption.
              ** simpl in H0. destruct H0; subst.
                 --- left. eapply set_add_iff. left. eauto.
                 --- right. eauto.
        -- reflexivity.
      * pose proof (proj_relation_fold_None').
        eapply H0 in X. rewrite X in H. invs H.
    + rewrite proj_relation_fold_None in H. invs H.
Qed.


Lemma proj_relation_monotone :
  forall v v0 v1 v2 proj_vars,
    list_set_subset v v0 ->
    proj_relation proj_vars v = Some v1 ->
    proj_relation proj_vars v0 = Some v2 ->
    list_set_subset v1 v2.
Proof.
  induction v; intros.
  - simpl in H0. invs H0. simpl. intros. invs H2.
  - simpl in H0.
    assert (v0 = a :: v0).
    {
      eapply list_set_equality.
      simpl; split; intros.
      - right. eassumption.
      - destruct H2; subst.
        + eapply H. left; reflexivity.
        + eassumption.
    }
    rewrite H2 in H1. clear H2.
    simpl. intros.
    destruct (proj_tuples proj_vars a) eqn:A.
    + Transparent proj_relation. simpl in H1.
      rewrite A in H1.
      simpl in H0. rewrite A in H0.
      eapply proj_tuples_fold_app in H1. eapply proj_tuples_fold_app in H0.
      assert (list_set_subset v v0).
      {
        simpl. intros.
        eapply H. right. eassumption.
      }
      destruct (proj_relation proj_vars v) eqn:V; destruct (proj_relation proj_vars v0) eqn:V0.
      * specialize (IHv v0 s s0).
        specialize (IHv _ H3 V V0).
        simpl in H0. simpl in H1. invs H0. invs H1. simpl in H2. destruct H2; subst.
        -- left; reflexivity.
        -- right; eauto.
      * simpl in H1. congruence.
      * simpl in H0. congruence.
      * simpl in H0. congruence.
    + simpl in H0. rewrite A in H0.
      rewrite proj_relation_fold_None in H0.
      invs H0.
Qed.

Lemma join_fold_app :
  forall v init join_vars,
    fold_left
      (fun (acc : set tup_type) (elmt : tup_type * tup_type) =>
         let (t1, t2) := elmt in
         match join_tuples join_vars t1 t2 with
         | Some tup => set_add str_gt_list_ot.eq_dec tup acc
         | None => acc
         end) v init =
      init ++ fold_left
           (fun (acc : set tup_type) (elmt : tup_type * tup_type) =>
              let (t1, t2) := elmt in
              match join_tuples join_vars t1 t2 with
              | Some tup => set_add str_gt_list_ot.eq_dec tup acc
              | None => acc
              end) v nil .
Proof.
  induction  v; intros.
  - simpl. rewrite app_nil_r. reflexivity.
  - Opaque join_tuples. simpl. destruct a; destruct (join_tuples join_vars t t0) eqn:J.
    + rewrite IHv. symmetry. rewrite IHv.
      eapply list_set_equality.
      split; intros.
      * eapply in_app_or in H. eapply in_or_app.
        destruct H.
        -- left. eapply set_add_iff. right. eauto.
        -- eapply in_app_or in H. destruct H.
           ++ destruct H; subst; try contradiction.
              left. eapply set_add_iff. left. eauto.
           ++ right. eauto.
      * eapply in_app_or in H. eapply in_or_app.
        destruct H.
        -- eapply set_add_iff in H. destruct H; subst.
           ++ right. eapply in_or_app. left. left; eauto.
           ++ left. eauto.
        -- right. eapply in_or_app. right. eauto.
    + eapply IHv.
Qed.


Lemma join_fold_monotone :
  forall v v' v0 v0' join_vars,
    list_set_subset v v0 ->
    fold_left
      (fun (acc : set tup_type) (elmt : tup_type * tup_type) =>
         let (t1, t2) := elmt in
         match join_tuples join_vars t1 t2 with
         | Some tup => set_add str_gt_list_ot.eq_dec tup acc
         | None => acc
         end) v nil = v' ->
    fold_left
      (fun (acc : set tup_type) (elmt : tup_type * tup_type) =>
         let (t1, t2) := elmt in
         match join_tuples join_vars t1 t2 with
         | Some tup => set_add str_gt_list_ot.eq_dec tup acc
         | None => acc
         end) v0 nil = v0' ->
    list_set_subset v' v0'.
Proof.
  induction v; intros.
  - simpl in H0. subst.
    Opaque join_tuples.
    simpl. intros. contradiction.
  - simpl in H0. destruct a. destruct (join_tuples join_vars t t0) eqn:J.
    + assert (v0 = (t, t0) :: v0).
      {
        eapply list_set_equality.
        simpl; split; intros.
        - right. eauto.
        - destruct H2; subst.
          + eapply H. left; reflexivity.
          + eauto.
      }
      rewrite H2 in H1. clear H2.
      simpl in H1.
      rewrite J in H1.
      rewrite join_fold_app in H1. rewrite join_fold_app in H0. rewrite <- H0. rewrite <- H1.
      simpl. intros. destruct H2.
      * left. eauto.
      * right. eapply IHv.
        simpl. intros. eapply H. right. eassumption.
        reflexivity. reflexivity. eassumption.
    + rewrite <- H0. rewrite <- H1. eapply IHv. simpl. intros. eapply H. right. eauto.
      reflexivity. reflexivity.
Qed.

Print join_relations.

Lemma set_prod_helper {A: Type}  {B: Type} :
  forall (v3: set B) t t0 (a: A),
    In (t, t0) (map (fun y => (a, y)) v3) <->
    t = a /\ In t0 v3.
Proof.
  induction v3; split; intros.
  - invs H.
  - destruct H. invs H0.
  - simpl in H. destruct H.
    + invs H. split; intros.
      * reflexivity.
      * left. reflexivity.
    + eapply IHv3 in H. destruct H. split; eauto.
      right; eauto.
  - destruct H. simpl in H0. subst.
    destruct H0; subst.
    + simpl. left. reflexivity.
    + simpl. right. eapply IHv3. split; eauto.
Qed.

Lemma set_prod_in_iff {A B: Type} :
  forall (v1: set A) (v2: set B) (a: A) (b: B),
    In (a, b) (set_prod v1 v2) <->
      In a v1 /\ In b v2.
Proof.
  induction v1; split; intros.
  - invs H.
  - destruct H. invs H.
  - simpl in H. eapply in_app_iff in H. destruct H.
    + eapply set_prod_helper in H. destruct H; subst.
      split; eauto. left. eauto.
    + eapply IHv1 in H. destruct H. split; eauto.
      right. eauto.
  - simpl in H. destruct H. simpl. eapply in_app_iff.
    destruct H.
    + subst. left. eapply set_prod_helper. split; eauto.
    + right. eapply IHv1. split; eauto.
Qed.

Lemma set_prod_monotone :
  forall (v0 v1 v3 v4: set tup_type),
    list_set_subset v0 v1 ->
    list_set_subset v3 v4 ->
    list_set_subset (set_prod v0 v3) (set_prod v1 v4).
Proof.
  induction v0; intros.
  - simpl. intros. contradiction.
  - simpl. simpl in H.
    assert (list_set_subset v0 v1).
    {
      simpl. intros. eapply H. right. eassumption.
    }
    specialize (IHv0 _ _ _ H1 H0).
    intros. eapply in_app_iff in H2. destruct H2.
    + destruct x. eapply set_prod_helper in H2.
      destruct H2.
      subst. eapply set_prod_in_iff.
      split.
      * eapply H. left. reflexivity.
      * eapply H0. eassumption.
    + destruct x. eapply set_prod_in_iff. eapply set_prod_in_iff in H2.
      destruct H2. simpl in H0. simpl in H1.
      split; eauto.
      * eapply H1. eauto.
      * eapply H0. eauto.
Qed.

Lemma join_relations_monotone :
  forall v0 v1 v3 v4 join_vars,
    list_set_subset v0 v1 ->
    list_set_subset v3 v4 ->
    list_set_subset (join_relations join_vars v0 v3)
                    (join_relations join_vars v1 v4).
Proof.
  induction v0; intros.
  - Opaque join_tuples. simpl.
    intros. contradiction.
  - assert (v1 = a :: v1).
    { eapply list_set_equality.
      simpl; split; intros.
      - right. eassumption.
      - destruct H1; subst.
        + eapply H. left; reflexivity.
        + eauto.
    }
    rewrite H1.
    unfold join_relations.
    eapply join_fold_monotone.
    eapply set_prod_monotone.
    rewrite H1 in H. eapply H. eapply H0. reflexivity. reflexivity.
Qed.






Lemma monotone_op_semantics_monotone :
  forall (m: monotone_ops) (g1 g2: gm_type) (v1 v2: tup_set),
    ground_map_Subset g1 g2 ->
    monotone_op_semantics g1 m v1 ->
    monotone_op_semantics g2 m v2 ->
    list_set_subset v1 v2.
Proof.
  induction m; intros.
  - inversion H0.
  - invs H0.
    invs H1.
    simpl in H. destruct H.
    specialize (H2 _ _ _ H4 H5). simpl.
    intros. eapply assign_vars_to_tuples_monotone. simpl. eapply H2. reflexivity. reflexivity.
    eapply H3.
  - invs H0. invs H1.
    specialize (IHm _ _ _ _ H H7 H8).
    eapply select_relation_monotone. eassumption.
  - invs H0. invs H1.
    specialize (IHm1 _ _ _ _ H H4 H5).
    specialize (IHm2 _ _ _ _ H H6 H8).
    simpl. intros. eapply set_union_iff in H2. eapply set_union_iff.
    destruct H2.
    + left. eapply IHm1. eassumption.
    + right. eapply IHm2. eauto.
  - invs H0. invs H1.
    specialize (IHm _ _ _ _ H H5 H6).
    eapply proj_relation_monotone; eauto.
  - invs H0. invs H1.
    specialize (IHm1 _ _ _ _ H H6 H7).
    specialize (IHm2 _ _ _ _ H H8 H10).
    eapply join_relations_monotone; eauto.
Qed.

(* TODO *)
Lemma rule_semantics_monotone :
  forall (rulez: list (string * rel * monotone_ops)) (g1 g2 g1' g2': gm_type),
    ground_map_Subset g1 g2 ->
    rule_semantics g1 rulez g1' ->
    rule_semantics g2 rulez g2' ->
    ground_map_Subset g1' g2'.
Proof.
  induction rulez; intros.
  - invs H0. invs H1. eassumption.
  - invs H0. invs H1.
    clear H9.
    pose proof (monotone_op_semantics_monotone).
    specialize (H2 _ _ _ _ _ H H5 H10).
    eapply IHrulez. shelve.
    eapply H11.
    eapply H17.
    Unshelve.
    Opaque set_union. simpl. split; intros.
    + pose proof (ground_maps.add_1).
      eapply ground_maps_add_iff.
      eapply ground_maps_add_iff in H3.
      destruct H3; try subst.
      * left. reflexivity.
      * right. eapply H. eassumption.
    + unfold ground_map_Subset in H.
      destruct H.
      eapply ground_maps.find_2 in H3.
      eapply ground_maps.find_2 in H4.

      unfold ground_maps.MapsTo in *. simpl in H3, H4.
      eapply ground_maps_raw_MapsTo_add_iff in H3, H4.
      destruct H3, H4.
      * destruct H3, H4.
        subst.
        eapply set_union_elim in H8. eapply set_union_iff.
        destruct H8.
        admit.
        admit.
      * destruct H4. destruct H3. congruence.
      * destruct H3, H4. congruence.
      * destruct H3, H4.
        eapply H9.
        eapply ground_maps.find_1. eauto. eapply ground_maps.find_1. eauto. eauto.
      * eapply (ground_maps.NoDup g2).
      * eapply (ground_maps.NoDup g1).
Admitted.

(* need equivalent of set_add_iff *)

Lemma rule_semantics_increasing :
  forall (rulez: list (string * rel * monotone_ops)) (g1 g2: gm_type),
    rule_semantics g1 rulez g2 ->
    ground_map_Subset g1 g2.
Proof.
  induction rulez; intros.
  - invs H. simpl. split; intros; eauto.
    rewrite H1 in H0. invs H0. eauto.
  - invs H.
    eapply IHrulez in H9.
    simpl. simpl in H9.
    split; intros.
    + destruct H9.
      eapply H1. unfold ground_maps.In in *. unfold ground_maps.Raw.PX.In in *. destruct H0.
      destruct (String_as_OT.eq_dec x (name R)).
      * subst. exists (set_union List_Ground_Type_as_OTF.eq_dec new_tuples
                            old_tuples).
        simpl. eapply ground_maps_raw_MapsTo_add_iff.
        eapply (ground_maps.NoDup g1).
        left. eauto.
      * exists x0. eapply ground_maps_raw_MapsTo_add_iff.
        eapply (ground_maps.NoDup g1).
        right. split; eauto.
    + destruct (String_as_OT.eq_dec x (name R)).
      * subst.
        destruct H9. eapply H7.
        eapply ground_maps.find_1.
        eapply ground_maps.find_2 in H1, H0.
        unfold ground_maps.MapsTo. eapply ground_maps_raw_MapsTo_add_iff.
        eapply (ground_maps.NoDup g1).
        left. split; reflexivity.
        eauto.
        rewrite <- H5 in H0. invs H0. eapply set_union_iff. right. eauto.
      * destruct H9. eapply H7.
        eapply ground_maps.find_1. unfold ground_maps.MapsTo. simpl. eapply ground_maps_raw_MapsTo_add_iff.
        eapply (ground_maps.NoDup g1).
        right. split; eauto.
        eapply ground_maps.find_2. eauto. eauto.
        eauto.
Qed.

Lemma ground_map_Subset_transitive :
  forall g1 g2 g3,
    ground_map_Subset g1 g2 ->
    ground_map_Subset g2 g3 ->
    ground_map_Subset g1 g3.
Proof.
  intros.
  destruct H as (G1k & G1v). destruct H0 as (G2k & G2v).
  simpl. split; intros.
  - eapply G2k. eapply G1k.
    eauto.
  - eapply ground_maps.find_2 in H, H0.
    unfold ground_maps.In in *. unfold ground_maps.MapsTo in *.
    unfold ground_maps.Raw.PX.In in *.
    assert (exists e, ground_maps.Raw.PX.MapsTo x e (ground_maps.this g1)).
    exists l1. eauto.
    eapply G1k in H2. destruct H2.
    pose proof (ground_maps_MapsTo_det).
    eapply G2v. eapply ground_maps.find_1. eauto. eapply ground_maps.find_1. eauto.
    eapply G1v.
    eapply ground_maps.find_1. eauto. eapply ground_maps.find_1. eauto. eauto.
Qed.

Lemma program_semantics_increasing :
  forall (rulez: list (string * rel * monotone_ops)) (g1 g2: gm_type),
    program_semantics g1 rulez g2 ->
    ground_map_Subset g1 g2.
Proof.
  intros. induction H; intros.
  - simpl. split; intros; eauto.
    rewrite H1 in H2. invs H2. eauto.
  - eapply ground_map_Subset_transitive.
    eapply rule_semantics_increasing; eauto.
    eauto.
Qed.


Lemma ground_maps_eq_refl :
  forall (g: gm_type),
    ground_maps.Equal g g.
Proof.
  intros.
  unfold ground_maps.Equal.
  intros. reflexivity.
Qed.

Lemma monotone_cannot_be_empty :
  forall (m: monotone_ops) v,
    monotone_op_semantics
      (ground_maps.empty _) m v ->
    False.
Proof.
  induction m; intros.
  - invs H.
  - invs H. unfold ground_maps.find in H2. simpl in H2. invs H2.
  - invs H. eapply IHm in H5. contradiction.
  - invs H. eapply IHm1 in H2. contradiction.
  - invs H. eapply IHm in H3. contradiction.
  - invs H. eauto.
Qed.

Lemma rule_semantics_cannot_be_empty :
  forall (rulez: list (string * rel * monotone_ops)) (r: string * rel * monotone_ops) (g: gm_type),
    rule_semantics
      (ground_maps.empty _) (r :: rulez)
      g ->
    False.
Proof.
  induction rulez; intros.
  - invs H. unfold ground_maps.find in H5. unfold ground_maps.Raw.find in H5. simpl in H5. invs H5.
  - invs H.
    invs H. eapply monotone_cannot_be_empty in H8. contradiction.
Qed.

Lemma program_semantics_monotone :
  forall (rulez: list (string * rel * monotone_ops)) (g1 g2 g1' g2': gm_type),
    program_semantics g1 rulez g1' ->
    ground_map_Subset g1 g2 ->
    program_semantics g2 rulez g2' ->
    ground_map_Subset g1' g2'.
Proof.
  intros rulez g1 g2 g1' g2'.
  intros P. revert g2 g2'. induction P; intros.
  - eapply program_semantics_increasing in H2. eapply ground_map_Subset_transitive; eauto.
  - invs H2.
    + eapply ground_maps_equality in H4. subst.
      invs P.
      * eapply ground_maps_equality in H5. subst.
        pose proof (rule_semantics_monotone).
        specialize (H5 _ _ _ _ _ H1 H H3).
        eauto.
      * invs H6. eapply ground_maps_equality in H8. subst.
        eapply rule_semantics_increasing in H4.
        invs H3.
        -- invs H. invs P. invs H8. eassumption.
           invs H8. eapply IHP. eapply H1. eassumption.
        -- pose proof (rule_semantics_monotone).
           specialize (H8 _ _ _ _ _ H1 H H3).
           specialize (IHP _ g'0 H8). eapply IHP in H2. eassumption.
        -- pose proof (rule_semantics_monotone _ _ _ _ _ H1 H H3).
           specialize (IHP _ g'0 H10 H2). eassumption.
    + pose proof (rule_semantics_monotone _ _ _ _ _ H1 H H3).
      specialize (IHP _ g2' H6 H5). eassumption.
Qed.
 
