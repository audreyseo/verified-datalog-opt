From Coq Require Import String List Arith.

From VeriFGH Require Import DatalogProps GroundMaps DatalogSemantics.
Import RelSemantics HelperTactics.



Lemma ground_maps_MapsTo_implies_In :
  forall (g: gm_type) (x: string) (e: list (list ground_types)),
    ground_maps.MapsTo x e g ->
    ground_maps.In x g.
Proof.
  intros. destruct g. unfold ground_maps.MapsTo in H. unfold ground_maps.In. unfold ground_maps.Raw.PX.In. unfold ground_maps.Raw.PX.MapsTo in *. exists e. eassumption.
Qed.

Lemma ground_maps_add_iff :
  forall (g: gm_type) (x x0: string) (l: list (list ground_types)),
    ground_maps.In x (ground_maps.add x0 l g) <->
      x = x0 \/ ground_maps.In x g.
Proof.
  destruct g. rename this into g.
  induction g; split; intros.
  - invs H.
    invs H0.
    + invs H2. simpl in *. subst.
      invs H1. left. reflexivity.
    + invs H2.
  - destruct H.
    + subst. unfold ground_maps.add. simpl. unfold ground_maps.In. simpl. unfold ground_maps.Raw.PX.In.
      exists l. econstructor. reflexivity.
    + unfold ground_maps.In in H. unfold ground_maps.Raw.PX.In in H. destruct H.
      invs H.
  - invs NoDup.
    specialize (IHg H3).
    unfold ground_maps.add in IHg. simpl in IHg. unfold ground_maps.In in IHg. simpl in IHg.
    
    unfold ground_maps.add in H. simpl in H.
    destruct a.
    pose proof (String_as_OT.eq_dec).
    specialize (H0 x0 s).
    destruct H0.
    + subst.
      unfold ground_maps.In in H. simpl in H. destruct (String_as_OT.eq_dec s s).
      * destruct (String_as_OT.eq_dec x s).
        -- left. eauto.
        -- right. unfold ground_maps.In. simpl.
           unfold ground_maps.Raw.PX.In in H. destruct H.
           invs H.
           ++ invs H1. simpl in *. subst. invs H0.
              unfold ground_maps.Raw.PX.In. exists g0. econstructor. reflexivity.
           ++ unfold ground_maps.Raw.PX.In.
              exists x0.
              unfold ground_maps.Raw.PX.MapsTo.
              right. eassumption.
      * congruence.
    + unfold ground_maps.In in H. simpl in H. destruct (String_as_OT.eq_dec x0 s); try congruence.
      unfold ground_maps.Raw.PX.In in H.
      destruct H.
      destruct (string_dec x x0); subst.
      * left. eauto.
      * right. unfold ground_maps.In. simpl. unfold ground_maps.Raw.PX.In.
        invs H.
        -- exists x1. invs H1. simpl in *. invs H0.
           econstructor. reflexivity.
        -- unfold ground_maps.Raw.PX.In in IHg. unfold ground_maps.Raw.PX.MapsTo in IHg. unfold ground_maps.Raw.PX.MapsTo.
           specialize (IHg x x0 l).
           destruct IHg.
           assert (exists e,  SetoidList.InA
                           (ground_maps.Raw.PX.eqke (elt:=list (list ground_types))) (
                             x, e) (ground_maps.Raw.add x0 l g)).
           exists x1. eassumption.
           eapply H0 in H5. destruct H5.
           congruence.
           destruct H5. exists x2. right. eassumption.
  - destruct H.
    + subst. unfold ground_maps.add. simpl. destruct a.
      unfold ground_maps.In. simpl. destruct (String_as_OT.eq_dec x0 s).
      * subst. unfold ground_maps.Raw.PX.In. exists l. econstructor. reflexivity.
      * unfold ground_maps.Raw.PX.In.
        unfold ground_maps.In in IHg. simpl in IHg. unfold ground_maps.Raw.PX.In in IHg.
        unfold ground_maps.Raw.PX.MapsTo in IHg.
        assert (exists e,
                   SetoidList.InA
                     (ground_maps.Raw.PX.eqke (elt:=list (list ground_types)))
                     (x0, e) (ground_maps.Raw.add x0 l g)).
        eapply IHg.  invs NoDup. eauto.
        left. reflexivity.
        destruct H.
        invs H.
        -- destruct y.
           invs H1. simpl in *. invs H2.
           rewrite H0.
           exists l1. right. eassumption.
        -- rewrite H0. destruct y.
           exists x.
           right. rewrite <- H0. right. eauto.
    + unfold ground_maps.In in *.
      simpl in *. destruct a.
      destruct (String_as_OT.eq_dec x0 s).
      * subst. destruct (String_as_OT.eq_dec x s).
        -- subst. unfold ground_maps.Raw.PX.In in *. unfold ground_maps.Raw.PX.MapsTo in *. exists l. left. reflexivity.
        -- unfold ground_maps.Raw.PX.In in *.
           unfold ground_maps.Raw.PX.MapsTo in *.
           destruct H. invs H. invs H1. simpl in *. invs H0. congruence.
           exists x0. right. eassumption.
      * unfold ground_maps.Raw.PX.In in *.
        unfold ground_maps.Raw.PX.MapsTo in *.
        destruct H.
        (* exists x1. *)
        invs H.
        -- invs H1. simpl in *. invs H0. exists l0. left. reflexivity.
        -- assert (exists e,
                      SetoidList.InA (ground_maps.Raw.PX.eqke (elt:=gt_set_type)) (
                                       x, e) g).
           exists x1. eassumption.
           assert (x = x0 \/ exists (e: list (list ground_types)), SetoidList.InA (ground_maps.Raw.PX.eqke (elt:=gt_set_type)) (
                                                                              x, e) g).
           right. eassumption. invs NoDup.
           specialize (IHg H6).
           eapply IHg in H2.
           pose proof (string_dec x s).
           destruct H3.
           ++ subst. exists l0. left. reflexivity.
           ++ destruct H2. exists x2. right. eassumption.
Qed.        


Lemma ground_maps_raw_MapsTo_implies_In :
  forall g x (l3: list (list ground_types)),
  ground_maps.Raw.PX.MapsTo x l3
                            (g) ->
  ground_maps.Raw.PX.In x (g).
Proof.
  intros. unfold ground_maps.Raw.PX.In. exists l3. eassumption.
Qed.

Lemma ground_maps_eqke_inversion :
  forall x0 (x l3: list (list ground_types)) s,
    ground_maps.Raw.PX.eqke (x0, x) (s, l3) ->
    x0 = s /\ x = l3.
Proof.
  intros. invs H. simpl in *. invc H0. split; reflexivity.
Qed.

Lemma ground_maps_raw_MapsTo_cons_iff :
  forall g x0 s (l1 l2: list (list ground_types)),
    ground_maps.Raw.PX.MapsTo x0 l1 ((s, l2) :: g) <->
      (x0 = s /\ l1 = l2) \/ ground_maps.Raw.PX.MapsTo x0 l1 g.
Proof.
  induction g; split; intros.
  - invs H. eapply ground_maps_eqke_inversion in H1. destruct H1; subst.
    left. eauto.
    invs H1.
  - destruct H; try congruence.
    destruct H; subst. econstructor. reflexivity.
    invs H.
  - invs H.
    + eapply ground_maps_eqke_inversion in H1. destruct H1; subst.
      left. eauto.
    + unfold ground_maps.Raw.PX.MapsTo in IHg. destruct a.
      eapply IHg in H1. destruct H1.
      * destruct H0; subst.
        invs H.
        -- eapply ground_maps_eqke_inversion in H1. destruct H1; subst.
           left; eauto.
        -- invs H1.
           ++ right. econstructor. reflexivity.
           ++ right. unfold ground_maps.Raw.PX.MapsTo.
              right. eassumption.
      * right. unfold ground_maps.Raw.PX.MapsTo. right. eassumption.
  - destruct H.
    + destruct H; subst. econstructor. reflexivity.
    + right. destruct a. eapply IHg in H. destruct H; [ destruct H; subst | ].
      * left. reflexivity.
      * right. eapply H.
Qed.

Lemma ground_maps_raw_In_cons_iff :
  forall g x0 s (l3: list (list ground_types)),
    ground_maps.Raw.PX.In x0 ((s, l3) :: g) <->
      x0 = s \/ ground_maps.Raw.PX.In x0 g.
Proof.
  split; intros.
  - unfold ground_maps.Raw.PX.In in H. destruct H.
    eapply ground_maps_raw_MapsTo_cons_iff in H. destruct H.
    + left. eapply H.
    + right. unfold ground_maps.Raw.PX.MapsTo in H. unfold ground_maps.Raw.PX.In. exists x. eapply H.
  - destruct H; subst.
    + unfold ground_maps.Raw.PX.In. exists l3. left. reflexivity.
    + unfold ground_maps.Raw.PX.In in *.
      destruct H. unfold ground_maps.Raw.PX.MapsTo in *.
      exists x. right. eauto.
Qed.

Print ground_maps.MapsTo.
#[local]
 Arguments ground_maps.MapsTo [elt]%type_scope x e m/.
#[local]
 Arguments ground_maps.add [elt]%type_scope x e m /.




Lemma notIn_setoid_cons_subsets :
  forall g x y,
    ~
       SetoidList.InA
         (ground_maps.Raw.PX.eqk (elt:=list (list ground_types))) x
         (y :: g) ->
    ~
       SetoidList.InA
         (ground_maps.Raw.PX.eqk (elt:=list (list ground_types))) x
         (g).
Proof.
  destruct g; intros.
  - unfold not. intros. invs H0.
  - unfold not. intros.
    negate_negated H.
    right. eauto. contradiction.
Qed.
         
Lemma NoDup_setoid_cons_subsets :
  forall g x y,
  SetoidList.NoDupA
         (ground_maps.Raw.PX.eqk (elt:=list (list ground_types)))
         (x :: y :: g) ->
  SetoidList.NoDupA
         (ground_maps.Raw.PX.eqk (elt:=list (list ground_types)))
         (x :: g) /\
    SetoidList.NoDupA
         (ground_maps.Raw.PX.eqk (elt:=list (list ground_types)))
         (y :: g).
Proof.
  induction g; intros.
  - split.
    + econstructor. unfold not; intros. invs H0.
      econstructor.
    + econstructor. unfold not; intros. invs H0. econstructor.
  - invs H.
    split; eauto.
    eapply notIn_setoid_cons_subsets in H2. invs H3. econstructor; eauto.
Qed.
Lemma ground_maps_cons_in_contradiction :
  forall g (v1 l: list (list ground_types)) s,
  SetoidList.InA
         (ground_maps.Raw.PX.eqke (elt:=list (list ground_types))) (
           s, v1) g ->
  SetoidList.NoDupA
            (ground_maps.Raw.PX.eqk (elt:=list (list ground_types)))
            ((s, l) :: g) ->
  False.
Proof.
  induction g; intros.
  - invs H.
  - invs H.
    + destruct a. eapply ground_maps_eqke_inversion in H2. destruct H2; subst.
      invs H0. negate_negated H3.
      left. reflexivity.
      congruence.
    + eapply NoDup_setoid_cons_subsets in H0.
      destruct H0.
      invs H0.
      eapply IHg.  eapply H2. eauto.
Qed.

      

Lemma ground_maps_MapsTo_add_iff :
  forall g x1 x2 (v1 v2: list (list ground_types)),
    ground_maps.MapsTo x1 v1 (ground_maps.add x2 v2 g) <->
      (x1 = x2 /\ v1 = v2) \/ (x1 <> x2 /\ ground_maps.MapsTo x1 v1 g).
Proof.
  destruct g. rename this into g. induction g; split; intros.
  - simpl in H. simpl. invs H. eapply ground_maps_eqke_inversion in H1. left. eauto.
    invs H1.
  - destruct H; try invs H.
    simpl. left. reflexivity.
    invs H1.
  - simpl in H. destruct a.
    simpl. destruct (String_as_OT.eq_dec x2 s).
    + subst. invs H.
      * eapply ground_maps_eqke_inversion in H1. destruct H1; subst.
        left; eauto.
      * destruct (string_dec x1 s).
        -- subst. invs H. eapply ground_maps_eqke_inversion in H2. destruct H2; subst.
           left; eauto.
           (* this is a contradiction, since
              SetoidList.InA
         (ground_maps.Raw.PX.eqke (elt:=list (list ground_types))) (
         s, v1) g
implies that s is a key of g, but
SetoidList.NoDupA
            (ground_maps.Raw.PX.eqk (elt:=list (list ground_types)))
            ((s, l) :: g)
implies that s is not a key of g
            *)
           eapply ground_maps_cons_in_contradiction in H2.
           invs H2. eauto.
        -- right. split; eauto.
    + invs H.
      * eapply ground_maps_eqke_inversion in H1. destruct H1; subst. right. split; try congruence.
        left; eauto.
      * eapply IHg in H1. destruct H1.
        -- destruct H0; subst. left; eauto.
        -- destruct H0. right. split; eauto.
  - simpl. simpl in H. destruct a. destruct (String_as_OT.eq_dec x2 s).
    + subst. destruct H.
      * destruct H; subst. left. reflexivity.
      * destruct H. invs H0.
        -- eapply ground_maps_eqke_inversion in H2. destruct H2; congruence.
        -- right. eauto.
    + destruct H.
      * destruct H; subst. right. eapply IHg. left. eauto.
      * destruct H. invs H0.
        -- eapply ground_maps_eqke_inversion in H2. destruct H2. subst.
           left. reflexivity.
        -- right. eapply IHg. right. eauto.
           Unshelve.
           ++ invs NoDup. eassumption.
           ++ invs NoDup. eassumption.
           ++ invs NoDup. eassumption.
Qed.

Lemma ground_maps_MapsTo_det :
  forall g x (v1 v2: list (list ground_types)),
    ground_maps.MapsTo x v1 g ->
    ground_maps.MapsTo x v2 g ->
    v1 = v2.
Proof.
  destruct g. rename this into g. induction g; intros.
  - invs H.
  - destruct a. invs NoDup. unfold ground_maps.MapsTo in *. simpl in H, H0.
    eapply ground_maps_raw_MapsTo_cons_iff in H, H0.
    destruct H, H0.
    + destruct H. destruct H0. subst. reflexivity.
    +  destruct H. subst. pose proof (ground_maps_cons_in_contradiction).
       specialize (H g v2 l s H0 NoDup).
       contradiction.
    + destruct H0. subst.
      pose proof (ground_maps_cons_in_contradiction g v1 l s H NoDup).
      contradiction.
    + simpl in IHg. eapply IHg; eauto.
Qed.

Lemma ground_maps_raw_MapsTo_add_iff :
  forall g x1 x2 (v1 v2: list (list ground_types)),
    SetoidList.NoDupA
            (ground_maps.Raw.PX.eqk (elt:=list (list ground_types)))
            g ->
    ground_maps.Raw.PX.MapsTo x1 v1
                              (ground_maps.Raw.add x2 v2 g) <->
      (x1 = x2 /\ v1 = v2) \/ (x1 <> x2 /\ ground_maps.Raw.PX.MapsTo x1 v1 g).
Proof.
  pose proof (ground_maps_MapsTo_add_iff).
  unfold ground_maps.MapsTo in H. simpl in H.
  intros.
  specialize (H ({| ground_maps.this := g; ground_maps.NoDup := H0 |})).
  simpl in H. eapply H.
Qed.

(* TODO *)
Lemma ground_maps_raw_cons_add_commute :
  forall g x0 x1 x l1 s g0,
    SetoidList.NoDupA (ground_maps.Raw.PX.eqk (elt:=list (list ground_types)))
                      ((s, g0) :: g) ->
    x <> s ->
    ground_maps.Raw.PX.MapsTo x0 x1
                              ((s, g0) :: ground_maps.Raw.add x l1 g) ->
    ground_maps.Raw.PX.MapsTo x0 x1
                             (ground_maps.Raw.add x l1 ((s, g0) :: g)).
Proof.
Admitted.

(* TODO *)
Lemma setoid_list_eqk_contradiction :
  forall l g0 s l1,
  SetoidList.InA
         (ground_maps.Raw.PX.eqk (elt:=list (list ground_types))) (
         s, l1) (l) ->
  SetoidList.NoDupA (ground_maps.Raw.PX.eqk (elt:=gt_set_type))
         (l) ->
  ~
       SetoidList.InA (ground_maps.Raw.PX.eqk (elt:=gt_set_type)) (
         s, g0) (l) ->
  False.
Proof.
Admitted.

Lemma ground_maps_raw_MapsTo_eq_cons :
  forall g l0 l1 s,
     SetoidList.NoDupA (ground_maps.Raw.PX.eqk (elt:=list (list ground_types)))
                      ((s, l1) :: g) ->
     ground_maps.Raw.PX.MapsTo s l0 ((s, l1) :: g) ->
     l0 = l1.
Proof.
  intros. eapply ground_maps_raw_MapsTo_cons_iff in H0. destruct H0.
  - destruct H0. eauto.
  - unfold ground_maps.Raw.PX.MapsTo in *. pose proof (ground_maps_cons_in_contradiction).
    specialize (H1 _ _ _ _ H0 H). contradiction.
Qed.

Lemma eqke_implies_eqk :
  forall g s l0,
  SetoidList.InA
         (ground_maps.Raw.PX.eqke (elt:=list (list ground_types))) (
           s, l0) g ->
  SetoidList.InA
         (ground_maps.Raw.PX.eqk (elt:=list (list ground_types))) (
           s, l0) g.
Proof.
  induction g; intros.
  - invs H.
  - destruct a. invs H.
    + eapply ground_maps_eqke_inversion in H1. destruct H1. subst.
      left. reflexivity.
    + right. eapply IHg. eauto.
Qed.

Lemma eqk_implies_not_NoDup :
  forall g x y,
  ground_maps.Raw.PX.eqk x y ->
  ~ SetoidList.NoDupA
         (ground_maps.Raw.PX.eqk (elt:=list (list ground_types)))
         (x :: y :: g).
Proof. intros. unfold not. intros.
 Admitted.
(* induction g; intros.
- unfold not. intros. invs H0. unfold not in H3.
Proof.
  induction g; intros.
  - split.
    + econstructor. unfold not; intros. invs H0.
      econstructor.
    + econstructor. unfold not; intros. invs H0. econstructor.
  - invs H.
    split; eauto.
    eapply notIn_setoid_cons_subsets in H2. invs H3. econstructor; eauto.
Qed.
  *)

(* TODO *)
Lemma setoid_list_NoDup_eqk_fst :
  forall g s l1 l2,
  SetoidList.NoDupA
    (ground_maps.Raw.PX.eqk (elt:=list (list ground_types)))
    ((s, l1) :: g) ->
  SetoidList.NoDupA
    (ground_maps.Raw.PX.eqk (elt:=list (list ground_types)))
    ((s, l2) :: g).
Proof.
induction g; intros.
- econstructor. unfold not. intros. invs H0. econstructor.
- econstructor. unfold not. intros. invs H0. 
(* This NoDup lemma seems to be going the wrong direction *)
(* but it's the only way I see to apply the inductive hypothesis  *)
pose proof (NoDup_setoid_cons_subsets _ _ _ H). destruct H1.
apply IHg with (l2:=l2) in H1. apply eqk_implies_not_NoDup with (g:=g) in H2.
(* Now it would be nice to go the other way back *)
(* The inverse of the NoDup lemma is true iff x != y *)
(* And here, x = y *)


Admitted.
    
Lemma ground_maps_add_Subset  :
  forall (g1 g2: gm_type) (l1 l2: list (list ground_types)) x,
    ground_map_Subset g1 g2 ->
    list_set_subset l1 l2 ->
    ground_map_Subset (ground_maps.add x l1 g1) (ground_maps.add x l2 g2).
Proof.
  destruct g1. rename this into g. split.
  - revert H0. revert H. revert x. revert l1 l2. revert g2. induction g; intros.
    + unfold ground_maps.In in *.
      unfold ground_maps.Raw.PX.In in *.
      destruct H1. simpl in H1. eapply ground_maps_raw_MapsTo_cons_iff in H1.
      destruct H1; subst.
      * destruct H1. subst. exists l2. eapply ground_maps_MapsTo_add_iff. left. eauto.
      * invs H1.
    + unfold ground_maps.In in *. simpl in *.
      destruct a.
      destruct (String_as_OT.eq_dec x s).
      * subst. unfold ground_maps.Raw.PX.In in H1.
        destruct H1. eapply ground_maps_raw_MapsTo_cons_iff in H1.
        destruct H1; subst.
        -- destruct H1; subst.
           unfold ground_maps.Raw.PX.In. exists l2. eapply ground_maps_raw_MapsTo_add_iff. eapply (ground_maps.NoDup g2). left. eauto.
        -- unfold ground_maps.Raw.PX.MapsTo in H1.
           destruct (String_as_OT.eq_dec x0 s).
           ++ subst. pose proof (ground_maps_cons_in_contradiction _ _ _ _ H1 NoDup). contradiction.
           ++ pose proof (ground_maps_add_iff).
              unfold ground_maps.In in H2. unfold ground_maps.add in H2. simpl in H2. destruct H.
              eapply IHg.
              ** split.
                 --- intros.
                     eapply H. unfold ground_maps.In in *. simpl. unfold ground_maps.Raw.PX.In in *. simpl in H4.
                     destruct H4. exists x2. right. eauto.
                 --- intros. eapply H3.
                     eapply ground_maps.find_1. unfold ground_maps.MapsTo.
                     eapply ground_maps.find_2 in H4.
                     unfold ground_maps.MapsTo in H4. simpl in H4. right. eauto.
                     eauto. eauto.
              ** intros. eauto.
              ** unfold ground_maps.Raw.PX.In. exists x. eapply ground_maps_raw_MapsTo_add_iff. invs NoDup. eapply H7. right. split; eauto.
      * unfold ground_maps.Raw.PX.In in *.
        destruct H. unfold ground_maps.In in H. unfold ground_maps.Raw.PX.In in H.
        pose proof (ground_maps_raw_cons_add_commute).
        destruct H1.
        specialize (H3 _ _ _ _ _ _ _ NoDup n H1).
        eapply ground_maps_raw_MapsTo_add_iff in H3.
        destruct H3.
        -- destruct H3; subst. exists l2. eapply ground_maps_raw_MapsTo_add_iff. eapply (ground_maps.NoDup g2).
           left. eauto.
        -- destruct H3. assert (exists e, ground_maps.Raw.PX.MapsTo x0 e ((s, l) :: g)).
           simpl in H.
           exists x1. eauto.
           eapply H in H5. destruct H5. exists x2.
           eapply ground_maps_raw_MapsTo_add_iff. eapply (ground_maps.NoDup g2). right. split; eauto.
        -- eauto.
  - revert H0. revert H. revert x. revert l1 l2 g2. induction g; intros.
    + simpl in *. unfold ground_maps.find in *.
      eapply ground_maps.find_2 in H1, H2.
      destruct H.
      unfold ground_maps.MapsTo in *. simpl in *.
      eapply ground_maps_raw_MapsTo_cons_iff in H1. destruct H1; try invs H1.
      intros.
      eapply ground_maps_raw_MapsTo_add_iff in H2. destruct H2.
      destruct H2; subst. eapply H0. eauto.
      destruct H2. congruence.
      eapply (ground_maps.NoDup g2).
    + pose proof (ground_maps.NoDup g2).
      invs NoDup. destruct H.
      eapply ground_maps.find_2 in H1.
      destruct a.
      destruct (String_as_OT.eq_dec x s).
      * subst.
        unfold ground_maps.MapsTo in *. eapply ground_maps.find_2 in H2.
        unfold ground_maps.add in *. simpl in *.
        destruct (String_as_OT.eq_dec s s); try congruence.
        destruct (String_as_OT.eq_dec x0 s).
        subst.
        eapply ground_maps_raw_MapsTo_eq_cons in H1. subst.
        eapply ground_maps_raw_MapsTo_add_iff in H2. destruct H2.
        -- destruct H1. subst. eauto.
        -- destruct H1. congruence.
        -- eauto.
        -- eapply setoid_list_NoDup_eqk_fst. eauto.
        -- pose proof (ground_maps.add_3).
           unfold ground_maps.MapsTo in H5.
           specialize (H5 _ g2).
           unfold ground_maps.add in H5. simpl in H5.
           assert (s <> x0) by congruence.
           specialize (H5 _ _ l3 l2 H8).
           specialize (H5 H2).
           assert (ground_maps.Raw.PX.MapsTo x0 l0 (ground_maps.Raw.add s l1 g)).
           eapply ground_maps_raw_MapsTo_add_iff.
           eauto.
           invs H1.
           eapply ground_maps_eqke_inversion in H10. destruct H10. congruence.
           right. split; eauto.
           eapply IHg.
           ++ split; intros.
              ** eapply H. unfold ground_maps.In in *. unfold ground_maps.Raw.PX.In in *.
                 destruct H10. exists x1. right. eauto.
              ** eapply H4. eapply ground_maps.find_1.
                 unfold ground_maps.MapsTo. simpl.
                 eapply ground_maps.find_2 in H10. unfold ground_maps.MapsTo in H10. simpl in H10.
                 right. eapply H10.
                 eauto.
                 eauto.
           ++ eauto.
           ++ eapply ground_maps.find_1. eauto.
           ++ eapply ground_maps.find_1. unfold ground_maps.MapsTo.
              simpl. eauto.
      * destruct (String_as_OT.eq_dec x0 x).
        -- subst. unfold ground_maps.MapsTo in H1. simpl in H1. destruct (String_as_OT.eq_dec x s); try congruence.
           eapply ground_maps_raw_cons_add_commute in H1.
           pose proof (ground_maps_raw_MapsTo_add_iff).
           specialize (H5 ((s, g0) :: g) x x l0 l1 NoDup).
           destruct H5. specialize (H5 H1).
           destruct H5.
           ++ destruct H5. subst.
              eapply IHg.
              ** split; intros.
                 --- eapply H. unfold ground_maps.In in *. unfold ground_maps.Raw.PX.In in *. destruct H9.
                     destruct (String_as_OT.eq_dec x0 s).
                     +++ subst. exists g0. simpl. eapply ground_maps_raw_MapsTo_cons_iff. left. eauto.
                     +++ exists x1. right. eauto.
                 --- eapply ground_maps.find_2 in H9.
                     eapply ground_maps.find_2 in H10.
                     unfold ground_maps.MapsTo in *.
                     simpl in H9.
                     eapply H4.
                     eapply ground_maps.find_1. unfold ground_maps.MapsTo. right. eauto.
                     eapply ground_maps.find_1. eauto.
              ** eauto.
              ** eapply ground_maps.find_1.
                 eapply ground_maps.add_1. reflexivity.
              ** eauto.
           ++ destruct H5. congruence.
           ++ eauto.
           ++ eauto.
        -- eapply H4.
           ++ eapply ground_maps.find_1. unfold ground_maps.MapsTo in *. unfold ground_maps.add in *. simpl in *.
              destruct (String_as_OT.eq_dec x s); try congruence.
              eapply ground_maps_raw_MapsTo_cons_iff in H1.
              destruct H1; subst.
              ** destruct H1. subst.
                 eapply ground_maps_raw_MapsTo_cons_iff. left. split; reflexivity.
              ** eapply ground_maps_raw_MapsTo_add_iff in H1.
                 destruct H1.
                 destruct H1. congruence.
                 destruct H1. right. eauto.
                 eauto.
           ++ eapply ground_maps.find_2 in H2.
              eapply ground_maps_raw_MapsTo_add_iff in H2. destruct H2.
              destruct H2. congruence.
              destruct H2. eapply ground_maps.find_1. eauto.
              eauto.
              Unshelve.
              invs NoDup. eauto.
              invs NoDup. eauto.
              invs NoDup. eauto.
Qed.
