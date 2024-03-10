From Coq Require Import List String Arith Psatz Lists.ListSet Logic.Classical_Prop.

From VeriFGH Require Import DatalogProps DatalogSemantics GroundMaps MonotonicityTheorems GroundMapsHelpers HelperTactics OrderedGroundTypes.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.


Import RelSemantics.

Inductive check_join_vars_rel : list string -> tup_type -> tup_type ->
                                Prop :=
| check_join_vars_nil :
  forall t1 t2,
    check_join_vars_rel nil t1 t2
| check_join_vars_cons :
  forall jvs j t1 t2 v1 v2,
    check_join_vars_rel jvs t1 t2 ->
    assoc_lookup_rel t1 j v1 ->
    assoc_lookup_rel t2 j v2 ->
    v1 = v2 ->
    check_join_vars_rel (j :: jvs) t1 t2.

Lemma fold_left_false:
forall jvs t1 t2,
fold_left
      (fun (acc : bool) (elmt : string) =>
       if acc
       then
        match assoc_lookup t1 elmt with
        | Some g1 =>
            match assoc_lookup t2 elmt with
            | Some g2 =>
                if Ground_Types_as_OTF.eq_dec g1 g2
                then true
                else false
            | None => false
            end
        | None => false
        end
       else false) jvs false = false.
Proof.
  induction jvs. simpl; intros; eauto. 
  simpl; eauto.
Qed.

(* TODO *)
Lemma check_join_vars_adequacy :
  forall (jvs: list string) (t1 t2: tup_type),
    check_join_vars_rel jvs t1 t2 <->
      check_join_vars jvs t1 t2 = true.
Proof.
  induction jvs; intros; split; intro.
  - unfold check_join_vars. simpl; eauto.
  - econstructor.
  - inversion H; subst. unfold check_join_vars; simpl. 
    specialize (IHjvs t1 t2). destruct IHjvs. specialize (H0 H2).
    specialize (assoc_lookup_adequacy t1 a v2). intro. destruct H5.
    specialize (H5 H3). rewrite <- H5. 
    specialize (assoc_lookup_adequacy t2 a v2). intro. destruct H7.
    specialize (H7 H4). rewrite <- H7.
    destruct (Ground_Types_as_OTF.eq_dec v2 v2).
    eauto. destruct n; eauto.
  - unfold check_join_vars in H. simpl in H. 
    specialize (IHjvs t1 t2). destruct IHjvs.
    remember (match assoc_lookup t1 a with
    | Some g1 =>
        match assoc_lookup t2 a with
        | Some g2 =>
            if Ground_Types_as_OTF.eq_dec g1 g2
            then true
            else false
        | None => false
        end
    | None => false
    end ).
    remember (assoc_lookup t1 a).
    remember (assoc_lookup t2 a).
    destruct b; destruct o; destruct o0. 
    + econstructor.
      eapply H1. eauto. eapply assoc_lookup_adequacy. exact Heqo.
      eapply assoc_lookup_adequacy. exact Heqo0.
      destruct (Ground_Types_as_OTF.eq_dec g g0); eauto.
      inversion Heqb.
    + inversion Heqb.
    + inversion Heqb.
    + inversion Heqb.
    + erewrite fold_left_false in H. inversion H.
    + erewrite fold_left_false in H. inversion H.
    + erewrite fold_left_false in H. inversion H.
    + erewrite fold_left_false in H. inversion H.
Qed.


Inductive get_vars_set_rel : tup_type -> string_sets.t -> Prop :=
| get_vars_assoc_empty :
    get_vars_set_rel nil string_sets.empty
| get_vars_assoc_cons :
  forall (assoc: tup_type) (s: string) (g: ground_types) (ss: string_sets.t),
    get_vars_set_rel assoc ss ->
    get_vars_set_rel ((s, g) :: assoc) (string_sets.add s ss).

(* Not used as of Mar 8, so not necessary *)
Lemma get_vars_set_adequacy :
  forall (assoc: tup_type) (ss: string_sets.t),
    get_vars_set_rel assoc ss <->
      ss = get_vars_set assoc.
Proof.
Admitted.


Inductive select_tuples_rel : string -> ground_types -> tup_type -> Prop :=
| select_tuples_end :
  forall n v1 t,
    ~ In n (map fst t) ->
    select_tuples_rel n v1 ((n, v1) :: t)
| select_tuples_continue :
  forall n1 n2 v1 v2 t,
    select_tuples_rel n1 v1 t ->
    n1 <> n2 ->
    select_tuples_rel n1 v1 ((n2, v2) :: t).

Inductive assoc_keys_NoDup : tup_type -> Prop :=
| assoc_keys_NoDup_nil :
  assoc_keys_NoDup nil
| assoc_keys_NoDup_cons :
  forall (s: string) (g: ground_types) (t: tup_type),
    ~ In s (map fst t) ->
    assoc_keys_NoDup t ->
    assoc_keys_NoDup ((s, g) :: t).

Lemma select_tuples_rest :
  forall (assoc: tup_type) (s: string) (g: ground_types) (init: tup_type),
    ~ In s (map fst assoc) ->
    fold_left
    (fun (acc : option (list (string * ground_types)))
       (elmt : string * ground_types) =>
     let (n', g0) := elmt in
     if string_dec s n'
     then
      if OrderedGroundTypes.Ground_Types_as_OTF.eq_dec g g0
      then option_map (cons elmt) acc
      else None
     else option_map (cons elmt) acc) assoc (Some init) = Some ((rev assoc) ++ init).
Proof.
  induction assoc; intros; simpl.
  - reflexivity.
  - destruct a.
    destruct (string_dec s s0).
    + simpl in H. negate_negated H.
      left. congruence.
      congruence.
    + assert (~ In s (map fst assoc)).
      {
        unfold not. intros. negate_negated H.
        right. eauto. congruence.
      }
      erewrite IHassoc; eauto.
      f_equal.
      rewrite <- app_assoc. simpl. reflexivity.
Qed.

(* Used in the select_tuples_adequacy proof that is commented out,
 * I think we ended up not using selects in the example so it's not 
 * strictly necessary.  *)
Lemma select_tuples_fold_None :
  forall (assoc: tup_type) (s0: string) (g: ground_types),
    fold_left
    (fun (acc : option (list (string * ground_types)))
       (elmt : string * ground_types) =>
     let (n', g1) := elmt in
     if string_dec s0 n'
     then
      if OrderedGroundTypes.Ground_Types_as_OTF.eq_dec g g1
      then option_map (cons elmt) acc
      else None
     else option_map (cons elmt) acc) assoc None = None.
Proof.
  induction assoc; intros.
Admitted.

(* Not strictly necessary *)
Lemma select_tuples_adequacy :
  forall (assoc: tup_type) (s: string) (g: ground_types),
    assoc <> nil ->
    assoc_keys_NoDup assoc ->
    select_tuples_rel s g assoc <->
      select_tuples s g assoc = Some (rev assoc).
Proof.
  (* split. *)
  (* - intros S. *)
  (*   revert H0 H. induction S; intros. *)
  (*   + simpl. destruct (string_dec n n); try congruence. *)
  (*     Ltac destruct_fold_left_if_init := *)
  (*       match goal with *)
  (*       | [ |- context G [fold_left _ _ (if ?a then _ else _)]] => *)
  (*           let A := fresh "A" in *)
  (*           destruct a eqn:A; *)
  (*           try congruence *)
  (*       end. *)
  (*     destruct_fold_left_if_init. *)
  (*     rewrite select_tuples_rest. f_equal. invs H0. eauto. *)
  (*   + simpl. *)
  (*     destruct_fold_left_if_init. *)
  (*     invs H0. *)
      
  (*     destruct t. *)
  (*     * simpl. reflexivity. *)
  (*     * eapply IHS in H6; try congruence. *)
  (*       simpl in H6. destruct p. *)
  (*       destruct (string_dec n1 s); try progress destruct ( OrderedGroundTypes.Ground_Types_as_OTF.eq_dec v1 g). *)
  (*       subst. *)
  (*       invs H0. invs H8. specialize (IHS H8). *)
  (*       simpl. destruct_fold_left_if_init. destruct_fold_left_if_init. *)
  (*       rewrite select_tuples_rest. f_equal. rewrite <- app_assoc. simpl. reflexivity. *)
  (*       eauto. *)
  (*       rewrite select_tuples_fold_None in H6. congruence. *)
  (*       invs H0. invs H8. *)
  (*       simpl. *)
  (*       simpl. destruct_fold_left_if_init; try destruct_fold_left_if_init. *)
  (*       erewrite IHS. *)
  (*       rewrite select_tuples_rest. f_equal. rewrite <- app_assoc. reflexivity. *)
        
  (*       rewrite select_tuples_rest in H6. *)
  (*       subst. *)
        
                             

  
  (* induction assoc; split; intros. *)
  (* - congruence. *)
  (* - congruence. *)
  (* - invs H1. *)
  (*   + simpl. destruct (string_dec s s); try congruence. *)
  (*     destruct (OrderedGroundTypes.Ground_Types_as_OTF.eq_dec g g); try congruence. *)
  (*     rewrite select_tuples_rest. *)
  (*     reflexivity. *)
  (*     invs H0. eauto. *)
  (*   + simpl. destruct (string_dec s n2); try congruence. *)
  (*     destruct assoc. invs H6. *)
  (*     eapply IHassoc in H6; try congruence. *)
  (*     * simpl. destruct p. destruct (string_dec s s0); try destruct (OrderedGroundTypes.Ground_Types_as_OTF.eq_dec g g0). *)
  (*       -- subst. rewrite select_tuples_rest. *)
  (*          ++ f_equal. rewrite <- app_assoc. simpl. reflexivity. *)
  (*          ++ invs H0. invs H8. *)
  (*             eassumption. *)
  (*       -- subst. invs H1. *)
  (*          invs H0. *)
  (*          simpl in H4. negate_negated H4. *)
  (*          left. eauto. congruence. *)
  (*          simpl in H6. *)
  (*          destruct (string_dec s0 s0); try congruence. *)
  (*          destruct (OrderedGroundTypes.Ground_Types_as_OTF.eq_dec g g0); try congruence. *)
  (*          rewrite select_tuples_fold_None in H6. congruence. *)
  (*       -- invs H1. *)
           
           
           
  (*     rewrite select_tuples_rest. reflexivity. *)
      
Admitted.


Inductive join_tuples_rel_helper : list string -> list string -> list string -> tup_type -> tup_type -> tup_type -> tup_type -> tup_type -> Prop :=
| join_tuples_rel_end :
  join_tuples_rel_helper nil nil nil nil nil nil nil nil
| join_tuples_step_left :
  forall (lvs jvs rvs: list string) (assoc1 assoc2 : tup_type) (lft join rght: tup_type) a1 a2,
    assoc_lookup_rel assoc1 a1 a2 ->
    join_tuples_rel_helper lvs jvs rvs assoc1 assoc2 lft join rght ->
    join_tuples_rel_helper (a1 :: lvs) jvs rvs assoc1 assoc2 ((a1, a2) :: lft) join rght
| join_tuples_step_join :
  forall (jvs rvs: list string) (assoc1 assoc2: tup_type) (lft join rght: tup_type) j1 j2,
    assoc_lookup_rel assoc1 j1 j2 ->
    assoc_lookup_rel assoc2 j1 j2 ->
    join_tuples_rel_helper nil jvs rvs assoc1 assoc2 lft join rght ->
    join_tuples_rel_helper nil (j1 :: jvs) rvs assoc1 assoc2 lft ((j1, j2) :: join) rght
| join_tuples_step_right :
  forall (rvs: list string) (assoc1 assoc2: tup_type) (lft join rght: tup_type) r1 r2,
    assoc_lookup_rel assoc2 r1 r2 ->
    join_tuples_rel_helper nil nil rvs assoc1 assoc2 lft join rght ->
    join_tuples_rel_helper nil nil (r1 :: rvs) assoc1 assoc2 lft join ((r1, r2) :: rght).


Require Import Program.Equality.

Section JoinTuplesAdequate.
  Hypothesis (jvs: list string).
  Hypothesis (assoc1 assoc2: tup_type).
  Hypothesis (NonNil : jvs <> nil).
  Let jv_set := list_to_string_set jvs.
  Let assoc1_vars := string_sets.diff (get_vars_set assoc1) jv_set.
  Let assoc2_vars := string_sets.diff (get_vars_set assoc2) jv_set.

  (* Not necessary *)
  Lemma join_tuples_adequacy_forward :
    forall (l j r: tup_type),
      join_tuples_rel_helper (string_sets.this assoc1_vars) (string_sets.this jv_set) (string_sets.this assoc2_vars) assoc1 assoc2 l j r ->
      join_tuples jvs assoc1 assoc2 = Some (rev l ++ rev j ++ rev r).
  Proof.
    intros l j r J.
    dependent induction J.
    - unfold jv_set in x1. unfold list_to_string_set in x1. destruct jvs.
      + congruence.
      + admit.
    - specialize (IHJ NonNil).
      destruct (string_sets.this assoc1_vars).
      + invs x.
      + invs x.
        

    (*   simpl. unfold check_join_vars. simpl. *)
    (*   enough (F : fold_left *)
    (*   (fun (acc : bool) (_ : string) => if acc then false else false) jvs *)
    (*   true = false). *)
    (*   rewrite F.  *)
      
    (* destruct jv_set. induction this; intros. *)
    (* - assert (assoc1_vars = (get_vars_set assoc1)). *)
    (*   { *)
    (*     unfold assoc1_vars. eapply string_sets_equality. *)
    (*     unfold string_sets.Equal. split; intros. *)
    (*     - eapply string_sets.diff_spec in H0. destruct H0. eauto. *)
    (*     - eapply string_sets.diff_spec. split. *)
    (*       + eauto. *)
    (*       + unfold not. intros. invs H1. *)
    (*   } *)
    (*   assert (assoc2_vars = (get_vars_set assoc2)). *)
    (*   { *)
    (*     unfold assoc1_ *)
        (* induction jvs; intros. *)
  Admitted.
End JoinTuplesAdequate.
   
                      
(*                           jvs          left       right      parts of left joined parts of right *)
(* Inductive join_tuples_rel : list string -> tup_type -> tup_type -> tup_type -> tup_type -> tup_type -> Prop := *)
(* | join_tuples_end : *)
(*   join_tuples_rel nil nil nil nil nil nil *)
(* | join_tuples_left : *)
(*   forall (jvs: list string) (t1 t2: tup_type) (ls: string) (lg: ground_types) (lft join right: tup_type), *)

Fixpoint all_vars_present (vars: list string) (assoc: tup_type): bool :=
  match vars with
  | nil => true
  | hd :: tl =>
      match assoc_lookup assoc hd with
      | Some _ => all_vars_present tl assoc
      | None => false
      end
  end.

Inductive all_vars_present_rel : list string -> tup_type -> Prop :=

| all_vars_present_nil :
  forall assoc,
    all_vars_present_rel nil assoc
| all_vars_present_cons :
  forall vars assoc a b,
    assoc_lookup_rel assoc a b ->
    all_vars_present_rel vars assoc ->
    all_vars_present_rel (a :: vars) assoc.

Lemma all_vars_present_adequacy :
  forall (vars: list string) (assoc: tup_type),
    all_vars_present_rel vars assoc <->
      all_vars_present vars assoc = true.
Proof.
  split.
  - intros. induction H.
    + reflexivity.
    + simpl. rewrite IHall_vars_present_rel.
      eapply assoc_lookup_adequacy in H. rewrite <- H.
      reflexivity.
  - revert assoc. induction vars; intros.
    + econstructor.
    + simpl in H. destruct (assoc_lookup assoc a) eqn:A.
      * eapply IHvars in H. econstructor. eapply assoc_lookup_adequacy. symmetry. eauto.
        eauto.
      * congruence.
Qed.
      
Definition join_tuples_left (jvs: list string) (assoc1: tup_type): option tup_type :=
  if all_vars_present jvs assoc1 then
    let jv_set := list_to_string_set jvs in
    let assoc1_vars := string_sets.diff (get_vars_set assoc1) jv_set in
    string_sets.fold (fun elmt acc =>
                        match assoc_lookup assoc1 elmt with
                        | Some g =>
                            option_map (cons (elmt, g)) acc
                        | None => None
                        end)
                     assoc1_vars
                     (Some nil)
  else None.

Definition join_tuples_right (jvs: list string) (assoc2: tup_type): option tup_type :=
  if all_vars_present jvs assoc2 then
    let jv_set := list_to_string_set jvs in
    let assoc2_vars := string_sets.diff (get_vars_set assoc2) jv_set in
    string_sets.fold (fun elmt acc =>
                        match assoc_lookup assoc2 elmt with
                        | Some g =>
                            option_map (cons (elmt, g)) acc
                        | None => None
                        end)
                     assoc2_vars
                     (Some nil)
  else None.

Definition join_tuples_joined (jvs: list string) (assoc1 assoc2: tup_type): option tup_type :=
  if check_join_vars jvs assoc1 assoc2 then
    let jv_set := list_to_string_set jvs in
     string_sets.fold (fun elmt acc =>
                            match assoc_lookup assoc1 elmt with
                            | Some g =>
                                option_map (cons (elmt, g)) acc
                            | None => None
                            end)
                         jv_set
                         (Some nil)
  else None.

Lemma check_join_vars_implies_all_vars_present :
  forall (jvs: list string) (assoc1 assoc2: tup_type),
    check_join_vars_rel jvs assoc1 assoc2 ->
    all_vars_present_rel jvs assoc1 /\ all_vars_present_rel jvs assoc2.
Proof.
  induction jvs; intros.
  - split; econstructor.
  - invs H.
    split; eauto.
    + econstructor. eauto. eapply IHjvs with (assoc2 := assoc2).
      eauto.
    + econstructor. eauto. eapply IHjvs. eauto.
Qed.

Lemma join_tuples_is_join_parts :
  forall (jvs: list string) (assoc1 assoc2: tup_type),
    join_tuples jvs assoc1 assoc2 =
      match join_tuples_left jvs assoc1, join_tuples_joined jvs assoc1 assoc2, join_tuples_right jvs assoc2 with
      | Some lft, Some join, Some rght => Some (lft ++ join ++ rght)
      | _, _, _ => None
      end.
Proof.
  intros.
  simpl. unfold join_tuples_left. unfold join_tuples_joined. unfold join_tuples_right.
  destruct (check_join_vars jvs assoc1 assoc2) eqn:C.
  eapply check_join_vars_adequacy in C. eapply check_join_vars_implies_all_vars_present in C. destruct C as (C1 & C2).
  eapply all_vars_present_adequacy in C1, C2.
  
  destruct_any_match_in_goal.
  destruct_any_match_in_goal.
  destruct_any_match_in_goal.
  rewrite C1. rewrite C2. reflexivity.
  rewrite C1. rewrite C2. reflexivity.
  rewrite C1. reflexivity.
  rewrite C1. reflexivity.
  destruct (all_vars_present jvs assoc1).
  - destruct_any_match_in_goal.
  - reflexivity.
Qed.
    

Module Type FoldableType.
  Parameter Inline t: Type.
  Parameter elmt: Type.
  Parameter elmt_eq_dec : forall (e1 e2: elmt), { e1 = e2 } + {e1 <> e2}.
  Parameter empty: t.
  Parameter add: elmt -> t -> t.
  Parameter In: elmt -> t -> Prop.
  Parameter fold_left: forall (A: Type), (A -> elmt -> A) -> t -> A -> A.
  Print fold_left.
  Arguments fold_left {A}%type_scope _%function_scope _ _ /.
  
  Definition Subset (s1 s2: t): Prop :=
    forall (x: elmt),
      In x s1 ->
      In x s2.
  Arguments Subset s1 s2/.
  
  Definition Equal (s1 s2: t) : Prop :=
    Subset s1 s2 /\ Subset s2 s1.

  Arguments Equal s1 s2 /.
  Inductive Fold_Left {A: Type} : (A -> elmt -> A) -> t -> A -> A -> Prop :=
  | Fold_Left_nil :
    forall (f: A -> elmt -> A) (init: A),
      Fold_Left f empty init init
  | Fold_Left_add :
    forall (f: A -> elmt -> A) (init: A) (res: A) (s: t) (e: elmt),
      Fold_Left f s (f init e) res ->
      Fold_Left f (add e s) init res.

  (* Parameter fold_left_spec : *)
  (*   forall (A: Type) (f: A -> elmt -> A) (s: t) (init res: A), *)
  (*     Fold_Left f s init res <-> *)
  (*       fold_left f s init = res. *)

  Definition monotonic {A B: Type} (f: A -> B) (le__A: A -> A -> Prop) (le__B: B -> B -> Prop) :=
    forall (a1 a2: A) (b1 b2: B),
      le__A a1 a2 ->
      f a1 = b1 ->
      f a2 = b2 ->
      le__B b1 b2.

  Definition monotonic2 {A B C: Type} (f: A -> B -> C) (le__A: A -> A -> Prop) (le__B: B -> B -> Prop) (le__C: C -> C -> Prop) :=
    forall (a1 a2: A) (b1 b2: B) (c1 c2: C),
      le__A a1 a2 ->
      le__B b1 b2 ->
      f a1 b1 = c1 ->
      f a2 b2 = c2 ->
      le__C c1 c2.

  Definition increasing {A B: Type} (f: A -> B -> A) (le__A : A -> A -> Prop) :=
    forall (a1 a2: A) (b: B),
      f a1 b = a2 ->
      le__A a1 a2.
      

  Parameter le__elmt : elmt -> elmt -> Prop.


  (* Parameter fold_left_monotonic : forall  {A: Type} (f: A -> elmt -> A) (le__A: A -> A -> Prop) (lt__A: A -> A -> Prop) (eq__A: A -> A -> Prop), *)
  (*   forall (le_lteq__A: forall (a1 a2: A), *)
  (*         le__A a1 a2 <-> lt__A a1 a2 \/ eq__A a1 a2), *)
  (*   forall (eq_spec__A: forall a1 a2: A, *)
  (*         eq__A a1 a2 <-> a1 = a2), *)
  (*   forall (le_trans__A : forall a1 a2 a3: A, *)
  (*         le__A a1 a2 -> le__A a2 a3 -> le__A a1 a3), *)
  (*   forall (s: t) *)
  (*     (init res: A), *)
  (*     monotonic2 f le__A le__elmt le__A -> *)
  (*     increasing f le__A -> *)
  (*     Fold_Left f s init res -> *)
  (*     le__A init res. *)

    
End FoldableType.

Require Import Orders.

Module ListFoldable (T: UsualOrderedTypeFull) <: FoldableType.
  (* Module Type Inner. *)
    
  (* Definition t := T.t. *)
  (* Definition add := @cons T.t. *)
  Include FoldableType
    with Definition t := list T.t
            with Definition elmt := T.t
            with Definition add := @cons T.t
            with Definition empty := @nil T.t
            with Definition In := @In T.t
            with Definition elmt_eq_dec := T.eq_dec
            with Definition le__elmt := T.le
            with Definition fold_left := fun (A: Type) => @fold_left A T.t.
  (* End Inner. *)

  Section FoldLeftMonotonic.
    Lemma fold_left_monotonic' :
      forall  {A: Type} (f: A -> T.t -> A) (le__A: A -> A -> Prop) (lt__A: A -> A -> Prop) (eq__A: A -> A -> Prop),
      forall (le_lteq__A: forall (a1 a2: A),
            le__A a1 a2 <-> lt__A a1 a2 \/ eq__A a1 a2),
      forall (eq_spec__A: forall a1 a2: A,
            eq__A a1 a2 <-> a1 = a2),
      forall (le_trans__A : forall a1 a2 a3: A,
            le__A a1 a2 -> le__A a2 a3 -> le__A a1 a3),
      forall (s: list T.t)
        (init res: A),
        monotonic2 f le__A le__elmt le__A ->
        increasing f le__A ->
        Fold_Left f s init res ->
        le__A init res.
    Proof.
      induction s; intros.
      - invs H1.
        eapply le_lteq__A. right. eapply eq_spec__A. reflexivity.
      - invs H1.
        pose proof (F := H7).
        eapply IHs in H7; eauto.
        
    Qed.
  End FoldLeftMonotonic.

  Lemma fold_left_spec :
    forall (A: Type) (f: list A -> elmt -> list A) (s: t) (init res: list A),
      Fold_Left f s init res <->
        fold_left f s init = res.
  Proof.
    induction s; split; intros.
    - simpl. invs H. reflexivity.
    - simpl in H. invs H. econstructor.
    - invs H.
      eapply IHs in H5. rewrite <- H5.
      simpl. reflexivity.
    - rewrite <- H. simpl. econstructor.
      eapply IHs. reflexivity.
  Qed.

  Lemma fold_left_option :
    forall (A: Type) (f: option A -> elmt -> option A) (s: t) (init: A) (res: option A),
      (forall (acc: A),
          Forall (fun e => exists res, f (Some acc) e = Some res) s) ->
      Fold_Left f s (Some init) res ->
      exists a,
        res = Some a.
  Proof.
    induction s; intros.
    - invs H0. exists init. reflexivity.
    - invs H0.
      pose proof (H' := H).
      specialize (H init).
      invs H.
      destruct H3.
      rewrite H1 in H6. eapply IHs in H6. eauto.
      intros.
      specialize (H' acc).
      invs H'. eauto.
  Qed.

  (* Lemma fold_left_option_map : *)
  (*   forall (A: Type) (f: option A -> elmt -> option A) (s: t) (init: A) (res: option A), *)
      
  
End ListFoldable.

Lemma join_left_right :
  forall (t: tup_type) (jvs: list string),
    join_tuples_left jvs t = join_tuples_right jvs t.
Proof.
  destruct t; intros.
  - unfold join_tuples_left. unfold join_tuples_right. destruct (all_vars_present jvs nil).
    reflexivity. reflexivity.
  - unfold join_tuples_left. unfold join_tuples_right.
    destruct (all_vars_present jvs (p :: t)).
    + reflexivity.
    + reflexivity.
Qed.

Lemma match_order_fine:
forall t1 a t2,
match assoc_lookup t1 a with
  | Some g1 =>
      match assoc_lookup t2 a with
      | Some g2 =>
          if Ground_Types_as_OTF.eq_dec g1 g2
          then true
          else false
      | None => false
      end
  | None => false
  end = match assoc_lookup t2 a with
  | Some g1 =>
      match assoc_lookup t1 a with
      | Some g2 =>
          if Ground_Types_as_OTF.eq_dec g1 g2
          then true
          else false
      | None => false
      end
  | None => false
  end.
Proof.
  intros. remember (assoc_lookup t1 a). remember (assoc_lookup t2 a).
  destruct o; destruct o0.
  destruct (Ground_Types_as_OTF.eq_dec g g0); destruct (Ground_Types_as_OTF.eq_dec g0 g); eauto.
  destruct n; eauto. eauto. eauto. eauto.
Qed.
  

(* TODO *)
Lemma check_join_vars_symmetric :
  forall (jvs: list string) (t1 t2: tup_type),
    check_join_vars jvs t1 t2 = check_join_vars jvs t2 t1.
Proof.
  induction jvs; intros.
  - unfold check_join_vars. simpl; eauto.
  - unfold check_join_vars. simpl.
    remember (match assoc_lookup t1 a with
    | Some g1 =>
        match assoc_lookup t2 a with
        | Some g2 =>
            if Ground_Types_as_OTF.eq_dec g1 g2
            then true
            else false
        | None => false
        end
    | None => false
    end). destruct b; erewrite match_order_fine; rewrite <- Heqb. eauto.
    erewrite fold_left_false. erewrite fold_left_false; eauto.
Qed. 


(* TODO, may also need a second pair of eyes to make sure
 * that this is reasonable  *)
Lemma join_tuples_symmetric :
  forall (jvs: list string) (t1 t2: tup_type),
    forall (NonNil: jvs <> nil),
    join_tuples jvs t1 t2 = join_tuples jvs t2 t1.
Proof.
  intros. rewrite join_tuples_is_join_parts.
  rewrite join_tuples_is_join_parts.
  destruct (join_tuples_left jvs t1) eqn:JL1;
  destruct_any_match_in_goal;
  rename A into JJ;
  destruct_any_match_in_goal;
  rename A into JR2;
  (try (destruct_any_match_in_goal; rename A into JL2));
  (try (destruct_any_match_in_goal; rename A into JJ1));
    (try (destruct_any_match_in_goal; rename A into JR1)).
  - rewrite join_left_right in JL1.
    rewrite JL1 in JR1. invc JR1.
    rewrite join_left_right in JL2. rewrite JL2 in JR2.
    invc JR2.
    f_equal.
    eapply list_set_equality.
    simpl. unfold set_In. split; intros; eapply in_or_app; repeat match goal with
                                                | [ H: In _ (_ ++ _) |- _ ] =>
                                                    eapply in_app_or in H; destruct H
                                                                  end.
    + right. eapply in_or_app. eauto.
    + right. eapply in_or_app. left.
      clear JL2. clear JL1. clear t3. clear t6.
      revert H. revert x. revert JJ1. revert t5. revert JJ. revert t0 t2. induction t1; intros.
      * unfold join_tuples_joined in *.
        simpl in *.
        destruct (check_join_vars jvs nil t2) eqn:C.
        pose proof (check_join_vars_symmetric).
        specialize (H0 jvs nil t2).
        rewrite C in H0. rewrite <- H0 in JJ1.
        unfold check_join_vars in C. simpl in C.
        enough (fold_left
        (fun (acc : bool) (_ : string) => if acc then false else false)
        jvs true = false).
        rewrite H1 in C. congruence.
        revert NonNil. clear. induction jvs; intros.
        -- congruence.
        -- simpl. destruct jvs.
           ++ simpl. reflexivity.
           ++ eapply IHjvs. congruence.
        -- rewrite check_join_vars_symmetric in C. rewrite C in JJ1. invs JJ1.
      * unfold join_tuples_joined in JJ, JJ1.
        rewrite check_join_vars_symmetric in JJ1.
        destruct (check_join_vars jvs (a :: t1) t2) eqn:C.
        -- eapply check_join_vars_adequacy in C. invs C.
           ++ congruence.
           ++ invs C. 
              eapply assoc_lookup_adequacy in H1, H2, H6, H7.
              rewrite H2 in H1.
              eapply IHt1; eauto. unfold join_tuples_joined.
              (* unfold check_join_vars.
              specialize (In_dec string_dec j jvs0); intro.
              destruct H3. unfold string_sets.fold in JJ1, JJ.
              erewrite rewite_rule2 in JJ1, JJ. rewrite JJ in JJ1.

              remember (list_to_string_set (j :: jvs0)).
              unfold string_sets.fold in JJ1, JJ.
              destruct (string_sets.this t). admit.
              simpl in JJ1, JJ.
              destruct t.this.
              unfold string_sets.add in JJ1. simpl in JJ1.
              remember (j::jvs0).
              simpl in JJ1, JJ. 
              
              (* This is definitely true, but will i have time to finish it? *)
              simpl in JJ.  *)
              

Admitted.

Lemma set_prod_nil_left :
  forall (g: set tup_type),
    set_prod (@nil tup_type) g = nil.
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma set_prod_nil_right :
  forall (g: set tup_type),
    set_prod g (@nil tup_type) = nil.
Proof.
  induction g; intros.
  - reflexivity.
  - simpl. eauto.
Qed.

Lemma set_prod_cons_right :
  forall (g1 g2: set tup_type) (a: tup_type),
    set_prod g1 (a :: g2) = map (fun x => (x, a)) g1 ++ (set_prod g1 g2).
Proof.
  induction g1; intros.
  - simpl. reflexivity.
  - simpl. rewrite IHg1.
    eapply list_set_equality.
    simpl. split; intros.
    + destruct H.
      * subst. left. eauto.
      * right. eapply in_app_iff in H. eapply in_app_iff.
        destruct H.
        -- right. eapply in_app_iff. eauto.
        -- eapply in_app_iff in H. destruct H.
           ++ eauto.
           ++ right. eapply in_app_iff. eauto.
    + destruct H; subst; eauto.
      eapply in_app_iff in H. destruct H.
      * right. eapply in_app_iff; eauto.
        right. eapply in_app_iff; eauto.
      * right. eapply in_app_iff in H.
        eapply in_app_iff.
        destruct H; eauto.
        right. eapply in_app_iff; eauto.
Qed.
(* TODO *)
Lemma fold_left_app_comm :
  forall (g1 g2: set (tup_type * tup_type)) init jvs,
    fold_left
    (fun (acc : set tup_type) (elmt : tup_type * tup_type) =>
       let (t1, t2) := elmt in
       match join_tuples jvs t1 t2 with
       | Some tup => set_add str_gt_list_ot.eq_dec tup acc
       | None => acc
       end) (g1 ++ g2) init =
      fold_left
    (fun (acc : set tup_type) (elmt : tup_type * tup_type) =>
       let (t1, t2) := elmt in
       match join_tuples jvs t1 t2 with
       | Some tup => set_add str_gt_list_ot.eq_dec tup acc
       | None => acc
       end) (g2 ++ g1) init.
Proof.
  induction g1; intros.
  - rewrite app_nil_r. Opaque join_tuples.
    simpl. reflexivity.
  - simpl. erewrite IHg1.
    enough (g2 ++ a :: g1 = a :: g2 ++ g1).
    simpl in *.
    rewrite H. simpl.
    reflexivity.
    eapply list_set_equality.
    simpl. split; intros.
    unfold set_In in H. specialize (in_app_or _ _ _ H); intro. 
    destruct H0. right. unfold set_In. eapply in_or_app. eauto.
    simpl in H0. destruct H0; eauto. right. eapply in_or_app; eauto.
    unfold set_In in *. eapply in_or_app; simpl. destruct H; eauto.
    specialize (in_app_or _ _ _ H); intro. destruct H0; eauto.
Qed.
Lemma switch_helper:
forall jvs a g2 init,
fold_left
  (fun (acc : set tup_type) (elmt : tup_type * tup_type)
   =>
   let (t1, t2) := elmt in
   match join_tuples jvs t1 t2 with
   | Some tup => set_add str_gt_list_ot.eq_dec tup acc
   | None => acc
   end) (set_prod (a :: nil) g2)
  init =
fold_left
  (fun (acc : set tup_type) (elmt : tup_type * tup_type)
   =>
   let (t1, t2) := elmt in
   match join_tuples jvs t1 t2 with
   | Some tup => set_add str_gt_list_ot.eq_dec tup acc
   | None => acc
   end) (set_prod g2 (a :: nil))
  init.
Proof.
  intros. revert init. induction g2. 
  - simpl; eauto.
  - intros.
    assert ((set_prod (a::nil) (a0 :: g2)) = (a,a0) :: (list_prod (a::nil) g2)).
    eauto. rewrite H.
    assert ((set_prod (a0::g2) (a :: nil)) = (a0,a) :: (list_prod (g2) (a::nil))).
    eauto. rewrite H0.
    simpl. fold tup_type. erewrite <- app_nil_end.
    replace (map (fun y : tup_type => (a, y)) g2) with (set_prod (a :: nil) g2).
    erewrite IHg2. erewrite join_tuples_symmetric. eauto.
    admit. (* didn't handle nil case of jvs *)
    unfold set_prod. unfold list_prod. erewrite app_nil_end; eauto.
Admitted.

(* TODO *)
Lemma fold_left_switch :
  forall (jvs: list string) g1 g2 init,
  fold_left
    (fun (acc : set tup_type) (elmt : tup_type * tup_type) =>
       let (t1, t2) := elmt in
       match join_tuples jvs t1 t2 with
       | Some tup => set_add str_gt_list_ot.eq_dec tup acc
       | None => acc
       end) (set_prod g1 g2) init =
    fold_left
      (fun (acc : set tup_type) (elmt : tup_type * tup_type) =>
         let (t1, t2) := elmt in
         match join_tuples jvs t1 t2 with
         | Some tup => set_add str_gt_list_ot.eq_dec tup acc
         | None => acc
         end) (set_prod g2 g1) init.
Proof.
  induction g1; intros.
  - rewrite set_prod_nil_right. rewrite set_prod_nil_left. reflexivity.  
  - Opaque join_tuples. simpl.
    rewrite fold_left_app.
    rewrite IHg1.
    rewrite <- fold_left_app. destruct g2.
    + simpl. reflexivity.
    + simpl. rewrite join_tuples_symmetric.
      destruct (join_tuples jvs t a).
      * rewrite fold_left_app. rewrite fold_left_app. rewrite <- IHg1.
        rewrite fold_left_app. rewrite set_prod_cons_right.
        rewrite fold_left_app.
        rewrite <- IHg1.
        f_equal. fold tup_type.
        replace ((map (fun y : tup_type => (t, y)) g1)) with (set_prod (t:: nil) g1).
        symmetry.
        rewrite <- fold_left_app. symmetry.
        rewrite fold_left_app_comm.
        rewrite fold_left_app. f_equal.
        replace (map (fun y : tup_type => (a, y)) g2) with (set_prod (a :: nil) g2).
        replace (map (fun x : tup_type => (x, a)) g2) with (set_prod g2 (a :: nil)).
        simpl. fold tup_type. 
        replace (map (fun y : tup_type => (a, y)) g2) with (set_prod (a :: nil) g2).
        rewrite <- app_nil_end.
        eapply switch_helper.
        unfold set_prod. unfold list_prod. erewrite app_nil_end; eauto.
        unfold set_prod. induction g2. simpl; eauto. simpl. f_equal. eauto. 
        unfold list_prod. simpl. erewrite app_nil_end; eauto.
        unfold set_prod. unfold list_prod. erewrite app_nil_end; eauto.
      * rewrite fold_left_app. rewrite fold_left_app. rewrite <- IHg1.
        rewrite fold_left_app. rewrite set_prod_cons_right.
        rewrite fold_left_app.
        rewrite <- IHg1.
        f_equal. fold tup_type.
        replace ((map (fun y : tup_type => (t, y)) g1)) with (set_prod (t:: nil) g1).
        symmetry.
        rewrite <- fold_left_app. symmetry.
        rewrite fold_left_app_comm.
        rewrite fold_left_app. f_equal.
        replace (map (fun y : tup_type => (a, y)) g2) with (set_prod (a :: nil) g2).
        replace (map (fun x : tup_type => (x, a)) g2) with (set_prod g2 (a :: nil)).
        simpl. fold tup_type. 
        replace (map (fun y : tup_type => (a, y)) g2) with (set_prod (a :: nil) g2).
        rewrite <- app_nil_end.
        eapply switch_helper.
        unfold set_prod. unfold list_prod. erewrite app_nil_end; eauto.
        unfold set_prod. induction g2. simpl; eauto. simpl. f_equal. eauto. 
        unfold list_prod. simpl. erewrite app_nil_end; eauto.
        unfold set_prod. unfold list_prod. erewrite app_nil_end; eauto.
      * admit.
Admitted.
  
  
Lemma join_relations_symmetric :
  forall (jvs: list string) (g1 g2: set tup_type),
    join_relations jvs g1 g2 = join_relations jvs g2 g1.
Proof.
  induction g1; intros.
  - unfold join_relations.
    rewrite set_prod_nil_left. rewrite set_prod_nil_right. reflexivity.
  - Opaque join_tuples.
    simpl.
    rewrite fold_left_switch.
    simpl. reflexivity.
Qed.
    
    
    
