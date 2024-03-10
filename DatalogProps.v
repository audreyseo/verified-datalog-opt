From Coq Require Import  List String Arith Psatz DecidableTypeEx OrdersEx Program.Equality FMapList MSetWeakList.

From VeriFGH Require Import OrdersFunctor HelperTactics StringOrders UIPList.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.

Module string_sets := Make(String_as_OT).

Variant rel_type :=
  | idb
  | edb.


Variant ground_types : Set :=
    | NAT (n: nat)
    | STR (s: string).

Structure rel :=
  Relation
    {
      name: String_as_OT.t;
      num_args: nat;
      args: Vector.t String_as_OT.t num_args;
      args_list: list String_as_OT.t;
      grounded_args: list (String_as_OT.t * ground_types);
      rtype : rel_type;
    }.

Variant rule : Type :=
  | rule_def_empty (head: rel)
  | rule_def (head: rel) (body: list rel)
  | rule_def_exists (head: rel) (l: string_sets.t) (body: list rel).
(* head :- exists (vars in l), body *)

Print string_sets.
Eval compute in string_sets.t_.

Fixpoint vector_to_string_set {n: nat} (v: Vector.t string n) :=
  match v with
  | Vector.nil _ => string_sets.empty
  | Vector.cons _ h n v' =>
      string_sets.add h (vector_to_string_set v')
  end.

Definition body_args (bodies: list rel) :=
  let fn := (fix helper bs res :=
               match bs with
               | List.nil => res
               | b :: bs' =>
                   helper bs' (string_sets.union (vector_to_string_set (args b))  res)
               end) in
  fn bodies string_sets.empty.

Fixpoint list_to_string_set (l: list string) :=
    match l with
    | nil => string_sets.empty
    | hd :: rst => string_sets.add hd (list_to_string_set rst)
    end.

Module List_String_OTF := List_as_OTF(String_OTF).


Module Safety.

  Definition in_at_least_one_rel (body: list rel) (v: string) :=
    existsb (fun r => ListSet.set_mem string_dec v (args_list r)) body.

  Definition rel_is_safe (r: rel) : Prop :=
    Vector.to_list (args r) = args_list r.

  Definition safe_rel (r: rel) : bool :=
    if List_String_OTF.eq_dec (Vector.to_list (args r)) (args_list r) then
      true
    else false.

  Arguments rel_is_safe r/.
  Arguments safe_rel r/.

  Lemma safe_rel_adequacy :
    forall (r: rel),
      rel_is_safe r <->
        safe_rel r = true.
  Proof.
    destruct r; split; simpl; intros.
    - rewrite H. match goal with
                 | [ |- (if ?a then true else false) = true ] =>
                     destruct (a) eqn:A; try congruence
                 end.
    - match goal with
      | [ H: (if ?a then true else false) = true |- _ ] =>
          destruct (a) eqn:A; try congruence
      end.
  Qed.
    
           

  Definition rule_safe (r: rule) : bool :=
    match r with
    | rule_def_empty hd =>
        andb (Nat.eqb (num_args hd) 0)
             (safe_rel hd)
    | rule_def hd body =>
        andb (forallb (in_at_least_one_rel body) (args_list hd))
             (andb (safe_rel hd)
                   (forallb safe_rel body))
    | rule_def_exists hd e_vars body =>
        andb
          (forallb (in_at_least_one_rel body) (args_list hd))
          (andb (string_sets.for_all (in_at_least_one_rel body) e_vars)
                (andb (safe_rel hd)
                      (forallb safe_rel body)))
    end.

  Arguments rule_safe r/.

  
  
  Inductive rule_safe_rel : rule -> Prop :=
  | empty_is_safe :
    forall (head: rel),
      num_args head = 0 ->
      rel_is_safe head ->
      rule_safe_rel (rule_def_empty head)
  | def_is_safe :
    forall (head: rel) (body: list rel),
      rel_is_safe head ->
      Forall (fun r => rel_is_safe r) body ->
      Forall (fun v => Exists (fun r => In v (args_list r)) body) (args_list head) ->
      rule_safe_rel (rule_def head body)
  | exists_def_is_safe :
    forall (head: rel) (e_vars: string_sets.t) (body: list rel),
      rel_is_safe head ->
      Forall (fun r => rel_is_safe r) body ->
      Forall (fun v => Exists (fun r => In v (args_list r)) body) (args_list head) ->
      string_sets.For_all (fun v => Exists (fun r => In v (args_list r)) body) e_vars ->
      rule_safe_rel (rule_def_exists head e_vars body).

  Lemma UIP_nat_refl :
    forall (n: nat)
      (H: n = n),
      H = eq_refl.
  Proof.
    intros. pose proof (UIP_nat n n H eq_refl). eauto.
  Qed.


  Lemma in_at_least_one_rel_adequacy :
    forall body h,
      Forall rel_is_safe body ->
      Exists (fun r : rel => In h (args_list r)) body <->
        in_at_least_one_rel body h = true.
  Proof.
    induction body; split; intros.
    - invs H0.
    - simpl in H0. congruence.
    - invs H. invs H0.
      + simpl.
        destruct (args_list a).
        * invs H2.
        * eapply ListSet.set_mem_correct2 in H2.
          rewrite H2. reflexivity.
      + simpl.
        eapply Bool.orb_true_iff.
        right. eapply IHbody; eauto.
    - simpl in H0. invs H.
      eapply Bool.orb_true_iff in H0.
      destruct H0.
      + left. eapply ListSet.set_mem_correct1. eauto.
      + right. eapply IHbody; eauto.
  Qed.

  Lemma safe_body_adequacy :
    forall body,
      Forall rel_is_safe body <->
        forallb safe_rel body = true.
  Proof.
    induction body; split; intros.
    - reflexivity.
    - econstructor.
    - simpl. eapply Bool.andb_true_iff.
      invs H.
      split.
      + simpl in H2. rewrite H2. destruct (List_String_OTF.eq_dec (args_list a) (args_list a)) eqn:A; try congruence.
      + eapply IHbody. eauto.
    - simpl in H. eapply Bool.andb_true_iff in H.
      destruct H.
      destruct (List_String_OTF.eq_dec (Vector.to_list (args a)) (args_list a)) eqn:A; try congruence.
      econstructor.
      + simpl. eauto.
      + eapply IHbody. eauto.
  Qed.
      
  
  Lemma rule_safe_adequacy :
    forall (r: rule),
      rule_safe_rel r <->
        rule_safe r = true.
  Proof.
    destruct r; split; intros.
    - invs H. simpl.
      simpl in H2. rewrite H2.
      rewrite H1. simpl.
      match goal with
      | [ |- (if ?a then true else false) = true ] =>
          destruct (a) eqn:A; try congruence
      end.
    - simpl in H.
      eapply Bool.andb_true_iff in H. destruct H.
      destruct (List_String_OTF.eq_dec (Vector.to_list (args head)) (args_list head)); try congruence.
      econstructor.

      eapply Nat.eqb_eq in H. eauto.
      simpl. eauto.
    - simpl. invs H.
      simpl in H2. rewrite H2.
      clear H2.
      clear H.
      revert H4 H3.
      remember (args_list head) as hd.
      clear Heqhd.
      clear head.
      
      revert body. induction hd; intros.
      + simpl.
        clear H4. invs H3.
        simpl. reflexivity.
        simpl. eapply safe_rel_adequacy in H.
        simpl in H.
        destruct (List_String_OTF.eq_dec (Vector.to_list (args x)) (args_list x)); try congruence.
        simpl.
        revert H0. clear e. clear H3. clear H.
        induction l; intros.
        * simpl. reflexivity.
        * invs H0. eapply IHl in H3. eapply safe_rel_adequacy in H2.
          Opaque safe_rel.
          simpl.
          rewrite H2. rewrite H3. reflexivity.
      + invs H4.
        pose proof (IHhd body H2 H3).
        Opaque in_at_least_one_rel.
        eapply Bool.andb_true_iff in H. destruct H.
        eapply Bool.andb_true_iff in H0. destruct H0.
        simpl.
        invs H4.
        destruct (in_at_least_one_rel body a) eqn:A.
        * Transparent in_at_least_one_rel.
          simpl in A. unfold in_at_least_one_rel in A.
          simpl.
          rewrite H. simpl.
          destruct (List_String_OTF.eq_dec hd hd); try congruence.
          destruct (String_OTF.eq_dec a a); try congruence.
          rewrite (UIP_string_refl _ e0).
          eapply Bool.andb_true_iff. split.
          -- match goal with
             | [ |- (if ?a then true else false) = true ] =>
                 destruct (a) eqn:A'; try congruence
             end.
          -- eauto.
        * simpl.
          eapply in_at_least_one_rel_adequacy in H1. congruence.
          eauto.
    - simpl in H. eapply Bool.andb_true_iff in H. destruct H.
      eapply Bool.andb_true_iff in H0. destruct H0.
      destruct (args_list head) eqn:ARGS;
     
        econstructor; try eapply safe_rel_adequacy; eauto.
      + clear H. clear H0. revert H1. clear ARGS. induction body; intros; try econstructor.
        simpl in H1. eapply Bool.andb_true_iff in H1.
        destruct H1. eapply safe_rel_adequacy; eauto.
        simpl in H1. eapply Bool.andb_true_iff in H1. destruct H1. eapply IHbody. eauto.
      + rewrite ARGS in *. econstructor.
      + revert H1. clear H. clear H0. clear ARGS. clear l. clear t. induction body; intros; econstructor.
        simpl in H1. eapply Bool.andb_true_iff in H1. destruct H1.
        eapply safe_rel_adequacy. eauto.
        simpl in H1. eapply Bool.andb_true_iff in H1. destruct H1. eapply IHbody. eauto.
      + rewrite ARGS in *. simpl in H.
        eapply Bool.andb_true_iff in H. destruct H.
        econstructor.
        * eapply in_at_least_one_rel_adequacy; eauto.
          revert H1. clear.
          induction body; intros; econstructor.
          simpl in H1. eapply safe_rel_adequacy.
          eapply Bool.andb_true_iff in H1. destruct H1. eauto.
          eapply IHbody.
          simpl in H1. eapply Bool.andb_true_iff in H1. eapply H1.
        * revert H2. clear H0. revert H1.
          clear H. clear ARGS. clear.
          revert body. induction l; intros.
          -- econstructor.
          -- simpl in H2. eapply Bool.andb_true_iff in H2. destruct H2.
             econstructor.
             ++ eapply in_at_least_one_rel_adequacy.
                eapply safe_body_adequacy.
                eauto.
                eauto.
             ++ eapply IHl. eauto. eauto.
    - simpl. eapply Bool.andb_true_iff. invs H.
      clear H.
      split.
      + clear H5.
        clear H3.
        revert H4. revert H6. clear.
        revert body.
        destruct (args_list head).
        clear head.
        * intros.
          reflexivity.
        * induction l0; intros.
          -- simpl. invs H4. eapply Bool.andb_true_iff; split; eauto.
             destruct l.
             simpl. unfold string_sets.For_all in *.
             destruct this.
             (*
             eapply in_at_least_one_rel_adequacy; eauto.
             eauto. eauto.
          -- simpl. invs H4. invs H2.
             rewrite Bool.andb_comm.
             rewrite <- Bool.andb_assoc.
             eapply Bool.andb_true_iff.
             split; try eapply in_at_least_one_rel_adequacy; eauto.
             rewrite Bool.andb_comm. eapply IHl.
             eauto.
             econstructor; eauto.
      + eapply Bool.andb_true_iff.
        split.
        * clear H4. revert H5. revert H3. revert body. destruct l.
          induction this; intros.
          -- reflexivity.
          -- unfold string_sets.for_all. simpl.
             unfold string_sets.For_all in H5.
             assert (string_sets.In a {| string_sets.this := a :: this;
                                        string_sets.is_ok := is_ok |}).
             unfold string_sets.In. left. reflexivity.
             pose proof (H5' := H5).
             specialize (H5 _ H).
             eapply in_at_least_one_rel_adequacy in H5; eauto.
             rewrite H5.
             eapply IHthis.
             eauto.
             unfold string_sets.For_all. intros.
             eapply H5'.
             right. eauto.
        * eapply Bool.andb_true_iff.
          
             
             
             
             ++ 
        induction hd; intros.
        * reflexivity.
        * invs H4. simpl. eapply Bool.andb_true_iff.
          split.
          -- eapply in_at_least_one_rel_adequacy.
             eauto. eauto.
          -- eapply IHhd.
             
                eapply 
             
                                         
          
          
          
        
        

      revert H; induction body; intros; try (solve [econstructor ]).
      + simpl in H1.
        eapply Bool.andb_true_iff in H1. destruct H1.
        econstructor; eauto.
        eapply safe_rel_adequacy.
        eauto.
      + simpl in H. rewrite ARGS. econstructor.
      + rewrite ARGS in *.
        econstructor.
      + simpl. simpl in H.
        eapply Bool.andb_true_iff in H. destruct H.
        eapply Bool.orb_true_iff in H. destruct H.
        * 
      + simpl in H1.
        eapply Bool.andb_true_iff in H1.
        destruct H1.
        
        econstructor.
        eapply safe_rel_adequacy. eauto.
        eapply IHbody.
        reflexivity.
        eauto.
      + rewrite ARGS. econstructor.
      + rewrite ARGS. econstructor.
      + simpl in H1. eapply Bool.andb_true_iff in H1. destruct H1.
        econstructor.
        eapply safe_rel_adequacy. eauto.
        eapply 
      + simpl in H1. eapply Bool.andb_true_iff in H1. destruct H1.
        econstructor.
        eapply safe_rel_adequacy. eauto.
        eapply IHbody.
        unfold in_at_least_one_rel in H.
        destruct (args_list head) eqn:A.*)
  Admitted.
End Safety.

  
      


(* (* Not sure if this is the correct formalization of this, actually *) *)
(* Definition safe_rule (r: rule) := *)
(*   match r with *)
(*   | rule_def_empty head => true *)
(*   | rule_def head body => *)
(*       let bargs := body_args body in *)
(*       let hargs := vector_to_string_set (args head) in *)
(*       string_sets.equal bargs hargs *)
(*   | rule_def_exists head exists_args body => *)
(*       let hargs := vector_to_string_set (args head) in *)
(*       let bargs := body_args body in *)
(*       let eargs := exists_args in *)
(*       string_sets.equal (string_sets.union hargs eargs) bargs *)
(*   end. *)



Structure program :=
  DlProgram
    { idbs: string_sets.t;
      edbs: string_sets.t;
      answer: rel;
      rules: list rule;
    }.


Module DatalogNotation.
  Declare Scope rel_scope.
  Delimit Scope rel_scope with rel.

  Notation "{ r :- }" := (rule_def_empty r) : rel_scope.
  Notation "{ r :- x } " := (rule_def r (x :: nil)) : rel_scope.
  Notation "{ r :- x ; y ; .. ; z }" := (rule_def r (cons x (cons y .. (cons z nil) ..))) : rel_scope.
  Print rule_def_exists.
  Notation "{ r 'exists' a :- x ; y ; .. ; z }" := (rule_def_exists r (string_sets.add a string_sets.empty) (cons x (cons y .. (cons z nil)  .. ))) : rel_scope.
  Notation "{ r 'exists'  a ; b ; .. ; c  :- x ; y ; .. ; z }" := (rule_def_exists r (string_sets.add a (string_sets.add b .. (string_sets.add c (string_sets.empty)) .. ) ) (cons x (cons y .. ( cons z nil ) .. ))) : rel_scope.

  Declare Scope string_sets_scope.
  Delimit Scope string_sets_scope with ssets.
  Notation "'s{' x '}s'" := (string_sets.add x string_sets.empty) : string_sets_scope.
  Notation "'s{' x ; y ; .. ; z '}s'" := (string_sets.add x (string_sets.add y .. (string_sets.add z string_sets.empty) ..)) : string_sets_scope.
  Eval compute in s{ "x"; "y"; "z" }s%ssets.

End DatalogNotation.
Import DatalogNotation.
Arguments DlProgram (idbs edbs)%ssets answer rules%list_scope.


(* Check Relation. *)

Definition mk_rel_ground (n: String_as_OT.t) (args: list String_as_OT.t) (grounds: list (string * ground_types)) (rtype: rel_type) :=
  Relation n (Datatypes.length args) (Vector.of_list args) args grounds rtype.

Definition mk_rel (n: String_as_OT.t) (args: list String_as_OT.t) (rtype: rel_type) :=
  Eval compute in mk_rel_ground n args nil rtype.



Eval compute in (mk_rel "R" (cons "x" nil) edb).


Section ProgramI.
  Let Rx := Eval compute in (mk_rel "R" (cons "x" nil) idb).
  Let Vx := Eval compute in (mk_rel "V" (cons "x" nil) edb).
  Let Txyz := Eval compute in (mk_rel "T" (cons "x" (cons "y" (cons "z" nil))) edb).
  Let Ry := Eval compute in (mk_rel "R" (cons "y" nil) idb).
  Let Rz := Eval compute in (mk_rel "R" (cons "z" nil) idb).
  Let Qx := Eval compute in (mk_rel "Q" (cons "x" nil) idb).
  Let Gx := Eval compute in (mk_rel "G" (cons "x" nil) edb).
  Let Qo' := Eval compute in (mk_rel "Qo'" nil idb).
  Let Ro' x := Eval compute in (mk_rel "Ro'" (cons x nil) idb).
  Let Ro'z := Eval compute in (Ro' "z").
  Let Ro'y := Eval compute in (Ro' "y").
  Let Ro'x := Eval compute in (Ro' "x").
  Let Ro x := Eval compute in (mk_rel "Ro" (cons x nil) idb).
  Let Rox := Eval compute in (Ro "x").
  Let Qox := Eval compute in (mk_rel "Qo" (cons "x" nil) idb).
  Let Go' := Eval compute in (mk_rel "Go'" nil idb).
  Let To' := Eval compute in (mk_rel "To'" nil idb).
  Let Vo' := Eval compute in (mk_rel "Vo'" nil idb).
  Let Roy := Eval compute in (Ro "y").
  Let Roz := Eval compute in (Ro "z").


  

  Definition magic_sets_edbs :=
    list_to_string_set (cons "V" (cons "T" (cons "G" nil))).

  Definition program1 :=
    DlProgram
      (list_to_string_set (cons "R" (cons "Q" nil)))
      magic_sets_edbs
      Qx
      (cons (rule_def Rx (cons Vx nil)) (* R(x) :- V(X) *)
            (cons (rule_def_exists
                     Rx (list_to_string_set (cons "y" (cons "z" nil)))
                     (cons Txyz (cons Ry (cons Rz nil))))
                  (* R(x) :- exists y, z, T(x, y, z), R(y), R(z) *)
                  (cons
                     (rule_def Qx
                               (cons Gx (cons Rx nil)))
                     nil))).

  Let Qo'rule := rule_def_empty Qo'.
  Let Ro'yrule := (rule_def_exists Ro'y (list_to_string_set (cons "x" (cons "z" nil))) (cons Ro'x (cons Txyz nil))).
  Let Ro'zrule := (rule_def_exists Ro'z
                                   (list_to_string_set (cons "x" (cons "y" nil)))
                                   (cons Ro'x (cons Txyz (cons Roy nil)))).
  Let Ro'xrule := (rule_def Ro'x
                            (cons Qo' (cons Gx nil))).
  Let Roxrule := (rule_def Rox
                           (cons Ro'x (cons Vx nil))).
  Let Roxexistsrule := (rule_def_exists Rox
                                        (list_to_string_set (cons "y" (cons "z" nil)))
                                        (cons Ro'x
                                              (cons Txyz
                                                    (cons Roy
                                                          (cons Roz nil))))).
  Let Qoxrule := rule_def Qox
                          (cons Qo' (cons Gx (cons Rox nil))).
  Definition program2 :=
    DlProgram
      (list_to_string_set (cons "Qo'" (cons "Ro'" (cons "Ro" (cons "Qo" (cons "Vo'" (cons "To'" (cons "Go'" nil))))))))
      magic_sets_edbs
      Qox
      (cons (rule_def_empty Qo')
            (cons Ro'yrule
                  (cons Ro'zrule
                        (cons Ro'xrule
                              
                              (cons Roxrule
                                    (cons Roxexistsrule
                                          (cons Qoxrule nil))))))).

End ProgramI.

      
