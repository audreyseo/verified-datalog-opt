From Coq Require Import MSetWeakList List String Arith Psatz DecidableTypeEx OrdersEx.

(* From VeriFGH Require Import Datalogo. *)

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.

Print String_as_OT.t.

Module string_sets := Make(String_as_OT).

Variant rel_type :=
  | idb
  | edb.


Structure rel :=
  Relation
    {
      name: String_as_OT.t;
      num_args: nat;
      args: Vector.t String_as_OT.t num_args;
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



Definition safe_rule (r: rule) :=
  match r with
  | rule_def_empty head => true
  | rule_def head body =>
      let bargs := body_args body in
      let hargs := vector_to_string_set (args head) in
      string_sets.equal bargs hargs
  | rule_def_exists head exists_args body =>
      let hargs := vector_to_string_set (args head) in
      let bargs := body_args body in
      let eargs := exists_args in
      string_sets.equal (string_sets.union hargs eargs) bargs
  end.

Structure program :=
  DlProgram
    { idbs: string_sets.t;
      edbs: string_sets.t;
      answer: rel;
      rules: list rule;
    }.

Check Relation.


Definition mk_rel (n: String_as_OT.t) (args: list String_as_OT.t) (rtype: rel_type) :=
  Relation n (Datatypes.length args) (Vector.of_list args) (rtype).

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


  Fixpoint list_to_string_set (l: list string) :=
    match l with
    | nil => string_sets.empty
    | hd :: rst => string_sets.add hd (list_to_string_set rst)
    end.

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

Section RelDec.
  Hypothesis (r1 r2: rel).

  Lemma rel_dec :
    { r1 = r2 } + { r1 <> r2 }.
  Proof.
    destruct r1, r2.
    destruct (String_as_OT.eq_dec name0 name1); try (right; congruence).
    destruct (Nat.eq_dec num_args0 num_args1); try (right; congruence).
    subst num_args0.
    destruct (Vector.eq_dec _ _ String_as_OT.eqb_eq _ args0 args1); try (subst; right; congruence).
    - subst.
      destruct rtype0, rtype1; try (right; congruence).
      all: left; congruence.
    - subst. right. unfold not; intros. inversion H. subst.
      inversion_sigma_on H1.
      pose proof (Eqdep_dec.UIP_refl_nat).
      specialize (H0 _ H1_).
      rewrite H0 in H1_0. simpl in H1_0. congruence.
  Defined.
End RelDec.


Module RelTyp <: Equalities.Typ.
  Definition t := rel.
End RelTyp.


Module RelHasUsualEq <: Equalities.HasUsualEq(RelTyp).
  Import RelTyp.
  Definition eq := @Logic.eq t.
End RelHasUsualEq.

Module RelUsualEq <: Equalities.UsualEq.
  Include RelHasUsualEq.
  Include RelTyp.
End RelUsualEq.

Print Equalities.UsualDecidableType.

Module RelDec <: Equalities.UsualDecidableType.
  Include RelUsualEq.
  Definition eq_equiv : RelationClasses.Equivalence RelUsualEq.eq := RelationClasses.eq_equivalence.
  Definition eq_dec := rel_dec.

End RelDec.

Module rset := Make(RelDec).

(* rule1 :- edb1(...), edb2(...)
rule1 = {}
rule1 = edb1(...) n edb2(...)



 *)

(*
Module RelSemantics.
  Import rset.

  Module RelTotalTransitiveBool <: Orders.TotalTransitiveLeBool'.
    Include RelDec.
    Definition rel_type_leb (rt1 rt2: rel_type) :=
      match rt1, rt2 with
      | idb, edb => false
      | _, _ => true
      end.
    Module String_OTF <: Orders.OrderedTypeFull.
      Include String_as_OT.
      
      Section StringLe.
        (* Hypothesis (s1 s2: string). *)
        Definition le (s1 s2: string) :=
          String.leb s1 s2 = true.
        Infix "<=" := le.
        Notation "x >= y" := (y<=x) (only parsing).
        Notation "x <= y <= z" := (x<=y /\ y<=z).
        Infix "<" := lt.
        Notation "x > y" := (y<x) (only parsing).
        Notation "x < y < z" := (x<y /\ y<z).
        Infix "==" := eq (at level 70, no associativity).
        Notation "x ~= y" := (~eq x y) (at level 70, no associativity).

        Lemma ascii_compare_same_as_ascii_ot_compare :
          forall (a1 a2: Ascii.ascii),
            Ascii_as_OT.compare a1 a2 = Ascii.compare a1 a2.
        Proof.
          reflexivity.
        Qed.

        Lemma string_compare_same_as_compare :
          forall (s1 s2: string),
            String.compare s1 s2 = compare s1 s2.
        Proof.
          reflexivity.
        Qed.
        
        Lemma le_lteq :
          forall (s1 s2: string),
            (s1 <= s2) <-> (s1 < s2) \/ (s1 == s2).
        Proof.
          induction s1; split; intros.
          - unfold le in H. destruct s2.
            + right. reflexivity.
            + left. reflexivity.
          - destruct H.
            + destruct s2; reflexivity.
            + symmetry in H. rewrite H. reflexivity.
          - destruct s2.
            + inversion H.
            + unfold le in H. destruct a, a0.
              unfold String.leb in H. simpl in H.
              destruct (Ascii.compare (Ascii.Ascii b b0 b1 b2 b3 b4 b5 b6)
                                      (Ascii.Ascii b7 b8 b9 b10 b11 b12 b13 b14)) eqn:COMP.
              * destruct (s1 ?= s2)%string eqn:C; try inversion H.
                pose proof (String_as_OT.compare_spec).
                unfold CompSpec in H0.
                specialize (H0 s1 s2).
                eapply OrderedTypeEx.String_as_OT.compare_helper_eq in C.
                subst.
                eapply OrderedTypeEx.Ascii_as_OT.cmp_eq in COMP. rewrite COMP. right. reflexivity.
                left. unfold lt.
                simpl. eapply OrderedTypeEx.Ascii_as_OT.cmp_eq in COMP. rewrite COMP. erewrite OrderedTypeEx.Ascii_as_OT.compare_helper_eq.
                shelve.
                eapply OrderedTypeEx.Ascii_as_OT.cmp_eq. symmetry. eassumption.
                Unshelve.
                assert (Ascii.Ascii b b0 b1 b2 b3 b4 b5 b6 = Ascii.Ascii b b0 b1 b2 b3 b4 b5 b6) by reflexivity.
                unfold Ascii_as_OT.compare. simpl.
                
                destruct b, b0, b1, b2, b3, b4, b5, b6; simpl; try eassumption.
              * left. unfold lt.
                simpl.
                rewrite ascii_compare_same_as_ascii_ot_compare.
                rewrite COMP. reflexivity.
              * inversion H.
          - destruct H.
            + destruct s2. inversion H.
              unfold lt in H. simpl in H.
              destruct (Ascii_as_OT.compare a a0) eqn:COMP; unfold le.
              * assert (compare s1 s2 = Lt \/ s1 == s2) by (left; assumption).
                eapply IHs1 in H0.
                unfold String.leb. simpl.
                rewrite ascii_compare_same_as_ascii_ot_compare in COMP. rewrite COMP.
                rewrite string_compare_same_as_compare. rewrite H.
                reflexivity.
              * unfold String.leb. simpl.
                rewrite ascii_compare_same_as_ascii_ot_compare in COMP. rewrite COMP. reflexivity.
              * unfold String.leb. simpl.
                rewrite ascii_compare_same_as_ascii_ot_compare in COMP.
                rewrite COMP. inversion H.
            + destruct s2. inversion H.
              inversion H. unfold le. unfold String.leb. simpl.
              assert (a0 = a0) by reflexivity.
              eapply OrderedTypeEx.Ascii_as_OT.cmp_eq in H0. unfold OrderedTypeEx.Ascii_as_OT.cmp in H0.
              rewrite H0.
              assert (s2 = s2) by reflexivity.
                                   
              eapply OrderedTypeEx.String_as_OT.cmp_eq in H3.
              unfold OrderedTypeEx.String_as_OT.cmp in H3. rewrite H3. reflexivity.
        Qed.
                
             
              
             
                
                
                eapply OrderedTypeEx.Ascii_as_OT.cmp_eq in H0.
                
                unfold OrderedTypeEx.Ascii_as_OT.cmp in H0. rewrite H0.
                assert (Ascii_as_OT.compare (Ascii.Ascii b b0 b1 b2 b3 b4 
                
          - 
    End String_OTF.
    Definition leb (r1 r2: rel) :=
      andb (String.leb (name r1) (name r2))
           (andb (Nat.leb (num_args r1) (num_args r2))
                 (andb (Vector.fold_left2
                          (fun acc elmt1 elmt2 =>
                             andb acc
                                  (String.leb elmt1 elmt2))
                          true
                          (args r1)
                          (args r2))
                       (rel_type_leb (rtype r1) (rtype r2)))).
    

  Lemma rel_type_dec :
    forall (r1 r2: rel_type),
      {r1 = r2} + {r1 <> r2}.
  Proof.
    destruct r1, r2; try (right; congruence); left; congruence.
  Defined.
  
  Definition is_edb (r: rel) :=
    if rel_type_dec (rtype r) edb then true
    else false.

  Variant ground_types : Set :=
    | NAT (n: nat)
    | STR (s: string).

  

  Structure rel_grounding: Type :=
    MkRelGrounding {
        r: rel;
        arg_types: Vector.t ground_types (num_args r);
      }.
  
  Definition rel_grounding_assoc 
    
  Structure grounding: Type :=
    MkGrounding {
        edbs: t;
        grounds: (* finite map *)
        is_edb: forall (r: rel), In r edbs -> rtype r = edb;
        grounded: forall (r: rel), In 
         
        

  Section RuleSemantics.
    Hypothesis (r: rule).

    
  
  Section Hypothesis (prog: program).
  

  
    (* 
      Theorem magic_sets_optimization_okay :
      answer1 = semantics of program1 ->
answer2 = semantics of program2 ->
answer1 = answer2.
 *)*)
