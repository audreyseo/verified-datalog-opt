From Coq Require Import  List String Arith Psatz DecidableTypeEx OrdersEx Program.Equality FMapList MSetWeakList.

From VeriFGH Require Import OrdersFunctor.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.

Print String_as_OT.t.

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

