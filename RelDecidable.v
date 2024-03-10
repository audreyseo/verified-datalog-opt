 From Coq Require Import  List String Arith Psatz DecidableTypeEx OrdersEx Program.Equality FMapList MSetWeakList.

From VeriFGH Require Import OrdersFunctor DatalogProps OrderedGroundTypes GroundMaps.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.


Section RelDec.
  Hypothesis (r1 r2: rel).

  Lemma rel_dec :
    { r1 = r2 } + { r1 <> r2 }.
  Proof.
    destruct r1, r2.
    destruct (String_as_OT.eq_dec name name0); try (right; congruence).
    destruct (list_eq_dec (String_GT_OT.eq_dec) grounded_args grounded_args0); try (right; congruence).
    destruct (Nat.eq_dec num_args num_args0); try (right; congruence).
    subst num_args0.
    destruct (list_eq_dec (OrdersEx.String_as_OT.eq_dec) args_list args_list0); try (right; congruence).
    destruct (Vector.eq_dec _ _ String_as_OT.eqb_eq _ args args0); try (subst; right; congruence).
    - subst.
      destruct rtype, rtype0; try (right; congruence).
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
