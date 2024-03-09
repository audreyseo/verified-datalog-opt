From Coq Require Import  List String Arith Psatz DecidableTypeEx OrdersEx Program.Equality FMapList FMapWeakList MSetWeakList Lists.ListSet.

From VeriFGH Require Import DatalogSemantics.
From VeriFGH Require Import OrdersFunctor DatalogProps StringOrders RelOrdered OrderedGroundTypes GroundMaps RelDecidable.

Require Export MonotoneOpSemanticsTheorems HelperTactics.

Import RelSemantics.


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
           eauto.
           simpl in H6.
           rewrite <- H6 in X1.
           invs X1. eauto.
           eauto.
        -- simpl in H6. rewrite <- H6 in X1.
           congruence.
      * eapply monotone_op_semantics_adequacy in H4. rewrite X in H4.
        invs H4.        
        some_is_not_none.
    + eapply monotone_op_semantics_adequacy in H4.
      some_is_not_none.
Qed.

(* States of reaching fixpoint:
     have fuel -> run another iter -> maps are the same -> end
                                   -> maps are not the same -> continue
     don't have fuel -> fail


 *)
