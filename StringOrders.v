From Coq Require Import OrdersEx DecidableTypeEx String List Arith.


Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.


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
  End StringLe.

  Lemma ascii_compare_eq :
    forall (a: Ascii.ascii),
      Ascii_as_OT.compare a a = Eq.
  Proof.
    intros.
    destruct a. destruct b, b0, b1, b2, b3, b4, b5, b6; simpl; reflexivity.
  Defined.
  

  Lemma ordered_type_string_lt :
    forall (x y: string),
      OrderedTypeEx.String_as_OT.lt x y <->
        String_as_OT.lt x y.
  Proof.
    induction x; intros; split; intros.
    - unfold String_as_OT.lt. simpl. inversion H. reflexivity.
    - unfold String_as_OT.lt in H. unfold OrderedTypeEx.String_as_OT.lt.
      destruct y; simpl in *.
      inversion H. econstructor.
    - inversion H; subst.
      + unfold String_as_OT.lt. simpl. rewrite ascii_compare_eq.
        eapply IHx. eauto.
      + unfold String_as_OT.lt. simpl.
        (* rewrite String_OTF.ascii_compare_same_as_ascii_ot_compare. *)
        eapply OrderedTypeEx.Ascii_as_OT.cmp_lt_nat in H3.
        rewrite String_OTF.ascii_compare_same_as_ascii_ot_compare in *.
        rewrite H3. reflexivity.
    - destruct y. unfold String_as_OT.lt in H. simpl in H. inversion H.
      destruct (Ascii.compare a a0) eqn:C.
      + eapply OrderedTypeEx.Ascii_as_OT.cmp_eq in C. subst a.
        
        eapply OrderedTypeEx.String_as_OT.lts_tail. eapply IHx.
        unfold String_as_OT.lt in *. simpl in H.
        rewrite String_OTF.ascii_compare_same_as_ascii_ot_compare in H.
        rewrite ascii_compare_eq in H.
        rewrite H. reflexivity.
      + econstructor. eapply OrderedTypeEx.Ascii_as_OT.cmp_lt_nat.
        eassumption.
      + unfold String_as_OT.lt in H. simpl in H.
        destruct (Ascii_as_OT.compare a a0) eqn:C'; subst.
        rewrite String_OTF.ascii_compare_same_as_ascii_ot_compare in C'.
        rewrite C' in C. inversion C.
        rewrite String_OTF.ascii_compare_same_as_ascii_ot_compare in C'. congruence.
        rewrite String_OTF.ascii_compare_same_as_ascii_ot_compare in C'.
        inversion H.
  Defined.
End String_OTF.
