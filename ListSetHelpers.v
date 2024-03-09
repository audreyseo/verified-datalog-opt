From Coq Require Import Lists.ListSet.

Definition list_set_subset {T: Type} (v v': ListSet.set T) :=
  forall (x: T),
    set_In x v -> set_In x v'.
Arguments list_set_subset {T}%type_scope v v'/.

Definition list_set_equal {T: Type} (v v': ListSet.set T) :=
  forall (x: T),
    set_In x v <-> set_In x v'.
Arguments list_set_equal {T}%type_scope v v' /.

Lemma list_set_eq_refl {T: Type}:
  forall (v v': ListSet.set T),
    v = v' ->
    list_set_equal v v'.
Proof.
  intros. simpl. subst. split; intros; eauto.
Qed.
