From octalgo Require Import syntax.
Print of_constant.
Print raw_gatom.

Print fintype.Finite.sort.
Print constant.
Print constype.

Print fintype.Finite.type.
From mathcomp.ssreflect Require Import seq.
From Coq Require Import String.
Local Open Scope string_scope.
From mathcomp Require Import all_ssreflect.

Definition symbols_seq: seq string := ([:: "R"; "V"; "T"; "Q"; "G"; "R'o"; "Q'o"; "Ro"; "Qo"]).

Print ssreflect.choice.

Lemma string_eqP :
  eqtype.Equality.axiom (String.eqb).
Proof.
  unfold eqtype.Equality.axiom.
  eapply String.eqb_spec.
Qed.

Print Finite.Mixin.

(* Module CountableStrings. *)


(*   Lemma ascii_list_inverse : *)
(*     forall (l: list Ascii.ascii), *)
(*       (List.map Ascii.ascii_of_nat *)
(*                 (List.map Ascii.nat_of_ascii l)) = l. *)
(*   Proof. *)
(*     induction l; simpl; intros. *)
(*     - reflexivity. *)
(*     - rewrite Ascii.ascii_nat_embedding. f_equal. assumption. *)
(*   Qed. *)

(*   Lemma ascii_list_bijection2 : *)
(*     forall (l: list nat), *)
(*       (List.map Ascii.nat_of_ascii *)
(*                 (List.map Ascii.ascii_of_nat l)) = l. *)
(*   Proof. *)
(*     induction l; simpl; intros. *)
(*     - reflexivity. *)
(*     - rewrite Ascii.nat_ascii_embedding. f_equal. *)
  
(*   Lemma string_pickle : *)
(*     cancel pickle unpickle. *)
(*   Proof. *)
(*     unfold cancel. unfold pickle. unfold unpickle. *)
(*     pose proof (CodeSeq.codeK). *)
(*     unfold cancel in H. intros. rewrite H. *)
(*     rewrite ascii_list_inverse. eapply string_list_bijection1. *)
(*   Qed. *)

(*   Lemma string_unpickle : *)
(*     cancel unpickle pickle. *)
(*   Proof. *)
(*     unfold cancel. unfold pickle, unpickle. *)
(*     intros. rewrite string_list_bijection2. *)

Module AsciiChoice.
  Definition ascii_to_bool_seq (a: Ascii.ascii) :=
    match a with
    | Ascii.Ascii b1 b2 b3 b4 b5 b6 b7 b8 =>
        [:: b1; b2; b3; b4; b5; b6; b7; b8]
    end.

  Definition bool_seq_to_ascii (b: seq bool) : option (Ascii.ascii) :=
    match b with
    | [:: b1; b2; b3; b4; b5; b6; b7; b8] =>
        Some (Ascii.Ascii b1 b2 b3 b4 b5 b6 b7 b8)
    | _ => None 
    (* | [ :: ] => None *)
    (* | [ :: b1 & b' ] => *)
        (* match b' with *)
        (* | [ :: ] => None *)
        (* | [ :: b2 & b'' ] => *)
            (* match b'' with *)
            (* | [ :: ] => None *)
            (* | [ :: b3 & b''' ] => *)
                (* match b''' with *)
                (* | [ :: ] => None *)
    end.

  Lemma ascii_cancel :
      pcancel ascii_to_bool_seq bool_seq_to_ascii.
  Proof.
   unfold pcancel, ascii_to_bool_seq, bool_seq_to_ascii.
   intros.
   destruct x. reflexivity.
  Qed.

  (* Print ssreflect.choice. *)
  (* Print ssreflect.choice.Choice. *)

  (* Print Choice.class_of. *)
  (* Definition bool_choice_class := Choice.Class bool_eqMixin bool_choiceMixin. *)
  

  (* Definition bool_seq_choice_mixin := Choice.Class (seq_eqMixin bool) (seq_choiceType *)

  Definition bool_seq_mixin := seq_choiceMixin (bool_choiceType).
  Definition bool_seq_eq_mixin := seq_eqMixin (bool_eqType).
  Canonical bool_seq_choiceType := @Choice.Class (seq bool) bool_seq_eq_mixin bool_seq_mixin.

  Definition bool_seq_countable_mixin := seq_countMixin (bool_countType).
  Definition bool_seq_count_class := Countable.Class bool_seq_choiceType bool_seq_countable_mixin.

  Canonical bool_seq_countType := Countable.Pack bool_seq_count_class.
  
                                                   

  
  
  Definition ascii_has_choice := ssreflect.choice.PcanChoiceMixin ascii_cancel.
  Print ascii_has_choice.

  Lemma ascii_eqP :
    Equality.axiom Ascii.eqb.
  Proof.
    unfold Equality.axiom. eapply Ascii.eqb_spec.
  Qed.

  Definition ascii_eqMixin := Equality.Mixin ascii_eqP.
  Definition ascii_choiceClass := @Choice.Class (Ascii.ascii) ascii_eqMixin ascii_has_choice.
  
  Canonical Structure ascii_choiceType := @Choice.Pack (Ascii.ascii) ascii_choiceClass.

  Definition ascii_seq_choiceMixin := seq_choiceMixin (ascii_choiceType).
  Canonical ascii_eqType := @Equality.Pack Ascii.ascii ascii_eqMixin.
  Definition ascii_seq_eqMixin := seq_eqMixin (ascii_eqType).

  Definition ascii_seq_choiceClass := @Choice.Class (seq Ascii.ascii) ascii_seq_eqMixin ascii_seq_choiceMixin.

  Canonical Structure ascii_seq_choiceType := @Choice.Pack (seq Ascii.ascii) ascii_seq_choiceClass.
 
  Definition bool_seq_pickle := Countable.pickle bool_seq_countable_mixin.
  Definition bool_seq_unpickle := Countable.unpickle bool_seq_countable_mixin.
                                                     

  Definition ascii_to_nat a := bool_seq_pickle (ascii_to_bool_seq a).
  Definition nat_to_ascii a := obind bool_seq_to_ascii (bool_seq_unpickle a).

  Lemma ascii_count_cancel :
    pcancel ascii_to_nat nat_to_ascii.
  Proof.
    unfold pcancel. intros. destruct x. unfold nat_to_ascii. unfold ascii_to_nat.
    pose proof (Countable.pickleK).
    specialize (H _ bool_seq_countable_mixin).
    replace (Countable.pickle bool_seq_countable_mixin) with bool_seq_pickle in H by reflexivity.
    replace (Countable.unpickle bool_seq_countable_mixin) with bool_seq_unpickle in H by reflexivity.
    unfold pcancel in H.
    rewrite H.
    eapply ascii_cancel.
  Qed.
  

  Definition ascii_countable := Countable.Mixin ascii_count_cancel.

  Definition ascii_count_class := Countable.Class ascii_choiceClass ascii_countable.

  Canonical ascii_countType := Countable.Pack ascii_count_class.

    Fixpoint list_ascii_of_string (s: string): list Ascii.ascii :=
    match s with
    | EmptyString => nil
    | String a s' =>
        cons a (list_ascii_of_string s')
    end.

  Fixpoint string_of_list_ascii (l: list Ascii.ascii) : string :=
    match l with
    | nil => EmptyString
    | cons a s => String a (string_of_list_ascii s)
    end.
  
(*   Definition pickle c := *)
(*     CodeSeq.code (List.map Ascii.nat_of_ascii (list_ascii_of_string c)). *)

(*   Definition unpickle c := *)
(*     string_of_list_ascii (List.map Ascii.ascii_of_nat (CodeSeq.decode c)). *)

Lemma string_list_bijection1 :
  forall (s: string),
    string_of_list_ascii (list_ascii_of_string s) = s.
Proof.
  induction s; simpl; intros.
  - reflexivity.
  - f_equal. assumption.
Qed.

Lemma string_list_bijection2 :
  forall (l: list Ascii.ascii),
    list_ascii_of_string (string_of_list_ascii l) = l.
Proof.
  induction l; simpl; intros.
  - reflexivity.
  - f_equal. eauto.
Qed.

Lemma string_cancel :
  cancel string_of_list_ascii list_ascii_of_string.
Proof.
  unfold cancel.
  intros. induction x; simpl; intros.
  - reflexivity.
  - f_equal. assumption.
Qed.


  Definition string_to_nat a := (Countable.pickle (seq_countMixin (nat_countType))) (List.map (Countable.pickle ascii_countable) (list_ascii_of_string a)).
  Definition nat_to_string a :=
    option_map string_of_list_ascii (option_map (List.fold_right (fun i acc => match i with
                              | Some i' => i' :: acc
                              | None => acc
                                                                            end) nil) (option_map (List.map (Countable.unpickle ascii_countable)) ((Countable.unpickle (seq_countMixin (nat_countType))) a))).

  Lemma string_pcancel :
    pcancel string_to_nat nat_to_string.
  Proof.
    unfold pcancel. intros. unfold nat_to_string. unfold  string_to_nat.
    pose proof (Countable.pickleK (seq_countMixin nat_countType)).
    unfold pcancel in H. rewrite H.

    induction x; simpl. reflexivity.
    f_equal. simpl in IHx. inversion IHx.
    pose proof ascii_count_cancel. unfold pcancel in H0.
    rewrite H0. simpl. f_equal.
    rewrite string_list_bijection2.
    rewrite H1.
    assert (list_ascii_of_string x = List.fold_right (fun (i : option Ascii.ascii) (acc : seq Ascii.ascii) =>
             match i with
             | Some i' => i' :: acc
             | None => acc
             end) [::]
            (List.map nat_to_ascii
                      (List.map ascii_to_nat (list_ascii_of_string x)))).
    rewrite <- H1 at 1. rewrite string_list_bijection2. reflexivity.
    rewrite <- H2. rewrite <- H2. rewrite string_list_bijection1. reflexivity.
  Qed.

  Definition string_choiceClass := @Choice.class 

  Definition string_choiceMixin := @CanChoiceMixin (seq Ascii.ascii) (string) string_of_list_ascii list_ascii_of_string string_cancel.
  
  Definition string_countMixin := Countable.Mixin string_pcancel.
  Definition string_countClass := Countable.
  
End AsciiChoice.

Import AsciiChoice.





Countable.ChoiceMixin

Definition string_choiceMixin := @CanChoiceMixin (seq Ascii.ascii) (string) string_of_list_ascii list_ascii_of_string string_cancel.
                                              

Print ssreflect.choice.PcanChoiceMixin.


Print Countable.mixin_of.

Definition string_eqMixin := eqtype.Equality.Mixin string_eqP.
Canonical string_eqType := @eqtype.Equality.Pack string string_eqMixin.

Lemma symbols_seq_finite :
  fintype.Finite.axiom symbols_seq.
Proof.
  unfold fintype.Finite.axiom.
  move=> a.
  unfold symbols_seq.
  simpl.
  
