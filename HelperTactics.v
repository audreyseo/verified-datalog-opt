From Coq Require Import List Lists.ListSet.
From VeriFGH Require Import BaseUtils.
Local Open Scope list_scope.

Ltac destruct_hyp_match :=
  match goal with
  | [H: Some _ = match ?x with | Some _ => _ | None => None end |- _ ] =>
      let Xfresh := fresh "X" in
      destruct (x) eqn:Xfresh; inversion H
  end.

Ltac destruct_goal_match :=
  match goal with
  | [ |- Some _ = match ?x with | Some _ => _ | None => None end ] =>
      let Xfresh := fresh "X" in
      destruct (x) eqn:Xfresh; subst
  end.

Ltac invs H :=
  inversion H; subst.

Ltac invc H :=
  inversion H; clear H; subst.

Ltac destruct_match_goal' :=
  match goal with
  | [ |- ?a = match ?x with
             | Some _ => _
             | None => None
             end ] =>
      let freshX := fresh "X" in
      destruct (x) eqn:freshX
  end.

Ltac app_of_options :=
  match goal with
  | [ |- context G [Some (?a ++ ?b)] ] =>
      let Atype := type of a in
      match Atype with
      | list ?A =>
          let G' := context G[option_map_map (@app A) (Some a) (Some b)] in
          change G'
      | set ?A =>
          let G' := context G[option_map_map (@app A) (Some a) (Some b)] in
          change G'
      end
  | [ H: context G [Some (?a ++ ?b)] |- _ ] =>
      let Atype := type of a in
      match Atype with
      | list ?A =>
          let G' := context G[option_map_map (@app A) (Some a) (Some b)] in
          change G'
      | set ?A =>
          let G' := context G[option_map_map (@app A) (Some a) (Some b)] in
          change G'
      end
  end.

Ltac some_is_not_none :=
  (* First we normalize direction, and get rid of anything that is dumb *)
  repeat (match goal with
          | [ H: Some ?a = Some ?b |- _ ] =>
              invc H
          | [ H: Some ?a = ?b |- _ ] =>
              symmetry in H
          | [ H: None = ?c |- _ ] =>
              symmetry in H
          | [ H: ?a = ?a |- _ ] =>
              clear H
          end);
  match goal with
  | [ H: ?a = Some _, H': ?a = None |- _ ] =>
      rewrite H' in H; congruence
  end.

Ltac negate_negated H :=
                let Ht := type of H in
                match Ht with
                | ~ ?y =>
                    let Y := fresh "Y" in
                    assert (Y: y)
                end.

Ltac destruct_any_match_in_goal :=
  match goal with
  | [ |- context G [match ?a with | Some _ => _ | None => _ end ] ] =>
      let A := fresh "A" in
      destruct (a) eqn:A; try congruence
  end.
