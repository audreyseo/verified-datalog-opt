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

Ltac destruct_match_goal' :=
  match goal with
  | [ |- ?a = match ?x with
             | Some _ => _
             | None => None
             end ] =>
      let freshX := fresh "X" in
      destruct (x) eqn:freshX
  end.
