(* An example of a simple datalog program using our formalization. *)
From Coq Require Import List String Arith Psatz.

From VeriFGH Require Import DatalogProps DatalogSemantics.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.


Import RelSemantics.

Module GroundingNotation.
  Coercion NAT : nat >-> ground_types.
  Coercion STR : string >-> ground_types.
End GroundingNotation.


Module SimpleProgram.
  Import GroundingNotation.

  Section RelDecls.

  (* Some helpful notation... *)
    Declare Scope rel_scope.
    Delimit Scope rel_scope with rel.

    Notation "{ r :- }" := (rule_def_empty r) : rel_scope.
    Notation "{ r :- x } " := (rule_def r (x :: nil)) : rel_scope.
    Notation "{ r :- x ; y ; .. ; z }" := (rule_def r (cons x (cons y .. (cons z nil) ..))) : rel_scope.

    Local Open Scope rel_scope.

    Declare Scope string_sets_scope.
    Delimit Scope string_sets_scope with ssets.
    Notation "'s{' x '}s'" := (string_sets.add x string_sets.empty) : string_sets_scope.
    Notation "'s{' x ; y ; .. ; z '}s'" := (string_sets.add x (string_sets.add y .. (string_sets.add z string_sets.empty) ..)) : string_sets_scope.

  (* 
    We would like to represent the following programs:

    Program 1
    R(a, b) :- T(a, b, c)
    S(a) :- R(a, b)

    Program 2
    S(a) :- T(a, b, c)

    Note that these are equivalent programs.
   *)
   
   (* First, we construct the T, R, and S relations. *)
   (* We must define the name of the relation, its variables,
    and whether it is an EDB or an IDB. *)
    Let Tabc := mk_rel "T" ("a" :: "b" :: "c" :: nil) edb.
    Let Rab := mk_rel "R" ("a" :: "b" :: nil) idb.
    Let Sa := mk_rel "S" ("a" :: nil) idb.

    (* Now, we construct our two programs. We can use the notation defined
    above - this is sugar for [rule_def]. *)

    (* Program 1 *)
    Let Rab_rule1 := { Rab :- Tabc }.
    Let Sa_rule1 := { Sa :- Rab }.

    (* Program 2 *)
    Let Sa_rule2 := { Sa :- Tabc }.

    Definition program1 :=
      DlProgram s{ "R"; "S" }s%ssets
                s{ "T" }s%ssets
                Sa
                (Rab_rule1 :: Sa_rule1 :: nil).

    Definition program2 :=
      DlProgram s{ "S" }s%ssets
                s{ "T" }s%ssets
                Sa
                (Sa_rule2 :: nil).


    (* Now we define the initial ground values in the database. 
    This adds the tuples (1, 2, 3) and (5, 6, 7) to T and initializes S and R as empty. *)
    Let G := MoreOrders.ground_maps.add "T" ( ( STR "1" :: STR "2" :: STR "3" :: nil)
                                                     ::
                                            (STR "5" :: STR "6" :: STR "7" :: nil) :: nil)
                                            (MoreOrders.ground_maps.empty (list (list ground_types))).
    Let G' := MoreOrders.ground_maps.add "S" nil G.
    Let G'' := MoreOrders.ground_maps.add "R" nil G'.

    (* Now we can evaluate our programs on the values in the ground maps. *)
    Let meaning1 := program_semantics_eval G'' program1 3.
    Eval compute in meaning1. 

    Let meaning2 := program_semantics_eval G' program2 3.
    Eval compute in meaning2. 

    (* This is a helper function to  *)
    Let find_meaning (m: option gm_type) x := match m with
    | Some m' => MoreOrders.ground_maps.find x m'
    (* option_map (@MoreOrders.ground_maps.this (list (list ground_types))) (MoreOrders.ground_maps.find x m') *)
    | None => None
    end.

    Eval compute in (find_meaning meaning1 "T").

    (* This is what we would need to prove to show these programs are identical *)
    Import MoreOrders.
    Lemma simple_programs_same :
            forall (fuel: nat) (g g' g'': gm_type),
              ground_maps.In "T" g ->
              ground_maps.find "R" g = Some nil ->
              ground_maps.find "S" g = Some nil ->
              Some g' = RelSemantics.program_semantics_eval g program1 fuel ->
              exists fuel',
                Some g'' = RelSemantics.program_semantics_eval g program2 fuel' ->
                forall (v v' : list (list ground_types)) (x : list ground_types),
                  ground_maps.find "S" g' = Some v ->
                  ground_maps.find "S" g'' = Some v' ->
                  In x v <-> In x v'.
          Proof. Admitted.
