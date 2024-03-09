(* Example of Transitive Closure Datalog Program *)
From Coq Require Import List String Arith Psatz.

From VeriFGH Require Import DatalogProps DatalogSemantics GroundMaps.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.


Import RelSemantics.

Module GroundingNotation.
  Coercion NAT : nat >-> ground_types.
  Coercion STR : string >-> ground_types.
End GroundingNotation.


Module TransitiveClosureProgram.
  Import GroundingNotation.

  Section RelDecls.


    (* We want to represent the following programs:

        P1:
        T(x,y) :- R(x,y)
        T(x,y) :- T(x,z),R(z,y)
        A(y) :- T('1',y)

        P2:
        A(y) :- R('1',y)
        A(y) :- A(x), R(x,y)

        Both of them computes all nodes that can be reached by '1'

     *)


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
      Here we construct R T A relations.
      We include relation name, its variables, and relation types (idb/edb).
    *)
    Let R x y := mk_rel "R" (x :: y :: nil) edb.
    Let T x y := mk_rel "T" (x :: y :: nil) idb.
    Let A x := mk_rel "A" (x :: nil) idb.

    Let Txy := T "x" "y".
    Let Txz := T "x" "z".
    Let Rxy := R "x" "y".
    Let Rzy := R "z" "y".
    Let Ax := A "x".
    

    (* Program 1 *)
    (* 
        Here is the first program 
        T(x,y) :- R(x,y)
        T(x,y) :- T(x,z), R(z,y)
        A(y) :- T('1',y)
        Note that the construction is a bit different for Ay since there is an
        addtional argument that x == "1".
    *)
    Let Txy1 := { Txy :- Rxy }.
    Let Txy2 := { Txy :- Txz ; Rzy }.
    Let Ay := { (A "y") :- (mk_rel_ground "T" ("x" :: "y" :: nil) (("x", STR "1") :: nil) idb ) }.

    Eval compute in Txy1.
    Eval compute in Txy2.
    Eval compute in Ay.

    Definition program1 :=
      DlProgram s{ "T" }s%ssets                 (* idb(s) *)
                s{ "R" }s%ssets                 (* edb(s) *)
                (A "y")                         (* answer *)
                (Txy1 :: Txy2 :: Ay :: nil).    (* rules *)

    Eval compute in program1.




    (* Program 2 *)
    (*
        Here is the second program
        A(y) = R('1',y)
        A(y) = A(x), R(x,y)
    *)
    Let Ay1 := { (A "y") :- (mk_rel_ground "R" ("x" :: "y" :: nil) (("x", STR "1") :: nil) edb) }.
    Let Ay2 := { (A "y") :- Ax; Rxy }.

    Eval compute in Ay1.
    Eval compute in Ay2.

    Definition program2 :=
      DlProgram s{ "A" }s%ssets         (* idb(s) *)
                s{ "R" }s%ssets         (* edb(s) *)
                (A "y")                 (* answer *)
                (Ay1 :: Ay2 :: nil).    (* rules *)

    (* 
        Let's try a small example.
        R =
        |  (1 , 2)  |
        |  (1 , 3)  |
        
        T and A are initialized to be empty
    *)
    Let G := GroundMaps.ground_maps.add "R" ( ( STR "1" :: STR "2":: nil)
                                                     ::
                                                     (STR "1" :: STR "3" :: nil) :: nil) (GroundMaps.ground_maps.empty (list (list ground_types))).

    Let G' := GroundMaps.ground_maps.add "T" nil G.
    Let G1 := GroundMaps.ground_maps.add "A" nil G'. (* ground map for program 1 *)
    Let G2 := GroundMaps.ground_maps.add "A" nil G.  (* ground map for program 2 *)


    (* Represent rules of program 1 as monotone operations *)
    Let monotones1 := Eval compute in rules_to_monotone_op (rules program1).
    Print monotones1.

    Let find_meaning (meaning: option gm_type) x := match meaning with
                            | Some m => ground_maps.find x m
                            | None => None
                                                      end.

    Let meaning1 := Eval compute in program_semantics_eval_without_fixpoint G1 program1 1.
    Print meaning1.

    Let A1_meaning := Eval compute in find_meaning meaning1 "A".
    Print A1_meaning.

    
    (* Represent rules of program 2 as monotone operations *)
    Let monotones2 := Eval compute in rules_to_monotone_op (rules program2).
    Print monotones2.

    Let meaning2 := Eval compute in program_semantics_eval_without_fixpoint G2 program2 1.
    Print meaning2.

    Let A2_meaning := Eval compute in find_meaning meaning2 "A".
    Print A2_meaning.
    
    Import GroundMaps.

    Lemma transitive_closure_same :
      forall (fuel: nat) (g g' g'': gm_type),
        ground_maps.In "R" g ->
        ground_maps.find "A" g = Some nil ->
        ground_maps.find "T" g = Some nil ->
        Some g' = RelSemantics.program_semantics_eval g program1 fuel ->
        exists fuel',
          Some g'' = RelSemantics.program_semantics_eval g program2 fuel' ->
          ground_maps.Equal g' g''.
    Proof.
