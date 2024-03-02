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


Module TransitiveClosureProgram.
  Import GroundingNotation.

  Section RelDecls.
    Let R x y := mk_rel "R" (x :: y :: nil) edb.
    Let T x y := mk_rel "T" (x :: y :: nil) idb.
    Let A x := mk_rel "A" (x :: nil) idb.

    (* We want to encode the following programs:

P1:
t(x,y) = r(x,y)
t(x,y) = t(x,z),r(z,y)
a(y) = t('1',y)

P2:
a(y) = R('1',y)
a(y) = a(x),r(x,y)

     *)

    
