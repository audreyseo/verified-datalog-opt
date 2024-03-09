From Coq Require Import Lists.ListSet.
From VeriFGH Require Import GroundMaps DatalogProps ListSetHelpers.


(* I wouldn't normally admit something like this, but if we don't run into any really terrible things...this might make it a bit easier. *)
Axiom ground_maps_equality :
  forall (g g': gm_type),
    ground_maps.Equal g g' ->
    g = g'.

Axiom string_sets_equality :
  forall (s1 s2: string_sets.t),
    string_sets.Equal s1 s2 ->
    s1 = s2.

Axiom list_set_equality :
  forall (T: Type) (x1 x2: set T),
    list_set_equal x1 x2 ->
    x1 = x2.
