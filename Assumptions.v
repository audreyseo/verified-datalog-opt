From VeriFGH Require Import GroundMaps.


(* I wouldn't normally admit something like this, but if we don't run into any really terrible things...this might make it a bit easier. *)
Axiom ground_maps_equality :
  forall (g g': gm_type),
    ground_maps.Equal g g' ->
    g = g'.
