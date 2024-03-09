From Coq Require Import List String.


Definition option_map_map {A' B' C': Type} (f: A' -> B' -> C') (a: option A') (b: option B') : option C' :=
  match a, b with
  | Some a', Some b' => Some (f a' b')
  | _, _ => None
  end.
