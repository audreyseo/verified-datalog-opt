From Coq Require Import  List String Arith Psatz DecidableTypeEx OrdersEx Program.Equality FMapList MSetWeakList.

From VeriFGH Require Import OrdersFunctor StringOrders DatalogProps.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.

Import RelDec.
(* Module RelTotalTransitiveBool <: Orders.TotalTransitiveLeBool'. *)
(* Include RelDec. *)
Definition rel_type_leb (rt1 rt2: rel_type) :=
  match rt1, rt2 with
  | idb, edb => false
  | _, _ => true
  end.

Module String_TTLB := Orders.OTF_to_TTLB(String_OTF).

Definition String_as_OT_leb (s1 s2: String_as_OT.t) :=
  String.leb s1 s2.

Section LebRel.
  Program Definition temp (r1 r2: rel) :=
    match Nat.eq_dec (num_args r1) (num_args r2) with
    | left H =>
        (Vector.fold_left2
           (fun acc elmt1 elmt2 =>
              andb acc
                   (String_as_OT_leb elmt1 elmt2))
           true
           (args r1)
           (args r2))
    | _ => false
    end.

  Definition leb (r1 r2: rel) :=
    andb
      (String.leb (name r1) (name r2))
      (andb
         (Nat.leb (num_args r1) (num_args r2))
         (andb (
              (
                let eq' := Nat.eq_dec (num_args r1) (num_args r2) in
                let argrr2' :=
                  (fun H Heq_anonymous =>
                     (eq_rect
                        (num_args r2)
                        (fun H0 : nat => Vector.t String_as_OT.t H0)
                        (args r2)
                        (num_args r1)
                        ((fun r3 r4 : rel =>
                            let NumArgsEq0 := Nat.eq_dec (num_args r3) (num_args r4) in
                            fun (H0 : num_args r3 = num_args r4)
                              (_ : left H0 = NumArgsEq0) =>
                              (fun (r1 r2 : rel)
                                 (H : num_args r1 = num_args r2) =>
                                 eq_sym H)
                                r3 r4 H0)
                           r1
                           r2 H Heq_anonymous))) in
                match eq' as eq'' return (eq'' = eq' -> bool) with
                | left H =>
                    (* fun (H : num_args r1 = num_args r2) *)
                    (fun (Heq_anonymous : left H = eq') =>
                       Vector.fold_left2
                         (fun (acc : bool) (elmt1 elmt2 : String_as_OT.t) =>
                            (acc && String_as_OT_leb elmt1 elmt2)%bool)
                         true 
                         (args r1)
                         (argrr2' H Heq_anonymous))
                | right n =>
                    (fun _ => false)
                end) eq_refl)
               (rel_type_leb (rtype r1) (rtype r2)))).

  
  
  Lemma rel_type_dec :
    forall (r1 r2: rel_type),
      {r1 = r2} + {r1 <> r2}.
  Proof.
    destruct r1, r2; try (right; congruence); left; congruence.
  Defined.

  
  Definition is_edb (r: rel) :=
    if rel_type_dec (rtype r) edb then true
    else false.

  Variant ground_types : Set :=
    | NAT (n: nat)
    | STR (s: string).
End LebRel.

(* Lemma leb_total : forall x y, leb x y \/ leb y x. *)
(* Proof. *)
  

(*   Lemma leb_trans : Transitive leb. *)

(*   Definition t := t. *)


(* End RelTotalTransitiveBool. *)
