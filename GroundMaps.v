From Coq Require Import  List String Arith Psatz DecidableTypeEx OrdersEx Program.Equality FMapList FMapWeakList MSetWeakList Lists.ListSet.

From VeriFGH Require Import OrdersFunctor DatalogProps StringOrders OrderedGroundTypes.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.


Module Ground_Type_as_OT := Orders_to_OrderedType(Ground_Types_as_OTF).
Module String_as_OT := Orders_to_OrderedType(String_OTF).
Module List_Ground_Type_as_OTF := OrdersFunctor.List_as_OTF(Ground_Types_as_OTF).
Module List_List_Ground_Type_as_OTF := OrdersFunctor.List_as_OTF(List_Ground_Type_as_OTF).

Module List_Ground_Type_as_OT <: OrderedType.OrderedType.
  Module Inner := OrdersFunctor.List_as_OT(List_Ground_Type_as_OTF).
  Include Inner.

  Definition eqb l1 l2 :=
    if Inner.eq_dec l1 l2 then
      true
    else false.
End List_Ground_Type_as_OT.

(* The type of tuples with named columns *)
Definition tup_type : Type := list (string * ground_types).
Arguments tup_type /.
Definition tup_entry : Type := string * ground_types.
Arguments tup_entry /.

Definition tup_empty_set := @empty_set tup_type.
Arguments tup_empty_set /.
Definition tup_set: Type := ListSet.set tup_type.
Arguments tup_set /.

Module ground_maps := FMapWeakList.Make(String_as_OT).
(* (List_Ground_Type_as_OT). *)
Module str_gt_list_ot := List_as_OTF(String_GT_OT).

Definition gt_set_type := list (list ground_types).
Arguments gt_set_type /.

Definition gm_empty := ground_maps.empty gt_set_type.
Arguments gm_empty /.

Definition gm_type := ground_maps.t gt_set_type.

Arguments gm_type /.

