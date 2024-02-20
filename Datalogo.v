From VeriFGH Require Import OrderedSemiring.
From Coq Require Import Structures.Equalities List ListSet Logic.FinFun String Vector Vectors.VectorEq Program.Equality Program.Program.
(*
Module Type Semiring.
  Parameter t: Type.
End Semiring.

(* D is the domain *)
Module Datalog (D: HasEqDec) (Se: Semiring).

  (* Kinda like inductive but flat *)
  Variant rel_type :=
    | Edb
    | Idb.

  Definition mset (A: Set): Type := A -> bool.

  Definition is_mem {A: Set} (M: mset A) (a: A) := M a = true.

  Inductive subset (A: Set) : Type :=
  | set_of_everything
  | set_of_nothing
  | set_includes (a: A) (s: subset A)
  | set_excludes (a: A) (s: subset A).

  Fixpoint subset_mem {A: Set} (adec: forall (a1 a2: A), {a1 = a2} + {a1 <> a2}) (s: subset A) (a: A) :=
    match s with
    | set_of_everything _ => true
    | set_of_nothing _ => false
    | set_includes _ a' s' =>
        if adec a a' then true else subset_mem adec s' a
    | set_excludes _ a' s' =>
        if adec a a' then false else subset_mem adec s' a
    end.
        
  
    (* make_subset *)
    (*   { *)
    (*     subset_mem :> mset A; *)
    (*   }. *)

  (* Structure finset : Type := *)
  (*   make_finset *)
  (*     { *)
  (*       A:> Set; *)
  (*       seq_A : list A; *)
  (*       seq_listing: Listing seq_A; *)
  (*     }. *)

  Print In.

  Structure myset: Type :=
    make_myset
      {
        A :> Set;
        myset_mem :> mset A;
      }.

  Structure finsubset (A: Set) (adec: forall (a1 a2: A), {a1 = a2} + {a1 <> a2}) :=
    make_finsubset
      {
        S' :> subset A;
        subset_seq : list A;
        subset_seq_in: forall s, subset_mem adec S' s=true <-> List.In s subset_seq;
        subset_seq_nodup : NoDup subset_seq;
      }.

  
  Structure vars := make_vars {
                       seq_vars : list string;
                       seq_listing : Listing seq_vars;
                     }.

  
  Check Vector.eq_dec.
  Example exists_ex :
    exists n, n = 2.
  Proof.
    exists 2.
    reflexivity.
  Defined.

  Inductive exists_pred: nat -> Type :=
  | exists_pred2 :
    exists_pred 2
  | exists_pred_intro :
    forall n,
      exists_pred n ->
      exists_pred (S n).

  Print exists_ex.
  Fixpoint kth_car_prod (T: Type) (k: nat) (H: exists_pred k) :=
    match H with
    | exists_pred2 => prod T T
    | exists_pred_intro n H' => prod T (kth_car_prod T n H')
    end.
    
  (* An atom -- a relation, with an arity, applied to variables *)
  Structure rel := make_rel
                     {
                       name: string;
                       rel_vars: vars;
                       rt: rel_type;
                       arity: nat;
                       domain: Set;
                       domain_dec : forall (d1 d2: domain), {d1 = d2} + {d1 <> d2};
                     }.

  Inductive rule_body: Type :=
  | empty_body
  | and_body (hd: rel) (rst: rule_body).

  Variant rule: Type :=
    | rule_def (R: rel) (Body: rule_body)
    | rule_def_exists (R: rel) (x: string) (Body: rule_body).

  Structure s_rel (k: nat) :=
    make_s_rel
      {
        value_space: Se.t;
        key_space: Set;
        map_fun : Vector.t key_space k -> Se.t;
      }.

  Definition size_ok (r: rel) :=
    (arity r) = (List.length (seq_vars (rel_vars r))).

  Structure wf_rel := make_wf_rel
                        {
                          wfrel_rel :> rel;
                          wf: size_ok wfrel_rel;
                        }.
  
  Definition nth_var (r: rel) (n: nat) :=
    nth_error (seq_vars (rel_vars r)) n.

  Definition has_var (r: rel) (v: string) :=
    List.fold_left (fun acc v' => orb acc (String.eqb v' v)) (seq_vars (rel_vars r)) false.

  
  
                         

  

  
               
             
                       
*)
