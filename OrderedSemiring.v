Require Import Coq.Relations.Relation_Definitions String Psatz Arith Bool List ZArith Coq.Init.Datatypes Nat.

Definition less_eq_general (X: Type) (op: X -> X -> X) : relation X :=
  fun x => fun y => exists (z: X), op x z = y.

Record PreSemiRing : Type := mkPreSemiRing {
    T: Type;
    op1: T -> T -> T where "a + b" := (op1 a b);
    op2: T -> T -> T where "a * b" := (op2 a b);
    assoc1: forall a b c, a + (b + c) = (a + b) + c;
    assoc2: forall a b c, a * (b * c) = (a * b) * c;
    comm: forall a b, a + b = b + a;
    distr: forall a b c, a * (b + c) = a * b + a * c;
    zero: T;
    zero_identity: forall a, a + zero = a /\ zero + a = a;
    one: T;
    one_identity: forall a, a * one = a /\ one * a = a;
    leq: relation T;
    partial_order: order T leq
}.


Check PreSemiRing.

Inductive binary: Type :=
| Zero
| One.

Definition bor (x y: binary): binary :=
    match x with
    | One => One
    | Zero => y
    end.

Definition band (x y: binary): binary :=
    match x with
    | Zero => Zero
    | One => y
    end.

Lemma assoc1_binary:
  forall (a b c: binary),
  bor a (bor b c) = bor (bor a b) c.
Proof.
  intros; destruct a; destruct b; destruct c; eauto.
Qed.

Lemma assoc2_binary:
  forall (a b c: binary),
  band a (band b c) = band (band a b) c.
Proof.
  intros; destruct a; destruct b; destruct c; eauto.
Qed.

Lemma comm_binary: 
  forall (a b: binary),
  bor a b = bor b a.
Proof.
    intros; destruct a; destruct b; eauto.
Qed.


Lemma distr_binary:
  forall (a b c: binary),
  band a (bor b c) = bor (band a b) (band a c).
Proof.
    intros; destruct a; destruct b; eauto.
Qed.

Lemma eq_zero_binary:
  forall (a: binary),
  band a Zero = Zero.
Proof.
  intros; destruct a; eauto.
Qed.

Lemma order_leq_binary:
  order binary (less_eq_general binary bor).
Proof.
  econstructor.
  - econstructor. destruct x; eauto. econstructor.
  - econstructor; destruct x; destruct z. econstructor. eauto. 
    destruct y.  inversion H; eauto. inversion H0; eauto. eauto.
  - unfold antisymmetric; intros; destruct x; destruct y; eauto.
    inversion H0. simpl in H1; eauto. inversion H. simpl in H1; eauto.
Qed.

Lemma zero_identity_binary:
  forall (a: binary),
  bor a Zero = a /\ bor Zero a = a.
Proof.
  destruct a; eauto.
Qed.

Lemma one_identity_binary:
  forall (a: binary),
  band a One = a /\ band One a = a.
Proof.
  destruct a; eauto.
Qed.
    

Definition binary_presemiring := 
{| T := binary
; op1 := bor
; op2 := band
; assoc1 := assoc1_binary
; assoc2 := assoc2_binary
; comm := comm_binary
; distr := distr_binary
; zero := Zero
; zero_identity := zero_identity_binary
; one := One
; one_identity := one_identity_binary
; leq := (less_eq_general binary bor)
; partial_order := order_leq_binary
|}
.

Inductive closed_nat: Type :=
| Inf
| Nat (n: nat).

Definition nat_plus (n1 n2: closed_nat) : closed_nat :=
  match (n1, n2) with
  | (Inf, _) => Inf
  | (_, Inf) => Inf
  | (Nat a, Nat b) => Nat (a + b)
  end.

Definition nat_times (n1 n2: closed_nat) : closed_nat :=
  match (n1, n2) with
  | (Inf, _) => Inf
  | (_, Inf) => Inf
  | (Nat a, Nat b) => Nat (a * b)
  end.

Lemma assoc_plus_nat:
forall (a b c: closed_nat),
nat_plus a (nat_plus b c) = nat_plus (nat_plus a b) c.
Proof.
intros; destruct a; destruct b; destruct c; eauto.
unfold nat_plus. f_equal; lia.
Qed.

Lemma assoc_times_nat:
forall (a b c: closed_nat),
nat_times a (nat_times b c) = nat_times (nat_times a b) c.
intros; destruct a; destruct b; destruct c; eauto.
unfold nat_times. f_equal; lia.
Qed.

Lemma comm_nat: 
forall (a b: closed_nat),
  nat_plus a b = nat_plus b a.
Proof.
  destruct a; destruct b; eauto.
  unfold nat_plus; f_equal; lia.
Qed.

Lemma distr_nat:
forall (a b c: closed_nat),
  nat_times a (nat_plus b c) = nat_plus (nat_times a b) (nat_times a c).
Proof.
intros; destruct a; destruct b; destruct c; eauto. 
unfold nat_times; unfold nat_plus; simpl; f_equal; lia.
Qed.

Lemma zero_identity_nat:
forall (a: closed_nat),
  nat_plus a (Nat 0) = a /\ nat_plus (Nat 0) a = a.
Proof.
  destruct a; unfold nat_plus; eauto.
Qed.

Lemma one_identity_nat:
forall (a: closed_nat),
  nat_times a (Nat 1) = a /\ nat_times (Nat 1) a = a.
Proof.
  destruct a; unfold nat_times; split; f_equal; eauto; lia.
Qed.

Lemma order_leq_nat:
order closed_nat (less_eq_general closed_nat nat_plus).
Proof.
  econstructor.
  - intro. exists (Nat 0). destruct x; eauto. unfold nat_plus; eauto.
  - unfold transitive; intros. inversion H; inversion H0. 
    exists (nat_plus x0 x1). erewrite assoc_plus_nat. rewrite H1; eauto.
  - unfold antisymmetric. intros. inversion H; inversion H0. 
    destruct x; destruct y; eauto. unfold nat_plus in H1. 
    destruct x0. discriminate H1. inversion H1. unfold nat_plus in H2.
    destruct x1. discriminate H2. inversion H2. f_equal. lia.
Qed.
  

Definition closed_nat_presemiring := 
  {| T := closed_nat
  ; op1 := nat_plus
  ; op2 := nat_times
  ; assoc1 := assoc_plus_nat
  ; assoc2 := assoc_times_nat
  ; comm := comm_nat
  ; distr := distr_nat
  ; zero := Nat 0
  ; zero_identity := zero_identity_nat
  ; one := Nat 1
  ; one_identity := one_identity_nat
  ; leq := (less_eq_general closed_nat nat_plus)
  ; partial_order := order_leq_nat
  |}.


Local Open Scope nat_scope.

Fixpoint type_mul (D: Type) (n: nat) : Type :=
  match n with
  | 0 => D
  | S m => D * (type_mul D m)
  end.


Definition SRelation (D: Type) (num: nat) (ring: PreSemiRing): Type := 
  (type_mul D num) -> (T ring).

Definition product (ring: PreSemiRing) (ls: list (T ring)): (T ring) :=
  fold_left (op2 ring) ls (one ring).

Definition sum (ring: PreSemiRing) (ls: list (T ring)): (T ring) :=
  fold_left (op1 ring) ls (zero ring).

Definition sum_product (ring: PreSemiRing) (ls: list (list (T ring))): (T ring) :=
  sum ring (map (product ring) ls). 

