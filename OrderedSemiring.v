Require Import Coq.Relations.Relation_Definitions.

Definition less_eq_general (X: Type) (op: X -> X -> X) : relation X :=
  fun x => fun y => exists (z: X), op x z = y.

Record PreSemiRing : Type := mkPreSemiRing {
    S: Type;
    op1: S -> S -> S where "a + b" := (op1 a b);
    op2: S -> S -> S where "a * b" := (op2 a b);
    assoc1: forall a b c, a + (b + c) = (a + b) + c;
    assoc2: forall a b c, a * (b * c) = (a * b) * c;
    comm: forall a b, a + b = b + a;
    distr: forall a b c, a * (b + c) = a * b + a * c;
    zero: S;
    one: S;
    eq_zero: forall x, x * zero = zero;
    leq: relation S;
    partial_order: order S leq
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
    

Definition binary_presemiring := 
{| S := binary
; op1 := bor
; op2 := band
; assoc1 := assoc1_binary
; assoc2 := assoc2_binary
; comm := comm_binary
; distr := distr_binary
; zero := Zero
; one := One
; eq_zero := eq_zero_binary
; leq := (less_eq_general binary bor)
; partial_order := order_leq_binary
|}
.



Check comm binary_presemiring.
