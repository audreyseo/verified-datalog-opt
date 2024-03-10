(*
 * This entire file is adapted from this gist:
 * https://gist.github.com/JoJoDeveloping/e44659128428a6bcd202585bb1b3a27f
 * by Johannes Matthias Hostert, with permission.
 *)

From Coq Require Import Arith Lia List.

Definition UIP (T:Type) := forall (x y:T) (H1 H2 : x = y), H1 = H2.

Definition sigma {X:Type} {x y : X} (H : x=y) : y=x := match H in (_=z) return z=x with eq_refl _ => eq_refl end.
Definition tau {X:Type} {x y z: X} (H1 : x=y) : y=z -> x=z := match H1 in (_=w) return w=z->x=z with eq_refl _ => fun H => H end.

(* A hedberg function yields a constant path if both arguments are equal
   (i.e. the output path does not depend on the input path)
   Usually these are constructed using an equalitiy decider.
   Here, we will do something different. *)
Definition is_hedberg (X:Type) (f : forall (x y:X), x=y -> x=y) :=
  forall x y H1 H2, f x y H1 = f x y H2.

(* Simple proof of UIP from existence of a Hedberg function.
   My version is due to Prof. Smolka's lecture notes: https://www.ps.uni-saarland.de/~smolka/drafts/icl_book.pdf (chapter 24),
   which cites Kraus et al @ TLCA 2013 as the original source *)
Lemma hedberg_to_UIP X f : is_hedberg X f -> UIP X.
Proof.
  intros H1 x y E1 E2.
  assert (forall (e:x=y), tau (f _ _ e) (sigma (f _ _ eq_refl)) = e) as Heq1.
  { intros e. destruct e. destruct (f x x eq_refl). easy. }
  rewrite <- (Heq1 E1).
  rewrite <- (Heq1 E2).
  rewrite (H1 x y E1 E2).
  reflexivity.
Qed.

(* by cleverly using constructor laws, we similarly gain a hedberg function for list *)
Lemma list_ctor_law1 (X:Type) (h1 h2 : X) (t1 t2 : list X) : (h1::t1) = (h2::t2) -> h1 = h2.
Proof. intros H; congruence. Qed.
Lemma list_ctor_law2 (X:Type) (h1 h2 : X) (t1 t2 : list X) : (h1::t1) = (h2::t2) -> t1 = t2.
Proof. intros H; congruence. Qed.
Lemma list_ctor_law3 (X:Type) (h1 h2 : X) (t1 t2 : list X) : h1 = h2 -> t1 = t2 -> (h1::t1) = (h2::t2).
Proof. intros H1 H2; congruence. Qed.

(* Our hedberg function. The key idea is extracting and recombining the equalities.
   This means that the intermediate equalities are all on X, which has UIP.
   Thus they are all equal, and their combination is also equal, yielding a hedberg function.
   See below for a formal proof *)
Fixpoint UIP_list_hedberg (X:Type) (l1 l2 : list X) : l1 = l2 -> l1 = l2.
Proof.
  destruct l1 as [|l1h l1t]; destruct l2 as [|l2h l2t]; intros Heq; try (exfalso; congruence).
  - reflexivity.
  - apply list_ctor_law3.
    + eapply list_ctor_law1, Heq.
    + eapply (UIP_list_hedberg _), list_ctor_law2, Heq.
Defined.

Lemma UIP_list_is_hedberg (X:Type) (Huip : UIP X) : is_hedberg _ (UIP_list_hedberg X).
Proof.
  intros x y; induction x as [|xh xr IH] in y|-*; destruct y as [|yh yr]; intros E1 E2; try (exfalso; congruence).
  - cbn. easy.
  - cbn.
    erewrite (Huip _ _ (list_ctor_law1 X xh yh xr yr E1)).
    erewrite (IH _ (list_ctor_law2 X xh yh xr yr E1)).
    reflexivity.
Qed.

Lemma UIP_to_list (T : Type) : UIP T -> UIP (list T).
Proof.
  intros H x y. eapply hedberg_to_UIP. apply (UIP_list_is_hedberg _ H).
Qed.

(* 
 * And we can use this for strings 
 *)

Module UIPAscii.
  Import Ascii.
  Lemma ascii_ctor_law1 (a1 a2 b1 b2 c1 c2 d1 d2 e1 e2 f1 f2 g1 g2 h1 h2: bool) : (Ascii a1 b1 c1 d1 e1 f1 g1 h1) = (Ascii a2 b2 c2 d2 e2 f2 g2 h2) -> a1 = a2.
  Proof. intros H; congruence. Qed.
  Lemma ascii_ctor_law2 (a1 a2 b1 b2 c1 c2 d1 d2 e1 e2 f1 f2 g1 g2 h1 h2: bool) : (Ascii a1 b1 c1 d1 e1 f1 g1 h1) = (Ascii a2 b2 c2 d2 e2 f2 g2 h2) -> b1 = b2.
  Proof. intros H; congruence. Qed.
  Lemma ascii_ctor_law3 (a1 a2 b1 b2 c1 c2 d1 d2 e1 e2 f1 f2 g1 g2 h1 h2: bool) : (Ascii a1 b1 c1 d1 e1 f1 g1 h1) = (Ascii a2 b2 c2 d2 e2 f2 g2 h2) -> c1 = c2.
  Proof. intros H; congruence. Qed.
  Lemma ascii_ctor_law4 (a1 a2 b1 b2 c1 c2 d1 d2 e1 e2 f1 f2 g1 g2 h1 h2: bool) : (Ascii a1 b1 c1 d1 e1 f1 g1 h1) = (Ascii a2 b2 c2 d2 e2 f2 g2 h2) -> d1 = d2.
  Proof. intros H; congruence. Qed.
  Lemma ascii_ctor_law5 (a1 a2 b1 b2 c1 c2 d1 d2 e1 e2 f1 f2 g1 g2 h1 h2: bool) : (Ascii a1 b1 c1 d1 e1 f1 g1 h1) = (Ascii a2 b2 c2 d2 e2 f2 g2 h2) -> e1 = e2.
  Proof. intros H; congruence. Qed.
  Lemma ascii_ctor_law6 (a1 a2 b1 b2 c1 c2 d1 d2 e1 e2 f1 f2 g1 g2 h1 h2: bool) : (Ascii a1 b1 c1 d1 e1 f1 g1 h1) = (Ascii a2 b2 c2 d2 e2 f2 g2 h2) -> f1 = f2.
  Proof. intros H; congruence. Qed.
  Lemma ascii_ctor_law7 (a1 a2 b1 b2 c1 c2 d1 d2 e1 e2 f1 f2 g1 g2 h1 h2: bool) : (Ascii a1 b1 c1 d1 e1 f1 g1 h1) = (Ascii a2 b2 c2 d2 e2 f2 g2 h2) -> g1 = g2.
  Proof. intros H; congruence. Qed.
  Lemma ascii_ctor_law8 (a1 a2 b1 b2 c1 c2 d1 d2 e1 e2 f1 f2 g1 g2 h1 h2: bool) : (Ascii a1 b1 c1 d1 e1 f1 g1 h1) = (Ascii a2 b2 c2 d2 e2 f2 g2 h2) -> h1 = h2.
  Proof. intros H; congruence. Qed.
  Lemma ascii_ctor_law9 (a1 a2 b1 b2 c1 c2 d1 d2 e1 e2 f1 f2 g1 g2 h1 h2: bool) : a1 = a2 -> b1 = b2 -> c1 = c2 -> d1 = d2 -> e1 = e2 -> f1 = f2 -> g1 = g2 -> h1 = h2 -> (Ascii a1 b1 c1 d1 e1 f1 g1 h1) = (Ascii a2 b2 c2 d2 e2 f2 g2 h2).
  Proof.
    intros; congruence. Qed.

  Fixpoint UIP_ascii_hedberg (a1 a2: ascii) : a1 = a2 -> a1 = a2.
  Proof.
    destruct a1 as [a1 b1 c1 d1 e1 f1 g1 h1]; destruct a2 as [a2 b2 c2 d2 e2 f2 g2 h2]; intros Heq; try (exfalso; congruence).
    eapply ascii_ctor_law9.
    - eapply ascii_ctor_law1, Heq.
    - eapply ascii_ctor_law2, Heq.
    - eapply ascii_ctor_law3, Heq.
    - eapply ascii_ctor_law4, Heq.
    - eapply ascii_ctor_law5, Heq.
    - eapply ascii_ctor_law6, Heq.
    - eapply ascii_ctor_law7, Heq.
    - eapply ascii_ctor_law8, Heq.
  Defined.

  Lemma UIP_bool :
    forall (b1 b2: bool)
      (H1 H2: b1 = b2),
      H1 = H2.
  Proof.
    destruct b1, b2; intros; try congruence.
    - pose proof (Eqdep_dec.UIP_refl_bool true H1).
      pose proof (Eqdep_dec.UIP_refl_bool true H2).
      subst. reflexivity.
    - pose proof (Eqdep_dec.UIP_refl_bool false H1).
      pose proof (Eqdep_dec.UIP_refl_bool false H2).
      subst. reflexivity.
  Qed.
  
  

  Lemma UIP_ascii_is_hedberg : is_hedberg _ (UIP_ascii_hedberg).
  Proof.
    intros x y; induction x as [a1 a2 a3 a4 a5 a6 a7 a8] in y|-*; destruct y as [b1 b2 b3 b4 b5 b6 b7 b8]; intros E1 E2; try (exfalso; congruence).
    cbn. erewrite (UIP_bool _ _ (ascii_ctor_law1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  E1)).
    erewrite (UIP_bool _ _ (ascii_ctor_law2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ E1)).
    erewrite (UIP_bool _ _ (ascii_ctor_law3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ E1)).
    erewrite (UIP_bool _ _ (ascii_ctor_law4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ E1)).
    erewrite (UIP_bool _ _ (ascii_ctor_law5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ E1)).
    erewrite (UIP_bool _ _ (ascii_ctor_law6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ E1)).
    erewrite (UIP_bool _ _ (ascii_ctor_law7 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ E1)).
    erewrite (UIP_bool _ _ (ascii_ctor_law8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ E1)).
    f_equal.
  Qed.

  Lemma UIP_ascii :
    UIP ascii.
  Proof.
    unfold UIP.
    intros. eapply hedberg_to_UIP.
    eapply UIP_ascii_is_hedberg.
  Qed.

  Lemma UIP_ascii_refl :
    forall (a: ascii)
      (H: a = a),
      H = eq_refl.
  Proof.
    intros. eapply UIP_ascii.
  Qed.
End UIPAscii.
      
                                                                                   

From Coq Require Import String.

Print string.

Lemma string_ctor_law1 (h1 h2 : Ascii.ascii) (t1 t2 : string) : (String h1 t1) = (String h2 t2) -> h1 = h2.
Proof. intros H; congruence. Qed.
Lemma string_ctor_law2 (h1 h2 : Ascii.ascii) (t1 t2 : string) : (String h1 t1) = (String h2 t2) -> t1 = t2.
Proof. intros H; congruence. Qed.
Lemma string_ctor_law3(h1 h2 : Ascii.ascii) (t1 t2 : string) : h1 = h2 -> t1 = t2 -> (String h1 t1) = (String h2 t2).
Proof. intros H1 H2; congruence. Qed.

Fixpoint UIP_string_hedberg (l1 l2 : string) : l1 = l2 -> l1 = l2.
Proof.
  destruct l1 as [|l1h l1t]; destruct l2 as [|l2h l2t]; intros Heq; try (exfalso; congruence).
  - reflexivity.
  - apply string_ctor_law3.
    + eapply string_ctor_law1, Heq.
    + eapply (UIP_string_hedberg _), string_ctor_law2, Heq.
Defined.



Lemma UIP_string_is_hedberg : is_hedberg _ (UIP_string_hedberg).
Proof.
  intros x y; induction x as [|xh xr IH] in y|-*; destruct y as [|yh yr]; intros E1 E2; try (exfalso; congruence).
  - cbn. easy.
  - cbn.
    erewrite (UIPAscii.UIP_ascii _ _ (string_ctor_law1 xh yh xr yr E1)).
    erewrite (IH _ (string_ctor_law2 xh yh xr yr E1)).
    reflexivity.
Qed.

Lemma UIP_string : UIP string.
Proof.
  intros x y. eapply hedberg_to_UIP. apply (UIP_string_is_hedberg).
Qed.

Lemma UIP_string_refl :
  forall (s: string)
    (H: s = s),
    H = eq_refl.
Proof.
  intros. eapply UIP_string.
Qed.

(*
 * We can use a similar approach for pairs (new code from here on out)
 *)
Lemma pair_ctor_law1 (X : Type) (x1 x2 : X) (x1' x2' : X) : (x1, x2) = (x1', x2') -> x1 = x1'.
Proof. intros; congruence. Qed.
Lemma pair_ctor_law2 (X : Type) (x1 x2 : X) (x1' x2' : X) : (x1, x2) = (x1', x2') -> x2 = x2'.
Proof. intros; congruence. Qed.
Lemma pair_ctor_law3 (X:Type) (x1 x2 : X) (x1' x2' : X) : x1 = x1' -> x2 = x2' -> (x1, x2) = (x1', x2').
Proof. intros; congruence. Qed.

(* Our hedberg function *)
Fixpoint UIP_pair_hedberg (X:Type) (p1 p2 : X * X) : p1 = p2 -> p1 = p2.
Proof.
  destruct p1; destruct p2; intros Heq; try (exfalso; congruence).
  apply pair_ctor_law3.
  - eapply pair_ctor_law1, Heq.
  - eapply pair_ctor_law2, Heq.
Defined.

Lemma UIP_pair_is_hedberg (X:Type) (Huip : UIP X) : is_hedberg _ (UIP_pair_hedberg X).
Proof.
  intros x y; destruct x; destruct y; intros E1 E2; try (exfalso; congruence).
  cbn. erewrite (Huip _ _ (pair_ctor_law1 X x x0 x1 x2 E1)).
  erewrite (Huip _ _ (pair_ctor_law2 X x x0 x1 x2 E1)).
  reflexivity.
Qed.

Lemma UIP_to_pair (T : Type) : UIP T -> UIP (T * T).
Proof.
  intros H x y. eapply hedberg_to_UIP. apply (UIP_pair_is_hedberg _ H).
Qed.

(* For options... *)

Lemma option_ctor_law1 (X: Type) (x x': X) : Some x = Some x' -> x = x'.
Proof.
  intros. inversion H. reflexivity.
Qed.
Lemma option_ctor_law3' (X: Type) (x x': option X) :
  match x as x0, x' as x0' with
  | Some y, Some y' => y = y'
  | None, None => True
  | _, _ => False
  end -> x = x'.
Proof.
  intros. destruct x, x'.
  - congruence.
  - inversion H.
  - inversion H.
  - reflexivity.
Qed.

Fixpoint UIP_option_hedberg (X: Type) (p1 p2 : option X) : p1 = p2 -> p1 = p2.
Proof.
  destruct p1; destruct p2; intros Heq; try (exfalso; congruence).
  - apply option_ctor_law3'.
    eapply option_ctor_law1. assumption.
  - apply option_ctor_law3'. eapply I.
Defined.

Axiom UIP_None :
  forall (X: Type)
    (H1 H2: @None X = @None X),
    H1 = H2.


Lemma UIP_option_is_hedberg (X: Type) (Huip: UIP X) : is_hedberg _ (UIP_option_hedberg X).
Proof.
  intros x y; destruct x; destruct y; intros E1 E2; try (exfalso; congruence).
  - cbn. erewrite (Huip _ _ (option_ctor_law1 X x x0 E1)).
    reflexivity.
  - cbn. reflexivity.
Qed.

Lemma UIP_to_option (T: Type) : UIP T -> UIP (option T).
Proof.
  intros H x y. eapply hedberg_to_UIP. apply (UIP_option_is_hedberg _ H).
Qed.
  
  
Lemma UIP_to_option_pair (T: Type) (Huip_T: UIP T) :
  UIP (option (T * T)).
Proof.
  intros x y.
  eapply hedberg_to_UIP.
  eapply (UIP_option_is_hedberg _ (UIP_to_pair _ Huip_T)).
Qed.

Lemma UIP_option_pair_refl (T: Type) (Huip_T: UIPList.UIP T) :
  forall (o: option (T * T))
    (H: o = o),
    H = eq_refl.
Proof.
  pose proof (UIP_option := UIP_to_option_pair).
  specialize (UIP_option _ Huip_T).
  unfold UIP in UIP_option.
  intros. eapply UIP_option.
Qed.

Lemma UIP_list_refl (T: Type) (Huip_T : UIP T) :
  forall (l: list T)
    (H: l = l),
    H = eq_refl.
Proof.
  pose proof (UIP_list := UIP_to_list).
  specialize (UIP_list _ Huip_T).
  unfold UIP in UIP_list.
  intros. eapply UIP_list.
Qed.



Lemma pair_ctor_law1' (X Y : Type) (x1: X) (x2 : Y) (x1': X) (x2' : Y) : (x1, x2) = (x1', x2') -> x1 = x1'.
Proof. intros; congruence. Qed.
Lemma pair_ctor_law2' (X Y: Type) (x1: X) (x2 : Y) (x1': X) (x2' : Y) : (x1, x2) = (x1', x2') -> x2 = x2'.
Proof. intros; congruence. Qed.
Lemma pair_ctor_law3' (X Y:Type) (x1: X) (x2 : Y) (x1': X) (x2' : Y) : x1 = x1' -> x2 = x2' -> (x1, x2) = (x1', x2').
Proof. intros; congruence. Qed.

(* Our hedberg function *)
Fixpoint UIP_pair_hedberg' (X Y:Type) (p1 p2 : X * Y) : p1 = p2 -> p1 = p2.
Proof.
  destruct p1; destruct p2; intros Heq; try (exfalso; congruence).
  apply pair_ctor_law3'.
  - eapply pair_ctor_law1', Heq.
  - eapply pair_ctor_law2', Heq.
Defined.

Lemma UIP_pair_is_hedberg' (X Y:Type) (HuipX : UIP X) (HuipY : UIP Y) : is_hedberg _ (UIP_pair_hedberg' X Y).
Proof.
  intros x y; destruct x; destruct y; intros E1 E2; try (exfalso; congruence).
  cbn. erewrite (HuipX _ _ (pair_ctor_law1' X Y x y0 x0 y E1)).
  erewrite (HuipY _ _ (pair_ctor_law2' X Y x y0 x0 y E1)).
  reflexivity.
Qed.

Lemma UIP_to_pair' (X Y : Type) : UIP X -> UIP Y -> UIP (X * Y).
Proof.
  intros HX HY x y. eapply hedberg_to_UIP. apply (UIP_pair_is_hedberg' _ _ HX HY).
Qed.

Lemma UIP_to_pair'_refl (X Y: Type) (HuipX : UIP X) (HuipY: UIP Y) :
  forall (p: X * Y)
    (H: p = p),
    H = eq_refl.
Proof.
  pose proof (UIP_pair := UIP_to_pair').
  specialize (UIP_pair _ _ HuipX HuipY).
  unfold UIP in UIP_pair.
  intros. eapply UIP_pair.
Qed.
