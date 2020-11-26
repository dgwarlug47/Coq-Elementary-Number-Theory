(** Load required packages. **)

Require Export Setoid Plus List Sorted Constructive_sets Utf8_core.

(** Unicode (UTF8) notations. **)
Require Export Classical_Prop Utf8.
Require Export BinNums.
Require Import BinPos BinNat.

Local Open Scope Z_scope.

Notation "x ⇒ y" := (x -> y)
  (at level 99, y at level 200, right associativity): type_scope.

Notation "x ⇔ y" := (x <-> y) (at level 95, no associativity): type_scope.

Notation "∃ ! x .. y , p" :=
  (ex (unique (fun x => .. (ex (unique (fun y => p))) ..)))
  (at level 200, x binder, right associativity,
   format "'[' '∃'  !  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

(** Useful symbols: ∀ ∃ ⇒ ⇔ ∧ ∨ ¬ ≠ ≤ ≥ ℕ ℤ ∈ ∉ ⊂ ∑ ∏ **)

(** Axioms for the integers. **)

Parameter Z : Set.

Parameter add mult : Z → Z → Z.
Parameter neg : Z → Z.
Parameter zero one : Z.
Notation "0" := zero.
Notation "1" := one.
Infix "+" := add.
Infix "*" := mult.
Notation "- x" := (neg x).
Notation "- 0" := (neg 0) (only parsing).
Notation "- 1" := (neg 1).
Definition sub a b := a + -b.
Infix "-" := sub.
Theorem Dan : ∀ P : Prop, P ∨ ¬ P.
Proof.
intros.
auto.
pose proof (classic P) as H0.
exact H0.
Qed.

Axiom A1 : ∀ a b   : Z, a + b = b + a.
Axiom A2 : ∀ a b c : Z, (a + b) + c = a + (b + c).
Axiom A3 : ∀ a     : Z, a + 0 = a.
Axiom A4 : ∀ a     : Z, a + -a = 0.
Axiom M1 : ∀ a b   : Z, a * b = b * a.
Axiom M2 : ∀ a b c : Z, (a * b) * c = a * (b * c).
Axiom M3 : ∀ a     : Z, a * 1 = a.
Axiom D1 : ∀ a b c : Z, (a + b) * c = a * c + b * c.


Lemma S1 : ∀ a b c : Z, a = b ⇒ a + c = b + c.
Proof.
  intros a b c H. 
  congruence.
Qed.

Lemma S2 : ∀ a b c : Z, a = b ⇒ a * c = b * c.
Proof.
  intros a b c H. 
  congruence.
Qed.

(** Homework assignment problems are given below. **)

Theorem A1P1 :  forall a : Z, 0 + a = a.
Proof.
   intros.
pose proof (A1 0 a).
rewrite A3 in H.
exact H.
Qed.

Theorem A1P2 :  forall a : Z, -a + a = 0.
Proof.
intros.
pose proof ( A1 (-a) a).
rewrite A4 in H.
exact H.
Qed.

Theorem A1P3 :  forall a : Z, 1 * a = a.
Proof.
intros.
pose proof (M1 1 a).
rewrite M3 in H.
exact H.
Qed.

Theorem A1P4 :  forall a b : Z, a + b = 0 ⇒ b = -a.
Proof.
intros.
apply (S1 (a+b) 0 (-a)) in H.
rewrite A1 in H.
rewrite <-A2 in H.
rewrite A1P2 in H.
rewrite A1 in H.
rewrite A3 in H.
rewrite A1 in H.
rewrite A3 in H.
exact H.
Qed.
Theorem U:  forall a : Z, -a= - (a).
Proof.
intros.
reflexivity.
Qed.

Theorem A1P5 :  forall a : Z, -(-a) = a.
Proof.
intros.
pose proof ( A4 (-a)).
apply (S1 _ _ a) in H.
rewrite A1P1 in H.
rewrite A1 in H.
rewrite <-A2 in H.
rewrite A4 in H.
rewrite A1P1 in H.
exact H.
Qed.

Theorem A1P6 :  forall a : Z, 0 * a = 0.
Proof.
intros.
  pose proof (A3 0).
  (* Multiply both sides by a *)
  apply (S2 (0+0) 0 a) in H.
  (* Undo the previous step in order to show you a different way
     to do the same thing *)
  Undo.
  (* Multiply both sides by a. Blank spaces _ mean "fill in the blank
     with the obvious thing" *)
  apply (S2 _ 0 a) in H.
  rewrite D1 in H.
  apply (S1 _ _ (-(0*a))) in H.
  rewrite A2 in H.
  (* If you want to use Axiom A2 backwards (i.e. replace "a+(b+c)"
     with "(a+b)+c", instead of replacing "(a+b)+c" with "a+(b+c)")
     then you need to use "rewrite <-A2" instead of "rewrite A2" *)
  rewrite <-A2 in H.
  (* Undo previous step, which was only for demonstration purposes *)
  rewrite A2 in H.
  rewrite A4, A3 in H.
  exact H.
Qed.
Theorem D7 :  forall a : Z,  a*0 = 0.
Proof.
intros.
  pose proof (A3 0).
  (* Multiply both sides by a *)
  apply (S2 (0+0) 0 a) in H.
  (* Undo the previous step in order to show you a different way
     to do the same thing *)
  Undo.
  (* Multiply both sides by a. Blank spaces _ mean "fill in the blank
     with the obvious thing" *)
  apply (S2 _ 0 a) in H.
  rewrite D1 in H.
  apply (S1 _ _ (-(0*a))) in H.
  rewrite A2 in H.
  (* If you want to use Axiom A2 backwards (i.e. replace "a+(b+c)"
     with "(a+b)+c", instead of replacing "(a+b)+c" with "a+(b+c)")
     then you need to use "rewrite <-A2" instead of "rewrite A2" *)
  rewrite <-A2 in H.
  (* Undo previous step, which was only for demonstration purposes *)
  rewrite A2 in H.
  rewrite A4, A3 in H.
rewrite M1 in H.
  exact H.
Qed.

Theorem A1P7 :  forall a : Z, -1 * a = -a.
Proof.
intros.
pose proof (D1 1 (-1) a).
rewrite A4 in H.
rewrite A1P6 in H.
rewrite A1P3 in H.
rewrite A1 in H.
apply  (S1  _ _ (-a))in H.
rewrite A1 in H.
rewrite A3 in H.
rewrite A2 in H.
rewrite A4 in H.
rewrite A3 in H.
symmetry in H.
exact H.
Qed.
Theorem NOW :  forall a : Z, a* -1 = -a.
Proof.
intros.
pose proof (A1P7 a).
rewrite M1 in H.
exact H.
Qed.


Theorem A1P8 :  forall a b : Z, -a * -b = a * b.
Proof.
intros.
pose proof (M2 ((-a)*(-b)) (-1) (-1)).
rewrite A1P7 in H.
rewrite A1P5 in H.
rewrite M3 in H.
rewrite M1 in H.
rewrite M2 in H.
rewrite M1 in H.
rewrite M2 in H.
rewrite M1 in H.
rewrite M2 in H.
rewrite A1P7 in H.
rewrite A1P5 in H.
rewrite M1 in H.
rewrite M1 in H.
rewrite NOW in H.
rewrite A1P5 in H.
symmetry.
rewrite M1 in H.
exact H.
Qed.

Theorem A1P9 :  forall a b : Z, a + b = a ⇒ b = 0.
Proof.
intros.
apply (S1 (a+b) a (-a)) in H.
rewrite A2 in H.
rewrite A4 in H.
rewrite A1 in H.
rewrite A2 in H.
rewrite A1P2 in H.
rewrite A3 in H.
exact H.
Qed.


Definition ℤ := (Full_set Z).
Definition P := Ensemble.
Infix "∋" := (In Z) (at level 70).
Notation "x ∈ S" := (S ∋ x) (at level 70).
Notation "x ∉ S" := (¬(x ∈ S)) (at level 70).
Infix "⊂" := (Included Z) (at level 70).
Notation "∅" := (Empty_set Z).
Notation "{ x : A | P }" := (λ x : A, P).



Definition divide (x y : Z) := exists z, y = z*x.
Notation "( x | y )" := (divide x y).

(** Definition of ±, used in problem 5. **)
Definition pm (a b : Z) := (a = b ∨ a = -b).
Notation " a = ± b " := (pm a b) (at level 60).

(** Homework assignment problems are given below. **)

Parameter ℕ : P(Z).


Definition lt (a b : Z) := b-a ∈ ℕ.
Infix "<" := lt.
Notation "x > y" := (y < x) (only parsing).
Notation "x ≠ ± y" := (¬ (x = ± y)) (at level 60).

Definition prime (p : Z) :=
  p ≠ ± 1 ∧ ∀ d : Z, (d | p) ⇒ d = ± 1 ∨ d = ± p.

Axiom W1 : ∀ S : P(Z), (S ≠ ∅) ⇒ (S ⊂ ℕ) ⇒ ∃ m : Z, m ∈ S ∧ ∀ x : Z, x ∈ S ⇒ m < x ∨ m = x.
Lemma WOP : ∀ S : P(Z), (∃ x : Z, S x) ⇒ (∀ x : Z, S x ⇒ x ∈ ℕ) ⇒
 ∃ s : Z, S s ∧ ∀ t : Z, S t ⇒ s < t ∨ s = t.
Proof.
  intros S [x H] H0.
  destruct (W1 S) as [y H1]; try eauto.
  intros H1.
  subst S.
  contradiction H.
Qed.



Axiom legal : ∃ a : Z, a ≠ 0.
(* I used this axiom, because if it is not true all the numbers will be equal to zero,
so to distingush the integers from module 1 *)

Theorem G : ∀a b : Z, a -b = a+ -b.
Proof.
intros.
tauto.
Qed.
Theorem PORRA : -0=0.
Proof.
pose proof (A1 0 (-0)).
rewrite A1P1 in H.
rewrite A1P2 in H.
exact H.
Qed.
Theorem lt_N : ℕ = {x : Z | 0 < x}.
Proof.
  apply Extensionality_Ensembles.
  split.
  - unfold Included.
    intros x H.
    unfold In, lt, sub.
    rewrite <-(A3 x), A2, A4, A3.
    exact H.
  - unfold Included.
    intros x H.
    unfold In, lt, sub in H.
    rewrite <-(A3 x), A2, A4, A3 in H.
    exact H.
Qed.

Theorem lt_N_elt : ∀ x : Z, x ∈ ℕ ⇔ x > 0.
Proof.
  split;
  unfold In, lt, sub;
  rewrite <-(A3 x), A2, A4;
  intros H;
  exact H.
Qed.
Definition cprime (a b : Z) := (∀ q : Z ,( (q | a) ∧ (q | b) )-> q=1 ∨  q=(-1)).
Notation " a $ b " := (cprime a b)(at level 60) .

Theorem O1 : ∀ a b c : Z, a < b ⇒ a + c < b + c.
Proof.
  unfold lt, sub.
  intros a b c H.
  rewrite <-(A1P7), M1, D1, M1, A1P7, M1, A1P7, A2, (A1 c), A2, A1P2, A3.
  exact H.
Qed.

Axiom O2 : ∀ a b c : Z, a < b ⇒ c > 0 ⇒ a * c < b * c.

Axiom T : ∀ a : Z,
(a > 0 ∧ a ≠ 0 ∧ ¬a < 0) ∨ 
(¬a > 0 ∧ a = 0 ∧ ¬a < 0) ∨
(¬a > 0 ∧ a ≠ 0 ∧ a < 0).
Lemma Putz : 0 ≠ 1.
Proof.
pose proof legal.
case ( classic ( 0=1)).
intros.
destruct H.
apply ( S2 0 1 x) in H0.
rewrite A1P6, A1P3    in H0.
symmetry in H0.
tauto.
intros.
tauto.
Qed.


Lemma I778 : 1>0.  
destruct (T (1)) as [[H0 [H1 H2]] | [[H0 [H1 H2]] | [H0 [H1 H2]]]].
tauto.
pose proof Putz.
symmetry in H1.
tauto.
apply (O1  1 0 (-1) ) in H2.
rewrite A4 in H2.
rewrite  A1 in H2.
rewrite A3 in H2.
pose proof ( O2 0 (-1) (-1) ).
apply H in H2.
rewrite A1P6 in H2.
rewrite A1P7 in H2.
rewrite A1P5 in H2.
tauto.
tauto.
Qed.


Notation "x > y" := (y < x) (only parsing).
Notation "x <= y" := (x < y ∨ x = y).
Notation "x ≤ y" := (x < y ∨ x = y) (at level 70).
Notation "x >= y" := (x > y ∨ x = y).
Notation "x ≥ y" := (x > y ∨ x = y) (at level 70).
Notation "x < y < z" := (x < y ∧ y < z).
Notation "x <= y < z" := (x <= y ∧ y < z).
Notation "x ≤ y < z" :=
  (x ≤ y ∧ y < z) (at level 70, y at next level).

Theorem AGORA :  ℕ ≠ ∅.
pose proof (lt_N_elt 1).
destruct H.
unfold lt in H.
pose proof I778.
apply H0 in H1.
unfold not.
intros.
rewrite H2 in H1 .
contradiction.
Qed.

Lemma I7 :  forall a b: Z, a>b -> ¬(a<b).
Proof.
intros.
apply (O1 b a (-a)) in H.
rewrite A4 in H.
destruct (T (b+ -a)) as [[H0 [H1 H2]] | [[H0 [H1 H2]] | [H0 [H1 H2]]]].
tauto.
tauto.
pose proof (Dan (a<b)).
destruct H3.
apply (O1 a b (-a)) in H3.
rewrite A4 in H3.
contradiction.
exact H3.
Qed.
Lemma I9 :  forall a b: Z, a=b -> ¬(a<b).
Proof.
intros.
apply (S1 a b (-a)) in H.
rewrite A4 in H.
destruct (T (b+ -a)) as [[H0 [H1 H2]] | [[H0 [H1 H2]] | [H0 [H1 H2]]]].
symmetry in H.
tauto.
pose proof (Dan (a<b)).
destruct H3.
apply (O1 a b (-a)) in H3.
rewrite A4 in H3.
tauto.
exact H3.
symmetry in H.
tauto.
Qed.

Lemma I8 :  forall a b: Z, a=0 -> ¬(a<0).
Proof.
intros.
destruct (T (a)) as [[H0 [H1 H2]] | [[H0 [H1 H2]] | [H0 [H1 H2]]]].
tauto.
tauto.
contradiction.
Qed.
Theorem OBVIO : 0=0.
Proof.
tauto.
Qed.
Theorem PORRA2 : ∀ a: Z, a=a.
Proof.
intros.
tauto.
Qed.

Lemma Y : ∀ a b: Z,
(a > b ∧ a ≠ b ∧ ¬a < b) ∨ 
(¬a > b ∧ a = b ∧ ¬a < b) ∨
(¬a > b ∧ a ≠ b ∧ a < b).
Proof.
intros.
destruct (T (a-b)) as [[H0 [H1 H2]] | [[H0 [H1 H2]] | [H0 [H1 H2]]]].
apply (O1 0 (a-b) b) in H0.
rewrite A1P1 in H0.
rewrite G in H0.
rewrite A2 in H0.
rewrite A1P2 in H0.
rewrite A3 in H0.
pose proof (Dan (a=b)).
destruct H.
apply (S1 a b (-b)) in H.
rewrite A4 in H.
tauto.
pose proof (Dan (a<b)).
destruct H3.
apply (O1 a b (-b)) in H3.
rewrite A4 in H3.
rewrite <-G in H3.
tauto.
pose proof (conj H0 H).
pose proof (conj H4 H3).
left.
tauto.
pose proof (Dan (a<b)).
destruct H.
apply (O1 a b (-b)) in H.
rewrite A4 in H.
rewrite <-G in H.
tauto.
pose proof (Dan (b<a)).
destruct H3.
apply (O1 b a (-b)) in H3.
rewrite A4 in H3.
rewrite <-G in H3.
tauto.
apply (S1 (a-b) 0 b) in H1.
rewrite G in H1.
rewrite A2 in H1.
rewrite A1P1 in H1. 
rewrite A1P2 in H1.
rewrite A3 in H1.
pose proof (conj H0 H).
pose proof (conj H4 H3).
tauto.

apply (O1 (a-b) 0 b) in H2.
rewrite G in H2.
rewrite A2 in H2.
rewrite A1P1 in H2.
rewrite A1P2 in H2.
rewrite A3 in H2.
pose proof (Dan (b<a)).
destruct H.
apply (O1 b a (-b)) in H.
rewrite A4 in H.
rewrite <-G in H.
tauto.
pose proof (Dan (a=b)).
destruct H3.
apply (S1 a b (-b)) in H3.
rewrite A4 in H3.
tauto.
tauto.
Qed.
Theorem A1P11 : ∀ a b : Z, a * b = 0 ⇒ a = 0 ∨ b = 0.
Proof.
  intros a b H.
  pose proof (T (a*b)) as J.
  destruct (T a) as [[H0 [H1 H2]] | [[H0 [H1 H2]] | [H0 [H1 H2]]]].
  - destruct (T b) as [[H3 [H4 H5]] | [[H3 [H4 H5]] | [H3 [H4 H5]]]].
    + pose proof (O2 0 a b) as H6.
      rewrite A1P6 in H6.
      tauto.
    + tauto.
    + pose proof (O2 b 0 a) as H6.
      rewrite A1P6, M1 in H6.
      tauto.
  - tauto.
  - destruct (T b) as [[H3 [H4 H5]] | [[H3 [H4 H5]] | [H3 [H4 H5]]]].
    + pose proof (O2 a 0 b) as H6.
      rewrite A1P6 in H6.
      tauto.
    + tauto.
    + apply (O1 _ _ (-a)) in H2.
      apply (S1 _ _ (-(a*b))) in H.
      rewrite A4, A1P1 in H2, H.
      pose proof (O2 b 0 (-a)) as H6.
      rewrite A1P6, M1, <-A1P7, M2, ? A1P7 in H6.
      symmetry in H.
      pose proof (T (-(a*b))) as H7.
      tauto.
Qed.
Theorem A1P10 : ∀ a b : Z,  a*b = a ⇒ b = 1 ∨ a=0.
Proof.
intros.
apply ( S1 (a*b) a (-a)) in H.
rewrite A4 in H.
rewrite M1 in H.
rewrite <-A1P7 in H.
rewrite <-D1 in H.
apply A1P11 in H.
case H.
intros.
apply (S1 (b + -1) 0 1) in H0.
rewrite A1P1 in H0.
rewrite A2 in H0.
rewrite A1P2 in H0.
rewrite A3 in H0. 
left.
exact H0.
intros.
right.
exact H0.
Qed.
Lemma R1 : forall a b : Z, a>b <-> b<a.
Proof.
intros.
split.
tauto.
tauto.
Qed.
Lemma I3 :  forall a b : Z, a>b -> -a<(-b).
Proof.
intros.
pose proof (R1 a b).
destruct H0.
apply R1 in H.
apply (O1 b a (-a-b)) in H.
rewrite A1 in H.
rewrite G in H.
rewrite A2 in H.
rewrite A1P2 in H.
rewrite A3 in H.
rewrite <-A2 in H.
rewrite A4 in H.
rewrite A1P1 in H.
exact H.
Qed.
