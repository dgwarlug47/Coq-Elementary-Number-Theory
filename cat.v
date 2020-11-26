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



Axiom R3 : forall a b c : Z, a<b ∧ b<c -> a<c.


(** Homework assignment problems are given below. **)


Theorem A2P1 : ∀ a m n x y : Z, (a | m) ⇒ (a | n) ⇒ (a | m * x + n * y).
Proof.
intros.
unfold divide in H .
unfold divide in H0 .
destruct H.
destruct H0.
unfold divide.
rewrite H.
rewrite H0.
rewrite M1.
rewrite <-M2.
rewrite (M1 (x1*a) y) .
rewrite <-(M2 y x1 a).
rewrite <-D1.
exists (x*x0 + y*x1).
tauto.
Qed.


Theorem A2P2: ∀ a b c : Z, (a | b) ⇒ (b | c) ⇒ (a | c).
Proof.
intros.
unfold divide in H.
unfold divide in H0.
destruct H.
destruct H0.
rewrite H in H0.
unfold divide.
rewrite <-M2 in H0.
exists (x0*x).
tauto.
Qed.

Theorem A2P3 : 0 ≠ 1.
Proof.
pose proof Putz.
tauto.
Qed.

Theorem A2P4 : ∀ a b c : Z, a * c = b * c ⇒ c ≠ 0 ⇒ a = b.
Proof.
intros.
apply (S1 (a*c) (b*c) (-(b*c))) in H.
rewrite A4 in H.
rewrite <-A1P7 in H.
rewrite <-M2 in H.
rewrite A1P7 in H.
rewrite <-D1 in H.
apply A1P11 in H.
destruct H.
apply (S1 (a+ - b) 0 b) in H.
rewrite A2 in H.
rewrite A1P2 in H.
rewrite A3 in H.
rewrite A1P1 in H.
tauto.
tauto.
Qed.
Theorem Davi : ∀ m : Z , m>0 -> m=1 ∨ m>1.
intros.
pose proof (W1 ℕ).
pose proof AGORA.
apply H0 in H1.
destruct H1.
destruct H1.
pose proof (H2 1).
pose proof (H2 m) as H45.
pose proof I778.
unfold lt in H4.
auto.
rewrite G in H4.
rewrite PORRA in H4.
rewrite A3 in H4.
apply H3 in H4.
destruct H4.
rewrite lt_N_elt in H1.
pose proof H1 as H67.
pose proof (O2 0 x x).
apply H5 in H1.
rewrite A1P6 in H1.
pose proof (O2 x 1 x).
apply H6 in H4.
rewrite A1P3 in H4.
pose proof (H2 (x*x)).
rewrite <-lt_N_elt in H1.
apply H7 in H1.
destruct H1.
pose proof (I7 x (x*x)).
apply H8 in H4.
contradiction.
symmetry in H1.
apply A1P10 in H1.
destruct H1.
pose proof (lt_N_elt m).
destruct H8.
apply H9 in H.
pose proof H as H78.
apply H45 in H.
destruct H.
rewrite H1 in H.
right.
exact H.
auto.
rewrite H1 in H.
left.
symmetry in H. 
exact H.
pose proof (lt_N_elt m).
destruct H8.
apply H9 in H.
apply H45 in H.
destruct H.
rewrite H1 in H.
apply H9 in H.
apply H45 in H.
destruct H.
rewrite H1 in H4.
rewrite A1P6 in H4.
pose proof OBVIO.
pose proof (I8 0).
apply H11 in H10.
contradiction.
pose proof (I9 0 0).
pose proof H10 as H46.
apply H12 in H10.
tauto.
rewrite H1 in H67.
pose proof (I9 0 0).
pose proof (Dan (0=0)).
destruct H11.
apply H10 in H11.
tauto.
tauto.
rewrite H1 in H67. 
pose proof (I9 0 0).
pose proof (Dan (0=0)).
destruct H11.
apply H10 in H11.
tauto.
tauto.
exact H67.
exact H67.
pose proof (lt_N_elt m).
destruct H5.
apply H6 in H.
apply H45 in H.
destruct H.
rewrite H4 in H.
right.
exact H.
rewrite H4 in H.
symmetry in H.
left.
exact H.
congruence.
Qed.
Theorem Davi2 : ∀ m : Z , m<0 -> m=-1 ∨ m< -1.
intros.
pose proof (I3 0 m).
apply H0 in H.
rewrite PORRA in H.
pose proof (Davi (-m)).
apply H1 in H.
destruct H.
apply (S2 (-m) 1 (-1)) in H.
rewrite M1 in H.
rewrite A1P7 in H.
rewrite A1P5 in H.
rewrite <-M3 in H.
rewrite M2 in H.
rewrite A1P7 in H.
rewrite M1 in H.
rewrite M3 in H.
left.
exact H.
right.
apply (O1 1 (-m) (m-1)) in H.
rewrite G in H.
rewrite A1 in H.
rewrite A2 in H.
rewrite A1P2 in H.
rewrite A3 in H.
rewrite <-A2 in H.
rewrite A1P2 in H.
rewrite A1P1 in H.
tauto.

Qed.
Theorem Sena : ∀ m a : Z , m>a -> m=a+1 ∨ m>a+1.
Proof.
intros.
pose proof (Davi (m-a)).
apply (O1 a m (-a)) in H.
rewrite A4 in H.
rewrite <-G in H.
apply H0 in H.
destruct H.
apply (S1 (m-a) 1 a) in H.
rewrite G in H.
rewrite A2 in H.
rewrite A1P2 in H.
rewrite A3 in H.
rewrite A1 in H.
tauto.
apply ( O1 1 (m-a ) a ) in H.
rewrite G in H.
rewrite A2 in H.
rewrite A1P2 in H.
rewrite A3 in H.
right.
rewrite A1 in H.
tauto.
Qed.
Theorem Sena2 : ∀ m a : Z , m<a -> m=a-1 ∨ m<a-1.
Proof.
intros.
pose proof (Davi2 (m-a)).
apply (O1 m a (-a)) in H.
rewrite A4 in H.
rewrite <-G in H.
apply H0 in H.
destruct H.
apply (S1 (m-a) (-1) a) in H.
rewrite G in H.
rewrite A2 in H.
rewrite A1P2 in H.
rewrite A3 in H.
rewrite A1 in H.
tauto.
apply ( O1 (m-a ) (-1) a ) in H.
rewrite G in H.
rewrite A2 in H.
rewrite A1P2 in H.
rewrite A3 in H.
right.
rewrite A1 in H.
tauto.
Qed.

Theorem SD :∀ a b : Z, a*b=1 -> (a=1 ∧ b=1)∨(a= -1 ∧ b=-1).
Proof.
intros.
 destruct (T b) as [[H0 [H1 H2]] | [[H0 [H1 H2]] | [H0 [H1 H2]]]].
destruct (Y a 1) as [[H4 [H5 H6]] | [[H4 [H5 H6]] | [H4 [H5 H6]]]].
pose proof (O2 1 a b).
pose proof H0 as H56.
apply Davi in H0.
destruct H0.
rewrite H0 in H.
rewrite M3 in H.
tauto.
apply H3 in H4.
rewrite M1 in H4.
rewrite M3 in H4.
rewrite H in H4.
pose proof (I7 b 1).
apply H7 in H0.
tauto.
exact H56.
rewrite H5 in H.
rewrite M1 in H.
rewrite M3 in H.
tauto.
pose proof (O2 a 1 b).
pose proof H6 as H79. 
apply H3 in H6.
rewrite A1P3 in H6.
pose proof (Sena 1 a).
apply H7 in H79.
destruct H79.
apply (S1 1 (a+1) (-1)) in H8.
rewrite A4 in H8.
rewrite A2 in H8.
rewrite A4 in H8.
rewrite A3 in H8.
symmetry in H8.
rewrite H8 in H.
rewrite A1P6 in H.
pose proof A2P3.
tauto.
apply (O1 (a+1) 1 (-1)) in H8.
rewrite A2 in H8.
rewrite A4 in H8.
rewrite A3 in H8.
pose proof (Davi2 a).
apply H9 in H8.
destruct H8.
rewrite H8 in H.
rewrite A1P7 in H.
apply (S2 (-b) 1 (-1)) in H.
rewrite NOW in H.
rewrite A1P5 in H.
rewrite M1 in H.
rewrite M3 in H.
tauto.
apply I3 in H8.
rewrite H in H6.
rewrite A1P5 in H8.
pose proof (O2 1 (-a) b).

apply H10 in H8.
rewrite M1 in H8.
rewrite M3 in H8.
pose proof (conj H6 H8).
pose proof (R3 1 b ((-a)*b)).
apply H12 in H11.
rewrite <-A1P7 in H11.
rewrite M2 in H11.
apply I3 in H11.
rewrite A1P7  in H11.
rewrite A1P5 in H11.
rewrite H in H11.
pose proof (I778).
pose proof H13 as H14.
apply I3 in H14.
rewrite PORRA in H14.
auto.
pose proof (R3 (-1) 0 1).
pose proof (conj H14 H13).
apply H15 in H16.
apply I7 in H16.
tauto.
exact H0.
exact H0.
rewrite H1 in H.
rewrite M1 in H.
rewrite A1P6 in H.
pose proof A2P3.
tauto.
pose proof (Davi2 b).
apply H3 in H2.
destruct H2.
rewrite H2 in H.
rewrite NOW in H.
apply (S2 (-a) 1 (-1)) in H.
rewrite NOW in H.
rewrite A1P5 in H.
rewrite M1 in H.
rewrite M3 in H.
tauto.
destruct (Y a 1) as [[H4 [H5 H6]] | [[H4 [H5 H6]] | [H4 [H5 H6]]]].
apply I3 in H2.
rewrite A1P5 in H2.
pose proof I778.
pose proof (R3 0 1 a).
pose proof (conj H7 H4).
apply H8 in H9.
pose proof (O2 1 (-b) a).
apply H10 in H2.
rewrite M1 in H2.
rewrite M3 in H2.
rewrite <-A1P7 in H2.
rewrite M2 in H2.
rewrite M1 in H.
rewrite H in H2.
rewrite  M3 in H2.
pose proof (R3 1 a (-1)).
pose proof (conj H4 H2).
apply H11 in H12.
auto.
pose proof (R3 0 (1) (-1)).
pose proof (conj H7 H12).
apply H13 in H14.
apply (O1 0 (-1) 1) in H14.
rewrite A1 in H14.
rewrite A3 in H14.
rewrite A1 in H14.
rewrite A4 in H14.
apply I7 in H14.
tauto.
exact H9.
rewrite H5 in H.
rewrite M1 in H.
rewrite M3 in H.
tauto.
pose proof (Sena2 a 1).
apply H7 in H6.
destruct H6.
rewrite G in H6.
rewrite A4 in H6.
rewrite H6 in H.
rewrite A1P6 in H.
pose proof (A2P3).
tauto.
rewrite G in H6.
rewrite A4 in H6.
pose proof (Davi2 a).
apply H8 in H6.
destruct H6.
rewrite H6 in H.
rewrite A1P7 in H.
apply (S2 (-b) 1 (-1)) in H.
rewrite M1 in H.
rewrite A1P7 in H.
rewrite A1P5 in H.
rewrite M1 in H.
rewrite M3 in H.
tauto.
apply I3 in H6.
apply I3 in H2.
rewrite A1P5 in H2, H6.
pose proof I778.
pose proof (R3 0 1 (-a)).
pose proof (conj H9 H6).
apply H10 in H11.
pose proof (O2 1 (-b) (-a)).
apply H12 in H2.
rewrite M1 in H2.
rewrite M3 in H2.
pose proof (R3 1 (-a) ((-b)*(-a))).
pose proof (conj H6 H2).
apply H13 in H14.
rewrite <-A1P7  in H14 .
rewrite M1 in H14.
rewrite <-M2 in H14.
rewrite NOW in H14.
rewrite A1P5 in H14.
rewrite H in H14.
pose proof (PORRA2 1).
apply I9 in H15.

tauto.
exact H11.
Qed.
Theorem Deusmeajude :∀ x b : Z,  ¬ ( x < b) -> (x=b ∨ b < x).
Proof.
intros.
destruct (Y x b) as [[H0 [H1 H2]] | [[H0 [H1 H2]] | [H0 [H1 H2]]]].
tauto.
tauto.
tauto.
Qed.


Theorem A2P5 : ∀ a b : Z, (a | b) ⇒ (b | a) ⇒ a = ± b.
Proof.
intros.
unfold divide in H, H0.
destruct H,  H0.
unfold pm.
rewrite H in H0.
rewrite <-M2 in H0.
symmetry in H0.
rewrite M1 in H0.
apply A1P10 in H0.
destruct H0.
apply SD in H0.
destruct H0.
destruct H0.
rewrite H1 in H.
rewrite M1 in H.
rewrite M3 in H.
symmetry in H.
tauto.
destruct H0.
rewrite H1 in H.
rewrite A1P7 in H.
symmetry in H.
apply (S2 (-a) b (-1)) in H.
rewrite M1 in H.
rewrite A1P7 in H.
rewrite A1P5 in H.
rewrite NOW in H.
tauto.
rewrite H0 in H.
rewrite M1 in H.
rewrite A1P6 in H.
rewrite <-H in H0.
tauto.
Qed.
Theorem Euclides : ∀ a b  : Z, b > 0 -> ∃ r q  : Z, (a=b*q + r) ∧ (0 < r ∨ 0=r)  ∧ r< b .
Proof.
intros.
set (S := {  l  : Z | ∃ q : Z, l=a - b*q +1 ∧ l>0 }).
pose proof ( W1 S).
assert (S≠ ∅).
{
case (classic (a > 0)).
case (classic (S = ∅)).
intros.
assert ( a +1 ∈ S ).
{
unfold In.
unfold S.
exists 0.
rewrite M1.
rewrite A1P6 .
rewrite G .
rewrite PORRA.
rewrite A3.
pose proof (R3 0 a (a+1)).
case (classic (0 < a+1)).
intros.
tauto.
pose proof H2 as H1945.
intros.
pose proof (I778 ).
apply (O1 0 1 a) in H5.
rewrite A1P1 in H5.
rewrite A1 in H5.
tauto. }
rewrite H1 in H3.
contradiction.
intros.
exact H1.
intros.
destruct (T a) as [[H3 [H4 H5]] | [[H3 [H4 H5]] | [H3 [H4 H5]]]].
tauto.
assert (1 ∈ S).
unfold S, In.
exists 0.
rewrite M1, A1P6 .

rewrite G, PORRA, A3.
rewrite H4, A1P1.
pose proof I778.
tauto.
case (classic (S = ∅)).
intros.
rewrite H6 in H2.
contradiction.
intros.
tauto.
case (classic (S = ∅)).
intros.
assert (((-a)*b + a + 1) ∈ S) .
unfold S, In.
exists a.
split. 
rewrite G.
rewrite (A1 a (- (b * a) )).
rewrite (M1 b a), <-A1P7.
rewrite <-(A1P7 (a*b)).
rewrite M2.
tauto.
apply Davi in H.
destruct H.
rewrite H.
rewrite M3, A1P2.
rewrite A1P1.
pose proof I778.
tauto.
pose proof H as H8.
pose proof (O2 1 b (-a) ).
apply H6 in H.
rewrite M1, M3 in H.
rewrite M1 in H.
pose proof (R3 (-a) ((-a)*b) (((-a)*b) + a +1)).
rewrite <-A1P7 .
rewrite M2.
rewrite (M1 a b).
rewrite <-M2.
rewrite <-(M3 a) at 2.
rewrite (M1 a 1).
rewrite M1, <-M2.
rewrite NOW.
rewrite A1P3.
rewrite <-(A1P5 a) at 2.
rewrite <-NOW at 2.
rewrite <-(NOW (a * (-1))).
rewrite NOW.
rewrite (M1 a (-1)).
rewrite <-(A1P7 ((-1) * a) ) .
rewrite (A1P7 a) .
rewrite M1 at 1.
rewrite <-D1.
rewrite <-G.
apply (O1 1 b (-1)) in H8.
rewrite A4 in H8.
rewrite <-G in H8.
pose proof (O2 0 (b-1) (-a)).
apply H9 in H8.
rewrite A1P6 in H8.
pose proof (R3 0  ((b - 1) * (- a))  ((b - 1) * (- a) + 1)).
pose proof (I778).
apply (O1 0 1 ((b - 1) * (- a))) in H11.
rewrite A1 in H11.
rewrite A3 in H11.
rewrite A1 in H11.
tauto.
apply I3 in H5.
rewrite PORRA in H5.
exact H5.
apply I3 in H5.
rewrite PORRA in H5.
exact H5.
rewrite H2 in H6.
unfold In in H6.
tauto.
tauto.   }
apply H0 in H1.
destruct H1.
pose proof I778 as H2.
destruct H1.
pose proof H1 as H67.
unfold S in H1.
unfold In in H1.
destruct H1.
destruct H1.

case (classic ( x<b+1 )).
intros.
exists (x-1).
exists x0.
apply (S1 x (a- (b*x0)+1) (b*x0)) in H1.
rewrite M1 in H1.
rewrite G in H1.
rewrite A2 in H1.
rewrite A2 in H1.
rewrite (A1 (-(x0 * b)) (1 +  (x0*b))) in H1.
rewrite A2 in H1.
rewrite A4 in H1.
rewrite A3 in H1.
apply (S1 (x+ (x0*b) ) (a+1) (-1)) in H1.
rewrite A1 in H1.
rewrite (A2 a 1 (-1)) in H1.
rewrite A4 in H1.
rewrite A3 in H1.
symmetry in H1.
rewrite <-A2 in H1.
rewrite M1 in H1.
rewrite (A1 (-1) x) in H1.
rewrite A1 in H1.
rewrite <-G in H1.
split.
tauto.
split.
unfold S in H67.
unfold In in H67.
destruct H67.
destruct H6.

apply (O1 0 (x) (-1)) in H7.

rewrite A1P1 in H7.
rewrite <-G in H7.
pose proof (Sena2 (-1) (x-1)).
destruct H8.
exact H7.
right.
apply (O1 (-1) (x-1) 1)in H7.
rewrite A1P2 in H7.
rewrite G in H7. 
rewrite A2 in H7.
rewrite A1P2 in H7.
rewrite A3 in H7.
apply (S1 (-1) (x-1-1) 1) in H8.
rewrite A1P2 in H8.
rewrite G in H8.
rewrite A2 in H8.
rewrite A1P2 in H8.
rewrite A3 in H8.
tauto.
apply Sena in H7.
destruct H7.
rewrite A1P2 in H7.
symmetry in H7.
tauto.
rewrite A1P2 in H7 .
tauto.
apply ( O1 (x) (b+1) (-1)) in H5.
rewrite A2 in H5.
rewrite A4 in H5.
rewrite A3 in H5.
rewrite <-G in H5.
tauto.  
intros.
case (classic (x=b)).
intros.
exists (x-1).
exists x0.
auto.
apply (S1 x ( a - (b*x0) + 1) ( (b*x0) + (- 1))) in H1.
rewrite A2 in H1.
rewrite (A1 (b*x0) (-1) ) in H1.
rewrite <-( A2 1 (-1) (b*x0)) in H1.
rewrite A4 in H1.
rewrite A1P1 in H1.
rewrite G in H1.
rewrite A2 in H1.
rewrite A1P2 in H1.
rewrite A3 in H1.
rewrite A1 in H1.
rewrite (A1 (-1) (b*x0)) in H1.
rewrite A2 in H1.
rewrite (A1 (-1) (x)) in H1.
split.
symmetry in H1.
tauto.
split.
apply Sena2 in H4.
tauto.
rewrite H6.
pose  proof (I778).
apply (O1 0 1 (b-1)) in H7.
rewrite A1P1 in H7.

rewrite G in H7.
rewrite A1 in H7 at 2.
rewrite <-A2 in H7.
rewrite A4 in H7.
rewrite <-G in H7.
rewrite A1P1 in H7.
tauto.
intros.
 destruct (Y x b) as [[H7 [H8 H9]] | [[H7 [H8 H9]] | [H7 [H8 H9]]]].
apply Sena2 in H7.
destruct H7.
assert ( (x-b) ∈ S ).
unfold In.
unfold S.
exists (x0 +1).
split.
rewrite G.
apply (S1 x  (a -( b * x0) + 1) (-b)) in H1.
rewrite <-G in H1.
rewrite (G a (b*x0)) in H1.
rewrite A2 in H1.
rewrite (A1 1 (-b)) in H1.
rewrite <-A2 in H1.
rewrite <-(A1P7 b) in H1.
rewrite M1 in H1.
rewrite (M1 (-1) b) in H1.
rewrite <-NOW in H1.
rewrite M2 in H1.
rewrite <-M2 in H1.
rewrite A1 in H1.
rewrite A2 in H1.

rewrite <-(D1 (x0*b) b (-1)) in H1.
rewrite NOW in H1.
rewrite <-(A1P3 b) in H1 at 3.
rewrite <-D1 in H1.
rewrite M1 in H1.
rewrite A1 in H1.
tauto.
apply (S1 b (x - 1) (-b +1)) in H7.
rewrite G in H7.
rewrite <-A2 in H7.
rewrite A4 in H7.
rewrite A1P1 in H7.
rewrite A2 in H7.
rewrite A1 in H7.
rewrite (A1 (-b) 1) in H7.
rewrite <-(A2 (-1) 1  (- b)) in H7.
rewrite A1P2 in H7.
rewrite A1P1 in H7.
rewrite A1 in H7.
rewrite <-G in H7.
rewrite <-H7.
pose proof I778.

tauto.
apply H3 in H10.
destruct H10.
apply (O1 x (x-b) (-x)) in H10.
rewrite A4 in H10.
rewrite A1 in H10.
rewrite G in H10.
rewrite <-A2 in H10.
rewrite A1P2 in H10.
rewrite A1P1 in H10.
apply I3 in H10.
rewrite A1P5 in H10.
rewrite PORRA in H10.
apply I7 in H10.
tauto.
apply (S1 x (x-b) (-x)) in H10.
rewrite A4 in H10.
rewrite A1 in H10.
rewrite G in H10.
rewrite <-A2 in H10.
rewrite A1P2 in H10.
rewrite A1P1 in H10.
apply (S2 0 (-b) (-1)) in H10.
rewrite A1P6 in H10.
rewrite NOW in H10.
rewrite A1P5 in H10.
pose proof (I8 b).
apply I9 in H10.
tauto.
assert ( (x-b) ∈ S ).
unfold In.
unfold S.
exists (x0 +1).
split.
rewrite G.
apply (S1 x  (a -( b * x0) + 1) (-b)) in H1.
rewrite <-G in H1.
rewrite (G a (b*x0)) in H1.
rewrite A2 in H1.
rewrite (A1 1 (-b)) in H1.
rewrite <-A2 in H1.
rewrite <-(A1P7 b) in H1.
rewrite M1 in H1.
rewrite (M1 (-1) b) in H1.
rewrite <-NOW in H1.
rewrite M2 in H1.
rewrite <-M2 in H1.
rewrite A1 in H1.
rewrite A2 in H1.

rewrite <-(D1 (x0*b) b (-1)) in H1.
rewrite NOW in H1.
rewrite <-(A1P3 b) in H1 at 3.
rewrite <-D1 in H1.
rewrite M1 in H1.
rewrite A1 in H1.
tauto.
apply (O1 b (x - 1) (-b +1)) in H7.
rewrite G in H7.
rewrite <-A2 in H7.
rewrite A4 in H7.
rewrite A1P1 in H7.
rewrite A2 in H7.
rewrite A1 in H7.
rewrite (A1 (-b) 1) in H7.
rewrite <-(A2 (-1) 1  (- b)) in H7.
rewrite A1P2 in H7.
rewrite A1P1 in H7.
rewrite A1 in H7.
rewrite <-G in H7.
pose proof I778.
pose proof (R3 0 1 (x-b)).
pose proof (conj H10 H7).
apply H11 in H12.
exact H12.
apply H3 in H10.
destruct H10.
apply (O1 x (x-b) (-x)) in H10.
rewrite A4 in H10.
rewrite A1 in H10.
rewrite G in H10.
rewrite <-A2 in H10.
rewrite A1P2 in H10.
rewrite A1P1 in H10.
apply I3 in H10.
rewrite A1P5 in H10.
rewrite PORRA in H10.
apply I7 in H10.
tauto.
apply (S1 x (x-b) (-x)) in H10.
rewrite A4 in H10.
rewrite A1 in H10.
rewrite G in H10.
rewrite <-A2 in H10.
rewrite A1P2 in H10.
rewrite A1P1 in H10.
apply (S2 0 (-b) (-1)) in H10.
rewrite A1P6 in H10.
rewrite NOW in H10.
rewrite A1P5 in H10.
pose proof (I8 b).
apply I9 in H10.
tauto.
tauto.
pose proof (Sena x 0).
exists (x-1).
exists x0.
apply (S1 x (a - (b * x0) + 1) ((b * x0) - 1)) in H1.
rewrite (G a (b*x0)) in H1.
rewrite A2  in H1.
rewrite (G (b*x0) (1)) in H1.
rewrite (A1 (b * x0) (- 1)) in H1.
rewrite <-(A2 1 (-1) (b*x0)) in H1.
rewrite A4 in H1.
rewrite A1P1 in H1.
rewrite A2 in H1.
rewrite A1P2 in H1.
rewrite A3 in H1.
rewrite <-A2 in H1.
rewrite A1 in H1.
symmetry in H1.
split.
tauto.
split.
apply H10 in H4.
rewrite A1P1 in H4.
destruct H4.
apply (S1 x 1 (-1)) in H4.
rewrite <-G in H4.
rewrite A4 in H4.
symmetry in H4.
tauto.
apply (O1 1 x (-1)) in H4.
rewrite A4 in H4.
rewrite <-G in H4.
tauto.
pose proof (R3 (x-1) x b).
pose proof I778.
apply I3 in H12.
rewrite PORRA in H12.
apply (O1 (-1) 0 x) in H12.
rewrite A1P1 in H12.
rewrite A1 in H12.
rewrite <-G in H12.
tauto.
unfold Included.
unfold S.
unfold In at 1.
intros.
destruct H2.
destruct H2.

apply lt_N_elt.
tauto.
Qed.

Theorem Bezout  : ∀ a b  : Z, a $ b -> ∃ x y: Z, a*x + b*y =1 .
Proof.
intros.
set (S := {  x  : Z | (∃ y z : Z,  x= a*y + b*z) ∧ x>0  }).
pose proof (W1 S).

pose proof (A3 a).
rewrite <-(M3 a) in H1 .
rewrite <-(A1P6 b) in H1.
rewrite (M3 a) in H1 at 2 .
assert ( S ≠ ∅). {
case (classic ( a>0)).
intros.
assert (a ∈ S).


unfold S.
unfold In.
split.

symmetry in H1.
rewrite (M1 0 b) in H1.
exists 1.
exists 0.
exact H1.
exact H2. 

case (classic ( S = ∅)).
intros.
rewrite H4 in H3.
unfold In in H3.
tauto.
tauto.
destruct (T a) as [[H2 [H3 H4]] | [[H2 [H3 H4]] | [H2 [H3 H4]]]].
tauto.
unfold cprime in H.
assert ( b | 0).
unfold divide.
exists 0.
rewrite A1P6.
tauto.
assert ( b | b).
unfold divide.
exists 1.
rewrite A1P3.
tauto.
pose proof (H b).
auto.
rewrite <-H3 in H5.
pose proof (conj H5 H6).
apply H7 in H8.
destruct H8.
intros.
assert ( 1 ∈ S) .
unfold In, S.
split.
exists 0, 1.
rewrite H3, A1P6, M3, A1P1.
rewrite H8.
tauto.
apply I778.
case (classic ( S = ∅)).
intros. 
rewrite H11 in H10.
unfold In in H10.
tauto.
intros.
tauto.
intros. 
assert ( 1 ∈ S) .
unfold In, S.
split.
exists 0,(- 1).
rewrite H3, A1P6, A1P1.
apply (S2 b (-1) (-1)) in H8.
rewrite A1P7 in H8.
rewrite A1P5 in H8.
symmetry in H8.
tauto. 
apply I778.
case (classic ( S = ∅)).
intros. 
rewrite H11 in H10.
unfold In in H10.
tauto.
intros.
tauto.
intros. 
assert (-a ∈ S).


unfold S.
unfold In.
split.

symmetry in H1.
rewrite (M1 0 b) in H1.
exists (-1).
exists 0.
rewrite NOW , M1 , A1P6, A3.
tauto.
apply I3 in H4.
apply ( O1 (-0) (-a) 0) in H4.
rewrite A1 in H4.
rewrite A4 in H4.
rewrite A3 in H4.
tauto.
case (classic ( S = ∅)).
intros.
rewrite H7 in H6.
unfold In in H6.
tauto.
tauto.  }
apply H0 in H2.
destruct H2.
destruct H2.
unfold divide.
 
pose proof ( Euclides a x).
pose proof H2 as H91.
unfold In , S in H2.
destruct H2.
apply H4 in H5.
destruct H5.
destruct H5.
destruct H5.
destruct H6.
pose proof H5 as H889.  

apply (S1 a (x * x1 + x0) (-(x * x1))) in H5.
rewrite A2 in H5.
rewrite (A1 (x * x1) (x0 + - (x * x1)) )in H5.
rewrite A2 in H5.
rewrite A1P2 in H5.
rewrite A3 in H5.
pose proof H2 as H78.
destruct H2, H2.
rewrite H2 in H5.
rewrite D1 in H5.
rewrite A1 in H5.
rewrite <-A1P7 in H5.
rewrite M1 in H5.
rewrite D1 in H5.
rewrite A1 in H5. 
rewrite <-A2 in H5.
rewrite <-(M3 a) in  H5 at 1.
rewrite M1 in H5 at 1.
rewrite M2 in H5.
rewrite NOW in H5.
rewrite M2 in H5.
rewrite (M1 a (x2 * - x1)) in H5.
rewrite <-D1 in H5.
rewrite M1 in H5.
symmetry in H5.
case (classic ( x0 ∈ S) ).
intros.
pose proof H8 as H23.
unfold In , S in H8.

destruct H8.
destruct H6.
destruct H8.
destruct H8.
pose proof (H3 x0).
apply H10 in H23.
destruct H23.
apply I7 in H11.
tauto.
symmetry in H11.
apply I9 in H11.
tauto.
rewrite <-H6 in H9.
destruct (T (0)) as [[H10 [H11 H12]] | [[H10 [H11 H12]] | [H10 [H11 H12]]]].
tauto.
tauto.
tauto.
intros.
unfold S in H8.
unfold In in H8.
destruct H6.
assert (∃ y z : Z, x0 = a * y + b * z).

exists (1 + x2 * - x1).
exists (x3 * x1 * -1) .
rewrite NOW in H5.
rewrite (M1 (x3*x1) (-1)).
rewrite <-M2.
rewrite (M1 b (-1)).
rewrite M2 .
rewrite A1P7.
rewrite <-M2.
exact H5.
pose proof (conj H9 H6).
tauto.
rewrite <-H6 in H889.
rewrite A3 in H889.
unfold divide in H889.
assert ( x | a).
unfold divide.
exists x1.
rewrite M1. 
tauto.
destruct H2.
pose proof ( Euclides b x) as H2.
rewrite <-H6 in H7.
destruct H1.
destruct H5.
destruct H6.
destruct H4.
exact H7.
destruct H78.
pose proof H7 as H90.
apply H2 in H90.
destruct H90.
destruct H4.
destruct H4.
destruct H5.
unfold In, S in H91.
destruct H91.
destruct H5.
destruct H5.
apply H2 in H7.
destruct H7.
destruct H7.
destruct H7.
destruct H10.
destruct H10.
assert (x10 ∈ S ).
unfold S ,In.
split.
symmetry in H7.
rewrite A1 in H7.
apply (S1 (x10 +(x * x11)) b (-(x*x11)))  in H7.
rewrite A2, A4, A3 in H7.
rewrite H5 in H7.
rewrite D1 in H7.
destruct H1.
rewrite (A1 (a * x8 * x11) (b * x9 * x11)) in H7.
rewrite <-A1P7 in H7.
rewrite M1 in H7.
rewrite D1 in H7.



rewrite <-A2 in H7.
rewrite M1 in H7.
rewrite (M2 b x9 x11) in H7.
rewrite (M1 b (x9*x11)) in H7.
rewrite <-M2 in H7.
rewrite <-M2 in H7.
rewrite <-(M3 b) in  H7 at 1.
rewrite  (M1 b 1) in H7.

rewrite <-D1 in H7.
rewrite A1 in H7.
rewrite M2 in H7.
rewrite NOW in H7.
rewrite M2 in H7.
exists  (x8 * - x11).
exists (1 + -1 * x9 * x11).
rewrite (M1 (1 + -1 * x9 * x11)  b ) in H7.
exact H7.
exact H10.
apply H3 in H12.
pose proof (Y x10 x).
destruct H12.
tauto.
destruct H13.
tauto.
destruct H13.
tauto.
symmetry in H12.
tauto.
rewrite <-H10 in H7.
rewrite A3 in H7.
assert (x | b).
unfold divide.
exists x11.
rewrite M1.
tauto.
unfold cprime in H.
pose proof (conj H9 H12).
apply H in H13.
destruct H13.
exists x8, x9.
rewrite M3, A1P6, A3 .
symmetry. rewrite H13 in H5. exact H5.
rewrite H13 in H6.
apply I3 in H6.
rewrite A1P5, PORRA in H6.
pose proof I778.
pose proof (T 1).
tauto.
unfold Included , S.
unfold In.
intros.
destruct H3.
pose proof (lt_N_elt).
apply H5 in H4.
tauto.
Qed.


Theorem A2P6 : ∀ a b c : Z, prime (a)  ∧ (a | b * c) ⇒ (a | b) ∨ (a | c).
Proof.
intros.
destruct H.
case (classic (a | b)).
tauto.
case( classic (c=0)).
intros.
assert (a | c).
unfold divide.
rewrite H1 .
exists 0.
rewrite A1P6.
tauto.
tauto.
intros.

unfold divide in H0.
destruct H0.
symmetry in H0.
intros.
assert( a $ b).
unfold cprime.
intros.
unfold prime in H.
auto.
intros.
destruct H3.
case (classic (q>0)).
intros.
pose proof (conj H5 H3).
destruct H.
destruct H6.
apply H7 in H8.
destruct H8.
tauto.
destruct H8.
rewrite H8 in H4.
tauto.
assert ( a| b).
unfold divide.
rewrite H8 in H4.

unfold divide in H4.
destruct H4.
exists (-x0).
rewrite <-NOW .
rewrite M2, A1P7 .
tauto.
tauto.
intros.
destruct (T q) as [[H7 [H9 H8]] | [[H7 [H9 H8]] | [H7 [H9 H8]]]].

tauto.
rewrite H9 in H3.
unfold divide in H3.
destruct H3 .
rewrite M1, A1P6 in H3.
assert ((1+1) | 0).
unfold divide.
exists 0.
rewrite A1P6.
tauto.
destruct H.
rewrite <-H3 in H6 .
apply H10 in H6.
destruct H6.
unfold pm in H6.
destruct H6.
apply (S1 (1+1) 1 (-1)) in H6.
rewrite A4 in H6.
rewrite A2, A4, A3 in H6.
pose proof I778.
pose proof (T 1).
tauto.
pose proof I778.
pose proof (R3 0 1 (1+1)).
pose proof H11 as H13.
apply (O1 0 1 1) in H13.
rewrite A1P1 in H13.
pose proof (conj H11 H13).
apply H12 in H14. 
pose proof (R3 (-1) 0 (1+1)).
pose proof H11 as H16.
apply (O1 0 1 (-1)) in H16.
rewrite A1P1, A4 in H16.

pose proof (conj H16 H14).
apply H15 in H17.
pose proof (Y (1+1) (-1)).
tauto.
rewrite H3 in H6.
destruct H6.
pose proof I778.
pose proof (R3 0 1 (1+1)).
pose proof H11 as H13.
apply (O1 0 1 1) in H13.
rewrite A1P1 in H13.
pose proof (conj H11 H13).
apply H12 in H14. 
pose proof (T (1+1)).
tauto.
rewrite PORRA in H6.
pose proof I778.
pose proof (R3 0 1 (1+1)).
pose proof H11 as H13.
apply (O1 0 1 1) in H13.
rewrite A1P1 in H13.
pose proof (conj H11 H13).
apply H12 in H14. 
pose proof (T (1+1)).
tauto.
intros.
destruct H.
pose proof H3 as H10.
apply H6 in H3.
destruct H3.
tauto.
unfold pm in H3.
destruct H3.
rewrite H3 in  H4.
tauto.
rewrite H3 in H4.
assert ( a | b).
unfold divide.
unfold divide in H4.
destruct H4.
exists (x0*-1).
rewrite M2, A1P7.
tauto.
tauto.
apply Bezout in H3.
destruct H3.
destruct H3.
assert ( a | b*c).
unfold divide.
exists x.
symmetry.
tauto.
assert ( b*c | b*c*x1).
unfold divide.
exists x1.
rewrite (M1 x1 (b*c)).
tauto.
pose proof ( A2P2 a (b*c) (b * c * x1)).
apply H6 in H4.
assert ((a | b * c )).
unfold divide.
exists x.
symmetry.
tauto.
apply H6 in H7.
unfold divide in H7.
destruct H7.
rewrite A1 in H3.
apply (S1 (b * x1 + a * x0)  1 (-(a*x0))) in H3.
rewrite A2, A4 , A3 in H3.
rewrite M2 , M1, M2 ,(M1 x1 b) , H3 in H7.
rewrite M1, D1 in H7.
rewrite (M1 1 c) , M3 in H7.
rewrite <-A1P7 , M1, (M1 a x0),  <-M2 , NOW in H7.
apply (S1 ( c + - c * (x0 * a)) (x2 * a) (-(- c * (x0 * a))) ) in H7.
rewrite  A2 , A4 , A3 in H7.
rewrite <-(A1P7 c) in H7.
rewrite <-A1P7 in H7.
rewrite <-M2 in H7.
rewrite <-M2 in H7.
rewrite <-M2 in H7.
rewrite A1P7  in H7.
rewrite A1P5 in H7.
rewrite A1P3 in H7.
rewrite <-D1 in H7.
right.
unfold divide.
exists (x2 + c * x0).
tauto.
exact H5.
exact H5.
Qed.

Theorem A3P1 : ∀ a b : Z, a < b ∨ a = b ∨ a > b.
Proof.
intros.
 destruct (Y a b) as [[H0 [H1 H2]] | [[H0 [H1 H2]] | [H0 [H1 H2]]]].
tauto.
tauto.
tauto.
Qed.
Theorem A3P4 : ∀ a b : Z,
    0 < a ⇒ 0 < b ⇒ (∃ q r : Z, a = b * q + r ∧ 0 ≤ r < b).
Proof.
intros.
pose proof (Euclides a b).
apply H1 in H0.
destruct H0, H0.
exists x0, x.
tauto.
Qed.
Theorem A3P2 : ∀ a : Z, ¬ (0 < a < 1).
Proof.
intros.
case (classic ( 0 < a < 1)).
intros.
pose proof (Davi a).
destruct H.
apply H0 in H.
destruct H.
rewrite H in H1.
destruct (Y  1 1 ) as [[H3 [H4 H5]] | [[H3 [H4 H5]] | [H3 [H4 H5]]]].
tauto.
tauto.
tauto.
pose proof (conj H H1).
apply R3 in H2.
destruct (Y  1 1 ) as [[H3 [H4 H5]] | [[H3 [H4 H5]] | [H3 [H4 H5]]]].
tauto.
tauto.
tauto.
tauto.
Qed.
Theorem A3P3 : ∀ a b : Z, b>0 ∧ (a | b) ⇒ a ≤ b.
Proof.
intros.
destruct (T (a)) as [[H0 [H1 H2]] | [[H0 [H1 H2]] | [H0 [H1 H2]]]].
destruct H.
unfold divide in H3.
destruct H3.
rewrite H3 .
rewrite H3 in H.
destruct (T (x)) as [[H4 [H33 H333]] | [[H4 [H33 H333]] | [H4 [H33 H333]]]].
apply Davi in H4.
destruct H4.
rewrite H4.
right.
rewrite M1, M3 .
tauto.
left.
pose proof (O2 1 x a).
apply H5 in H4.
rewrite (M1 1 a) ,M3 in H4.
exact H4.
tauto.
rewrite H33 in H.
rewrite A1P6 in H.
pose proof (T 0).
tauto.
pose proof (O2 0 a (-x)).
apply H5 in H0.
rewrite A1P6 in H0.
apply I3 in H0.
rewrite <-(NOW), <-(NOW x) in H0.
rewrite M2 in H0.
rewrite M2 in H0.
rewrite A1P7 in H0.
rewrite A1P5 in H0.
rewrite M3, PORRA, M1 in H0.
pose proof (T (x*a)).
tauto.
apply I3 in H333.
rewrite PORRA in H333.
tauto.
destruct H.

rewrite H1 in H3.
unfold divide in H3.
destruct H3.
rewrite M1, A1P6 in H3.
rewrite H3 in H.
pose proof (T 0).
tauto.
destruct H.
unfold divide in H3.
destruct H3.
pose proof (R3 a 0 b).
pose proof (conj H2 H).

apply H4 in H5.
left.
exact H5.
Qed.
Notation "x ≠ ± y" := (¬ (x = ± y)) (at level 60).
Definition gcd (a b d : Z) :=
  (d | a) ∧ (d | b) ∧ ∀ x : Z, (x | a) ⇒ (x | b) ⇒ (x | d).
Theorem tod: ∀ a b : Z,  1 ∈ gcd a b <-> a$b.
Proof.
intros.
split.
intros.
unfold In, gcd in H.
unfold cprime.
destruct H.
destruct H0.
intros.
pose proof (H1 q).
destruct H2.
apply H3 in H2.
unfold divide in H2.
destruct H2.
symmetry in H2.
apply SD in H2.
tauto.

tauto.
intros.
unfold In, gcd.
unfold cprime in H.
intros.
intros.
assert ( (1 | a)).
exists a .
rewrite M3.
tauto.
assert ( (1 | b)).
exists b .
rewrite M3.
tauto.
pose proof (conj H0 H1).
auto.
intuition.
pose proof (H x).
intuition.
rewrite H6. 
unfold divide.
exists 1.
rewrite M3 .
tauto.
rewrite H6. 
unfold divide.
exists (-1).
rewrite A1P7, A1P5 .
tauto.
Qed.


Theorem A4P1 : ∀ a b : Z, 1 ∈ gcd a b ⇒ ∃ x y : Z, a * x + b * y = 1.
Proof.
intros.
pose proof (Bezout a b).
apply tod in H.
apply H0 in H.
tauto.
Qed.

Theorem A4P2 : ∀ a b p : Z, p ∈ prime ⇒ (p | a * b) ⇒ (p | a) ∨ (p | b).
Proof.
intros.
pose proof (A2P6  p a b).
intuition.
Qed.
Theorem I22 : forall P, (((P 1) ∧ (forall a : Z, (P a) -> (P (a + 1)))) -> (forall a : Z, ((0 < a) -> (P a)))).
Proof.
intros.
set (S := {  x  : Z | (¬(P0 x)) ∧ x>0 }).
pose proof (W1 S).

intros.
case (classic (S = ∅) ).
intros.

case (classic ( a ∈ S) ).
intros.

rewrite H2 in H3.
unfold In in H3.
tauto.
intros.
case (classic ( P0 a)).
tauto.
intros.
assert ( a ∈ S).
unfold In, S.
intuition.
contradiction.
intros.
apply H1 in H2.
destruct H2.
destruct H2.

case (classic (( x + - 1) ∈ S) ).
intros.
apply H3 in H4.
destruct H4.
apply (O1 x (x + -1) ( - x + 1)) in H4.
rewrite <-A2 in H4.
rewrite A4 in H4.
rewrite A1P1 in H4.
rewrite <-A2 in H4.
rewrite (A1 (x + -1) (- x) )  in H4.
rewrite A1 in H4.
rewrite <-A2 in H4.
rewrite A1 in H4.
rewrite <-A2 in H4.
rewrite (A1 x (-1)) in H4.
rewrite A1 in H4.
rewrite (A1 (-1) x ) in H4.
rewrite <-A2 in H4.
rewrite <-A2 in H4.
rewrite A1P2 in H4.
rewrite A1P1, A1P2 in H4.
pose proof (Y 1 0).
pose proof I778.
tauto.
apply (S1 x (x + -1) ( - x + 1)) in H4.
rewrite <-A2 in H4.
rewrite A4 in H4.
rewrite A1P1 in H4.
rewrite <-A2 in H4.
rewrite (A1 (x + -1) (- x) )  in H4.
rewrite A1 in H4.
rewrite <-A2 in H4.
rewrite A1 in H4.
rewrite <-A2 in H4.
rewrite (A1 x (-1)) in H4.
rewrite A1 in H4.
rewrite (A1 (-1) x ) in H4.
rewrite <-A2 in H4.
rewrite <-A2 in H4.
rewrite A1P2 in H4.
rewrite A1P1, A1P2 in H4.
pose proof (Y 1 0).
pose proof I778.
tauto.
intros.
unfold S in H4.
unfold In , S in H2.
destruct H2.
apply Davi in H5.
destruct H5.
destruct H.
rewrite H5 in H2.
tauto.
apply (O1 1 x (-1)) in H5.
rewrite A4 in H5.
case (classic  (P0 (x + -1))).
intros.
destruct H.
apply H7 in H6.
rewrite A2 in H6.
rewrite A1P2, A3 in H6.
tauto.
intros.
pose proof (conj H6 H5).
assert ( (x + -1) ∈ S ).
unfold In, S.
tauto.
tauto.
unfold S.
pose proof lt_N_elt.
unfold Included.
intuition.
unfold In in H1.
destruct H1.
pose proof lt_N_elt.
apply <-H7 in H6.
tauto.
Qed.
Theorem NNPP : ∀ P : Prop, ¬¬ P ⇒ P.
Proof.
intros.
case (classic (¬P0)).
tauto.
tauto.
Qed.
Theorem A4P3calma : ∀ n : Z, n> 1 -> ∃ p : Z, p ∈ prime ∧ (p | n).
Proof.
intros.
set (S :=  {x : Z | x > 1 ∧ ¬ (∃ p : Z, p ∈ prime ∧ (p | x) )}).
pose proof (W1 S).
case (classic ( S ≠ ∅ )).
intros.
apply H0 in H1.
destruct H1.
destruct H1.
set (U := {y :Z | y>1 ∧ (y | x)}).
pose proof (W1 U).
case (classic ( U = ∅ )).
intros.
assert ( x ∈ U).
unfold In, U.
split.
unfold In, S in H1.


tauto.
unfold divide.
exists 1.
rewrite A1P3.
tauto.
rewrite H4 in H5.
unfold In in H5.
tauto.
intros.
apply H3 in H4.
destruct H4.
destruct H4.
unfold In, U in H4.
destruct H4.
pose proof (A3P3 x0 x ).
pose proof (R3 0 1 x).
pose proof I778.
unfold In, S in H1.
destruct H1.

pose proof (conj H9 H1).
apply H8 in H11.
pose proof (conj H11 H6).
apply H7 in H12.

destruct H12.
case (classic ( x0 ∈ S)).
intros.
apply H2 in H13.
destruct H13.
pose proof (Y x x0).
tauto.
symmetry in H13.
pose proof (Y x0 x).
tauto.
intros.
unfold In ,S in H13.
intuition.
apply NNPP in H13.
destruct H13.
destruct H8.
pose proof (A2P2 x1 x0 x).
apply H15 in H13.
assert ( (∃ p : Z, p ∈ prime ∧ (p | x)) ).
exists x1.
tauto.
tauto.
tauto.
rewrite H7 in H12.
pose proof (Y x x).
tauto.
assert (x ∈ prime).
unfold In, prime.
split.
unfold pm.
case (classic  (x=1)).
intros.
rewrite H13 in H1.
pose proof (Y 1 1).
tauto.
intros.
case (classic  (x=(-1))).
intros.
pose proof (R3 (-1) 1 x).
pose proof I778.
pose proof I778.
apply I3 in H16.
rewrite PORRA in H16.
pose proof (R3 (-1) 0 1).
intuition.
pose proof (Y (-1) x).
symmetry in H14.
tauto.
rewrite H20 in H8.
pose proof ( Y (-1) (-1)).
tauto.
intros.
tauto.
intros.
destruct (T d) as [[H14 [H15 H16]] | [[H14 [H15 H16]] | [H14 [H15 H16]]]].

apply Davi in H14.
destruct H14.
left.
unfold pm.
tauto.
assert (d ∈ U).
unfold In, U.
tauto.
apply H5 in H17.
rewrite H12 in H17.
pose proof ( A3P3 d x).
pose proof (conj H11 H13).
apply H18 in H19.
destruct H17.
pose proof (Y d x).
tauto.
right.
unfold pm.
auto.
rewrite H15 in H13.
unfold divide in H13.
destruct H13.
rewrite M1, A1P6 in H13.
pose proof (T x).
tauto.
apply I3 in H16.
rewrite PORRA in H16.
apply Davi in H16.
destruct H16.
left.
unfold pm.
apply (S2 (-d) 1 (-1)) in H16.
rewrite NOW in H16.
rewrite A1P5, M1, M3 in H16.
tauto.
assert ((-d) ∈ U).
unfold In, U.
assert ( (-d) | x).
unfold divide in H13.
unfold divide.
destruct H13.
exists (-x1).
rewrite <- NOW.
rewrite M2.
rewrite A1P7, A1P5.

tauto.
tauto.
apply H5 in H17.
rewrite H12 in H17.
pose proof ( A3P3 (-d) x).
assert ( (-d) | x).
unfold divide in H13.
unfold divide.
destruct H13.
exists (-x1).
rewrite <- NOW.
rewrite M2.
rewrite A1P7, A1P5.

tauto.
pose proof (conj H11 H19).
apply H18 in H20.
destruct H17.
pose proof (Y (-d) x).
tauto.
right.
unfold pm.
auto.
symmetry in H17.
apply (S2 (-d) x (-1)) in H17.
rewrite NOW in H17.
rewrite A1P5, M1 in H17.
rewrite A1P7 in H17.
tauto.
assert (∃ p : Z, p ∈ prime ∧ (p | x)).
exists x.
split.
tauto.
exists 1.
rewrite A1P3.
tauto.
tauto.
unfold Included.
intros.
unfold In, U in H5.
destruct H5.
pose proof I778 .
pose proof(R3 0 1 x0).
pose proof (conj H7 H5).
apply H8 in H9.
apply <-(lt_N_elt).
tauto.
unfold Included.
intros.
unfold In, S in H2.
destruct H2.
pose proof I778 .
pose proof(R3 0 1 x).
pose proof (conj H4 H2).
apply H5 in H6.
apply <-(lt_N_elt).
tauto.
intros.
apply NNPP in H1.

case (classic (n ∈ S )).
intros.
rewrite H1 in H2.
unfold In in H2.
tauto.
intros.
unfold In, S in H2.
intuition.
apply NNPP in H2.
tauto.
Qed.


Theorem A4P3 : ∀ n : Z, n≠ ±1 -> ∃ p : Z, p ∈ prime ∧ (p | n).
Proof.
intros.
destruct (T n) as [[H0 [H1 H2]] | [[H0 [H1 H2]] | [H0 [H1 H2]]]].
apply Davi in H0.
destruct H0.
unfold pm in H.
tauto.
pose proof (A4P3calma n).
apply H3 in H0.
tauto.
assert ( (1+1) ∈ prime).
unfold In, prime.
split.
unfold pm.
case (classic ((1+1)=1)).
intros.
apply (S1 (1+1) 1 (-1)) in H3.
rewrite A2, A4, A3 in H3.
pose proof I778.
pose proof (T 1).
tauto.
case (classic ((1+1)=(-1))).
intros.
pose proof (R3 0 1 (1+1)).
pose proof I778.
pose proof I778.
apply (O1 0 1 1) in H7.
rewrite A1P1 in H7.
pose proof (conj H6 H7).
apply H5 in H8.
pose proof (R3 (-1) 0 (1+1)).
apply I3 in H6.
rewrite PORRA in H6.
pose proof (conj H6 H8).
apply H9 in H10.
pose proof ( Y (-1) (1+1)).
symmetry in H3.
tauto.
intros.
tauto.
intros.
pose proof (A3P3 d (1+1)) .
pose proof (R3 0 1 (1+1)).
pose proof I778.
pose proof I778.
apply (O1 0 1 1) in H7.
rewrite A1P1 in H7.
pose proof (conj H6 H7).
apply H5 in H8.
pose proof (conj H8 H3) .
apply H4 in H9.
destruct (T d) as [[H10 [H11 H12]] | [[H10 [H11 H12]] | [H10 [H11 H12]]]].
apply Davi in H10.
destruct H10.
unfold pm.
tauto.
apply Sena2 in H10.
destruct H10.
apply (S1 1 (d+-1) 1) in H10.
rewrite A2 in H10.
rewrite A1P2, A3 in H10.
symmetry in H10.
unfold pm.
tauto.
apply (O1 1 (d+-1) 1) in H10.
rewrite A2 in H10.
rewrite A1P2, A3 in H10.
pose proof ( Y (1+1) d).
destruct H9.
tauto.
symmetry in H9.
tauto.
unfold divide in H3.
destruct H3.
rewrite H11 in H3.
rewrite M1, A1P6 in H3.
pose proof (T (1+1)).
tauto.
apply I3 in H12.
rewrite PORRA in H12. 
apply Davi in H12.
destruct H12.
unfold pm.
apply (S2 (-d) 1 (-1)) in H12.

rewrite (M1 1 (-1)) in H12.
rewrite M3 in H12.
rewrite NOW, A1P5 in H12.
tauto.
unfold divide in H3.
destruct H3. 
assert ( ((-d) | 1 + 1)).
exists (-x).
rewrite <-NOW,M2, A1P7,A1P5.
tauto.



pose proof (A3P3 (-d) (1+1)) .
pose proof (R3 0 1 (1+1)).
pose proof I778.
pose proof I778.
apply (O1 0 1 1) in H17.
rewrite A1P1 in H17.
pose proof (conj H6 H7).
apply H15 in H18.

pose proof (conj H18 H13) .
apply H14 in H19.
pose proof (Sena (-d) 1).
apply H20 in H12.
destruct H12.
apply (S2 (-d) (1+1) (-1)) in H12.
rewrite NOW in H12.
rewrite A1P5,NOW in H12.
right.
right.
tauto.
pose proof (Y (1+1) (-d)).
intuition.
symmetry in H9.
contradiction.
symmetry in H9.
tauto.
exists (1+1) .
split.
tauto.
unfold divide.
exists 0.
rewrite H1 .
rewrite A1P6.
reflexivity.
apply I3 in H2.
rewrite PORRA in H2.
apply Davi in H2.
destruct H2.
apply (S2 (-n) (1) (-1)) in H2.
rewrite NOW in H2.
rewrite A1P5,NOW in H2.
unfold pm in H.
tauto.

pose proof (A4P3calma (-n)).
apply H3 in H2.
destruct H2.
destruct H2.
destruct H4.
exists (-x).
split.
unfold prime, In.
unfold 
split.
unfold In, prime in H2.
destruct H2.
split.
case (classic (-x =1)).
intros.
apply (S2 (-x) 1 (-1)) in H6.
rewrite NOW, A1P5 in H6.
rewrite M1,M3 in H6.
unfold pm in H2.

tauto.
intros.
case (classic (-x =-1)).
intros.
apply (S2 (-x) (-1) (-1)) in H7.
rewrite NOW, A1P5 in H7.
rewrite NOW,A1P5 in H7.
unfold pm in H2.

tauto.
intros.
unfold pm.
tauto.
intros.
destruct H6.
assert ((d | x)).
unfold divide.
exists (-x1).
apply (S2 (-x) (x1*d) (-1)) in H6.
rewrite NOW, A1P5 in H6.
rewrite M1 in H6.
rewrite <-(M2) in H6.
rewrite A1P7 in H6.
tauto.
apply H5 in H7.
destruct H7.
tauto.
right.
unfold pm.
rewrite A1P5.
unfold pm in H7.
tauto.
unfold divide.
exists (x0).
apply (S2 (-n) (x0*x) (-1)) in H4.
rewrite NOW, A1P5 in H4.
rewrite M2, NOW in H4.
tauto.
Qed.
