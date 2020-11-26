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

