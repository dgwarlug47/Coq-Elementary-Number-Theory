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
