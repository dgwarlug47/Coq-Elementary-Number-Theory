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
