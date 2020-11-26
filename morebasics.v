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