(******************************************************************************)
(*          This project is distributed under the terms of the                *)
(*            GNU Lesser General Public License version 2.1                   *)
(*                (see file LICENSE for more details).                        *)
(*     It is developmented in the CoqIDE (version 8.13.2) for windows.        *)
(*                                                                            *)
(*                       This project is implemented by                       *)
(*         Wensheng Yu, Dakai Guo, Si Chen, Guowei Dou and Shukun Len         *)
(*                                                                            *)
(*   Beijing Key Laboratory of Space-ground Interconnection and Convergence,  *)
(*                     School of Electronic Engineering,                      *)
(*        Beijing University of Posts and Telecommunications, Beijing         *)
(******************************************************************************)
(*                  This file presents a formalization of                     *)
(*                     the uniqueness of real numbers,                        *)
(*                   namely, any two algebraic structures                     *)
(*        that satisfy all the axioms of real numbers are isomorphic.         *)
(*                                                                            *)
(*               The work is based on the formalization of                    *)
(*                   Morse-Kelley axiomatic set theory.                       *)
(******************************************************************************)

(** reals_uniqueness *)

Require Export reals_axioms.

Section real_numbers_uniqueness.


Variable R_str1 : Real_Struct.
Variable RA1 : Real_Axioms R_str1.
Variable R_str2 : Real_Struct.
Variable RA2 : Real_Axioms R_str2.


Let R1 := @R R_str1.
Let R2 := @R R_str2.
Let N1 := N R_str1.
Let N2 := N R_str2.
Let Z1 := Z R_str1.
Let Z2 := Z R_str2.
Let Q1 := Q R_str1.
Let Q2 := Q R_str2.
Let Sup1a := Sup1 R_str1.
Let Sup1b := Sup1 R_str2.


Declare Scope R1_scope.
Delimit Scope R1_scope with r1.
Declare Scope R2_scope.
Delimit Scope R2_scope with r2.

Notation "0" := (@zeroR R_str1).
Notation "0 '" := (@zeroR R_str2).

Notation "1" := (@oneR R_str1).
Notation "1 '" := (@oneR R_str2).

Notation "x + y" := ((@fp R_str1)[[x, y]])
  (at level 50, left associativity) : R1_scope.
Notation "x + y" := ((@fp R_str2)[[x, y]])
  (at level 50, left associativity) : R2_scope.

Notation "x · y" := ((@fm R_str1)[[x, y]])(at level 40) : R1_scope.
Notation "x · y" := ((@fm R_str2)[[x, y]])(at level 40) : R2_scope.

Notation "- a" := (∩(\{ λ u, u ∈ R1 /\ (u + a)%r1 = 0 \}))
  (at level 35, right associativity) : R1_scope.
Notation "- a" := (∩(\{ λ u, u ∈ R2 /\ (u + a)%r2 = 0' \}))
  (at level 35, right associativity) : R2_scope.

Notation "x - y" := (x + (-y))%r1 : R1_scope.
Notation "x - y" := (x + (-y))%r2 : R2_scope.

Notation "a ⁻" := (∩(\{ λ u, u ∈ (R1 ~ [0]) /\ (u · a)%r1 = 1 \}))
  (at level 30) : R1_scope.
Notation "a ⁻" := (∩(\{ λ u, u ∈ (R2 ~ [0']) /\ (u · a)%r2 = 1' \}))
  (at level 30) : R2_scope.

Notation "m / n" := (m · (n⁻))%r1 : R1_scope.
Notation "m / n" := (m · (n⁻))%r2 : R2_scope.

Notation "x ≤ y" := ([x,y] ∈ (@Leq R_str1))(at level 60) : R1_scope.
Notation "x ≤ y" := ([x,y] ∈ (@Leq R_str2))(at level 60) : R2_scope.

Notation "x < y" := (x ≤ y /\ x <> y)%r1 : R1_scope.
Notation "x < y" := (x ≤ y /\ x <> y)%r2 : R2_scope.


Let zero_in_R_str1 := @zero_in_R R_str1 RA1.
Let zero_in_R_str2 := @zero_in_R R_str2 RA2.
Let one_in_R_Co_str1 := @one_in_R_Co R_str1 RA1.
Let one_in_R_Co_str2 := @one_in_R_Co R_str2 RA2.
Let Plus_close_str1 := @Plus_close R_str1 RA1.
Let Plus_close_str2 := @Plus_close R_str2 RA2.
Let Mult_close_str1 := @Mult_close R_str1 RA1.
Let Mult_close_str2 := @Mult_close R_str2 RA2.
Let Plus_neg1a_str1 := @Plus_neg1a R_str1 RA1.
Let Plus_neg1a_str2 := @Plus_neg1a R_str2 RA2.
Let Plus_neg1b_str1 := @Plus_neg1b R_str1 RA1.
Let Plus_neg1b_str2 := @Plus_neg1b R_str2 RA2.
Let Plus_neg2_str1 := @Plus_neg2 R_str1 RA1.
Let Plus_neg2_str2 := @Plus_neg2 R_str2 RA2.
Let Minus_P1_str1 := @Minus_P1 R_str1 RA1.
Let Minus_P1_str2 := @Minus_P1 R_str2 RA2.
Let Minus_P2_str1 := @Minus_P2 R_str1 RA1.
Let Minus_P2_str2 := @Minus_P2 R_str2 RA2.
Let Mult_inv1_str1 := @Mult_inv1 R_str1 RA1.
Let Mult_inv1_str2 := @Mult_inv1 R_str2 RA2.
Let Mult_inv2_str1 := @Mult_inv2 R_str1 RA1.
Let Mult_inv2_str2 := @Mult_inv2 R_str2 RA2.
Let Divide_P1_str1 := @Divide_P1 R_str1 RA1.
Let Divide_P1_str2 := @Divide_P1 R_str2 RA2.
Let Divide_P2_str1 := @Divide_P2 R_str1 RA1.
Let Divide_P2_str2 := @Divide_P2 R_str2 RA2.
Let OrderPM_Co9_str1 := @OrderPM_Co9 R_str1 RA1.
Let OrderPM_Co9_str2 := @OrderPM_Co9 R_str2 RA2.
Let OrderPM_Co10_str1 := @OrderPM_Co10 R_str1 RA1.
Let OrderPM_Co10_str2 := @OrderPM_Co10 R_str2 RA2.
Let N_Subset_R_str1 := @N_Subset_R R_str1 RA1.
Let N_Subset_R_str2 := @N_Subset_R R_str2 RA2.
Let one_in_N_str1 := @one_in_N R_str1 RA1.
Let one_in_N_str2 := @one_in_N R_str2 RA2.
Let Nat_P1a_str1 := @Nat_P1a R_str1 RA1.
Let Nat_P1a_str2 := @Nat_P1a R_str2 RA2.
Let Nat_P1b_str1 := @Nat_P1b R_str1 RA1.
Let Nat_P1b_str2 := @Nat_P1b R_str2 RA2.
Let N_Subset_Z_str1 := @N_Subset_Z R_str1.
Let N_Subset_Z_str2 := @N_Subset_Z R_str2.
Let Z_Subset_R_str1 := @Z_Subset_R R_str1 RA1.
Let Z_Subset_R_str2 := @Z_Subset_R R_str2 RA2.
Let Int_P1a_str1 := @Int_P1a R_str1 RA1.
Let Int_P1a_str2 := @Int_P1a R_str2 RA2.
Let Int_P1b_str1 := @Int_P1b R_str1 RA1.
Let Int_P1b_str2 := @Int_P1b R_str2 RA2.
Let Z_Subset_Q_str1 := @Z_Subset_Q R_str1 RA1.
Let Z_Subset_Q_str2 := @Z_Subset_Q R_str2 RA2.
Let Q_Subset_R_str1 := @Q_Subset_R R_str1 RA1.
Let Q_Subset_R_str2 := @Q_Subset_R R_str2 RA2.
Let Rat_P1a_str1 := @Rat_P1a R_str1 RA1.
Let Rat_P1a_str2 := @Rat_P1a R_str2 RA2.
Let Rat_P1b_str1 := @Rat_P1b R_str1 RA1.
Let Rat_P1b_str2 := @Rat_P1b R_str2 RA2.
Let Abs_in_R_str1 := @Abs_in_R R_str1 RA1.
Let Abs_in_R_str2 := @Abs_in_R R_str2 RA2.


Local Hint Resolve
  zero_in_R_str1     zero_in_R_str2     one_in_R_Co_str1     one_in_R_Co_str2
  Plus_close_str1    Plus_close_str2    Mult_close_str1      Mult_close_str2
  Plus_neg1a_str1    Plus_neg1a_str2    Plus_neg1b_str1      Plus_neg1b_str2
  Plus_neg2_str1     Plus_neg2_str2     Minus_P1_str1        Minus_P1_str2
  Minus_P2_str1      Minus_P2_str2      Mult_inv1_str1       Mult_inv1_str2
  Mult_inv2_str1     Mult_inv2_str2     Divide_P1_str1       Divide_P1_str2
  Divide_P2_str1     Divide_P2_str2     OrderPM_Co9_str1     OrderPM_Co9_str2
  OrderPM_Co10_str1  OrderPM_Co10_str2  N_Subset_R_str1      N_Subset_R_str2
  one_in_N_str1      one_in_N_str2      Nat_P1a_str1         Nat_P1a_str2
  Nat_P1b_str1       Nat_P1b_str2       N_Subset_Z_str1      N_Subset_Z_str2
  Z_Subset_R_str1    Z_Subset_R_str2    Int_P1a_str1         Int_P1a_str2
  Int_P1b_str1       Int_P1b_str2       Z_Subset_Q_str1      Z_Subset_Q_str2
  Q_Subset_R_str1    Q_Subset_R_str2    Rat_P1a_str1         Rat_P1a_str2
  Rat_P1b_str1       Rat_P1b_str2       Abs_in_R_str1        Abs_in_R_str2 : real.


Theorem UniqueT1 : ∀ f, Function f -> dom(f) = R1 -> ran(f) ⊂ R2
  -> (∀ x y, x ∈ R1 -> y ∈ R1 -> f[(x + y)%r1] = (f[x] + f[y])%r2
    /\ f[(x · y)%r1] = (f[x] · f[y])%r2)
  -> f[0] = 0' /\ (ran(f) <> [0'] -> f[1] = 1').
Proof.
  assert (H:True) by auto.
  intros. assert (f[0] ∈ R2 /\ f[1] ∈ R2) as [].
  { split; apply H2; [apply (@ Property_ran 0)|
    apply (@ Property_ran 1)]; apply Property_Value; auto;
    rewrite H1. apply zero_in_R. apply one_in_R_Co; auto. }
  pose proof (@zero_in_R R_str1 RA1).
  apply (H3 0 0) in H6 as []; auto.
  assert (f[(0 + 0)%r1] = f[0]). { rewrite Plus_P1; auto. }
  rewrite H6 in H8. apply Plus_Co3 in H8; auto.
  rewrite Minus_P1 in H8; auto. split; auto. intros.
  pose proof one_in_R_Co. apply (H3 1 1) in H10 as []; auto.
  assert (f[(1 · 1)%r1] = f[1]). { rewrite Mult_P1; auto. }
  rewrite H12 in H11. symmetry in H11.
  assert (f[1] ∈ (R2 ~ [0'])).
  { apply MKT4'; split; auto. apply AxiomII; split; eauto.
    intro. apply MKT41 in H13; eauto. elim H9.
    apply AxiomI; split; intros. apply Einr in H14 as [x[]]; auto.
    pose proof H14. rewrite H1 in H14,H16.
    apply (H3 x 1) in H16 as []; auto.
    rewrite Mult_P1,H13,PlusMult_Co1 in H17; auto.
    apply MKT41; eauto. rewrite H15; auto.
    rewrite <-H1 in H14. apply Property_Value,Property_ran in H14; auto.
    apply MKT41 in H14; eauto. rewrite H14.
    assert (0∈dom( f)). rewrite H1. auto.
    apply Property_Value,Property_ran in H15; auto.
    rewrite H8 in H15; auto. }
  apply Mult_Co3 in H11; auto. rewrite Divide_P1 in H11; auto.
Qed.

Lemma UniqueT2_Lemma1 : ∀ f, Function f -> dom(f) = R1 -> ran(f) ⊂ R2
  -> (∀ x y, x ∈ R1 -> y ∈ R1 -> f[(x + y)%r1] = (f[x] + f[y])%r2
    /\ f[(x · y)%r1] = (f[x] · f[y])%r2)
  -> ran(f) <> [0']
  -> (∀ m, m ∈ N1 -> f[m] ∈ N2).
Proof.
  intros. set (E := \{ λ u, u ∈ N1 /\ f[u] ∈ N2 \}).
  assert (E ⊂ N1 /\ 1 ∈ E) as [].
  { split. unfold Included; intros. apply AxiomII in H5; tauto.
    apply AxiomII; repeat split; eauto.
    apply UniqueT1 in H3; auto. rewrite H3; auto. }
  assert (E = N1).
  { apply MathInd; auto. intros. apply AxiomII; repeat split;
    eauto. pose proof H7.
    apply H5,N_Subset_R,(H2 x 1) in H8 as []; auto.
    rewrite H8. apply UniqueT1 in H3; auto. rewrite H3.
    apply Nat_P1a; auto. apply AxiomII in H7; tauto. }
  rewrite <-H7 in H4. apply AxiomII in H4; tauto.
Qed.

Lemma UniqueT2_Lemma2 : ∀ f, Function f -> dom(f) = R1 -> ran(f) ⊂ R2
  -> (∀ x y, x ∈ R1 -> y ∈ R1 -> f[(x + y)%r1] = (f[x] + f[y])%r2
    /\ f[(x · y)%r1] = (f[x] · f[y])%r2)
  -> ran(f) <> [0']
  -> f[(-(1))%r1] = (-f[1%r1])%r2.
Proof.
  assert (H:True) by auto.
  intros. pose proof one_in_R_Co.
  apply (H3 1 (-(1))%r1) in H5 as []; auto.
  rewrite Minus_P1 in H5; auto.
  assert (∀ m, m ∈ R1 -> f[m] ∈ R2).
  { intros. rewrite <-H1 in H7.
    apply Property_Value,Property_ran in H7; auto. }
  symmetry in H5. apply Plus_Co3 in H5; auto.
  apply UniqueT1 in H0 as []; auto. rewrite H0 in H5.
  rewrite Plus_P4,Plus_P1 in H5; auto.
Qed.

Lemma UniqueT2_Lemma3 : ∀ f, Function f -> dom(f) = R1 -> ran(f) ⊂ R2
  -> (∀ x y, x ∈ R1 -> y ∈ R1 -> f[(x + y)%r1] = (f[x] + f[y])%r2
    /\ f[(x · y)%r1] = (f[x] · f[y])%r2)
  -> ran(f) <> [0']
  -> (∀ r, r ∈ R1 -> f[(-r)%r1] = (-f[r])%r2).
Proof.
  assert (H:True) by auto.
  intros. pose proof one_in_R_Co_str1. apply Plus_neg1a in H6; auto.
  apply (H3 r) in H6 as []; auto.
  rewrite UniqueT2_Lemma2 in H7; auto. pose proof H0.
  apply UniqueT1 in H8 as []; auto. rewrite H9 in H7; auto.
  rewrite Mult_P4,<-PlusMult_Co3 in H7; auto.
  assert (f[r] ∈ R2).
  { rewrite <-H1 in H5.
    apply Property_Value,Property_ran in H5; auto. }
  rewrite (@PlusMult_Co3 R_str2 RA2),(@Mult_P4 R_str2 RA2); auto.
Qed.

Lemma UniqueT2_Lemma4 : ∀ f, Function f -> dom(f) = R1 -> ran(f) ⊂ R2
  -> (∀ x y, x ∈ R1 -> y ∈ R1 -> f[(x + y)%r1] = (f[x] + f[y])%r2
    /\ f[(x · y)%r1] = (f[x] · f[y])%r2)
  -> ran(f) <> [0']
  -> (∀ m, m ∈ R1 -> m <> 0 -> f[m] <> 0').
Proof.
  assert (H:True) by auto.
  intros. intro. elim H4. apply AxiomI; split; intros.
  apply Einr in H8 as [x[]]; auto.
  assert (m ∈ (R1 ~ [0])).
  { apply MKT4'; split; auto. apply AxiomII; split; eauto.
    intro. apply MKT41 in H10; eauto. }
  replace x with (m · (x / m))%r1 in H9. pose proof H8.
  rewrite H1 in H11. pose proof H10. apply Mult_inv1,MKT4' in H12
  as [H12 _]; auto. pose proof H5. apply (H3 m (x / m)%r1) in H13 as [];
  auto. assert (f[(x / m)%r1] ∈ R2).
  { apply H2,(@ Property_ran (x / m)%r1),Property_Value; auto.
    rewrite H1; auto. }
  rewrite H14,H7,Mult_P4,PlusMult_Co1 in H9; auto.
  apply MKT41; eauto. rewrite H1 in H8. pose proof H10.
  apply Mult_inv1,MKT4' in H10 as []; auto. rewrite Mult_P3,(Mult_P4 m),
  <-Mult_P3,Divide_P1,Mult_P1; auto.
  apply MKT41 in H8; eauto. rewrite H8.
  rewrite <-H7. apply (@ Property_ran m),Property_Value; auto.
  rewrite H1; auto.
Qed.

Lemma UniqueT2_Lemma5 : ∀ n, n ∈ Z1 -> (0 < n)%r1 -> n ∈ N1.
Proof.
  intros. apply MKT4 in H as []; auto.
  apply MKT4 in H as []. apply AxiomII in H as [].
  assert (0 < -n)%r1.
  { destruct (@one_is_min_in_N R_str1 RA1) as [_[]].
    apply (@Order_Co2 R_str1 RA1 _ 1); auto. }
  apply (@OrderPM_Co2a R_str1 RA1) in H0; auto.
  destruct H0,H2. elim H4. apply (@Leq_P2 R_str1 RA1); auto.
  apply MKT41 in H; eauto. rewrite H in H0.
  destruct H0. elim H1; auto.
Qed.

Theorem UniqueT2 : ∀ f, Function f -> dom(f) = R1 -> ran(f) ⊂ R2
  -> (∀ x y, x ∈ R1 -> y ∈ R1 -> f[(x + y)%r1] = (f[x] + f[y])%r2
    /\ f[(x · y)%r1] = (f[x] · f[y])%r2)
  -> ran(f) <> [0']
  -> (∀ m, m ∈ Z1 -> f[m] ∈ Z2)
    /\ Function1_1 (f|(Z1)) /\ dom(f|(Z1)) = Z1 /\ ran(f|(Z1)) = Z2
    /\ (∀ x y, x ∈ Z1 -> y ∈ Z1 -> (x ≤ y)%r1 -> (f[x] ≤ f[y])%r2).
Proof.
  assert (H:True) by auto.
  intros. pose proof H0. apply UniqueT1 in H5 as []; auto.
  assert (∀ m, m ∈ R1 -> f[m] ∈ R2).
  { intros. rewrite <-H1 in H7.
    apply Property_Value,Property_ran in H7; auto. }
  assert (∀ m, m ∈ Z1 -> f[m] ∈ Z2).
  { intros. apply MKT4 in H8 as [].
    apply N_Subset_Z,UniqueT2_Lemma1; auto.
    apply MKT4 in H8 as []. apply AxiomII in H8 as [].
    assert (f[(-m)%r1] ∈ N2). { apply UniqueT2_Lemma1; auto. }
    pose proof H0. apply UniqueT2_Lemma2 in H11; auto.
    rewrite (@PlusMult_Co3 R_str1 RA1) in H10; auto.
    pose proof H9. apply N_Subset_R,Plus_neg1b in H12; auto.
    apply (H3 (-(1))%r1 m) in H12 as []; auto.
    replace (∩\{ λ u, u ∈ R /\ u + 1 = 0 \})%r1 with (-(1))%r1 in H10; auto.
    rewrite H13,H11,H6,<-PlusMult_Co3 in H10; auto.
    apply MKT4; right. apply MKT4; left.
    apply AxiomII; split; auto. exists R2. auto.
    apply MKT41 in H8; eauto. rewrite H8,H5.
    repeat (apply MKT4; right). apply MKT41; eauto. }
  assert (Function1_1 (f|(Z1))).
  { split. apply MKT126a; auto. split; unfold Relation; intros.
    - apply AxiomII in H9 as [_[x[y[]]]]; eauto.
    - apply AxiomII' in H9 as [_],H10 as [_].
      apply MKT4' in H9 as [],H10 as [].
      apply AxiomII' in H11 as [_[H11 _]],H12 as [_[H12 _]].
      pose proof H9. apply Property_ran,H2 in H13.
      apply Property_Fun in H9,H10; auto.
      assert (f[y] + f[(-z)%r1] = 0')%r2.
      { pose proof H0. apply UniqueT2_Lemma2 in H14; auto.
        pose proof H12. apply Z_Subset_R in H15; auto.
        apply (H3 (-(1))%r1 z) in H15 as []; auto.
        rewrite (@PlusMult_Co3 R_str1 RA1); auto. replace R with R1; auto.
        rewrite H16, H14,H6,<-PlusMult_Co3,
        <-H9,<-H10,Minus_P1; auto. }
      pose proof H11. apply Z_Subset_R,(H3 y (-z)%r1) in H15 as [];
      auto. rewrite <-H15 in H14. apply NNPP; intro.
      assert (y - z <> 0)%r1.
      { intro. assert (y - z + z = 0 + z)%r1. { rewrite H18; auto. }
        rewrite <-Plus_P3,(Plus_P4 _ z),Minus_P1,(Plus_P4 0),
        Plus_P1,Plus_P1 in H19; auto. }
      assert (f[(y - z)%r1] <> 0'); auto.
      { apply UniqueT2_Lemma4; auto. } }
  assert (dom(f|(Z1)) = Z1).
  { rewrite MKT126b; auto. apply MKT30. rewrite H1; auto. }
  assert (∀ n, n ∈ N2 -> n ∈ ran(f|(Z1))).
  { set (E := \{ λ u, u ∈ N2 /\ u ∈ ran(f|(Z1)) \}). destruct H9.
    assert (E ⊂ N2 /\ 1' ∈ E) as [].
    { split. unfold Included; intros. apply AxiomII in H12; tauto.
      apply AxiomII; repeat split; eauto.
      rewrite <-H6,<-(MKT126c f Z1); auto; [ |rewrite H10; auto].
      apply (@ Property_ran 1),Property_Value; auto. rewrite H10. auto. }
    assert (E = N2).
    { apply MathInd; auto. intros. apply AxiomII in H13 as [_[]].
      apply AxiomII; repeat split; eauto.
      apply AxiomII in H14 as [_[]]. pose proof H15.
      pose proof H16. rewrite reqdi in H17,H18.
      apply Property_Value,Property_ran in H17,H18; auto.
      rewrite <-deqri in H17,H18.
      assert (f[(((f|(Z1))⁻¹)[x] + ((f|(Z1))⁻¹)[1'])%r1] = (x + 1')%r2).
      { rewrite H10 in H17,H18. pose proof H17.
        apply Z_Subset_R,(H3 (((f|(Z1))⁻¹)[x])) in H19 as [H19 _]; auto.
        rewrite <-(MKT126c f Z1),<-(MKT126c f Z1),<-(MKT126c f Z1),
        MKT126c in H19; try rewrite H10; auto.
        rewrite f11vi,f11vi in H19; auto. }
      rewrite H10 in H17,H18. rewrite <-H19,<-(MKT126c f Z1);
      try rewrite H10; auto.
      apply (@ Property_ran (((f|(Z1))⁻¹)[x] + ((f|(Z1))⁻¹)[1'])%r1),
      Property_Value; try rewrite H10; auto. }
    intros. rewrite <-H14 in H15. apply AxiomII in H15; tauto. }
  assert (ReqR: (@R R_str1) = R1) by auto.
  assert (ReqR': (@R R_str2) = R2) by auto.
  assert (ran(f|(Z1)) = Z2).
  { destruct H9. apply AxiomI; split; intros.
    apply Einr in H13 as [x[]]; auto. rewrite MKT126c in H14; auto.
    rewrite H10 in H13. rewrite H14; auto.
    apply MKT4 in H13 as []; auto. apply MKT4 in H13 as [].
    apply AxiomII in H13 as []. pose proof H14. apply H11 in H15.
    rewrite reqdi in H15. apply Property_Value,Property_ran
    in H15; auto. rewrite <-deqri in H15.
    assert (f[(((f|(Z1))⁻¹)[(-z)%r2] · (-(1)))%r1] = (-z · -1')%r2).
    { rewrite H10,ReqR' in H15. pose proof H15.
      apply (@Z_Subset_R R_str1 RA1),(H3 _ (-(1))%r1) in H16 as [_];
      auto. pose proof H0. apply UniqueT2_Lemma2 in H17; auto.
      rewrite <-(MKT126c f Z1 H0 (((f|(Z1))⁻¹)[(-z)%r2])),f11vi,H17,H6 in H16;
      auto. rewrite H10; auto. } rewrite ReqR, ReqR' in *.
    rewrite (Mult_P4 (-z)%r2),PlusMult_Co4 in H16; auto.
    rewrite <-H16. rewrite H10 in H15. rewrite <-(MKT126c f Z1); auto;
    [ |rewrite H10; apply Int_P1b; auto; apply Int_P3; auto].
    apply (@ Property_ran (((f|(Z1))⁻¹)[(-z)%r2] · -(1))%r1),
    Property_Value; auto. rewrite H10. apply Int_P1b; auto.
    apply Int_P3; auto. apply MKT41 in H13; eauto.
    assert (0 ∈ dom(f|(Z1))).
    { rewrite H10. repeat (apply MKT4; right). apply MKT41; eauto. }
    rewrite H13,<-H5,<-(MKT126c f Z1); auto.
    apply (@ Property_ran 0),Property_Value; auto. }
  split; [ |split; [ |repeat split]]; auto. intros.
  destruct (classic (x = y)). rewrite H16. apply Leq_P1; auto.
  assert ((y - x)%r1 ∈ N1).
  { apply UniqueT2_Lemma5. apply Int_P1a; auto.
    apply Int_P3; auto. assert (x < y)%r1. { split; auto. }
    apply (@OrderPM_Co1 R_str1 RA1 _ _ (-x)%r1) in H17; auto.
    rewrite Minus_P1 in H17; auto. }
  assert (f[(y - x)%r1] ∈ N2). { apply UniqueT2_Lemma1; auto. }
  pose proof H14. apply Z_Subset_R,(H3 y (-x)%r1) in H19 as [H19 _]; auto.
  rewrite UniqueT2_Lemma3 in H19; auto.
  rewrite H19 in H18. assert (0' < (f[y] - f[x]))%r2.
  { destruct (@one_is_min_in_N R_str2 RA2) as [_[]].
    apply (@Order_Co2 R_str2 RA2 _ 1'); auto. }
  apply (@OrderPM_Co1 R_str2 RA2 _ _ f[x]) in H20; auto.
  rewrite Plus_P4,Plus_P1,<-Plus_P3,(@Plus_P4 R_str2 RA2 (-f[x])%r2),
  Minus_P1,Plus_P1 in H20; auto. destruct H20; auto.
Qed.

Lemma UniqueT3_Lemma1 : ∀ f, Function f -> dom(f) = R1 -> ran(f) ⊂ R2
  -> (∀ x y, x ∈ R1 -> y ∈ R1 -> f[(x + y)%r1] = (f[x] + f[y])%r2
    /\ f[(x · y)%r1] = (f[x] · f[y])%r2)
  -> ran(f) <> [0']
  -> (∀ r, r ∈ (R1 ~ [0]) -> f[(r⁻)%r1] = ((f[r])⁻)%r2).
Proof.
  assert (H:True) by auto.
  intros. pose proof H5. apply Mult_inv1,MKT4' in H6 as [H6 _]; auto.
  assert (∀ m, m ∈ R1 -> f[m] ∈ R2).
  { intros. rewrite <-H1 in H7.
    apply Property_Value,Property_ran in H7; auto. }
  pose proof H5. apply MKT4' in H8 as []. apply AxiomII in H9 as [_].
  assert (f[r] ∈ (R2 ~ [0'])).
  { apply MKT4'; split; auto. apply AxiomII; split; eauto.
    intro. elim H9. apply MKT41. eauto.
    apply NNPP; intro. apply MKT41 in H10; eauto.
    apply NNPP in H10. apply H10,UniqueT2_Lemma4; auto. }
  assert (f[r] · f[(r⁻)%r1] = 1')%r2.
  { pose proof H8. apply (H3 _ (r⁻)%r1) in H11 as [_]; auto.
    apply UniqueT1 in H0 as []; auto.
    rewrite Divide_P1,H12 in H11; auto. }
  apply Mult_Co3 in H11; auto.
  apply Mult_inv1,MKT4' in H10 as []; auto.
  rewrite Mult_P4,Mult_P1 in H11; auto.
Qed.

Lemma UniqueT3_Lemma2 : ∀ f, Function f -> dom(f) = R1 -> ran(f) ⊂ R2
  -> (∀ x y, x ∈ R1 -> y ∈ R1 -> f[(x + y)%r1] = (f[x] + f[y])%r2
    /\ f[(x · y)%r1] = (f[x] · f[y])%r2)
  -> ran(f) <> [0']
  -> (∀ r, r ∈ Q1 -> (0 < r)%r1 -> (0' < f[r])%r2).
Proof.
  assert (H:True) by auto.
  intros. apply Existence_of_irRational_Number_Lemma6 in H6
  as [a[b[H6[]]]]; auto. assert (b ∈ (R1 ~ [0])).
  { apply MKT4'; split; auto. apply AxiomII;
    split; eauto. intro. apply MKT41 in H9; eauto.
    destruct (@one_is_min_in_N R_str1 RA1) as [_[_]]. pose proof H7.
    apply H10 in H11. rewrite H9 in H11.
    assert (0 < 0)%r1 as []; auto.
    { apply (@Order_Co2 R_str1 RA1 _ 1); auto. } }
  pose proof H9. apply Mult_inv1,MKT4' in H10 as [H10 _]; auto.
  apply (H3 a) in H10 as [_]; auto.
  rewrite UniqueT3_Lemma1 in H10; auto.
  assert (f[a] ∈ N2 /\ f[b] ∈ N2) as [].
  { split; apply UniqueT2_Lemma1; auto. }
  assert (0' < f[a] /\ 0' < f[b])%r2 as [].
  { destruct (@one_is_min_in_N R_str2 RA2) as [_[_]].
    split; apply (@Order_Co2 R_str2 RA2 _ 1'); auto. }
  assert (f[b] ∈ (R2 ~ [0'])).
  { apply MKT4'; split; auto. apply AxiomII;
    split; eauto. intro. apply MKT41 in H15; eauto.
    rewrite H15 in H14. destruct H14; auto. }
  apply (@Mult_inv1 R_str2 RA2),MKT4' in H15 as [H15 _].
  replace R with R2 in H15; auto.
  rewrite H8,H10. apply OrderPM_Co5; auto.
Qed.

Theorem UniqueT3 : ∀ f, Function f -> dom(f) = R1 -> ran(f) ⊂ R2
  -> (∀ x y, x ∈ R1 -> y ∈ R1 -> f[(x + y)%r1] = (f[x] + f[y])%r2
    /\ f[(x · y)%r1] = (f[x] · f[y])%r2)
  -> ran(f) <> [0']
  -> (∀ m n, m ∈ Z1 -> n ∈ (Z1 ~ [0]) -> f[(m/n)%r1] = (f[m]/f[n])%r2)
    /\ Function1_1 (f|(Q1)) /\ dom(f|(Q1)) = Q1 /\ ran(f|(Q1)) = Q2
    /\ (∀ x y, x ∈ Q1 -> y ∈ Q1 -> (x ≤ y)%r1 -> (f[x] ≤ f[y])%r2).
Proof.
  assert (H:True) by auto.
  intros. pose proof H0. apply UniqueT1 in H5 as []; auto.
  assert (∀ m, m ∈ R1 -> f[m] ∈ R2).
  { intros. rewrite <-H1 in H7.
    apply Property_Value,Property_ran in H7; auto. }
  assert (∀ m, m ∈ Z1 -> f[m] ∈ Z2). { apply UniqueT2; auto. }
  assert (∀ m, m ∈ (Z1 ~ [0]) -> f[m] ∈ (Z2 ~ [0'])) as H8'.
  { intros. apply MKT4' in H9 as []. apply MKT4'; split; auto.
    apply AxiomII; split; eauto. intro. apply AxiomII in H10 as [_].
    apply H10,MKT41; eauto. apply NNPP; intro.
    apply MKT41 in H11; eauto. apply NNPP in H11.
    apply H11,UniqueT2_Lemma4; auto. }
  assert (∀ m n, m ∈ Z1 -> n ∈ (Z1 ~ [0]) -> f[(m/n)%r1] = (f[m]/f[n])%r2).
  { intros. assert (m ∈ R1 /\ n ∈ (R1 ~ [0])) as [].
    { apply MKT4' in H10 as [].
      split; [ |apply MKT4'; split]; auto. }
    pose proof H11. apply (H3 _ (n⁻)%r1) in H13 as [_]; auto.
    rewrite UniqueT3_Lemma1 in H13; auto.
    apply Mult_inv1,MKT4' in H12 as []; auto. }
  assert (ReqR: (@R R_str1) = R1) by auto.
  assert (ReqR': (@R R_str2) = R2) by auto.
  assert (Function1_1 (f|(Q1))) as [].
  { split. apply MKT126a; auto. split; unfold Relation; intros.
    - apply AxiomII in H10 as [_[x[y[]]]]; eauto.
    - apply AxiomII' in H10 as [_],H11 as [_].
      apply MKT4' in H10 as [],H11 as [].
      apply AxiomII' in H12 as [_[H12 _]],H13 as [_[H13 _]].
      pose proof H10. apply Property_ran,H2 in H14.
      apply Property_Fun in H10,H11; auto.
      assert (f[y] + f[(-z)%r1] = 0')%r2.
      { pose proof H0. apply UniqueT2_Lemma2 in H15; auto.
        pose proof H13. apply Q_Subset_R in H16; auto.
        apply (H3 (-(1))%r1 z) in H16 as []; auto.
        rewrite (@PlusMult_Co3 R_str1 RA1). rewrite ReqR, ReqR' in *.
        rewrite H17, H15,H6,<-PlusMult_Co3,
        <-H10,<-H11,Minus_P1; auto. rewrite ReqR; auto. }
      pose proof H12. apply Q_Subset_R,(H3 y (-z)%r1) in H16 as [];
      auto. rewrite <-H16 in H15. apply NNPP; intro.
      assert (y - z <> 0)%r1.
      { intro. assert (y - z + z = 0 + z)%r1. { rewrite H19; auto. }
        rewrite <-Plus_P3,(Plus_P4 _ z),Minus_P1,(Plus_P4 0),
        Plus_P1,Plus_P1 in H20; auto. }
      assert (f[(y - z)%r1] <> 0'); auto.
      { apply UniqueT2_Lemma4; auto. } }
  assert (dom(f|(Q1)) = Q1).
  { rewrite MKT126b; auto. apply MKT30.
    rewrite H1; auto. }
  pose proof H0. apply UniqueT2 in H13 as [H13[[][H16[]]]]; auto.
  assert (ZeqZ : @Z R_str1 = Z1) by auto.
  assert (ZeqZ' : @Z R_str2 = Z2) by auto.
  assert (ran(f|(Q1)) = Q2).
  { apply AxiomI; split; intros. apply Einr in H19 as [x[]]; auto.
    rewrite MKT126c in H20; auto. rewrite H12 in H19. pose proof H19.
    apply AxiomII in H21 as [H21[m[n[H22[]]]]]. pose proof H20.
    rewrite H24,H9 in H20; auto. rewrite H20. apply AxiomII; split.
    rewrite <-H20,H25. eauto. exists f[m],f[n]; auto.
    pose proof H19. apply AxiomII in H20 as [_[m[n[H21[]]]]].
    pose proof H20; pose proof H21. apply MKT4' in H23 as [H23 _].
    rewrite ZeqZ' in *.
    rewrite <-H17, reqdi in H23,H24. apply Property_Value,Property_ran
    in H23,H24; auto. rewrite <-deqri in H23,H24.
    assert (((f|(Z1))⁻¹)[n] ∈ (Z1 ~ [0])).
    { apply MKT4'; split. rewrite H16 in H23; auto.
      apply AxiomII; split; eauto. intro. apply MKT41 in H25;
      eauto. apply MKT4' in H20 as [].
      rewrite <-H25,<-(MKT126c f Z1),f11vi in H5; auto.
      rewrite <-H5 in H26. apply AxiomII in H26 as [].
      apply H27,MKT41; eauto. rewrite H17; auto. }
    pose proof H24. rewrite H16 in H26.
    apply (H9 _ (((f|(Z1))⁻¹)[n])) in H26; auto.
    rewrite <-(MKT126c f Z1 H0 (((f|(Z1))⁻¹)[m])),
    <-(MKT126c f Z1 H0 (((f|(Z1))⁻¹)[n])),f11vi,f11vi in H26;
    try rewrite H17; auto; [ |apply MKT4' in H20; tauto].
    assert ((((f|(Z1))⁻¹)[m] / ((f|(Z1))⁻¹)[n])%r1 ∈ dom(f|(Q1))).
    { rewrite H12. rewrite H16 in H24. apply AxiomII; split; eauto.
      exists R1. apply Mult_close; auto.
      assert (((f|(Z1))⁻¹)[n] ∈ (R1 ~ [0])).
      { apply MKT4' in H25 as [].
        apply MKT4'; split; auto. }
      apply Mult_inv1,MKT4' in H27 as []; auto. }
    rewrite <-(MKT126c f Q1) in H26; auto.
    apply Property_Value,Property_ran in H27; auto.
    rewrite ReqR, ReqR' in *.
    rewrite H26,<-H22 in H27; auto. }
  split; [ |split; [split|repeat split]]; auto. intros.
  assert (∀ m, m ∈ R1 -> f[m] ∈ R2).
  { intros. rewrite <-H1 in H23.
    apply Property_Value,Property_ran in H23; auto. }
  destruct (classic (x = y)). rewrite H24.
  apply Leq_P1; auto. assert (x < y)%r1. split; auto.
  apply (@OrderPM_Co1 R_str1 RA1 _ _ (-x)%r1) in H25; auto.
  rewrite Minus_P1 in H25; auto.
  assert ((y - x)%r1 ∈ Q1).
  { apply Rat_P1a; auto. apply Rat_P3; auto. }
  assert (0' < (f[(y - x)%r1]))%r2. { apply UniqueT3_Lemma2; auto. }
  pose proof H21. apply Q_Subset_R in H28; auto.
  apply (H3 y (-x)%r1) in H28 as [H28 _]; auto.
  rewrite UniqueT2_Lemma3 in H28; auto.
  rewrite H28 in H27. apply Q_Subset_R,H23 in H20,H21; auto.
  apply (@OrderPM_Co1 R_str2 RA2 _ _ f[x]) in H27; auto.
  rewrite Plus_P4,Plus_P1,<-Plus_P3,(@Plus_P4 R_str2 RA2 _ f[x]),
  Minus_P1,Plus_P1 in H27; auto. destruct H27; auto.
Qed.

Lemma UniqueT4_Lemma1 : ∀ r, r ∈ R2 -> Sup1b \{ λ u, u ∈ Q2 /\ (u ≤ r)%r2 \} r.
Proof.
  intros. repeat split; intros; auto. unfold Included; intros.
  apply AxiomII in H0 as [_[]]; auto.
  apply AxiomII in H0; tauto. apply Arch_P9 in H1 as [q[H1[H2[]]]]; auto.
  exists q. split; auto. apply AxiomII; split; eauto.
Qed.

Lemma UniqueT4_Lemma2 : ∀ f, Function f -> dom(f) = R1 -> ran(f) ⊂ R2
  -> (∀ x y, x ∈ R1 -> y ∈ R1 -> f[(x + y)%r1] = (f[x] + f[y])%r2
    /\ f[(x · y)%r1] = (f[x] · f[y])%r2)
  -> ran(f) <> [0']
  -> (∀ x y, x ∈ R1 -> y ∈ R1 -> (x < y)%r1 <-> (f[x] < f[y])%r2).
Proof.
  assert (H:True) by auto. intros.
  assert (ReqR: (@R R_str1) = R1) by auto.
  assert (ReqR': (@R R_str2) = R2) by auto.
  assert (∀ r, r ∈ R1 -> (0 < r)%r1 -> (0' < f[r])%r2).
  { intros. apply Existence_of_irRational_Number_Lemma5 in H8
    as [e[H8[]]]; auto. pose proof H8. apply (H3 e e) in H11
    as []; auto. pose proof H8. rewrite ReqR, ReqR' in *.
    rewrite <-H1 in H13.
    apply Property_Value,Property_ran,H2 in H13; auto.
    rewrite <-H10,H12. apply OrderPM_Co5; auto.
    pose proof H13. apply (@Order_Co1 R_str2 RA2 0') in H14 as [H14|[]];
    auto.
    assert (∀ r, r ∈ R1 -> r <> 0 -> f[r] <> 0').
    { apply UniqueT2_Lemma4; auto. }
    destruct H9. apply H15 in H8; auto. elim H8; auto. }
  assert (∀ m, m ∈ R1 -> f[m] ∈ R2).
  { intros. rewrite <-H1 in H8.
    apply Property_Value,Property_ran in H8; auto. }
  assert (∀ a b, a ∈ R1 -> b ∈ R1 -> (a < b)%r1 -> (f[a] < f[b])%r2).
  { intros. apply (@OrderPM_Co1 R_str1 RA1 _ _ (-a)%r1) in H11; auto.
    rewrite Minus_P1 in H11; auto. apply H7 in H11; auto.
    pose proof H10. apply (H3 b (-a)%r1) in H12 as []; auto.
    rewrite H12,UniqueT2_Lemma3 in H11; auto.
    apply (@OrderPM_Co1 R_str2 RA2 _ _ f[a]) in H11; auto.
    rewrite Plus_P4,Plus_P1,<-Plus_P3,(@Plus_P4 R_str2 RA2 _ f[a]),
    Minus_P1,Plus_P1 in H11; auto. }
  split; auto. intros. pose proof H5.
  apply (@Order_Co1 R_str1 RA1 x y) in H11 as [H11|[]]; auto.
  apply H9 in H11; auto. destruct H10,H11. elim H13.
  apply Leq_P2; auto. rewrite H11 in H10.
  destruct H10. elim H12; auto.
Qed.

Lemma UniqueT4_Lemma3 : ∀ f, Function f -> dom(f) = R1 -> ran(f) ⊂ R2
  -> (∀ x y, x ∈ R1 -> y ∈ R1 -> f[(x + y)%r1] = (f[x] + f[y])%r2
    /\ f[(x · y)%r1] = (f[x] · f[y])%r2)
  -> ran(f) <> [0']
  -> (∀ A r, A ⊂ Q1 -> r ∈ R1 -> Sup1a A r -> Sup1b ran(f|(A)) f[r]).
Proof.
  assert (H:True) by auto. intros.
  assert (ReqR: (@R R_str1) = R1) by auto.
  assert (ReqR': (@R R_str2) = R2) by auto.
  assert (QeqQ: (@Q R_str1) = Q1) by auto.
  assert (QeqQ': (@Q R_str2) = Q2) by auto.
  destruct H7 as [[H7[_]]].
  assert (∀ m, m ∈ R1 -> f[m] ∈ R2).
  { intros. rewrite <-H1 in H10.
    apply Property_Value,Property_ran in H10; auto. }
  assert (∀ x y, x ∈ R1 -> y ∈ R1 -> (x ≤ y)%r1 -> (f[x] ≤ f[y])%r2).
  { intros. destruct (classic (x = y)). rewrite H14. apply Leq_P1; auto.
    assert (x < y)%r1. split; auto. apply UniqueT4_Lemma2; auto. }
  assert (Function (f|(A))). { apply MKT126a; auto. }
  repeat split; auto; unfold Included; intros.
  apply AxiomII in H13 as [H13[]]. apply MKT4' in H14 as [].
  apply Property_ran in H14; auto. apply AxiomII in H13 as [_[]].
  apply MKT4' in H13 as []. apply AxiomII' in H14 as [_[]].
  apply Property_Fun in H13; auto. rewrite H13.
  apply H11; auto. apply Arch_P9 in H14 as [q[H14[]]]; auto.
  assert (q ∈ ran(f)).
  { pose proof H0. apply UniqueT3 in H17 as [H17[[][H20[]]]]; auto.
    rewrite QeqQ, QeqQ' in *.
    rewrite <-H21 in H14. apply Einr in H14 as [x[]]; auto.
    rewrite MKT126c in H23; auto. rewrite H20 in H14.
    apply Q_Subset_R in H14; auto. rewrite ReqR, ReqR' in *.
    rewrite <-H1 in H14. apply Property_Value,Property_ran in H14; auto.
    rewrite H23; auto. }
  apply Einr in H17 as [x[]]; auto.
  assert (x < r)%r1.
  { rewrite H1 in H17. rewrite H18 in H16. pose proof H17.
    apply (@Order_Co1 R_str1 RA1 r) in H19 as [H19|[]]; auto.
    destruct H19. apply H11 in H19; auto. destruct H16. elim H21.
    apply Leq_P2; auto. rewrite H19 in H16. destruct H16. elim H20; auto. }
  rewrite H1 in H17. apply H9 in H19 as [x0[]]; auto.
  assert (x0 ∈ dom(f|(A))).
  { rewrite MKT126b; auto. apply MKT30 in H7. rewrite ReqR, ReqR' in *.
   rewrite H1,H7; auto. }
  exists f[x0]. split. rewrite <-(MKT126c f A); auto.
  apply (@ Property_ran x0),Property_Value; auto.
  apply (@Order_Co2 R_str2 RA2 _ q); auto. left. split; auto.
  rewrite H18. apply H11; auto. destruct H20; auto.
Qed.

Theorem UniqueT4 : ∀ f, Function f -> dom(f) = R1 -> ran(f) ⊂ R2
  -> (∀ x y, x ∈ R1 -> y ∈ R1 -> f[(x + y)%r1] = (f[x] + f[y])%r2
    /\ f[(x · y)%r1] = (f[x] · f[y])%r2)
  -> ran(f) <> [0']
  -> Function1_1 f /\ dom(f) = R1 /\ ran(f) = R2
    /\ (∀ x y, x ∈ R1 -> y ∈ R1 -> (x ≤ y)%r1 -> (f[x] ≤ f[y])%r2).
Proof.
  assert (H:True) by auto. intros.
  assert (ReqR: (@R R_str1) = R1) by auto.
  assert (ReqR': (@R R_str2) = R2) by auto.
  assert (QeqQ: (@Q R_str1) = Q1) by auto.
  assert (QeqQ': (@Q R_str2) = Q2) by auto.
  pose proof H0. apply UniqueT1 in H5 as []; auto.
  assert (∀ m, m ∈ R1 -> f[m] ∈ R2).
  { intros. rewrite <-H1 in H7.
    apply Property_Value,Property_ran in H7; auto. }
  assert (Function1_1 f) as [].
  { split; auto. split; unfold Relation; intros.
    - apply AxiomII in H8 as [_[x[y[]]]]; eauto.
    - apply AxiomII' in H8 as [_],H9 as [_].
      pose proof H8. apply Property_ran,H2 in H10.
      pose proof H8; pose proof H9.
      apply Property_dom in H11,H12. rewrite H1 in H11,H12.
      apply Property_Fun in H8,H9; auto.
      assert (f[y] + f[(-z)%r1] = 0')%r2.
      { rewrite UniqueT2_Lemma3,<-H8,<-H9,Minus_P1; auto. }
      pose proof H11. apply (H3 y (-z)%r1) in H14 as [];
      auto. rewrite H13 in H14. apply NNPP; intro.
      assert (y - z <> 0)%r1.
      { intro. assert (y - z + z = 0 + z)%r1. { rewrite H17; auto. }
        rewrite <-Plus_P3,(Plus_P4 _ z),Minus_P1,(Plus_P4 0),
        Plus_P1,Plus_P1 in H18; auto. }
      assert (f[(y - z)%r1] <> 0'); auto.
      { apply UniqueT2_Lemma4; auto. } }
  assert (ran(f) = R2).
  { apply AxiomI; split; auto. intros.
    set (A := \{ λ u, u ∈ Q2 /\ (u ≤ z)%r2 \}).
    pose proof H10. apply UniqueT4_Lemma1 in H11.
    set (B := \{ λ u, u ∈ Q1 /\ f[u] ∈ A \}). pose proof H0.
    assert (Hb : B ⊂ R1).
    { unfold Included; intros.
      apply AxiomII in H13 as [_[]]; auto. }
    apply UniqueT3 in H12 as [_[[][H14[H15 _]]]]; auto.
    assert (Function1_1 (f|(B)) /\ dom(f|(B)) = B
      /\ ran(f|(B)) = A) as [[][]].
    { assert (Function (f|(B))). { apply MKT126a; auto. }
      assert (∀ g g1, Function g -> g1 ⊂ g -> Function g1).
      { intros. destruct H17. split; unfold Relation; intros.
        apply H18,H17 in H20; auto. apply (H19 x); auto. }
      assert (Function1_1 (f|(B))).
      { split; auto. apply (H17 (f|(Q1))⁻¹); auto.
        unfold Included; intros. apply AxiomII in H18
        as [H18[x[y[]]]]. apply MKT4' in H20 as [].
        apply AxiomII; split; auto. exists x,y. split; auto.
        apply MKT4'; split; auto. apply AxiomII' in H21 as [H21[]].
        apply AxiomII'; repeat split; auto.
        apply AxiomII in H22; tauto. }
      split; auto. destruct H18. assert (dom(f|(B)) = B).
      { apply MKT30 in Hb. rewrite MKT126b,H1; auto. }
      split; auto. apply AxiomI; split; intros.
      apply Einr in H21 as [x[]]; auto. rewrite MKT126c in H22; auto.
      rewrite H20 in H21. apply AxiomII in H21 as [_[]].
      rewrite H22; auto. apply AxiomII; split; eauto. pose proof H21.
      apply AxiomII in H22 as [_[]]. rewrite <-H15 in H22.
      apply Einr in H22 as [x[]]; auto. rewrite MKT126c in H24; auto.
      exists x. assert (x ∈ dom(f|(B))).
      { rewrite H20. apply AxiomII; repeat split;
        [ |rewrite <-H14|rewrite <-H24]; eauto. }
      rewrite <-(MKT126c f B) in H24; auto. rewrite H24.
      apply Property_Value; auto. }
    assert (B <> Φ /\ ∃ c, (@Upper R_str1 B c)) as [].
    { pose proof (@OrderPM_Co9 R_str2 RA2).
      apply (@OrderPM_Co1 R_str2 RA2 _ _ (-1')%r2) in H20; auto.
      rewrite Minus_P1,Plus_P4,Plus_P1 in H20; auto.
      apply (@OrderPM_Co1 R_str2 RA2 _ _ z) in H20; auto.
      rewrite (@Plus_P4 R_str2 RA2 0'),Plus_P1 in H20; auto.
      apply Arch_P9 in H20 as [q[H20[_]]]; auto.
      pose proof H10. apply Arch_P10 in H22 as [n[[H22[_]]_]]; auto.
      apply (@Int_P1a R_str2 RA2 n 1'),Z_Subset_Q in H22; auto.
      split. assert (q ∈ A).
      { apply AxiomII; split; eauto. destruct H21; auto. }
      rewrite <-H19 in H24. rewrite reqdi in H24.
      apply Property_Value,Property_ran in H24; auto.
      rewrite <-deqri,H18 in H24. apply NEexE; eauto.
      rewrite QeqQ, QeqQ' in *.
      rewrite <-H15 in H22. apply Einr in H22 as [x[]]; auto.
      exists x. repeat split; auto. rewrite H14 in H22;
      auto. intros. pose proof H25. rewrite <-H18 in H26.
      apply Property_Value,Property_ran in H26; auto.
      rewrite H19 in H26. apply AxiomII in H26 as [_[]].
      rewrite MKT126c in H24,H27; auto; [ |rewrite H18; auto].
      assert (f[x0] < f[x])%r2.
      { rewrite H14 in H22. rewrite H24 in H23.
        apply (@Order_Co2 R_str2 RA2 _ z); auto. }
      apply UniqueT4_Lemma2 in H28; auto. destruct H28; auto.
      rewrite H14 in H22. auto. }
    apply SupT in H21 as [y[]]; auto.
    assert (@Sup1b ran(f|(B)) f[y]).
    { apply UniqueT4_Lemma3; auto. unfold Included; intros.
      apply AxiomII in H23; tauto. destruct H21 as [[_[]]]; auto. }
    apply Sup1_equ_Sup2 in H11,H23; auto. rewrite H19 in H23.
    assert (z = f[y]).
    { apply (Min_Unique R_str2 RA2 (\{ λ u, (Upper R_str2 A u) \})); auto. }
    rewrite H24. apply (@ Property_ran y),Property_Value; auto.
    rewrite H1. destruct H21 as [[_[]]]; auto. }
  split; [split|split; [ |split]]; auto. intros.
  destruct (classic (x = y)). rewrite H14. apply Leq_P1; auto.
  apply UniqueT4_Lemma2; auto.
Qed.

Lemma UniqueT5_Lemma1 : ∃ f, Function1_1 f /\ dom(f) = N1 /\ ran(f) = N2
  /\ (∀ m n, m ∈ N1 -> n ∈ N1 -> (m < n)%r1 <-> (f[m] < f[n])%r2).
Proof.
  assert (NeqN: (@N R_str1) = N1) by auto.
 assert (NeqN': (@N R_str2) = N2) by auto.
  set (L1 := \{\ λ u v, u ∈ N1 /\ v ∈ N1 /\ (u < v)%r1 \}\).
  assert (WellOrdered L1 N1).
  { split; unfold Connect; intros. pose proof H.
    apply N_Subset_R in H1; auto. apply (@Order_Co1 R_str1 RA1 v) in H1
    as [H1|[]]; auto. right; left.
    apply AxiomII'; split; auto. apply MKT49a; eauto.
    left. apply AxiomII'; split; auto. apply MKT49a; eauto.
    apply Nat_P7 in H as [n[H[]]]; auto. exists n. split; auto.
    intros. intro. apply AxiomII' in H4 as [_[H4[H5[]]]].
    apply H2 in H3. apply H7,(@Leq_P2 R_str1 RA1); auto. }
  set (L2 := \{\ λ u v, u ∈ N2 /\ v ∈ N2 /\ (u < v)%r2 \}\).
  assert (WellOrdered L2 N2).
  { split; unfold Connect; intros. pose proof H0.
    apply N_Subset_R in H2; auto. apply (@Order_Co1 R_str2 RA2 v) in H2
    as [H2|[]]; auto. right; left.
    apply AxiomII'; split; auto. apply MKT49a; eauto.
    left. apply AxiomII'; split; auto. apply MKT49a; eauto.
    apply Nat_P7 in H0 as [n[H0[]]]; auto. exists n. split; auto.
    intros. intro. apply AxiomII' in H5 as [_[H5[H6[]]]].
    apply H3 in H4. apply H8,(@Leq_P2 R_str2 RA2); auto. }
  apply (@ MKT99 L1 L2 N1 N2) in H0 as [f[H0[[_[_[H1[]]]]]]]; auto.
  pose proof H1. apply MKT96 in H5 as [[_]].
  destruct H2 as [H2[_]], H3 as [H3[_]].
  assert (dom(f) = N1 /\ ran(f) = N2) as [].
  { destruct H4; split; auto; apply AxiomI; split; intros; auto;
    apply NNPP; intro.
    - assert ((N2 ~ ran(f)) <> Φ /\ (N2 ~ ran(f)) ⊂ N2) as [].
      { split. apply NEexE. exists z. apply MKT4'; split; auto.
        apply AxiomII; split; eauto. unfold Included; intros.
        apply MKT4' in H11; tauto. }
      apply Nat_P7 in H12 as [n[H12[]]]; auto.
      assert (∃ x, (@Upper R_str2 ran(f) x)).
      { exists n. repeat split; auto; intros. unfold Included;
        auto. apply MKT4' in H13 as []. pose proof H13.
        apply N_Subset_R,(@Order_Co1 R_str2 RA2 x) in H17 as [H17|[]]; auto;
        auto. destruct H17; auto. apply (H8 n) in H15;
        auto. apply AxiomII in H16 as []. elim H18; auto.
        apply AxiomII'; split; auto. apply MKT49a; eauto.
        rewrite H17. apply Leq_P1; auto. }
      apply Arch_P3a in H15 as [m[H15[]]]; unfold Included;
      auto. elim (@Arch_P2 R_str1 RA1). rewrite NeqN, NeqN' in *.
      rewrite <-H4. exists (f⁻¹[m]). pose proof H16. rewrite reqdi in H18.
      apply Property_Value,Property_ran in H18; auto.
      rewrite <-deqri in H18. repeat split; unfold Included;
      auto. intros. pose proof H19.
      apply Property_Value,Property_ran in H20; auto.
      pose proof H20. apply H17 in H20.
      destruct (classic (f[x] = m)). rewrite <-H22,f11iv; auto.
      apply Leq_P1; auto. assert (Rrelation f[x] L2 m).
      { apply AxiomII'; repeat split; auto. apply MKT49a; eauto. }
      destruct H6 as [_[_[_]]]. apply H6 in H23; try rewrite
      <-reqdi; auto. apply AxiomII' in H23 as [_[H23[]]].
      rewrite f11iv in H25; auto. destruct H25; auto. apply NEexE.
      exists f[1]. apply (@ Property_ran 1),Property_Value; auto.
      rewrite H4; auto.
    - assert ((N1 ~ dom(f)) <> Φ /\ (N1 ~ dom(f)) ⊂ N1) as [].
      { split. apply NEexE. exists z. apply MKT4'; split; auto.
        apply AxiomII; split; eauto. unfold Included; intros.
        apply MKT4' in H11; tauto. }
      apply Nat_P7 in H12 as [n[H12[]]]; auto.
      assert (∃ x, (@Upper R_str1 dom(f) x)).
      { exists n. repeat split; auto; intros. unfold Included;
        auto. apply MKT4' in H13 as []. pose proof H13.
        apply N_Subset_R,(@Order_Co1 R_str1 RA1 x) in H17 as [H17|[]]; auto;
        auto. destruct H17; auto. apply (H7 n) in H15;
        auto. apply AxiomII in H16 as []. elim H18; auto.
        apply AxiomII'; split; auto. apply MKT49a; eauto.
        rewrite H17. apply Leq_P1; auto. }
      apply Arch_P3a in H15 as [m[H15[]]]; unfold Included;
      auto. elim (@Arch_P2 R_str2 RA2). rewrite NeqN' in *.
      rewrite <-H4. exists (f[m]). pose proof H16.
      apply Property_Value,Property_ran in H18; auto.
      repeat split; unfold Included; auto. intros.
      pose proof H19. rewrite reqdi in H20.
      apply Property_Value,Property_ran in H20; auto.
      pose proof H20. rewrite <-deqri in H21. apply H17 in H21.
      destruct (classic (f⁻¹[x] = m)). rewrite <-H22,f11vi; auto.
      apply Leq_P1; auto. assert (Rrelation f⁻¹[x] L1 m).
      { apply AxiomII'; repeat split; auto. apply MKT49a; eauto.
        rewrite <-deqri in H20; auto. }
      destruct H1 as [_[_[_]]]. apply H1 in H23; auto;
      try rewrite deqri; auto. apply AxiomII' in H23 as [_[H23[]]].
      rewrite f11vi in H25; auto. destruct H25; auto. apply NEexE.
      exists f⁻¹[1']. rewrite deqri.
      apply (@ Property_ran 1'),Property_Value; auto.
      rewrite <-reqdi,H4; auto. }
  exists f. split; [split|split; [ |split]]; auto.
  assert (∀ m n, m ∈ N1 -> n ∈ N1 -> (m < n)%r1 -> (f[m] < f[n])%r2).
  { intros. destruct H1 as [_[_[_]]]. rewrite H9 in H1.
    assert (Rrelation m L1 n).
    { apply AxiomII'; split; try apply MKT49a; eauto. }
    apply H1 in H14; auto. apply AxiomII' in H14; tauto. }
  split; auto; intros. pose proof H12. apply N_Subset_R in H15; auto.
  apply (@Order_Co1 R_str1 RA1 n) in H15 as [H15|[]]; auto.
  apply H11 in H15; auto. destruct H14,H15. elim H17.
  apply Leq_P2; auto; apply N_Subset_R; auto; rewrite NeqN,NeqN' in *;
  rewrite <-H10; [apply (@ Property_ran n)|apply (@ Property_ran m)];
  apply Property_Value; auto; rewrite H9; auto.
  rewrite H15 in H14. destruct H14; contradiction.
Qed.

Lemma UniqueT5_Lemma2 : ∀ f, Function1_1 f -> dom(f) = N1 -> ran(f) = N2
  -> (∀ m n, m ∈ N1 -> n ∈ N1 -> (m < n)%r1 <-> (f[m] < f[n])%r2)
  -> (∀ m n, m ∈ N1 -> n ∈ N1
       -> f[(m + n)%r1] = (f[m] + f[n])%r2 /\ f[(m · n)%r1] = (f[m] · f[n])%r2
         /\ ((m < n)%r1 -> f[(n - m)%r1] = (f[n] - f[m])%r2))
     /\ f[1] = 1'.
Proof.
  intros f [] H1 H2 H3.
  assert (ReqR: (@R R_str1) = R1) by auto.
  assert (ReqR': (@R R_str2) = R2) by auto.
  assert (NeqN: (@N R_str1) = N1) by auto.
  assert (NeqN': (@N R_str2) = N2) by auto.
  assert ((∀ m, m ∈ N1 -> f[m] ∈ N2)
    /\ (∀ m, m ∈ N1 -> f[m] ∈ R2)) as [].
  { split; intros; rewrite <-H1 in H4;
    apply Property_Value,Property_ran in H4; auto.
    rewrite <-H2; auto. rewrite H2 in H4; auto. }
  assert (f[1] = 1').
  { pose proof one_in_R_Co. rewrite ReqR' in *;
    apply (@Order_Co1 R_str2 RA2 f[1]) in H6 as [H6|[]]; auto.
    destruct (@one_is_min_in_N R_str2 RA2) as [_[]].
    pose proof (@one_in_N R_str1 RA1). apply H4,H8 in H9.
    destruct H6. apply Leq_P2; auto.
    pose proof (@one_in_N R_str2 RA2). rewrite NeqN' in *;
    rewrite <-H2 in H7. apply Einr in H7 as [x[]]; auto.
    rewrite H1 in H7. rewrite H8 in H6. apply H3 in H6;
    auto. destruct (@one_is_min_in_N R_str1 RA1) as [_[]].
    pose proof H7. apply H10 in H7. destruct H6. elim H12.
    apply (@Leq_P2 R_str1 RA1); auto. }
  assert (∀ m, m ∈ N1 -> f[(m + 1)%r1] = (f[m] + f[1])%r2).
  { intros. assert (f[m] < f[(m + 1)%r1])%r2.
    { apply H3; auto. pose proof (@OrderPM_Co9 R_str1 RA1).
      apply (@OrderPM_Co1 R_str1 RA1 _ _ m) in H8; auto.
      rewrite Plus_P4,Plus_P1,Plus_P4 in H8; auto. }
    assert (f[(m + 1)%r1] ∈ R2). auto.
    apply (@Order_Co1 R_str2 RA2 (f[m] + f[1])%r2) in H9 as [H9|[]];
    auto. rewrite H6 in H9.
    assert ((f[m] + 1')%r2 ∈ N2). auto.
    rewrite <-H2 in H10. apply Einr in H10 as [x[]]; auto.
    pose proof (@ OrderPM_Co9 R_str2 RA2).
    apply (@OrderPM_Co1 R_str2 RA2 _ _ (f[m])) in H12; auto.
    rewrite Plus_P4,Plus_P1,Plus_P4 in H12; auto. rewrite H11 in H12.
    rewrite H1 in H10. apply H3 in H12; auto. apply Nat_P4 in H12; auto.
    destruct (classic ((m + 1)%r1 = x)). rewrite H13,H6; auto.
    assert (m + 1 < x)%r1. split; auto. apply H3 in H14;
    auto. rewrite H11 in H9.
    assert (f[x] < f[x])%r2 as []; try contradiction.
    { destruct H14. apply (@Order_Co2 R_str2 RA2 _ (f[(m + 1)%r1])); auto. }
    apply Nat_P4 in H9; auto. rewrite H6 in H9.
    apply (@OrderPM_Co1 R_str2 RA2 _ _ 1') in H8 as []; auto.
    elim H10. apply Leq_P2; auto. }
  assert (∀ m, m ∈ N1 -> (1 < m)%r1 -> f[(m - 1)%r1] = (f[m] - f[1])%r2).
  { intros. assert (f[(m - 1)%r1] < f[m])%r2.
    { apply H3; auto. apply Nat_P2; destruct H9; auto.
      pose proof (@OrderPM_Co9 R_str1 RA1).
      apply (@OrderPM_Co1 R_str1 RA1 _ _ (-(1))%r1) in H10; auto.
      rewrite Minus_P1,Plus_P4,Plus_P1 in H10; auto.
      apply (@OrderPM_Co1 R_str1 RA1 _ _ m) in H10; auto.
      rewrite (@Plus_P4 R_str1 RA1 0),Plus_P1,Plus_P4 in H10; auto. }
    assert (f[(m - 1)%r1] ∈ N2). { apply H4,Nat_P2; destruct H9; auto. }
    assert ((f[m] - 1')%r2 ∈ N2).
    { apply Nat_P2; auto. apply H3 in H9 as []; auto.
      rewrite H6 in H12; auto. }
    pose proof H11. apply N_Subset_R,(@Order_Co1 R_str2 RA2 (f[m] - f[1])%r2)
    in H13 as [H13|[]]; auto. rewrite H6 in H13.
    apply Nat_P4 in H13; auto. rewrite <-Plus_P3,(@Plus_P4 R_str2 RA2 (-1')%r2),
    Minus_P1,Plus_P1 in H13; auto. destruct H10.
    elim H14. apply Leq_P2; auto. rewrite H6 in H13.
    rewrite <-H2 in H12. apply Einr in H12 as [x[]]; auto.
    rewrite H14 in H13. assert ((m - 1)%r1 ∈ N1).
    { apply Nat_P2; destruct H9; auto. }
    rewrite H1 in H12. apply H3 in H13; auto.
    assert (x < m)%r1.
    { apply H3; auto. replace f[m] with (0' + f[m])%r2.
      rewrite <-H14,Plus_P4; auto. apply OrderPM_Co1; auto.
      apply OrderPM_Co2a; auto. rewrite Plus_P4,Plus_P1; auto. }
    destruct H9. apply Nat_P6 in H8; auto. elim H8; eauto. }
  set (E := \{ λ u, u ∈ N1 /\ (∀ m, m ∈ N1 -> f[(m + u)%r1]
    = (f[m] + f[u])%r2 /\ ((u < m)%r1 -> f[(m - u)%r1] = (f[m] - f[u])%r2)) \}).
  assert (E ⊂ N1 /\ 1 ∈ E) as [].
  { split. unfold Included; intros. apply AxiomII in H9; tauto.
    apply AxiomII; repeat split; eauto. }
  assert (E = N1).
  { apply MathInd; auto. intros. apply AxiomII in H11 as [_[]].
    apply AxiomII; repeat split; eauto.
    - assert (m + 1 ∈ N1)%r1. auto. apply H12 in H14
      as [H14 _]. rewrite H7,(@Plus_P4 R_str1 RA1 x),Plus_P3,H14,H7,
      (@Plus_P4 R_str2 RA2 f[x]),Plus_P3; auto.
    - intros. rewrite (@PlusMult_Co3 R_str1 RA1),Mult_P4,Mult_P5,Mult_P4,
      <-PlusMult_Co3,Mult_P4,Mult_P1,(@Plus_P4 R_str1 RA1 (-x)%r1),Plus_P3;
      auto. assert (1 < m)%r1.
      { apply (@Order_Co2 R_str1 RA1 _ (x + 1)%r1); auto. left.
        split; [ |destruct H14; auto]. assert (0 < x)%r1.
        { apply (@Order_Co2 R_str1 RA1 _ 1); auto. left.
          split; auto. destruct (@one_is_min_in_N R_str1 RA1)
          as [_[]]; auto. }
        apply (@OrderPM_Co1 R_str1 RA1 _ _ 1) in H15; auto.
        rewrite Plus_P4,Plus_P1 in H15; auto. }
      apply (@OrderPM_Co1 R_str1 RA1 _ _ (-(1))%r1) in H14; auto.
      rewrite <-Plus_P3,Minus_P1,Plus_P1 in H14; auto.
      apply H12 in H14; [ |apply Nat_P2; destruct H15]; auto.
      rewrite ReqR, ReqR' in *. rewrite H14,H8,H7; auto.
      replace (-(f[x] + f[1]))%r2 with ((-1') · (f[x] + f[1]))%r2.
      rewrite Mult_P4,Mult_P5,Mult_P4,<-PlusMult_Co3,Mult_P4,H6,Mult_P1,
      (@Plus_P4 R_str2 RA2 (-f[x])%r2),Plus_P3; auto.
      rewrite <-PlusMult_Co3; auto. }
  assert (∀ m n, m ∈ N1 -> n ∈ N1 -> f[(m + n)%r1] = (f[m] + f[n])%r2
    /\ ((m < n)%r1 -> f[(n - m)%r1] = (f[n] - f[m])%r2)).
  { intros. pose proof H12; pose proof H13.
    rewrite <-H11 in H12. apply AxiomII in H12 as [_[]].
    apply H16 in H13 as []. split; auto.
    rewrite (@Plus_P4 R_str1 RA1),(@Plus_P4 R_str2 RA2); auto. }
  set (F := \{ λ u, u ∈ N1 /\ (∀ m, m ∈ N1 -> f[(m · u)%r1]
    = (f[m] · f[u])%r2) \}).
  assert (F ⊂ N1 /\ 1 ∈ F) as [].
  { split. unfold Included; intros. apply AxiomII in H13; tauto.
    apply AxiomII; repeat split; eauto. intros.
    rewrite Mult_P1,H6,Mult_P1; auto. }
  assert (F = N1).
  { apply MathInd; auto. intros. apply AxiomII in H15 as [_[]].
    apply AxiomII; repeat split; eauto. intros.
    rewrite Mult_P4,Mult_P5,(Mult_P4 1),Mult_P1,H7,(@Mult_P4 R_str2 RA2),
    Mult_P5,(@Mult_P4 R_str2 RA2),<-H16,H6,(@Mult_P4 R_str2 RA2),
    (@Mult_P1 R_str2 RA2),Mult_P4; auto. apply H12; auto. }
  split; auto. intros; repeat split; try apply H12; auto.
  rewrite <-H15 in H17. apply AxiomII in H17 as [_[]]; auto.
Qed.

Lemma UniqueT5_Lemma3 : ∃ f, Function f /\ dom(f) = Z1 /\ ran(f) ⊂ Z2
  /\ f[0] = 0' /\ f[1] = 1'
  /\ (∀ m n, m ∈ Z1 -> n ∈ Z1
     -> f[(m + n)%r1] = (f[m] + f[n])%r2 /\ f[(m · n)%r1] = (f[m] · f[n])%r2)
  /\ (∀ m, m ∈ Z1 -> m <> 0 -> f[m] <> 0')
  /\ (∀ m, m ∈ Z1 -> (0 < m)%r1 -> (0' < f[m])%r2).
Proof.
  assert (NeqN: (@N R_str1) = N1) by auto.
  assert (NeqN': (@N R_str2) = N2) by auto.
  assert (ZeqZ: (@Z R_str1) = Z1) by auto.
  assert (ZeqZ': (@Z R_str2) = Z2) by auto.
  assert (ReqR: (@R R_str1) = R1) by auto.
  assert (ReqR': (@R R_str2) = R2) by auto.
  destruct UniqueT5_Lemma1 as [f[[][H1[]]]]. pose proof H3 as H3a.
  apply UniqueT5_Lemma2 in H3 as []; try split; auto.
  set (g := \{\ λ u v, (u ∈ N1 /\ v = f[u])
    \/ (u ∈ \{ λ a, (-a)%r1 ∈ N1 \} /\ v = (-f[(-u)%r1])%r2)
    \/ (u = 0 /\ v = 0') \}\).
  assert (∀ m, ~ (m ∈ N1 /\ ((-m)%r1) ∈ N1)).
  { intros; intro. destruct H5.
    assert (0 < m /\ 0 < -m)%r1 as [].
    { destruct (@one_is_min_in_N R_str1 RA1) as [_[]].
      split; apply (@Order_Co2 R_str1 RA1 _ 1); auto. }
    apply OrderPM_Co2a in H7; auto.
    destruct H7,H8. apply H10,(@Leq_P2 R_str1 RA1); auto. }
  assert (Function g).
  { split; unfold Relation; intros.
    apply AxiomII in H6 as [_[x[y[]]]]; eauto.
    apply AxiomII' in H6 as [_[[]|[[]|[]]]],
    H7 as [_[[]|[[]|[]]]]; try rewrite H8,H9; auto.
    apply AxiomII in H7 as []. elim (H5 x); auto.
    elim (@zero_not_in_N R_str1 RA1). rewrite <-H7; auto.
    apply AxiomII in H6 as []. elim (H5 x); auto.
    apply AxiomII in H6 as []. rewrite H7,(@PlusMult_Co3 R_str1 RA1),
    PlusMult_Co1 in H10; auto.
    elim (@zero_not_in_N R_str1 RA1); auto. rewrite H6 in H7.
    elim (@zero_not_in_N R_str1 RA1); auto. apply AxiomII in H7 as [].
    rewrite H6,(@PlusMult_Co3 R_str1 RA1),PlusMult_Co1 in H10; auto.
    elim (@zero_not_in_N R_str1 RA1); auto. }
  assert (dom(g) = Z1).
  { apply AxiomI; split; intros.
    apply Property_Value,AxiomII' in H7 as [_[[]|[[]|[]]]];
    auto. apply MKT4; right. apply MKT4; auto.
    rewrite H7. repeat (apply MKT4; right).
    apply MKT41; eauto. apply AxiomII; split; eauto.
    apply MKT4 in H7 as []. exists f[z].
    apply AxiomII'; split; auto. apply MKT49a; eauto.
    rewrite NeqN in *; rewrite <-H1 in H7.
    apply Property_Value,Property_ran in H7; eauto.
    apply MKT4 in H7 as []. pose proof H7.
    apply AxiomII in H7 as []. exists (-f[(-z)%r1])%r2.
    apply AxiomII'; split; auto. apply MKT49a; auto. rewrite NeqN in *; 
    rewrite <-H1 in H9. apply Property_Value,Property_ran in H9;
    auto. rewrite H2 in H9. eauto. exists 0'.
    apply MKT41 in H7; eauto. rewrite H7.
    apply AxiomII'; split; auto. apply MKT49a; eauto. }
  assert (ran(g) ⊂ Z2).
  { unfold Included; intros. apply AxiomII in H8 as [_[]].
    apply AxiomII' in H8 as [_[[]|[[]|[]]]]. rewrite H9.
    apply N_Subset_Z; auto. rewrite NeqN' in *; rewrite <-H2.
    rewrite <-H1 in H8. apply Property_Value,Property_ran in H8; auto.
    apply MKT4; right. apply MKT4; left. apply AxiomII.
    apply AxiomII in H8 as []. rewrite <-H1 in H10.
    apply Property_Value,Property_ran in H10; auto.
    rewrite H2 in H10. rewrite PlusMult_Co3,H9,PlusMult_Co4;
    try rewrite H9; auto. split; eauto.
    rewrite H9. repeat (apply MKT4; right).
    apply MKT41; eauto. }
  assert (g[0] = 0').
  { assert (0 ∈ Z1).
    { repeat (apply MKT4; right). apply MKT41; eauto. }
    rewrite <-H7 in H9. apply Property_Value,AxiomII' in H9
    as [_[[]|[[]|[]]]]; auto. elim (@zero_not_in_N R_str1 RA1); auto.
    apply AxiomII in H9 as []. rewrite (@PlusMult_Co3 R_str1 RA1),PlusMult_Co1
    in H11; auto. elim (@zero_not_in_N R_str1 RA1); auto. }
  assert (g[1] = 1').
  { pose proof (@one_in_N R_str1 RA1). apply N_Subset_Z in H10.
    rewrite ZeqZ in *; rewrite <-H7 in H10.
    apply Property_Value,AxiomII' in H10 as [_[[]|[[]|[]]]]; auto.
    rewrite <-H4; auto. apply AxiomII in H10 as []. elim (H5 1); auto.
    pose proof (@OrderPM_Co9 R_str1 RA1). destruct H12. elim H13; auto. }
  exists g. split; [ |split; [ |split; [ |split; [ |split]]]]; auto.
  assert (∀ m, m ∈ N1 -> g[m] = f[m]).
  { intros. pose proof H11. apply N_Subset_Z in H11. rewrite ZeqZ in *;
    rewrite <-H7 in H11. apply Property_Value,AxiomII' in H11
    as [_[[]|[[]|[]]]]; auto. apply AxiomII in H11 as [].
    elim (H5 m); auto. rewrite H11 in H12.
    elim (zero_not_in_N R_str1 RA1); auto. }
  assert (∀ m, m ∈ \{ λ a, (-a)%r1 ∈ N1 \} -> g[m] = (-f[(-m)%r1])%r2).
  { intros. assert (m ∈ Z1).
    { apply MKT4; right; apply MKT4; auto. }
    rewrite <-H7 in H13. apply Property_Value,AxiomII' in H13
    as [_[[]|[[]|[]]]]; auto. apply AxiomII in H12 as [].
    elim (H5 m); auto. apply AxiomII in H12 as [].
    rewrite H13,(@PlusMult_Co3 R_str1 RA1),PlusMult_Co1 in H15; auto.
    elim (@zero_not_in_N R_str1 RA1); auto. }
  assert (∀ m, m ∈ N1 -> f[m] ∈ N2).
  { intros. rewrite <-H1 in H13. rewrite <-H2.
    apply Property_Value,Property_ran in H13; auto. }
  assert (∀ m n, m ∈ N1 -> n ∈ \{ λ a, (-a)%r1 ∈ N1 \}
    -> g[(m + n)%r1] = (g[m] + g[n])%r2 /\ g[(m · n)%r1] = (g[m] · g[n])%r2).
  { intros. assert (n ∈ Z1).
    { apply MKT4; right; apply MKT4; auto. }
    assert ((m · n)%r1 ∈ \{ λ a, (-a)%r1 ∈ N1 \}) as Ha.
    { apply AxiomII; split; eauto.
      apply AxiomII in H15 as [].
      rewrite (@PlusMult_Co3 R_str1 RA1),Mult_P3,(Mult_P4 _ m),<-Mult_P3,
      <-PlusMult_Co3; auto. }
    assert ((m + n)%r1 ∈ Z1). auto.
    apply MKT4 in H17 as []. assert (0 < (m + n))%r1.
    { apply (@Order_Co2 R_str1 RA1 _ 1); auto. left.
      destruct (@one_is_min_in_N R_str1 RA1) as [_[_]]; auto. }
    apply (@OrderPM_Co1 R_str1 RA1 _ _ (-n)%r1) in H18; auto.
    rewrite Plus_P4,Plus_P1,<-Plus_P3,Minus_P1,Plus_P1 in H18;
    auto. pose proof H15. apply AxiomII in H19 as [_].
    apply H3 in H18; auto. rewrite (@PlusMult_Co3 R_str1 RA1),PlusMult_Co4 in H18;
    auto. rewrite H11,H11,H12,H18; auto. split; auto.
    rewrite (@PlusMult_Co3 R_str2 RA2),Mult_P3,(Mult_P4 f[m]),<-Mult_P3,
    <-PlusMult_Co3; auto.
    pose proof H19. apply (H3 m) in H20 as [_[H20 _]]; auto.
    rewrite ReqR, ReqR' in *.
    rewrite <-H20,(@PlusMult_Co3 R_str1 RA1),Mult_P3,(Mult_P4 m (-(1))%r1),
    <-Mult_P3,<-PlusMult_Co3,H12; auto.
    apply MKT4 in H17 as []. pose proof H17.
    apply AxiomII in H18 as [_]. assert (0 < (-(m + n)))%r1.
    { destruct (@one_is_min_in_N R_str1 RA1) as [_[_]].
      apply (@Order_Co2 R_str1 RA1 _ 1); auto. }
    rewrite (@PlusMult_Co3 R_str1 RA1),Plus_P4,Mult_P4,Mult_P5,Mult_P4,
    <-PlusMult_Co3,Mult_P4,<-PlusMult_Co3 in H19; auto.
    apply (@OrderPM_Co1 R_str1 RA1 _ _ m) in H19; auto.
    rewrite Plus_P4,Plus_P1,<-Plus_P3,(Plus_P4 _ m),Minus_P1,
    Plus_P1 in H19; auto. pose proof H15.
    apply AxiomII in H20 as [_]. apply H3 in H19; auto.
    rewrite H12,H11,H12; auto. split. rewrite ReqR, ReqR' in *.
    rewrite (@PlusMult_Co3 R_str1 RA1),Mult_P4,Mult_P5,Mult_P4,
    <-(@PlusMult_Co3 R_str1 RA1),Mult_P4,<-PlusMult_Co3,Plus_P4; auto.
    replace R with R1; auto. rewrite H19,(@PlusMult_Co3 R_str2 RA2),Mult_P4; auto.
    replace R with R2; auto. rewrite Mult_P5,Mult_P4,<-(@PlusMult_Co3 R_str2 RA2),
    Mult_P4,PlusMult_Co4,Plus_P4; auto.
    rewrite (@PlusMult_Co3 R_str2 RA2),(@Mult_P3 R_str2 RA2),
    (@Mult_P4 R_str2 RA2 f[m]),<-Mult_P3,<-(@PlusMult_Co3 R_str2 RA2),H12;
    auto. pose proof H20. apply (H3 m) in H21 as [_[]]; auto.
    rewrite ReqR, ReqR' in *.
    rewrite (@PlusMult_Co3 R_str1 RA1),Mult_P3,(@Mult_P4 R_str1 RA1 _ m),
    <-Mult_P3,<-(@PlusMult_Co3 R_str1 RA1); auto. replace R with R1; auto.
    rewrite H21; auto. apply MKT41 in H17; eauto. pose proof H17.
    rewrite Plus_P4 in H17; auto. apply Plus_Co3 in H17; auto.
    rewrite Plus_P4,Plus_P1 in H17; auto. rewrite ReqR, ReqR' in *.
    rewrite H18,H9,H11,H12,<-H17,Minus_P1; auto.
    rewrite H12,(@PlusMult_Co3 R_str1 RA1),Mult_P4,<-Mult_P3,
    (@Mult_P4 R_str1 RA1 n),<-(@PlusMult_Co3 R_str1 RA1); auto.
    replace R with R1; auto. rewrite <-H17; auto.
    pose proof H14. apply (H3 m m) in H19 as [_[]]; auto.
    rewrite H19,(@PlusMult_Co3 R_str2 RA2),Mult_P3,<-(@PlusMult_Co3 R_str2 RA2),
    Mult_P4; auto. }
  assert (∀ m n, m ∈ \{ λ a, (-a)%r1 ∈ N1 \}
    -> n ∈ \{ λ a, (-a)%r1 ∈ N1 \} -> g[(m + n)%r1] = (g[m] + g[n])%r2
    /\ g[(m · n)%r1] = (g[m] · g[n])%r2).
  { intros. assert (m ∈ Z1 /\ n ∈ Z1) as [].
    { split; apply MKT4; right; apply MKT4; auto. }
    assert ((m + n)%r1 ∈ \{ λ a, (-a)%r1 ∈ N1 \}).
    { apply AxiomII in H15 as [_],H16 as [_].
      apply AxiomII; split; eauto.
      rewrite (@PlusMult_Co3 R_str1 RA1),Mult_P4,Mult_P5,Mult_P4,
      <-PlusMult_Co3,Mult_P4,<-PlusMult_Co3; auto. }
    assert (m · n = (-m) · (-n))%r1.
    { rewrite ReqR, ReqR' in *.
      assert (-m = (-(1)) · m)%r1. { rewrite (@PlusMult_Co3 R_str1 RA1); auto. }
      assert (-n = (-(1)) · n)%r1. { rewrite (@PlusMult_Co3 R_str1 RA1); auto. }
      rewrite H20,H21,Mult_P3,(@Mult_P4 R_str1 RA1 _ m),<-(@Mult_P3 R_str1 RA1 m),
      PlusMult_Co5,Mult_P1,Mult_P1; auto. }
    assert ((m · n)%r1 ∈ N1).
    { apply AxiomII in H15 as [_],H16 as [_]. rewrite H20; auto. }
    rewrite H12,H12,H12,H11; auto. split.
    rewrite (@PlusMult_Co3 R_str1 RA1),Mult_P4,Mult_P5,Mult_P4,<-PlusMult_Co3,
    Mult_P4,<-PlusMult_Co3; auto.
    apply AxiomII in H15 as [_],H16 as [_].
    pose proof H16. apply (H3 (-m)%r1) in H22 as [H22 _]; auto.
    rewrite ReqR, ReqR' in *.
    rewrite H22,(@PlusMult_Co3 R_str2 RA2),Mult_P4,Mult_P5,Mult_P4,
    <-(@PlusMult_Co3 R_str2 RA2),Mult_P4,<-(@PlusMult_Co3 R_str2 RA2);
    auto. apply AxiomII in H15 as [_],H16 as [_].
    pose proof H16. apply (H3 (-m)%r1) in H22 as [_[H22 _]]; auto.
    rewrite ReqR, ReqR' in *.
    rewrite H20,H22,(@PlusMult_Co3 R_str2 RA2); auto.
    replace (-f[(-n)%r1])%r2 with ((-1')·f[(-n)%r1])%r2.
    rewrite Mult_P3,(@Mult_P4 R_str2 RA2 (-1')%r2),
    <-(@Mult_P3 R_str2 RA2 _ (-1')%r2 (-1')%r2),PlusMult_Co4,Mult_P1; auto.
    rewrite <-(@PlusMult_Co3 R_str2 RA2); auto. }
  assert (∀ m, m ∈ Z1 -> g[m] ∈ Z2).
  { intros. rewrite <-H7 in H16.
    apply Property_Value,Property_ran in H16; auto. }
  split; intros. pose proof H17; pose proof H18.
  apply MKT4 in H19 as []. apply MKT4 in H20 as [].
  rewrite H11,H11,H11,H11; auto.
  apply (H3 m n) in H19; tauto. apply MKT4 in H20 as [].
  apply (H14 m n) in H19; auto. apply MKT41 in H20; eauto.
  rewrite H20,Plus_P1,PlusMult_Co1,H9,(@Plus_P1 R_str2 RA2),
  (@PlusMult_Co1 R_str2 RA2); auto. apply MKT4 in H19 as [].
  apply MKT4 in H20 as []. rewrite Plus_P4,(@Plus_P4 R_str2 RA2),
  Mult_P4,(@Mult_P4 R_str2 RA2); auto. apply MKT4 in H20 as []; auto.
  apply MKT41 in H20; eauto.
  rewrite H20,Plus_P1,PlusMult_Co1,H9,(@Plus_P1 R_str2 RA2),
  (@PlusMult_Co1 R_str2 RA2); auto. apply MKT41 in H19; eauto.
  rewrite H19,H9,Plus_P4,Plus_P1,(@Plus_P4 R_str2 RA2),(@Plus_P1 R_str2 RA2),
  Mult_P4,PlusMult_Co1,(@Mult_P4 R_str2 RA2),(@PlusMult_Co1 R_str2 RA2);
  auto. split; intros. apply MKT4 in H17 as []. rewrite H11; auto.
  rewrite NeqN, NeqN' in *. rewrite <-H1 in H17.
  apply Property_Value,Property_ran in H17; auto. rewrite H2 in H17.
  assert (0' < f[m])%r2 as []; auto.
  { destruct (@one_is_min_in_N R_str2 RA2) as [_[]].
    apply (@Order_Co2 R_str2 RA2 _ 1'); auto. }
  apply MKT4 in H17 as []. rewrite H12; auto.
  apply AxiomII in H17 as []. rewrite NeqN, NeqN' in *. rewrite <-H1 in H19.
  apply Property_Value,Property_ran in H19; auto.
  rewrite H2 in H19. assert (0' < f[(-m)%r1])%r2.
  { destruct (@one_is_min_in_N R_str2 RA2) as [_[]].
    apply (@Order_Co2 R_str2 RA2 _ 1'); auto. }
  apply (@OrderPM_Co1 R_str2 RA2 _ _ (-f[(-m)%r1])%r2) in H20; auto.
  rewrite (@Plus_P4 R_str2 RA2),(@Plus_P1 R_str2 RA2),Minus_P1 in H20; auto.
  destruct H20; auto. apply MKT41 in H17; eauto.
  assert (m ∈ N1).
  { pose proof H17. apply MKT4 in H17 as []; auto.
    apply MKT4 in H17 as []. apply AxiomII in H17 as [].
    apply OrderPM_Co2a in H18; auto.
    assert (0 < (-m))%r1.
    { destruct (@one_is_min_in_N R_str1 RA1) as [_[_]].
      apply (@Order_Co2 R_str1 RA1 _ 1); auto. }
    assert (0 < 0)%r1 as []; try contradiction.
    { apply (@Order_Co2 R_str1 RA1 _ (-m)%r1); destruct H21; auto. }
    apply MKT41 in H17; eauto. rewrite H17 in H18.
    destruct H18; contradiction. }
  destruct (classic (m = 1)). rewrite H20,H10; auto.
  assert (1 < m)%r1.
  { split; auto. destruct (@one_is_min_in_N R_str1 RA1) as [_[]]; auto. }
  apply H3a in H21; auto. rewrite <-H11 in H21; auto.
  rewrite H10 in H21. rewrite H11; auto. destruct H21.
  apply (@Order_Co2 R_str2 RA2 _ 1'); auto.
Qed.

Lemma UniqueT5_Lemma4 : ∃ f, Function f /\ dom(f) = Q1 /\ ran(f) ⊂ Q2
  /\ f[0] = 0' /\ f[1] = 1'
  /\ (∀ a b, a ∈ Q1 -> b ∈ Q1
     -> f[(a + b)%r1] = (f[a] + f[b])%r2 /\ f[(a · b)%r1] = (f[a] · f[b])%r2)
  /\ (∀ a b, a ∈ Q1 -> b ∈ Q1 -> (a < b)%r1 -> (f[a] < f[b])%r2).
Proof.
  destruct UniqueT5_Lemma3 as [f[H[H0[H1[H2[H3[H4[H5 H5a]]]]]]]].
  assert (∀ m, m ∈ (Z1 ~ [0]) -> f[m] ∈ (Z2 ~ [0'])).
  { intros. apply MKT4' in H6 as []. apply AxiomII in H7 as [].
    pose proof H6. rewrite <-H0 in H6.
    apply Property_Value,Property_ran in H6; auto.
    apply MKT4'; split; auto. apply AxiomII; split; eauto.
    intro. apply MKT41 in H10; eauto. apply NNPP in H10.
    apply H10,H5; auto. intro. elim H8. apply MKT41; eauto. }
  assert (∀ m, m ∈ Z1 -> f[m] ∈ Z2) as H6a.
  { intros. rewrite <-H0 in H7.
    apply Property_Value,Property_ran in H7; auto. }
  assert ((Z1 ~ [0]) ⊂ (R1 ~ [0]) /\ (Z2 ~ [0']) ⊂ (R2 ~ [0'])) as [].
  { split; unfold Included; intros; apply MKT4' in H7 as [];
    apply MKT4'; auto. }
  assert ((Z1 ~ [0]) ⊂ R1 /\ (Z2 ~ [0']) ⊂ R2) as [].
  { split; unfold Included; intros; apply MKT4' in H9 as [];
    auto. }
  assert ((R1 ~ [0]) ⊂ R1 /\ (R2 ~ [0']) ⊂ R2) as [].
  { split; unfold Included; intros; apply MKT4' in H11; tauto. }
  assert ((Z1 ~ [0]) ⊂ Z1 /\ (Z2 ~ [0']) ⊂ Z2) as [].
  { split; unfold Included; intros; apply MKT4' in H13; tauto. }
  pose proof (@Mult_inv1 R_str1 RA1); pose proof (@Mult_inv1 R_str2 RA2).
  assert (∀ a b c d, a ∈ Z1 -> b ∈ (Z1 ~ [0])
    -> c ∈ Z1 -> d ∈ (Z1 ~ [0]) -> (a / b = c / d)%r1
    -> (f[a] / f[b] = f[c] / f[d])%r2).
  { intros. assert ((b · d) · (a / (1 ·b)) = (b · d) · (c / (1 · d)))%r1.
    { rewrite (@Mult_P4 R_str1 RA1 1),(@Mult_P4 R_str1 RA1 1),
      Mult_P1,Mult_P1,H21; auto. }
    rewrite Mult_P3,<-(@Mult_P3 R_str1 RA1 b d a),(@Mult_P4 R_str1 RA1 b),
    <-Frac_P2,Divide_P2,Divide_P1,Mult_P1,Mult_P3,(@Mult_P4 R_str1 RA1 _ c),
    Mult_P3,<-Frac_P2,Divide_P2,Divide_P1,Mult_P1 in H22;
    try (rewrite Mult_P4,Mult_P1); try apply one_in_R; auto.
    assert (f[d · a] = f[c · b])%r1. { rewrite H22; auto. }
    assert (f[(d · a)%r1] = (f[d] · f[a])%r2 /\ f[(c · b)%r1] = (f[c] · f[b])%r2)
    as []. { split; apply H4; auto. } rewrite H24,H25 in H23.
    assert ((f[d] · f[a]) / (f[d] · f[b])
      = (f[c] · f[b]) / (f[d] · f[b]))%r2. { rewrite H23; auto. }
    rewrite <-Frac_P1,(@Mult_P4 R_str2 RA2 f[d]),(@Mult_P4 R_str2 RA2 f[d]),
    <-Frac_P1 in H26; auto. }
  set (g := \{\ λ u v, (∃ m n, m ∈ Z1 /\ n ∈ (Z1 ~ [0])
    /\ u = (m / n)%r1 /\ v = (f[m] / f[n])%r2) \}\).
  assert (Function g).
  { split; unfold Relation; intros.
    apply AxiomII in H18 as [_[x[y[]]]]; eauto.
    apply AxiomII' in H18 as [_[m[n[H18[H20[]]]]]].
    apply AxiomII' in H19 as [_[a[b[H19[H23[]]]]]].
    rewrite H21 in H24. rewrite H22,H25; auto. }
  assert (dom(g) = Q1).
  { apply AxiomI; split; intros. apply AxiomII in H19 as [H19[]].
    apply AxiomII' in H20 as [_[a[b[H20[H21[]]]]]].
    apply AxiomII; split; eauto.
    apply AxiomII in H19 as [H19[a[b[H20[]]]]].
    apply AxiomII; split; auto. exists (f[a] / f[b])%r2.
    apply AxiomII'; split. apply MKT49a; auto. exists R2.
    apply Mult_close; auto. exists a,b; auto. }
  assert (ran(g) ⊂ Q2).
  { unfold Included; intros. apply Einr in H20 as [x[]]; auto.
    apply Property_Value,AxiomII' in H20 as [_[a[b[H20[H22[]]]]]]; auto.
    rewrite H21,H24. apply AxiomII; split. exists R2.
    apply Mult_close; auto. exists f[a],f[b]. auto. }
  assert (∀ a b, a ∈ Z1 -> b ∈ (Z1 ~ [0]) -> g[(a / b)%r1]
    = (f[a] / f[b])%r2).
  { intros. assert ((a / b)%r1 ∈ Q1).
    { apply AxiomII; split; eauto. exists R1. auto. }
    rewrite <-H19 in H23. apply Property_Value,AxiomII' in H23
    as [_[x[y[H23[H24[]]]]]]; auto. rewrite H26; auto. }
  assert (0 ∈ Z1 /\ 1 ∈ (Z1 ~ [0])) as [].
  { split. repeat (apply MKT4; right). apply MKT41; eauto.
    apply MKT4'; split; auto. apply AxiomII; split;
    eauto. intro. apply MKT41 in H22; eauto.
    destruct OrderPM_Co9; auto. }
  assert (g[0] = 0' /\ g[1] = 1') as [].
  { assert (0 = 0 / 1 /\ 1 = 1 / 1)%r1 as [].
    { split; rewrite Divide_P2; auto. }
    split; [rewrite H24|rewrite H25]; rewrite H21; auto;
    try rewrite H2; rewrite H3,Divide_P2; auto. }
  assert (ReqR: (@R R_str1) = R1) by auto.
  assert (ReqR': (@R R_str2) = R2) by auto.
  assert (∀ a b, a ∈ Q1 -> b ∈ Q1 -> g[(a + b)%r1] = (g[a] + g[b])%r2
    /\ g[(a · b)%r1] = (g[a] · g[b])%r2).
  { intros. apply AxiomII in H26 as [_[a1[a2[H26[]]]]].
    apply AxiomII in H27 as [_[b1[b2[H27[]]]]].
    rewrite H29,H31,H21,H21,Frac_P2; auto.
    assert ((a2 · b2)%r1 ∈ (Z1 ~ [0])).
    { apply MKT4' in H28 as [],H30 as [].
      apply MKT4'; split; auto.
      apply AxiomII; split; eauto. intro. apply MKT41 in H34;
      eauto. apply AxiomII in H32 as [_],H33 as [_].
      apply PlusMult_Co2 in H34 as []; auto; [elim H32|elim H33];
      apply MKT41; eauto. }
    assert (a1 / a2 + b1 / b2 = (a1 · b2 + a2 · b1) / (a2 · b2))%r1.
    { rewrite Mult_P5,<-Frac_P1,(@Mult_P4 R_str1 RA1 a2),
     (@Mult_P4 R_str1 RA1 a2),<-Frac_P1; auto. }
    rewrite ReqR, ReqR' in *.
    rewrite H33,H21; auto.
    assert ((a1 · b2) ∈ Z1 /\ (a2 · b1) ∈ Z1)%r1 as [].
    { split; apply Int_P1b; auto. }
    apply (H4 (a1 · b2)%r1) in H35 as [H35 _]; auto.
    pose proof H26; pose proof H27. apply (H4 _ b2) in H36 as [_]; auto.
    apply (H4 a2) in H37 as [_]; auto. rewrite H35,H36,H37.
    pose proof H28. apply MKT4' in H38 as []. apply (H4 _ b2) in H38
    as []; auto. split. rewrite H40,Mult_P5,<-Frac_P1,
    (@Mult_P4 R_str2 RA2 f[a2]),(@Mult_P4 R_str2 RA2 f[a2]),<-Frac_P1; auto.
    apply H6,H8,(@Mult_inv1 R_str2 RA2),MKT4' in H32 as [].
    apply MKT4' in H28 as []. apply (H4 _ b2) in H28 as []; auto.
    rewrite <-H43; auto. rewrite H21; auto. pose proof H26.
    apply (H4 a1 b1) in H41 as []; auto.
    rewrite H42,H40,Frac_P2; auto. }
  assert (NeqN: (@N R_str1) = N1) by auto.
  assert (NeqN': (@N R_str2) = N2) by auto.
  assert (∀ a, a ∈ Q1 -> (0 < a)%r1 -> 0' < g[a])%r2.
  { intros. apply Existence_of_irRational_Number_Lemma6 in H27
    as [x[y[H27[]]]]; auto. assert (0 < x /\ 0 < y)%r1 as [].
    { destruct (@one_is_min_in_N R_str1 RA1) as [_[]].
      split; apply (@Order_Co2 R_str1 RA1 _ 1); auto. }
    assert (y ∈ (Z1 ~ [0])).
    { apply MKT4'; split; auto. apply AxiomII; split;
      eauto. intro. apply MKT41 in H33; eauto.
      rewrite H33 in H32. destruct H32; auto. }
    rewrite H30,H21; auto. pose proof H31; pose proof H32.
    apply H5a in H34,H35; auto. apply OrderPM_Co5; auto.
    rewrite ReqR, ReqR' in *. rewrite NeqN, NeqN' in *.
    left. split; auto. }
  assert (∀ a b, a ∈ Q1 -> b ∈ Q1 -> (a < b)%r1 -> (g[a] < g[b])%r2).
  { intros. apply (@OrderPM_Co1 R_str1 RA1 _ _ (-a)%r1) in H30; auto.
    rewrite Minus_P1 in H30; auto.
    apply H27 in H30; [ |apply Rat_P1a; auto; apply Rat_P3; auto].
    assert (∀ x, x ∈ Q1 -> g[x] ∈ Q2).
    { intros. rewrite <-H19 in H31.
      apply Property_Value,Property_ran in H31; auto. }
    assert (g[(b - a)%r1] = (g[b] - g[a])%r2).
    { pose proof H28. apply Rat_P3 in H32 as [H32 _].
      apply (H26 b) in H32 as [H32 _]; auto.
      rewrite PlusMult_Co3 in H32; auto.
      assert ((-(1)) ∈ Q1)%r1. { apply Rat_P3; auto. }
      pose proof H33. apply (H26 _ a) in H33 as [_]; auto.
      assert (g[1] + g[(-(1))%r1] = 0')%r2.
      { apply (H26 1) in H34 as [H34 _]; auto.
        rewrite Minus_P1,H24 in H34; auto. }
      rewrite H25 in H35. apply Plus_Co3 in H35; auto.
      rewrite Plus_P4,Plus_P1 in H35; auto.
      rewrite H35,<-(@PlusMult_Co3 R_str2 RA2) in H33; auto.
      rewrite ReqR, ReqR' in *.
      rewrite H33,<-(@PlusMult_Co3 R_str1 RA1) in H32; auto. eauto. }
    rewrite H32 in H30. apply (@OrderPM_Co1 R_str2 RA2 _ _ g[a]) in H30; auto.
    rewrite (@Plus_P4 R_str2 RA2),(@Plus_P1 R_str2 RA2),<-Plus_P3,
    (@Plus_P4 R_str2 RA2 (-(g[a]))%r2),Minus_P1,Plus_P1 in H30; auto. }
  eauto 10.
Qed.

Lemma UniqueT5_Lemma5a : ∀ a b c, a ∈ Q1 -> b ∈ R1 -> c ∈ R1
  -> (0 < a)%r1 -> (0 < b)%r1 -> (0 < c)%r1 -> (a < (b + c))%r1
  -> ∃ a1 a2, a1 ∈ Q1 /\ a2 ∈ Q1 /\ (0 < a1)%r1 /\ (a1 < b)%r1
    /\ (0 < a2)%r1 /\ (a2 < c)%r1 /\ (a1 + a2)%r1 = a.
Proof.
  intros. assert ((a - c) < b)%r1.
  { apply (@OrderPM_Co1 R_str1 RA1 _ _ (-c)%r1) in H5; auto.
    rewrite <-Plus_P3,Minus_P1,Plus_P1 in H5; auto. }
  assert (∃ a1, a1 ∈ Q1 /\ 0 < a1 /\ (a - c) < a1 /\ a1 < b /\ a1 < a)%r1
    as [a1[H7[H8[H9[]]]]].
  { pose proof (@zero_in_R R_str1 RA1).
    pose proof H. apply Q_Subset_R in H8; auto.
    apply (@Order_Co1 R_str1 RA1 _ (a - c)%r1) in H7 as []; auto;
    apply (@Order_Co1 R_str1 RA1 b) in H8 as []; auto.
    - apply Arch_P9 in H6 as [a1[H6[]]]; auto.
      exists a1. split; [ |split; [ |split; [ |split]]]; auto.
      apply (@Order_Co2 R_str1 RA1 _ (a - c)%r1); auto; destruct H7; auto.
      apply (@Order_Co2 R_str1 RA1 _ b); auto; destruct H8; auto.
    - assert (a - c < a)%r1.
      { apply (@OrderPM_Co1 R_str1 RA1 _ _ a) in H4; auto.
        rewrite Plus_P4,Plus_P1,Plus_P4 in H4; auto.
        apply (@OrderPM_Co1 R_str1 RA1 _ _ (-c)%r1) in H4; auto.
        rewrite <-Plus_P3,Minus_P1,Plus_P1 in H4; auto. }
      apply Arch_P9 in H9 as [a1[H9[]]]; auto.
      exists a1. split; [ |split; [ |split; [ |split]]]; auto.
      apply (@Order_Co2 R_str1 RA1 _ (a - c)%r1); auto; destruct H7; auto.
      destruct H8; [ |rewrite H8; auto].
      apply (@Order_Co2 R_str1 RA1 _ a); auto; destruct H8; auto.
    - apply Arch_P9 in H3 as [a1[H3[]]]; auto.
      exists a1. split; [ |split; [ |split; [ |split]]]; auto.
      apply (@Order_Co2 R_str1 RA1 _ 0); auto. right. split; auto.
      repeat destruct H7; auto. apply Leq_P1; auto.
      apply (@Order_Co2 R_str1 RA1 _ b); auto; destruct H8; auto.
    - apply Arch_P9 in H2 as [a1[H2[]]]; auto.
      exists a1. split; [ |split; [ |split; [ |split]]]; auto.
      apply (@Order_Co2 R_str1 RA1 _ 0); auto. right. split; auto.
      repeat destruct H7; auto. apply Leq_P1; auto.
      destruct H8; [ |rewrite H8; auto].
      apply (@Order_Co2 R_str1 RA1 _ a); auto; destruct H8; auto. }
  apply (@OrderPM_Co1 R_str1 RA1 _ _ c) in H9; auto.
  rewrite <-Plus_P3,(@Plus_P4 R_str1 RA1 (-c)%r1),Minus_P1,Plus_P1 in H9;
  auto. apply (@OrderPM_Co1 R_str1 RA1 _ _ (-a1)%r1) in H9; auto.
  rewrite (@Plus_P4 R_str1 RA1 a1),<-Plus_P3,Minus_P1,Plus_P1 in H9; auto.
  exists a1,(a - a1)%r1. split; auto. split. apply Rat_P1a; auto.
  apply Rat_P3; auto. split; [ |split; [ |split; [ |split]]]; auto.
  apply (@OrderPM_Co1 R_str1 RA1 _ _ (-a1)%r1) in H11; auto.
  rewrite Minus_P1 in H11; auto. rewrite Plus_P3,
  (@Plus_P4 R_str1 RA1 a1),<-Plus_P3,Minus_P1,Plus_P1; auto.
Qed.

Lemma UniqueT5_Lemma5b : ∀ a b c, a ∈ R2 -> b ∈ R2 -> c ∈ R2
  -> (0' < a)%r2 -> (0' < b)%r2 -> (0' < c)%r2 -> (a < (b + c))%r2
  -> ∃ a1 a2, a1 ∈ R2 /\ a2 ∈ R2 /\ (0' < a1)%r2 /\ (a1 < b)%r2
    /\ (0' < a2)%r2 /\ (a2 < c)%r2 /\ (a1 + a2)%r2 = a.
Proof.
  intros. assert ((a - c) < b)%r2.
  { apply (@OrderPM_Co1 R_str2 RA2 _ _ (-c)%r2) in H5; auto.
    rewrite <-Plus_P3,Minus_P1,Plus_P1 in H5; auto. }
  assert (∃ a1, a1 ∈ R2 /\ 0' < a1 /\ (a - c) < a1 /\ a1 < b /\ a1 < a)%r2
    as [a1[H7[H8[H9[]]]]].
  { pose proof (@zero_in_R R_str2 RA2). pose proof H.
    apply (@Order_Co1 R_str2 RA2 _ (a - c)%r2) in H7 as []; auto;
    apply (@Order_Co1 R_str2 RA2 b) in H8 as []; auto.
    - apply Arch_P9 in H6 as [a1[H6[]]]; auto. exists a1.
      split; [ |split; [ |split; [ |split]]]; auto.
      apply (@Order_Co2 R_str2 RA2 _ (a - c)%r2); auto; destruct H7; auto.
      apply (@Order_Co2 R_str2 RA2 _ b); auto; destruct H8; auto.
    - assert (a - c < a)%r2.
      { apply (@OrderPM_Co1 R_str2 RA2 _ _ a) in H4; auto.
        rewrite Plus_P4,Plus_P1,Plus_P4 in H4; auto.
        apply (@OrderPM_Co1 R_str2 RA2 _ _ (-c)%r2) in H4; auto.
        rewrite <-Plus_P3,Minus_P1,Plus_P1 in H4; auto. }
      apply Arch_P9 in H9 as [a1[H9[]]]; auto. exists a1.
      split; [ |split; [ |split; [ |split]]]; auto.
      apply (@Order_Co2 R_str2 RA2 _ (a - c)%r2); auto; destruct H7; auto.
      destruct H8; [ |rewrite H8; auto].
      apply (@Order_Co2 R_str2 RA2 _ a); auto; destruct H8; auto.
    - apply Arch_P9 in H3 as [a1[H3[]]]; auto. exists a1.
      split; [ |split; [ |split; [ |split]]]; auto.
      apply (@Order_Co2 R_str2 RA2 _ 0'); auto. right. split; auto.
      repeat destruct H7; auto. apply Leq_P1; auto.
      apply (@Order_Co2 R_str2 RA2 _ b); auto; destruct H8; auto.
    - apply Arch_P9 in H2 as [a1[H2[]]]; auto. exists a1.
      split; [ |split; [ |split; [ |split]]]; auto.
      apply (@Order_Co2 R_str2 RA2 _ 0'); auto. right. split; auto.
      repeat destruct H7; auto. apply Leq_P1; auto.
      destruct H8; [ |rewrite H8; auto].
      apply (@Order_Co2 R_str2 RA2 _ a); auto; destruct H8; auto. }
  apply (@OrderPM_Co1 R_str2 RA2 _ _ c) in H9; auto.
  rewrite <-Plus_P3,(@Plus_P4 R_str2 RA2 (-c)%r2),Minus_P1,Plus_P1 in H9; auto.
  apply (@OrderPM_Co1 R_str2 RA2 _ _ (-a1)%r2) in H9; auto.
  rewrite (@Plus_P4 R_str2 RA2 a1),<-Plus_P3,Minus_P1,Plus_P1 in H9; auto.
  exists a1,(a - a1)%r2. split; auto. split. auto.
  split; [ |split; [ |split; [ |split]]]; auto.
  apply (@OrderPM_Co1 R_str2 RA2 _ _ (-a1)%r2) in H11; auto.
  rewrite Minus_P1 in H11; auto. rewrite Plus_P3,(@Plus_P4 R_str2 RA2 a1),
  <-Plus_P3,Minus_P1,Plus_P1; auto.
Qed.

Lemma UniqueT5_Lemma6a : ∀ a b c, a ∈ Q1 -> b ∈ R1 -> c ∈ R1
  -> (0 < a)%r1 -> (0 < b)%r1 -> (0 < c)%r1 -> (a < (b · c))%r1
  -> ∃ a1 a2, a1 ∈ Q1 /\ a2 ∈ Q1 /\ (0 < a1)%r1 /\ (a1 < b)%r1
    /\ (0 < a2)%r1 /\ (a2 < c)%r1 /\ (a1 · a2)%r1 = a.
Proof.
  intros. assert (c ∈ (R1 ~ [0])).
  { apply MKT4'; split; auto. apply AxiomII; split; eauto.
    intro. apply MKT41 in H6; eauto. rewrite H6 in H4.
    destruct H4; auto. }
  pose proof H6. apply (@Mult_inv1 R_str1 RA1),MKT4' in H7 as [H7 _].
  pose proof H4. apply OrderPM_Co10 in H8; auto.
  assert ((a / c) < b)%r1.
  { apply (@OrderPM_Co7a R_str1 RA1 _ _ (c⁻)%r1) in H5; auto.
    rewrite <-Mult_P3,Divide_P1,Mult_P1 in H5; auto. }
  assert (0 < (a / c))%r1.
  { apply (@OrderPM_Co7a R_str1 RA1 _ _ (c⁻)%r1) in H2; auto.
    rewrite <-Mult_P4,PlusMult_Co1 in H2; auto. }
  assert (∃ a1, a1 ∈ Q1 /\ 0 < a1 /\ (a / c) < a1 /\ a1 < b)%r1
    as [a1[H11[H12[]]]].
  { apply Arch_P9 in H9 as [a1[H9[]]]; auto. exists a1.
    split; [ |split; [ |split]]; auto.
    apply (@Order_Co2 R_str1 RA1 _ (a / c)%r1); auto; destruct H11; auto. }
  assert (a1 ∈ (R1 ~ [0])).
  { apply MKT4'; split; auto. apply AxiomII; split; eauto.
    intro. apply MKT41 in H15; eauto. rewrite H15 in H12. destruct H12; auto. }
  pose proof H15. apply Mult_inv1,MKT4' in H16 as [H16 _]; auto.
  pose proof H12. apply OrderPM_Co10 in H17; auto.
  exists a1,(a / a1)%r1. split; auto. split. apply Rat_P1b; auto.
  apply Rat_P7; auto. apply MKT4'; split; auto.
  apply MKT4' in H15; tauto. split; [ |split; [ |split; [ |split]]]; auto.
  apply OrderPM_Co5; auto.
  apply (@OrderPM_Co7a R_str1 RA1 _ _ c) in H13; auto.
  rewrite Mult_P4,Mult_P3,(Mult_P4 c),<-Mult_P3,
  Divide_P1,Mult_P1,Mult_P4 in H13; auto.
  apply (@OrderPM_Co7a R_str1 RA1 _ _ (a1⁻)%r1) in H13; auto.
  rewrite <-Mult_P3,Divide_P1,Mult_P1 in H13; auto.
  rewrite Mult_P4,<-Mult_P3,(@Mult_P4 R_str1 RA1 _ a1),Divide_P1,Mult_P1; auto.
Qed.

Lemma UniqueT5_Lemma6b : ∀ a b c, a ∈ R2 -> b ∈ R2 -> c ∈ R2
  -> (0' < a)%r2 -> (0' < b)%r2 -> (0' < c)%r2 -> (a < (b · c))%r2
  -> ∃ a1 a2, a1 ∈ R2 /\ a2 ∈ R2 /\ (0' < a1)%r2 /\ (a1 < b)%r2
    /\ (0' < a2)%r2 /\ (a2 < c)%r2 /\ (a1 · a2)%r2 = a.
Proof.
  intros. assert (c ∈ (R2 ~ [0'])).
  { apply MKT4'; split; auto. apply AxiomII; split; eauto.
    intro. apply MKT41 in H6; eauto. rewrite H6 in H4. destruct H4; auto. }
  pose proof H6. apply Mult_inv1,MKT4' in H7 as [H7 _]; auto.
  pose proof H4. apply OrderPM_Co10 in H8; auto.
  assert ((a / c) < b)%r2.
  { apply (@OrderPM_Co7a R_str2 RA2 _ _ (c⁻)%r2) in H5; auto.
    rewrite <-Mult_P3,Divide_P1,Mult_P1 in H5; auto. }
  assert (0' < (a / c))%r2.
  { apply (@OrderPM_Co7a R_str2 RA2 _ _ (c⁻)%r2) in H2; auto.
    rewrite <-Mult_P4,PlusMult_Co1 in H2; auto. }
  assert (∃ a1, a1 ∈ R2 /\ 0' < a1 /\ (a / c) < a1 /\ a1 < b)%r2
    as [a1[H11[H12[]]]].
  { apply Arch_P9 in H9 as [a1[H9[]]]; auto. exists a1.
    split; [ |split; [ |split]]; auto.
    apply (@Order_Co2 R_str2 RA2 _ (a / c)%r2); auto. destruct H11; auto. }
  assert (a1 ∈ (R2 ~ [0'])).
  { apply MKT4'; split; auto. apply AxiomII; split; eauto.
    intro. apply MKT41 in H15; eauto. rewrite H15 in H12. destruct H12; auto. }
  pose proof H15. apply Mult_inv1,MKT4' in H16 as [H16 _]; auto.
  pose proof H12. apply OrderPM_Co10 in H17; auto.
  exists a1,(a / a1)%r2. split; auto. split. auto.
  split; [ |split; [ |split; [ |split]]]; auto. apply OrderPM_Co5; auto.
  apply (@OrderPM_Co7a R_str2 RA2 _ _ c) in H13; auto.
  rewrite Mult_P4,Mult_P3,(@Mult_P4 R_str2 RA2 c),<-Mult_P3,
  Divide_P1,Mult_P1,Mult_P4 in H13; auto.
  apply (@OrderPM_Co7a R_str2 RA2 _ _ (a1⁻)%r2) in H13; auto.
  rewrite <-Mult_P3,Divide_P1,Mult_P1 in H13; auto.
  rewrite Mult_P4,<-Mult_P3,(@Mult_P4 R_str2 RA2 _ a1),Divide_P1,Mult_P1; auto.
Qed.

Lemma UniqueT5_Lemma7 : ∃ f, Function f
  /\ dom(f) = \{ λ u, u ∈ R1 /\ (0 < u)%r1 \} /\ ran(f) ⊂ R2
  /\ (∀ m n, m ∈ dom(f) -> n ∈ dom(f) -> f[(m + n)%r1] = (f[m] + f[n])%r2)
  /\ (∀ m n, m ∈ dom(f) -> n ∈ dom(f) -> f[(m · n)%r1] = (f[m] · f[n])%r2)
  /\ (∀ m n, m ∈ dom(f) -> n ∈ dom(f) -> (m < n)%r1
    -> f[(n - m)%r1] = (f[n] - f[m])%r2)
  /\ f[1] = 1'.
Proof.
  destruct UniqueT5_Lemma4 as [f[H[H0[H1[H2[H3[]]]]]]].
  set (A r := \{ λ u, ∃ x, x ∈ \{ λ v, v ∈ Q1 /\ (0 < v)%r1
    /\ (v < r)%r1 \} /\ u = f[x] \}).
  assert (∀ r, (A r) ⊂ R2) as Ha.
  { unfold Included; intros. apply AxiomII in H6 as [_[x[]]].
    apply AxiomII in H6 as [_[H6[]]]. rewrite <-H0 in H6.
    apply Property_Value,Property_ran in H6; auto. rewrite H7; auto. }
  assert (∀ r, r ∈ Q1 -> f[r] ∈ R2) as Hf.
  { intros. rewrite <-H0 in H6.
    apply Property_Value,Property_ran in H6; auto. }
  set (g := \{\ λ u v, u ∈ R1 /\ (0 < u)%r1 /\ Sup1b (A u) v \}\).
  assert (Function g).
  { split; unfold Relation; intros.
    apply AxiomII in H6 as [_[x[y[]]]]; eauto.
    apply AxiomII' in H6 as [_[_[_]]],H7 as [_[_[_]]].
    apply Sup1_equ_Sup2 in H6,H7; auto. unfold Sup2 in H6,H7.
    eapply Min_Unique; eauto. }
  assert (dom(g) = \{ λ u, u ∈ R1 /\ (0 < u)%r1 \}).
  { apply AxiomI; split; intros. apply AxiomII in H7 as [_[]].
    apply AxiomII' in H7 as [_[H7[]]]. apply AxiomII; split; eauto.
    assert (exists ! y, Sup1b (A z) y) as [y[H8 _]].
    { apply SupT; auto. apply NEexE. apply AxiomII in H7 as [_[]].
      apply Arch_P9 in H8 as [q[H8[]]]; auto. exists f[q].
      pose proof H8. replace (Q R_str1) with Q1 in H11; auto.
      rewrite <-H0 in H11. apply Property_Value,Property_ran in H11; auto.
      apply AxiomII; split; eauto. exists q. split; auto.
      apply AxiomII; split; eauto. apply AxiomII in H7 as [_[]].
      pose proof H7. apply Arch_P10 in H9 as [m[[H9[_]]_]]; auto.
      apply (@Int_P1a R_str1 RA1 m 1),Z_Subset_Q in H9; auto.
      pose proof H9. replace (Q R_str1) with Q1 in H11; auto.
      rewrite <-H0 in H11. apply Property_Value,Property_ran in H11; auto.
      exists f[(m + 1)%r1]. repeat split; auto. intros.
      apply AxiomII in H12 as [_[x0[]]].
      apply AxiomII in H12 as [_[H12[]]].
      assert (x0 < m + 1)%r1.
      { apply (@Order_Co2 R_str1 RA1 _ z); auto; destruct H10; auto. }
      rewrite H13. apply H5 in H16 as []; auto. }
    apply AxiomII; split; eauto. exists y. apply AxiomII'; split.
    destruct H8 as [[_[]]]. apply MKT49a; eauto.
    apply AxiomII in H7 as [_[]]; auto. }
  assert (ran(g) ⊂ R2).
  { unfold Included; intros. apply Einr in H8 as [x[]]; auto.
    apply Property_Value,AxiomII' in H8 as [_[_[]]]; auto.
    destruct H10 as [[_[]]]. rewrite H9; auto. }
  assert (∀ m, m ∈ dom(g) -> g[m] ∈ R2).
  { intros. apply Property_Value,Property_ran in H9; auto. }
  assert (dom(g) ⊂ R1).
  { unfold Included; intros. rewrite H7 in H10.
    apply AxiomII in H10; tauto. }
  assert (∀ m, m ∈ dom(g) -> (0' < g[m])%r2).
  { intros. apply Property_Value,AxiomII' in H11 as [_[H11[]]]; auto.
    destruct H13 as [[_[]]_]. apply Arch_P9 in H12 as [x[H12[]]];
    auto. assert (f[x] ∈ (A m)).
    { apply AxiomII; split; [ |exists x].
       replace (Q R_str1) with Q1 in H12; auto.
      rewrite <-H0 in H12. apply MKT69b in H12; eauto. split; auto.
      apply AxiomII; split; eauto. }
    pose proof H17. apply H14 in H18. apply H5 in H15; auto.
    rewrite H2 in H15. apply (@Order_Co2 R_str2 RA2 _ f[x]); auto.
    apply Z_Subset_Q; auto. repeat (apply MKT4; right).
    apply MKT41; eauto. }
  assert (∀ m, m ∈ dom(g) -> Sup1b (A m) g[m]).
  { intros. apply Property_Value,AxiomII' in H12 as [_[_[]]]; auto. }
  assert (∀ a b, a ∈ Q1 -> b ∈ R1 -> (0 < a)%r1 -> (0 < b)%r1
    -> (a < b)%r1 -> (f[a] ≤ g[b])%r2) as Hb.
  { intros. pose proof H13. rewrite <-H0 in H18.
    apply Property_Value,Property_ran in H18; auto.
    assert (f[a] ∈ (A b)).
    { apply AxiomII; split; eauto. exists a. split; auto.
      apply AxiomII; split; eauto. }
    assert (b ∈ dom(g)). { rewrite H7. apply AxiomII; split; eauto. }
    apply H12 in H20 as [[_[]]]; auto. }
  assert (∀ m n, m ∈ dom(g) -> n ∈ dom(g)
    -> g[(m + n)%r1] = (g[m] + g[n])%r2).
  { intros. assert ((m + n)%r1 ∈ dom(g)).
    { rewrite H7. apply AxiomII; split; [exists R1|split].
      apply (@Plus_close R_str1 RA1). apply H10 in H13, H14; auto.
      apply H10 in H13, H14; auto. apply Plus_close; auto. rewrite H7 in H13,H14.
      apply AxiomII in H13 as [_[]],H14 as [_[]].
      replace 0 with (0 + 0)%r1. apply (@OrderPM_Co4 R_str1 RA1); auto.
      destruct H15; auto. rewrite Plus_P1; auto. }
    assert (g[(m + n)%r1] ∈ R2); auto.
    assert ((g[m] + g[n])%r2 ∈ R2). auto.
    pose proof H17. apply (@Order_Co1 R_str2 RA2 g[(m + n)%r1]) in H18
    as [H18|[]]; auto.
    - pose proof H18. apply UniqueT5_Lemma5b in H19
      as [a1[a2[H19[H20[H21[H22[H23[]]]]]]]]; auto.
      pose proof H13; pose proof H14.
      apply H12 in H26 as [[_[_]]],H27 as [[_[_]]].
      apply H28 in H22 as [q1[]]; auto.
      apply AxiomII in H22 as [_[x1[]]].
      apply AxiomII in H22 as [_[H22[]]].
      apply H29 in H24 as [q2[]]; auto.
      apply AxiomII in H24 as [_[x2[]]].
      apply AxiomII in H24 as [_[H24[]]].
      assert (x1 + x2 < m + n)%r1.
      { apply OrderPM_Co4; auto. destruct H33; auto. }
      assert (0 + 0 < x1 + x2)%r1.
      { apply OrderPM_Co4; auto. destruct H32; auto. }
      rewrite Plus_P1 in H39; auto.
      apply Hb in H38; auto.
      assert (f[(x1 + x2)%r1] = (f[x1] + f[x2])%r2). { apply H4; auto. }
      rewrite H40,<-H31,<-H35,<-H25 in H38.
      assert (a1 + a2 < q1 + q2)%r2 as [].
      { apply OrderPM_Co4; auto;
        [rewrite H31|rewrite H35|destruct H30]; auto. }
      elim H42. apply Leq_P2; auto. rewrite H31,H35. apply Plus_close; auto.
      rewrite H7 in H15. apply AxiomII in H15; tauto.
    - pose proof H15. apply H12 in H19 as [[_[_]]].
      pose proof H18. apply H20 in H21 as [q[]]; auto.
      apply AxiomII in H21 as [_[x[]]]. apply AxiomII in H21
      as [_[H21[]]]. pose proof H13; pose proof H14.
      rewrite H7 in H26,H27. apply AxiomII in H26 as [_[_]],
      H27 as [_[_]]. apply UniqueT5_Lemma5a in H25
      as [x1[x2[H25[H28[H29[H30[H31[]]]]]]]]; auto.
      apply Hb in H30,H32; auto.
      assert (f[x1] + f[x2] ≤ g[m] + g[n])%r2. { apply OrderPM_Co3; auto. }
      assert (f[(x1 + x2)%r1] = (f[x1] + f[x2])%r2). { apply H4; auto. }
      rewrite <-H35,H33,<-H23 in H34. destruct H22. elim H36.
      apply Leq_P2; auto. rewrite H23; auto. }
  assert (∀ m n, m ∈ dom(g) -> n ∈ dom(g) -> g[(m · n)%r1] = (g[m] · g[n])%r2).
  { intros. assert ((m · n)%r1 ∈ dom(g)).
    { rewrite H7. apply AxiomII; split; [exists R1|split].
      apply H10 in H14, H15; auto. apply H10 in H14, H15; auto.
      rewrite H7 in H14,H15.
      apply AxiomII in H14 as [_[]],H15 as [_[]].
      apply OrderPM_Co5; auto. }
    assert (g[(m · n)%r1] ∈ R2); auto.
    assert ((g[m] · g[n])%r2 ∈ R2). auto.
    pose proof H18. apply (@Order_Co1 R_str2 RA2 g[(m · n)%r1]) in H19
    as [H19|[]]; auto.
    - apply UniqueT5_Lemma6b in H19
      as [a1[a2[H19[H20[H21[H22[H23[]]]]]]]]; auto.
      pose proof H14; pose proof H15.
      apply H12 in H26 as [[_[_]]],H27 as [[_[_]]].
      apply H28 in H22 as [q1[]]; auto.
      apply AxiomII in H22 as [_[x1[]]].
      apply AxiomII in H22 as [_[H22[]]].
      apply H29 in H24 as [q2[]]; auto.
      apply AxiomII in H24 as [_[x2[]]].
      apply AxiomII in H24 as [_[H24[]]].
      assert (0 < m /\ 0 < n)%r1 as [].
      { rewrite H7 in H14,H15.
        split; [apply AxiomII in H14|apply AxiomII in H15]; tauto. }
      assert (x1 · x2 < m · n)%r1.
      { apply (@OrderPM_Co7a R_str1 RA1 _ _ x2) in H33; auto.
        apply (@OrderPM_Co7a R_str1 RA1 _ _ m) in H37; auto.
        rewrite Mult_P4,(@Mult_P4 R_str1 RA1 n) in H37; auto.
        apply (@Order_Co2 R_str1 RA1 _ (m · x2)%r1); auto.
        destruct H33; auto. }
      apply Hb in H40; auto; try apply OrderPM_Co5; auto.
      assert (f[(x1 · x2)%r1] = (f[x1] · f[x2])%r2). { apply H4; auto. }
      rewrite H41,<-H31,<-H35,<-H25 in H40.
      assert (a1 · a2 < q1 · q2)%r2 as [].
      { apply (@OrderPM_Co7a R_str2 RA2 _ _ a2) in H30; auto;
        [ |rewrite H31; auto].
        apply (@OrderPM_Co7a R_str2 RA2 _ _ q1) in H34; auto;
        try rewrite H31; try rewrite H35; auto.
        rewrite Mult_P4,(@Mult_P4 R_str2 RA2 q2) in H34; auto;
        try rewrite H31; try rewrite H35; auto.
        rewrite <-H31,<-H35. apply (@Order_Co2 R_str2 RA2 _ (q1 · a2)%r2);
        try apply Mult_close; destruct H34; auto;
        try rewrite H31; try rewrite H35; auto.
        rewrite <-H2. apply H5; auto. apply Z_Subset_Q; auto.
        repeat (apply MKT4; right). apply MKT41; eauto. }
      elim H43. apply Leq_P2; auto.
      apply Mult_close; auto; [rewrite H31|rewrite H35]; auto.
    - pose proof H16. apply H12 in H20 as [[_[_]]].
      pose proof H19. apply H21 in H22 as [q[]]; auto.
      apply AxiomII in H22 as [_[x[]]]. apply AxiomII in H22
      as [_[H22[]]]. pose proof H14; pose proof H15.
      rewrite H7 in H27,H28. apply AxiomII in H27 as [_[_]],
      H28 as [_[_]]. apply UniqueT5_Lemma6a in H26
      as [x1[x2[H26[H29[H30[H31[H32[]]]]]]]]; auto.
      apply Hb in H31,H33; auto.
      assert (f[x1] · f[x2] ≤ g[m] · g[n])%r2.
      { apply (@OrderPM_Co7b R_str2 RA2 _ _ f[x2]) in H31; auto.
        apply (@OrderPM_Co7b R_str2 RA2 _ _ g[m]) in H33; auto.
        rewrite Mult_P4,(@Mult_P4 R_str2 RA2 g[n]) in H33; auto.
        apply (@Leq_P3 R_str2 RA2 _ (g[m] · f[x2])%r2); auto.
        apply H11; auto. apply H5 in H32 as []; auto.
        rewrite <-H2; auto. apply Z_Subset_Q; auto.
        repeat (apply MKT4; right). apply MKT41; eauto. }
      assert (f[(x1 · x2)%r1] = (f[x1] · f[x2])%r2). { apply H4; auto. }
      rewrite <-H36,H34,<-H24 in H35. destruct H23. elim H37.
      apply Leq_P2; auto. rewrite H24; auto. }
  assert (∀ m n, m ∈ dom(g) -> n ∈ dom(g) -> (m < n)%r1
    -> g[(n - m)%r1] = (g[n] - g[m])%r2).
  { intros. assert ((n - m)%r1 ∈ dom(g)).
    { rewrite H7 in *. apply AxiomII in H15 as [_[]],H16 as [_[]].
      apply AxiomII; split; [ |split]. exists R1; auto. auto.
      apply (@OrderPM_Co1 R_str1 RA1 _ _ (-m)%r1) in H17; auto.
      rewrite Minus_P1 in H17; auto. }
    assert (g[(n - m + m)%r1] = (g[(n - m)%r1] + g[m])%r2).
    { apply H13; auto. }
    rewrite <-Plus_P3,(@Plus_P4 R_str1 RA1 (-m)%r1),Minus_P1,Plus_P1 in H19;
    auto. rewrite H19,<-Plus_P3,Minus_P1,Plus_P1; auto. }
  assert (g[1] = 1').
  { assert (1 ∈ dom(g)).
    { rewrite H7; apply AxiomII; split; eauto. }
    assert (g[(1 · 1)%r1] = (g[1] · g[1])%r2). { apply H14; auto. }
    assert (g[1] ∈ (R2 ~ [0'])).
    { apply MKT4'; split; auto. apply AxiomII; split; eauto.
      intro. apply MKT41 in H18; eauto. apply H11 in H16 as []; auto. }
    rewrite Mult_P1 in H17; auto. symmetry in H17.
    apply Mult_Co3 in H17; auto. rewrite Divide_P1 in H17; auto. }
  exists g. split; auto. split; auto.
Qed.

Lemma UniqueT5_Lemma8 : ∃ f, Function f
  /\ dom(f) = R1 /\ ran(f) ⊂ R2 /\ ran(f) <> [0']
  /\ (∀ m n, m ∈ dom(f) -> n ∈ dom(f) -> f[(m + n)%r1] = (f[m] + f[n])%r2)
  /\ (∀ m n, m ∈ dom(f) -> n ∈ dom(f) -> f[(m · n)%r1] = (f[m] · f[n])%r2).
Proof.
  destruct UniqueT5_Lemma7 as [f[H[H0[H1[H2[H3[]]]]]]].
  set (g := \{\ λ u v, u ∈ R1 /\ (((0 < u)%r1 /\ v = f[u])
    \/ (u = 0 /\ v = 0') \/ ((u < 0)%r1 /\ v = (-f[(-u)%r1])%r2)) \}\).
  assert (∀ m, m ∈ R1 -> (0 < m)%r1 -> f[m] ∈ R2) as Hf.
  { intros. apply H1,(@ Property_ran m),Property_Value; auto.
    rewrite H0. apply AxiomII; split; eauto. }
  assert (∀ m, m ∈ R1 -> (m < 0)%r1 -> (0 < -m)%r1) as Hb.
  { intros. apply (@OrderPM_Co1 R_str1 RA1 _ _ (-m)%r1) in H7; auto.
    rewrite Minus_P1,Plus_P4,Plus_P1 in H7; auto. }
  assert (Function g).
  { split; unfold Relation; intros.
    apply AxiomII in H6 as [_[x[y[]]]]; eauto.
    apply AxiomII' in H6 as [_[H6[[]|[[]|[]]]]],
    H7 as [_[H7[[]|[[]|[]]]]]; try rewrite H9,H11; auto;
    try (rewrite H8 in H10; destruct H10; contradiction);
    try (destruct H8,H10; elim H12; apply (@Leq_P2 R_str1 RA1); auto).
    destruct H8. elim H12. auto. rewrite H10 in *. destruct H8. tauto. }
  assert (dom(g) = R1).
  { apply AxiomI; split; intros.
    apply Property_Value,AxiomII' in H7 as [_[]]; auto.
    pose proof H7. apply (@Order_Co1 R_str1 RA1 0) in H8 as [H8|[]];
    auto; apply AxiomII; split; eauto.
    - exists f[z]. apply AxiomII'; split; auto. apply MKT49a; eauto.
    - exists (-f[(-z)%r1])%r2. apply AxiomII'; split; auto.
      apply MKT49a; eauto. exists R2. apply Plus_neg1a,Hf; auto.
    - exists 0'. apply AxiomII'; split; auto. apply MKT49a; eauto. }
  assert (ran(g) ⊂ R2).
  { unfold Included; intros. apply Einr in H8 as [x[]]; auto.
    apply Property_Value,AxiomII' in H8 as [_[H8[[]|[[]|[]]]]]; auto;
    rewrite H9,H11; auto. }
  assert (g[0] = 0').
  { pose proof (@zero_in_R R_str1 RA1). replace R with R1 in H9; auto.
    rewrite <-H7 in H9. apply Property_Value,AxiomII' in H9
    as [_[H9[[]|[[]|[]]]]]; auto; destruct H10; contradiction. }
  assert (∀ m, m ∈ R1 -> (0 < m)%r1 -> g[m] = f[m]).
  { intros. rewrite <-H7 in H10.
    apply Property_Value,AxiomII' in H10 as [_[H10[[]|[[]|[]]]]]; auto.
    rewrite H12 in H11. destruct H11; contradiction.
    destruct H11,H12. elim H14. apply (@Leq_P2 R_str1 RA1); auto. }
  assert (∀ m, m ∈ R1 -> (m < 0)%r1 -> g[m] = (-f[(-m)%r1])%r2).
  { intros. rewrite <-H7 in H11.
    apply Property_Value,AxiomII' in H11 as [_[H11[[]|[[]|[]]]]]; auto.
    destruct H12,H13. elim H15. apply (@Leq_P2 R_str1 RA1); auto.
    rewrite H13 in H12. destruct H12; contradiction. }
  assert (g[1] = 1'). { rewrite H10; auto. }
  assert (ran(g) <> [0']).
  { assert (1' ∈ ran(g)).
    { rewrite <-H12. apply (@ Property_ran 1),Property_Value; auto.
      rewrite H7; auto. }
    intro. rewrite H14 in H13. apply MKT41 in H13; eauto.
    destruct (@OrderPM_Co9 R_str2 RA2); auto. }
  assert (∀ m, m ∈ R1 -> g[m] ∈ R2) as Hg.
  { intros. apply H8,(@ Property_ran m),Property_Value; auto.
    rewrite H7; auto. }
  assert (∀ m n, m ∈ R1 -> n ∈ R1 -> (0 < m)%r1 -> (n < 0)%r1
    -> g[(m + n)%r1] = (g[m] + g[n])%r2 /\ g[(m · n)%r1] = (g[m] · g[n])%r2).
  { intros. rewrite (H10 m),(H11 n); auto.
    assert (m ∈ dom(f) /\ (-n)%r1 ∈ dom(f)) as [].
    { rewrite H0. split; apply AxiomII; split; eauto. }
    pose proof (@zero_in_R R_str1 RA1).
    apply (@Order_Co1 R_str1 RA1 (m + n)%r1) in H20
    as [H20|[]]; auto.
    - rewrite H11; auto. split. rewrite (@PlusMult_Co3 R_str1 RA1),
      Mult_P4,Mult_P5,Mult_P4,<-(PlusMult_Co3 R_str1 RA1),Mult_P4,
      <-(PlusMult_Co3 R_str1 RA1),Plus_P4,H4,(@PlusMult_Co3 R_str2 RA2),
      (@Mult_P4 R_str2 RA2),(@Mult_P5 R_str2 RA2),(@Mult_P4 R_str2 RA2),
      <-(@PlusMult_Co3 R_str2 RA2),Mult_P4,PlusMult_Co4,Plus_P4; auto.
      apply (@OrderPM_Co1 R_str1 RA1 _ _ (-n)%r1) in H20; auto.
      rewrite <-Plus_P3,Minus_P1,Plus_P1,Plus_P4,Plus_P1 in H20; auto.
      rewrite H11; auto. rewrite (@PlusMult_Co3 R_str1 RA1),Mult_P3,
      (@Mult_P4 R_str1 RA1 _ m),<-Mult_P3,<-(@PlusMult_Co3 R_str1 RA1),H3; auto.
      rewrite (@PlusMult_Co3 R_str2 RA2),(@Mult_P3 R_str2 RA2),
      (@Mult_P4 R_str2 RA2 _ f[m]),<-Mult_P3,<-(@PlusMult_Co3 R_str2 RA2); auto.
      rewrite Mult_P4; auto. apply OrderPM_Co6; auto.
    - rewrite H10; auto. split. pattern n at 1.
      rewrite <-(@PlusMult_Co4 R_str1 RA1 n),<-(@PlusMult_Co3 R_str1 RA1),H4;
      auto. apply (@OrderPM_Co1 R_str1 RA1 _ _ (-n)%r1) in H20; auto.
      rewrite <-Plus_P3,Minus_P1,Plus_P4,Plus_P1,Plus_P1 in H20; auto.
      rewrite H11,(@PlusMult_Co3 R_str1 RA1),Mult_P3,(@Mult_P4 R_str1 RA1 _ m),
      <-Mult_P3,<-(@PlusMult_Co3 R_str1 RA1),H3,(@PlusMult_Co3 R_str2 RA2),
      Mult_P3,(@Mult_P4 R_str2 RA2 _ f[m]),<-(@Mult_P3 R_str2 RA2),
      <-(@PlusMult_Co3 R_str2 RA2); auto.
      rewrite Mult_P4; auto. apply OrderPM_Co6; auto.
    - rewrite H20. rewrite Plus_P4 in H20; auto.
      apply Plus_Co3 in H20; auto.
      rewrite Plus_P4,Plus_P1 in H20; auto. split.
      replace R with R1 in H20; auto.
      rewrite <-H20,(@Minus_P1 R_str2 RA2); auto.
      rewrite H11,(@PlusMult_Co3 R_str1 RA1),Mult_P3,(@Mult_P4 R_str1 RA1 _ m),
      <-Mult_P3,<-(@PlusMult_Co3 R_str1 RA1),<-H20,H3,(@PlusMult_Co3 R_str2 RA2),
      (@Mult_P3 R_str2 RA2),<-(@PlusMult_Co3 R_str2 RA2),(@Mult_P4 R_str2 RA2);
      auto. replace R with R2; auto. replace R with R1 in H20; auto.
      rewrite <-H20; auto. rewrite Mult_P4; auto. apply OrderPM_Co6; auto. }
  assert (∀ m n, m ∈ R1 -> n ∈ R1 -> (m < 0)%r1 -> (n < 0)%r1
    -> g[(m + n)%r1] = (g[m] + g[n])%r2 /\ g[(m · n)%r1] = (g[m] · g[n])%r2).
  { intros. rewrite (H11 m),(H11 n); auto.
    assert ((-m)%r1 ∈ dom(f) /\ (-n)%r1 ∈ dom(f)) as [].
    { rewrite H0. split; apply AxiomII; split; eauto. }
    assert (m + n < 0 + 0)%r1.
    { apply OrderPM_Co4; auto. destruct H17; auto. }
    rewrite Plus_P1 in H21; auto. split.
    rewrite H11,(@PlusMult_Co3 R_str1 RA1),Mult_P4,Mult_P5,Mult_P4,
    <-(@PlusMult_Co3 R_str1 RA1),Mult_P4,<-(@PlusMult_Co3 R_str1 RA1),H2,
    (@PlusMult_Co3 R_str2 RA2),(@Mult_P4 R_str2 RA2),(@Mult_P5 R_str2 RA2),
    (@Mult_P4 R_str2 RA2),<-(@PlusMult_Co3 R_str2 RA2),(@Mult_P4 R_str2 RA2),
    <-(@PlusMult_Co3 R_str2 RA2); auto.
    assert (m · n = (-m) · (-n))%r1.
    { replace (-m)%r1 with ((-(1))·m)%r1. replace (-n)%r1 with ((-(1))·n)%r1.
      rewrite (@Mult_P3 R_str1 RA1),(@Mult_P4 R_str1 RA1 (-(1))%r1),
      <-(@Mult_P3 R_str1 RA1 m),PlusMult_Co5,Mult_P1,Mult_P1; auto.
      rewrite <-(@PlusMult_Co3 R_str1 RA1); auto.
      rewrite <-(@PlusMult_Co3 R_str1 RA1); auto. }
    rewrite H22. replace (-f[(-m)%r1])%r2 with ((-1')·f[(-m)%r1])%r2.
    replace (-f[(-n)%r1])%r2 with ((-1')·f[(-n)%r1])%r2.
    rewrite H10,H3,Mult_P3,(@Mult_P4 R_str2 RA2 (-1')%r2),
    <-(@Mult_P3 R_str2 RA2 f[(-m)%r1]),(@PlusMult_Co5 R_str2 RA2),
    (@Mult_P1 R_str2 RA2),(@Mult_P1 R_str2 RA2); auto. rewrite <-H22.
    apply OrderPM_Co5; auto. rewrite <-(@PlusMult_Co3 R_str2 RA2); auto.
    rewrite <-(@PlusMult_Co3 R_str2 RA2); auto. }
  assert (∀ m n, m ∈ dom(g) -> n ∈ dom(g) -> g[(m + n)%r1] = (g[m] + g[n])%r2).
  { intros.
    apply Property_Value,AxiomII' in H16
    as [_[H16[[]|[[]|[]]]]],H17 as [_[H17[[]|[[]|[]]]]]; auto.
    rewrite H10. rewrite H19, H21; apply H2;
    rewrite H0; apply AxiomII; split; eauto. apply Plus_close; auto.
    replace 0 with (0 + 0)%r1. apply OrderPM_Co4; auto.
    destruct H18; auto. rewrite Plus_P1; auto.
    rewrite H20,Plus_P1,H9,(@Plus_P1 R_str2 RA2); auto. apply H14; auto.
    rewrite H18,Plus_P4,Plus_P1,H9,(@Plus_P4 R_str2 RA2),(@Plus_P1 R_str2 RA2);
    auto. rewrite H19,H21,H18,H20,Plus_P1,H9,(@Plus_P1 R_str2 RA2); auto.
    rewrite H18,Plus_P4,Plus_P1,H9,(@Plus_P4 R_str2 RA2),(@Plus_P1 R_str2 RA2);
    auto. rewrite Plus_P4,(@Plus_P4 R_str2 RA2); auto. apply H14; auto.
    rewrite H20,Plus_P1,H9,(@Plus_P1 R_str2 RA2); auto. apply H15; auto. }
  assert (∀ m n, m ∈ dom(g) -> n ∈ dom(g) -> g[(m · n)%r1] = (g[m] · g[n])%r2).
  { clear H16. intros. apply Property_Value,AxiomII' in H16
    as [_[H16[[]|[[]|[]]]]],H17 as [_[H17[[]|[[]|[]]]]]; auto.
    rewrite H10,H19,H21,H3; try (rewrite H0; apply AxiomII; split);
    eauto. apply OrderPM_Co5; auto.
    rewrite H20,PlusMult_Co1,H9,(@PlusMult_Co1 R_str2 RA2); auto.
    apply H14; auto. rewrite H19,H18,Mult_P4,(@Mult_P4 R_str2 RA2),
    PlusMult_Co1,(@PlusMult_Co1 R_str2 RA2); auto.
    rewrite H20,PlusMult_Co1,H9,(@PlusMult_Co1 R_str2 RA2); auto.
    rewrite H18,Mult_P4,PlusMult_Co1,H9,(@Mult_P4 R_str2 RA2),
    (@PlusMult_Co1 R_str2 RA2); auto.
    rewrite Mult_P4,(@Mult_P4 R_str2 RA2); auto. apply H14; auto.
    rewrite H20,PlusMult_Co1,H9,(@PlusMult_Co1 R_str2 RA2); auto.
    apply H15; auto. }
  exists g. split; auto.
Qed.

Definition Reals_Isomorphism := ∃ f, Function1_1 f /\ dom(f) = R1 /\ ran(f) = R2
  /\ (∀ x y, x ∈ R1 -> y ∈ R1 -> f[(x + y)%r1] = (f[x] + f[y])%r2)
  /\ (∀ x y, x ∈ R1 -> y ∈ R1 -> f[(x · y)%r1] = (f[x] · f[y])%r2)
  /\ (∀ x y, x ∈ R1 -> y ∈ R1 -> (x ≤ y)%r1 <-> (f[x] ≤ f[y])%r2).

Theorem UniqueT5 : Reals_Isomorphism.
Proof.
  assert (H:True) by auto. unfold Reals_Isomorphism.
  destruct UniqueT5_Lemma8 as [f[H0[H1[H2[H3[]]]]]].
  pose proof H0. apply UniqueT4 in H6 as [H6[H7[]]]; auto;
  [ |intros; split; [apply H4|apply H5]; rewrite H1; auto].
  exists f. split; auto. repeat split; intros; auto;
  [apply H4|apply H5| ]; try rewrite H1; auto.
  assert (∀ r, r ∈ R1 -> f[r] ∈ R2).
  { intros. rewrite <-H1 in H13.
    apply Property_Value,Property_ran in H13; auto. }
  intros. pose proof H10.
  apply (@Order_Co1 R_str1 RA1 y) in H14 as [H14|]; auto.
  assert (y ≤ x)%r1. { destruct H14; auto. }
  apply H9 in H15; auto. assert (f[x] = f[y]). { apply Leq_P2; auto. }
  apply f11inj in H16; try rewrite H1; auto. rewrite H16 in H14.
  destruct H14; contradiction. destruct H6; auto.
  destruct H14; [destruct H14|rewrite H14]; auto.
  apply Leq_P1; auto.
Qed.


End real_numbers_uniqueness.

