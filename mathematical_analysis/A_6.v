(** A_6 *)
(* 微分中值定理及其应用 *)

(* 读入文件 *)
Require Export A_5.


(* 6.1 拉格朗日定理和函数的单调性 *)

(* 罗尔定理 *)
Theorem Theorem6_1 : ∀ f (a b : R), a < b -> ContinuousClose f a b
  -> (∀ x, a < x < b -> Derivable f x) -> f[a] = f[b]
  -> ∃ ξ, a < ξ < b /\ Derivative f ξ 0.
Proof.
  intros f a b H0 H1 H2 H3. generalize (Theorem4_6 f a b H0 H1).
  intros [[M[H4[H5[ξ1[H6 H10]]]]] [m[H7[H8[ξ2[H9 H11]]]]]].
  assert (H12 : m <= M).
  { assert (I1 : a ∈ \[a, b\]). { apply Classifier1. lra. }
    apply H5 in I1 as I2. apply H8 in I1 as I3. lra. }
  destruct H12 as [H12 | H12].
  - assert (I1 : a < ξ1 < b \/ a < ξ2 < b).
    { apply NNPP. intro J1. apply not_and_or in J1 as [J1 J2].
      applyClassifier1 H6. applyClassifier1 H9.
      assert (J3 : ξ1 = a \/ ξ1 = b). lra.
      assert (J4 : ξ2 = a \/ ξ2 = b). lra.
      destruct J3 as [J3 | J3]; rewrite J3 in *;
      destruct J4 as [J4 | J4]; rewrite J4 in *; lra. } destruct I1 as [I1 | I1].
    + exists ξ1. split; auto. apply Theorem5_3.
      * apply H2; assumption.
      * left. unfold LocalMax. split; try apply H1.
        assert (J1 : ∃ δ, δ > 0 /\ δ < ξ1 - a /\ δ < b - ξ1).
        { destruct (Rlt_or_le (ξ1 - a) (b - ξ1)) as [J1 | J1].
          - exists ((ξ1 - a)/2). repeat split; lra.
          - exists ((b - ξ1)/2). repeat split; lra. }
        destruct J1 as [δ[J1[J2 J3]]]. exists δ. repeat split; auto.
        -- intros x K1. applyClassifier1 K1. apply H4. apply Classifier1. 
           apply Abs_R in K1. lra.
        -- intros x K1. applyClassifier1 K1. apply Abs_R in K1. rewrite H10. 
           apply H5. apply Classifier1. lra.
    + exists ξ2. split; auto. apply Theorem5_3.
      * apply H2; assumption.
      * right. unfold LocalMin. split; try apply H1.
        assert (J1 : ∃ δ, δ > 0 /\ δ < ξ2 - a /\ δ < b - ξ2).
        { destruct (Rlt_or_le (ξ2 - a) (b - ξ2)) as [J1 | J1].
          - exists ((ξ2 - a)/2). repeat split; lra.
          - exists ((b - ξ2)/2). repeat split; lra. } 
        destruct J1 as [δ[J1[J2 J3]]]. exists δ. repeat split; auto.
        -- intros x K1. applyClassifier1 K1. apply H4. apply Classifier1. 
           apply Abs_R in K1. lra.
        -- intros x K1. applyClassifier1 K1. apply Abs_R in K1. rewrite H11. 
           apply H8. apply Classifier1. lra.
  - assert (I1 : ∀ x, x ∈ \[ a, b \] -> f[x] = m).
    { intros x J1. apply H5 in J1 as J2. apply H8 in J1 as J3. lra. }
    exists ((a + b)/2). split; try lra. apply Theorem5_3.
    + apply H2; lra.
    + left. unfold LocalMax. split; try apply H1. exists ((b - a)/2). 
      repeat split; try lra.
      * intros x J1. applyClassifier1 J1. apply H4. apply Abs_R in J1. 
        apply Classifier1. lra.
      * intros x J1. applyClassifier1 J1. apply Abs_R in J1. rewrite I1. rewrite I1. 
        lra. apply Classifier1. lra. apply Classifier1. lra.
Qed.

(* 拉格朗日中值定理 *)
Theorem Theorem6_2 : ∀ f (a b : R), a < b -> ContinuousClose f a b
  -> (∀ x, a < x < b -> Derivable f x)
  -> ∃ ξ, a < ξ < b /\ Derivative f ξ ((f[b] - f[a])/(b - a)).
Proof.
  intros f a b H0 H1 H2.
  assert (H3 : ∃ F, F = \{\ λ x y, y = f[x] - f[a]
    - (f[b] - f[a])/(b - a)*(x - a) \}\).
  { exists \{\ λ x y, y = f[x] - f[a] - (f[b] - f[a])/(b - a)*(x - a) \}\; 
    reflexivity. }
  destruct H3 as [F H3].
  assert (H4 : Function F).
  { rewrite H3. unfold Function. intros x y z I1 I2. applyClassifier2 I1. 
    applyClassifier2 I2. rewrite I2. assumption. }
  assert (H5 : ∀ x, F[x] = f[x] - f[a] - (f[b] - f[a])/(b - a)*(x - a)).
  { intro x. apply f_x_T; auto. rewrite H3. apply Classifier2. reflexivity. }
  destruct H1 as [H1[H6 H7]]. unfold ContinuousOpen in H1.
  assert (H8 : ContinuousClose F a b).
  { unfold ContinuousClose. split; [idtac | split].
    - unfold ContinuousOpen. intros x I1. unfold Continuous. split.
      + apply Classifier1. exists (f[x] - f[a] - (f[b] - f[a])/(b - a)*(x - a)).
        rewrite H3. apply Classifier2. reflexivity.
      + unfold limit. split; auto. apply H1 in I1 as I2. unfold Continuous in I2. 
        destruct I2 as [I2 I3]. unfold limit in I3. 
        destruct I3 as [I3[δ'[I4[I5 I6]]]]. exists δ'. split; auto. split.
        * intros x0 J1. apply Classifier1. 
          exists (f[x0] - f[a] - (f[b] - f[a])/(b - a)*(x0 - a)). rewrite H3. 
          apply Classifier2. reflexivity.
        * intros ε J1. assert (J2 : ε/2 > 0). lra. apply I6 in J2 as J3.
          destruct J3 as [δ1[J3 J4]].
          assert (J5 : ∃ δ2, 0 < δ2 /\ ∀ x0 : R,0 < ∣(x0 - x)∣ < δ2 
            -> ∣((f[b] - f[a])/(b - a) * (x0 - x))∣ < ε/2).
          { destruct classic with (P := (f[b] - f[a] = 0)) as [K1 | K1].
            - exists 1. split; try lra. intros x0 K2. rewrite K1. unfold Rdiv. 
              rewrite Rmult_0_l. rewrite Rmult_0_l. rewrite Abs_ge; try lra.
            - exists ((ε/2 * ((b - a)/∣(f[b] - f[a])∣))). split.
              + apply Rmult_lt_0_compat; auto. apply Rdiv_lt_0_compat; try lra.
                apply Abs_not_eq_0; auto.
              + intros x0 K2. rewrite Abs_mult. rewrite Abs_div; try lra.
                rewrite (Abs_gt (b - a)); try lra. destruct K2 as [K2 K3].
                assert (K4 : 0 < ∣(f[b] - f[a])∣/(b - a)).
                { apply Rdiv_lt_0_compat; try lra. apply Abs_not_eq_0; auto. }
                apply Rmult_lt_compat_r with (r := ∣(f[b] - f[a])∣/(b - a)) 
                in K3; auto.
                assert (K5 : ε/2 * ((b - a)/∣(f[b] - f[a])∣) *
                  (∣(f[b] - f[a])∣/(b - a)) = ε/2).
                { apply Abs_not_eq_0 in K1. field; split; lra. }
                rewrite K5 in K3. clear K5.
                assert (K5 : ∣(x0 - x)∣ * (∣(f[b] - f[a])∣/(b - a))
                  = ∣(f[b] - f[a])∣/(b - a) * ∣(x0 - x)∣). { field. lra. }
                rewrite K5 in K3. assumption. }
          destruct J5 as [δ2[J5 J6]].
          assert (J7 : ∃ δ, 0 < δ /\ δ < δ1 /\ δ < δ2).
          { destruct (Rlt_or_le δ1 δ2) as [K1 | K1]. exists (δ1 / 2). split; lra.
            exists (δ2 / 2). split; lra. } destruct J7 as [δ[J7[J8 J9]]].
          exists δ. split; try lra. intros x0 J10. rewrite H5. rewrite H5.
          assert (J11 : f[x0] - f[a] - (f[b] - f[a])/(b - a) * (x0 - a)
              - (f[x] - f[a] - (f[b] - f[a])/(b - a) * (x - a))
            = f[x0] - f[x] - (f[b] - f[a])/(b - a) * (x0 - x)). { field. lra. }
          rewrite J11. clear J11.
          generalize (Abs_minus_le (f[x0]-f[x]) ((f[b]-f[a])/(b-a)*(x0-x))).
          intros J11. assert (J12 : 0 < ∣(x0 - x)∣ < δ1). lra.
          apply J4 in J12. assert (J13 : 0 < ∣(x0 - x)∣ < δ2). lra. 
          apply J6 in J13. lra.
    - unfold ContinuousRight. split.
      + apply Classifier1. exists (f[a] - f[a] - (f[b] - f[a])/(b - a)*(a - a)).
        rewrite H3. apply Classifier2. reflexivity.
      + unfold limit_pos. split; auto. unfold ContinuousRight in H6. 
        destruct H6 as [I2 I3]. unfold limit_pos in I3. 
        destruct I3 as [I3[δ'[I4[I5 I6]]]]. exists δ'. split; auto. split.
        * intros x0 J1. apply Classifier1. 
          exists (f[x0] - f[a] - (f[b] - f[a])/(b - a)*(x0 - a)).
          rewrite H3. apply Classifier2. reflexivity.
        * intros ε J1. assert (J2 : ε/2 > 0). lra. apply I6 in J2 as J3.
          destruct J3 as [δ1[J3 J4]].
          assert (J5 : ∃ δ2, 0 < δ2 /\ ∀ x0 : R,a < x0 < a + δ2 
            -> ∣((f[b] - f[a])/(b - a) * (x0 - a))∣ < ε/2).
          { destruct classic with (P := (f[b] - f[a] = 0)) as [K1 | K1].
            - exists 1. split; try lra. intros x0 K2. rewrite K1. unfold Rdiv. 
              rewrite Rmult_0_l. rewrite Rmult_0_l. rewrite Abs_ge; try lra.
            - exists ((ε/2 * ((b - a)/∣(f[b] - f[a])∣))). split.
              + apply Rmult_lt_0_compat; auto. apply Rdiv_lt_0_compat; try lra.
                apply Abs_not_eq_0; auto.
              + intros x0 K2. rewrite Abs_mult. rewrite Abs_div; try lra.
                rewrite (Abs_gt (b - a)); try lra. destruct K2 as [K2 K3].
                assert (K4 : 0 < ∣(f[b] - f[a])∣/(b - a)).
                { apply Rdiv_lt_0_compat; try lra. apply Abs_not_eq_0; auto. }
                assert (K6 : x0 - a < ε/2 * ((b - a)/∣(f[b] - f[a])∣)). lra.
                apply Rmult_lt_compat_r with (r := ∣(f[b]-f[a])∣/(b-a)) in K6; 
                auto.
                assert (K5 : ε/2 * ((b - a)/∣(f[b] - f[a])∣)
                  * (∣(f[b] - f[a])∣/(b - a)) = ε/2).
                { apply Abs_not_eq_0 in K1. field; split; lra. }
                rewrite K5 in K6. clear K5. rewrite (Abs_gt (x0 - a)); lra. }
          destruct J5 as [δ2[J5 J6]].
          assert (J7 : ∃ δ, 0 < δ /\ δ < δ1 /\ δ < δ2).
          { destruct (Rlt_or_le δ1 δ2) as [K1 | K1].
            - exists (δ1 / 2). split; lra.
            - exists (δ2 / 2). split; lra. } destruct J7 as [δ[J7[J8 J9]]].
          exists δ. split; try lra. intros x0 J10. rewrite H5. rewrite H5.
          assert (J11 : f[x0] - f[a] - (f[b] - f[a])/(b - a) * (x0 - a) 
              - (f[a] - f[a] - (f[b] - f[a])/(b - a) * (a - a))
            = f[x0] - f[a] - (f[b] - f[a])/(b - a) * (x0 - a)). { field. lra. }
          rewrite J11. clear J11.
          generalize (Abs_minus_le (f[x0]-f[a])((f[b]-f[a])/(b-a)*(x0-a))).
          intros J11. assert (J12 : a < x0 < a + δ1). lra. apply J4 in J12. 
          assert (J13 : a < x0 < a + δ2). lra. apply J6 in J13. lra.
    - unfold ContinuousLeft. split.
      + apply Classifier1. exists (f[b] - f[a] - (f[b] - f[a])/(b - a)*(b - a)).
        rewrite H3. apply Classifier2. reflexivity.
      + unfold limit_neg. split; auto. unfold ContinuousLeft in H7. 
        destruct H7 as [I2 I3]. unfold limit_neg in I3. 
        destruct I3 as [I3[δ'[I4[I5 I6]]]]. exists δ'. split; auto. split.
        * intros x0 J1. apply Classifier1. 
          exists (f[x0] - f[a] - (f[b] - f[a])/(b - a)*(x0 - a)). rewrite H3.
          apply Classifier2. reflexivity.
        * intros ε J1. assert (J2 : ε/2 > 0). lra. apply I6 in J2 as J3.
          destruct J3 as [δ1[J3 J4]].
          assert (J5 : ∃ δ2, 0 < δ2 /\ ∀ x0, b - δ2 < x0 < b 
            -> ∣((f[b] - f[a])/(b - a) * (x0 - b))∣ < ε/2).
          { destruct classic with (P := (f[b] - f[a] = 0)) as [K1 | K1].
            - exists 1. split; try lra. intros x0 K2. rewrite K1. unfold Rdiv.
              rewrite Rmult_0_l. rewrite Rmult_0_l. rewrite Abs_ge; try lra.
            - exists ((ε/2 * ((b - a)/∣(f[b] - f[a])∣))). split.
              + apply Rmult_lt_0_compat; auto. apply Rdiv_lt_0_compat; try lra.
                apply Abs_not_eq_0; auto.
              + intros x0 K2. rewrite Abs_mult. rewrite Abs_div; try lra.
                rewrite (Abs_gt (b - a)); try lra. destruct K2 as [K2 K3].
                assert (K4 : 0 < ∣(f[b] - f[a])∣/(b - a)).
                { apply Rdiv_lt_0_compat; try lra. apply Abs_not_eq_0; auto. }
                assert (K6 : b - x0 < ε/2 * ((b - a)/∣(f[b] - f[a])∣)). lra.
                apply Rmult_lt_compat_r with (r := ∣(f[b]-f[a])∣/(b-a)) in K6;
                auto.
                assert (K5 : ε/2 * ((b - a)/∣(f[b] - f[a])∣) 
                  * (∣(f[b] - f[a])∣/(b - a)) = ε/2).
                { apply Abs_not_eq_0 in K1. field; split; lra. } 
                rewrite K5 in K6. clear K5. rewrite (Abs_lt (x0 - b)); lra. }
          destruct J5 as [δ2[J5 J6]].
          assert (J7 : ∃ δ, 0 < δ /\ δ < δ1 /\ δ < δ2).
          { destruct (Rlt_or_le δ1 δ2) as [K1 | K1].
            - exists (δ1/2). split; lra.
            - exists (δ2/2). split; lra. } destruct J7 as [δ[J7[J8 J9]]].
          exists δ. split; try lra. intros x0 J10. rewrite H5. rewrite H5.
          assert (J11 : f[x0] - f[a] - (f[b] - f[a])/(b - a) * (x0 - a) 
              - (f[b] - f[a] - (f[b] - f[a])/(b - a) * (b - a))
            = f[x0] - f[b] - (f[b] - f[a])/(b - a) * (x0 - b)). { field. lra. }
          rewrite J11. clear J11.
          generalize (Abs_minus_le (f[x0]-f[b])((f[b]-f[a])/(b-a)*(x0-b))).
          intros J11. assert (J12 : b - δ1 < x0 < b). lra. apply J4 in J12. 
          assert (J13 : b - δ2 < x0 < b). lra. apply J6 in J13. lra. }
  assert (H9 : ∀ x, a < x < b -> Derivable F x).
  { intros x I1. apply H2 in I1 as I2. destruct I2 as [y'[I2[[δ'[I3 I4]]I5]]].
    exists (y' - (f[b] - f[a])/(b - a)). split; auto. split.
    - exists δ'. split; auto. intros x0 J1. apply Classifier1. rewrite H3.
      exists (f[x0] - f[a] - (f[b] - f[a])/(b - a) * (x0 - a)). apply Classifier2.
      reflexivity.
    - unfold limit. destruct I5 as [I5[δ0'[I6[I7 I8]]]]. split.
      + unfold Function. intros x0 y0 z0 J1 J2. applyClassifier2 J1;
        applyClassifier2 J2. rewrite J2. assumption.
      + exists δ0'. split; auto. split.
        * intros x0 J1. apply Classifier1. exists ((F[x0] - F[x])/(x0 - x)).
          apply Classifier2. reflexivity.
        * intros ε J1. apply I8 in J1 as J2. destruct J2 as [δ[J2 J3]]. 
          exists δ. split; auto. intros x0 J4. apply J3 in J4 as J5.
          assert (J6 : \{\ λ x0 y, y = (f[x0] - f[x])/(x0 - x) \}\ [x0]
            = (f[x0] - f[x])/(x0 - x)).
          { apply f_x_T.
            - intros x1 y1 z1 K1 K2. applyClassifier2 K1; applyClassifier2 K2.
              rewrite K2. assumption.
            - apply Classifier2. reflexivity. }
          rewrite J6 in J5. clear J6.
          assert (J6 : \{\ λ x1 y, y = (F[x1] - F[x])/(x1 - x) \}\ [x0]
            = (F[x0] - F[x])/(x0 - x)).
          { apply f_x_T.
            - intros x1 y1 z1 K1 K2. applyClassifier2 K1; applyClassifier2 K2.
              rewrite K2. assumption.
            - apply Classifier2. reflexivity. }
          rewrite J6. clear J6. rewrite H5. rewrite H5.
          assert (J6 : (f[x0] - f[a] - (f[b] - f[a])/(b - a) * (x0 - a)
            - (f[x] - f[a] - (f[b] - f[a])/(b - a) * (x - a)))/ (x0 - x)
            - (y' - (f[b] - f[a])/(b - a))
          = (f[x0] - f[x])/(x0 - x) - y').
          { field. destruct J4 as [J4 K1]. split; try lra. intro K2.
            rewrite K2 in J4. rewrite Abs_ge in J4; lra. }
          rewrite J6. clear J6. assumption. }
  assert (H10 : F[a] = F[b]).
  { rewrite H5; rewrite H5. field. lra. }
  generalize (Theorem6_1 F a b H0 H8 H9 H10). intros [ξ[H11 H12]]. exists ξ.
  split; auto. apply H2 in H11 as H13. destruct H13 as [f' H13].
  assert (H14 : Derivative F ξ (f' - (f[b] - f[a])/(b - a))).
  { split; auto. split.
    - exists 1. split; try lra. intros x0 I1. rewrite H3. apply Classifier1.
      exists (f[x0] - f[a] - (f[b] - f[a])/(b - a) * (x0 - a)). apply Classifier2.
      reflexivity.
    - unfold limit. destruct H13 as [H13[[δ'[I1 I2]]I3]].
      destruct I3 as [I3[δ0'[I4[I5 I6]]]]. split.
      + intros x1 y1 z1 J1 J2. applyClassifier2 J1; applyClassifier2 J2. rewrite J2. 
        assumption.
      + exists δ0'. repeat split; auto.
        * intros x0 J1. apply Classifier1. exists ((F[x0] - F[ξ])/(x0 - ξ)).
          apply Classifier2. reflexivity.
        * intros ε J1. apply I6 in J1 as J2. destruct J2 as [δ[J2 J3]].
          exists δ. split; auto. intros x J4. apply J3 in J4 as J5.
          assert (J6 : \{\ λ x y, y = (f[x] - f[ξ]) / (x - ξ) \}\ [x]
            = (f[x] - f[ξ])/(x - ξ)).
          { apply f_x_T.
            - intros x1 y1 z1 K1 K2. applyClassifier2 K1; applyClassifier2 K2.
              rewrite K2. assumption.
            - apply Classifier2. reflexivity. }
          rewrite J6 in J5. clear J6.
          assert (J6 : \{\ λ x y, y = (F[x] - F[ξ]) / (x - ξ) \}\ [x]
            = (F[x] - F[ξ]) / (x - ξ)).
          { apply f_x_T.
            - intros x1 y1 z1 K1 K2. applyClassifier2 K1; applyClassifier2 K2.
              rewrite K2. assumption.
            - apply Classifier2. reflexivity. }
          rewrite J6. clear J6.
          assert (J6 : (F[x] - F[ξ])/(x - ξ) - (f' - (f[b] - f[a])/(b - a))
            = (f[x] - f[ξ])/(x - ξ) - f').
          { rewrite H5. rewrite H5. field. destruct J4 as [J4 K1]. 
            apply Abs_not_eq_0 in J4. split; lra. } rewrite J6. assumption. }
  generalize (DerivativeUnique F ξ 0 (f' - (f[b] - f[a])/(b - a)) H12 H14). 
  intro H15. assert (H16 : f' = (f[b] - f[a])/(b - a)). lra. rewrite <- H16. 
  assumption.
Qed.

Corollary Corollary6_2a : ∀ f a b, a < b -> (∀ x, a < x < b -> Derivative f x 0)
  -> (∃ c, ∀ x, a < x < b -> f[x] = c).
Proof.
  intros. assert (∀ x1 x2, a < x1 < b -> a < x2 < b -> x1 < x2 -> f[x1] = f[x2]).
  { intros. assert (∀ x, x1 < x < x2 -> Derivable f x).
    { intros. exists 0. apply H0. lra. }
    assert (ContinuousClose f x1 x2).
    { split. red; intros. apply Theorem5_1; auto.
      split; apply Theorem4_1,Theorem5_1; exists 0; auto. }
    apply Theorem6_2 in H5 as [x[]]; auto. assert (a < x < b) by lra.
    apply H0 in H7. apply (DerivativeUnique _ _ _ 0) in H6; auto.
    apply Rmult_integral in H6 as []. lra. assert (x2 - x1 <> 0) by lra.
    apply Rinv_neq_0_compat in H8. contradiction. }
  assert (∀ x1 x2, a < x1 < b -> a < x2 < b -> f[x1] = f[x2]).
  { intros. destruct (Rtotal_order x1 x2) as [H4|[]]; auto. rewrite H4; auto.
    symmetry; auto. }
  exists f[(a + b)/2]. intros. apply H2; auto. lra.
Qed.

Corollary Corollary6_2b : ∀ f g a b, a < b -> (∀ x, a < x < b -> Derivable f x)
  -> (∀ x, a < x < b -> Derivable g x) -> (∀ x, a < x < b -> f’[x] = g’[x])
  -> (∃ c, ∀ x, a < x < b -> f[x] = g[x] + c).
Proof.
  intros. assert (∀ x, a < x < b -> Derivative (f \- g) x 0).
  { intros. replace 0 with (f’[x] - g’[x]). apply Theorem5_4b; auto.
    apply H2 in H3; lra. }
  apply Corollary6_2a in H3 as [c]; auto. exists c. intros.
  assert (x ∈ dom[f] /\ x ∈ dom[g]) as [].
  { pose proof H4. apply H0 in H4 as [x0[_[[x1[]] _]]].
    apply H1 in H5 as [x2[_[[x3[]] _]]]. split; [apply H6|apply H7];
    apply Classifier1; rewrite Abs_ge; lra. }
  apply H3 in H4. rewrite Corollary_sub_fun_b in H4; auto. lra.
Qed.

Corollary Corollary6_2c : ∀ f x0,
  (∃ δ, 0 < δ /\ (∀ x, x ∈ U(x0; δ) -> Continuous f x)
    /\ (∀ x, x ∈ Uº(x0; δ) -> Derivable f x))
  -> (∃ A, limit (dN f 1) x0 A)
  -> Derivable f x0 /\ limit (dN f 1) x0 (f’[x0]).
Proof.
  intros. destruct H as [δ[H[]]]. destruct H0 as [A].
  pose proof H0. apply Theorem3_1 in H3 as [].
  assert (Function \{\ λ x y, y = (f[x] - f[x0])/(x - x0) \}\).
  { red; intros. applyClassifier2 H5. applyClassifier2 H6. subst; auto. }
  assert (∀ x, x ∈ Uº(x0; δ) -> (dN f 1)[x] = f’[x]).
  { intros. assert (x ∈ dom[dN f 1]).
    { apply Classifier1. apply H2 in H6 as []. exists x1. apply Classifier2; auto. }
    destruct H0. apply x_fx_T in H7; auto. applyClassifier2 H7.
    apply Corollary_DerivativeValue_a in H7; auto. }
  assert (limit \{\ λ x y, y = (f[x] - f[x0])/(x - x0) \}\ x0 A).
  { apply Theorem3_1; split; split; auto; exists δ; split; auto; split;
    unfold Contain; intros; try (apply Classifier1; exists ((f[z] - f[x0])/(z - x0));
    apply Classifier2; auto).
    - destruct H3 as [H3[δ1[H8[]]]]. apply H10 in H7 as [δ3[]].
      destruct (Examp1 δ δ3) as [δ4[H12[]]]; auto. lra. exists δ4. split. lra.
      intros. rewrite FunValue.
      assert (∃ ξ, x0 < ξ < x /\ Derivative f ξ ((f[x] - f[x0])/(x - x0))).
      { apply Theorem6_2. lra. split; [red; intros|split; apply Theorem4_1];
        apply H1,Classifier1; rewrite Abs_ge; lra. intros. apply H2,Classifier1.
        rewrite Abs_ge; lra. } destruct H16 as [ξ[]].
      apply Corollary_DerivativeValue_a in H17. assert (x0 < ξ < x0 + δ3) by lra.
      apply H11 in H18. rewrite <-H17,<-H6; auto. apply Classifier1.
      rewrite Abs_ge; lra.
    - destruct H4 as [H4[δ1[H8[]]]]. apply H10 in H7 as [δ3[]].
      destruct (Examp1 δ δ3) as [δ4[H12[]]]; auto. lra. exists δ4. split. lra.
      intros. rewrite FunValue.
      assert (∃ ξ, x < ξ < x0 /\ Derivative f ξ ((f[x0] - f[x])/(x0 - x))).
      { apply Theorem6_2. lra. split; [red; intros|split; apply Theorem4_1];
        apply H1,Classifier1; try (rewrite Abs_lt; lra). rewrite Abs_ge; lra.
        intros. apply H2,Classifier1. rewrite Abs_lt; lra. } destruct H16 as [ξ[]].
      apply Corollary_DerivativeValue_a in H17.
      assert (x0 - δ3 < ξ < x0) by lra. apply H11 in H18.
      replace ((f[x] - f[x0])/(x - x0)) with ((f[x0] - f[x])/(x0 - x)).
      rewrite <-H17,<-H6; auto. apply Classifier1. rewrite Abs_lt; lra.
      replace (f[x] - f[x0]) with (-(f[x0] - f[x])); [ |lra]. rewrite Rdiv_opp_l.
      replace (x - x0) with (-(x0 - x)); [ |lra].
      rewrite <-Rdiv_opp_r,Ropp_involutive. auto. }
  assert (Derivative f x0 A).
  { assert (x0 ∈ U(x0; δ)). { apply Classifier1. rewrite Abs_ge; lra. }
    apply H1 in H8 as [H8[H9[x[H10[]]]]]. split; auto. split; auto.
    exists x. split; auto. red; intros. applyClassifier1 H13.
    destruct (classic (z = x0)). rewrite H14; auto. apply H11.
    apply Classifier1. split; auto. apply Abs_not_eq_0. lra. }
  split. red; eauto. apply Corollary_DerivativeValue_a in H8. rewrite H8; auto.
Qed.

(* 函数在区间单调递增的充要条件 *)
Theorem Theorem6_3a : ∀ f a b, (a < b /\ \(a, b\) ⊂ dom[f] 
    /\ ∀ x, x ∈ \(a, b\) -> Derivable f x)
  -> (DIncreaseFun f (\( a, b\)) <-> (∀ x, x ∈ \(a, b\) -> f’[x] >= 0)). 
Proof.
  intros. destruct H as [H'[H H0]]. split; intros.
  - apply H0 in H2 as H2'. red in H2'. destruct H2' as [y']. 
    apply Corollary_DerivativeValue_a in H3 as H3'. rewrite <- H3' in H3. 
    red in H3. red in H1. destruct H1 as [H1[H4 H5]]. destruct H3 as [_[H6 H7]].
    red in H7. destruct H7 as [H7[δ[H8[H9 H10]]]]. 
    pose proof (Rbasic_fun.Rcase_abs (f’[x])). destruct H3. 
    + assert (∣(f’[x])∣ > 0). { apply Abs_not_eq_0; lra. }
      apply H10 in H3. destruct H3 as [δ0[H3 H11]].
      assert(∃δ', δ' = Rbasic_fun.Rmin (b-x) (x-a) /\ δ' > 0).
      { exists (Rbasic_fun.Rmin (b - x) (x - a)). split; auto.
        unfold Rbasic_fun.Rmin. applyClassifier1 H2; destruct Rle_dec; lra. }
      destruct H12 as [δ'[H12 H12']]. 
      assert(∃x1, 0 < ∣(x1 - x)∣ < δ0 /\ x1 ∈ \(a, b\)).
      { exists ((Rbasic_fun.Rmin δ' δ0)/2 + x). split. rewrite Abs_gt. 
        replace (Rbasic_fun.Rmin δ' δ0/2+x-x) with ((Rbasic_fun.Rmin δ' δ0)/2); 
        unfold Rbasic_fun.Rmin; destruct Rle_dec; lra. unfold Rbasic_fun.Rmin;
        destruct Rle_dec; lra. applyClassifier1 H2; destruct H2. 
        unfold Rbasic_fun.Rmin; destruct Rle_dec. rewrite H12. 
        unfold Rbasic_fun.Rmin; destruct Rle_dec; apply Classifier1; lra.
        apply Classifier1. apply Rnot_le_gt in n. split. lra. 
        unfold Rbasic_fun.Rmin in H12; destruct Rle_dec; lra. }
      destruct H13 as [x1[H13 H13']]. apply H11 in H13 as H13''. 
      assert(\{\ λ x0 y,y = (f[x0]-f[x])/(x0-x) \}\ [x1] = (f[x1]-f[x])/(x1-x)).
      { apply f_x_T; auto. apply Classifier2; auto. }
      rewrite H14 in H13''. clear H14.
      assert ((f[x1] - f[x])/(x1 - x) >= 0).
      { destruct H13. apply <- Abs_not_eq_0 in H13. apply Rdichotomy in H13. 
        destruct H13. apply Rminus_lt in H13.
        - apply (H5 x1 x) in H13'; auto. unfold Rdiv. apply Rmult_leq_le; auto. 
          split. lra. apply Rinv_lt_0_compat; lra.
        - apply Rminus_gt in H13. apply (H5 x x1) in H2; auto. unfold Rdiv. 
          apply Rmult_gre_gr. split. lra. apply Rinv_0_lt_compat; lra. } 
      assert(∣((f[x1]-f[x])/(x1-x)-f’[x])∣ = (f[x1]-f[x])/(x1-x)-f’[x]). 
      apply Abs_gt. lra. rewrite H15 in H13''. rewrite Abs_lt in H13''; auto. lra.
    + auto.
  - red. split.
    + assert (∃ x1, x1 ∈ \(a, b\)). 
      { exists ((b+a)/2). apply Classifier1. split; lra. }
      destruct H2 as [x1 H2]. apply H0 in H2. red in H2. destruct H2 as [y1 H2]. 
      red in H2. destruct H2 as [H2 [H3 H4]]. auto.
    + split; auto. intros.
      assert (ContinuousClose f x1 x2).
      { red. split.
        - red. intros.
          assert (x ∈ \(a, b\)).
          { apply Classifier1. applyClassifier1 H2. applyClassifier1 H3. destruct H2. 
            destruct H3. lra. }
          apply H0 in H6. apply Theorem5_1 in H6. auto.
        - split.
          + apply H0 in H2. apply Theorem5_1 in H2. apply Theorem4_1 in H2.
            destruct H2; auto.
          + apply H0 in H3. apply Theorem5_1 in H3. apply Theorem4_1 in H3.
            destruct H3; auto. }
      apply (Theorem6_2 f x1 x2) in H4; auto. destruct H4 as [ξ H4]. 
      destruct H4. apply Corollary_DerivativeValue_a in H6.
      assert (ξ ∈ \( a, b\)). apply Classifier1. destruct H4. applyClassifier1 H2. 
      applyClassifier1 H3. lra. apply H1 in H7. rewrite H6 in H7. unfold Rdiv in H7. 
      pose proof (Rle_or_lt f[x1] f[x2]). destruct H8. auto.
      assert (/(x2 - x1) > 0). 
      { assert ((x2-x1) > 0). lra. apply Rinv_0_lt_compat. auto. }
      assert ((f[x2] - f[x1]) < 0). lra.
      assert (f[x2] - f[x1] < 0 /\ /(x2 - x1) > 0). lra.
      apply (Rmult_le_gr (f[x2] - f[x1]) (/(x2 - x1))) in H11. lra. intros. 
      assert (x ∈ \( a, b\)). apply Classifier1. applyClassifier1 H2. applyClassifier1 H3. 
      destruct H2. destruct H3. destruct H6. lra. apply H0 in H7. auto.
Qed.

Theorem Theorem6_3b: ∀ f a b, (a < b /\ \(a, b\) ⊂ dom[f] /\ ∀ x, x ∈ \(a, b\) 
    -> Derivable f x)
  -> DDecreaseFun f (\(a, b\)) <-> (∀ x, x ∈ \(a, b\) -> f’[x] <= 0).
Proof.   
  - intros. destruct H as [H'[H H0]]. split; intros. 
    + apply H0 in H2 as H2'. red in H2'. destruct H2' as [y']. 
      apply Corollary_DerivativeValue_a in H3 as H3'. rewrite <- H3' in H3. 
      red in H3. red in H1. destruct H1 as [H1[H4 H5]]. destruct H3 as [_[H6 H7]].
      red in H7. destruct H7 as [H7[δ[H8[H9 H10]]]]. 
      pose proof (Rge_gt_dec 0 (f’[x])). destruct H3. lra. 
      assert (∣(f’[x])∣ > 0). { apply Abs_not_eq_0; lra. }
      apply H10 in H3. destruct H3 as [δ0[H3 H11]].
      assert(∃δ', δ' = Rbasic_fun.Rmin (b-x) (x-a) /\ δ' > 0).
      { exists (Rbasic_fun.Rmin (b - x) (x - a)). split; auto.
        unfold Rbasic_fun.Rmin. applyClassifier1 H2; destruct Rle_dec; lra. } 
      destruct H12 as [δ'[H12 H12']].
      assert(∃x1, 0 < ∣(x1 - x)∣ < δ0 /\ x1 ∈ \(a, b\)).
      { exists ((Rbasic_fun.Rmin δ' δ0)/2 + x).
        split. rewrite Abs_gt. replace (Rbasic_fun.Rmin δ' δ0/2 + x - x)
        with ((Rbasic_fun.Rmin δ' δ0)/2); unfold Rbasic_fun.Rmin;
        destruct Rle_dec; lra. unfold Rbasic_fun.Rmin; destruct Rle_dec; lra. 
        applyClassifier1 H2; destruct H2. unfold Rbasic_fun.Rmin; destruct Rle_dec. 
        rewrite H12. unfold Rbasic_fun.Rmin; destruct Rle_dec; apply Classifier1; lra. 
        apply Classifier1. apply Rnot_le_gt in n. split. lra. 
        unfold Rbasic_fun.Rmin in H12; destruct Rle_dec; lra. }
      destruct H13 as [x1[H13 H13']]. apply H11 in H13 as H13''. 
      assert(\{\ λ x0 y, y = (f[x0] - f[x])/(x0 - x) \}\[x1]
        = (f[x1] - f [x])/(x1 - x)).
      { apply f_x_T; auto. apply Classifier2; auto. } rewrite H14 in H13''. clear H14.
      assert ((f[x1] - f[x])/(x1 - x) <= 0). 
      { destruct H13. apply <- Abs_not_eq_0 in H13. apply Rdichotomy in H13. 
        destruct H13. apply Rminus_lt in H13.
        - apply (H5 x1 x) in H13'; auto. unfold Rdiv. apply Rmult_gre_le. split. 
          lra. apply Rinv_lt_0_compat; lra. 
        - apply Rminus_gt in H13. apply (H5 x x1) in H2; auto. unfold Rdiv. 
          apply Rmult_leq_gre. split. lra. apply Rinv_0_lt_compat; lra. } 
      assert(∣((f[x1] - f[x])/(x1 - x) - f’[x])∣ 
        = - ((f[x1] - f[x])/(x1 - x) - f’[x])). { apply Abs_lt. lra. } 
      rewrite H15 in H13''. rewrite Abs_gt in H13''; auto. lra.
    + red. split.
      * assert (∃ x1, x1 ∈ \(a, b\)). 
        { exists ((b+a)/2). apply Classifier1. split; lra. }
        destruct H2 as [x1 H2]. apply H0 in H2. red in H2. 
        destruct H2 as [y1 H2]. red in H2. destruct H2 as [H2 [H3 H4]]. auto.
      * split; auto. intros.
        assert (ContinuousClose f x1 x2).
        { red. split.
          - red. intros.
            assert (x ∈ \(a, b\)).
            { apply Classifier1. applyClassifier1 H2. applyClassifier1 H3. destruct H2. 
              destruct H3. lra. }
            apply H0 in H6. apply Theorem5_1 in H6. auto.
          - split.
            + apply H0 in H2. apply Theorem5_1 in H2. apply Theorem4_1 in H2.
              destruct H2; auto.
            + apply H0 in H3. apply Theorem5_1 in H3. apply Theorem4_1 in H3.
              destruct H3; auto. } 
        apply (Theorem6_2 f x1 x2) in H4; auto. destruct H4 as [ξ H4]. 
        destruct H4. apply Corollary_DerivativeValue_a in H6.
        assert (ξ ∈ \(a, b\)). apply Classifier1. destruct H4.
        applyClassifier1 H2. applyClassifier1 H3. lra. apply H1 in H7. rewrite H6 in H7. 
        unfold Rdiv in H7. pose proof (Rle_or_lt f[x2] f[x1]). destruct H8. lra.
        assert (/(x2 - x1) > 0).
        { assert ((x2-x1) > 0). lra. apply Rinv_0_lt_compat. auto. }
        assert ((f[x2] - f[x1]) > 0). lra.
        apply (Rmult_gt_0_compat (f[x2] - f[x1]) (/(x2 - x1))) in H10. lra. lra.
        intros. assert (x ∈ \(a, b\)). apply Classifier1. applyClassifier1 H2.
        applyClassifier1 H3. destruct H2. destruct H3. destruct H6. lra.
        apply H0 in H7. auto.
Qed.

(* 函数在区间严格单调递增的充要条件 *)
Theorem Theorem6_4a : ∀ f a b, (a < b /\ \(a, b\) ⊂ dom[f] /\ ∀x, x ∈ \(a, b\) 
    -> Derivable f x) 
  -> DStrictlyIncreaseFun f (\(a, b\)) <-> (∀x, x ∈ \(a, b\) -> f’[x] >= 0) 
    /\ ((∀ a1 b1, a1 < b1 /\ \(a1,b1\) ⊂ \(a, b\) 
    -> ~(∀ x0, x0 ∈ \(a1,b1\) -> f’[x0] = 0))).
Proof.
  intros. destruct H as [K1[H H0]]. split; intros.
  - split.
    + intros. apply H0 in H2 as H2'. red in H2'. destruct H2' as [y']. 
      apply Corollary_DerivativeValue_a in H3 as H3'. rewrite <- H3' in H3. 
      red in H3. red in H1. destruct H1 as [H1[H4 H5]]. destruct H3 as [_[H6 H7]].
      red in H7. destruct H7 as [H7[δ[H8[H9 H10]]]]. 
      pose proof (Rbasic_fun.Rcase_abs (f’[x])). destruct H3. 
      assert (∣(f’[x])∣ > 0). { apply Abs_not_eq_0; lra.  }
      apply H10 in H3. destruct H3 as [δ0[H3 H11]].
      assert(∃ δ', δ' = Rbasic_fun.Rmin (b-x) (x-a) /\ δ' > 0).
      { exists (Rbasic_fun.Rmin (b - x) (x - a)). split; auto.
        unfold Rbasic_fun.Rmin. applyClassifier1 H2; destruct Rle_dec; lra. } 
      destruct H12 as [δ'[H12 H12']]. 
      assert(∃x1, 0 < ∣(x1 - x)∣ < δ0 /\ x1 ∈ \(a, b\)).
      { exists ((Rbasic_fun.Rmin δ' δ0)/2 + x). split. rewrite Abs_gt. 
        replace (Rbasic_fun.Rmin δ' δ0/2 + x - x) with ((Rbasic_fun.Rmin δ' δ0)/2); 
        unfold Rbasic_fun.Rmin; destruct Rle_dec; lra. unfold Rbasic_fun.Rmin;
        destruct Rle_dec; lra. applyClassifier1 H2; destruct H2.
        unfold Rbasic_fun.Rmin; destruct Rle_dec. rewrite H12. 
        unfold Rbasic_fun.Rmin; destruct Rle_dec; apply Classifier1; lra. 
        apply Classifier1. apply Rnot_le_gt in n. split. lra. 
        unfold Rbasic_fun.Rmin in H12; destruct Rle_dec; lra. }
      destruct H13 as [x1[H13 H13']]. apply H11 in H13 as H13''. 
      assert(\{\ λ x0 y,y = (f[x0] - f[x])/(x0 - x) \}\ [x1] 
        = (f[x1] - f[x])/(x1 - x)). { apply f_x_T; auto. apply Classifier2; auto. }
      rewrite H14 in H13''. clear H14. 
      assert ((f[x1] - f[x])/(x1 - x) > 0).
      { destruct H13. apply <- Abs_not_eq_0 in H13. apply Rdichotomy in H13. 
        destruct H13. apply Rminus_lt in H13.
        - apply (H5 x1 x) in H13'; auto. unfold Rdiv. apply Rmult_le_le; auto. 
          split. lra. apply Rinv_lt_0_compat; lra.
        - apply Rminus_gt in H13. apply (H5 x x1) in H2; auto. unfold Rdiv. 
          apply Rmult_gt_0_compat. lra. apply Rinv_0_lt_compat; lra. } 
      assert(∣((f[x1] - f[x])/(x1 - x) - f’[x])∣ = (f[x1]-f[x])/(x1-x)-f’[x]). 
      { apply Abs_gt. lra. } rewrite H15 in H13''. rewrite Abs_lt in H13''; auto. 
      lra. auto.
    + intros. destruct H2.  
      pose proof (classic (∀x0 : R,x0 ∈ \(a1, b1\) -> f’[x0] = 0)).   
      destruct H4; auto. red in H1. destruct H1 as [H1[H7 H6]]. 
      assert(∀x, x ∈ \(a1, b1\) -> Continuous f x). 
      { intros. apply Theorem5_1; auto. }
      assert(∃ x1 x2, x1 < x2 /\ \[x1,x2\] ⊂ \(a1, b1\)).
      { exists ((3*a1+b1)/4), ((3*b1+a1)/4). split. lra. intros z H8. 
        applyClassifier1 H8. apply Classifier1. split; lra. } 
      destruct H8 as [x1[x2[H9 H10]]].
      assert(ContinuousClose f x1 x2).
      { red.  split. red. intros. apply H5. apply H10. apply Classifier1. lra. split. 
        - assert(Continuous f x1). apply H5; apply H10; apply Classifier1; lra.
          apply Theorem4_1 in H8. eapply H8.
        - assert(Continuous f x2). apply H5; apply H10; apply Classifier1; lra.
          apply Theorem4_1 in H8. eapply H8. }
      assert(∀x, x1 < x < x2 -> Derivable f x).
      { intros. apply H0. apply H3; apply H10. apply Classifier1; lra. } 
      apply Theorem6_2 in H8; auto. destruct H8 as [ξ[H12 H13]].
      apply Corollary_DerivativeValue_a in H13. 
      assert(f’[ξ] = 0). apply H4. apply H10. apply Classifier1; lra. 
      rewrite H8 in H13. assert(x1 ∈ \(a, b\)). apply H3; apply H10. 
      apply Classifier1. lra. assert(x2 ∈ \(a, b\)). apply H3; apply H10. 
      apply Classifier1. lra. apply (H6 x1 x2) in H14; auto. unfold Rdiv in H13.  
      symmetry in H13. apply Rmult_integral in H13. destruct H13. lra.
      assert(x2- x1 <>0). lra. apply Rinv_neq_0_compat in H16. lra.
  - destruct H1. 
    assert(DIncreaseFun f (\(a, b\)) <-> (∀x, x ∈ \(a, b\) -> f’[x] >= 0)).
    apply Theorem6_3a; auto. pose proof H1 as H1'. apply <- H3 in H1. clear H3. 
    red in H1. destruct H1 as [H1[_ H3]]. red; split; auto. split; auto. intros. 
    apply H3 in H6 as H6'; auto. destruct H6'; auto. pose proof (H2 x1 x2). 
    assert(\(x1, x2\) ⊂ \(a, b\)).
    { intros z H9. applyClassifier1 H9. apply Classifier1. applyClassifier1 H4. 
      applyClassifier1 H5. split; lra. }
    assert( x1 < x2 /\ \(x1, x2\) ⊂ \(a, b\)). { split; auto. } 
    apply H8 in H10 as H10'. clear H8 H10.
    assert(∀x0, x0 ∈ \(x1, x2\) -> f[x0] = f[x1]).
    { intros. assert(x0 ∈ \(a, b\)).
      { apply Classifier1. applyClassifier1 H4. applyClassifier1 H5. applyClassifier1 H8. 
        split; lra. } 
      applyClassifier1 H8. destruct H8. apply (H3 x1 x0) in H4 as H4'; auto.  
      apply (H3 x0 x2) in H11 as H11'; auto. rewrite <- H7 in H11'. lra. }
    assert(∀x0, x0 ∈ \(x1, x2\) -> f’[x0] = 0).
    { intros. apply Corollary_DerivativeValue_a. repeat split; auto.
      - assert(J1: ∃ δ, δ > 0 /\ δ = Rbasic_fun.Rmin (b - x0) (x0 - a)).
        { exists (Rbasic_fun.Rmin (b - x0) (x0 - a)). split; auto. 
        assert(x0 ∈\(a, b\)). { apply H9; auto. } 
        applyClassifier1 H11. unfold Rbasic_fun.Rmin; destruct Rle_dec; lra. } 
        destruct J1 as [δ0[J2 J3]]. exists δ0; split; auto. intros z J4. 
        apply H. apply Classifier1. applyClassifier1 J4. apply Abs_R in J4.  
        unfold Rbasic_fun.Rmin in J3; destruct Rle_dec in J3; lra.
      - red; intros. applyClassifier2 H11; applyClassifier2 H12. subst; auto.
      - assert(∃ δ, δ > 0 /\ δ = Rbasic_fun.Rmin (x2 - x0) (x0 - x1)).
        { exists (Rbasic_fun.Rmin (x2 - x0) (x0 - x1)). split; auto. 
          applyClassifier1 H10. unfold Rbasic_fun.Rmin; destruct Rle_dec; lra. }
        destruct H11 as [δ'[H11 H12]]. exists δ'; split; auto. split. 
        intros z H13. apply Classifier1. exists ((f[z] - f[x0])/(z - x0)).
        apply Classifier2; auto. intros.
        assert(∃δ, δ > 0 /\ δ < δ').
        { exists (δ'/2). lra. } destruct H14 as [δ[H14 H15]].
        exists δ. split; auto. intros. 
        assert(x ∈ \(x1, x2\)).
        { apply Classifier1. destruct H16. unfold Rbasic_fun.Rmin in H12;  
          destruct Rle_dec in H12. applyClassifier1 H10; destruct H10;
          apply Abs_not_eq_0 in H16; apply Rdichotomy in H16.
          destruct H16 as [H16|H16]. rewrite Abs_lt in H17; auto. lra. 
          rewrite Abs_gt in H17; auto;lra. apply Abs_not_eq_0 in H16; 
          apply Rdichotomy in H16. destruct H16 as [H16|H16]. 
          rewrite Abs_lt in H17; auto. lra. rewrite Abs_gt in H17; auto;lra. }
        assert(\{\ λ x3 y, y = (f[x3] - f[x0])/(x3 - x0) \}\ [x]
          = (f[x] - f[x0])/(x - x0)). 
        { apply f_x_T. red; intros. applyClassifier2 H18; applyClassifier2 H19.
          subst; auto. apply Classifier2; auto. }
        rewrite H18. apply H8 in H17. apply H8 in H10.
        rewrite H17. rewrite H10. rewrite Abs_ge. lra. lra. } elim H10'; auto. 
Qed.

(* 函数在区间严格单调递减的充要条件 *)
Theorem Theorem6_4b : ∀ f a b,
  (a < b /\ \(a, b\) ⊂ dom[f] /\ ∀x, x ∈ \(a, b\) -> Derivable f x)
  -> DStrictlyDecreaseFun f (\(a, b\)) <-> (∀ x, x ∈ \(a, b\) -> f’[x] <= 0)
    /\ (∀ a1 b1, a1 < b1 /\ \(a1,b1\) ⊂ \(a, b\)
      -> ~(∀ x0, x0 ∈ \(a1,b1\) -> f ’[x0] = 0)).
Proof.
  intros. destruct H as [K1[H H0]]. split; intros.
- split.
  + intros. apply H0 in H2 as H2'. red in H2'. destruct H2' as [y']. 
    apply Corollary_DerivativeValue_a in H3 as H3'. rewrite <- H3' in H3. 
    red in H3. red in H1. destruct H1 as [H1[H4 H5]]. destruct H3 as [_[H6 H7]].
    red in H7. destruct H7 as [H7[δ[H8[H9 H10]]]]. 
    pose proof (Rge_gt_dec 0 (f’[x])). destruct H3. lra. 
    assert (∣(f’[x])∣ > 0). { apply Abs_not_eq_0; lra. }
    apply H10 in H3. destruct H3 as [δ0[H3 H11]].
    assert(∃ δ', δ' = Rbasic_fun.Rmin (b - x) (x - a) /\ δ' > 0).
    { exists (Rbasic_fun.Rmin (b - x) (x - a)). split; auto.
      unfold Rbasic_fun.Rmin. applyClassifier1 H2; destruct Rle_dec; lra. } 
    destruct H12 as [δ'[H12 H12']]. 
    assert(∃ x1, 0 < ∣(x1 - x)∣ < δ0 /\ x1 ∈ \(a, b\)).
    { exists ((Rbasic_fun.Rmin δ' δ0)/2 + x). split. rewrite Abs_gt. 
      replace (Rbasic_fun.Rmin δ' δ0/2 + x - x) with ((Rbasic_fun.Rmin δ' δ0)/2); 
      unfold Rbasic_fun.Rmin; destruct Rle_dec; lra. unfold Rbasic_fun.Rmin;
      destruct Rle_dec; lra. applyClassifier1 H2; destruct H2.
      unfold Rbasic_fun.Rmin; destruct Rle_dec. rewrite H12. 
      unfold Rbasic_fun.Rmin; destruct Rle_dec; apply Classifier1; lra. 
      apply Classifier1. apply Rnot_le_gt in n. split. lra. 
      unfold Rbasic_fun.Rmin in H12; destruct Rle_dec; lra. } 
    destruct H13 as [x1[H13 H13']]. apply H11 in H13 as H13''. 
    assert(\{\ λ x0 y, y = (f[x0] - f[x])/(x0 - x) \}\ [x1] 
      = (f[x1] - f[x])/(x1 - x)). { apply f_x_T; auto. apply Classifier2; auto. } 
    rewrite H14 in H13''. clear H14.
    assert ((f[x1] - f[x])/(x1 - x) < 0).
    { destruct H13. apply <- Abs_not_eq_0 in H13. apply Rdichotomy in H13. 
      destruct H13. apply Rminus_lt in H13.
      - apply (H5 x1 x) in H13'; auto. unfold Rdiv. rewrite Rmult_comm.
        apply Rmult_le_gr. split. apply Rinv_lt_0_compat; lra. lra.
      - apply Rminus_gt in H13. apply (H5 x x1) in H2; auto. unfold Rdiv.  
        apply Rmult_le_gr. split. lra. apply Rinv_0_lt_compat; lra. }
    assert(∣((f[x1] - f[x])/(x1 - x) - f’[x])∣
      = - ((f[x1] - f[x])/(x1 - x) - f’[x])). { apply Abs_lt. lra. }
    rewrite H15 in H13''. rewrite Abs_gt in H13''; auto. lra.
  + intros. destruct H2. 
    pose proof (classic (∀ x0, x0 ∈ \(a1, b1\) -> f’[x0] = 0)). destruct H4; 
    auto. red in H1. destruct H1 as [H1[H7 H6]].
    assert(∀ x, x ∈ \(a1, b1\) -> Continuous f x).
    { intros. apply Theorem5_1; auto. }
    assert(∃ x1 x2, x1 < x2 /\ \[x1,x2\] ⊂ \(a1, b1\)).
    { exists ((3 * a1 + b1)/4), ((3 * b1 + a1)/4). split. lra. intros z H8. 
      applyClassifier1 H8. apply Classifier1. split; lra. } 
    destruct H8 as [x1[x2[H9 H10]]].
    assert(ContinuousClose f x1 x2).
    { red.  split. red. intros. apply H5. apply H10. apply Classifier1. lra. split. 
      - assert(Continuous f x1). apply H5; apply H10; apply Classifier1; lra.
        apply Theorem4_1 in H8. eapply H8.
      - assert(Continuous f x2). apply H5; apply H10; apply Classifier1; lra.
        apply Theorem4_1 in H8. eapply H8.  } 
    assert(∀ x, x1 < x < x2 -> Derivable f x).
    { intros. apply H0. apply H3; apply H10. apply Classifier1; lra. } 
    apply Theorem6_2 in H8; auto. destruct H8 as [ξ[H12 H13]].
    apply Corollary_DerivativeValue_a in H13. 
    assert(f’[ξ] = 0). { apply H4. apply H10. apply Classifier1; lra. }
    rewrite H8 in H13. 
    assert(x1 ∈ \(a, b\)). { apply H3; apply H10. apply Classifier1. lra. }
    assert(x2 ∈ \(a, b\)). { apply H3; apply H10. apply Classifier1. lra. }
    apply (H6 x1 x2) in H14; auto. unfold Rdiv in H13.  symmetry in H13.
    apply Rmult_integral in H13. destruct H13. lra. assert(x2- x1 <>0). lra.
    apply Rinv_neq_0_compat in H16. lra.
 - destruct H1. 
   assert(DDecreaseFun f (\(a, b\)) <-> (∀ x, x ∈ \(a, b\) -> f’[x] <= 0)).
   { apply Theorem6_3b; auto. } pose proof H1 as H1'. apply <- H3 in H1. 
   clear H3. red in H1. destruct H1 as [H1[_ H3]]. red; split; auto. split; auto. 
   intros. apply H3 in H6 as H6'; auto. destruct H6'; auto. pose proof (H2 x1 x2). 
   assert(\(x1, x2\) ⊂ \(a, b\)).
   { intros z H9. applyClassifier1 H9. apply Classifier1. applyClassifier1 H4. 
     applyClassifier1 H5. split; lra. }
   assert(x1 < x2 /\ \(x1, x2\) ⊂ \(a, b\)). { split; auto. }
   apply H8 in H10 as H10'. clear H8 H10.
   assert(∀ x0, x0 ∈ \(x1, x2\) -> f[x0] = f[x1]).
   { intros. assert(x0 ∈ \(a, b\)). 
     { apply Classifier1. applyClassifier1 H4. applyClassifier1 H5. applyClassifier1 H8. 
       split; lra. } 
     applyClassifier1 H8. destruct H8. apply (H3 x1 x0) in H4 as H4'; auto.
     apply (H3 x0 x2) in H11 as H11'; auto. rewrite <- H7 in H11'. lra. }
   assert(∀ x0, x0 ∈ \(x1, x2\) -> f’[x0] = 0).
   { intros. apply Corollary_DerivativeValue_a. repeat split; auto.
     - assert(J1: ∃ δ, δ > 0 /\ δ = Rbasic_fun.Rmin (b - x0) (x0 - a)).
       { exists (Rbasic_fun.Rmin (b - x0) (x0 - a)). split; auto. 
         assert(x0 ∈\( a, b \)). { apply H9; auto. } 
         applyClassifier1 H11. unfold Rbasic_fun.Rmin; destruct Rle_dec; lra. } 
       destruct J1 as [δ0[J2 J3]]. exists δ0; split; auto. intros z J4. apply H. 
       apply Classifier1. applyClassifier1 J4. apply Abs_R in J4.  
       unfold Rbasic_fun.Rmin in J3; destruct Rle_dec in J3; lra.
     - red; intros. applyClassifier2 H11; applyClassifier2 H12. subst; auto.
     - assert(∃ δ, δ > 0 /\ δ = Rbasic_fun.Rmin (x2 - x0) (x0 - x1)).
       { exists (Rbasic_fun.Rmin (x2 - x0) (x0 - x1)). split; auto. 
         applyClassifier1 H10. unfold Rbasic_fun.Rmin; destruct Rle_dec; lra. }
       destruct H11 as [δ'[H11 H12]]. exists δ'; split; auto. split. 
       intros z H13. apply Classifier1. exists ((f[z] - f[x0])/(z - x0)). 
       apply Classifier2; auto. intros.
       assert(∃ δ, δ > 0 /\ δ < δ'). { exists (δ'/2). lra. } 
       destruct H14 as [δ[H14 H15]]. exists δ. split; auto. intros. 
       assert(x ∈ \(x1, x2\)).
       { apply Classifier1. destruct H16. unfold Rbasic_fun.Rmin in H12;  
         destruct Rle_dec in H12. applyClassifier1 H10; destruct H10;
         apply Abs_not_eq_0 in H16; apply Rdichotomy in H16.
         destruct H16 as [H16|H16]. rewrite Abs_lt in H17; auto. lra. 
         rewrite Abs_gt in H17; auto;lra. apply Abs_not_eq_0 in H16; 
         apply Rdichotomy in H16. destruct H16 as [H16|H16]. 
         rewrite Abs_lt in H17; auto. lra. rewrite Abs_gt in H17; auto;lra. }
       assert(\{\ λ x3 y, y = (f[x3] - f[x0])/(x3 - x0) \}\ [x]
         = (f[x] - f[x0])/(x - x0)). 
       { apply f_x_T. red; intros. applyClassifier2 H18; applyClassifier2 H19.
         subst; auto. apply Classifier2; auto. }
       rewrite H18. apply H8 in H17. apply H8 in H10. rewrite H17. rewrite H10.
       rewrite Abs_ge. lra. lra. } elim H10'; auto. 
Qed.

Corollary Corollary6_4a : ∀ f a b, a < b
  -> (∀ x, x ∈ \(a, b\) -> Differentiable f x) -> (∀ x, x ∈ \(a, b\) -> 0 < f’[x])
  -> DStrictlyIncreaseFun f \(a, b\).
Proof.
  intros.
  assert (a < b /\ \(a, b\) ⊂ dom[f] /\ ∀ x, x ∈ \(a, b\) -> Derivable f x).
  { split; auto. split; unfold Contain; intros; apply H0,Theorem5_9a in H2; auto.
    destruct H2 as [y[H2[[δ[]]_]]]. apply H4,Classifier1. rewrite Abs_ge; lra. }
  apply Theorem6_4a in H2. apply H2. split; intros. apply H1 in H3. lra.
  intro. destruct H3. assert ((a1 + b1)/2 ∈ \(a1, b1\)).
  { apply Classifier1; split; lra. } pose proof H6.
  apply H5,H1 in H6. apply H4 in H7. rewrite H7 in H6. lra.
Qed.

Corollary Corollary6_4b : ∀ f a b, a < b
  -> (∀ x, x ∈ \(a, b\) -> Differentiable f x) -> (∀ x, x ∈ \(a, b\) -> f’[x] < 0)
  -> DStrictlyDecreaseFun f \(a, b\).
Proof.
  intros.
  assert (a < b /\ \(a, b\) ⊂ dom[f] /\ ∀ x, x ∈ \(a, b\) -> Derivable f x).
  { split; auto. split; unfold Contain; intros; apply H0,Theorem5_9a in H2; auto.
    destruct H2 as [y[H2[[δ[]]_]]]. apply H4,Classifier1. rewrite Abs_ge; lra. }
  apply Theorem6_4b in H2. apply H2. split; intros. apply H1 in H3. lra.
  intro. destruct H3. assert ((a1 + b1)/2 ∈ \(a1, b1\)).
  { apply Classifier1; split; lra. } pose proof H6.
  apply H5,H1 in H6. apply H4 in H7. rewrite H7 in H6. lra.
Qed.

(* x0处右导数大于0则有右邻域大于f[x0] *)
Lemma Lemma6_5a : ∀ f x0, Derivative_pos f x0 (f’+[x0]) -> f’+[x0] > 0
  -> (∃ δ, δ > 0 /\ (∀ x , x ∈ \(x0, x0 + δ\) -> f[x0] < f[x])).
Proof.
  assert (∀ f x0 A, limit_pos f x0 A -> A > 0 -> (∀ r, 0 < r < A
    -> (∃ δ, δ > 0 /\ (∀ x, x ∈ U+º(x0; δ) -> 0 < r < f[x])))) as K.
  { intros f x0 A H0 H1 r H2. destruct H0 as [H0[δ'[H3[H4 H5]]]].
    assert (H6 : A - r > 0). lra. apply H5 in H6 as H7. destruct H7 as [δ[H7 H8]].
    exists δ. split; try lra. intros x H9. applyClassifier1 H9. apply H8 in H9 as H10. 
    apply Abs_R in H10. lra. }
  intros. destruct H as [H[H3 H4]].
  assert (∃ g, g = \{\ λ x y, y = (f[x] - f[x0])/(x - x0) \}\).
  { exists \{\ λ x y, y = (f [x] - f [x0]) / (x - x0) \}\. auto. }
  destruct H1 as [g H1]. rewrite <- H1 in H4.
  assert ((∀ r, 0 < r < (f’+[x0])
    -> (∃ δ, δ > 0 /\ (∀ x, x ∈ U+º(x0; δ) -> 0 < r < g[x])))).
  { apply K; auto. } pose proof (H2 ((f’+[x0])/2)).
  assert (0 < f’+[x0]/2 < f’+[x0]). lra. apply H5 in H6. 
  destruct H6 as [δ [H6 H7]]. exists δ. split; auto. intros.
  pose proof H8 as H8'. apply H7 in H8. assert (0 < g[x]). lra.
  rewrite H1, FunValue in H9. assert ((x - x0) > 0). { applyClassifier1 H8'. lra. }
  apply (Rmult_lt_0_compat (x - x0) ((f[x] - f[x0])/(x - x0))) in H10 as H12; auto.
  unfold Rdiv in H12. rewrite <- Rmult_assoc in H12.
  rewrite Rinv_r_simpl_m in H12; lra.
Qed.

(* x0处右导数小于0则有右邻域小于f[x0] *)
Lemma Lemma6_5b : ∀ f x0, Derivative_pos f x0 (f’+[x0]) -> f’+[x0] < 0
  -> (∃ δ, δ > 0 /\ (∀ x , x ∈ \(x0, x0 + δ\) -> f[x] < f[x0])).
Proof.
  assert (∀ f x0 A, limit_pos f x0 A -> A < 0 -> (∀ r, A < r < 0
    -> (∃ δ, δ > 0 /\ (∀ x, x ∈ U+º(x0; δ) -> f[x] < r < 0)))) as K.
  { intros f x0 A H0 H1 r H2. destruct H0 as [H0[δ'[H3[H4 H5]]]].
    assert (H6 : r - A > 0). lra. apply H5 in H6 as H7. destruct H7 as [δ[H7 H8]]. 
    exists δ. split; try lra. intros x H9. applyClassifier1 H9. apply H8 in H9 as H10. 
    apply Abs_R in H10. lra. }
  intros. destruct H as [H[H3 H4]].
  assert (∃ g, g = \{\ λ x y, y = (f[x] - f[x0])/(x - x0) \}\).
  { exists \{\ λ x y, y = (f[x] - f[x0])/(x - x0) \}\. auto. }
  destruct H1 as [g H1]. rewrite <- H1 in H4.
  assert ((∀ r, (f’+[x0] < r < 0)
    -> (∃ δ, δ > 0 /\ (∀ x, x ∈ U+º(x0; δ) -> g[x] < r < 0)))).
  { apply K; auto. } pose proof (H2 ((f’+[x0])/2)).
  assert (f’+[x0] < f’+[x0]/2 < 0). lra. apply H5 in H6. destruct H6 as [δ[H6 H7]]. 
  exists δ. split; auto. intros. pose proof H8 as H8'. apply H7 in H8. 
  assert (g[x] < 0). lra. rewrite H1, FunValue in H9. 
  assert ((x - x0) > 0). { applyClassifier1 H8'. lra. }
  assert ((f[x] - f[x0])/(x - x0) * (x - x0) < 0). { apply Rmult_le_gr; auto. }
  unfold Rdiv in H11. rewrite Rmult_comm, <- Rmult_assoc, Rinv_r_simpl_m in H11.
  lra. lra.
Qed.

(* x0处左导数大于0则有左邻域小于f[x0] *)
Lemma Lemma6_5c : ∀ f x0, Derivative_neg f x0 (f’_[x0]) -> f’_[x0] > 0
  -> (∃ δ, δ > 0 /\ (∀ x, x ∈ \(x0 - δ, x0\) -> f[x] < f[x0])).
Proof.
  assert (∀ f x0 A, limit_neg f x0 A -> A > 0 -> (∀ r, 0 < r < A
    -> (∃ δ, δ > 0 /\ (∀ x, x ∈ U-º(x0; δ) -> 0 < r < f[x])))) as K.
  { intros f x0 A H0 H1 r H2. destruct H0 as [H0[δ'[H3[H4 H5]]]].
    assert (H6 : A - r > 0). lra. apply H5 in H6 as H7. destruct H7 as [δ[H7 H8]]. 
    exists δ. split; try lra. intros x H9. applyClassifier1 H9. apply H8 in H9 as H10. 
    apply Abs_R in H10. lra. }
  intros. destruct H as [H[H3 H4]]. 
  assert (∃ g, g = \{\ λ x y, y = (f[x] - f[x0])/(x - x0) \}\).
  { exists \{\ λ x y, y = (f[x] - f[x0])/(x - x0) \}\. auto. }
  destruct H1 as [g H1]. rewrite <- H1 in H4.
  assert ((∀ r, 0 < r < (f’_[x0])
    -> (∃ δ, δ > 0 /\ (∀ x, x ∈ U-º(x0; δ) -> 0 < r < g[x])))).
  { apply K; auto. } pose proof (H2 ((f’_[x0])/2)).
  assert (0 < f’_[x0]/2 < f’_[x0]). lra. apply H5 in H6.
  destruct H6 as [δ[H6 H7]]. exists δ. split; auto. intros. pose proof H8 as H8'.
  apply H7 in H8. assert (g[x] > 0). lra. rewrite H1, FunValue in H9.
  assert ((x - x0) < 0). { applyClassifier1 H8'. lra. }
  assert ((f[x] - f[x0])/(x - x0) * (x - x0) < 0).
  { rewrite Rmult_comm. apply Rmult_le_gr; auto. } unfold Rdiv in H11.
  rewrite Rmult_comm, <- Rmult_assoc, Rinv_r_simpl_m in H11. lra. lra.
Qed.

(* x0处左导数小于0则有左邻域大于f[x0] *)
Lemma Lemma6_5d : ∀ f x0, Derivative_neg f x0 (f’_[x0]) -> f’_[x0] < 0
  -> (∃ δ, δ > 0 /\ (∀ x, x ∈ \(x0 - δ, x0\) -> f[x] > f[x0])).
Proof.
  assert (∀ f x0 A, limit_neg f x0 A -> A < 0 -> (∀ r, A < r < 0
    -> (∃ δ, δ > 0 /\ (∀ x, x ∈ U-º(x0; δ) -> f[x] < r < 0)))) as K.
  { intros f x0 A H0 H1 r H2. destruct H0 as [H0[δ'[H3[H4 H5]]]].
    assert (H6 : r - A > 0). lra. apply H5 in H6 as H7. 
    destruct H7 as [δ[H7 H8]]. exists δ. split; try lra. intros x H9. 
    applyClassifier1 H9. apply H8 in H9 as H10. apply Abs_R in H10. lra. }
  intros. destruct H as [H[H3 H4]].
  assert (∃ g, g = \{\ λ x y, y = (f[x] - f[x0])/(x - x0) \}\).
  { exists \{\ λ x y, y = (f[x] - f[x0])/(x - x0) \}\. auto. }
  destruct H1 as [g H1]. rewrite <- H1 in H4.
  assert ((∀ r, (f’_[x0]) < r < 0
    -> (∃ δ, δ > 0 /\ (∀ x, x ∈ U-º(x0; δ) -> g[x] < r < 0)))).
  { apply K; auto. } pose proof (H2 ((f’_[x0])/2)).
  assert (f’_[x0] < f’_[x0]/2 < 0). lra. apply H5 in H6. destruct H6 as [δ[H6 H7]]. 
  exists δ. split; auto. intros. pose proof H8 as H8'. apply H7 in H8. 
  assert (g[x] < 0). lra. rewrite H1, FunValue in H9.
  assert ((x - x0) < 0). { applyClassifier1 H8'. lra. }
  assert ((f[x] - f[x0])/(x - x0) * (x - x0) > 0). { apply Rmult_le_le; auto. }
  unfold Rdiv in H11. rewrite Rmult_comm, <- Rmult_assoc, Rinv_r_simpl_m in H11.
  lra. lra.
Qed.

(* 函数相减左求导 *)
Lemma Lemma6_5e : ∀ u v x0, Derivative_neg u x0 (u’_[x0])
  -> Derivative_neg v x0 (v’_[x0])
  -> Derivative_neg (u \- v) x0 (u’_[x0] - v’_[x0]).
Proof.
  intros u v x0 H0 H1.
  assert (H3 : Function (u \- v)). { apply Corollary_sub_fun_a. }
  split; auto. destruct H0 as [H0[[δ1'[H4 H5]]H6]].
  destruct H1 as [H1[[δ2'[H7 H8]]H9]].
  generalize (Examp1 δ1' δ2' H4 H7); intros [δ'[H10[H11 H12]]]. split.
  - exists δ'. split; auto. intros x I1. applyClassifier1 I1. apply Classifier1.
    exists (u[x] - v[x]). apply Classifier2. repeat split; auto; 
    [apply H5 | apply H8]; apply Classifier1; lra.
  - assert (H13 : Function \{\ λ x y, y 
      = ((u \- v)[x] - (u \- v)[x0])/(x - x0) \}\).
    { intros x y z I1 I2. applyClassifier2 I1; applyClassifier2 I2. 
      rewrite I2; apply I1. } split; auto. exists δ'. split; [assumption | split].
    + intros x I1. apply Classifier1. exists (((u \- v)[x] - (u \- v)[x0])/(x - x0)).
      apply Classifier2. reflexivity.
    + intros ε H14. destruct H6 as [H6[δ3'[H15[H16 H17]]]].
      destruct H9 as [H9[δ4'[H18[H19 H20]]]]. assert (H21 : ε/2 > 0). lra.
      apply H20 in H21 as H22. destruct H22 as [δ2[[H22 H26]H23]].
      apply H17 in H21 as [δ1[[H24 H27]H25]].
      generalize (Examp2 δ' δ1 δ2 H10 H24 H22). intros [δ[H28[H29[H30 H31]]]].
      exists δ. split; try lra. intros x H32.
      assert (H33 : \{\ λ x y, y = ((u \- v)[x] - (u \- v)[x0])/(x - x0) \}\[x]
        = ((u \- v)[x] - (u \- v)[x0])/(x - x0)).
      { apply f_x_T; auto. apply Classifier2. reflexivity. }
      rewrite H33. clear H33.
      assert (H33 : ∀ x1, x1 ∈ dom[u] -> x1 ∈ dom[v]
        -> (u \- v)[x1] = u[x1] - v[x1]).
      { intros. rewrite Corollary_sub_fun_b; auto. }
      assert (x ∈ dom[u] /\ x ∈ dom[v]) as [].
      { split; [apply H5|apply H8]; apply Classifier1; lra. }
      assert (x0 ∈ dom[u] /\ x0 ∈ dom[v]) as [].
      { split; [apply H5|apply H8]; apply Classifier1; lra. }
      rewrite H33; auto. rewrite H33; auto.
      assert (H38 : x0 - δ1 < x < x0). lra. apply H25 in H38.
      assert (H39 : x0 - δ2 < x < x0). lra. apply H23 in H39.
      assert (H40 : \{\ λ x y, y = (u[x] - u[x0])/(x - x0) \}\[x]
        = (u[x] - u[x0])/(x - x0)).
      { apply f_x_T; auto. apply Classifier2. reflexivity. }
      rewrite H40 in H38. clear H40.
      assert (H40 : \{\ λ x y, y = (v[x] - v[x0])/(x - x0) \}\[x]
        = (v[x] - v[x0])/(x - x0)).
      { apply f_x_T; auto. apply Classifier2. reflexivity. }
      rewrite H40 in H39. clear H40.
      assert (H40 : (u[x]-v[x]-(u[x0]-v[x0]))/(x-x0)-(u’_[x0]-v’_[x0])
        = ((u[x]-u[x0])/(x-x0)-u’_[x0])-((v[x]-v[x0])/(x-x0)-v’_[x0])).
      { field. lra. } rewrite H40.
      generalize (Abs_minus_le ((u[x] - u[x0])/(x - x0) - u’_[x0])
        ((v[x] - v[x0])/(x - x0) - v’_[x0])). intro H41. lra.
Qed.

(* 函数相减右求导 *)
Lemma Lemma6_5f : ∀ u v x0, Derivative_pos u x0 (u’+[x0])
  -> Derivative_pos v x0 (v’+[x0])
  -> Derivative_pos (u \- v) x0 (u’+[x0] - v’+[x0]).
Proof.
  intros u v x0 H0 H1.
  assert (H3 : Function (u \- v)). { apply Corollary_sub_fun_a. }
  split; auto. destruct H0 as [H0[[δ1'[H4 H5]]H6]].
  destruct H1 as [H1[[δ2'[H7 H8]]H9]].
  generalize (Examp1 δ1' δ2' H4 H7); intros [δ'[H10[H11 H12]]]. split.
  - exists δ'. split; auto. intros x I1. applyClassifier1 I1. apply Classifier1.
    exists (u[x] - v[x]). apply Classifier2. repeat split; auto; 
    [apply H5 | apply H8]; apply Classifier1; lra.
  - assert (H13 : Function \{\ λ x y, y
      = ((u \- v)[x] - (u \- v)[x0])/(x - x0) \}\).
    { intros x y z I1 I2. applyClassifier2 I1; applyClassifier2 I2. 
      rewrite I2; apply I1. } split; auto. exists δ'. split; [assumption|split].
    + intros x I1. apply Classifier1. exists (((u \- v)[x] - (u \- v)[x0])/(x - x0)).
      apply Classifier2. reflexivity.
    + intros ε H14. destruct H6 as [H6[δ3'[H15[H16 H17]]]].
      destruct H9 as [H9[δ4'[H18[H19 H20]]]]. assert (H21 : ε/2 > 0). lra.
      apply H20 in H21 as H22. destruct H22 as [δ2[[H22 H26]H23]].
      apply H17 in H21 as [δ1[[H24 H27]H25]].
      generalize (Examp2 δ' δ1 δ2 H10 H24 H22). intros [δ[H28[H29[H30 H31]]]].
      exists δ. split; try lra. intros x H32.
      assert (H33 : \{\ λ x y, y = ((u \- v)[x] - (u \- v)[x0])/(x - x0) \}\[x]
        = ((u \- v)[x] - (u \- v)[x0])/(x - x0)).
      { apply f_x_T; auto. apply Classifier2. reflexivity. }
      rewrite H33. clear H33.
      assert (H33 : ∀ x1, x1 ∈ dom[u] -> x1 ∈ dom[v]
        -> (u \- v)[x1] = u[x1] - v[x1]).
      { intros. rewrite Corollary_sub_fun_b; auto. }
      assert (x ∈ dom[u] /\ x ∈ dom[v]) as [].
      { split; [apply H5 | apply H8]; apply Classifier1; lra. }
      assert (x0 ∈ dom[u] /\ x0 ∈ dom[v]) as [].
      { split; [apply H5 | apply H8]; apply Classifier1; lra. }
      rewrite H33; auto. rewrite H33; auto.
      assert (H38 : x0 < x < x0 + δ1). lra. apply H25 in H38.
      assert (H39 : x0 < x < x0 + δ2). lra. apply H23 in H39.
      assert (H40 : \{\ λ x y, y = (u[x] - u[x0])/(x - x0) \}\[x]
        = (u[x] - u[x0])/(x - x0)).
      { apply f_x_T; auto. apply Classifier2. reflexivity. } 
      rewrite H40 in H38. clear H40.
      assert (H40 : \{\ λ x y, y = (v[x] - v[x0])/(x - x0) \}\[x]
        = (v[x] - v[x0])/(x - x0)).
      { apply f_x_T; auto. apply Classifier2. reflexivity. }
      rewrite H40 in H39. clear H40.
      assert (H40 : (u[x]-v[x]-(u[x0]-v[x0]))/(x-x0)-(u’+[x0]-v’+[x0])
        = ((u[x]-u[x0])/(x-x0)-u’+[x0])-((v[x]-v[x0])/(x-x0)-v’+[x0])).
      { field. lra. } rewrite H40.
      generalize (Abs_minus_le ((u[x] - u[x0])/(x - x0) - u’+[x0])
        ((v[x] - v[x0])/(x - x0) - v’+[x0])). intro H41. lra.
Qed.

Theorem Theorem6_5 : ∀ f (a b : R), a < b -> (∀ x, x ∈ \(a, b\) -> Derivable f x)
  -> (∃ y1 y2, Derivative_pos f a y1 /\ Derivative_neg f b y2 /\ y1 <> y2)
  -> (∀ k, k ∈ \(f’_[b], f’+[a]\) \/ k ∈ \(f’+[a], f’_[b]\)
    -> ∃ ξ, a < ξ < b /\ Derivative f ξ k).
Proof.
  intros. destruct H1 as [y1[y2[H1[]]]].
  set (g := \{\ λ u v, v = k * u \}\). set (F := f \- g).
  assert (∀ x, Derivative g x k).
  { assert (\{\ λ u v, v = k * u \}\ = \{\ λ u v, v = k * (u - 0)^(1)%nat \}\).
    { apply AxiomI; split; intros; applyClassifier1 H5; destruct H5 as [x[y[]]];
      rewrite H5; apply Classifier2; simpl in *; lra. }
    intros. assert (k * (INR 1)  * (x - 0)^(1 - 1) = k). simpl. lra.
    unfold g. pattern k at 2. rewrite <- H6, H5. apply EleFun_Fact10. }
  assert (∀ x, x ∈ \(a, b\) -> Derivative F x (f’[x] - k)) as HK.
  { intros. pose proof (H5 x). apply Corollary_DerivativeValue_a in H7.
    rewrite <- H7. apply Theorem5_4b; auto. exists k. auto. }
  assert (f’+[a] = y1 /\ f’_[b] = y2) as [].
  { apply Corollary_DerivativeValue_pos in H1; 
    apply Corollary_DerivativeValue_neg in H3; auto. }
  assert (Derivative_pos F a (y1 - k)).
  { pose proof (H5 a). apply Theorem5_2 in H8 as []. pose proof H9.
    apply Corollary_DerivativeValue_pos in H9. rewrite <- H6, <-H9. unfold F.
    apply Lemma6_5f; [rewrite H6 | rewrite H9]; auto. }
  assert (Derivative_neg F b (y2 - k)).
  { pose proof (H5 b). apply Theorem5_2 in H9 as []. pose proof H9.
    apply Corollary_DerivativeValue_neg in H11. rewrite <- H7, <-H11. unfold F.
    apply Lemma6_5e; [rewrite H7 | rewrite H11]; auto. }
  pose proof H8; pose proof H9. apply Corollary_DerivativeValue_pos in H10;
  apply Corollary_DerivativeValue_neg in H11; auto.
  assert (F’+[a] * F’_[b] < 0).
  { rewrite H10, H11. rewrite H6, H7 in H2. destruct H2; applyClassifier1 H2;
    destruct H2; [rewrite Rmult_comm | ]; apply Rmult_le_gr; lra. }
  assert (ContinuousClose F a b).
  { split. red; intros. apply Theorem5_1. exists (f’[x] - k).
    pose proof (H5 x). pose proof H14. apply Corollary_DerivativeValue_a in H14.
    rewrite <-H14. apply Theorem5_4b. apply H0. apply Classifier1; auto. red. eauto.
    split; [apply Corollary5_1b | apply Corollary5_1a]; eauto. }
  pose proof H13. apply Theorem4_6 in H14 as [[M][m]]; auto.
  destruct H14 as [H14[H16[x1[]]]], H15 as [H15[H19[x2[]]]].
  destruct (Rtotal_order 0 (F’+[a])) as [H22|[]].
  - assert (F’_[b] < 0).
    { destruct (Rlt_or_le (F’_[b]) 0); auto. assert (0 <= F’+[a] * F’_[b]).
      { apply Rmult_le_pos; lra. } exfalso. lra. }
    apply Lemma6_5a in H22 as [δ1[]]; [|rewrite H10; auto].
    apply Lemma6_5d in H23 as [δ2[]]; [|rewrite H11; auto].
    destruct (Examp1 δ1 (b - a)) as [δ3[H26[]]]; auto. lra.
    assert ((a + δ3/2) ∈ \[a, b\] /\ F[a] < F[a + δ3/2]) as [].
    { split; [|apply H24]; apply Classifier1; lra. }
    destruct (Examp1 δ2 (b - a)) as [δ4[H31[]]]; auto. lra.
    assert ((b - δ4/2) ∈ \[a, b\] /\ F[b] < F[b - δ4/2]) as [].
    { split; [|apply H25]; apply Classifier1; lra. }
    assert (x1 <> a /\ x1 <> b) as [].
    { split; intro. rewrite <- H36, H18, H36 in H30. apply H16 in H29. lra.
      rewrite <- H36, H18, H36 in H35. apply H16 in H34. lra. }
    assert (x1 ∈ \(a, b\)). { applyClassifier1 H17. apply Classifier1; lra. }
    assert (Extremum F x1).
    { left. split. red; intros. applyClassifier2 H39. applyClassifier2 H40.
      destruct H39 as [_[]], H40 as [_[]]. rewrite H41, H42; auto.
      assert (a < x1 < b) as []. { applyClassifier1 H38; auto. }
      destruct (Examp1 (x1 - a) (b - x1)) as [x[H41[]]]. lra. lra.
      exists x. repeat split; auto. red; intros. apply H14.
      applyClassifier1 H44. apply Abs_R in H44. apply Classifier1. lra. intros.
      rewrite H18. apply H16. applyClassifier1 H44. apply Abs_R in H44.
      apply Classifier1. lra. } apply Theorem5_3 in H39.
    assert (Derivative F x1 (f’[x1] - k)). { apply HK; auto. }
    assert (f’[x1] - k = 0). { apply (DerivativeUnique F x1); auto. }
    apply H0 in H38 as []. pose proof H38. 
    apply Corollary_DerivativeValue_a in H42. 
    assert (x = k). lra. exists x1. split. applyClassifier1 H17; lra.
    rewrite <- H43; auto. exists (f’[x1] - k). apply HK; auto.
  - rewrite <- H22, Rmult_0_l in H12. lra.
  - assert (0 < F’_[b]).
    { destruct (Rlt_or_le 0 (F’_[b])); auto. assert (F’+[a] * F’_[b] >= 0).
      { rewrite Rmult_comm. apply Rmult_leq_le; lra. } exfalso. lra. }
    apply Lemma6_5b in H22 as [δ1[]]; [|rewrite H10; auto].
    apply Lemma6_5c in H23 as [δ2[]]; [|rewrite H11; auto].
    destruct (Examp1 δ1 (b - a)) as [δ3[H26[]]]; auto. lra.
    assert ((a + δ3/2) ∈ \[a, b\] /\ F[a + δ3/2] < F[a]) as [].
    { split; [|apply H24]; apply Classifier1; lra. }
    destruct (Examp1 δ2 (b - a)) as [δ4[H31[]]]; auto. lra.
    assert ((b - δ4/2) ∈ \[a, b\] /\ F[b - δ4/2] < F[b]) as [].
    { split; [|apply H25]; apply Classifier1; lra. }
    assert (x2 <> a /\ x2 <> b) as [].
    { split; intro. rewrite <- H36, H21, H36 in H30. apply H19 in H29. lra.
      rewrite <- H36, H21, H36 in H35. apply H19 in H34. lra. }
    assert (x2 ∈ \(a, b\)). { applyClassifier1 H20. apply Classifier1; lra. }
    assert (Extremum F x2).
    { right. split. red; intros. applyClassifier2 H39. applyClassifier2 H40.
      destruct H39 as [_[]], H40 as [_[]]. rewrite H41, H42; auto.
      assert (a < x2 < b) as []. { applyClassifier1 H38; auto. }
      destruct (Examp1 (x2 - a) (b - x2)) as [x[H41[]]]. lra. lra.
      exists x. repeat split; auto. red; intros. apply H14. applyClassifier1 H44.
      apply Abs_R in H44. apply Classifier1. lra. intros. rewrite H21. apply H19.
      applyClassifier1 H44. apply Abs_R in H44. apply Classifier1. lra. } 
    apply Theorem5_3 in H39.
    assert (Derivative F x2 (f’[x2] - k)). { apply HK; auto. }
    assert (f’[x2] - k = 0). { apply (DerivativeUnique F x2); auto. }
    apply H0 in H38 as []. pose proof H38. apply Corollary_DerivativeValue_a
    in H42. assert (x = k). lra. exists x2. split. applyClassifier1 H20; lra.
    rewrite <- H43; auto. exists (f’[x2] - k). apply HK; auto.
Qed.

Corollary Corollary6_5 : ∀ f a b, a < b
  -> (∀ x, x ∈ \(a, b\) -> Derivable f x /\ f’[x] <> 0)
  -> DStrictlyDecreaseFun f \(a, b\) \/ DStrictlyIncreaseFun f \(a, b\).
Proof.
  intros. assert ((∀ x, x ∈ \(a, b\) -> 0 < f’[x])
    \/ (∀ x, x ∈ \(a, b\) -> f’[x] < 0)).
  { apply NNPP. intro. apply not_and_or in H1 as [].
    assert (∃ x1, x1 ∈ \(a, b\) /\ 0 < f’[x1]) as [x1[]].
    { apply NNPP; intro. elim H2. intros. destruct (Rtotal_order 0 (f’[x]))
      as [H5|[]]; auto. elim H3; eauto. apply H0 in H4 as []. elim H6; auto. }
    assert (∃ x2, x2 ∈ \(a, b\) /\ f’[x2] < 0) as [x2[]].
    { apply NNPP; intro. elim H1. intros. destruct (Rtotal_order 0 (f’[x]))
      as [H7|[]]; auto. apply H0 in H6 as []. elim H8; auto. elim H5; eauto. }
    assert ((∃ y1 y2, Derivative_pos f x1 y1 /\ Derivative_neg f x2 y2 /\ y1 <> y2)
      /\ (∃ y3 y4, Derivative_pos f x2 y3 /\ Derivative_neg f x1 y4 /\ y3 <> y4)).
    { split; [exists (f’[x1]), (f’[x2])|exists (f’[x2]), (f’[x1])];
      split; [ |split; [ |lra]| |split; [ |lra]]; apply H0 in H3 as [[]];
      pose proof H3; apply H0 in H5 as [[]]; pose proof H5;
      apply Corollary_DerivativeValue_a in H8,H10; try rewrite H8;
      try rewrite H10; apply Theorem5_2; auto. }
    destruct (Rtotal_order x1 x2) as [H8|[]].
    + destruct H7 as [H7 _]. apply Theorem6_5 with (k := 0) in H7 as [ξ[]]; auto.
      assert (ξ ∈ \(a, b\)).
      { applyClassifier1 H3. applyClassifier1 H5. apply Classifier1 ;lra. }
      apply H0 in H10 as []. apply Corollary_DerivativeValue_a in H9; auto.
      intros. apply H0. applyClassifier1 H9. applyClassifier1 H3. applyClassifier1 H5.
      apply Classifier1; lra. apply H0 in H3 as [[]], H5 as [[]]. pose proof H3.
      pose proof H5. apply Corollary_DerivativeValue_a in H11,H12.
      apply Theorem5_2 in H3 as [], H5 as [].
      apply Corollary_DerivativeValue_neg in H5.
      apply Corollary_DerivativeValue_pos in H13.
      rewrite H11,<-H13 in H4. rewrite H12,<-H5 in H6. left. apply Classifier1; auto.
    + rewrite H8 in H4. lra.
    + destruct H7 as [_]. apply Theorem6_5 with (k := 0) in H7 as [ξ[]]; auto.
      assert (ξ ∈ \(a, b\)).
      { applyClassifier1 H3. applyClassifier1 H5. apply Classifier1 ;lra. }
      apply H0 in H10 as []. apply Corollary_DerivativeValue_a in H9; auto.
      intros. apply H0. applyClassifier1 H9. applyClassifier1 H3. applyClassifier1 H5.
      apply Classifier1; lra. apply H0 in H3 as [[]], H5 as [[]]. pose proof H3.
      pose proof H5. apply Corollary_DerivativeValue_a in H11,H12.
      apply Theorem5_2 in H3 as [], H5 as [].
      apply Corollary_DerivativeValue_neg in H3.
      apply Corollary_DerivativeValue_pos in H14.
      rewrite H11,<-H3 in H4. rewrite H12,<-H14 in H6. right. apply Classifier1; auto. }
  assert (\(a, b\) ⊂ dom[f]).
  { red; intros. apply H0 in H2 as [[x[H2[[x0[]]]]]]. apply H4.
    apply Classifier1. rewrite Abs_ge; lra. }
  assert (∀ x, x ∈ \(a, b\) -> Derivable f x). { intros. apply H0; auto. }
  destruct H1; [right; apply Theorem6_4a|left; apply Theorem6_4b]; auto;
  split; intros; try (apply H1 in H4; lra); intro; destruct H4;
  assert ((a1 + b1)/2 ∈ \(a1, b1\)) by (apply Classifier1; lra); pose proof H7;
  apply H5 in H7; apply H6,H0 in H8 as []; auto.
Qed.

(* 6.2 柯西中值定理和不定式极限 *)

(* 柯西中值定理 *)
Theorem Theorem6_6 : ∀ f g (a b : R), a < b -> ContinuousClose f a b 
  -> ContinuousClose g a b -> (∀ x, a < x < b -> Derivable f x)
  -> (∀ x, a < x < b -> Derivable g x) 
  -> (∀ x, a < x < b -> ~(f’[x] = 0 /\ g’[x] = 0)) -> g[b] <> g[a]
  -> ∃ ξ, a < ξ < b /\ (f’[ξ])/(g’[ξ]) = ((f[b] - f[a])/(g[b] - g[a])).
Proof.
  intros f g a b H0 H1 H2 H3 H4 H50 H20.
  assert (H5 : (∀ x u v, a < x < b -> Derivative f x u -> Derivative g x v 
    -> ~(u = 0 /\ v = 0))).
  { intros x u v I1 I2 I3. apply Corollary_DerivativeValue_a in I2 as I4.
    apply Corollary_DerivativeValue_a in I3 as I5. rewrite <- I4; rewrite <- I5.
    auto. }
  assert (H6 : ∃ F, F = \{\ λ x y, y 
    = f[x] - f[a] - (f[b] - f[a])/(g[b] - g[a])*(g[x] - g[a]) \}\).
  { exists \{\ λ x y, y = f[x]-f[a]-(f[b]-f[a])/(g[b]-g[a])*(g[x]-g[a]) \}\. 
    reflexivity. } destruct H6 as [F H6].
  assert (H7 : Function F).
  { rewrite H6. unfold Function. intros x y z I1 I2. applyClassifier2 I1. 
    applyClassifier2 I2. rewrite I2. assumption. }
  assert (H8 : ∀ x, F[x] = f[x]-f[a]-(f[b]-f[a])/(g[b]-g[a])*(g[x]-g[a])).
  { intro x. apply f_x_T; auto. rewrite H6. apply Classifier2. reflexivity. }
  destruct H1 as [H1[H9 H10]]. unfold ContinuousOpen in H1. 
  destruct H2 as [H2[H11 H12]]. unfold ContinuousOpen in H2.
  assert (H13 : ContinuousClose F a b).
  { unfold ContinuousClose. split; [idtac | split].
    - intros x I1. unfold Continuous. split.
      + apply Classifier1. exists (f[x]-f[a]-(f[b]-f[a])/(g[b]-g[a])*(g[x]-g[a])).
        rewrite H6. apply Classifier2. reflexivity.
      + unfold limit. split; auto. apply H1 in I1 as I2. unfold Continuous in I2. 
        destruct I2 as [I2 I3]. unfold limit in I3. 
        destruct I3 as [I3[δ'[I4[I5 I6]]]]. exists δ'. split; auto. split.
        * intros x0 J1. apply Classifier1. 
          exists (f[x0] - f[a] - (f[b] - f[a])/(g[b] - g[a])*(g[x0] - g[a])).
          rewrite H6. apply Classifier2. reflexivity.
        * intros ε J1. assert (J2 : ε/2 > 0). lra. apply I6 in J2 as J3.
          destruct J3 as [δ1[J3 J4]].
          assert (J5 : ∃ δ2, 0 < δ2 /\ ∀ x0 : R,0 < ∣(x0 - x)∣ < δ2 
            -> ∣((f[b] - f[a])/(g[b] - g[a]) * (g[x0] - g[x]))∣ < ε/2).
          { destruct classic with (P := (f[b] - f[a] = 0)) as [K1 | K1].
            - exists 1. split; try lra. intros x0 K2. rewrite K1. unfold Rdiv. 
              rewrite Rmult_0_l. rewrite Rmult_0_l. rewrite Abs_ge; try lra.
            - apply H2 in I1 as K2. destruct K2 as [K2 K3].
              destruct K3 as [K3[δ''[K4[K5 K6]]]].
              assert (K7 : ε/2 * ∣((g[b] - g[a])/(f[b] - f[a]))∣ > 0).
              { apply Rmult_gt_0_compat; auto. apply Abs_not_eq_0.
                apply Rmult_integral_contrapositive_currified; try lra. 
                apply Rinv_neq_0_compat. lra. } apply K6 in K7 as K8.
              destruct K8 as [δ2'[K9 K10]]. exists δ2'. split; try lra.
              intros x0 K11. apply K10 in K11 as K12.
              assert (K13 : 0 < ∣((f[b] - f[a])/(g[b] - g[a]))∣).
              { apply Abs_not_eq_0. apply Rmult_integral_contrapositive_currified;
                try lra. apply Rinv_neq_0_compat. lra. }
              apply Rmult_lt_compat_r with
                (r := ∣((f[b] - f[a])/(g[b] - g[a]))∣) in K12; try lra.
              assert (K14 : ε/2 * ∣((g[b] - g[a])/(f[b] - f[a]))∣ 
                * ∣((f[b] - f[a])/(g[b] - g[a]))∣ = ε/2 * (∣((g[b] - g[a])
                /(f[b] - f[a]))∣ * ∣((f[b] - f[a])/(g[b] - g[a]))∣)). field.
              rewrite K14 in K12. clear K14. rewrite <- Abs_mult in K12.
              rewrite <- Abs_mult in K12.
              assert (K14 : (g[b] - g[a])/(f[b] - f[a]) 
                * ((f[b] - f[a])/(g[b] - g[a])) = 1). { field. split; lra. }
              rewrite K14 in K12. clear K14. rewrite (Abs_ge 1) in K12; try lra.
              rewrite Rmult_1_r in K12.
              assert (K14 : (g[x0] - g[x]) * ((f[b] - f[a])/(g[b] - g[a])) 
                = (f[b] - f[a])/(g[b] - g[a]) * (g[x0] - g[x])). { field. lra. }
              rewrite K14 in K12. assumption. }
          destruct J5 as [δ2[J5 J6]].
          assert (J7 : ∃ δ, δ > 0 /\ δ < δ1 /\ δ < δ2).
          { destruct (Rlt_or_le δ1 δ2) as [K1 | K1].
            - exists (δ1/2). repeat split; lra.
            - exists (δ2/2). repeat split; lra. }
          destruct J7 as [δ[J7[J8 J9]]]. exists δ. split; try lra. intros x0 J10.
          assert (J11 : F[x0] - F[x] = f[x0] - f[x] - (f[b] - f[a])/(g[b] - g[a]) 
            * (g[x0] - g[x])). { rewrite H8. rewrite H8. field. lra. }
          rewrite J11. clear J11. generalize (Abs_minus_le (f[x0] - f[x])
            ((f[b] - f[a])/(g[b] - g[a]) * (g[x0] - g[x]))). intro J11. 
          assert (J12 : 0 < ∣(x0 - x)∣ < δ1). lra. apply J4 in J12. 
          assert (J13 : 0 < ∣(x0 - x)∣ < δ2). lra. apply J6 in J13. lra.
    - unfold ContinuousRight. split.
      + apply Classifier1. exists (f[a]-f[a]-(f[b]-f[a])/(g[b]-g[a])*(g[a]-g[a])). 
        rewrite H6. apply Classifier2. reflexivity.
      + unfold limit_pos. split; auto. unfold ContinuousRight in H9. 
        destruct H9 as [I2 I3]. unfold limit_pos in I3. 
        destruct I3 as [I3[δ'[I4[I5 I6]]]]. exists δ'. split; auto. split.
        * intros x0 J1. apply Classifier1. 
          exists (f[x0] - f[a] - (f[b] - f[a])/(g[b] - g[a]) * (g[x0] - g[a])).
          rewrite H6. apply Classifier2. reflexivity.
        * intros ε J1. assert (J2 : ε/2 > 0). lra. apply I6 in J2 as J3.
          destruct J3 as [δ1[J3 J4]].
          assert (J5 : ∃ δ2, 0 < δ2 /\ ∀ x, a < x < a + δ2 
            -> ∣((f[b] - f[a])/(g[b] - g[a]) * (g[x] - g[a]))∣ < ε/2).
          { destruct classic with (P := (f[b] - f[a] = 0)) as [K1 | K1].
            - exists 1. split; try lra. intros x0 K2. rewrite K1. unfold Rdiv. 
              rewrite Rmult_0_l. rewrite Rmult_0_l. rewrite Abs_ge; try lra.
            - destruct H11 as [K2 K3]. destruct K3 as [K3[δ''[K4[K5 K6]]]].
              assert (K7 : ε/2 * ∣((g[b] - g[a])/(f[b] - f[a]))∣ > 0).
              { apply Rmult_gt_0_compat; auto. apply Abs_not_eq_0.
                apply Rmult_integral_contrapositive_currified; try lra. 
                apply Rinv_neq_0_compat. lra. }
              apply K6 in K7 as K8. destruct K8 as [δ2'[K9 K10]]. exists δ2'. 
              split; try lra. intros x0 K11. apply K10 in K11 as K12.
              assert (K13 : 0 < ∣((f[b] - f[a])/(g[b] - g[a]))∣).
              { apply Abs_not_eq_0. apply Rmult_integral_contrapositive_currified;
                try lra. apply Rinv_neq_0_compat. lra. }
              apply Rmult_lt_compat_r with 
                (r := ∣((f[b] - f[a])/(g[b] - g[a]))∣) in K12; try lra.
              assert (K14 : ε/2 * ∣((g [b] - g [a])/(f[b] - f[a]))∣ 
                * ∣((f[b] - f[a])/(g[b] - g[a]))∣ = ε/2 * (∣((g[b] - g[a])
                /(f[b] - f[a]))∣ * ∣((f[b] - f[a])/(g[b] - g[a]))∣)). field.
              rewrite K14 in K12. clear K14. rewrite <- Abs_mult in K12.
              rewrite <- Abs_mult in K12.
              assert (K14 : (g[b] - g[a])/(f[b] - f[a]) 
                * ((f[b] - f[a])/(g[b] - g[a])) = 1). { field. split; lra. }
              rewrite K14 in K12. clear K14. rewrite (Abs_ge 1) in K12; try lra.
              rewrite Rmult_1_r in K12.
              assert (K14 : (g[x0] - g[a]) * ((f[b] - f[a])/(g[b] - g[a])) 
                = (f[b] - f[a])/(g[b] - g[a]) * (g[x0] - g[a])). { field. lra. }
              rewrite K14 in K12. assumption. }
          destruct J5 as [δ2[J5 J6]].
          assert (J7 : ∃ δ, δ > 0 /\ δ < δ1 /\ δ < δ2).
          { destruct (Rlt_or_le δ1 δ2) as [K1 | K1].
            - exists (δ1/2). repeat split; lra.
            - exists (δ2/2). repeat split; lra. }
          destruct J7 as [δ[J7[J8 J9]]]. exists δ. split; try lra. intros x0 J10.
          assert (J11:F[x0]-F[a]=f[x0]-f[a]-(f[b]-f[a])/(g[b]-g[a])*(g[x0]-g[a])).
          { rewrite H8. rewrite H8. field. lra. } rewrite J11. clear J11.
          generalize (Abs_minus_le (f[x0] - f[a]) ((f[b] - f[a])/(g[b] - g[a])
            * (g[x0] - g[a]))). intro J11. 
          assert (J12 : a < x0 < a + δ1). lra. apply J4 in J12. 
          assert (J13 : a < x0 < a + δ2). lra. apply J6 in J13. lra.
    - unfold ContinuousLeft. split.
      + apply Classifier1. exists (f[b]-f[a]-(f[b]-f[a])/(g[b]-g[a])*(g[b]-g[a])). 
        rewrite H6. apply Classifier2. reflexivity.
      + unfold limit_neg. split; auto. unfold ContinuousLeft in H10. 
        destruct H10 as [I2 I3]. unfold limit_neg in I3. 
        destruct I3 as [I3[δ'[I4[I5 I6]]]]. exists δ'. split; auto. split.
        * intros x0 J1. apply Classifier1. 
          exists (f[x0] - f[a] - (f[b] - f[a])/(g[b] - g[a]) * (g[x0] - g[a])).
          rewrite H6. apply Classifier2. reflexivity.
        * intros ε J1. assert (J2 : ε/2 > 0). lra. apply I6 in J2 as J3.
          destruct J3 as [δ1[J3 J4]].
          assert (J5 : ∃ δ2, 0 < δ2 /\ ∀ x, b - δ2 < x < b 
            -> ∣((f[b] - f[a])/(g[b] - g[a]) * (g[x] - g[b]))∣ < ε/2).
          { destruct classic with (P := (f[b] - f[a] = 0)) as [K1 | K1].
            - exists 1. split; try lra. intros x0 K2. rewrite K1. unfold Rdiv. 
              rewrite Rmult_0_l. rewrite Rmult_0_l. rewrite Abs_ge; try lra.
            - destruct H12 as [K2 K3]. destruct K3 as [K3[δ''[K4[K5 K6]]]].
              assert (K7 : ε/2 * ∣((g[b] - g[a])/(f[b] - f[a]))∣ > 0).
              { apply Rmult_gt_0_compat; auto. apply Abs_not_eq_0.
                apply Rmult_integral_contrapositive_currified; try lra. 
                apply Rinv_neq_0_compat. lra. } apply K6 in K7 as K8.
              destruct K8 as [δ2'[K9 K10]]. exists δ2'. split; try lra.
              intros x0 K11. apply K10 in K11 as K12.
              assert (K13 : 0 < ∣((f[b] - f[a])/(g[b] - g[a]))∣).
              { apply Abs_not_eq_0. apply Rmult_integral_contrapositive_currified;
                try lra. apply Rinv_neq_0_compat. lra. }
              apply Rmult_lt_compat_r with
                (r := ∣((f[b] - f[a])/(g[b] - g[a]))∣) in K12; try lra.
              assert (K14 : ε/2*∣((g[b] - g[a])/(f[b] - f[a]))∣*∣((f[b] - f[a])
                /(g[b] - g[a]))∣ = ε/2*(∣((g[b] - g[a])/(f [b] - f [a]))∣ 
                *∣((f[b] - f[a])/(g[b] - g[a]))∣)). field. rewrite K14 in K12. 
              clear K14. rewrite <- Abs_mult in K12. rewrite <- Abs_mult in K12.
              assert (K14 : (g[b] - g[a])/(f[b] - f[a]) 
                * ((f[b] - f[a])/(g[b] - g[a])) = 1). { field. split; lra. }
              rewrite K14 in K12. clear K14. rewrite (Abs_ge 1) in K12; try lra.
              rewrite Rmult_1_r in K12.
              assert (K14 : (g[x0] - g[b]) * ((f[b] - f[a])/(g[b] - g[a])) 
                = (f[b] - f[a])/(g[b] - g[a]) * (g[x0] - g[b])). { field. lra. }
              rewrite K14 in K12. assumption. }
          destruct J5 as [δ2[J5 J6]].
          assert (J7 : ∃ δ, δ > 0 /\ δ < δ1 /\ δ < δ2).
          { destruct (Rlt_or_le δ1 δ2) as [K1 | K1].
            - exists (δ1/2). repeat split; lra.
            - exists (δ2/2). repeat split; lra. }
          destruct J7 as [δ[J7[J8 J9]]]. exists δ. split; try lra. intros x0 J10.
          assert (J11:F[x0]-F[b]=f[x0]-f[b]-(f[b]-f[a])/(g[b]-g[a])*(g[x0]-g[b])).
          { rewrite H8. rewrite H8. field. lra. } rewrite J11. clear J11.
          generalize (Abs_minus_le (f[x0] - f[b]) 
            ((f[b] - f[a])/(g[b] - g[a]) * (g[x0] - g[b]))).
          intro J11. assert (J12 : b - δ1 < x0 < b). lra. apply J4 in J12. 
          assert (J13 : b - δ2 < x0 < b). lra. apply J6 in J13. lra. }
  assert (H14 : ∀ x, a < x < b -> Derivable F x).
  { intros x I1. apply H3 in I1 as I2. apply H4 in I1 as I20.
    destruct I2 as [y1'[I2[[δ1'[I3 I4]]I5]]].
    destruct I20 as [y2'[I21[[δ2'[I22 I23]]I24]]].
    exists (y1' - (f[b] - f[a])/(g[b] - g[a]) * y2'). split; auto. split.
    - exists δ1'. split; auto. intros x0 J1. apply Classifier1. rewrite H6.
      exists (f[x0] - f[a] - (f[b] - f[a])/(g[b] - g[a]) * (g[x0] - g[a])).
      apply Classifier2. reflexivity.
    - unfold limit. destruct I5 as [I5[δ0'[I6[I7 I8]]]]. 
      destruct I24 as [I24[δ3'[I25[I26 I27]]]]. split.
      + unfold Function. intros x0 y0 z0 J1 J2. applyClassifier2 J1; 
        applyClassifier2 J2. rewrite J2. assumption.
      + exists δ0'. split; auto. split.
        * intros x0 J1. apply Classifier1. exists ((F[x0] - F[x])/(x0 - x)).
          apply Classifier2. reflexivity.
        * intros ε J1. assert (J20 : ε/2 > 0). lra. apply I8 in J20 as J2.
          destruct J2 as [δ1[J2 J3]].
          destruct classic with (P := (f[b] - f[a] = 0)) as [L1 | L1].
          -- exists δ1. split; try lra. intros x0 J4.
             assert (J6 : \{\ λ x1 y, y = (F[x1] - F[x])/(x1 - x) \}\ [x0] 
               = (F[x0] - F[x])/(x0 - x)).
             { apply f_x_T.
               - intros x1 y1 z1 K1 K2. applyClassifier2 K1; applyClassifier2 K2.
                 rewrite K2. assumption.
               - apply Classifier2. reflexivity. }
             rewrite J6. clear J6. rewrite H8; rewrite H8. rewrite L1 in *. 
             unfold Rdiv. rewrite Rmult_0_l in *. rewrite Rmult_0_l in *. 
             rewrite Rmult_0_l in *. rewrite Rmult_0_l in *.
             assert (J5 : (f[x0] - f[a] - 0 - (f[x] - f[a] - 0)) 
               * /(x0 - x) - (y1' - 0) = (f[x0] - f[x])/(x0 - x) - y1').
             { field. destruct J4 as [J4 J5]. apply Abs_not_eq_0 in J4. 
               assumption. }
             rewrite J5. clear J5. apply J3 in J4.
             assert (J6 : \{\ λ x0 y, y = (f[x0] - f[x])/(x0 - x) \}\ [x0]
               = (f[x0] - f[x])/(x0 - x)). { rewrite FunValue; auto. }
             rewrite J6 in J4. lra.
          -- assert (J30 : ∣((g[b] - g[a])/(f[b] - f[a]))∣ * (ε/2) > 0).
             { apply Rmult_gt_0_compat; try lra. apply Abs_not_eq_0.
               apply Rmult_integral_contrapositive_currified; try lra.
               apply Rinv_neq_0_compat. lra. }
             apply I27 in J30 as J21. destruct J21 as [δ2[J21 J22]].
             assert (J25 : ∃ δ, 0 < δ /\ δ < δ1 /\ δ < δ2).
             { destruct (Rlt_or_le δ1 δ2) as [K1 | K1].
               - exists (δ1/2). repeat split; lra.
               - exists (δ2/2). repeat split; lra. }
             destruct J25 as [δ[J26[J23 J24]]]. exists δ. split; try lra.
             intros x0 J4.
             assert (J27 : 0 < ∣(x0 - x)∣ < δ1). lra.
             assert (J28 : 0 < ∣(x0 - x)∣ < δ2). lra. 
             apply J3 in J27 as J5. apply J22 in J28 as J29.
             assert (J6 : \{\ λ x0 y, y = (f[x0] - f[x])/(x0 - x) \}\ [x0]
               = (f[x0] - f[x])/(x0 - x)). { rewrite FunValue; auto. }
             rewrite J6 in J5. clear J6.
             assert (J6 : \{\ λ x0 y, y = (g[x0] - g[x])/(x0 - x) \}\ [x0]
               = (g[x0] - g[x])/(x0 - x)). { rewrite FunValue; auto. }
             rewrite J6 in J29. clear J6.
             assert (J6 : \{\ λ x1 y, y = (F[x1] - F[x])/(x1 - x) \}\ [x0] 
               = (F[x0] - F[x])/(x0 - x)). { rewrite FunValue; auto. }
             rewrite J6. clear J6. rewrite H8; rewrite H8.
             assert (J6 : (f[x0] - f[a] - (f[b] - f[a])/(g[b] - g[a]) 
               *(g[x0] - g[a]) - (f[x] - f[a] - (f[b] - f[a])/(g[b] - g[a]) 
               *(g[x] - g[a])))/(x0 - x) - (y1' - (f[b] - f[a])/(g[b] - g[a])*y2') 
               = (f[x0] - f[x])/(x0 - x) - y1' - ((f[b] - f[a])/(g[b] - g[a])
               *((g[x0] - g[x])/(x0 - x) - y2'))).
             { field. destruct J4 as [J4 K1]. apply Abs_not_eq_0 in J4. 
               split; lra. } rewrite J6. clear J6.
             generalize (Abs_minus_le ((f[x0] - f[x])/(x0 - x) - y1')
               ((f[b] - f[a])/(g[b] - g[a]) * ((g[x0] - g[x])/(x0 - x) - y2'))).
             intro J6. assert (J7 : 0 < ∣((f[b] - f[a])/(g[b] - g[a]))∣).
             { apply Abs_not_eq_0. apply Rmult_integral_contrapositive_currified; 
               auto. apply Rinv_neq_0_compat. lra. }
             apply Rmult_lt_compat_l with 
               (r := ∣((f[b] - f[a])/(g[b] - g[a]))∣) in J29; auto.
             rewrite <- Abs_mult in J29. rewrite <- Rmult_assoc in J29.
             rewrite <- Abs_mult in J29.
             assert (J31 : (f[b] - f[a])/(g[b] - g[a]) 
               * ((g[b] - g[a])/(f[b] - f[a])) = 1). { field. split; lra. }
             rewrite J31 in J29.
             assert (J32 : ∣(1)∣ * (ε/2) = ε/2). { rewrite Abs_gt; try lra. }
             rewrite J32 in J29. lra. }
  assert(H15 : F[a] = F[b]).
  { rewrite H8; rewrite H8. field. lra. } 
  generalize (Theorem6_1 F a b H0 H13 H14 H15). intros [ξ[H16 H17]]. exists ξ. 
  apply H3 in H16 as H18. unfold Derivable in H18. destruct H18 as [s H18].
  apply H4 in H16 as H19. destruct H19 as [t H19]. split; auto.
  assert (H21 : Derivative F ξ (s - (f[b] - f[a])/(g[b] - g[a]) * t)).
  { split; auto. split.
    - exists 1. split; try lra. intros x0 I1. rewrite H6. apply Classifier1.
      exists (f[x0] - f[a] - (f[b] - f[a])/(g[b] - g[a]) * (g[x0] - g[a])).
      apply Classifier2. reflexivity.
    - unfold limit. destruct H18 as [H18[[δ1'[I1 I2]]I3]].
      destruct I3 as [I3[δ0'[I4[I5 I6]]]]. 
      destruct H19 as [H19[[δ2'[I11 I12]]I13]].
      destruct I13 as [I13[δ3'[I14[I15 I16]]]]. split.
      + intros x1 y1 z1 J1 J2. applyClassifier2 J1; applyClassifier2 J2. rewrite J2. 
        assumption.
      + assert (I7 : ∃ δ4', δ4' > 0 /\ δ4' < δ0' /\ δ4' < δ3').
        { destruct (Rlt_or_le δ0' δ3') as [J1 | J1].
          - exists (δ0'/2). repeat split; lra.
          - exists (δ3'/2). repeat split; lra. } destruct I7 as [δ4'[I7[I8 I9]]].
        exists δ4'. repeat split; auto.
        * intros x0 J1. apply Classifier1. exists ((F[x0] - F[ξ])/(x0 - ξ)).
          apply Classifier2. reflexivity.
        * intros ε J1. assert (J7 : ε/2 > 0). lra. apply I6 in J7 as J2.
          destruct J2 as [δ0[J2 J3]].
          assert (J9 : ∃ δ1, δ1 > 0 /\ δ1 < δ0 /\ δ1 < δ4').
          { destruct (Rlt_or_le δ0 δ4') as [K1 | K1].
            - exists (δ0/2). repeat split; lra.
            - exists (δ4'/2). repeat split; lra. }
          destruct J9 as [δ1[J10[J11 J12]]].
          destruct classic with (P := (f[b] - f[a] = 0)) as [J8 | J8].
          -- exists δ1. split; try lra. intros x K1.
             assert (K2 : \{\ λ x0 y : R, y = (F[x0] - F[ξ])/(x0 - ξ) \}\ [x] 
               = (F[x] - F[ξ])/(x - ξ)). { rewrite FunValue; auto. } rewrite K2.
             assert (K3 : F[x] - F[ξ] = f[x] - f[ξ]).
             { rewrite H8; rewrite H8. rewrite J8. field. lra. } rewrite K3.
             assert (K4 : s - (f[b] - f[a])/(g[b] - g[a]) * t = s).
             { rewrite J8. field. lra. } rewrite K4. 
             assert (K5 : 0 < ∣(x - ξ)∣ < δ0). lra. apply J3 in K5.
             assert (K6 : \{\ λ x y, y = (f[x] - f[ξ])/(x - ξ) \}\ [x] 
               = (f[x] - f[ξ])/(x - ξ)). { rewrite FunValue; auto. }
             rewrite K6 in K5. lra.
          -- assert (J13 : ε/2 * ∣((g[b] - g[a])/(f[b] - f[a]))∣ > 0).
             { apply Rmult_gt_0_compat; auto. apply Abs_not_eq_0.
               apply Rmult_integral_contrapositive_currified; try lra.
               apply Rinv_neq_0_compat. assumption. } apply I16 in J13 as J14.
             destruct J14 as [δ2[J14 J15]].
             assert (J9 : ∃ δ, δ > 0 /\ δ < δ0 /\ δ < δ4' /\ δ < δ2).
             { destruct (Rlt_or_le δ0 δ4') as [K1 | K1].
               - destruct (Rlt_or_le δ0 δ2) as [K2 | K2].
                 + exists (δ0/2). repeat split; lra.
                 + exists (δ2/2). repeat split; lra.
               - destruct (Rlt_or_le δ4' δ2) as [K2 | K2].
                 + exists (δ4'/2). repeat split; lra.
                 + exists (δ2/2). repeat split; lra. }
             destruct J9 as [δ[J9[J16[J17 J18]]]]. exists δ. split; auto. 
             intros x J4. assert (J5 : 0 < ∣(x - ξ)∣ < δ0). lra. apply J3 in J5.
             assert (J6 : \{\ λ x y, y = (f[x] - f[ξ])/(x - ξ) \}\ [x]
               = (f[x] - f[ξ])/(x - ξ)). { rewrite FunValue; auto. }
             rewrite J6 in J5. clear J6.
             assert (J6 : \{\ λ x y, y = (F[x] - F[ξ])/(x - ξ) \}\ [x]
               = (F[x] - F[ξ])/(x - ξ)). { rewrite FunValue; auto. }
             rewrite J6. clear J6.
             assert (J19 : 0 < ∣(x - ξ)∣ < δ2). lra. apply J15 in J19.
             assert (J6 : \{\ λ x y, y = (g[x] - g[ξ])/(x - ξ) \}\ [x]
               = (g[x] - g[ξ])/(x - ξ)). { rewrite FunValue; auto. }
             rewrite J6 in J19. clear J6.
             assert (J6 : (F[x] - F[ξ])/(x - ξ) 
               - (s - (f[b] - f[a])/(g[b] - g[a]) * t) 
               = (f[x] - f[ξ])/(x - ξ) - s - (f[b] - f[a])/(g[b] - g[a])
               * ((g[x] - g[ξ])/(x - ξ) - t)).
             { rewrite H8. rewrite H8. field. destruct J4 as [J4 K1]. 
               apply Abs_not_eq_0 in J4. split; lra. } rewrite J6. clear J6.
             generalize (Abs_minus_le ((f[x] - f[ξ])/(x - ξ) - s) 
               ((f[b] - f[a])/(g[b] - g[a]) * ((g[x] - g[ξ])/(x - ξ) - t))).
             intro J20.
             assert (J21 : ∣((f[b] - f[a])/(g[b] - g[a]) 
               * ((g[x] - g[ξ])/(x - ξ) - t))∣ < ε/2).
             { rewrite Abs_mult. 
               assert (K1 : 0 < ∣((g[b] - g[a])/(f[b] - f[a]))∣).
               { apply Abs_not_eq_0. apply Rmult_integral_contrapositive_currified.
                 lra. apply Rinv_neq_0_compat. assumption. }
               apply Rmult_lt_reg_r with (r := ∣((g[b] - g[a])/(f[b] - f[a]))∣); 
               auto.
               assert (K2 : ∣((f[b] - f[a])/(g[b] - g[a]))∣ 
                 * ∣((g[x] - g[ξ])/(x - ξ) - t)∣ 
                 * ∣((g[b] - g[a])/(f[b] - f[a]))∣ 
                 = ∣((g[x] - g[ξ])/(x - ξ) - t)∣).
               { rewrite (Rmult_comm (∣((f[b] - f[a])/(g[b] - g[a]))∣)
                   (∣((g[x] - g[ξ])/(x - ξ) - t)∣)). rewrite Rmult_assoc. 
                 rewrite <- Abs_mult.
                 assert (L1:(f[b]-f[a])/(g[b]-g[a])*((g[b]-g[a])/(f[b]-f[a]))=1). 
                 { field. split; lra. } rewrite L1. rewrite (Abs_ge 1); lra. }
               rewrite K2. clear K2. assumption. }
             lra. }
  assert (H22 : s - (f[b] - f[a])/(g[b] - g[a]) * t = 0).
  { eapply DerivativeUnique; eauto. }
  assert (H23 : s = (f[b] - f[a])/(g[b] - g[a]) * t). lra.
  assert (H24 : t <> 0).
  { intro I1. assert (I2 : s = 0).
    { rewrite I1 in H23. rewrite Rmult_0_r in H23. assumption. } 
    eapply H5; eauto. } apply Rmult_eq_compat_r with (r := /t) in H23.
  assert (H25 : (f[b] - f[a])/(g[b] - g[a]) * t * /t
    = (f[b] - f[a])/(g[b] - g[a])). field; lra. rewrite H25 in H23.
  apply Corollary_DerivativeValue_a in H18. 
  apply Corollary_DerivativeValue_a in H19. rewrite H18. rewrite H19. assumption.
Qed.

(* 洛必达法则 *)
Theorem Theorem6_7 : ∀ f g x0 A, limit f x0 0 -> limit g x0 0
  -> (∃ δ', δ' > 0 /\ (∀ x, x ∈ Uº(x0; δ')
    -> Derivable f x /\ Derivable g x /\ g’[x] <> 0))
  -> limit \{\ λ x y, y = f’[x]/g’[x] \}\ x0 A
  -> limit \{\ λ x y, y = f[x]/g[x] \}\ x0 A.
Proof.
  intros f g x0 A H0 H1 [δ'[H2 H3]] H4.
  assert (H5 : ∃ f1, f1 = \{\ λ x y,
    (x <> x0 /\ y = f[x]) \/ (x = x0 /\ y = 0) \}\).
  { exists \{\ λ x y, (x <> x0 /\ y = f[x]) \/ (x = x0 /\ y = 0) \}\. 
    reflexivity. } destruct H5 as [f1 H5].
  assert (H6 : ∃ g1, g1 = \{\ λ x y, (x <> x0 /\ y = g[x]) 
    \/ (x = x0 /\ y = 0) \}\).
  { exists \{\ λ x y, (x <> x0 /\ y = g[x]) \/ (x = x0 /\ y = 0) \}\. 
    reflexivity. } destruct H6 as [g1 H6].
  assert (H8 : Uº(x0; δ') ⊂ dom[f]).
  { intros x I1. apply H3 in I1 as I2. destruct I2 as [I2 I3]. 
    destruct I2 as [y0' I2]. unfold Derivative in I2. 
    destruct I2 as [I2[[δ0'[I6 I4]]I5]]. apply I4. apply Classifier1. unfold Rminus.
    rewrite Rplus_opp_r. assert (I7 : ∣(0)∣ = 0).
    { apply Abs_ge. lra. }
    rewrite I7. assumption. }
  assert (H9 : Function f1).
  { intros x y z I1 I2. rewrite H5 in *. applyClassifier2 I1; applyClassifier2 I2.
    destruct I1 as [[I1 I3] | [I1 I3]].
    - destruct I2 as [[I2 I4] | [I2 I4]]; [lra | contradiction].
    - destruct I2 as [[I2 I4] | [I2 I4]]; [contradiction | lra]. }
  assert (H10 : Function g1).
  { intros x y z I1 I2. rewrite H6 in *. applyClassifier2 I1; applyClassifier2 I2.
    destruct I1 as [[I1 I3] | [I1 I3]].
    - destruct I2 as [[I2 I4] | [I2 I4]]; [lra | contradiction].
    - destruct I2 as [[I2 I4] | [I2 I4]]; [contradiction | lra]. }
  assert (H11 : ∀ x, x <> x0 -> f[x] = f1[x]).
  { intros x I1. symmetry. apply f_x_T; auto. rewrite H5. apply Classifier2. left. 
    split; auto. }
  assert (H12 : ∀ x, x <> x0 -> g[x] = g1[x]).
  { intros x I1. symmetry. apply f_x_T; auto. rewrite H6. apply Classifier2. left. 
    split; auto. }
  assert (H13 : f1[x0] = 0).
  { apply f_x_T; auto. rewrite H5. apply Classifier2. right. split; auto. }
  assert (H14 : g1[x0] = 0).
  { apply f_x_T; auto. rewrite H6. apply Classifier2. right. split; auto. }
  assert (H15 : ∀ x, x ∈ Uº(x0; δ')
    -> Derivative f1 x (f’[x]) /\ Derivative g1 x (g’[x])).
  { intros x I1. apply H3 in I1 as I2. destruct I2 as [[y1' I2][[y2' I3]I4]].
    apply Corollary_DerivativeValue_a in I2 as I11.
    apply Corollary_DerivativeValue_a in I3 as I12.
    destruct I2 as [I2[[δ1'[I5 I6]]I7]]. destruct I3 as [I3[[δ2'[I8 I9]]I10]].
    rewrite I11. rewrite I12. applyClassifier1 I1. destruct I1 as [I1 I13].
    apply Abs_not_eq_0 in I1 as I14.
    assert (I15 : Function \{\ λ x1 y, y = (f[x1] - f[x])/(x1 - x) \}\).
    { intros x1 y1 z1 K1 K2. applyClassifier2 K1; applyClassifier2 K2. 
      rewrite K2; assumption. }
    assert (I16 : Function \{\ λ x1 y, y = (f1[x1] - f1[x])/(x1 - x) \}\).
    { intros x1 y1 z1 K1 K2. applyClassifier2 K1; applyClassifier2 K2. 
      rewrite K2; assumption. }
    assert (I17 : Function \{\ λ x1 y, y = (g[x1] - g[x])/(x1 - x) \}\).
    { intros x1 y1 z1 K1 K2. applyClassifier2 K1; applyClassifier2 K2.
      rewrite K2; assumption. }
    assert (I18 : Function \{\ λ x1 y, y = (g1[x1] - g1[x])/(x1 - x) \}\).
    { intros x1 y1 z1 K1 K2. applyClassifier2 K1; applyClassifier2 K2.
      rewrite K2; assumption. } split.
    - split; auto. split.
      + exists δ1'. split; auto. intros x1 J1. apply Classifier1.
        destruct classic with (P := x1 = x0) as [J2 | J2].
        * exists 0. rewrite H5. apply Classifier2. right; split; auto.
        * exists f[x1]. rewrite H5. apply Classifier2. left; split; auto.
      + unfold limit. split; auto. destruct I7 as [I7[δ0'[J2[J3 J4]]]].
        exists δ0'. split; auto. split.
        * intros x1 K1. apply Classifier1. exists ((f1[x1] - f1[x])/(x1 - x)).
          apply Classifier2. reflexivity.
        * intros ε K1. apply J4 in K1 as K2. destruct K2 as [δ1[[K2 K3]K4]].
          generalize (Examp1 δ1 ∣(x - x0)∣ K2 I1). intros [δ[K5[K6 K7]]].
          exists δ. split; try lra. intros x1 K8.
          assert (K9 : \{\ λ x2 y, y = (f1[x2] - f1[x])/(x2 - x) \}\ [x1]
            = (f1[x1] - f1[x])/(x1 - x)).
          { apply f_x_T; auto. apply Classifier2. reflexivity. } rewrite K9.
          assert (K10 : 0 < ∣(x1 - x)∣ < δ1). lra. apply K4 in K10 as K11.
          assert (K12 : \{\ λ x0 y, y = (f[x0] - f[x])/(x0 - x) \}\ [x1]
            = (f[x1] - f[x])/(x1 - x)).
          { apply f_x_T; auto. apply Classifier2. reflexivity. }
          rewrite K12 in K11. clear K12.
          assert (K12 : x1 <> x0).
          { intros L1. rewrite L1 in K8. rewrite Abs_eq_neg in K7.
            rewrite Ropp_minus_distr in K7. lra. }
          rewrite <- H11; auto. rewrite <- H11; auto. lra.
    - split; auto. split.
      + exists δ2'. split; auto. intros x1 J1. apply Classifier1.
        destruct classic with (P := x1 = x0) as [J2 | J2].
        * exists 0. rewrite H6. apply Classifier2. right; split; auto.
        * exists g[x1]. rewrite H6. apply Classifier2. left; split; auto.
      + unfold limit. split; auto. destruct I10 as [I10[δ0'[J2[J3 J4]]]]. 
        exists δ0'. split; auto. split.
        * intros x1 K1. apply Classifier1. exists ((g1[x1] - g1[x])/(x1 - x)).
          apply Classifier2. reflexivity.
        * intros ε K1. apply J4 in K1 as K2. destruct K2 as [δ1[[K2 K3]K4]].
          generalize (Examp1 δ1 ∣(x - x0)∣ K2 I1). intros [δ[K5[K6 K7]]].
          exists δ. split; try lra. intros x1 K8.
          assert (K9 : \{\ λ x2 y, y = (g1[x2] - g1[x])/(x2 - x) \}\ [x1]
            = (g1[x1] - g1[x])/(x1 - x)).
          { apply f_x_T; auto. apply Classifier2. reflexivity. } rewrite K9.
          assert (K10 : 0 < ∣(x1 - x)∣ < δ1). lra. apply K4 in K10 as K11.
          assert (K12 : \{\ λ x0 y, y = (g[x0] - g[x])/(x0 - x) \}\ [x1]
            = (g[x1] - g[x])/(x1 - x)).
          { apply f_x_T; auto. apply Classifier2. reflexivity. }
          rewrite K12 in K11. clear K12.
          assert (K12 : x1 <> x0).
          { intros L1. rewrite L1 in K8. rewrite Abs_eq_neg in K7.
            rewrite Ropp_minus_distr in K7. lra. }
          rewrite <- H12; auto. rewrite <- H12; auto. lra. }
  assert (H16 : ∀ x, x ∈ Uº(x0; δ') -> Continuous f1 x /\ Continuous g1 x).
  { intros x I1. apply H15 in I1 as [I1 I2]. split; apply Theorem5_1; auto;
    [exists (f’[x]) | exists (g’[x])]; auto. }
  assert (H17 : limit f1 x0 0).
  { destruct H0 as [H0[δ0'[I2[I3 I4]]]]. split; auto. exists δ0'. split; auto.
    split.
    - intros x1 J1. applyClassifier1 J1. apply Classifier1. exists f[x1]. rewrite H5. 
      apply Classifier2. left. apply Examp4 in J1. split; lra.
    - intros ε I5. apply I4 in I5 as I6. destruct I6 as [δ[I6 I7]]. exists δ. 
      split; auto. intros x1 I8. apply Examp4 in I8 as I10.
      assert (I9 : x1 <> x0). lra. rewrite <- H11; auto. }
  assert (H18 : limit g1 x0 0).
  { destruct H1 as [H1[δ0'[I2[I3 I4]]]]. split; auto. exists δ0'. split; auto.
    split.
    - intros x1 J1. applyClassifier1 J1. apply Classifier1. exists g[x1]. rewrite H6.
      apply Classifier2. left. apply Examp4 in J1. split; lra.
    - intros ε I5. apply I4 in I5 as I6. destruct I6 as [δ[I6 I7]]. exists δ. 
      split; auto. intros x1 I8. apply Examp4 in I8 as I10.
      assert (I9 : x1 <> x0). lra. rewrite <- H12; auto. }
  assert (H19 : ∀ x, x ∈ Uº(x0; δ') -> g1[x] <> 0).
  { intros x I1 I2. apply H16 in I1 as I5. destruct I5 as [I5 I6]. 
    applyClassifier1 I1. destruct I1 as [I3 I4]. apply Abs_R in I4. 
    apply Abs_not_eq_0 in I3. apply Rdichotomy in I3 as [I3 | I3].
    - assert (J1 : ContinuousClose g1 x x0).
      { split; [idtac | split].
        - intros x1 K1. assert (K2 : x1 ∈ Uº(x0; δ')).
          { apply Classifier1. split.
            - apply Abs_not_eq_0. lra.
            - apply Abs_R. lra. } apply H16 in K2 as [K2 K3]. assumption.
        - destruct I6 as [I6 I7]. split; auto. apply Theorem3_1. assumption.
        - split.
          + apply Classifier1. exists 0. rewrite H6. apply Classifier2. right. 
            split; reflexivity.
          + apply Theorem3_1. rewrite H14. assumption. }
      assert (J2 : ∀ x1, x < x1 < x0 -> Derivable g1 x1).
      { intros x1 K1. exists (g’[x1]). apply H15. apply Classifier1. split.
        - apply Abs_not_eq_0. lra.
        - apply Abs_R. lra. }
      assert (J3 : g1[x] = g1[x0]). lra. assert (J4 : x < x0). lra.
      generalize (Theorem6_1 g1 x x0 J4 J1 J2 J3). intros [ξ[J5 J6]].
      assert (J7 : ξ ∈ Uº(x0; δ')).
      { apply Classifier1. split.
        - apply Abs_not_eq_0. lra.
        - apply Abs_R. lra. } apply H3 in J7 as J8. destruct J8 as [J8[J9 J10]].
      apply J10. apply H15 in J7 as [J11 J12]. eapply DerivativeUnique; eauto.
    - assert (J1 : ContinuousClose g1 x0 x).
      { split; [idtac | split].
        - intros x1 K1. assert (K2 : x1 ∈ Uº(x0; δ')).
          { apply Classifier1. split. apply Abs_not_eq_0. lra. apply Abs_R. lra. }
          apply H16 in K2 as [K2 K3]. assumption.
        - split.
          + apply Classifier1. exists 0. rewrite H6. apply Classifier2. right. 
            split; reflexivity.
          + apply Theorem3_1. rewrite H14. assumption.
        - destruct I6 as [I6 I7]. split; auto. apply Theorem3_1. assumption. }
      assert (J2 : ∀ x1, x0 < x1 < x -> Derivable g1 x1).
      { intros x1 K1. exists (g’[x1]). apply H15. apply Classifier1. split.
        - apply Abs_not_eq_0. lra.
        - apply Abs_R. lra. }
      assert (J3 : g1[x0] = g1[x]). lra. assert (J4 : x0 < x). lra.
      generalize (Theorem6_1 g1 x0 x J4 J1 J2 J3). intros [ξ[J5 J6]].
      assert (J7 : ξ ∈ Uº(x0; δ')).
      { apply Classifier1. split.
        - apply Abs_not_eq_0. lra.
        - apply Abs_R. lra. } apply H3 in J7 as J8. destruct J8 as [J8[J9 J10]].
      apply J10. apply H15 in J7 as [J11 J12]. eapply DerivativeUnique; eauto. }
  assert (H20 : ∀ x, x0 < x < x0 + δ' 
    -> ∃ ξ, x0 < ξ < x /\ f[x]/g[x] = f’[ξ]/g’[ξ]).
  { intros x I1.
    assert (I2 : ContinuousClose f1 x0 x).
    { split; [idtac | split].
      - intros x1 J1.
        assert (J2 : x1 ∈ Uº(x0; δ')).
        { apply Classifier1. assert (K1 : x1 - x0 > 0). lra. rewrite Abs_gt; auto. 
          split; lra. } apply H16 in J2 as [J2 J3]. assumption.
      - destruct H0 as [H0[δ0'[I2[I3 I4]]]]. split.
        + apply Classifier1. exists 0. rewrite H5. apply Classifier2. right. 
          split; reflexivity.
        + rewrite H13. apply Theorem3_1. assumption.
      - split.
        + apply Classifier1. exists f[x]. rewrite H5. apply Classifier2. left; split; lra.
        + assert (I2 : x ∈ Uº(x0; δ')).
          { apply Classifier1. split.
            - apply Abs_not_eq_0. lra.
            - apply Abs_R. lra. } apply H16 in I2 as I3. destruct I3 as [I3 I4].
          destruct I3 as [I3 I5]. apply Theorem3_1. assumption. }
    assert (I3 : ContinuousClose g1 x0 x).
    { split; [idtac | split].
      - intros x1 J1.
        assert (J2 : x1 ∈ Uº(x0; δ')).
        { apply Classifier1. assert (K1 : x1 - x0 > 0). lra. rewrite Abs_gt; auto. 
          split; lra. } apply H16 in J2 as [J2 J3]. assumption.
      - destruct H1 as [H1[δ0'[I10[I3 I4]]]]. split.
        + apply Classifier1. exists 0. rewrite H6. apply Classifier2. right. 
          split; reflexivity.
        + rewrite H14. apply Theorem3_1. assumption.
      - split.
        + apply Classifier1. exists g[x]. rewrite H6. apply Classifier2. left; split; lra.
        + assert (I10 : x ∈ Uº(x0; δ')).
          { apply Classifier1. split.
            - apply Abs_not_eq_0. lra.
            - apply Abs_R. lra. } apply H16 in I10 as I3. destruct I3 as [I3 I4].
          destruct I4 as [I4 I5]. apply Theorem3_1. assumption. }
    assert (I4 : ∀ x1, x0 < x1 < x -> Derivable f1 x1).
    { intros x1 J1. exists (f’[x1]). apply H15. apply Classifier1. split.
      - apply Abs_not_eq_0; lra.
      - apply Abs_R. lra. }
    assert (I5 : ∀ x1, x0 < x1 < x -> Derivable g1 x1).
    { intros x1 J1. exists (g’[x1]). apply H15. apply Classifier1. split.
      - apply Abs_not_eq_0; lra.
      - apply Abs_R. lra. }
    assert (I6 : ∀ x1, x0 < x1 < x -> ~(f1’[x1] = 0 /\ g1’[x1] = 0)).
    { intros x1 J1 [J2 J3].
      assert (J4 : x1 ∈ Uº(x0; δ')).
      { apply Classifier1. split.
        - apply Abs_not_eq_0. lra.
        - apply Abs_R. lra. } apply H15 in J4 as J8. destruct J8 as [J8 J9].
      apply H3 in J4 as [J5[J6 J7]]. apply J7. 
      apply Corollary_DerivativeValue_a in J9. rewrite J9 in J3. assumption. }
    assert (I7 : g1[x] <> g1[x0]).
    { rewrite H14. apply H19. apply Classifier1. split.
      - apply Abs_not_eq_0; lra.
      - apply Abs_R. lra. }
    destruct I1 as [I1 I8]. 
    generalize (Theorem6_6 f1 g1 x0 x I1 I2 I3 I4 I5 I6 I7).
    intros [ξ[I9 I10]]. exists ξ. split; auto. rewrite H13 in I10. 
    rewrite H14 in I10. assert (I11 : x <> x0). lra. apply H12 in I11 as I13. 
    apply H11 in I11 as I12. rewrite I12; rewrite I13.
    assert (I14 : ξ ∈ Uº(x0; δ')).
    { apply Classifier1. split.
      - apply Abs_not_eq_0; lra.
      - apply Abs_R. lra. }
    apply H15 in I14 as I15. destruct I15 as [I15 I16].
    apply Corollary_DerivativeValue_a in I15; 
    apply Corollary_DerivativeValue_a in I16. rewrite <- I15; rewrite <- I16.
    rewrite Rminus_0_r in I10. rewrite Rminus_0_r in I10. symmetry. assumption. }
  assert (H21 : ∀ x, x0 - δ' < x < x0  
    -> ∃ ξ, x < ξ < x0 /\ f[x]/g[x] = f’[ξ]/g’[ξ]).
  { intros x I1. 
    assert (I2 : ContinuousClose f1 x x0).
    { split; [idtac | split].
      - intros x1 J1.
        assert (J2 : x1 ∈ Uº(x0; δ')).
        { apply Classifier1. assert (K1 : x1 - x0 < 0). lra.  rewrite Abs_lt; auto. 
          split; lra. } apply H16 in J2 as [J2 J3]. assumption.
      - split.
        + apply Classifier1. exists f[x]. rewrite H5. apply Classifier2. left; split; lra.
        + assert (I2 : x ∈ Uº(x0; δ')).
          { apply Classifier1. split.
            - apply Abs_not_eq_0. lra.
            - apply Abs_R. lra. } apply H16 in I2 as I3. destruct I3 as [I3 I4].
          destruct I3 as [I3 I5]. apply Theorem3_1. assumption.
      - destruct H0 as [H0[δ0'[I2[I3 I4]]]]. split.
        + apply Classifier1. exists 0. rewrite H5. apply Classifier2. right. 
          split; reflexivity.
        + rewrite H13. apply Theorem3_1. assumption. }
    assert (I3 : ContinuousClose g1 x x0).
    { split; [idtac | split].
      - intros x1 J1.
        assert (J2 : x1 ∈ Uº(x0; δ')).
        { apply Classifier1. assert (K1 : x1 - x0 < 0). lra. rewrite Abs_lt; auto. 
          split; lra. } apply H16 in J2 as [J2 J3]. assumption.
      - split.
        + apply Classifier1. exists g[x]. rewrite H6. apply Classifier2. left; split; lra.
        + assert (I10 : x ∈ Uº(x0; δ')).
          { apply Classifier1. split.
            - apply Abs_not_eq_0. lra.
            - apply Abs_R. lra. } apply H16 in I10 as I3. destruct I3 as [I3 I4].
          destruct I4 as [I4 I5]. apply Theorem3_1. assumption.
      - destruct H1 as [H1[δ0'[I10[I3 I4]]]]. split.
        + apply Classifier1. exists 0. rewrite H6. apply Classifier2. right. 
          split; reflexivity.
        + rewrite H14. apply Theorem3_1. assumption. }
    assert (I4 : ∀ x1, x < x1 < x0 -> Derivable f1 x1).
    { intros x1 J1. exists (f’[x1]). apply H15. apply Classifier1. split.
      - apply Abs_not_eq_0; lra.
      - apply Abs_R. lra. }
    assert (I5 : ∀ x1, x < x1 < x0 -> Derivable g1 x1).
    { intros x1 J1. exists (g’[x1]). apply H15. apply Classifier1. split.
      - apply Abs_not_eq_0; lra.
      - apply Abs_R. lra. }
    assert (I6 : ∀ x1, x < x1 < x0 -> ~(f1’[x1] = 0 /\ g1’[x1] = 0)).
    { intros x1 J1 [J2 J3].
      assert (J4 : x1 ∈ Uº(x0; δ')).
      { apply Classifier1. split.
        - apply Abs_not_eq_0. lra.
        - apply Abs_R. lra. } apply H15 in J4 as J8. destruct J8 as [J8 J9].
      apply H3 in J4 as [J5[J6 J7]]. apply J7. 
      apply Corollary_DerivativeValue_a in J9. rewrite J9 in J3. assumption. }
    assert (I7 : g1[x0] <> g1[x]).
    { rewrite H14. apply not_eq_sym. apply H19. apply Classifier1. split.
      - apply Abs_not_eq_0; lra.
      - apply Abs_R. lra. } destruct I1 as [I1 I8].
    generalize (Theorem6_6 f1 g1 x x0 I8 I2 I3 I4 I5 I6 I7). intros [ξ[I9 I10]].
    exists ξ. split; auto. rewrite H13 in I10. rewrite H14 in I10.
    assert (I11 : x <> x0). lra.
    apply H12 in I11 as I13. apply H11 in I11 as I12. rewrite I12; rewrite I13.
    assert (I14 : ξ ∈ Uº(x0; δ')).
    { apply Classifier1. split.
      - apply Abs_not_eq_0; lra.
      - apply Abs_R. lra. } apply H15 in I14 as I15. destruct I15 as [I15 I16].
    apply Corollary_DerivativeValue_a in I15; 
    apply Corollary_DerivativeValue_a in I16. rewrite <- I15; rewrite <- I16.
    assert (I17 : (0 - f1[x])/(0 - g1[x]) = f1[x]/g1[x]).
    { field. apply H19. apply Classifier1. split.
      - apply Abs_not_eq_0; lra.
      - apply Abs_R. lra. } rewrite I17 in I10. symmetry. assumption. }
  assert (H22 : Function \{\ λ x y, y = f[x]/g[x] \}\).
  { intros x1 y1 z1 I1 I2. applyClassifier2 I1. applyClassifier2 I2. rewrite I2.
    assumption. } split; auto. unfold limit in H4. 
  destruct H4 as [H4[δ1'[H23[H24 H25]]]]. exists δ1'. split; try lra. split.
  - intros x1 I1. apply Classifier1. exists (f[x1]/g[x1]). apply Classifier2. reflexivity.
  - intros ε I1. apply H25 in I1 as I2. destruct I2 as [δ[[I2 I3]I4]].
    generalize (Examp1 δ' δ H2 I2). intros [δ1[I5[I6 I7]]]. exists δ1. 
    split; try lra. intros x I8. apply Examp4 in I8 as I9. destruct I9 as [I9 I10].
    assert (I11 : \{\ λ x1 y, y = f[x1]/g[x1] \}\ [x] = f[x]/g[x]).
    { apply f_x_T; auto. apply Classifier2. reflexivity. } rewrite I11.
    assert (I12 : ∀ x, \{\ λ x0 y, y = f’[x0]/g’[x0] \}\ [x] = f’[x]/g’[x]).
    { intro x1. apply f_x_T; auto. apply Classifier2. reflexivity. }
    apply Rdichotomy in I9 as [I9 | I9].
    + assert (J1 : x0 - δ' < x < x0). lra. apply H21 in J1 as J2. 
      destruct J2 as [ξ[J2 J3]]. rewrite J3. assert (J4 : 0 < ∣(ξ - x0)∣ < δ).
      { split.
        - apply Abs_not_eq_0; lra.
        - apply Abs_R. lra. } apply I4 in J4. rewrite I12 in J4. assumption.
    + assert (J1 : x0 < x < x0 + δ'). lra. apply H20 in J1 as J2. 
      destruct J2 as [ξ[J2 J3]]. rewrite J3. assert (J4 : 0 < ∣(ξ - x0)∣ < δ).
      { split.
        - apply Abs_not_eq_0; lra.
        - apply Abs_R. lra. } apply I4 in J4. rewrite I12 in J4. assumption.
Qed.

(* 单边局部保号性 *)
Lemma Lemma6_8a : ∀ f x0 A, limit_pos f x0 A -> A > 0
  -> (∀ r, 0 < r < A -> (∃ δ, δ > 0 /\ (∀ x, x ∈ U+º(x0; δ) -> 0 < r < f[x]))).
Proof.
  intros f x0 A H0 H1 r H2. destruct H0 as [H0[δ'[H3[H4 H5]]]].
  assert (H6 : A - r > 0). lra. apply H5 in H6 as H7. destruct H7 as [δ[H7 H8]]. 
  exists δ. split; try lra. intros x H9. applyClassifier1 H9. apply H8 in H9 as H10. 
  apply Abs_R in H10. lra.
Qed.

Lemma Lemma6_8b : ∀ f (x0 A: R), (∃ δ', δ' > 0 /\ U+º(x0; δ') ⊂ dom[f] 
    /\ (∀ x, x ∈ U+º(x0; δ') -> f[x] <> 0)) -> limit_infinite_pos f x0 
  -> limit_pos (A /// f) x0 0.
Proof.
  intros. destruct H as [δ'[H[H1 H2]]]. red in H0. 
  destruct H0 as [L1[δ1'[L2[L3 H0]]]]. red.
  assert(L0:Function (A /// f)).
  { unfold Function. intros x y z I1 I2. applyClassifier2 I1; applyClassifier2 I2.
    destruct I2 as [I2[I3 I4]]. rewrite I4. apply I1. } split; auto.
  exists δ'. repeat split; auto.
  - intros z H3. apply Classifier1. exists (A/f[z]). apply Classifier2. 
    repeat split; auto. 
  - intros. destruct (classic (A = 0)).
    + pose proof (Examp1 δ'). apply H5 in H as H5'; auto. clear H5. 
      destruct H5' as [δ[H6[H7 H8]]]. exists δ. split; auto. intros. 
      assert ((A /// f) [x] = A/f[x]). 
      { apply f_x_T; auto. apply Classifier2. repeat split; auto. apply H1. 
        apply Classifier1; lra. apply H2; apply Classifier1; lra. } 
      rewrite H9. rewrite H4. unfold Rdiv. rewrite Rmult_0_l. apply Abs_R. lra.
    + assert (∣(A)∣/ε > 0).
      { unfold Rdiv. apply Rinv_0_lt_compat in H3. apply Rmult_gt_0_compat; auto.
        apply Abs_not_eq_0; auto. }
      apply H0 in H5. destruct H5 as [δ1[[H7 H8]H9]]. pose proof (Examp2 δ' δ1). 
      apply H5 in H as H4'; auto. clear H5. destruct H4' as [δ[H5'[H5 H6]]].  
      exists  δ. split; auto. intros. cut(f[x] <> 0). intros.
      assert ((A /// f) [x] = A/f[x]). 
      { apply f_x_T; auto. apply Classifier2. repeat split; auto. apply H1. 
        apply Classifier1; lra. } 
      rewrite H12. rewrite Rminus_0_r. cut(x0 < x < x0 + δ1). intros. 
      apply H9 in H13. rewrite Abs_div; auto. unfold Rdiv. 
      apply (Rmult_lt_reg_r (∣(f[x])∣)); auto. apply Abs_not_eq_0; auto. 
      rewrite Rmult_assoc; rewrite Rinv_l; unfold Rdiv in H13.
      apply (Rmult_lt_compat_r ε) in H13; auto. rewrite Rmult_assoc in H13; 
      rewrite Rinv_l in H13; lra. apply Abs_not_eq_0 in H11 as H11';lra. lra. 
      apply H2; apply Classifier1; lra.
Qed.

Theorem Theorem6_8 : ∀ f g x0 A, (∃ δ', δ' > 0 /\ (∀ x, x ∈ U+º(x0; δ') 
    -> Derivable f x /\ Derivable g x /\ g’[x] <> 0))
  -> limit_infinite_pos g x0 -> limit_pos \{\ λ x y, y = f’[x]/g’[x] \}\ x0 A
  -> limit_pos \{\ λ x y, y = f[x]/g[x] \}\ x0 A.
Proof.
  intros. destruct H as [δ'[H2 H3]]. red in H1.
  destruct H1 as [J1[δ1'[J2 [J3 J4]]]]. red. split. red; intros. applyClassifier2 H; 
  applyClassifier2 H1. subst; auto. exists δ'. split; auto. split.
  - intros z H4. apply Classifier1. exists (f[z]/g[z]). apply Classifier2; auto.
  - intros. cut ((ε/2) > 0). intros. apply J4 in H1 as J5. clear J4.
    destruct J5 as [δ1[J4 J5]]. destruct J4 as [J4 J4']. pose proof H0 as H0'.
    red in H0. destruct H0 as [_[δ2'[K2[K3 K4]]]]. assert(1>0). lra. 
    apply K4 in H0. destruct H0 as [δ2[[K5 K5']K6]].
    assert (K1 : ∃ x1, x0 < x1 < x0 + δ' /\ x1 < x0 + δ1 /\ x1 < x0 + δ2).
    { pose proof (Examp3 δ' δ1 δ2). apply H0 in H2 as H2''; auto. clear H0.
      destruct H2'' as [δx[L1[L2[L3 L4]]]]. exists (x0+δx). split; lra. }
    destruct K1 as [x1[[K1 K3']K4']]. clear K4.
    assert (K4 : ∀ x1, x0 < x1 < x0 + δ2 -> g[x1] <> 0).
    { intros. destruct (classic (g[x2] = 0)). apply K6 in H0. 
      apply Abs_eq_0 in H4. rewrite H4 in H0; lra. lra. }  
    assert (I8 : ∃ g1, g1 = \{\ λ x y, y = g[x]/(g[x] - g[x1]) \}\).
    { exists \{\ λ x y, y = g[x]/(g[x] - g[x1]) \}\; auto. }
    destruct I8 as [g1 I8]. 
    assert (I8' : ∀ x, g1[x] = g[x]/(g[x] - g[x1])).
    { intros. rewrite I8. rewrite FunValue; auto. }
    assert (I6 : ∀ x, x0 < x < x1 -> g[x] <> g[x1]).
    { intros. destruct (classic (g[x] = g[x1])).
      assert (∃ ξ, x < ξ < x1 /\ Derivative g ξ 0).
      { apply Theorem6_1; auto. lra. 
        - red. split; [idtac | split]; auto.
          + red. intros. apply Theorem5_1.
            assert (H21 : x2 ∈ U+º(x0; δ')). { apply Classifier1; lra. } 
            apply H3 in H21 as H24'; tauto.
          + assert (H19 : x ∈ U+º(x0; δ')). apply Classifier1; lra. 
            apply H3 in H19. destruct H19 as [_[H19 _]]. apply Theorem5_1 in H19. 
            apply Theorem4_1 in H19; tauto.
          + assert (H19 : x1 ∈ U+º(x0; δ')). apply Classifier1; lra. 
            apply H3 in H19. destruct H19 as [_[H19 _]]. apply Theorem5_1 in H19. 
            apply Theorem4_1 in H19; tauto.
        - intros. cut (x2 ∈ U+º(x0; δ')). intros. apply H3 in H6. 
          tauto. apply Classifier1; lra. }
      destruct H5 as [ξ[H5 H5']]. cut (ξ ∈ U+º(x0; δ')). intros. 
      apply H3 in H6. apply Corollary_DerivativeValue_a in H5'. lra. 
      apply Classifier1;lra. auto. } 
    assert (I9 : limit_pos g1 x0 1).
    { red. repeat split. rewrite I8. red; intros. applyClassifier2 H0; 
      applyClassifier2 H4. subst; auto. red in H0'. 
      destruct H0' as [L1[δ3'[L3[L4 L5]]]]. exists δ'. repeat split; auto. 
      intros z H0. rewrite I8. apply Classifier1. exists (g[z]/(g[z] - g[x1])). 
      apply Classifier2;auto. intros. assert(∣(g[x1])∣/ε0 + ∣(g[x1])∣ > 0).
      { apply Rplus_lt_0_compat. 
        - unfold Rdiv. apply Rmult_gt_0_compat. apply Abs_not_eq_0; auto. 
          apply K4; lra. apply Rinv_0_lt_compat; auto. 
        - apply Abs_not_eq_0; auto. apply K4; lra. } 
      apply L5 in H4. destruct H4 as [δ3[[H5 H6]H7]].
      pose proof (Examp3 δ' δ3 (x1-x0)). apply H4 in H2 as H4'; auto. clear H4. 
      destruct H4' as [δ[H8[H9[H10[H11 H12]]]]]. exists δ. split; auto. intros. 
      assert (x0 < x < x0 + δ3). lra. assert (g [x] <> g [x1]). { apply I6; lra. }
      apply H7 in H13. rewrite I8'. 
      replace (g[x]/(g[x] - g[x1]) - 1) with (g[x1]/(g[x] - g[x1])).
      rewrite Abs_div. unfold Rdiv. apply (Rmult_lt_reg_r ∣(g[x] - g[x1])∣). 
      apply Abs_not_eq_0; lra. rewrite Rmult_assoc; rewrite Rinv_l. 
      rewrite Rmult_1_r. apply (Rmult_gt_reg_l (/ε0)). apply Rinv_0_lt_compat; 
      auto. rewrite <- Rmult_assoc. rewrite Rinv_l. rewrite Rmult_1_l. 
      generalize (Abs_abs_minus' g[x] g[x1]). intro; lra. lra.  
      apply Rminus_eq_contra in H14; apply Abs_not_eq_0 in H14; lra. lra.
      assert (∀ a b, a <> b -> a/(b-a) = b/(b-a) - 1).
      { intros. cut ((b - a)/(b - a) = 1). intros. rewrite <- H16. lra. 
        unfold Rdiv. apply Rinv_r. lra. } apply H15; auto. lra. }
    assert (H0 : (∀ r, 0 < r < 1 -> (∃ δ, δ > 0 /\ 
      (∀ x, x ∈ (U+º(x0; δ)) -> 0 < r < g1[x])))). 
    { apply Lemma6_8a; auto. lra. } pose proof (H0 (1/2)).  
    assert (H5 : 0 < 1/2 < 1). lra. apply H4 in H5. destruct H5 as [δ3[H13 H13']].
    clear H0 H4. pose proof (Examp2 (x1 - x0) δ3 δ2) as H0. 
    assert (x1 - x0>0). lra. apply H0 in H4 as H4'; auto. clear H0. 
    destruct H4' as [δ0[H5[H6[H7 H7']]]].
    assert (L3 : limit_pos (f[x1] /// g) x0 0).
    { apply (Lemma6_8b g x0 f[x1]); auto. unfold limit_infinite_pos in H0'. 
      destruct H0' as [_[δ5'[Ll[L1' _]]]]. pose proof (Examp2 δ' δ2 δ5'). 
      apply H0 in H2 as H'; auto. clear H0. destruct H' as [δ[L2[L3[L4 L5]]]]. 
      exists δ. split; auto. split. intros z H8. apply L1'. apply Classifier1.
      applyClassifier1 H8. lra. intros. assert (x0 < x < x0 + δ2). applyClassifier1 H0. 
      lra. apply K6 in H8. apply  Abs_not_eq_0. lra. }
    assert (I10 : ∃ h1, h1 = \{\ λ x y, y 
      = (ε/2 + A) * ((g[x] - g[x1])/g[x]) + f[x1]/g[x]\}\).
    { exists \{\ λ x y, y = (ε/2 + A) * ((g[x] - g[x1])/g[x]) + f[x1]/g[x] \}\; 
      auto. } destruct I10 as [h1 H10].
    assert (I10' : ∀ x, h1[x] = (ε/2 + A) * ((g[x] - g[x1])/g[x]) + f[x1]/g[x]).
    { intros. rewrite H10. rewrite FunValue; auto. }
    assert (I12 : ∃ h2, h2 
      = \{\ λ x y, y = (-(ε/2) + A) * ((g[x] - g[x1])/g[x]) + f[x1]/g[x]\}\).
    { exists \{\ λ x y, y = (-(ε/2) + A) * ((g[x] - g[x1])/g[x]) + f[x1]/g[x]\}\; 
      auto. } destruct I12 as [h2 H12].
    assert (I12': ∀ x, h2[x] = (-(ε/2) + A) * ((g[x] - g[x1])/g[x]) + f[x1]/g[x]).
    { intros. rewrite H12. rewrite FunValue; auto. }
    assert (I11 : ∃ f1, f1 = \{\ λ x y, y = f[x]/g[x] \}\).
    { exists \{\ λ x y, y = f[x]/g[x] \}\; auto. } destruct I11 as [f1 I11]. 
    assert (I11' : ∀ x, f1[x] = f[x]/g[x]).
    { intros. rewrite I11. rewrite FunValue; auto. } unfold limit_pos in L3. 
    destruct L3 as [L3[δ0''[L4'[L5' L6']]]]. 
    assert (L : ∀ B, limit_pos \{\ λ x y, y = B * ((g[x] - g[x1])/g[x]) \}\ x0 B).
    { intros. assert (L' : ∀ x, \{\ λ x y, y = B * ((g[x] - g[x1])/g[x]) \}\ [x]
        = B * ((g[x] - g[x1])/g[x])). intros. rewrite FunValue; auto. red. 
      repeat split. red; intros. applyClassifier2 H0; applyClassifier2 H8. subst; auto. 
      red in H0'. destruct H0' as [L1[δ4'[L3'[L4 L5]]]]. exists δ'. 
      repeat split; auto. intros z H0. apply Classifier1. 
      exists (B * ((g[z] - g[x1])/g[z])). apply Classifier2;auto. intros. 
      destruct (classic (B =0)).
      - pose proof (Examp1 δ'). apply H9 in H2 as H2'; auto. clear H9. 
        destruct H2' as [δ[H9[H9' _]]]. exists δ. split; auto. intros. rewrite L'.
        replace (∣(B * ((g[x] - g[x1])/g[x]) - B)∣) with 0. lra. symmetry. 
        rewrite H8. rewrite Rminus_0_r. rewrite Rmult_0_l. rewrite Abs_ge; lra. 
      - assert (∣(g[x1])∣ * ∣B∣/ε0 > 0). apply Rmult_gt_0_compat. 
        apply Rmult_gt_0_compat; apply Abs_not_eq_0; auto. apply K4; lra.
        apply Rinv_0_lt_compat; auto. apply L5 in H9 as H9'. clear L5. 
        destruct H9' as [δ4[[H16 H14]H15]]. pose proof(Examp3 δ' δ4 (x1 - x0) δ2).
        apply H11 in H2 as H4'; auto. clear H11. 
        destruct H4' as [δ[H21[H17[H18[H19 H20]]]]]. exists δ. split; auto. 
        intros. assert(x0 < x < x0 + δ4). lra. 
        assert (g [x] <> g [x1]). { apply I6; lra. }
        assert (g[x] <> 0). { apply K4; lra. } apply H15 in H22. rewrite L'.
        replace (B * ((g[x] - g[x1])/g[x]) - B) with (B * ((-g[x1])/g[x])).  
        unfold Rdiv. rewrite <- Rmult_assoc. rewrite Abs_mult. rewrite Abs_mult.
        rewrite <- Abs_eq_neg. apply (Rmult_lt_reg_r ∣(g[x])∣). 
        apply Abs_not_eq_0; apply K4; lra. apply (Rmult_lt_compat_r ε0) in H22.
        rewrite Rmult_assoc. replace (∣(/ g[x])∣ * ∣(g[x])∣) with 1.
        unfold Rdiv in H22; rewrite Rmult_assoc in H22. rewrite Rinv_l in H22; 
        lra. unfold Rdiv. rewrite Rmult_comm. rewrite <- Abs_mult. 
        rewrite Rinv_r; auto. rewrite Abs_gt; lra. lra. unfold Rdiv. 
        rewrite <- Rmult_assoc. apply (Rmult_eq_reg_r g[x]); auto. 
        rewrite Rmult_assoc. rewrite Rinv_l; auto. rewrite Rmult_assoc.
        rewrite Rmult_1_r. unfold Rminus. rewrite <- Rmult_assoc. 
        rewrite Rmult_plus_distr_r. rewrite Rmult_assoc. rewrite Rinv_l; auto. 
        lra. }
    assert (L4 : limit_pos \{\ λ x y, y  
      = (ε/2 + A) * ((g[x] - g[x1])/g[x])\}\ x0 (ε/2 + A)). 
    { pose proof (L (ε/2 + A)). auto. }
    assert (L5 : ∃ δh1, δh1 > 0 /\ ∀ x, x0 < x < x0 + δh1 
      -> ∣(h1[x] - (ε/2 + A))∣ < ε/2).
    { unfold limit_pos in L4. 
      destruct L4 as [L4 [δ1''[L7'[L8' L9']]]]. 
      assert (L6 : ε/4 > 0). lra. apply L6' in L6 as L6''. clear L6'.
      apply L9' in L6 as L9''. clear L9'. destruct L6'' as [δ2''[[T1 T3]T2]].
      destruct L9'' as [δ3''[[T4 T5]T6]]. pose proof (Examp2 δ2'' δ3'' δ2).
      apply H0 in T1 as T1'; auto. clear H0. 
      destruct T1' as [δh1[T7[T8[T9 T10]]]]. exists δh1. split; auto. intros. 
      cut (x0 < x < x0 + δ2''). cut (x0 < x < x0 + δ3''). intros. apply T2 in H9. 
      apply T6 in H8.
      assert (\{\ λ x y, y = (ε/2 + A) * ((g[x] - g[x1])/g[x]) \}\ [x] 
        = (ε/2 + A) * ((g[x] - g[x1])/g[x])).
      { rewrite FunValue; auto. } rewrite H11 in H8. clear T2. clear T6 H11.
      assert ((f[x1] /// g)[x] = f[x1]/g[x]).
      { apply f_x_T; auto. apply Classifier2. repeat split; auto.
        - apply K3. apply Classifier1. lra.
        - cut (x0 < x < x0 + δ2). intros. apply K6 in H11. apply Abs_not_eq_0. 
          lra. lra. } rewrite H11 in H9.
      assert (h1[x] = (ε/2 + A) * ((g[x] - g[x1])/g[x]) + f[x1]/g[x]).
      { rewrite I10'; auto. } 
      rewrite H14. 
      generalize (Abs_plus_le ((ε/2+A)*((g[x]-g[x1])/g[x])-(ε/2+A)) (f[x1]/g[x]-0)).
      intro H27.
      assert (H28 : (ε/2 + A) * ((g[x] - g[x1])/g[x]) + (f[x1]/g[x])- ((ε/2 + A))
        = (ε/2 + A) * ((g[x] - g[x1])/g[x]) - (ε/2 + A) + ((f[x1]/g[x] ) - 0)).
      field.  cut (x0 < x < x0 + δ2). intros. apply K6 in H15. 
      apply Abs_not_eq_0. lra. lra. rewrite H28. lra. lra. lra. }  
    assert (L10 : limit_pos \{\ λ x y, y = (-(ε/2) + A) * ((g[x] - g[x1])/g[x])\}\ 
      x0 (-(ε/2) + A)). { pose proof (L (- (ε/2) + A)). auto. }
    assert (L7 : ∃ δh2, δh2 > 0 /\ ∀x : R, x0 < x < x0 + δh2 
      -> ∣(h2[x] - (-(ε/2) + A))∣ < ε/2). 
    { unfold limit_pos in L10. destruct L10 as [L10[δ1''[L7'[L8' L9']]]]. 
      assert (L6 : ε/4 > 0). lra. apply L6' in L6 as L6''. clear L6'.
      apply L9' in L6 as L9''. clear L9'. destruct L6'' as [δ2''[[T1 T3]T2]].
      destruct L9'' as [δ3''[[T4 T5]T6]]. pose proof (Examp2 δ2'' δ3'' δ2).
      apply H0 in T1 as T1'; auto. clear H0. 
      destruct T1' as [δh1[T7[T8[T9 T10]]]]. exists δh1. split; auto. intros. 
      cut (x0 < x < x0 + δ2''). cut (x0 < x < x0 + δ3''). intros. 
      apply T2 in H9. apply T6 in H8.
      assert (\{\ λ x y,y = (-(ε/2) + A) * ((g[x] - g[x1])/g[x]) \}\ [x] 
        = (-(ε/2) + A) * ((g[x] - g[x1])/g[x])). { rewrite FunValue; auto. } 
      rewrite H11 in H8. clear T2. clear T6 H11.
      assert ((f[x1] /// g)[x] = f[x1]/g[x]).
      { apply f_x_T; auto. apply Classifier2. repeat split; auto.
        - apply K3. apply Classifier1. lra.
        - cut (x0 < x < x0 + δ2). intros. apply K6 in H11. apply Abs_not_eq_0. 
          lra. lra. } rewrite H11 in H9.
      assert (h2[x] = (-(ε/2) + A) * ((g[x] - g[x1])/g[x]) + f[x1]/g[x]).
      { rewrite H12; rewrite FunValue; auto. }
      rewrite H14. generalize (Abs_plus_le ((-(ε/2) + A) * ((g[x] - g[x1])/g[x])
        - (-(ε/2) + A)) (f[x1]/g[x] - 0)). intro H27.
      assert (H28 : (-(ε/2)+A)*((g[x]-g[x1])/g[x])+(f[x1]/g[x])-((-(ε/2)+A))
        = (-(ε/2)+A)*((g[x]-g[x1])/g[x])-(-(ε/2)+A)+((f[x1]/g[x])-0)).
      field. cut (x0 < x < x0 + δ2). intros. apply K6 in H15. 
      apply Abs_not_eq_0. lra. lra. rewrite H28. lra. lra. lra. }       
    assert ((∃ δ', δ' > 0 /\ (U+º(x0; δ')) ⊂ dom[f1]
      /\ (∀ x, x ∈ (U+º(x0; δ')) -> h2[x] <= f1[x] <= h1[x]))).
    { exists δ0. split; auto. split.
      - intros z P1. apply Classifier1. rewrite I11. exists (f[z]/g[z]).
        apply Classifier2; auto. 
      - intros. applyClassifier1 H0. assert (H14 : x1 ∈ U+º(x0; δ')).
        { apply Classifier1; lra. } apply H3 in H14 as H14'.
        destruct H14' as [H15[H16 H17]]. apply Theorem5_1 in H15 as H15'.
        apply Theorem5_1 in H16 as H16'. apply Theorem4_1 in H15' as H15''.
        apply Theorem4_1 in H16' as H16''. 
        assert (H18 : x ∈ U+º(x0; δ')). { apply Classifier1. lra. }
        apply H3 in H18 as H18'. destruct H18' as [H18'[H19 H20]].
        assert (I1: ContinuousClose f x x1).
        { destruct H15''. split; [idtac | split]; auto.
          - red. intros. apply Theorem5_1. 
            assert (H21 : x2 ∈ U+º(x0; δ')). { apply Classifier1; lra. } 
            apply H3 in H21 as H24'; tauto.
          - apply Theorem5_1 in H18'. apply Theorem4_1 in H18'; tauto. }
        assert (I2 : ContinuousClose g x x1).
        { destruct H16''. split; [idtac | split]; auto.
          - red. intros. apply Theorem5_1.
            assert (H21 : x2 ∈ U+º(x0; δ')). { apply Classifier1; lra. } 
            apply H3 in H21 as H24'; tauto.
          - apply Theorem5_1 in H19. apply Theorem4_1 in H19; tauto. }
        assert (I3 : ∀ x', x < x' < x1 -> Derivable f x').
        { intros. cut (x' ∈ U+º(x0; δ')). intros. apply H3 in H9; 
          tauto. apply Classifier1; lra. }
        assert (I4 : ∀ x', x < x' < x1 -> Derivable g x').
        { intros. cut (x' ∈ U+º(x0; δ')). intros. apply H3 in H9; 
          tauto. apply Classifier1; lra. } 
        assert (I5 : (∀ x', x < x' < x1  -> ~(f’[x'] = 0 /\ g’[x'] = 0))).
        { intros. cut (x' ∈ U+º(x0; δ')). intros. apply H3 in H9. 
          destruct H9 as [_[_ H22]]. intro. tauto. apply Classifier1; lra. }
        assert (H8' : x < x1). lra. assert (I6' : g[x] <> g[x1]). 
        { apply I6; lra. } apply not_eq_sym in I6'.
        generalize (Theorem6_6 f g x x1 H8' I1 I2 I3 I4 I5 I6'). intros. 
        destruct H8 as [ξ[H22 H23]]. assert ( H4' : x0 < ξ < x0 + δ1). lra. 
        apply J5 in H4' as J5'. clear J5.
        assert (H9 : \{\ λ x y, y = f’[x]/g’[x] \}\ [ξ] = f’[ξ]/g’[ξ]).
        { rewrite FunValue; auto. } rewrite H9 in J5'. apply Abs_R in J5'. 
        destruct J5' as [J5 J5']. assert (-(ε/2) + A < f’[ξ]/g’[ξ]). lra. 
        assert (f’[ξ]/g’[ξ] < ε/2 + A). lra. clear J5 J5'. clear H10 H9.  
        assert (K1' : g[x] <> 0).
        { destruct (classic (g[x] = 0)). assert (x0 < x < x0 + δ2). lra. 
          apply K6 in H10. apply Abs_eq_0 in H9. rewrite H9 in H10. lra. auto. }
        assert (I7 : (f[x1] - f[x])/(g[x1] - g[x]) 
          = (f[x]/g[x] - f[x1]/g[x]) * (g[x]/(g[x] - g[x1]))).
        { unfold Rdiv. rewrite <- Rmult_assoc. unfold Rminus. symmetry. 
          rewrite Rmult_plus_distr_r. rewrite Rmult_assoc.
          rewrite (Rinv_l g[x]); auto. 
          replace (f[x] * 1 + -(f[x1] * /g[x]) * g[x]) with (f[x] - f[x1]). 
          rewrite <- Rmult_opp_opp. rewrite Ropp_minus_distr.
          replace (-/(g[x] + -g[x1])) with (/(g[x1] + -g[x])). auto.
          rewrite <-Rinv_opp. replace (-(g[x] + -g[x1])) with (g[x1] + -g[x]); auto.
          lra. unfold Rminus. rewrite Rmult_1_r. apply Rplus_eq_compat_l.
          rewrite Ropp_mult_distr_l_reverse. rewrite Rmult_assoc.
          rewrite (Rinv_l g[x]); auto. lra. } rewrite H23 in H11.
        rewrite H23 in H8. rewrite I7 in H11. rewrite I7 in H8.
        assert (L1 : (g[x]/(g[x] - g[x1])) > 0). 
        { cut (x ∈ U+º(x0; δ3)). intros. apply H13' in H9.
          assert (g1[x] = g[x]/(g[x] - g[x1])). 
          { rewrite I8. rewrite FunValue; auto. } 
          rewrite <- H10; lra. apply Classifier1; lra. }
        apply Rinv_0_lt_compat in L1. 
        generalize (Rmult_lt_compat_r (/(g[x]/(g[x] - g[x1]))) _ _ L1 H11).
        rewrite Rmult_assoc. rewrite Rinv_r. rewrite Rmult_1_r. intros.   
        assert (L2 : (/(g[x]/(g[x] - g[x1]))) = (g[x] - g[x1])/g[x]).
        { unfold Rdiv. symmetry. rewrite Rmult_comm. 
          apply (Rmult_eq_reg_l g[x]); auto. rewrite <- Rmult_assoc. 
          rewrite Rinv_r; auto. rewrite Rmult_1_l. symmetry. 
          rewrite Rinv_mult; auto. rewrite <- Rmult_assoc. 
          rewrite Rinv_r; auto. rewrite Rmult_1_l. rewrite Rinv_inv; lra. }
        rewrite L2 in H9. assert (∀ x y z, x - z < y <-> x < y + z).
        { intros. split; intros. apply (Rplus_lt_compat_r z (x2 - z) y) in H10.
          simpl in H10. lra. apply (Rplus_lt_compat_r (-z) _ _) in H. lra. }
        assert (∀ x y z, x < y - z -> x + z < y).
        { intros. apply (Rplus_lt_compat_r z _ _) in H21. lra. }
        apply H10 in H9. rewrite <- (I10' x) in H9. rewrite <- (I11' x) in H9. 
        generalize (Rmult_lt_compat_r (/(g[x]/(g[x] - g[x1]))) _ _ L1 H8).
        rewrite Rmult_assoc. rewrite Rinv_r. rewrite Rmult_1_r. intros.
        rewrite L2 in H24. apply H21 in H24. rewrite <- (I12' x) in H24.
        rewrite <- (I11' x) in H24. lra. unfold Rdiv. 
        apply Rmult_integral_contrapositive. split. lra. apply Rinv_neq_0_compat. 
        lra. unfold Rdiv. apply Rmult_integral_contrapositive. split. lra. 
        apply Rinv_neq_0_compat. lra. }
    clear L5'. destruct L5 as [δh1[L5 L5']]. destruct L7 as [δh2[L7 L7'']]. 
    destruct H0 as [δ''[H0''[H1'' H2'']]]. pose proof (Examp3 δ' δh1 δh2 δ''). 
    apply H0 in H2 as H2'; auto. clear H0. destruct H2' as [δ[D1[D2[D3[D4 D5]]]]].
    exists δ. split; auto. intros. rewrite <- I11. apply Abs_R. 
    cut (x0 < x < x0 + δh2). intros. apply L7'' in H8. apply Abs_R in H8. 
    cut (x ∈ U+º(x0; δ'')). intros. apply H2'' in H9. split. lra. 
    cut (x0 < x < x0 + δh1). intros. apply L5' in H11. apply Abs_R in H11; lra. 
    lra. apply Classifier1; lra. lra. lra.
Qed.

(* 6.3 泰勒公式 *)

(* 定义：数列前n项和 *)
Fixpoint Σ (f : Seq) (n : nat) :=
  match n with
  | 0%nat => f[0%nat]
  | S m => Σ f m + f[S m]
  end.

Fact Σ_Fact1 : ∀ (f : nat -> (@set (@prod R R))) m n x, (m <= n)%nat 
  -> (∀ k, (k < m)%nat -> (f k)[x] = 0) -> Σ \{\ λ u v, v = (f u)[x] \}\ n
    = Σ \{\ λ u v, v = (f (m+u)%nat)[x] \}\ (n - m) .
Proof.
  intros. induction n. simpl. rewrite FunValue, FunValue.
  assert (m = 0)%nat by lia. rewrite H1. auto.
  assert (m = S n \/ m < S n)%nat by lia. destruct H1. rewrite <-H1, Nat.sub_diag.
  simpl. rewrite FunValue. clear H IHn H1. induction m. simpl. rewrite FunValue;
  auto. simpl. rewrite IHm. rewrite FunValue, Nat.add_0_r, H0; auto. lra. 
  intros. apply H0. lia. assert (m <= n)%nat by lia. apply IHn in H2.
  replace (S n - m)%nat with (S (n-m))%nat; [ | lia]. simpl. rewrite H2,
  FunValue, FunValue. replace (m + S (n - m))%nat with (S n); auto. lia.
Qed.

Fact Σ_Fact2 : ∀ f n, (∀ k, (k < n)%nat -> f[k] = 0) -> Σ f n = f[n].
Proof.
  intros. induction n. simpl; auto. simpl. rewrite IHn; auto. rewrite H; auto. lra.
Qed.

Fact Σ_Fact3 : ∀ n f g, (∀ i, (i <= n)%nat -> f[i] >= g[i]) -> Σ f n >= Σ g n.
Proof.
  intros. induction n.
  - simpl. pose proof (H 0%nat). apply H0. lia.
  - simpl. apply Rplus_ge_compat. apply IHn. intros. apply H. lia. apply H. lia.
Qed.

Fact Σ_Fact4 : ∀ n f g, (∀ i, (i <= n)%nat -> f[i] > g[i]) -> Σ f n > Σ g n.
Proof.
  intros. induction n.
  - simpl. pose proof (H 0%nat). apply H0. lia.
  - simpl. apply Rplus_gt_compat. apply IHn. intros. apply H. lia. apply H. lia.
Qed.

Fact Σ_Fact5 : ∀ n A B, (∀ x,(x < S n)%nat -> A[x] = B[x]) -> Σ A n = Σ B n.
Proof.
  intros. induction n. simpl. rewrite H. auto. lia. simpl. rewrite IHn.
  pose proof (H (S n)). rewrite H0. auto. auto. intros. rewrite H. auto. lia.
Qed.

(* 定义: 阶乘 *)
Fixpoint Factorial (n : nat) :=
  match n with
  | 0%nat => 1%nat
  | S n => ((S n) * Factorial n)%nat
  end.

Notation "n !" := (Factorial n)(at level 10).

Fact Factorial_Fact1 : ∀ n, (0 < n!)%nat.
Proof.
  intros n. induction n as [ | n IHn].
  - simpl. apply Nat.lt_0_1.
  - simpl. apply Nat.add_pos_l. assumption.
Qed.

Fact Factorial_Fact2 : ∀ n m, (0 < mult_NM n m)%nat.
Proof.
  intros n. induction n; intros. simpl. auto. simpl. destruct m; auto.
  replace ((mult_NM n m) + n*(mult_NM n m))%nat with ((1+n)*(mult_NM n m))%nat;
  [ | lia]. apply Nat.mul_pos_pos; auto. lia.
Qed.

Fact Factorial_Fact3 : ∀ m x, (((m + x)!)/(mult_NM (m + x) m) = x!)%nat.
Proof.
  intros. induction m. rewrite Nat.add_0_l. destruct x. simpl; auto.
  simpl (mult_NM (S x) 0). rewrite Nat.div_1_r; auto.
  assert ((S m) + x = S (m + x))%nat by lia. rewrite H. remember (m+x)%nat. simpl. 
  replace ((mult_NM n m)+n*(mult_NM n m))%nat with ((1+n)*(mult_NM n m))%nat;
  [ | lia]. replace (n! + n * (n!))%nat with ((1 + n) * (n!))%nat; [ | lia].
  rewrite <-IHm,Nat.Div0.div_mul_cancel_l; auto.
Qed.

Fact Factorial_Fact4 : ∀ m x, INR (((m + x)!)/(mult_NM (m + x) m))%nat
  = (INR (((m + x)!))) * /(INR (mult_NM (m + x) m)).
Proof.
  intros. induction m. rewrite Nat.add_0_l. destruct x. simpl; auto. lra.
  simpl (mult_NM (S x) 0). rewrite Nat.div_1_r; auto. simpl. lra.
  assert ((S m) + x = S (m + x))%nat by lia. rewrite H. remember (m+x)%nat. simpl. 
  replace ((mult_NM n m)+n*(mult_NM n m))%nat with ((1+n)*(mult_NM n m))%nat;
  [ | lia]. replace (n! + n * (n!))%nat with ((1 + n) * (n!))%nat; [ | lia].
  assert (INR (1 + n) <> 0). { apply not_0_INR. lia. }
  assert (mult_NM n m <> 0)%nat. { pose proof (Factorial_Fact2 n m). lia. }
  assert (INR (mult_NM n m) <> 0). { apply not_0_INR; auto. }
  rewrite Nat.Div0.div_mul_cancel_l; auto. rewrite mult_INR, mult_INR, IHm.
  rewrite Rinv_mult, <-Rmult_assoc, (Rmult_comm (INR (1 + n))),
  Rinv_r_simpl_l; auto.
Qed.

Fact Factorial_Fact5 : ∀ m x, (INR (mult_NM (m + x) m)) * /(INR (((m + x)!)))
  = /(INR (x!)).
Proof.
  intros. pose proof (Factorial_Fact4 m x). rewrite Factorial_Fact3 in H.
  assert (/(INR (x!)) = /(INR ((m + x) !) * /(INR (mult_NM (m + x) m)))).
  { rewrite H; auto. } rewrite Rinv_mult,Rinv_inv in H0. lra.
Qed.


Lemma Lemma6_9a : ∀ f g (x0 A : R) (n : nat),
  (∀ k, (k < n)%nat -> limit (dN f k) x0 0 /\ limit (dN g k) x0 0)
  -> (∀ k, (k < n)%nat -> (∃ δ', δ' > 0 /\ (∀ x, x ∈ Uº(x0; δ')
    -> Derivable (dN f k) x /\ Derivable (dN g k) x /\ (dN g k)’[x] <> 0)))
  -> limit \{\ λ x y, y = (dN f n)[x]/(dN g n)[x] \}\ x0 A
  -> limit \{\ λ x y, y = f[x]/g[x] \}\ x0 A.
Proof.
  intros. induction n. simpl in H1; auto. apply IHn; intros. apply H. lia. 
  apply H0. lia. apply Theorem6_7; try (apply H; lia).
  apply H0. lia. assert (\{\ λ x y, y = (dN f (S n))[x]/(dN g (S n))[x] \}\
    = \{\ λ x y, y = (dN f n)’[x]/(dN g n)’[x] \}\).
  { apply AxiomI; split; intros; destruct z; applyClassifier2 H2.
    apply Classifier2. rewrite <-dN_Fact3,<-dN_Fact3; auto. apply Classifier2.
    rewrite dN_Fact3,dN_Fact3; auto. } rewrite <-H2; auto.
Qed.

Lemma Lemma6_9b : ∀ f g x0 A, Function g -> limit f x0 A
  -> (∃ δ, δ > 0 /\ Uº(x0; δ) ⊂ dom[g] /\ (∀ x, x ∈ Uº(x0; δ) -> f[x] = g[x]))
  -> limit g x0 A.
Proof.
  intros. destruct H1 as [δ[H1[]]]. destruct H0 as [H0[δ1[H4[]]]]. split; auto. 
  destruct (Examp1 δ δ1) as [x[H7[]]]; auto. exists x. repeat split; auto. 
  red; intros. apply H2. applyClassifier1 H10. apply Classifier1. lra. intros. 
  apply H6 in H10 as [x1[]]. destruct (Examp1 x x1) as [x2[H12[]]]; auto. lra. 
  exists x2. split. lra. intros. rewrite <-H3. apply H11. lra. apply Classifier1. lra.
Qed.

Lemma Lemma6_9c : ∀ f g x0 A, limit \{\ λ x y, y = f[x]/g[x] \}\ x0 A
  -> (∃ δ, δ > 0 /\ Uº(x0; δ) ⊂ dom[f // g]) -> limit (f // g) x0 A.
Proof.
  intros. destruct H as [H[x[H1[]]]], H0 as [δ[]]. split.
  apply Corollary_div_fun_a. rewrite Corollary_div_fun_c.
  destruct (Examp1 x δ) as [δ1[H5[]]]; auto. exists δ1. split; auto.
  split. red; intros. rewrite Corollary_div_fun_c in H4. apply H4.
  apply Classifier1. applyClassifier1 H8. lra. intros. apply H3 in H8 as [x1[]].
  destruct (Examp1 δ1 x1) as [x2[H10[]]]; try lra. exists x2. split. lra.
  intros. assert (0 < ∣(x3 - x0)∣ < x1) by lra. apply H9 in H14.
  assert (x3 ∈ Uº(x0; δ)). { apply Classifier1. lra. } apply H4 in H15. 
  rewrite Corollary_div_fun_c in H15. applyClassifier1 H15. destruct H15. 
  applyClassifier1 H16. destruct H16. applyClassifier1 H17.
  rewrite Corollary_div_fun_b; auto. rewrite FunValue in H14; auto.
Qed.

(* 泰勒展开的核心是证明佩亚诺余项为 (x-x0)^n 的高阶无穷小 *)
Section taylor_equation_P.

(* 被展开的函数 *)
Variable f : @set (@prod R R).
Hypothesis Function_f : Function f.

(* 展开式的次数 *)
Variable n : nat.

(* 在x0处展开 *)
Variable x0 : R.

(* f在x0处需要n阶可导 *)
Hypothesis f_n_Derivable : (n = 0%nat /\ Derivable f x0)
  \/ ((0 < n)%nat /\ (∀ k, (k < n)%nat -> Derivable (dN f k) x0)).

Let f_Derivable : Derivable f x0.
Proof.
  destruct f_n_Derivable as [[] | []]; auto. apply H0 in H; auto. 
Qed.

Let x0_in_dom_f : x0 ∈ dom[f].
Proof.
  destruct f_Derivable as [y[_[[δ[]]]]]. apply H0, Classifier1.
  rewrite Rminus_diag. replace ∣0∣ with 0; auto. symmetry.
  apply (Abs_eq_0 0); auto.
Qed.

(* k次项 *)
Let kst k := \{\ λ u v, v = (dN f k)[x0]/(INR (k!)) * (u - x0)^k \}\.

(* 任意k次项式m阶导函数的定义域为全体实数 *)
Let kst_dom : ∀ k m, dom[dN (kst k) m] = Full R.
Proof.
  intros. apply AxiomI; split; intros. apply Classifier1; auto. apply Classifier1. 
  unfold kst. destruct (Nat.lt_ge_cases k m). rewrite dN_Fact6; auto. exists 0.
  apply Classifier2; auto. rewrite dN_Fact4; auto.
  exists ((dN f k)[x0]/(INR (k!)) * (INR (mult_NM k m)) * (z - x0)^(k - m)).
  apply Classifier2; auto.
Qed.

(* k次泰勒多项式 *)
Let T_poly x k := Σ \{\ λ u v, v = (kst u)[x] \}\ k.

Let T_poly_Function : Function \{\ λ u v, v = T_poly u \}\.
Proof. 
  red; intros. applyClassifier2 H. applyClassifier2 H0. subst; auto. 
Qed.

(* 任意k次泰勒多项式m阶导函数的定义域为全体实数 *)
Let T_poly_dom : ∀ m k, dom[dN (\{\ λ u v, v = T_poly u k \}\) m] = Full R.
Proof.
  intros. clear Function_f f_n_Derivable T_poly_Function. apply AxiomI; split; 
  intros. applyClassifier1 H. destruct H. apply Classifier1; auto. induction k.
  assert (\{\ λ u v, v = T_poly u 0 \}\ = \{\ λ u v, v = f[x0] \}\).
  { apply AxiomI; split; intros; destruct z0; applyClassifier2 H0.
    unfold T_poly in H0. simpl in H0. rewrite FunValue in H0. unfold kst in H0.
    rewrite FunValue in H0. simpl in H0. rewrite H0. apply Classifier2. lra.
    rewrite H0. apply Classifier2. unfold T_poly; simpl. rewrite FunValue.
    unfold kst. rewrite FunValue. simpl. lra. }
  rewrite H0. destruct m. simpl. apply Classifier1. exists f[x0].
  apply Classifier2; auto. rewrite dN_Fact14. apply Classifier1. exists 0.
  apply Classifier2; auto. lia. unfold T_poly. simpl.
  assert (\{\ λ u v, v = (T_poly u k) + \{\ λ u0 v0, v0 = (kst u0)[u] \}\[S k] \}\
    = \{\ λ u v, v = T_poly u k \}\ \+ (kst (S k))).
  { apply AxiomI; split; intros; destruct z0; applyClassifier2 H0. rewrite H0.
    apply Classifier2. split. apply Classifier1. exists (T_poly x k). 
    apply Classifier2; auto. split. pose proof (kst_dom (S k) 0). simpl in H1.
    rewrite H1. apply Classifier1; auto. rewrite FunValue in H0.
    rewrite FunValue, FunValue; auto. destruct H0 as [H0[]]. rewrite H2.
    apply Classifier2. rewrite FunValue,FunValue; auto. }
  unfold T_poly in H0. rewrite H0. apply Classifier1.
  exists ((dN \{\ λ u v, v = Σ \{\ λ k v0, v0 = (kst k)[u]\}\ k \}\ m)[z]
    + (dN (kst (S k)) m)[z]). apply dN_Fact7; auto.
  rewrite kst_dom. apply Classifier1; auto.
Qed.

(* 任意k次泰勒多项式在任意x1处任意m阶可导 *)
Let T_poly_Derivable1 : ∀ k x1 m, 
  Derivable (dN (\{\ λ u v, v = T_poly u k \}\) m) x1.
Proof.
  intros k. induction k.
  - assert (\{\ λ u v, v = T_poly u 0 \}\ = \{\ λ u v, v = f[x0]/1 * 1 \}\).
    { apply AxiomI; split; intros; destruct z; applyClassifier2 H; apply Classifier2.
      unfold T_poly in H. simpl in H. rewrite FunValue in H. unfold kst in H.
      rewrite FunValue in H; auto. unfold T_poly. simpl. rewrite FunValue.
      unfold kst. rewrite FunValue; auto. }
    intros. rewrite H. destruct m. simpl. exists 0. apply EleFun_Fact14.
    rewrite dN_Fact14. exists 0. apply EleFun_Fact14. lia.
  - assert (\{\ λ u v, v = T_poly u (S k) \}\
      = \{\ λ u v, v = T_poly u k \}\ \+ (kst (S k))).
    { apply AxiomI; split; intros; destruct z; applyClassifier2 H; apply Classifier2.
      pose proof (T_poly_dom 0 k). pose proof (kst_dom (S k) 0). simpl in H0, H1.
      rewrite H0, H1. repeat split; try (apply Classifier1; reflexivity).
      rewrite FunValue. unfold T_poly in H. simpl in H.
      rewrite FunValue in H; auto. destruct H as [H[]]. rewrite FunValue in H1.
      unfold T_poly. simpl. rewrite FunValue; auto. } intros.
    rewrite H, <-dN_Fact9. pose proof (IHk x1 m).
    assert (Derivable (dN (kst (S k)) m) x1).
    { unfold kst. destruct (Nat.le_gt_cases m (S k)). rewrite dN_Fact4; auto.
      exists (((dN f (S k))[x0]/(INR ((S k)!)) * (INR (mult_NM (S k) m)))
        * (INR ((S k) - m)) * (x1 - x0)^(((S k) - m) - 1)). apply EleFun_Fact10.
      rewrite dN_Fact6; auto. exists 0. apply EleFun_Fact14. }
    exists ((dN \{\ λ u v, v = T_poly u k \}\ m)’[x1] + (dN (kst (S k)) m)’[x1]).
    apply Theorem5_4a; auto. red; intros. rewrite T_poly_dom,kst_dom.
    apply Classifier1; split; apply Classifier1; auto.
Qed.

(* n次泰勒多项式整体在x1处的m阶导数值 等于 各项在x1处m阶导数值的加和 *)
Let T_poly_Derivable2 : ∀ m x1, (dN (\{\ λ u v, v = T_poly u n \}\) m)[x1]
  = (Σ \{\ λ k v, v = (dN (kst k) m)[x1] \}\ n).
Proof.
  intros. clear Function_f f_n_Derivable T_poly_Function. induction n. simpl. 
  rewrite FunValue.
  assert (\{\ λ u v, v = T_poly u 0 \}\ = kst 0).
  { apply AxiomI; split; intros; destruct z; applyClassifier2 H; apply Classifier2; 
    rewrite H; unfold T_poly; simpl; rewrite FunValue; unfold kst; 
    rewrite FunValue; simpl; auto. } rewrite H; auto.
  assert (\{\ λ u v, v = T_poly u (S n0) \}\
    = \{\ λ u v, v = T_poly u n0 \}\ \+ (kst (S n0))).
  { apply AxiomI; split; intros; destruct z; applyClassifier2 H; apply Classifier2.
    repeat split. apply Classifier1. exists (T_poly x n0). apply Classifier2; auto.
    apply Classifier1. exists ((dN f (S n0))[x0]/(INR ((S n0)!)) * (x - x0)^(S n0)).
    apply Classifier2; auto. unfold kst. rewrite FunValue, FunValue.
    unfold T_poly, kst in H. simpl in H. rewrite FunValue, FunValue in H; auto.
    destruct H as [H[]]. unfold kst, T_poly in H1. 
    rewrite FunValue, FunValue in H1. unfold T_poly,kst. simpl. 
    rewrite FunValue, FunValue; auto. } rewrite H.
  assert ((dN (\{\ λ u v, v = T_poly u n0 \}\ \+ (kst (S n0))) m)[x1]
    = (dN (\{\ λ u v, v = T_poly u n0 \}\) m)[x1] + (dN (kst (S n0)) m)[x1]).
  { symmetry. apply dN_Fact8; [rewrite T_poly_dom | rewrite kst_dom];
    apply Classifier1; auto. } rewrite H0, IHn0. simpl. rewrite FunValue; auto.
Qed.

(* 泰勒多项式在任意x1处m阶求导的导数值 *)
Let T_poly_Derivable3 : ∀ x1 m, (m <= n)%nat
  -> (dN (\{\ λ u v, v = T_poly u n \}\) m)[x1]
   = (Σ \{\ λ k v, v = (dN f (m + k))[x0]/(INR (k!)) * (x1 - x0)^k \}\ (n - m)).
Proof.
  intros. clear Function_f f_n_Derivable T_poly_Function.
  rewrite T_poly_Derivable2. rewrite (Σ_Fact1 _ m); auto.
  assert (\{\ λ u v, v = (dN (kst (m + u)) m)[x1] \}\
    = \{\ λ k v, v = (dN f (m + k))[x0]/(INR (k!)) * (x1 - x0)^k \}\).
  { apply AxiomI; split; intros; destruct z; applyClassifier2 H0; apply Classifier2.
    unfold kst in H0. rewrite dN_Fact4, FunValue in H0. unfold Rdiv in H0.
    rewrite (Rmult_assoc ((dN f (m + x))[x0])),(Rmult_comm (/(INR ((m + x)!)))),
    Factorial_Fact5 in H0. replace (m + x - m)%nat with x in H0. auto. lia. lia.
    unfold kst. rewrite dN_Fact4,FunValue. unfold Rdiv.
    rewrite (Rmult_assoc ((dN f (m + x))[x0])),(Rmult_comm (/(INR ((m + x)!)))),
    Factorial_Fact5. replace (m + x - m)%nat with x; auto. lia. lia. }
  rewrite H0; auto. intros. unfold kst. rewrite dN_Fact6,FunValue; auto.
Qed.

(* 佩亚诺余项 *)
Let P_remainder := f \- \{\ λ u v, v = T_poly u n \}\.

Let P_remainder_Function : Function P_remainder.
Proof. 
  apply Corollary_sub_fun_a. 
Qed.

Let P_remainder_dom : ∀ m, dom[(dN P_remainder m)] = dom[dN f m].
Proof.
  intros. unfold P_remainder.
  rewrite <-dN_Fact12,Corollary_sub_fun_c,(T_poly_dom m n).
  apply AxiomI; split; intros. applyClassifier1 H; tauto.
  apply Classifier1; split; auto. apply Classifier1; auto. rewrite T_poly_dom.
  induction m. simpl. rewrite Corollary_sub_fun_c. pose proof (T_poly_dom 0 n).
  simpl in H. rewrite H. red; auto. simpl. red; intros. applyClassifier1 H.
  destruct H. applyClassifier2 H. destruct (T_poly_Derivable1 n z m).
  assert (Derivative ((dN (f \- \{\ λ u v, v = T_poly u n \}\) m)
    \+ (dN \{\ λ u v, v = T_poly u n \}\ m)) z (x + x1)).
  { pose proof H. pose proof H0. apply Corollary_DerivativeValue_a in H1.
    apply Corollary_DerivativeValue_a in H2. rewrite <- H1, <- H2. 
    apply Theorem5_4a; red; eauto. }
  assert (f \- \{\ λ u v, v = T_poly u n \}\ \+ \{\ λ u v, v = T_poly u n \}\ = f).
  { apply AxiomI; split; intros; destruct z0. applyClassifier2 H2.
    destruct H2 as [H2[]]. rewrite Corollary_sub_fun_c in H2.
    applyClassifier1 H2. destruct H2 as [H2 _]. rewrite Corollary_sub_fun_b in H4;
    auto. assert (y = f[x2]) by lra. rewrite H5. apply x_fx_T; auto.
    assert (x2 ∈ dom[f]). { apply Classifier1; eauto. } apply f_x_T in H2; auto.
    pose proof (T_poly_dom 0 n). simpl in H4. apply Classifier2; repeat split.
    rewrite Corollary_sub_fun_c. rewrite H4. apply Classifier1; split; auto.
    apply Classifier1; auto. rewrite H4. apply Classifier1; auto.
    rewrite Corollary_sub_fun_b,H2; auto. lra. rewrite H4. apply Classifier1; auto. }
  rewrite dN_Fact9, H2 in H1. apply Classifier1; split. apply Classifier1. 
  exists (x + x1). apply Classifier2; auto. apply Classifier1; auto.
  rewrite T_poly_dom,H2. red; intros. rewrite <-dN_Fact12.
  rewrite Corollary_sub_fun_c,T_poly_dom. apply Classifier1; split.
  apply Classifier1; split; auto. apply Classifier1; auto.
  apply Classifier1; auto. rewrite T_poly_dom; auto.
Qed.

Let P_remainder_Derivable : Derivable P_remainder x0
  /\ (∀ m, (m < n)%nat -> Derivable (dN P_remainder m) x0).
Proof.
  split.
  - exists (f’[x0] - \{\ λ u v, v = T_poly u n \}\’[x0]). apply Theorem5_4b; 
    auto. apply (T_poly_Derivable1 n x0 0).
  - intros. unfold P_remainder. rewrite <-dN_Fact12.
    exists ((dN f m)’[x0] - (dN \{\ λ u v, v = T_poly u n \}\ m)’[x0]).
    apply Theorem5_4b; auto. destruct f_n_Derivable as [[] | []]. 
    rewrite H0 in H. exfalso. lia. apply H1; auto.
    rewrite <-P_remainder_dom,T_poly_dom. red; intros.
    apply Classifier1; split; auto. apply Classifier1; auto.
Qed.

Let P_remainder_Derivable_Neighbor : ∀ m, (m < (n - 1))%nat
  -> (∃ δ', δ' > 0 /\ (∀ x, x ∈ Uº(x0; δ') -> Derivable (dN P_remainder m) x)).
Proof.
  intros. assert (Derivable (dN P_remainder (S m)) x0).
  { apply P_remainder_Derivable. lia. }
  apply Theorem5_1 in H0 as [_[H0[δ[H1[H2 _]]]]]. simpl in H0, H2. exists δ. 
  split; auto. intros. apply H2 in H3. apply x_fx_T in H3; auto. 
  applyClassifier2 H3. red. eauto.
Qed.

(* 佩亚诺余项是x0处的无穷小 *)
Let P_remainder_Infsimal : Infinitesimal P_remainder x0
  /\ (∀ m, (m < n)%nat -> Infinitesimal (dN P_remainder m) x0).
Proof.
  split; intros.
  - destruct P_remainder_Derivable. apply Theorem5_1 in H as [].
    replace (P_remainder[x0]) with 0 in H1; auto. unfold P_remainder.
    rewrite Corollary_sub_fun_b; auto. rewrite FunValue.
    assert (∀ m, T_poly x0 m = f[x0]).
    { intros. induction m. unfold T_poly. simpl. rewrite FunValue.
      unfold kst. rewrite FunValue,Rminus_diag. simpl. lra. unfold T_poly.
      simpl. rewrite FunValue. unfold T_poly in IHm. rewrite IHm. unfold kst.
      rewrite FunValue,Rminus_diag. simpl. rewrite Rmult_0_l,Rmult_0_r. lra. }
    rewrite H2. lra. pose proof (T_poly_dom 0 n). simpl in H2. rewrite H2.
    apply Classifier1; auto.
  - unfold P_remainder. rewrite <- dN_Fact12. red.
    replace 0 with ((dN f m)[x0] - (dN f m)[x0]). apply Theorem3_7b.
    assert (Derivable (dN f m) x0).
    { assert (n = 0 \/ 0 < n)%nat as []. lia. rewrite H0 in H. exfalso. lia. 
      destruct f_n_Derivable as [[] | []]; auto. rewrite H1 in H0. exfalso. lia. }
    apply Theorem5_1 in H0 as []; auto. pose proof (T_poly_Derivable1 n x0 m).
    apply Theorem5_1 in H0 as []. assert (m <= n)%nat. lia.
    apply (T_poly_Derivable3 x0 m) in H2.
    assert (Σ \{\ λ k v, v = (dN f (m+k))[x0]/(INR (k!)) * (x0-x0)^k \}\ (n-m)
      = (dN f m)[x0]).
    { remember (n - m)%nat. clear dependent n. induction n0. simpl.
      rewrite FunValue. simpl. rewrite Nat.add_0_r. lra. simpl. 
      rewrite FunValue,Rminus_diag. simpl. rewrite Rmult_0_l, Rmult_0_r.
      rewrite Rminus_diag in IHn0. rewrite IHn0. lra. }
    rewrite <- H3, <- H2; auto. lra. unfold P_remainder in P_remainder_dom.
    rewrite P_remainder_dom, T_poly_dom. red; intros.
    apply Classifier1; split; auto. apply Classifier1; auto.
Qed.

Let x_x0_n_Derivable : ∀ m k x,
  Derivable (dN (\{\ λ u v, v = (u - x0)^m \}\) k) x.
Proof.
  intros. assert (k <= m \/ m < k)%nat as []. lia.
  - rewrite dN_Fact5; auto.
    exists ((INR (mult_NM m k)) * (INR (m - k)%nat) * (x - x0)^(m - k - 1)%nat).
    apply EleFun_Fact10.
  - replace \{\ λ u v, v = (u - x0)^m \}\ with \{\ λ u v, v = 1 * (u - x0)^m \}\.
    rewrite dN_Fact6; auto. exists 0. apply EleFun_Fact14. apply AxiomI; split;
    intros; destruct z; applyClassifier2 H0; apply Classifier2; lra.
Qed.

(* (x-x0)^n 是x0处的无穷小 *)
Let x_x0_n_Infsimal : ∀ m, (m < n)%nat
  -> Infinitesimal (dN \{\ λ u v, v = (u - x0)^n \}\ m) x0.
Proof.
  intros. assert (\{\ λ u v, v = (u-x0)^n \}\ = \{\ λ u v, v = 1*(u-x0)^n \}\).
  { apply AxiomI; split; intros; destruct z; applyClassifier2 H0; apply Classifier2;
    lra. } pose proof (x_x0_n_Derivable n m x0). apply Theorem5_1 in H1 as [].
  assert ((dN \{\ λ u v, v = (u - x0)^n \}\ m)[x0] = 0).
  { rewrite H0. rewrite dN_Fact4,FunValue,Rminus_diag,PowR_Fact5; auto;
    try lia. lra. } rewrite H3 in H2; auto.
Qed.

Let lim_P_remainder_div_x_x0_n : limit \{\ λ u v,
  v = (P_remainder[u])/(\{\ λ u0 v0, v0 = (u0 - x0)^n \}\[u]) \}\ x0 0.
Proof.
  apply (Lemma6_9a _ _ _ _ (n-1)%nat); intros.
  - split. destruct P_remainder_Infsimal. apply (H1 k). lia. 
    apply (x_x0_n_Infsimal k). lia.
  - pose proof H. apply P_remainder_Derivable_Neighbor in H as [δ[]]. exists δ. 
    split; auto. intros. split; auto. split.
    + unfold T_poly in T_poly_Derivable1. apply x_x0_n_Derivable.
    + rewrite <-dN_Fact3,dN_Fact5; [ | lia]. rewrite FunValue.
      pose proof (Factorial_Fact2 n (S k)). intro.
      apply Rmult_integral in H4 as []. assert (mult_NM n (S k) <> 0)%nat. lia. 
      apply not_0_INR in H5; auto. apply PowR_Fact6 in H4. applyClassifier1 H2. 
      rewrite H4 in H2. assert (0 = 0) by auto. apply Abs_eq_0 in H5. 
      rewrite H5 in H2. lra.
  - destruct n.
    + assert (\{\ λ u v, v = P_remainder[u] / \{\ λ r t, t = 1 \}\[u] \}\|[dom[f]]
        = f \- \{\ λ u v, v = f[x0] \}\).
      { apply AxiomI; split; intros; destruct z. applyClassifier1 H. destruct H.
        applyClassifier2 H; applyClassifier2 H0. destruct H0 as [H0 _].
        unfold P_remainder in H. rewrite Corollary_sub_fun_b, FunValue in H; auto.
        unfold T_poly in H. simpl in H. rewrite FunValue in H. unfold kst in H.
        rewrite FunValue, FunValue in H. simpl in H. apply Classifier2. split;
        auto. split. apply Classifier1. exists f[x0]. apply Classifier2; auto.
        rewrite FunValue. lra. apply Classifier1. exists (T_poly x 0).
        apply Classifier2; auto. applyClassifier2 H. destruct H as [H[]].
        rewrite FunValue in H1. apply Classifier1. split. apply Classifier2.
        unfold P_remainder. rewrite Corollary_sub_fun_b; auto. rewrite FunValue.
        unfold T_poly. simpl. rewrite FunValue. unfold kst. rewrite FunValue.
        simpl. rewrite FunValue. lra. apply Classifier1. exists (T_poly x 0).
        apply Classifier2; auto. apply Classifier2; split; auto.
        apply Classifier1; auto. }
      assert (limit (f \- \{\ λ u v, v = f[x0] \}\) x0 (f[x0] - f[x0])).
      { apply Theorem3_7b. apply Theorem5_1 in f_Derivable as []; auto.
        apply EleFun_Fact15. } simpl.
      replace (f[x0] - f[x0]) with 0 in H0. rewrite <- H in H0.
      apply Lemma3_12 in H0; auto. red; intros. applyClassifier2 H1.  
      applyClassifier2 H2. subst; auto. lra.
    + remember (S n0)%nat. assert (0 <= n1 - 1)%nat. lia.
      assert (limit (\{\ λ u v, v = /(INR (mult_NM n1 (n1-1))) \}\
        \* (\{\ λ u v, v = ((dN f (n1-1))[u]-(dN f (n1-1))[x0])/(u-x0) \}\
        \- \{\ λ u v, v = (dN f n1)[x0] \}\)) x0 0).
      { replace 0 with ((/(INR (mult_NM n1 (n1-1))))*0); [ | lra].
        apply Theorem3_7c. apply EleFun_Fact15.
        replace 0 with ((dN f n1)[x0] - (dN f n1)[x0]); [ | lra].
        apply Theorem3_7b; [ | apply EleFun_Fact15].
        assert (Derivable (dN f (n1 - 1)) x0).
        { destruct f_n_Derivable as [[] | []]. rewrite Heqn1 in H0. exfalso. lia.
          apply H1. lia. } destruct H0 as [y]. pose proof H0. 
        apply Corollary_DerivativeValue_a in H0. destruct H1 as [_[_]].
        rewrite <-H0, <-dN_Fact3 in H1. replace (S (n1-1)) with n1 in H1; auto.
        lia. }
      apply (Lemma6_9b _ (\{\ λ u v, v = (dN P_remainder (n1 - 1))[u]
        /(dN \{\ λ u0 v0, v0 = (u0 - x0)^n1 \}\ (n1 - 1))[u] \}\)) in H0; auto.
      red; intros. applyClassifier2 H1. applyClassifier2 H2. subst; auto.
      assert (Derivable (dN f (n1 - 1)) x0).
      { destruct f_n_Derivable as [[] | []]. rewrite Heqn1 in H1. exfalso. lia.
        apply H2. lia. } apply Theorem5_1 in H1 as [_[_[δ[H1[H2 _]]]]].
      exists δ. repeat split; auto. red; intros. apply Classifier1.
      exists ((dN P_remainder (n1 - 1))[z]
        /(dN \{\ λ u v, v = (u - x0)^n1 \}\ (n1 - 1))[z]). apply Classifier2; auto.
      intros. assert (x - x0 <> 0).
      { applyClassifier1 H3. intro. rewrite H4 in H3. assert (0 = 0) by auto.
        apply Abs_eq_0 in H5. rewrite H5 in H3. lra. }
      assert (x ∈ dom[\{\ λ u v, v = /(INR (mult_NM n1 (n1-1))) \}\]
        /\ x ∈ dom[\{\ λ u v, v = ((dN f (n1-1))[u]-(dN f (n1-1))[x0])/(u-x0) \}\]
        /\ x ∈ dom[\{\ λ u v, v = (dN f n1)[x0] \}\]) as [H5[]].
      { repeat split; intros; apply Classifier1; 
        [exists (/(INR (mult_NM n1 (n1 - 1)))) 
         | exists (((dN f (n1 - 1))[x] - (dN f (n1 - 1))[x0])/(x - x0)) 
         | exists ((dN f n1)[x0])]; apply Classifier2; auto. }
      rewrite Corollary_mult_fun_b, Corollary_sub_fun_b, FunValue, FunValue,
      FunValue, FunValue; auto; 
      [ | rewrite Corollary_sub_fun_c; apply Classifier1; auto]. unfold P_remainder.
      rewrite <-dN_Fact11,T_poly_Derivable3,dN_Fact5; auto; try lia.
      replace (n1 - (n1 - 1))%nat with 1%nat; [ | lia]. simpl.
      rewrite FunValue, FunValue, FunValue. simpl. rewrite Nat.add_0_r, Rmult_1_r,
      Rmult_1_r. replace (n1 - 1 + 1)%nat with n1; [ | lia].
      replace ((dN f (n1 - 1))[x0]/1) with (dN f (n1 - 1))[x0]; [ | lra].
      replace ((dN f n1)[x0]/1) with (dN f n1)[x0]; [ | lra].
      assert (INR (mult_NM n1 (n1 - 1)) <> 0).
      { pose proof Factorial_Fact2 n1 (n1 - 1). apply lt_0_INR in H8. lra. }
      unfold Rdiv. rewrite Rinv_mult, <-Rmult_assoc,
      (Rmult_comm _ (/(INR (mult_NM n1 (n1 - 1))))), Rmult_assoc,
      Rmult_minus_distr_r, Rmult_minus_distr_r, Rmult_plus_distr_r,
      Rinv_r_simpl_l; auto. lra. rewrite (T_poly_dom (n1 - 1) n1). 
      apply Classifier1; auto.
Qed.

(* 佩亚诺余项是 (x-x0)^n 的高阶无穷小 *)
Theorem Theorem6_9a : (0 < n)%nat
  -> InfinitesimalHigherOrder P_remainder \{\ λ u v, v = (u - x0)^n \}\ x0.
Proof.
  split. apply P_remainder_Infsimal. split. apply (x_x0_n_Infsimal 0); auto. 
  apply Lemma6_9c; auto. pose proof (P_remainder_dom 0). simpl in H0. 
  rewrite Corollary_div_fun_c, H0.
  apply Theorem5_1 in f_Derivable as [_[_[δ[H1[H2 _]]]]]. exists δ. split; auto. 
  red; intros. apply Classifier1. split; auto. apply Classifier1. split. apply Classifier1. 
  exists ((z - x0)^n). apply Classifier2; auto. apply Classifier1. rewrite FunValue. 
  intro. apply PowR_Fact6 in H4. applyClassifier1 H3. apply Abs_eq_0 in H4. 
  rewrite H4 in H3. lra.
Qed.

(* 对于确定的x0及f[x0], f在其他x处的值可以展开为泰勒多项式的值加上佩亚诺余项的值,
   其中泰勒多项式与佩亚诺余项均以x0为参数 *)
Theorem Theorem6_9b : ∀ x, x ∈ dom[f] -> f[x] = T_poly x n + P_remainder[x].
Proof.
  intros. unfold P_remainder. rewrite Corollary_sub_fun_b; auto. 
  rewrite FunValue. lra. apply Classifier1. exists (T_poly x n). apply Classifier2; auto.
Qed.

End taylor_equation_P.

Theorem Theorem6_9 : ∀ f n x0, Function f -> (0 < n)%nat
  -> (∀ k, (k < n)%nat -> Derivable (dN f k) x0)
  -> (∃ o, dom[o] = dom[f]
    /\ InfinitesimalHigherOrder o \{\ λ x y, y = (x - x0)^n \}\ x0
    /\ (∀ x, x ∈ dom[f] -> f[x]
      = (Σ \{\ λ k v, v = (dN f k)[x0]/(INR (k!)) * (x - x0)^k \}\ n) + o[x])).
Proof.
  intros. pose proof H0. apply (Theorem6_9a f H n x0) in H2; auto.
  exists (f \- \{\ λ u v, v = Σ \{\ λ u0 v0, v0 = \{\ λ u1 v1, v1
    = (dN f u0)[x0]/(INR (u0!)) * (u1 - x0)^u0 \}\[u] \}\ n \}\).
  split. rewrite Corollary_sub_fun_c. apply AxiomI; split; intros.
  applyClassifier1 H3. destruct H3. auto. apply Classifier1; split; auto.
  apply Classifier1.
  exists (Σ \{\ λ u0 v0, v0 = \{\ λ u1 v1, v1 = (dN f u0)[x0]/(INR (u0!))
    * (u1 - x0)^u0 \}\[z] \}\ n). apply Classifier2; auto.
  split; auto. intros. pose proof H3. apply (Theorem6_9b f n x0) in H3.
  rewrite Corollary_sub_fun_b, FunValue; auto.
  assert (\{\ λ k v, v = (dN f k)[x0]/(INR (k!)) * (x - x0)^k \}\
    = \{\ λ u0 v0, v0 = \{\ λ u1 v1, v1 
      = (dN f u0)[x0]/(INR (u0!)) * (u1 - x0)^u0 \}\[x] \}\).
  { apply AxiomI; split; intros; destruct z; applyClassifier2 H5; apply Classifier2.
    rewrite FunValue; auto. rewrite FunValue in H5; auto. }
  rewrite <-H5; lra. apply Classifier1.
  exists (Σ \{\ λ u0 v0, v0 = \{\ λ u1 v1, v1
    = (dN f u0)[x0]/(INR (u0!))*(u1-x0)^u0 \}\[x] \}\ n). apply Classifier2; auto.
Qed.


(* 以下引理为证明泰勒定理做准备, 主要涉及函数导数及连续性问题 *)
(* (x0 - x)^n 的导数为 -n*(x0 - x)^(n-1) *)
Lemma Lemma6_10a : ∀ c a x0 n, Derivative
  \{\ λ u v, v = c * (a - u)^n \}\ x0 (-(INR n) * c * ((a - x0)^(n - 1))).
Proof.
  intros. assert (\{\ λ u v, v = c * (a - u)^n \}\ 
    = \{\ λ u v, v = (-1)^n * c * (u - a)^n \}\).
  { apply AxiomI; split; intros; destruct z; applyClassifier2 H;
    apply Classifier2. rewrite Rmult_assoc, (Rmult_comm c), <- Rmult_assoc,PowR_Fact4.
    replace (-1 * (x - a)) with (a - x). rewrite H. lra. lra.
    rewrite Rmult_assoc, (Rmult_comm c), <- Rmult_assoc, PowR_Fact4 in H.
    replace (-1 * (x - a)) with (a - x) in H. rewrite H. lra. lra. }
  assert ((-1)^n*c*(INR n)*(x0 - a)^(n - 1) = -(INR n)*c*(a - x0)^(n - 1)).
  { destruct n. simpl. lra. replace (S n - 1)%nat with n; [ | lia].
    simpl ((-1)^(S n)). rewrite (Rmult_comm (-1)),Rmult_assoc,
    (Rmult_assoc _ (-1)), (Rmult_comm (-1)), Rmult_assoc, Rmult_assoc,
    <- (Rmult_assoc (-1)). replace (-1 * (INR (S n))) with (-INR (S n));
    [ | lra]. rewrite Rmult_comm, Rmult_assoc, Rmult_assoc, PowR_Fact4.
    replace ((x0 - a) * (-1)) with (a - x0); lra. }
  rewrite H, <- H0. apply EleFun_Fact10.
Qed.

(* (x0 - x)^n 在实数域上连续 *)
Lemma Lemma6_10b : ∀ c a x0 n, Continuous \{\ λ u v, v = c * (a - u)^n \}\ x0.
Proof.
  intros. assert (\{\ λ u v, v = c * (a - u)^n \}\
    = \{\ λ u v, v = (-1)^n * c * (u - a)^n \}\).
  { apply AxiomI; split; intros; destruct z; applyClassifier2 H; apply Classifier2. 
    rewrite Rmult_assoc, (Rmult_comm c), <- Rmult_assoc, PowR_Fact4.
    replace (-1 * (x - a)) with (a - x). rewrite H. lra. lra.
    rewrite Rmult_assoc, (Rmult_comm c), <- Rmult_assoc, PowR_Fact4 in H.
    replace (-1 * (x - a)) with (a - x) in H. rewrite H. lra. lra. }
  split. apply Classifier1. exists (c * (a - x0)^n). apply Classifier2; auto.
  rewrite H, FunValue. apply EleFun_Fact16.
Qed.

(* f在x0处右极限为A, 则利用f构造的关于x0对称的函数, 其在x0处极限为A *)
Lemma Lemma6_10c : ∀ f x0 A, limit_pos f x0 A
  -> limit \{\ λ u v, (u < x0 /\ v = f[2 * x0 - u])
    \/ (x0 < u /\ v = f[u]) \}\ x0 A.
Proof.
  intros. assert (Function \{\ λ u v, (u < x0 /\ v = f[2 * x0 - u])
    \/ (x0 < u /\ v = f[u]) \}\).
  { red; intros. applyClassifier2 H0. applyClassifier2 H1. destruct H0 as [[] | []];
    destruct H1 as [[] | []]; try (subst; auto); exfalso; lra. } split; auto.
  destruct H as [H[δ[H1[]]]]. exists δ. split; auto. split. red; intros. 
  apply Classifier1. destruct (Rtotal_order z x0) as [H5 | []]. exists f[2 * x0 - z].
  apply Classifier2; auto. applyClassifier1 H4. assert (z - x0 = 0) by lra.
  apply Abs_eq_0 in H6. rewrite H6 in H4. exfalso. lra. exists f[z].
  apply Classifier2; auto. intros. apply H3 in H4 as [δ1[]]. exists δ1. split; auto.
  intros. destruct (Rtotal_order (x - x0) 0) as [H7 | []].
  - assert (\{\ λ u v, u < x0 /\ v = f[2 * x0 - u] \/ x0 < u /\ v = f [u] \}\ [x]
      = f[2 * x0 - x]).
    { apply (H0 x). apply x_fx_T; auto. apply Classifier1. exists (f[2 * x0 - x]).
      apply Classifier2. left. split; auto. lra. apply Classifier2. left. split; auto. 
      lra. }
    rewrite H8. apply Abs_lt in H7. rewrite H7 in H6. apply H5. lra.
  - apply Abs_eq_0 in H7. rewrite H7 in H6. exfalso. lra.
  - assert (\{\ λ u v, u < x0 /\ v = f[2 * x0 - u] \/ x0 < u /\ v = f [u] \}\ [x]
      = f[x]).
    { apply (H0 x). apply x_fx_T; auto. apply Classifier1. exists (f[x]).
      apply Classifier2. right. split; auto. lra. apply Classifier2. right. split; auto.
      lra. } rewrite H8. apply Abs_gt in H7. rewrite H7 in H6. apply H5. lra.
Qed.

(* 函数相加的右极限等于两个函数的右极限相加 *)
Lemma Lemma6_10d : ∀ f g x0 A B, limit_pos f x0 A -> limit_pos g x0 B
  -> limit_pos (f \+ g) x0 (A + B).
Proof.
  intros. pose proof H. pose proof H0. destruct H1 as [H1[δ1[H3[]]]], 
  H2 as [H2[δ2[H6[]]]]. destruct (Examp1 δ1 δ2) as [δ3[H9[]]]; auto. split.
  apply Corollary_plus_fun_a. exists δ3. split; auto. split.
  rewrite Corollary_plus_fun_c. red; intros. apply Classifier1; split; 
  [apply H4 | apply H7]; applyClassifier1 H12; apply Classifier1; lra.
  apply Lemma6_10c in H. apply Lemma6_10c in H0. clear H5 H8.
  remember (\{\ λ u v, u < x0 /\ v = f[2 * x0 - u] \/ x0 < u /\ v = f[u] \}\
    \+ \{\ λ u v, u < x0 /\ v = g[2 * x0 - u] \/ x0 < u /\ v = g[u] \}\) as h.
  assert (limit h x0 (A + B)). { rewrite Heqh. apply Theorem3_7a; auto. }
  destruct H5 as [H5[δ4[H8[]]]]. intros. apply H13 in H14 as [δ5[[]]].
  destruct (Examp1 δ5 δ3) as [δ6[H17[]]]; auto. exists δ6. split. auto.
  intros x []. assert (x ∈ dom[h]).
  { rewrite Heqh, Corollary_plus_fun_c. apply Classifier1; split; apply Classifier1;
    [exists f[x] | exists g[x]]; apply Classifier2; right; split; auto. } 
  assert ((f \+ g)[x] = h[x]).
  { apply (H5 x). rewrite Heqh, Corollary_plus_fun_c in H22. applyClassifier1 H22.
    destruct H22. rewrite Heqh. apply Classifier2. repeat split; auto.
    rewrite Corollary_plus_fun_b; [ | apply H4 | apply H7];
    try (apply Classifier1; lra). destruct H as [H _], H0 as [H0 _].
    apply x_fx_T in H22,H23; auto. applyClassifier2 H22. applyClassifier2 H23.
    destruct H22 as [[] | []], H23 as [[] | []]; try (exfalso; lra).
    rewrite H24, H25; auto. apply x_fx_T; auto. }
  rewrite H23. apply H16. rewrite Abs_gt; lra.
Qed.

(* 函数相减的右极限等于两个函数的右极限相减 *)
Lemma Lemma6_10e : ∀ f g x0 A B, limit_pos f x0 A -> limit_pos g x0 B
  -> limit_pos (f \- g) x0 (A - B).
Proof.
  intros. pose proof H. pose proof H0. destruct H1 as [H1[δ1[H3[]]]], 
  H2 as [H2[δ2[H6[]]]]. destruct (Examp1 δ1 δ2) as [δ3[H9[]]]; auto. split.
  apply Corollary_sub_fun_a. exists δ3. split; auto. split. 
  rewrite Corollary_sub_fun_c. red; intros. apply Classifier1; split; 
  [apply H4 | apply H7]; applyClassifier1 H12; apply Classifier1; lra.
  apply Lemma6_10c in H. apply Lemma6_10c in H0. clear H5 H8.
  remember (\{\ λ u v, u < x0 /\ v = f[2 * x0 - u] \/ x0 < u /\ v = f[u] \}\
    \- \{\ λ u v, u < x0 /\ v = g[2 * x0 - u] \/ x0 < u /\ v = g[u] \}\) as h.
  assert (limit h x0 (A - B)). { rewrite Heqh. apply Theorem3_7b; auto. }
  destruct H5 as [H5[δ4[H8[]]]]. intros. apply H13 in H14 as [δ5[[]]].
  destruct (Examp1 δ5 δ3) as [δ6[H17[]]]; auto. exists δ6. split. auto.
  intros x []. assert (x ∈ dom[h]).
  { rewrite Heqh, Corollary_sub_fun_c. apply Classifier1; split; apply Classifier1;
    [exists f[x] | exists g[x]]; apply Classifier2; right; split; auto. }
  assert ((f \- g)[x] = h[x]).
  { apply (H5 x). rewrite Heqh, Corollary_sub_fun_c in H22. applyClassifier1 H22.
    destruct H22. rewrite Heqh. apply Classifier2. repeat split; auto.
    rewrite Corollary_sub_fun_b; [ | apply H4 | apply H7];
    try (apply Classifier1; lra). destruct H as [H _], H0 as [H0 _].
    apply x_fx_T in H22,H23; auto. applyClassifier2 H22. applyClassifier2 H23.
    destruct H22 as [[] | []], H23 as [[] | []]; try (exfalso; lra).
    rewrite H24, H25; auto. apply x_fx_T; auto. }
  rewrite H23. apply H16. rewrite Abs_gt; lra.
Qed.

(* 函数相乘的右极限等于两个函数的右极限相乘 *)
Lemma Lemma6_10f : ∀ f g x0 A B, limit_pos f x0 A -> limit_pos g x0 B
  -> limit_pos (f \* g) x0 (A * B).
Proof.
  intros. pose proof H. pose proof H0. destruct H1 as [H1[δ1[H3[]]]], 
  H2 as [H2[δ2[H6[]]]]. destruct (Examp1 δ1 δ2) as [δ3[H9[]]]; auto. split.
  apply Corollary_mult_fun_a. exists δ3. split; auto. split.
  rewrite Corollary_mult_fun_c. red; intros. apply Classifier1; split; 
  [apply H4 | apply H7]; applyClassifier1 H12; apply Classifier1; lra.
  apply Lemma6_10c in H. apply Lemma6_10c in H0. clear H5 H8.
  remember (\{\ λ u v, u < x0 /\ v = f[2 * x0 - u] \/ x0 < u /\ v = f[u] \}\
    \* \{\ λ u v, u < x0 /\ v = g[2 * x0 - u] \/ x0 < u /\ v = g[u] \}\) as h.
  assert (limit h x0 (A * B)). { rewrite Heqh. apply Theorem3_7c; auto. }
  destruct H5 as [H5[δ4[H8[]]]]. intros. apply H13 in H14 as [δ5[[]]].
  destruct (Examp1 δ5 δ3) as [δ6[H17[]]]; auto. exists δ6. split. auto.
  intros x []. assert (x ∈ dom[h]).
  { rewrite Heqh,Corollary_mult_fun_c. apply Classifier1; split; apply Classifier1;
    [exists f[x] | exists g[x]]; apply Classifier2; right; split; auto. }
  assert ((f \* g)[x] = h[x]).
  { apply (H5 x). rewrite Heqh, Corollary_mult_fun_c in H22. applyClassifier1 H22.
    destruct H22. rewrite Heqh. apply Classifier2. repeat split; auto.
    rewrite Corollary_mult_fun_b; [ | apply H4 | apply H7];
    try (apply Classifier1; lra). destruct H as [H _], H0 as [H0 _].
    apply x_fx_T in H22,H23; auto. applyClassifier2 H22. applyClassifier2 H23.
    destruct H22 as [[] | []], H23 as [[] | []]; try (exfalso; lra).
    rewrite H24, H25; auto. apply x_fx_T; auto. }
  rewrite H23. apply H16. rewrite Abs_gt; lra.
Qed.

(* f在x0处左极限为A, 则利用f构造的关于x0对称的函数, 其在x0处极限为A *)
Lemma Lemma6_10g : ∀ f x0 A, limit_neg f x0 A 
  -> limit \{\ λ u v, (u < x0 /\ v = f[u]) \/ (x0 < u /\ v = f[2*x0-u]) \}\ x0 A.
Proof.
  intros. assert (Function \{\ λ u v, (u < x0 /\ v = f[u])
    \/ (x0 < u /\ v = f[2 * x0 - u]) \}\).
  { red; intros. applyClassifier2 H0. applyClassifier2 H1. destruct H0 as [[] | []];
    destruct H1 as [[] | []]; try (subst; auto); exfalso; lra. } split; auto.
  destruct H as [H[δ[H1[]]]]. exists δ. split; auto. split. red; intros. 
  apply Classifier1. destruct (Rtotal_order z x0) as [H5 | []]. exists f[z]. 
  apply Classifier2; auto. applyClassifier1 H4. assert (z - x0 = 0) by lra. 
  apply Abs_eq_0 in H6. rewrite H6 in H4. exfalso. lra. exists f[2 * x0 - z]. 
  apply Classifier2; auto. intros. apply H3 in H4 as [δ1[]]. exists δ1. split; auto.
  intros. destruct (Rtotal_order (x - x0) 0) as [H7 | []].
  - assert (\{\ λ u v, u < x0 /\ v = f[u] \/ x0 < u /\ v = f[2 * x0 - u] \}\[x]
      = f[x]).
    { apply (H0 x). apply x_fx_T; auto. apply Classifier1. exists (f[x]).
      apply Classifier2. left. split; auto. lra. apply Classifier2. left. split; auto. 
      lra. } rewrite H8. apply Abs_lt in H7. rewrite H7 in H6. apply H5. lra.
  - apply Abs_eq_0 in H7. rewrite H7 in H6. exfalso. lra.
  - assert (\{\ λ u v, u < x0 /\ v = f[u] \/ x0 < u /\ v = f[2 * x0 - u] \}\[x]
      = f[2 * x0 - x]).
    { apply (H0 x). apply x_fx_T; auto. apply Classifier1. exists (f[2 * x0 - x]).
      apply Classifier2. right. split; auto. lra. apply Classifier2. right. split; auto.
      lra. } rewrite H8. apply Abs_gt in H7. rewrite H7 in H6. apply H5. lra.
Qed.

(* 函数相加的左极限等于两个函数的左极限相加 *)
Lemma Lemma6_10h : ∀ f g x0 A B, limit_neg f x0 A -> limit_neg g x0 B
  -> limit_neg (f \+ g) x0 (A + B).
Proof.
  intros. pose proof H. pose proof H0. destruct H1 as [H1[δ1[H3[]]]], 
  H2 as [H2[δ2[H6[]]]]. destruct (Examp1 δ1 δ2) as [δ3[H9[]]]; auto. split.
  apply Corollary_plus_fun_a. exists δ3. split; auto. split.
  rewrite Corollary_plus_fun_c. red; intros. apply Classifier1; split; 
  [apply H4 | apply H7]; applyClassifier1 H12; apply Classifier1; lra.
  apply Lemma6_10g in H. apply Lemma6_10g in H0. clear H5 H8.
  remember (\{\ λ u v, u < x0 /\ v = f[u] \/ x0 < u /\ v = f[2 * x0 - u] \}\
    \+ \{\ λ u v, u < x0 /\ v = g[u] \/ x0 < u /\ v = g[2 * x0 - u] \}\) as h.
  assert (limit h x0 (A + B)). { rewrite Heqh. apply Theorem3_7a; auto. }
  destruct H5 as [H5[δ4[H8[]]]]. intros. apply H13 in H14 as [δ5[[]]].
  destruct (Examp1 δ5 δ3) as [δ6[H17[]]]; auto. exists δ6. split. auto.
  intros x []. assert (x ∈ dom[h]).
  { rewrite Heqh,Corollary_plus_fun_c. apply Classifier1; split; apply Classifier1;
    [exists f[x] | exists g[x]]; apply Classifier2; left; split; auto. }
  assert ((f \+ g)[x] = h[x]).
  { apply (H5 x). rewrite Heqh, Corollary_plus_fun_c in H22. applyClassifier1 H22.
    destruct H22. rewrite Heqh. apply Classifier2. repeat split; auto.
    rewrite Corollary_plus_fun_b; [ | apply H4 | apply H7];
    try (apply Classifier1; lra). destruct H as [H _], H0 as [H0 _].
    apply x_fx_T in H22,H23; auto. applyClassifier2 H22. applyClassifier2 H23.
    destruct H22 as [[] | []], H23 as [[] | []]; try (exfalso; lra).
    rewrite H24, H25; auto. apply x_fx_T; auto. }
  rewrite H23. apply H16. rewrite Abs_lt; lra.
Qed.

(* 函数相减的左极限等于两个函数的左极限相减 *)
Lemma Lemma6_10i : ∀ f g x0 A B, limit_neg f x0 A -> limit_neg g x0 B
  -> limit_neg (f \- g) x0 (A - B).
Proof.
  intros. pose proof H. pose proof H0. destruct H1 as [H1[δ1[H3[]]]], 
  H2 as [H2[δ2[H6[]]]]. destruct (Examp1 δ1 δ2) as [δ3[H9[]]]; auto. split.
  apply Corollary_sub_fun_a. exists δ3. split; auto. split.
  rewrite Corollary_sub_fun_c. red; intros. apply Classifier1; split; 
  [apply H4 | apply H7]; applyClassifier1 H12; apply Classifier1; lra.
  apply Lemma6_10g in H. apply Lemma6_10g in H0. clear H5 H8.
  remember (\{\ λ u v, u < x0 /\ v = f[u] \/ x0 < u /\ v = f[2 * x0 - u] \}\
    \- \{\ λ u v, u < x0 /\ v = g[u] \/ x0 < u /\ v = g[2 * x0 - u] \}\) as h.
  assert (limit h x0 (A - B)). { rewrite Heqh. apply Theorem3_7b; auto. }
  destruct H5 as [H5[δ4[H8[]]]]. intros. apply H13 in H14 as [δ5[[]]].
  destruct (Examp1 δ5 δ3) as [δ6[H17[]]]; auto. exists δ6. split. auto.
  intros x []. assert (x ∈ dom[h]).
  { rewrite Heqh,Corollary_sub_fun_c. apply Classifier1; split; apply Classifier1;
    [exists f[x] | exists g[x]]; apply Classifier2; left; split; auto. }
  assert ((f \- g)[x] = h[x]).
  { apply (H5 x). rewrite Heqh, Corollary_sub_fun_c in H22. applyClassifier1 H22.
    destruct H22. rewrite Heqh. apply Classifier2. repeat split; auto.
    rewrite Corollary_sub_fun_b; [ | apply H4 | apply H7];
    try (apply Classifier1; lra). destruct H as [H _], H0 as [H0 _].
    apply x_fx_T in H22,H23; auto. applyClassifier2 H22. applyClassifier2 H23.
    destruct H22 as [[] | []], H23 as [[] | []]; try (exfalso; lra).
    rewrite H24, H25; auto. apply x_fx_T; auto. }
  rewrite H23. apply H16. rewrite Abs_lt; lra.
Qed.

(* 函数相乘的左极限等于两个函数的左极限相乘 *)
Lemma Lemma6_10j : ∀ f g x0 A B, limit_neg f x0 A -> limit_neg g x0 B
  -> limit_neg (f \* g) x0 (A * B).
Proof.
  intros. pose proof H. pose proof H0. destruct H1 as [H1[δ1[H3[]]]], 
  H2 as [H2[δ2[H6[]]]]. destruct (Examp1 δ1 δ2) as [δ3[H9[]]]; auto. split.
  apply Corollary_mult_fun_a. exists δ3. split; auto. split.
  rewrite Corollary_mult_fun_c. red; intros.
  apply Classifier1; split; [apply H4 | apply H7]; applyClassifier1 H12; apply Classifier1; 
  lra. apply Lemma6_10g in H. apply Lemma6_10g in H0. clear H5 H8.
  remember (\{\ λ u v, u < x0 /\ v = f[u] \/ x0 < u /\ v = f[2 * x0 - u] \}\
    \* \{\ λ u v, u < x0 /\ v = g[u] \/ x0 < u /\ v = g[2 * x0 - u] \}\) as h.
  assert (limit h x0 (A * B)). { rewrite Heqh. apply Theorem3_7c; auto. }
  destruct H5 as [H5[δ4[H8[]]]]. intros. apply H13 in H14 as [δ5[[]]].
  destruct (Examp1 δ5 δ3) as [δ6[H17[]]]; auto. exists δ6. split. auto.
  intros x []. assert (x ∈ dom[h]).
  { rewrite Heqh, Corollary_mult_fun_c. apply Classifier1; split; apply Classifier1;
    [exists f[x] | exists g[x]]; apply Classifier2; left; split; auto. }
  assert ((f \* g)[x] = h[x]).
  { apply (H5 x). rewrite Heqh, Corollary_mult_fun_c in H22. applyClassifier1 H22.
    destruct H22. rewrite Heqh. apply Classifier2. repeat split; auto.
    rewrite Corollary_mult_fun_b; [ | apply H4 | apply H7];
    try (apply Classifier1; lra). destruct H as [H _], H0 as [H0 _].
    apply x_fx_T in H22,H23; auto. applyClassifier2 H22. applyClassifier2 H23.
    destruct H22 as [[] | []], H23 as [[] | []]; try (exfalso; lra).
    rewrite H24, H25; auto. apply x_fx_T; auto. }
  rewrite H23. apply H16. rewrite Abs_lt; lra.
Qed.

Lemma Lemma6_10k : ∀ f g a b, ContinuousClose f a b
  -> ContinuousClose g a b -> ContinuousClose (f \+ g) a b.
Proof.
  intros. destruct H as [H[]], H0 as [H0[]]. split. red; intros.
  apply Theorem4_4a; [apply H | apply H0]; auto. clear H H0.
  destruct H1, H2, H3, H4. split; split; try rewrite Corollary_plus_fun_b;
  try (rewrite Corollary_plus_fun_c; apply Classifier1); auto;
  [apply Lemma6_10d | apply Lemma6_10h]; auto.
Qed.

Lemma Lemma6_10m : ∀ f g a b, ContinuousClose f a b
  -> ContinuousClose g a b -> ContinuousClose (f \- g) a b.
Proof.
  intros. destruct H as [H[]], H0 as [H0[]]. split. red; intros. 
  apply Theorem4_4b; [apply H | apply H0]; auto. clear H H0.
  destruct H1, H2, H3, H4. split; split; try rewrite Corollary_sub_fun_b;
  try (rewrite Corollary_sub_fun_c; apply Classifier1); auto;
  [apply Lemma6_10e | apply Lemma6_10i]; auto.
Qed.

Lemma Lemma6_10n : ∀ f g a b, ContinuousClose f a b
  -> ContinuousClose g a b -> ContinuousClose (f \* g) a b.
Proof.
  intros. destruct H as [H[]], H0 as [H0[]]. split. red; intros.
  apply Theorem4_4c; [apply H | apply H0]; auto. clear H H0.
  destruct H1, H2, H3, H4. split; split; try rewrite Corollary_mult_fun_b;
  try (rewrite Corollary_mult_fun_c; apply Classifier1); auto;
  [apply Lemma6_10f | apply Lemma6_10j]; auto.
Qed.

Lemma Lemma6_10p : ∀ f A x0 a, Function f -> limit_pos (f|[A]) x0 a
  -> limit_pos f x0 a.
Proof.
  intros. destruct H0 as [H0[x[H1[]]]]. split; auto. exists x.
  apply RestrictFun with (D := A) in H as [H[]]. repeat split; auto. 
  red; intros. apply H2 in H6. rewrite H4 in H6. applyClassifier1 H6; tauto. 
  intros. apply H3 in H6 as [x1[]]. exists x1. split; intros; auto. rewrite <-H5.
  apply H7 in H8; auto. apply H2, Classifier1. lra.
Qed.

Lemma Lemma6_10q : ∀ f A x0 a, Function f -> limit_neg (f|[A]) x0 a
  -> limit_neg f x0 a.
Proof.
  intros. destruct H0 as [H0[x[H1[]]]]. split; auto. exists x.
  apply RestrictFun with (D := A) in H as [H[]]. repeat split; auto. 
  red; intros. apply H2 in H6. rewrite H4 in H6. applyClassifier1 H6; tauto. 
  intros. apply H3 in H6 as [x1[]]. exists x1. split; intros; auto. rewrite <-H5.
  apply H7 in H8; auto. apply H2, Classifier1. lra.
Qed.

Lemma Lemma6_10r : ∀ f A a b, Function f -> ContinuousClose (f|[A]) a b
  -> ContinuousClose f a b.
Proof.
  intros. pose proof H. apply (@RestrictFun _ _ f A) in H1 as [_[]].
  destruct H0 as [H0[]]. destruct H3, H4. split. red; intros. apply H0 in H7 as [].
  split. rewrite H1 in H7. applyClassifier1 H7; tauto. rewrite H2 in H8; auto. 
  apply Lemma3_12 in H8; auto. split; split; try (rewrite H1 in H3, H4; 
  applyClassifier1 H3; applyClassifier1 H4; tauto); rewrite H2 in H5,H6; auto; 
  [apply Lemma6_10p in H5 | apply Lemma6_10q in H6]; auto.
Qed.

Lemma Lemma6_10s : ∀ f A x y, Function f -> Derivative (f|[A]) x y
  -> Derivative f x y.
Proof.
  intros. pose proof H. apply (@RestrictFun _ _ f A) in H1 as [_[]].
  apply (EleFun_Fact11 (f|[A]) f x y) in H0; auto. destruct H0 as [H0[[δ[]]_]].
  exists δ. split; auto. intros. apply H4 in H5. split; auto. rewrite H1 in H5.
  applyClassifier1 H5; tauto.
Qed.

(* 泰勒定理的核心是找到拉格朗日余项 *)
Section taylor_equation_L.

(* 被展开的函数 *)
Variable f : @set (@prod R R).
Hypothesis Function_f : Function f.

(* 展开的区间范围 *)
Variable a b : R.
Hypothesis a_less_b : a < b.

(* 展开至n阶 *)
Variable n : nat.

(* f在区间[a,b]中需要有n阶连续导函数 *)
Hypothesis f_Derivable_Continuous : ContinuousClose (dN f 1) a b
  /\ (∀ m, (m <= n)%nat -> ContinuousClose (dN f m) a b).

(* 可证明: f在区间(a,b)上n阶可导 *)
Let f_Derivable1 : ∀ m x, (m <= n)%nat -> x ∈ \(a, b\) 
  -> Derivable (dN f (m - 1)) x.
Proof.
  intros. destruct m. simpl. destruct f_Derivable_Continuous as [[H2 _]_].
  applyClassifier1 H0. apply H2 in H0 as [H0[]]. apply x_fx_T in H0; auto.
  applyClassifier2 H0. red; eauto. apply f_Derivable_Continuous in H as [H _].
  applyClassifier1 H0. apply H in H0 as [H0[H1 _]]. apply x_fx_T in H0; auto.
  replace (S m - 1)%nat with m; [ | lia]. applyClassifier2 H0. red; eauto.
Qed.

(* f在区间(a,b)上n+1阶可导 *)
Hypothesis f_Derivable2 : ∀ x, x ∈ \(a, b\) -> Derivable (dN f n) x.


Let a_b_in_domf : ∀ m, (m <= n)%nat -> \[a, b\] ⊂ dom[dN f m].
Proof.
  red; intros. destruct f_Derivable_Continuous. apply H2 in H as [H[]].
  applyClassifier1 H0. assert (a < z < b \/ a = z \/ b = z). lra. destruct H5. 
  apply H in H5 as []; auto. destruct H3,H4. destruct H5; rewrite <-H5; auto.
Qed.

(* 任意给定的 x0 和 x1 *)
Variable x0 x1 : R.

Hypothesis x0_in_a_b : x0 ∈ \[a, b\].
Hypothesis x1_in_a_b : x1 ∈ \[a, b\].

(* 泰勒多项式 *)
Let T_poly t := Σ \{\ λ u v, v = ((dN f u)[t]/(INR (u!))) * (x1 - t)^u \}\ n.

(* 泰勒多项式在区间[a,b]上连续 *)
Let T_poly_Continuous : ContinuousClose \{\ λ u v, v = T_poly u \}\ a b.
Proof.
  induction n.
  - unfold T_poly. simpl.
    assert (\{\ λ u v, v = \{\ λ u0 v0, v0 
      = (dN f u0)[u]/(INR (u0!)) * (x1 - u)^u0 \}\[0%nat] \}\ | [dom[f]] = f).
    { apply AxiomI; split; intros; destruct z. applyClassifier1 H. destruct H.
      applyClassifier2 H. rewrite FunValue in H. simpl in H. applyClassifier2 H0.
      destruct H0. apply x_fx_T in H0; auto. rewrite H.
      replace (f[x]/1 * 1) with f[x]; auto. lra. apply Classifier1. split.
      apply Classifier2. rewrite FunValue. simpl. apply f_x_T in H; auto.
      rewrite H. lra. apply Classifier2. split. apply Classifier1; eauto.
      apply Classifier1; auto. }
    assert (0 <= 0)%nat by lia. apply f_Derivable_Continuous in H0.
    simpl in H0. destruct H0 as [H0[]].
    assert (∀ x, \{\ λ u v, v = \{\ λ u0 v0, v0 
      = (dN f u0)[u]/(INR (u0!)) * (x1 - u)^u0 \}\[0%nat] \}\[x] = f[x]).
    { intros. rewrite FunValue,FunValue. simpl. lra. }
    assert (Function \{\ λ u v, v = \{\ λ u0 v0, v0 
      = (dN f u0)[u]/(INR (u0!)) * (x1 - u)^u0 \}\ [0%nat] \}\).
    { red; intros. applyClassifier2 H4. applyClassifier2 H5. subst; auto. }
    assert (∀ x, x ∈ dom[\{\ λ u v, v = \{\ λ u0 v0, v0 
      = (dN f u0)[u]/(INR (u0!)) * (x1 - u)^u0 \}\[0%nat] \}\]).
    { intros. apply Classifier1. exists f[x]. apply Classifier2. rewrite FunValue. 
      simpl. lra. } split; [ | split]; split; auto; rewrite H3.
    apply H0 in H6 as []. pattern f at 1 in H7. rewrite <- H in H7. 
    apply Lemma3_12 in H7; auto. destruct H1. pattern f at 1 in H6. 
    rewrite <- H in H6. apply Lemma6_10p in H6; auto. destruct H2. 
    pattern f at 1 in H6. rewrite <- H in H6. apply Lemma6_10q in H6; auto.
  - set (T_poly1 t := Σ \{\ λ u v, v 
      = ((dN f u)[t]/(INR (u!))) * (x1 - t)^u \}\ n0).
    assert (ContinuousClose \{\ λ u v, v = T_poly1 u \}\ a b).
    { apply IHn0; auto. destruct f_Derivable_Continuous. split; auto. intros. 
      apply (f_Derivable1 (S n0)) in H; auto. replace n0 with (S n0 - 1)%nat; 
      auto. lia. }
    assert (\{\ λ u v, v 
      = (dN f (S n0))[u]/(INR ((S n0)!)) * (x1 - u)^(S n0) \}\|[dom[dN f (S n0)]]
      = (dN f (S n0)) \* \{\ λ u v, v = /(INR ((S n0)!)) * (x1 - u)^(S n0) \}\).
    { remember (S n0). apply AxiomI; split; intros; destruct z. applyClassifier1 H0.
      destruct H0. applyClassifier2 H1. destruct H1 as [H1 _]. applyClassifier2 H0.
      apply Classifier2. repeat split; auto. apply Classifier1.
      exists (/(INR (n1!)) * (x1 - x)^n1). apply Classifier2; auto.
      rewrite H0, FunValue. lra. applyClassifier2 H0. destruct H0 as [H0[]].
      apply Classifier1. split. apply Classifier2. rewrite H2,FunValue. lra.
      apply Classifier2. split; auto. apply Classifier1; auto. }
    assert (ContinuousClose (dN f (S n0) \* \{\ λ u v, v 
      = /(INR ((S n0)!)) * (x1 - u)^(S n0) \}\) a b).
    { apply Lemma6_10n. apply f_Derivable_Continuous; auto.
      assert (∀ x, x ∈ dom[\{\ λ u v, v = /(INR ((S n0)!)) * (x1-u)^(S n0) \}\]).
      { intros. apply Classifier1. exists (/(INR ((S n0)!)) * (x1-x)^(S n0)).
        apply Classifier2; auto. } split. red; intros. apply Lemma6_10b. 
      split; split; auto; apply Theorem3_1; apply Lemma6_10b. }
    rewrite <-H0 in H1. apply Lemma6_10r in H1.
    assert (\{\ λ u v, v = T_poly u \}\ = \{\ λ u v, v = T_poly1 u \}\
      \+ \{\ λ u v, v = (dN f (S n0))[u]/(INR ((S n0)!)) * (x1 - u)^(S n0) \}\).
    { apply AxiomI; split; intros; destruct z; applyClassifier2 H2; apply Classifier2.
      repeat split. apply Classifier1. exists (T_poly1 x). apply Classifier2; auto.
      apply Classifier1. exists ((dN f (S n0))[x]/(INR ((S n0)!)) * (x1 - x)^(S n0)).
      apply Classifier2; auto. rewrite FunValue, FunValue. unfold T_poly in H2.
      simpl in H2. rewrite FunValue in H2; auto. destruct H2 as [_[_]].
      rewrite FunValue,FunValue in H2. unfold T_poly. simpl.
      rewrite FunValue; auto. } rewrite H2. apply Lemma6_10k; auto.
    red; intros. applyClassifier2 H2. applyClassifier2 H3. subst; auto.
Qed.

Let T_poly_Derivable : ∀ x, x ∈ \(a, b\)
  -> Derivative (\{\ λ u v, v = T_poly u \}\) x
    ((dN f (S n))[x]/(INR (n!)) * (x1-x)^n).
Proof.
  intros. clear T_poly_Continuous. induction n.
  - rewrite dN_Fact3. simpl. assert (\{\ λ u v, v = T_poly u \}\ | [dom[f]] = f).
    { apply AxiomI; split; intros; destruct z. applyClassifier1 H0. destruct H0.
      applyClassifier2 H1. destruct H1 as [H1 _]. applyClassifier2 H0.
      unfold T_poly in H0. simpl in H0. rewrite FunValue in H0. simpl in H0.
      replace y with f[x2]. apply x_fx_T; auto. rewrite H0; lra. apply Classifier1.
      split. apply Classifier2. unfold T_poly. simpl. rewrite FunValue. simpl. 
      apply f_x_T in H0; auto. rewrite H0; lra. apply Classifier2. split. 
      apply Classifier1; eauto. apply Classifier1; auto. } apply f_Derivable2 in H. 
    destruct H. simpl in H. pose proof H. apply Corollary_DerivativeValue_a in H1.
    rewrite H1. rewrite <- H0 in H. apply Lemma6_10s in H. 
    replace (x2/1 * 1) with x2; auto. lra. red; intros. applyClassifier2 H2.
    applyClassifier2 H3. subst; auto.
  - set (T_poly1 t := Σ \{\ λ u v, v 
      = ((dN f u)[t]/(INR (u!))) * (x1 - t)^u \}\ n0).
    assert (Derivative \{\ λ u v, v = T_poly1 u \}\ x
      ((dN f (S n0))[x]/(INR (n0!)) * (x1 - x)^n0)).
    { apply IHn0; auto. destruct f_Derivable_Continuous. split; auto. intros. 
      apply (f_Derivable1 (S n0)) in H0; auto. replace n0 with (S n0 - 1)%nat; 
      auto. lia. } remember (S n0).
    assert (\{\ λ u v, v = T_poly u \}\ = \{\ λ u v, v = T_poly1 u \}\
      \+ \{\ λ u v, v = (dN f n1)[u]/(INR (n1!)) * (x1 - u)^n1 \}\).
    { apply AxiomI; split; intros; destruct z; applyClassifier2 H1; apply Classifier2.
      repeat split. apply Classifier1. exists (T_poly1 x2). apply Classifier2; auto.
      apply Classifier1. exists ((dN f n1)[x2]/(INR (n1!)) * (x1 - x2)^n1).
      apply Classifier2; auto. rewrite FunValue,FunValue. unfold T_poly in H1.
      rewrite Heqn1 in H1. simpl in H1. rewrite Heqn1. rewrite FunValue in H1; 
      auto. destruct H1 as [_[_]]. rewrite FunValue,FunValue in H1. 
      unfold T_poly. rewrite Heqn1 in *. simpl. rewrite FunValue; auto. }
    assert (\{\ λ u v, v 
      = (dN f n1)[u]/(INR (n1!)) * (x1 - u)^n1 \}\|[dom[dN f n1]]
      = (dN f n1) \* \{\ λ u v, v = /(INR (n1!)) * (x1 - u)^n1 \}\).
    { apply AxiomI; split; intros; destruct z. applyClassifier1 H2. destruct H2.
      applyClassifier2 H2. applyClassifier2 H3. destruct H3. apply Classifier2.
      repeat split; auto. apply Classifier1. exists (/(INR (n1!)) * (x1 - x2)^n1).
      apply Classifier2; auto. rewrite FunValue, H2. lra. applyClassifier2 H2.
      destruct H2 as [H2[_]]. apply Classifier1. split. apply Classifier2. rewrite H3,
      FunValue; lra. apply Classifier2. split; auto. apply Classifier1; auto. }
    pose proof (Lemma6_10a (/(INR (n1!))) x1 x n1).
    assert (Derivable \{\ λ u v, v = /(INR (n1!)) * (x1 - u)^n1 \}\ x).
    { red; eauto. } apply Corollary_DerivativeValue_a in H3.
    apply (Theorem5_5b (dN f n1)) in H4; auto. rewrite FunValue, H3 in H4.
    assert ((dN f (S n1))[x]/(INR (n1!)) * (x1 - x)^n1
      = ((dN f n1)[x]/(INR (n0!)) * (x1 - x)^n0)
       + ((dN f n1)’[x] * (/(INR (n1!)) * (x1 - x)^n1) +
         -INR n1 * /(INR (n1!)) * (x1 - x)^(n1 - 1) * (dN f n1)[x])).
    { rewrite dN_Fact3. replace (n1 - 1)%nat with n0; [ | lia].
      replace (-(INR n1) * /(INR (n1!)) * (x1 - x)^n0 * (dN f n1)[x])
      with (-((INR n1) * /(INR (n1!)) * (x1 - x)^n0 * (dN f n1)[x])); [ | lra].
      replace (INR n1 * /(INR (n1!))) with (/(INR (n0!))). lra. rewrite Heqn1. 
      simpl ((S n0)!). replace (n0! + n0 * n0!)%nat with ((S n0) * n0!)%nat; 
      [ | lia]. rewrite mult_INR,Rinv_mult,<-Rmult_assoc,Rinv_r,Rmult_1_l;
      try apply not_0_INR; auto. }
    rewrite <-H2 in H4. apply Lemma6_10s in H4. pose proof H0. pose proof H4.
    apply Corollary_DerivativeValue_a in H6. 
    apply Corollary_DerivativeValue_a in H7. rewrite H1, H5, <- H6, <- H7.
    apply Theorem5_4a; red; eauto. red; intros. applyClassifier2 H6.
    applyClassifier2 H7. subst; auto.
Qed.

(* 辅助函数F和G *)
Let F := \{\ λ u v, v = f[x1] \}\ \- \{\ λ u v, v = T_poly u \}\.
Let G := \{\ λ u v, v = (x1 - u)^(S n) \}\.

(* 使用柯西中值定理所需条件 *)

Let F_Continuous : ContinuousClose F a b.
Proof.
  apply Lemma6_10m; auto.
  assert (∀ x c, Continuous \{\ λ u v, v = c \}\ x).
  { intros. split. apply Classifier1. exists c. apply Classifier2; auto.
    rewrite FunValue. apply EleFun_Fact15. } split. red; intros; auto.
  pose proof (H a f[x1]). pose proof (H b f[x1]). destruct H0, H1. 
  apply Theorem3_1 in H2 as []. apply Theorem3_1 in H3 as []. split; split; auto.
Qed.

Let G_Continuous : ContinuousClose G a b.
Proof.
  assert (G = \{\ λ u v, v = 1 * (x1 - u)^(S n) \}\).
  { apply AxiomI; split; intros; destruct z; applyClassifier2 H; apply Classifier2;
    rewrite H; simpl; lra. } rewrite H. split. red; intros. apply Lemma6_10b.
  split; apply Theorem4_1; apply Lemma6_10b.
Qed.

Let F_Derivable : ∀ x, x ∈ \(a, b\)
  -> Derivative F x (-((dN f (S n))[x]/(INR (n!)) * (x1 - x)^n)).
Proof.
  intros. apply T_poly_Derivable in H. pose proof H. 
  apply Corollary_DerivativeValue_a in H0.
  replace (-((dN f (S n))[x]/(INR (n!)) * (x1 - x)^n))
  with ((\{\ λ u v, v = f[x1] \}\)’[x] - (\{\ λ u v, v = T_poly u \}\)’[x]).
  apply Theorem5_4b; red; eauto. exists 0. apply EleFun_Fact14.
  rewrite H0. pose proof (EleFun_Fact14 f[x1] x).
  apply Corollary_DerivativeValue_a in H1. rewrite H1. lra.
Qed.

Let G_Derivable : ∀ x, Derivative G x (-(INR (S n)) * (x1 - x)^n).
Proof.
  intros. assert (G = \{\ λ u v, v = 1*(x1 - u)^(S n) \}\).
  { apply AxiomI; split; intros; destruct z; applyClassifier2 H; apply Classifier2;
    rewrite H; simpl; lra. } pose proof (Lemma6_10a 1 x1 x (S n)). 
  rewrite <- H in H0. simpl (S n - 1)%nat in H0. 
  rewrite Nat.sub_0_r, Rmult_1_r in H0; auto.
Qed.

Let G'_neq_0 : ∀ x, x <> x1 -> G’[x] <> 0.
Proof.
  intros. intro. elim H. pose proof G_Derivable x.
  apply Corollary_DerivativeValue_a in H1. rewrite H0 in H1. symmetry in H1. 
  apply Rmult_integral in H1 as []. assert (INR (S n) = 0) by lra. exfalso. 
  apply (not_0_INR (S n)); auto. apply PowR_Fact6 in H1. lra.
Qed.

Let F_eq_0 : F[x1] = 0.
Proof.
  unfold F. rewrite Corollary_sub_fun_b. rewrite FunValue,FunValue.
  assert (T_poly x1 = f[x1]).
  { clear f_Derivable1 f_Derivable2 a_b_in_domf T_poly_Derivable
    T_poly_Continuous T_poly_Continuous f_Derivable_Continuous. clear dependent F.
    clear dependent G. induction n.
    - unfold T_poly. simpl. rewrite FunValue. simpl. lra.
    - unfold T_poly. simpl. rewrite IHn0,FunValue,Rminus_diag. simpl.
      rewrite Rmult_0_l,Rmult_0_r. lra. } rewrite H. lra. apply Classifier1. 
  exists f[x1]. apply Classifier2; auto. apply Classifier1. exists (T_poly x1). 
  apply Classifier2; auto.
Qed.

Let G_eq_0 : G[x1] = 0.
Proof. 
  unfold G. rewrite FunValue,Rminus_diag. simpl. lra. 
Qed.

Let G_x0_neq_G_x1 : x0 <> x1 -> G[x0] <> G[x1].
Proof.
  intros. unfold G. intro. rewrite FunValue,FunValue,Rminus_diag in H0.
  simpl (0^(S n)) in H0. rewrite Rmult_0_l in H0. apply PowR_Fact6 in H0. lra.
Qed.

Let F_and_G : x0 <> x1
  -> ∃ ξ, ξ ∈ \(a, b\) /\ F[x0]/G[x0] = (dN f (S n))[ξ]/(INR ((S n)!)).
Proof.
  intros.
  assert (∃ ξ, a < ξ < b /\ ξ <> x1
    /\ F’[ξ]/G’[ξ] = (F[x0] - F[x1])/(G[x0] - G[x1])).
  { assert (∀ y0 y1, y0 ∈ \[a, b\] -> y1 ∈ \[a, b\] -> y0 < y1
      -> ContinuousClose F y0 y1 ).
    { intros. destruct F_Continuous as [H3[]]. applyClassifier1 H0. applyClassifier1 H1. 
      split. red; intros. assert (a < x < b) by lra. apply H3 in H7; auto. split.
      assert (y0 = a \/ a < y0 < b) by lra. destruct H6. rewrite H6; auto. 
      apply H3 in H6. apply Theorem4_1; auto. 
      assert (y1 = b \/ a < y1 < b) by lra. destruct H6. rewrite H6; auto.
      apply H3 in H6. apply Theorem4_1; auto. }
    assert (∀ y0 y1, y0 ∈ \[a, b\] -> y1 ∈ \[a, b\] -> y0 < y1
      -> ContinuousClose G y0 y1 ).
    { intros. destruct G_Continuous as [H4[]]. applyClassifier1 H1. applyClassifier1 H2. 
      split. red; intros. assert (a < x < b) by lra. apply H4 in H8; auto. split.
      assert (y0 = a \/ a < y0 < b) by lra. destruct H7. rewrite H7; auto. 
      apply H4 in H7. apply Theorem4_1; auto. assert (y1 = b \/ a < y1 < b) by lra.
      destruct H7. rewrite H7; auto. apply H4 in H7. apply Theorem4_1; auto. }
    assert (∀ y0 y1 x, y0 ∈ \[a, b\] -> y1 ∈ \[a, b\] -> y0 < x < y1
      -> Derivable F x).
    { intros. applyClassifier1 H2. applyClassifier1 H3. assert (x ∈ \(a, b\)). 
      { apply Classifier1; lra. } apply F_Derivable in H5. red; eauto. }
    assert (x0 < x1 \/ x1 < x0) by lra. destruct H3.
    - assert (∃ ξ, x0 < ξ < x1 /\ F’[ξ]/G’[ξ] = (F[x1] - F[x0])/(G[x1] - G[x0])).
      { apply Theorem6_6; auto. intros. apply H2 in H4; auto. intros.
        pose proof (G_Derivable x). red; eauto. intros. apply not_and_or. right.
        apply G'_neq_0. lra. assert (x0 <> x1) by auto. 
        apply G_x0_neq_G_x1 in H4; auto. } destruct H4 as [ξ[]].
      assert (G[x0] <> G[x1]). { apply G_x0_neq_G_x1; lra. }
      assert (G[x1] - G[x0] <> 0) by lra. exists ξ. split. 
      applyClassifier1 x0_in_a_b. applyClassifier1 x1_in_a_b. lra. split. lra.
      replace ((F[x0] - F[x1])/(G[x0] - G[x1]))
      with ((-1 * (F[x0] - F[x1]))/(-1 * (G[x0] - G[x1]))).
      replace (-1 * (F[x0] - F[x1])) with (F[x1] - F[x0]); [ | lra].
      replace (-1 * (G[x0] - G[x1])) with (G[x1] - G[x0]); auto. lra.
      unfold Rdiv. rewrite Rinv_mult,Rmult_assoc,<-(Rmult_assoc _ (/-1)),
      (Rmult_comm _ (/-1)),<-Rmult_assoc,<-Rmult_assoc,<- Rinv_r_sym,Rmult_1_l;
      auto; lra.
    - assert (∃ ξ, x1 < ξ < x0 /\ F’[ξ]/G’[ξ] = (F[x0] - F[x1])/(G[x0] - G[x1])).
      { apply Theorem6_6; auto. intros. apply H2 in H4; auto. intros.
        pose proof (G_Derivable x). red; eauto. intros. apply not_and_or.
        right. apply G'_neq_0. lra. } destruct H4 as [ξ[]]. exists ξ.
      split. applyClassifier1 x0_in_a_b. applyClassifier1 x1_in_a_b. lra. split; lra. } 
  destruct H0 as [ξ[H0[]]]. exists ξ. split. apply Classifier1; auto.
  assert (ξ ∈ \(a, b\)). { apply Classifier1; auto. } apply F_Derivable in H3. 
  pose proof (G_Derivable ξ). apply Corollary_DerivativeValue_a in H3.
  apply Corollary_DerivativeValue_a in H4. rewrite H3, H4, F_eq_0, G_eq_0, 
  Rminus_0_r, Rminus_0_r in H2. rewrite <-H2.
  replace (-(INR (S n)) * (x1 - ξ)^n) with (-((INR (S n)) * (x1 - ξ)^n)); 
  [ | lra]. apply G'_neq_0 in H1. rewrite H4 in H1. 
  assert ((INR (S n)) * (x1 - ξ)^n <> 0) by lra.
  assert (INR (S n) <> 0 /\ (x1 - ξ)^n <> 0) as [].
  { apply NNPP; intro. apply not_and_or in H6 as [];
    apply ->NNPP in H6; elim H5; rewrite H6; lra. } unfold Rdiv.
  rewrite Rinv_opp,Rmult_opp_opp,Rinv_mult,
  Rmult_assoc,<-(Rmult_assoc ((x1 - ξ)^n)),Rinv_r_simpl_m; auto.
  pose proof (Factorial_Fact1 n). apply lt_INR in H8. simpl in H8.
  rewrite Rmult_assoc,<-Rinv_mult,<-mult_INR; auto. simpl ((S n)!).
  rewrite Nat.mul_comm. simpl ((S n) * (n!))%nat; auto.
Qed.

Theorem Theorem6_10 : ∃ ξ, ξ ∈ \(a, b\)
  /\ f[x1] = (T_poly x0) + (dN f (S n))[ξ]/(INR ((S n)!)) * (x1 - x0)^(S n).
Proof.
  assert (x0 = x1 \/ x0 <> x1) by lra. destruct H.
  - exists ((a + b)/2). split. apply Classifier1. lra. rewrite H,Rminus_diag.
    simpl. rewrite Rmult_0_l, Rmult_0_r, Rplus_0_r. unfold T_poly.
    clear dependent T_poly. clear dependent G. clear dependent a. induction n. 
    simpl. rewrite FunValue. simpl. lra. simpl. rewrite FunValue.
    rewrite IHn0,Rminus_diag. simpl.
    rewrite Rmult_0_l,Rmult_0_r,Rplus_0_r; auto.
  - pose proof H. apply G_x0_neq_G_x1 in H. rewrite G_eq_0 in H.
    apply F_and_G in H0 as [ξ[]]. exists ξ. split; auto. rewrite <- H1.
    assert ((x1 - x0)^(S n) = G[x0]). { unfold G. rewrite FunValue; auto. }
    unfold Rdiv. rewrite H2,Rmult_comm,<-Rmult_assoc,Rinv_r_simpl_m; auto.
    unfold F. rewrite Corollary_sub_fun_b, FunValue, FunValue; try lra;
    apply Classifier1; [exists f[x1] | exists (T_poly x0)]; apply Classifier2; auto.
Qed.

End taylor_equation_L.

(* 6.4 函数的极值与最大(小)值 *)

(* 极值的第一充分条件 *)
Lemma Lemma6_11 : ∀ x x0 δ, δ > 0 -> x ∈ U(x0; δ)
  -> x ∈ \(x0 - δ, x0\) \/ x= x0 \/ x ∈ \(x0, x0+δ\).
Proof.
  intros. applyClassifier1 H0. apply Abs_R in H0 as []. 
  destruct (Req_appart_dec x x0) as [H2 | []]; auto; [left | right; right];
  apply Classifier1; lra.
Qed.

Theorem Theorem6_11a : ∀ f x0 δ, 0 < δ -> Continuous f x0
  -> (∀ x, x ∈ Uº(x0; δ) -> Derivable f x)
  -> (∀ x, x ∈ \(x0 - δ, x0\) -> f’[x] <= 0) 
  -> (∀ x, x ∈ \(x0, x0 + δ\) -> f’[x] >= 0) 
  -> LocalMin f x0.
Proof.
  intros. assert (DDecreaseFun f \(x0 - δ, x0\)).
  { apply Theorem6_3b; auto. split. lra.
    assert (\(x0 - δ, x0\) ⊂ Uº(x0; δ)).
    { red; intros. applyClassifier1 H4. apply Classifier1. destruct H4. rewrite Abs_lt;
      lra. }
    split. red; intros. apply H4,H1 in H5 as [y[_[[x[]]_]]]. apply H6,Classifier1.
    rewrite Abs_ge; lra. intros. apply H1. applyClassifier1 H5. apply Classifier1.
    rewrite Abs_lt; lra. }
  assert (DIncreaseFun f \(x0, x0 + δ\)).
  { apply Theorem6_3a; auto. split. lra.
    assert (\(x0, x0+δ\) ⊂ Uº(x0; δ)).
    { red; intros. applyClassifier1 H5. apply Classifier1. destruct H5. rewrite Abs_gt; 
      lra. }
    split. red; intros. apply H5,H1 in H6 as [y[_[[x[]]_]]]. apply H7,Classifier1.
    rewrite Abs_ge; lra. intros. apply H1. applyClassifier1 H6. apply Classifier1.
    rewrite Abs_gt; lra. }
  assert (∀ x, x ∈ \(x0 - δ, x0\) -> f[x0] <= f[x]).
  { intros. destruct (Rle_or_lt f[x0] f[x]); auto.
    destruct H0 as [H0[H8[x1[H9[]]]]]. assert (f[x0] - f[x] > 0) by lra.
    apply H11 in H12 as [x2[[]]]. applyClassifier1 H6. destruct H6.
    destruct (Examp1 x2 (x0 - x)) as [x3[H16[]]]; auto. lra.
    assert (0 < ∣(x0 - x3 - x0)∣ < x2).
    { replace (x0 - x3 - x0) with (-x3). rewrite Abs_lt; lra. lra. }
    assert (f[x] >= f[x0 - x3]).
    { destruct H4 as [_[]]. apply H20; try lra; apply Classifier1; lra. }
    assert (f[x0] >= f[x0 - x3]) by lra.
    apply H14 in H19. assert (∣(f[x0 - x3] - f[x0])∣ = f[x0] - f[x0 - x3]).
    { destruct H21. rewrite Abs_lt; lra. rewrite Abs_ge; lra. }
    rewrite H22 in H19. assert (f[x] < f[x0 - x3]) by lra. exfalso. lra. }
  assert (∀ x, x ∈ \(x0, x0 + δ\) -> f[x0] <= f[x]).
  { intros. destruct (Rle_or_lt f[x0] f[x]); auto.
    destruct H0 as [H0[H9[x1[H10[]]]]]. assert (f[x0] - f[x] > 0) by lra.
    apply H12 in H13 as [x2[[]]]. applyClassifier1 H7. destruct H7.
    destruct (Examp1 x2 (x - x0)) as [x3[H17[]]]; auto. lra.
    assert (0 < ∣(x0 + x3 - x0)∣ < x2).
    { replace (x0 + x3 - x0) with x3. rewrite Abs_ge; lra. lra. }
    assert (f[x0 + x3] <= f[x]).
    { destruct H5 as [_[]]. apply H21; try lra; apply Classifier1; lra. }
    assert (f[x0] >= f[x0 + x3]) by lra.
    apply H15 in H20. assert (∣(f[x0 + x3] - f[x0])∣ = f[x0] - f[x0 + x3]).
    { destruct H22. rewrite Abs_lt; lra. rewrite Abs_ge; lra. }
    rewrite H23 in H20. assert (f[x] < f[x0 + x3]) by lra. exfalso. lra. }
  split. destruct H0 as [_[]]; auto. exists δ. split; auto. split. red; intros.
  destruct (classic (z = x0)). rewrite H9. destruct H0; auto.
  assert (z ∈ Uº(x0; δ)).
  { apply Classifier1. applyClassifier1 H8. split; auto. apply Abs_not_eq_0. lra. }
  apply H1 in H10 as [y[_[[x[]]_]]]. apply H11. apply Classifier1. rewrite Abs_ge; lra.
  intros. apply Lemma6_11 in H8 as [H8 | []]; auto. rewrite H8; lra.
Qed.

Theorem Theorem6_11b : ∀ f x0 δ, 0 < δ -> Continuous f x0
  -> (∀ x, x ∈ Uº(x0; δ) -> Derivable f x) 
  -> (∀ x, x ∈ \(x0 - δ, x0\) -> f’[x] >= 0)
  -> (∀ x, x ∈ \(x0, x0 + δ\) -> f’[x] <= 0)
  -> LocalMax f x0.
Proof.
  intros. assert (DIncreaseFun f \(x0 - δ, x0\)).
  { apply Theorem6_3a; auto. split. lra.
    assert (\(x0 - δ, x0\) ⊂ Uº(x0; δ)).
    { red; intros. applyClassifier1 H4. apply Classifier1. destruct H4. rewrite Abs_lt;
      lra. }
    split. red; intros. apply H4,H1 in H5 as [y[_[[x[]]_]]]. apply H6,Classifier1.
    rewrite Abs_ge; lra. intros. apply H1. applyClassifier1 H5. apply Classifier1.
    rewrite Abs_lt; lra. }
  assert (DDecreaseFun f \(x0, x0 + δ\)).
  { apply Theorem6_3b; auto. split. lra.
    assert (\(x0, x0 + δ\) ⊂ Uº(x0; δ)).
    { red; intros. applyClassifier1 H5. apply Classifier1. destruct H5. rewrite Abs_gt;
      lra. }
    split. red; intros. apply H5,H1 in H6 as [y[_[[x[]]_]]]. apply H7, Classifier1.
    rewrite Abs_ge; lra. intros. apply H1. applyClassifier1 H6. apply Classifier1.
    rewrite Abs_gt; lra. }
  assert (∀ x, x ∈ \(x0 - δ, x0\) -> f[x] <= f[x0]).
  { intros. destruct (Rle_or_lt f[x] f[x0]); auto.
    destruct H0 as [H0[H8[x1[H9[]]]]]. assert (f[x] - f[x0] > 0) by lra.
    apply H11 in H12 as [x2[[]]]. applyClassifier1 H6. destruct H6.
    destruct (Examp1 x2 (x0 - x)) as [x3[H16[]]]; auto. lra.
    assert (0 < ∣(x0 - x3 - x0)∣ < x2).
    { replace (x0 - x3 - x0) with (-x3). rewrite Abs_lt; lra. lra. }
    assert (f[x] <= f[x0 - x3]).
    { destruct H4 as [_[]]. apply H20; try lra; apply Classifier1; lra. }
    assert (f[x0] <= f[x0 - x3]) by lra.
    apply H14 in H19. rewrite Abs_ge in H19; lra. }
  assert (∀ x, x ∈ \(x0, x0 + δ\) -> f[x] <= f[x0]).
  { intros. destruct (Rle_or_lt f[x] f[x0]); auto.
    destruct H0 as [H0[H9[x1[H10[]]]]]. assert (f[x] - f[x0] > 0) by lra.
    apply H12 in H13 as [x2[[]]]. applyClassifier1 H7. destruct H7.
    destruct (Examp1 x2 (x - x0)) as [x3[H17[]]]; auto. lra.
    assert (0 < ∣(x0 + x3 - x0)∣ < x2).
    { replace (x0 + x3 - x0) with x3. rewrite Abs_ge; lra. lra. }
    assert (f[x0 + x3] >= f[x]).
    { destruct H5 as [_[]]. apply H21; try lra; apply Classifier1; lra. }
    assert (f[x0] <= f[x0 + x3]) by lra.
    apply H15 in H20. rewrite Abs_ge in H20; lra. }
  split. destruct H0 as [_[]]; auto. exists δ. split; auto. split.
  red; intros. destruct (classic (z = x0)). rewrite H9. destruct H0; auto.
  assert (z ∈ Uº(x0; δ)).
  { apply Classifier1. applyClassifier1 H8. split; auto. apply Abs_not_eq_0. lra. }
  apply H1 in H10 as [y[_[[x[]]_]]]. apply H11. apply Classifier1. rewrite Abs_ge; 
  lra. intros. apply Lemma6_11 in H8 as [H8 | []]; auto. rewrite H8; lra.
Qed.

(* 极值的第二充分条件 *)
Lemma Lemma6_12a : ∀ r o x0, r < 0 -> Infinitesimal o x0
  -> (∃ δ, 0 < δ /\ (∀ x, x ∈ Uº(x0; δ) -> o[x] + r < 0)).
Proof.
  intros. destruct H0 as [H0[x[H1[]]]]. assert (-r > 0) by lra.
  apply H3 in H4 as [x1[[]]]. exists x1. split; auto. intros. applyClassifier1 H7.
  apply H6 in H7. rewrite Rminus_0_r in H7. destruct (Rle_or_lt 0 o[x2]). 
  rewrite Abs_ge in H7; lra. lra.
Qed.

Theorem Theorem6_12a : ∀ f x0 δ, 0 < δ
  -> (∀ x, x ∈ U(x0; δ) -> Derivable f x) -> Derivable (dN f 1) x0 
  -> f’[x0] = 0 -> (dN f 2)[x0] < 0 -> LocalMax f x0.
Proof.
  intros. assert (Function f).
  { assert (x0 ∈ U(x0; δ)). { apply Classifier1. rewrite Abs_ge; lra. }
    apply H0 in H4 as [y[]]; auto. }
  assert (∀ k, (k < 2)%nat -> Derivable (dN f k) x0).
  { intros. assert (k = 0 \/ k = 1)%nat by lia. destruct H6; rewrite H6; auto.
    simpl. apply H0. apply Classifier1. rewrite Abs_ge; lra. }
  assert (0 < 2)%nat by lia. apply (Theorem6_9 f 2%nat x0) in H6 as [o[H6[]]];
  auto. split; auto. destruct H7 as [H7[]].
  assert ((dN f 2)[x0]/(INR (2!)) < 0).
  { apply Rmult_le_gr; split; auto. apply Rinv_0_lt_compat. apply lt_0_INR.
    apply Factorial_Fact1. }
  apply (Lemma6_12a _ (o // \{\ λ x y, y = (x - x0)^2 \}\) x0) in H11 as [x[]];
  auto. destruct (Examp1 δ x) as [x1[H13[]]]; auto. exists x1. split; auto.
  assert (U(x0; x1) ⊂ dom[f]).
  { red; intros. assert (z ∈ U(x0; δ)). { applyClassifier1 H16. apply Classifier1. lra. }
    apply H0 in H17 as [y[_[[x2[]]_]]]. apply H18, Classifier1. rewrite Abs_ge; lra. }
  split; auto. intros. pose proof H17. apply H16, H8 in H18. simpl in H18.
  rewrite FunValue, FunValue, FunValue in H18. rewrite dN_Fact3 in H18.
  simpl (dN f 0) in H18. rewrite H2 in H18.
  replace (f[x0]/(INR (0!)) * (x2 - x0)^0) with f[x0] in H18; [ | simpl; lra].
  replace (0/(INR (1!)) * (x2 - x0)^1) with 0 in H18; [ | lra].
  rewrite Rplus_0_r in H18. destruct (classic (x2 = x0)). rewrite H19; lra.
  assert (x2 ∈ Uº(x0; x)).
  { applyClassifier1 H17. apply Classifier1. split. apply Abs_not_eq_0; lra. lra. }
  apply H12 in H20. rewrite Corollary_div_fun_b,FunValue in H20.
  assert (0 < (x2 - x0)^2). { apply PowR_Fact8. lra. }
  apply (Rmult_lt_compat_r ((x2 - x0)^2)) in H20; auto.
  rewrite Rmult_0_l,Rmult_plus_distr_r in H20. assert ((x2 - x0)^2 <> 0) by lra.
  unfold Rdiv in H20. rewrite Rmult_assoc, (Rmult_comm (/(x2 - x0)^2)),
  <- Rmult_assoc, Rinv_r_simpl_l, Rplus_comm in H20; auto. lra. rewrite H6; auto.
  apply Classifier1. exists ((x2 - x0)^2). apply Classifier2; auto. rewrite FunValue.
  intro. apply PowR_Fact6 in H21. lra.
Qed.

Lemma Lemma6_12b : ∀ r o x0, 0 < r -> Infinitesimal o x0
  -> (∃ δ, 0 < δ /\ (∀ x, x ∈ Uº(x0; δ) -> 0 < o[x] + r)).
Proof.
  intros. destruct H0 as [H0[x[H1[]]]]. pose proof H. apply H3 in H4 as [x1[[]]].
  exists x1. split; auto. intros. applyClassifier1 H7. apply H6 in H7. 
  rewrite Rminus_0_r in H7. destruct (Rle_or_lt 0 o[x2]). rewrite Abs_ge in H7;
  lra. rewrite Abs_lt in H7; lra.
Qed.

Theorem Theorem6_12b : ∀ f x0 δ, 0 < δ -> (∀ x, x ∈ U(x0; δ) -> Derivable f x)
  -> Derivable (dN f 1) x0 -> f’[x0] = 0 -> 0 < (dN f 2)[x0] -> LocalMin f x0.
Proof.
  intros. assert (Function f).
  { assert (x0 ∈ U(x0; δ)). { apply Classifier1. rewrite Abs_ge; lra. }
    apply H0 in H4 as [y[]]; auto. }
  assert (∀ k, (k < 2)%nat -> Derivable (dN f k) x0).
  { intros. assert (k = 0 \/ k = 1)%nat by lia. destruct H6; rewrite H6; auto.
    simpl. apply H0. apply Classifier1. rewrite Abs_ge; lra. }
  assert (0 < 2)%nat by lia. apply (Theorem6_9 f 2%nat x0) in H6 as [o[H6[]]];
  auto. split; auto. destruct H7 as [H7[]].
  assert (0 < (dN f 2)[x0]/(INR (2!))).
  { apply Rmult_lt_0_compat; auto. apply Rinv_0_lt_compat. apply lt_0_INR.
    apply Factorial_Fact1. }
  apply (Lemma6_12b _ (o // \{\ λ x y, y = (x - x0)^2 \}\) x0) in H11 as [x[]];
  auto. destruct (Examp1 δ x) as [x1[H13[]]]; auto. exists x1. split; auto.
  assert (U(x0; x1) ⊂ dom[f]).
  { red; intros. assert (z ∈ U(x0; δ)). { applyClassifier1 H16. apply Classifier1. lra. }
    apply H0 in H17 as [y[_[[x2[]]_]]]. apply H18,Classifier1. rewrite Abs_ge; lra. }
  split; auto. intros. pose proof H17. apply H16, H8 in H18. simpl in H18.
  rewrite FunValue, FunValue,FunValue in H18. rewrite dN_Fact3 in H18.
  simpl (dN f 0) in H18. rewrite H2 in H18.
  replace (f[x0]/(INR (0!)) * (x2 - x0)^0) with f[x0] in H18; [ | simpl; lra].
  replace (0/(INR (1!)) * (x2 - x0)^1) with 0 in H18; [ | lra].
  rewrite Rplus_0_r in H18. destruct (classic (x2 = x0)). rewrite H19; lra.
  assert (x2 ∈ Uº(x0; x)).
  { applyClassifier1 H17. apply Classifier1. split. apply Abs_not_eq_0; lra. lra. }
  apply H12 in H20. rewrite Corollary_div_fun_b,FunValue in H20.
  assert (0 < (x2 - x0)^2). { apply PowR_Fact8. lra. }
  apply (Rmult_lt_compat_r ((x2 - x0)^2)) in H20; auto.
  rewrite Rmult_0_l, Rmult_plus_distr_r in H20. assert ((x2 - x0)^2 <> 0) by lra.
  unfold Rdiv in H20. rewrite Rmult_assoc, (Rmult_comm (/(x2 - x0)^2)),
  <- Rmult_assoc, Rinv_r_simpl_l, Rplus_comm in H20; auto. lra. rewrite H6; auto.
  apply Classifier1. exists ((x2 - x0)^2). apply Classifier2; auto. rewrite FunValue.
  intro. apply PowR_Fact6 in H21. lra.
Qed.

(* 极值的第三充分条件 *)
Lemma Lemma6_13a : ∀ f n x0, (0 < n)%nat -> Derivable (dN f (n - 1)) x0
  -> (∀ k, (k < n)%nat -> Derivable (dN f k) x0).
Proof.
  intros. induction n. exfalso. lia. assert (0 = n \/ 0 < n)%nat by lia. 
  destruct H2. assert (k = 0)%nat by lia. rewrite H3. simpl. 
  rewrite <- H2, Nat.sub_diag in H0. simpl in H0; auto.
  assert (k = n \/ k < n)%nat by lia. destruct H3. rewrite H3.
  replace (S n - 1)%nat with n in H0; auto. lia. apply IHn; auto.
  replace (S n - 1)%nat with (S (n - 1))%nat in H0; [ | lia].
  simpl in H0. destruct H0 as [y[H0[[x[]]_]]].
  assert (x0 ∈ U(x0; x)). { apply Classifier1. rewrite Abs_ge; lra. }
  apply H5 in H6. applyClassifier1 H6. destruct H6. applyClassifier2 H6. red; eauto.
Qed.

Fact Lemma6_13b : ∀ x n, x <> 0 -> (∃ k, n = (2 * k)%nat) -> 0 < x^n.
Proof.
  intros. destruct H0 as [k]. rewrite H0.
  assert (x^(2 * k) = (x^k)^2).
  { clear H0. induction k. simpl. lra. simpl (x^(S k)). rewrite <-PowR_Fact4,
    <- IHk, <- PowR_Fact1. replace (2 * (S k))%nat with (2 + 2 * k)%nat; auto.
    lia. } rewrite H1. apply PowR_Fact8. intro. apply PowR_Fact6 in H2; auto.
Qed.

Fact Lemma6_13c : ∀ x n, x < 0 -> (∃ k, n = (2 * k + 1)%nat) -> x^n < 0.
Proof.
  intros. destruct H0 as [k]. rewrite H0, PowR_Fact1, Rmult_comm.
  apply Rmult_le_gr. split. simpl; lra. apply Lemma6_13b; eauto. lra.
Qed.

Fact Lemma6_13d : ∀ f n, (0 < n)%nat -> (∀ k, (0 < k < n)%nat -> f[k] = 0)
  -> Σ f n = f[0%nat] + f[n].
Proof.
  intros. induction n. exfalso. lia. simpl. assert (n = 0 \/ 0 < n)%nat by lia.
  destruct H1. rewrite H1. simpl; auto. rewrite IHn; auto. rewrite (H0 n); auto.
  lra. intros. apply H0. lia.
Qed.

Theorem Theorem6_13a : ∀ f n x0 δ, (0 < n)%nat -> (∃ k, n = (2 * k)%nat)
  -> 0 < δ -> U(x0; δ) ⊂ dom[dN f (n - 1)] -> Derivable (dN f (n - 1)) x0
  -> (∀ k, (0 < k < n)%nat -> (dN f k)[x0] = 0) -> (dN f n)[x0] < 0
  -> LocalMax f x0.
Proof.
  intros. assert (∀ k, (k < n)%nat -> Derivable (dN f k) x0).
  { apply Lemma6_13a; auto. }
  assert (Function f). { apply H6 in H as [y[]]; auto. }
  pose proof H. apply (Theorem6_9 f n x0) in H8 as [o[H8[]]]; auto. split; auto.
  destruct H9 as [H9[]].
  assert ((dN f n)[x0]/(INR (n!)) < 0).
  { apply Rmult_le_gr; split; auto. apply Rinv_0_lt_compat. apply lt_0_INR.
    apply Factorial_Fact1. }
  apply (Lemma6_12a _ (o // \{\ λ x y, y = (x - x0)^n \}\) x0) in H13 as [x[]];
  auto. destruct (Examp1 δ x) as [x1[H15[]]]; auto. exists x1. split; auto.
  assert (U(x0; x1) ⊂ dom[f]).
  { red; intros. assert (z ∈ U(x0; δ)). 
    { applyClassifier1 H18. apply Classifier1. lra. }
    apply H2,dN_Fact2 in H19; auto. }
  split; auto. intros. pose proof H19. apply H18, H10 in H20.
  rewrite Lemma6_13d, FunValue, FunValue in H20; auto. simpl in H20.
  replace (f[x0]/1 * 1) with f[x0] in H20; [ | lra].
  destruct (classic (x2 = x0)). rewrite H21; lra.
  assert (x2 ∈ Uº(x0; x)).
  { applyClassifier1 H19. apply Classifier1. split. apply Abs_not_eq_0; lra. lra. }
  apply H14 in H22. rewrite Corollary_div_fun_b, FunValue in H22.
  assert (0 < (x2 - x0)^n). { apply Lemma6_13b; auto. lra. }
  apply (Rmult_lt_compat_r ((x2 - x0)^n)) in H22; auto.
  rewrite Rmult_0_l, Rmult_plus_distr_r in H22. assert ((x2 - x0)^n <> 0) by lra.
  unfold Rdiv in H22. rewrite Rmult_assoc, (Rmult_comm (/(x2 - x0)^n)),
  <- Rmult_assoc, Rinv_r_simpl_l, Rplus_comm in H22; auto. lra. rewrite H8; auto.
  apply Classifier1. exists ((x2 - x0)^n). apply Classifier2; auto. rewrite FunValue.
  intro. apply PowR_Fact6 in H23. lra. intros. rewrite FunValue. rewrite H4; auto.
  lra.
Qed.

Theorem Theorem6_13b : ∀ f n x0 δ, (0 < n)%nat -> (∃ k, n = (2 * k)%nat)
  -> 0 < δ -> U(x0; δ) ⊂ dom[dN f (n - 1)] -> Derivable (dN f (n - 1)) x0
  -> (∀ k, (0 < k < n)%nat -> (dN f k)[x0] = 0) -> 0 < (dN f n)[x0]
  -> LocalMin f x0.
Proof.
  intros. assert (∀ k, (k < n)%nat -> Derivable (dN f k) x0).
  { apply Lemma6_13a; auto. }
  assert (Function f). { apply H6 in H as [y[]]; auto. }
  pose proof H. apply (Theorem6_9 f n x0) in H8 as [o[H8[]]]; auto.
  split; auto. destruct H9 as [H9[]].
  assert (0 < (dN f n)[x0]/(INR (n!))).
  { apply Rmult_lt_0_compat; auto. apply Rinv_0_lt_compat. apply lt_0_INR.
    apply Factorial_Fact1. }
  apply (Lemma6_12b _ (o // \{\ λ x y, y = (x - x0)^n \}\) x0) in H13 as [x[]];
  auto. destruct (Examp1 δ x) as [x1[H15[]]]; auto. exists x1. split; auto.
  assert (U(x0; x1) ⊂ dom[f]).
  { red; intros. assert (z ∈ U(x0; δ)). 
    { applyClassifier1 H18. apply Classifier1. lra. }
    apply H2, dN_Fact2 in H19; auto. }
  split; auto. intros. pose proof H19. apply H18, H10 in H20.
  rewrite Lemma6_13d, FunValue, FunValue in H20; auto. simpl in H20.
  replace (f[x0]/1 * 1) with f[x0] in H20; [ | lra].
  destruct (classic (x2 = x0)). rewrite H21; lra.
  assert (x2 ∈ Uº(x0; x)).
  { applyClassifier1 H19. apply Classifier1. split. apply Abs_not_eq_0; lra. lra. }
  apply H14 in H22. rewrite Corollary_div_fun_b, FunValue in H22.
  assert (0 < (x2 - x0)^n). { apply Lemma6_13b; auto. lra. }
  apply (Rmult_lt_compat_r ((x2 - x0)^n)) in H22; auto.
  rewrite Rmult_0_l, Rmult_plus_distr_r in H22. assert ((x2 - x0)^n <> 0) by lra.
  unfold Rdiv in H22. rewrite Rmult_assoc, (Rmult_comm (/(x2 - x0)^n)),
  <- Rmult_assoc, Rinv_r_simpl_l, Rplus_comm in H22; auto. lra. rewrite H8; auto.
  apply Classifier1. exists ((x2 - x0)^n). apply Classifier2; auto. rewrite FunValue.
  intro. apply PowR_Fact6 in H23. lra. intros. rewrite FunValue. rewrite H4; auto.
  lra.
Qed.

Theorem Theorem6_13c : ∀ f n x0 δ, (0 < n)%nat -> (∃ k, n = (2 * k + 1)%nat)
  -> 0 < δ -> U(x0; δ) ⊂ dom[dN f (n - 1)] -> Derivable (dN f (n - 1)) x0
  -> (∀ k, (0 < k < n)%nat -> (dN f k)[x0] = 0) -> (dN f n)[x0] <> 0
  -> ~ LocalMax f x0 /\ ~ LocalMin f x0.
Proof.
  intros. assert (∀ k, (k < n)%nat -> Derivable (dN f k) x0).
  { apply Lemma6_13a; auto. }
  assert (Function f). { apply H6 in H as [y[]]; auto. }
  pose proof H. apply (Theorem6_9 f n x0) in H8 as [o[H8[]]]; auto.
  destruct H9 as [H9[]]. 
  assert (∀ x, x ∈ dom[f] -> x <> x0 -> f[x] - f[x0]
    = ((dN f n)[x0]/(INR (n!))+(o // \{\ λ u v, v = (u-x0)^n \}\)[x])*(x-x0)^n).
  { intros. pose proof H13. apply H10 in H15. rewrite Lemma6_13d in H15; auto.
    rewrite FunValue, FunValue in H15. simpl in H15.
    rewrite Corollary_div_fun_b, Rmult_plus_distr_r, FunValue.
    replace (o[x]/(x - x0)^n * (x - x0)^n) with o[x]. lra. unfold Rdiv.
    rewrite Rmult_assoc, (Rmult_comm (/(x-x0)^n)), <- Rmult_assoc, Rinv_r_simpl_l;
    auto. intro. apply PowR_Fact6 in H16. lra. rewrite H8; auto. apply Classifier1.
    exists ((x - x0)^n). apply Classifier2; auto. intro. rewrite FunValue in H16.
    apply PowR_Fact6 in H16; lra. intros. rewrite FunValue,H4; auto. lra. }
  assert ((dN f n)[x0]/(INR (n!)) <> 0).
  { intro. apply Rmult_integral in H14 as []; auto. 
    apply Rinv_neq_0_compat in H14; auto. apply not_0_INR.
    pose proof (Factorial_Fact1 n). lia. }
  assert (0 < (dN f n)[x0]/(INR (n!)) \/ (dN f n)[x0]/(INR (n!)) < 0) by lra.
  destruct H15.
  - apply (Lemma6_12b _ (o // \{\ λ x y, y = (x - x0)^n \}\) x0) in H15
    as [x1[]]; auto. destruct (Examp1 x1 δ) as [x2[H17[]]]; auto.
    assert (Uº(x0; x2) ⊂ dom[f]).
    { red; intros. apply (dN_Fact2 f (n-1)),H2. apply Classifier1.
      applyClassifier1 H20. lra. } split; intro; destruct H21 as [_[x[H21[]]]].
    + destruct (Examp1 x x2) as [x3[H24[]]]; auto.
      assert (0 < f[x0 + x3] - f[x0]).
      { rewrite H13. apply Rmult_lt_0_compat. rewrite Rplus_comm. apply H16.
        apply Classifier1. rewrite Abs_ge; lra. apply PowR_Fact3. lra.
        apply H22, Classifier1. rewrite Abs_ge; lra. lra. }
      assert (f[x0 + x3] <= f[x0]). { apply H23, Classifier1. rewrite Abs_ge; lra. }
      lra.
    + destruct (Examp1 x x2) as [x3[H24[]]]; auto.
      assert (f[x0 - x3] - f[x0] < 0).
      { rewrite H13. rewrite Rmult_comm. apply Rmult_le_gr. split.
        apply Lemma6_13c; auto. lra. rewrite Rplus_comm. apply H16,Classifier1.
        rewrite Abs_lt; lra. apply H22, Classifier1. rewrite Abs_lt; lra. lra. }
      assert (f[x0] <= f[x0 - x3]). { apply H23,Classifier1. rewrite Abs_lt; lra. }
      lra.
  - apply (Lemma6_12a _ (o // \{\ λ x y, y = (x - x0)^n \}\) x0) in H15 as [x1[]];
    auto. destruct (Examp1 x1 δ) as [x2[H17[]]]; auto.
    assert (Uº(x0; x2) ⊂ dom[f]).
    { red; intros. apply (dN_Fact2 f (n - 1)), H2. apply Classifier1.
      applyClassifier1 H20. lra. } split; intro; destruct H21 as [_[x[H21[]]]].
    + destruct (Examp1 x x2) as [x3[H24[]]]; auto.
      assert (0 < f[x0 - x3] - f[x0]).
      { rewrite H13. apply Rmult_le_le. split. rewrite Rplus_comm. apply H16.
        apply Classifier1. rewrite Abs_lt; lra. apply Lemma6_13c; auto. lra.
        apply H22, Classifier1. rewrite Abs_lt; lra. lra. }
      assert (f[x0 - x3] <= f[x0]). { apply H23,Classifier1. rewrite Abs_lt; lra. }
      lra.
    + destruct (Examp1 x x2) as [x3[H24[]]]; auto.
      assert (f[x0 + x3] - f[x0] < 0).
      { rewrite H13. apply Rmult_le_gr. split. rewrite Rplus_comm. 
        apply H16, Classifier1. rewrite Abs_ge; lra. apply PowR_Fact3. lra.
        apply H22, Classifier1. rewrite Abs_ge; lra. lra. }
      assert (f[x0] <= f[x0 + x3]).
      { apply H23, Classifier1. rewrite Abs_ge; lra. } lra.
Qed.

(* 6.5 函数的凸性与拐点 *)

(* 以下几个定义在实际使用时, 其中的I应该是一个区间(可开可闭) *)
(* 定义： 凸函数 *)
Definition Convex_Function f (I : @set R) := Function f /\ I ⊂ dom[f] 
    /\ (∀ (x1 x2 ξ: R), x1 ∈ I -> x2 ∈ I-> ξ ∈ \(0, 1\) 
  -> f[ξ * x1 + (1 - ξ) * x2] <= ξ * f[x1] + (1 - ξ) * f[x2]).

(* 定义： 凹函数 *)
Definition Concave_Function f (I : @set R) := Function f /\ I ⊂ dom[f] 
    /\ (∀ (x1 x2 ξ: R), x1 ∈ I -> x2 ∈ I-> ξ ∈ \(0, 1\)
  -> f[ξ * x1 + (1 - ξ) * x2] >= ξ * f[x1] + (1 - ξ) * f[x2]).

(* 定义： 严格凸函数 *)
Definition StrictlyConvex_Function f (I : @set R) := Function f /\ I ⊂ dom[f] 
    /\ (∀ (x1 x2 ξ: R), x1 ∈ I -> x2 ∈ I-> ξ ∈ \(0, 1\)
  -> f[ξ * x1 + (1 - ξ) * x2] < ξ * f[x1] + (1 - ξ) * f[x2]).

(* 定义： 严格凹函数 *)
Definition StrictlyConcave_Function f (I : @set R) := Function f /\ I ⊂ dom[f] 
    /\ (∀ (x1 x2 ξ: R), x1 ∈ I -> x2 ∈ I-> ξ ∈ \(0, 1\)
  -> f[ξ * x1 + (1 - ξ) * x2] > ξ * f[x1] + (1 - ξ) * f[x2]).

Lemma Lemma6_14 :  ∀ f (a b : R), Function f /\ \(a, b\) ⊂ dom[ f] 
  -> Convex_Function f \(a, b\)
    <-> (∀ x1 x2 x3, x1 ∈ \(a, b\) -> x2 ∈ \(a, b\) -> x3 ∈ \(a, b\)
      -> x1 < x2 < x3 -> (f[x2] - f[x1])/(x2 - x1) <= (f[x3] - f[x2])/(x3 - x2)).
Proof.
  intros f a b L. split; intros. 
  - assert (∃ ξ, ξ = (x3 - x2)/(x3 - x1)). { exists ((x3 - x2)/(x3 - x1)); auto. }
    destruct H4 as [ξ H4].
    assert (x2 = ξ * x1 + (1 - ξ) * x3).
    { assert (ξ * (x3 - x1) = x3 - x2).
      { rewrite H4. unfold Rdiv. rewrite Rmult_assoc, (Rmult_comm (/(x3 - x1))),
        <- Rmult_assoc, Rinv_r_simpl_l; auto. lra. } lra. } 
    red in H. destruct H as [H[H6 H7]]. destruct H3 as [H3 H3']. 
    apply (H7 x1 x3 ξ) in H0; auto. rewrite <- H5 in H0.
    assert (1 - ξ = (x2 - x1)/(x3 - x1)).
    { apply (Rmult_eq_reg_r (x3 - x1)). unfold Rdiv. rewrite Rmult_assoc.
      rewrite Rinv_l; lra. lra. } 
    rewrite H8 in H0. rewrite H4 in H0. apply (Rmult_le_compat_l (x3 - x1)) in H0.
    rewrite Rmult_plus_distr_l in H0. rewrite <- Rmult_assoc in H0. 
    unfold Rdiv in H0. rewrite <- Rmult_assoc in H0. rewrite Rinv_r_simpl_m in H0; 
    [ | lra]. rewrite Rplus_comm in H0. rewrite <- Rmult_assoc in H0;
    rewrite <- Rmult_assoc in H0. rewrite Rinv_r_simpl_m in H0; [ | lra];
    rewrite Rplus_comm in H0. rewrite Rmult_comm in H0.
    assert ((f[x2] - f[x1]) * (x3 - x2) <= (f[x3] - f[x2]) * (x2 - x1)). lra.
    assert (0 < /(x2 - x1) /\ 0 < /(x3 - x2)) as [].
    { split; apply Rinv_0_lt_compat; lra. }
    apply (Rmult_le_compat_r (/(x2 - x1))) in H9; [ | lra].
    rewrite Rinv_r_simpl_l in H9; [ | lra].
    apply (Rmult_le_compat_r (/(x3 - x2))) in H9; [ | lra].
    rewrite Rmult_assoc, Rmult_assoc, <- (Rmult_assoc (x3 - x2)), 
    Rinv_r_simpl_m in H9; lra. lra. rewrite H4. apply Classifier1. split; unfold Rdiv. 
    apply Rmult_gt_0_compat. lra. apply Rinv_0_lt_compat; lra. 
    apply (Rmult_lt_reg_r (x3-x1)). lra. rewrite Rmult_assoc. rewrite Rinv_l; lra.
  - red. destruct L. repeat split; auto. intros x1 x3 ξ H2 H3 H4. 
    destruct (classic (x1 = x3)).
    + rewrite H5.  replace (ξ * x3 + (1 - ξ) * x3) with x3. lra. lra.
    + apply Rdichotomy in H5. destruct H5.
      * assert (∃ x2, x2 = ξ * x1 + (1 - ξ) * x3 /\ x2 ∈ \(x1, x3\)).
        { exists (ξ * x1 + (1 - ξ)* x3); split; auto. apply Classifier1. 
          applyClassifier1 H4. cut ((1 - ξ) > 0); intros; [ | lra]. split. 
          apply (Rplus_gt_reg_l (-(ξ * x1))). rewrite <- Rplus_assoc.
          rewrite (Rplus_opp_l (ξ*x1)).  replace (-(ξ*x1)+x1) with ((1-ξ)*x1).
          apply (Rmult_gt_compat_l (1 - ξ) x3 x1) in H6; auto. lra. lra. 
          assert (ξ * x1 < x3 - (1 - ξ) * x3).
          { replace (x3 - (1 - ξ) * x3) with (ξ * x3). apply Rmult_lt_compat_l; 
            lra. lra. } lra. } destruct H6 as [x2[H6 H7]]. applyClassifier1 H7.
        assert (x2 ∈ \(a, b\)).
        { apply Classifier1. applyClassifier1 H2. applyClassifier1 H3. lra. } 
        apply (H x1 x2 x3) in H2; auto. rewrite <- H6. 
        assert (ξ = (x3 - x2)/(x3 - x1)). 
        { apply (Rmult_eq_reg_r (x3 - x1)); [ | lra]. unfold Rdiv. 
          rewrite Rmult_assoc. rewrite Rinv_l. lra. lra. }
        apply (Rmult_le_compat_r (x2 - x1)) in H2; [ | lra]. unfold Rdiv in H2. 
        rewrite Rmult_assoc in H2. rewrite Rinv_l in H2; [ | lra]. 
        rewrite Rmult_1_r in H2. rewrite Rmult_comm in H2.
        rewrite <- Rmult_assoc in H2. apply (Rmult_le_compat_r (x3 - x2)) in H2;
        [ | lra]. rewrite Rmult_assoc in H2. rewrite Rinv_l in H2; [ | lra]. 
        rewrite Rmult_1_r in H2. unfold Rminus. rewrite Rmult_plus_distr_r. 
        rewrite <- Rplus_comm. rewrite H9. unfold Rdiv. rewrite Rmult_assoc.
        apply (Rmult_le_reg_r (x3 - x1)). lra. rewrite Rmult_plus_distr_r.  
        replace ((x3 - x2)*(/(x3 - x1)*f[x1])*(x3 -x1)) with ((x3 - x2)*f[x1]).
        rewrite Rmult_plus_distr_r.
        replace (-((x3-x2)*/(x3-x1))*f[x3]*(x3-x1)) with (-(x3-x2)*f[x3]). lra. 
        symmetry. rewrite <- Rmult_comm. rewrite <- Rmult_assoc.
        replace ((x3 - x1) * -((x3 - x2) * /(x3 - x1))) with (-(x3 - x2)). lra.
        rewrite Ropp_mult_distr_l. rewrite <- Rmult_assoc.  
        apply (Rmult_eq_reg_r (x3 - x1)); [ | lra]. rewrite Rmult_assoc. 
        rewrite Rinv_l; lra. rewrite Rmult_assoc. 
        replace (/(x3 - x1) * f[x1] * (x3 - x1)) with (f[x1]). lra. 
        rewrite Rmult_comm. rewrite <- Rmult_assoc. rewrite Rinv_r_simpl_r; lra.
      * assert (∃ x2, x2 = ξ * x1 + (1 - ξ) * x3 /\ x2 ∈ \(x3, x1\)).
        { exists (ξ * x1 + (1 - ξ) * x3); split; auto. apply Classifier1. 
          applyClassifier1 H4. cut ((1 - ξ) > 0); intros; [ | lra]. split. 
          apply (Rplus_gt_reg_l (-(ξ * x1))). rewrite <- Rplus_assoc.
          rewrite (Rplus_opp_l (ξ * x1)). unfold Rminus. 
          rewrite Rmult_plus_distr_r. rewrite Rplus_0_l. rewrite Rmult_1_l. 
          rewrite Rplus_comm. apply Rplus_gt_compat_r. rewrite Ropp_mult_distr_l. 
          apply Rmult_lt_gt_compat_neg_l; lra. rewrite Rplus_comm.
          assert ((1 - ξ) * x3 < x1 - ξ * x1).
          { replace (x1 - ξ * x1) with ((1 - ξ) * x1). 
            apply Rmult_lt_compat_l; lra. lra. } lra. }
         destruct H6 as [x2[H6 H7]]. applyClassifier1 H7.
         assert (x2 ∈ \(a, b\)).
         { apply Classifier1. applyClassifier1 H2. applyClassifier1 H3. lra. } 
         apply (H x3 x2 x1) in H2; auto. rewrite <- H6. 
         assert (ξ = (x2 - x3)/(x1 - x3)). 
         { apply (Rmult_eq_reg_r (x1 - x3)); [ | lra]. unfold Rdiv. 
           rewrite Rmult_assoc. rewrite Rinv_l. lra. lra. }
         apply (Rmult_le_compat_r (x2 - x3)) in H2; [ | lra]. unfold Rdiv in H2.
         rewrite Rmult_assoc in H2. rewrite Rinv_l in H2; [ | lra].
         rewrite Rmult_1_r in H2. rewrite Rmult_comm in H2.
         rewrite <- Rmult_assoc in H2. apply (Rmult_le_compat_r (x1 - x2)) in H2;
         [ | lra]. rewrite Rmult_assoc in H2. rewrite Rinv_l in H2; [ | lra]. 
         rewrite Rmult_1_r in H2. unfold Rminus. rewrite Rmult_plus_distr_r. 
         rewrite <- Rplus_comm. rewrite H9. unfold Rdiv. rewrite Rmult_assoc.
         apply (Rmult_le_reg_r (x1 - x3)). lra. rewrite Rmult_plus_distr_r.  
         replace ((x2 - x3)*(/(x1 - x3)*f[x1])*(x1 - x3)) with ((x2 - x3)*f[x1]).
         rewrite Rmult_plus_distr_r.
         replace (-((x2-x3)*/(x1-x3))*f[x3]*(x1-x3)) with (-(x2-x3)*f[x3]). lra.
         symmetry. rewrite <- Rmult_comm. rewrite <- Rmult_assoc.
         replace ((x1 - x3) * -((x2 - x3) * /(x1 - x3))) with (-(x2 - x3)). lra. 
         rewrite Ropp_mult_distr_l. rewrite <- Rmult_assoc.  
         apply (Rmult_eq_reg_r (x1 - x3)); [ | lra].
         rewrite Rmult_assoc. rewrite Rinv_l; lra. rewrite Rmult_assoc. 
         replace (/(x1 - x3) * f[x1] * (x1 - x3)) with (f[x1]). lra. 
         rewrite Rmult_comm. rewrite <- Rmult_assoc. rewrite Rinv_r_simpl_r; lra.
Qed.


(* 定理6.14  1º -> 2º *)
Theorem Theorem6_14a: ∀ f (a b : R), (∀x : R, x ∈ \(a, b\) -> Derivable f x )
  -> Convex_Function f \(a, b\) -> DIncreaseFun (dN f 1) \(a, b\).
Proof.
  intros. pose proof H0 as H0'. red in H0. destruct H0 as [H0[H1 H2]]. red. 
  repeat split. apply dN_Fact1; auto.
  - simpl. intros z H3. apply Classifier1. apply H in H3. red in H3. 
    destruct H3 as [y0']. exists y0'. apply Classifier2; auto.
  - intros. apply H in H3 as H3'. apply H in H4 as H4'. destruct H3' as [y1' H3'].
    destruct H4' as [y2' H4']. 
    assert(I0 : (dN f 1)[x1] = y1').
    { apply f_x_T. apply dN_Fact1; auto. apply Classifier2; auto. } 
    assert(I1 : (dN f 1)[x2] = y2').
    { apply f_x_T. apply dN_Fact1; auto. apply Classifier2; auto. } 
    rewrite I0. rewrite I1. red in H3'. destruct H3' as [L1[L2 L3]]. 
    red in L3. destruct L3 as [L3[δ1'[L4[L5 L6]]]]. red in H4'. 
    destruct H4' as [K1[K2 K3]]. red in K3. destruct K3 as [K3[δ2'[K4[K5 K6]]]].
    assert (H6: ∃ A, A = (f[x2] - f[x1])/(x2 - x1)).
    exists ((f[x2] - f[x1])/(x2 - x1)); auto. destruct H6 as [A].
    assert (H7: Function f /\ \(a, b\) ⊂ dom[f]). split; auto.
    apply Lemma6_14 in H7. destruct H7. clear H8. 
    assert (I2 : ∃ δ', δ' > 0 /\ (∀ x, x ∈ \(x1 - δ', x1\) 
      -> (f[x1] - f[x])/(x1 - x) <= (f[x2] - f[x1])/(x2 - x1))).
    { exists (x1 - a). applyClassifier1 H3. split. lra. intros. applyClassifier1 H8.
      apply (H7 H0' x x1 x2); auto. apply Classifier1; lra. apply Classifier1; auto. lra. }
    assert(I4 : ∀ x, \{\ λ x y, y = (f[x] - f[x1])/(x - x1) \}\ [x] 
      = (f[x] - f[x1])/(x - x1)). { intros. rewrite FunValue; auto. }
    assert(I4' : ∀ x, \{\ λ x y,y = (f[x] - f[x2])/(x - x2) \}\ [x] 
      = (f[x] - f[x2])/(x - x2)). { intros. rewrite FunValue; auto. }
    assert(y1' <= (f[x2] - f[x1])/(x2 - x1)).
    { destruct I2 as [δ'[I3 I2]]. rewrite <- H6. rewrite <- H6 in I2. 
      assert (H9 : ∀ ε, ε > 0 -> y1' < A + ε).
      { intros. apply L6 in H8. destruct H8 as [δ1[[H8 H9]H10]].
        pose proof (Examp1 δ1 δ'). apply H11 in H8; auto. clear H11. 
        destruct H8 as [δ[H8[H12 H11]]].
        assert (∃ x, x ∈ \(x1 - δ', x1\) /\ 0 < ∣(x - x1)∣ < δ1).
        { exists (x1 - δ/2). split. apply Classifier1. lra.  split. 
          apply Abs_not_eq_0; lra. apply Abs_R; lra. }
        destruct H13 as [x[H13 H14]]. pose proof H14 as H14'. apply H10 in H14.
        apply I2 in H13. rewrite I4 in H14. apply Abs_R in H14. 
        replace ((f[x1] - f[x])/(x1 - x)) with ((f[x] - f[x1])/(x - x1)) in H13. 
        lra. field. destruct H14'. apply Abs_not_eq_0 in H15. lra. }
       apply Rnot_gt_le. intro. 
       assert (H12 : (y1' - A)/2 > 0). lra. apply H9 in H12 as H13. lra. }
    assert (I5 : ∃ δ', δ' > 0 /\ (∀ x, x ∈ \(x2, x2 + δ'\) 
      -> (f[x2] - f[x1])/(x2 - x1) <= (f[x] - f[x2])/(x - x2))).
    { exists (b - x2). applyClassifier1 H4. split. lra. intros. applyClassifier1 H9.
      apply (H7 H0' x1 x2 x); auto. apply Classifier1; lra. apply Classifier1; auto. 
      lra. } 
    assert (y2' >= (f[x2] - f[x1])/(x2 - x1)).
    { destruct I5 as [δ'[I3 I6]]. rewrite <- H6. rewrite <- H6 in I6. 
      assert (H9 : ∀ ε, ε > 0 -> y2' > A - ε).
      { intros. apply K6 in H9. destruct H9 as [δ2[[H9 H10]H11]].
        pose proof (Examp1 δ2 δ'). apply H12 in H9; auto. clear H12. 
        destruct H9 as [δ[H9[H12 H13]]].
        assert (∃ x, x ∈ \(x2, x2 + δ'\) /\ 0 < ∣(x - x2)∣ < δ2).
        { exists (x2 + δ/2). split. apply Classifier1. lra. split. 
          apply Abs_not_eq_0; lra. apply Abs_R; lra. }
        destruct H14 as [x[H15 H14]]. apply H11 in H14. apply I6 in H15. 
        rewrite I4' in H14. apply Abs_R in H14. lra. } 
      apply Rnot_gt_ge. intro. assert (H12 : (A - y2')/2 > 0). lra. 
      apply H9 in H12 as H13. lra. }
    lra.
Qed.

(* 定理6.14  2º -> 3º *)
Theorem Theorem6_14b : ∀ f (a b : R), (∀ x, x ∈ \(a, b\) -> Derivable f x)
  -> DIncreaseFun (dN f 1) \(a, b\)
  -> (∀ x1 x2, x1 ∈ \(a, b\) -> x2 ∈ \(a, b\) -> f[x2] >= f[x1]+f’[x1]*(x2-x1)).
Proof.
  intros. red in H0. destruct H0 as [H0[H3 H4]].
  assert (H5': ∀ x, x ∈ \(a, b\) -> (dN f 1)[x] = f’[x]).
  { intros. apply f_x_T; auto. apply Classifier2. apply H in H5. red in H5. 
    destruct H5 as [y']. apply Corollary_DerivativeValue_a in H5 as H6'. 
    rewrite H6'; auto. }
  destruct (classic (x1 = x2)).
  - rewrite H5. lra.
  - apply Rdichotomy in H5. destruct H5.
    + assert (L0 : ContinuousClose f x1 x2).
      { red. split. applyClassifier1 H1; applyClassifier1 H2. red. intros. 
        apply Theorem5_1. apply H. apply Classifier1; lra. split. apply H in H1; 
        apply Theorem5_1 in H1; apply Theorem4_1 in H1; tauto. apply H in H2; 
        apply Theorem5_1 in H2; apply Theorem4_1 in H2; tauto. }
      assert (L1 : (∀ x, x1 < x < x2 -> Derivable f x)).
      { intros. apply H. applyClassifier1 H1; applyClassifier1 H2. apply Classifier1; lra. }
      pose proof (Theorem6_2 f x1 x2 H5 L0 L1). destruct H6 as [ξ[H7 H8]]. 
      apply Corollary_DerivativeValue_a in H8. cut (ξ ∈ \(a, b\)); intros. 
      apply (H4 x1 ξ) in H1 as H1'; auto. rewrite H5' in H1'; auto.   
      rewrite H5' in H1'; auto.
      assert (f’[ξ] * (x2 - x1) = f[x2] - f[x1]).
      { rewrite H8. unfold Rdiv. rewrite Rmult_assoc, (Rmult_comm (/(x2 - x1))),
        <- Rmult_assoc, Rinv_r_simpl_l; auto. lra. }
      assert (f’[x1] * (x2 - x1) <= f’[ξ] * (x2 - x1)).
      { apply Rmult_le_compat_r; lra. }
      lra. lra. apply Classifier1; applyClassifier1 H1; applyClassifier1 H2; lra.
    + assert (L0 : ContinuousClose f x2 x1).
      { red. split. applyClassifier1 H1; applyClassifier1 H2. red. intros. 
        apply Theorem5_1. apply H. apply Classifier1; lra. split. apply H in H2; 
        apply Theorem5_1 in H2; apply Theorem4_1 in H2; tauto. apply H in H1; 
        apply Theorem5_1 in H1; apply Theorem4_1 in H1; tauto. }
      assert (L1 : (∀ x, x2 < x < x1 -> Derivable f x)).
      { intros. apply H. applyClassifier1 H1; applyClassifier1 H2. apply Classifier1; lra. }
      pose proof (Theorem6_2 f x2 x1 H5 L0 L1). destruct H6 as [ξ[H7 H8]]. 
      apply Corollary_DerivativeValue_a in H8. cut (ξ ∈ \(a, b\)); intros. 
      apply (H4 ξ x1) in H1 as H1'; auto; [ | lra]. rewrite H5' in H1'; auto.
      rewrite H5' in H1'; auto.
      assert (f’[ξ] * (x1 - x2) = f[x1] - f[x2]).
      { rewrite H8. unfold Rdiv. rewrite Rmult_assoc, (Rmult_comm (/(x1 - x2))),
        <- Rmult_assoc, Rinv_r_simpl_l; auto. lra. }
      assert ((x2 - x1)* f’[x1] <= ((x2 - x1) * f’[ξ])).
      { apply Rmult_le_compat_neg_l; lra. }
      lra. apply Classifier1; applyClassifier1 H1; applyClassifier1 H2; lra.
Qed.

(* 定理6.14  3º -> 1º *)
Theorem Theorem6_14c : ∀ f (a b : R), Function f
  -> (∀ x : R, x ∈ \(a, b\) -> Derivable f x)
  -> (∀ x1 x2, x1 ∈ \(a, b\) -> x2 ∈ \(a, b\) -> f[x2] >= f[x1]+f’[x1]*(x2-x1))
  -> (Convex_Function f \(a, b\)).
Proof.
  intros. assert (\(a, b\) ⊂ dom[f]).
  { red; intros. apply H0 in H2 as [y[H2[[x[]]_]]]. apply H4,Classifier1.
    rewrite Abs_ge; lra. } destruct (Rlt_or_le a b).
  - assert (∃ x, x ∈ \(a, b\)). { exists((a + b)/2). apply Classifier1. lra. }
    destruct H4 as [x H4]. apply H0 in H4. destruct H4 as [y']. split. tauto. 
    split; auto. intros. assert (∃ x3, x3 = ξ * x1 + (1 - ξ) * x2).
    { exists (ξ * x1 + (1 - ξ) * x2); auto. } destruct H8 as [x3 H8]. 
    assert ((x1 - x3) = (1 - ξ) * (x1 - x2)). { rewrite H8. lra. }
    assert ((x2 - x3) = ξ * (x2 - x1)). { rewrite H8. lra.  } 
    assert (x3 ∈ \(a, b\)).
    { rewrite H8. apply Classifier1. applyClassifier1 H5. applyClassifier1 H6;
      applyClassifier1 H7. destruct H5. destruct H7. destruct H6.
      assert (0 < (1 - ξ) < 1). lra. assert (ξ * x1 > ξ * a).
      apply Rmult_gt_compat_l; lra. assert ((1 - ξ) * x2 > (1 - ξ) * a).
      apply Rmult_gt_compat_l; lra. split. lra. assert (ξ * x1 < ξ * b). 
      apply Rmult_lt_compat_l; lra. assert((1 - ξ) * x2 < (1 - ξ) * b).
      apply Rmult_gt_compat_l; lra. lra. }
    apply (H1 x3 x1) in H11 as H11'; auto. rewrite H9 in H11'. applyClassifier1 H7.
    apply (H1 x3 x2) in H11 as H11''; auto. rewrite H10 in H11''. rewrite <-H8.
    apply (Rmult_ge_compat_l ξ f[x1] _) in H11'; [ | lra].
    apply (Rmult_ge_compat_l (1 - ξ)) in H11''; [ | lra]. lra.
  - assert (\(a, b\) = Empty R).
    { apply AxiomI; split; intros. applyClassifier1 H4. exfalso. lra.
      applyClassifier1 H4. elim H4; auto. } rewrite H4. split; auto. unfold Contain.
    split; intros; applyClassifier1 H5; elim H5; auto.
Qed.

Theorem Theorem6_15 : ∀ f (a b : R), a < b -> \( a, b \) ⊂ dom[ f]
  -> (∀ x : R, x ∈ \(a, b\) -> Derivable f x )
  -> (∀ x : R, x ∈ \(a, b\) -> Derivable (dN f 1) x)
  -> (Convex_Function f \(a, b\) <-> (∀ x, x ∈ \(a, b\) -> (dN f 1)’[x] >= 0)).
Proof.
  intros. assert (Function f).
  { assert ((a + b)/2 ∈ \(a, b\)). { apply Classifier1; lra. }
    apply H1 in H3 as [y[]]; auto. } split; intros.
  - apply -> (Theorem6_3a (dN f 1) a b); auto. apply Theorem6_14a; auto. split.
    applyClassifier1 H5. lra. split. intros z H6; apply Classifier1. apply H1 in H6.
    destruct H6 as [z']. exists (z'). apply Classifier2; auto. apply H2.
  - apply Theorem6_14c; auto. apply Theorem6_14b; auto.
    assert(DIncreaseFun (dN f 1) \(a, b\) 
      <-> (∀ x, x ∈ \(a, b\) -> (dN f 1)’[x] >= 0)).
    { apply Theorem6_3a. repeat split; auto. intros z H5; apply Classifier1.
      apply H1 in H5. red in H5. destruct H5 as [z']. exists (z'). 
      apply Classifier2; auto. } destruct H5. apply H6; auto.
Qed.

(* 定义 拐点 *)
Definition InflectionPoint f x0 := Continuous f x0 /\ (∃ δ, 0 < δ
  /\ ((Convex_Function f U-º(x0; δ) /\ Concave_Function f U+º(x0; δ))
    \/ (Concave_Function f U-º(x0; δ) /\ Convex_Function f U+º(x0; δ)))).

Lemma Lemma6_16a: ∀ f a b, (∀ x, x ∈ \(a, b\) -> Derivable f x)
  -> Concave_Function f \(a, b\) -> DDecreaseFun (dN f 1) \(a, b\).
Proof.
  intros. assert (Convex_Function (\{\ λ u v, v = 0 \}\ \- f) \(a, b\)).
  { split. apply Corollary_sub_fun_a.
    assert (dom[ \{\ λ u v, v = 0 \}\ \- f] = dom[f]).
    { rewrite Corollary_sub_fun_c. apply AxiomI; split; intros.
      applyClassifier1 H1. tauto. apply Classifier1. split; auto. apply Classifier1.
      exists 0. apply Classifier2; auto. }
    rewrite H1. split. destruct H0 as [_[]]; auto. intros. destruct H0 as [H0[]].
    assert (ξ * x1 + (1 - ξ) * x2 ∈ dom[f]).
    { assert (∀ x3 x4, x3 ∈ \(a, b\) -> x4 ∈ \(a, b\) -> x3 < x4
        -> x3 < ξ * x3 + (1 - ξ) * x4 < x4).
      { intros. applyClassifier1 H4. destruct H4.
        assert (ξ * x3 < ξ * x4). { apply Rmult_lt_compat_l; auto. }
        assert ((1-ξ) * x3 < (1-ξ) * x4). { apply Rmult_lt_compat_l; lra. }
        split; lra. } apply H5,Classifier1. pose proof H2. pose proof H3.
        applyClassifier1 H2. applyClassifier1 H3. destruct H2,H3.
      destruct (Rtotal_order x1 x2) as [H12|[]]; try (apply H7 in H12 as [];
      auto; try lra). rewrite H12. lra. } apply (H6 x1 x2) in H4; auto.
    repeat rewrite Corollary_sub_fun_b; repeat rewrite FunValue; auto;
    try (apply Classifier1; exists 0; apply Classifier2; auto). lra. }
  apply Theorem6_14a in H1. destruct H1 as [H1[]]. split. apply dN_Fact1.
  destruct H0; auto. split. red; intros. apply Classifier1. exists (f’[z]).
  apply Classifier2. apply H in H4 as []. pose proof H4.
  apply Corollary_DerivativeValue_a in H4. rewrite H4; auto. intros.
  apply (H3 x1 x2) in H6; auto. rewrite <-dN_Fact11,<-dN_Fact11,dN_Fact14,
  FunValue,FunValue in H6; auto; try lra; try (rewrite dN_Fact14; auto;
  apply Classifier1; exists 0; apply Classifier2; auto); apply Classifier1;
  [exists (f’[x2])|exists (f’[x1])]; apply Classifier2;
  [apply H in H5 as []; pose proof H5|apply H in H4 as []; pose proof H4];
  apply Corollary_DerivativeValue_a in H7; subst; auto.
  intros. apply H in H2 as []. exists (\{\ λ u v, v = 0 \}\’[x] - f’[x]).
  apply Theorem5_4b. exists 0. apply EleFun_Fact14. exists x0; auto.
Qed.

Lemma Lemma6_16b : ∀ f I1 I2, I1 ⊂ I2 -> Convex_Function f I2
  -> Convex_Function f I1.
Proof.
  intros. destruct H0 as [H0[]]. repeat split; auto. red; intros; auto.
Qed.

Lemma Lemma6_16c : ∀ f I1 I2, I1 ⊂ I2 -> Concave_Function f I2
  -> Concave_Function f I1.
Proof.
  intros. destruct H0 as [H0[]]. repeat split; auto. red; intros; auto.
Qed.

Theorem Theorem6_16 : ∀ f x0, Derivable (dN f 1) x0
  -> InflectionPoint f x0 -> (dN f 2)[x0] = 0.
Proof.
  intros. pose proof H. apply Theorem5_1 in H1 as [H1[H2[δ[H3[]]]]].
  destruct H0 as [H0[δ1[]]].
  assert (∀ x, x ∈ \(x0 - δ, x0\) \/ x ∈ \(x0, x0 + δ\) -> Derivable f x).
  { intros. assert (x ∈ Uº(x0; δ)).
    { apply Classifier1; auto. split. apply Abs_not_eq_0. destruct H8;
      applyClassifier1 H8; lra. apply Abs_R. destruct H8; applyClassifier1 H8; lra. }
    apply H4,x_fx_T in H9; auto. applyClassifier2 H9. red; eauto. }
  destruct H7 as [[]|[]]; destruct (Examp1 δ δ1) as [δ2[H10[]]]; auto.
  - apply (Lemma6_16b f U-º(x0; δ2)) in H7;
    [apply (Lemma6_16c f U+º(x0; δ2)) in H9| ];
    try (red; intros; applyClassifier1 H13; apply Classifier1; lra).
    apply Theorem6_14a in H7; [apply Lemma6_16a in H9| ]; intros; try apply H8;
    [ |right|left]; try (applyClassifier1 H13; apply Classifier1; lra).
    assert (Derivative (dN f 1) x0 0).
    { apply Theorem5_3; auto. left. red. split; auto. exists δ2. split; auto.
      split. red; intros. destruct (classic (z = x0)). rewrite H14; auto.
      apply H4. applyClassifier1 H13. apply Classifier1. split. apply Abs_not_eq_0; lra.
      lra. intros. destruct (classic (x = x0)). rewrite H14. lra.
      destruct H7 as [_[_]], H9 as [_[_]].
      destruct (Rle_or_lt (dN f 1)[x] (dN f 1)[x0]); auto.
      assert ((dN f 1)[x] - (dN f 1)[x0] > 0) by lra. apply H5 in H16 as [δ3[]].
      destruct (Examp1 δ3 (∣(x-x0)∣)) as [δ4[H18[]]]; auto. lra.
      apply Abs_not_eq_0. lra. assert (0 < ∣((δ4 + x0) - x0)∣ < δ3).
      { split. apply Abs_not_eq_0. lra. apply Abs_R. lra. }
      assert (0 < ∣((x0 - δ4) - x0)∣ < δ3).
      { split. apply Abs_not_eq_0. lra. apply Abs_R. lra. } apply H17 in H21,H22.
      destruct (Rtotal_order x x0) as [H23|[]]; try contradiction.
      assert ((dN f 1)[x0 - δ4] >= (dN f 1)[x]).
      { applyClassifier1 H13; rewrite Abs_eq_neg,Ropp_minus_distr,Abs_ge in H13,H20;
        try lra. apply Rle_ge,H7; try (apply Classifier1; lra). }
      rewrite Abs_ge in H22; try lra.
      assert ((dN f 1)[δ4 + x0] >= (dN f 1)[x]).
      { applyClassifier1 H13; rewrite Abs_ge in H13,H20; try lra.
        apply H9; try (apply Classifier1; lra). }
      rewrite Abs_ge in H21; try lra. }
    rewrite dN_Fact3. apply Corollary_DerivativeValue_a in H13; auto.
  - apply (Lemma6_16c f U-º(x0; δ2)) in H7;
    [apply (Lemma6_16b f U+º(x0; δ2)) in H9| ];
    try (red; intros; applyClassifier1 H13; apply Classifier1; lra).
    apply Lemma6_16a in H7; [apply Theorem6_14a in H9| ]; intros; try apply H8;
    [ |right|left]; try (applyClassifier1 H13; apply Classifier1; lra).
    assert (Derivative (dN f 1) x0 0).
    { apply Theorem5_3; auto. right. red. split; auto. exists δ2. split; auto.
      split. red; intros. destruct (classic (z = x0)). rewrite H14; auto.
      apply H4. applyClassifier1 H13. apply Classifier1. split. apply Abs_not_eq_0; lra.
      lra. intros. destruct (classic (x = x0)). rewrite H14. lra.
      destruct H7 as [_[_]], H9 as [_[_]].
      destruct (Rle_or_lt (dN f 1)[x0] (dN f 1)[x]); auto.
      assert ((dN f 1)[x0] - (dN f 1)[x] > 0) by lra. apply H5 in H16 as [δ3[]].
      destruct (Examp1 δ3 (∣(x-x0)∣)) as [δ4[H18[]]]; auto. lra.
      apply Abs_not_eq_0. lra. assert (0 < ∣((δ4 + x0) - x0)∣ < δ3).
      { split. apply Abs_not_eq_0. lra. apply Abs_R. lra. }
      assert (0 < ∣((x0 - δ4) - x0)∣ < δ3).
      { split. apply Abs_not_eq_0. lra. apply Abs_R. lra. } apply H17 in H21,H22.
      destruct (Rtotal_order x x0) as [H23|[]]; try contradiction.
      assert ((dN f 1)[x0 - δ4] <= (dN f 1)[x]).
      { applyClassifier1 H13; rewrite Abs_eq_neg,Ropp_minus_distr,Abs_ge in H13,H20;
        try lra. apply Rge_le,H7; try (apply Classifier1; lra). }
      rewrite Abs_eq_neg,Abs_ge,Ropp_minus_distr in H22; lra.
      assert ((dN f 1)[δ4 + x0] <= (dN f 1)[x]).
      { applyClassifier1 H13; rewrite Abs_ge in H13,H20; try lra.
        apply H9; try (apply Classifier1; lra). }
      rewrite Abs_eq_neg,Abs_ge,Ropp_minus_distr in H21; lra. }
    rewrite dN_Fact3. apply Corollary_DerivativeValue_a in H13; auto.
Qed.

Lemma Lemma6_17 : ∀ f a b, a < b -> \(a, b\) ⊂ dom[ f]
  -> (∀ x, x ∈ \(a, b\) -> Derivable f x )
  -> (∀ x, x ∈ \(a, b\) -> Derivable (dN f 1) x)
  -> ((∀ x, x ∈ \(a, b\) -> (dN f 1)’[x] <= 0) -> Concave_Function f \(a, b\)).
Proof.
  intros. assert (Function f).
  { assert ((a + b)/2 ∈ \(a, b\)). { apply Classifier1; lra. }
    apply H1 in H4 as [y[]]; auto. }
  assert (dN (\{\ λ _ v, v = 0 \}\ \- f) 1
    = (dN (\{\ λ _ v, v = 0 \}\) 1) \- (dN f 1)).
  { rewrite <-dN_Fact12. rewrite dN_Fact14; auto. red; intros. applyClassifier1 H5.
    destruct H5 as [y]. applyClassifier2 H5. apply Classifier1. split.
    apply Classifier1. exists 0. rewrite dN_Fact14. apply Classifier2; auto. lia.
    apply Classifier1. exists (-y). apply Classifier2.
    assert (Derivative (\{\ λ u v, v = 0 \}\ \- (\{\ λ u v, v = 0 \}\ \- f)) z
      (\{\ λ u v, v = 0 \}\’[z] - (\{\ λ u v, v = 0 \}\ \- f)’[z])).
    { apply Theorem5_4b. exists 0. apply EleFun_Fact14. red; eauto. }
    assert (\{\ λ u v, v = 0 \}\ \- (\{\ λ u v, v = 0 \}\ \- f) = f).
    { apply AxiomI; split; intros; destruct z0. applyClassifier2 H7.
      destruct H7 as [H7[]]. rewrite Corollary_sub_fun_c in H8.
      applyClassifier1 H8. destruct H8. rewrite Corollary_sub_fun_b in H9; auto.
      rewrite FunValue in H9. replace (0 - (0 - f[x])) with f[x] in H9; [ |lra].
      rewrite H9. apply x_fx_T; auto. apply Classifier2.
      assert (x ∈ dom[\{\ λ u v,v = 0 \}\])
      by (apply Classifier1; exists 0; apply Classifier2; auto). split; auto.
      split. rewrite Corollary_sub_fun_c. apply Classifier1. split; auto.
      apply Classifier1; eauto. rewrite Corollary_sub_fun_b,FunValue; auto.
      replace (0 - (0 - f[x])) with f[x]; [ |lra]. symmetry. apply f_x_T; auto.
      apply Classifier1; eauto. } rewrite H7 in H6.
    assert (Derivative (\{\ λ u v, v = 0 \}\) z 0) by (apply EleFun_Fact14).
    apply Corollary_DerivativeValue_a in H5,H8.
    rewrite H5,H8,Rminus_0_l in H6; auto. }
  assert (Convex_Function (\{\ λ u v, v = 0 \}\ \- f) \(a, b\)).
  { apply Theorem6_15; intros. auto. rewrite Corollary_sub_fun_c. red; intros.
    apply Classifier1. split; auto. apply Classifier1. exists 0. apply Classifier2; auto.
    exists (\{\ λ u v, v = 0 \}\’[x] - f’[x]). apply Theorem5_4b; auto.
    exists 0. apply EleFun_Fact14. rewrite H5,dN_Fact14; [ |lia].
    exists (\{\ λ u v, v = 0 \}\’[x] - (dN f 1)’[x]). apply Theorem5_4b; auto.
    exists 0. apply EleFun_Fact14. rewrite H5,dN_Fact14; [ |lia].
    assert (Derivative (\{\ λ u v, v = 0 \}\ \- (dN f 1)) x
      (\{\ λ u v, v = 0 \}\’[x] - (dN f 1)’[x])).
    { apply Theorem5_4b; auto. exists 0. apply EleFun_Fact14. }
    apply Corollary_DerivativeValue_a in H7. rewrite H7.
    assert (Derivative (\{\ λ u v, v = 0 \}\) x 0) by (apply EleFun_Fact14).
    apply Corollary_DerivativeValue_a in H8. rewrite H8. apply H3 in H6. lra. }
  destruct H6 as [H6[]]. split; auto. rewrite Corollary_sub_fun_c in H7. split.
  red; intros. apply H7 in H9. applyClassifier1 H9; tauto. intros. pose proof H11.
  apply (H8 x1 x2) in H12; auto. rewrite Corollary_sub_fun_b,Corollary_sub_fun_b,
  Corollary_sub_fun_b,FunValue,FunValue,FunValue in H12; auto; [ | | | |apply H0];
  try (apply Classifier1; exists 0; apply Classifier2; auto). lra.
  assert (∀ x3 x4, x3 ∈ \(a, b\) -> x4 ∈ \(a, b\) -> x3 < x4
    -> x3 < ξ * x3 + (1 - ξ) * x4 < x4).
  { intros. applyClassifier1 H11. destruct H11.
    assert (ξ * x3 < ξ * x4). { apply Rmult_lt_compat_l; auto. }
    assert ((1-ξ) * x3 < (1-ξ) * x4). { apply Rmult_lt_compat_l; lra. }
    split; lra. } apply Classifier1. pose proof H9. pose proof H10.
  applyClassifier1 H14. applyClassifier1 H15. destruct H14,H15.
  destruct (Rtotal_order x1 x2) as [H18|[]]; try (apply H13 in H18 as []; auto;
  try lra). rewrite H18. lra.
Qed.

Theorem Theorem6_17 : ∀ f x0, Derivable f x0
  -> (∃ δ, 0 < δ /\ (∀ x, x ∈ Uº(x0; δ) -> Derivable (dN f 1) x)
    /\ (((∀ x, x ∈ U-º(x0; δ) -> (dN f 2)[x] <= 0)
        /\ (∀ x, x ∈ U+º(x0; δ) -> 0 <= (dN f 2)[x]))
      \/ ((∀ x, x ∈ U-º(x0; δ) -> 0 <= (dN f 2)[x])
        /\ (∀ x, x ∈ U+º(x0; δ) -> (dN f 2)[x] <= 0))))
  -> InflectionPoint f x0.
Proof.
  intros. split. apply Theorem5_1; auto. destruct H0 as [δ[]].
  exists δ. split; auto. destruct H1.
  assert (∀ x, x ∈ Uº(x0; δ) -> x ∈ dom[f]).
  { intros. apply H1 in H3 as [y[H3[[x1[]]_]]].
    apply (dN_Fact2 f 1),H5,Classifier1. rewrite Abs_ge; lra. }
  assert (U-º(x0; δ) ⊂ Uº(x0; δ) /\ U+º(x0; δ) ⊂ Uº(x0; δ)) as [].
  { split; red; intros; applyClassifier1 H4; destruct H4; apply Classifier1;
    [rewrite Abs_eq_neg,Ropp_minus_distr| ]; rewrite Abs_ge; lra. }
  assert (∀ x, x ∈ Uº(x0; δ) -> Derivable f x).
  { intros. apply H1 in H6 as [y[H6[[x1[]]_]]].
    assert (x ∈ U(x; x1)) by (apply Classifier1; rewrite Abs_ge; lra).
    apply H8,x_fx_T in H9; auto. applyClassifier2 H9. red; eauto. }
  destruct H2 as [[]|[]].
  - right. split. apply Lemma6_17; intros; auto. lra. red; intros; auto.
    rewrite <-dN_Fact3; auto. apply Theorem6_15; intros; auto. lra.
    red; intros; auto. rewrite <-dN_Fact3. apply Rle_ge; auto.
  - left. split. apply Theorem6_15; intros; auto. lra. red; intros; auto.
    rewrite <-dN_Fact3. apply Rle_ge; auto. apply Lemma6_17; intros; auto. lra.
    red; intros; auto. rewrite <-dN_Fact3; auto.
Qed.






