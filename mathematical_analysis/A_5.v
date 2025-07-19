(** A_5 *)
(* 导数和微分 *)

(* 读入文件 *)
Require Export A_4.


(* 5.1 导数的概念 *)

(* 定义：导数 *)
Definition Derivative f x0 y0' := Function f
  /\ (∃ δ', δ' > 0 /\ U(x0; δ') ⊂ dom[f])
  /\ (limit \{\ λ x y, y = (f[x] - f[x0])/(x - x0) \}\ x0 y0').

Definition Derivative' f x0 y0' := Function f
  /\ (∃ δ', δ' > 0 /\ U(x0; δ') ⊂ dom[f])
  /\ (limit \{\ λ δx y, y = (f[x0 + δx] - f[x0])/δx \}\ 0 y0').

(* 两个导数定义等价 *) 
Corollary EquaDerivative : ∀ f x0 y0', Derivative f x0 y0' <-> Derivative' f x0 y0'.
Proof.
  intros. split; intros.
  - destruct H as [H[]]. split; auto. split; auto. 
    destruct H1 as [H1[δ[H8[H9 H10]]]]. split; auto.
    + unfold Function. intros. applyClassifier2 H2. applyClassifier2 H3. rewrite H2; 
      auto.
    + exists δ. split; auto. split. unfold Contain. intros. apply Classifier1.
      exists ((f[x0 + z]-f[x0])/z). apply Classifier2; auto. intros. apply H10 in H2.
      destruct H2 as [δ0]. exists δ0. destruct H2. split; auto. intros. 
      replace (x - 0) with x in H4. assert (0 < ∣(x0 + x - x0)∣ < δ0).
      { assert ((x0 + x - x0) = x). rewrite Rplus_comm. lra. rewrite H5. auto. }
      pose proof (H3 (x0 + x)). apply H6 in H5.
      assert (Function \{\ λ h0 y, y = (f[x0 + h0] - f[x0])/h0 \}\).
      { unfold Function. intros. applyClassifier2 H7. applyClassifier2 H11. rewrite H11.
        auto. }
      assert (\{\ λ h0 y, y = (f[x0 + h0]-f[x0])/h0 \}\ [x] = (f[x0 + x]-f[x0])/x).
      { apply f_x_T; auto. apply Classifier2; simpl; auto. } rewrite H11. 
      assert (\{\ λ x y, y = (f[x] - f[x0])/(x - x0) \}\ [x0 + x] 
        = (f[x0 + x] - f[x0])/(x0 + x - x0)).
      { apply f_x_T; auto. apply Classifier2; simpl; auto. } rewrite H12 in H5.
      assert (x0 + x - x0 = x). { lra. } rewrite H13 in H5. auto. lra.
  - destruct H as [H[H1 H2]]. destruct H2.
    assert (Function \{\ λ x y, y = (f[x] - f[x0])/(x - x0) \}\).
    { unfold Function. intros. applyClassifier2 H3. applyClassifier2 H4. rewrite H4. 
      auto. }
    repeat split; auto. destruct H2 as[δ'[H4[H5]]]. exists δ'. split; auto. split.
    + unfold Contain. intros. apply Classifier1. exists ((f[z] - f[x0])/(z - x0)).
      apply Classifier2; auto.
    + intros. apply H2 in H6. destruct H6 as [δ[H6 H7]]. exists δ. split; auto.
      intros. assert (x - x0 = x - x0 - 0). lra. rewrite H9 in H8. apply H7 in H8.
      assert (\{\ λ h y, y = (f[x0 + h] - f[x0])/h \}\ [x - x0] 
        = (f[x0 + x - x0] - f[x0])/(x - x0)). 
      { apply f_x_T; auto. apply Classifier2. 
        replace (x0 + (x - x0)) with (x0 + x - x0). auto. lra. }
      replace (x0 + x - x0) with x in H10. rewrite H10 in H8.
      assert (\{\ λ x1 y, y = (f[x1] - f[x0])/(x1 - x0) \}\ [x] 
        = (f[x] - f[x0])/(x - x0)). { apply f_x_T; auto. apply Classifier2; auto. }
      rewrite H11; auto. lra.
Qed.

(* 在某去心邻域导数(该定义之后没有用过, 并且与导数本身的定义区别不大) *)
(* Definition DerivativeU f x0 y0' δ' :=
  Function f /\ (δ' > 0 /\ Neighbor x0 δ' ⊂ dom[f]) /\
  (limit \{\ λ x y, y = (f[x] - f[x0]) / (x - x0) \}\ x0 y0'). *)
(* 定义：可导 *)
Definition Derivable f x0 := ∃ y0', Derivative f x0 y0'.
Definition Derivable' f x0 := ∃ y0', Derivative' f x0 y0'.

(* 导数唯一性 *)
Corollary DerivativeUnique : ∀ f x0 A B, Derivative f x0 A -> Derivative f x0 B
  -> A = B.
Proof. 
  intros f x0 A B [H0[H1 H2]] [H3[H4 H5]]. eapply Theorem3_2a; eauto. 
Qed.

(* 导数值 *)
Definition DerivativeValue f x := c \{ λ y', Derivative f x y' \}.
Notation "f ’[ x ]" := (DerivativeValue f x)(at level 20).

Corollary Corollary_DerivativeValue_a : ∀ f x y', Derivative f x y' -> f’[x] = y'.
Proof.
  intros f x y' H0. assert (H1 : Derivative f x (f’[x])).
  { assert (I1 : NotEmpty \{ λ y', Derivative f x y' \}).
    { exists y'. apply Classifier1. assumption. }
    apply Axiomc in I1. applyClassifier1 I1. assumption. }
  eapply DerivativeUnique; eauto.
Qed.

Corollary Corollary_DerivativeValue_b : ∀ f x y', Derivative' f x y' -> f’[x] = y'.
Proof.
  intros f x y' H0. rewrite <- EquaDerivative in H0.
  apply Corollary_DerivativeValue_a in H0. apply H0.
Qed.

(* 右导数 *)
Definition Derivative_pos f x0 y0' := Function f
  /\ (∃ δ', δ' > 0 /\ U+(x0; δ') ⊂ dom[f])
  /\ (limit_pos \{\ λ x y, y = (f[x] - f[x0])/(x - x0) \}\ x0 y0').

(* ！！！！！！！！！！！定理3_2处增加了左右极限的唯一性！！！！！！！！！！！！！ *)
(* 右导数唯一性 *)
Corollary DerivativeUnique_pos : ∀ f (x0 A B : R),
  Derivative_pos f x0 A -> Derivative_pos f x0 B -> A = B.
Proof. 
  intros f x0 A B [H0[H1 H2]] [H3[H4 H5]]. eapply Theorem3_2b; eauto. 
Qed.

(* 右导数值 *)
Definition DerivativeValue_pos f x := c \{ λ y', Derivative_pos f x y' \}.
Notation "f ’+[ x ]" := (DerivativeValue_pos f x)(at level 20).

Corollary Corollary_DerivativeValue_pos : ∀ f x y', Derivative_pos f x y'
  -> f ’+[x] = y'.
Proof.
  intros f x y' H0. assert (H1 : Derivative_pos f x (f’+[x])).
  { assert (I1 : NotEmpty \{ λ y', Derivative_pos f x y' \}).
    { exists y'. apply Classifier1. assumption. }
    apply Axiomc in I1. applyClassifier1 I1. assumption. }
  eapply DerivativeUnique_pos; eauto.
Qed.

(* 左导数 *)
Definition Derivative_neg f x0 y0' := Function f
  /\ (∃ δ', δ' > 0 /\ U-(x0; δ') ⊂ dom[f])
  /\ (limit_neg \{\ λ x y, y = (f[x] - f[x0])/(x - x0) \}\ x0 y0').

(* 左导数唯一性 *)
Corollary DerivativeUnique_neg : ∀ f x0 A B, Derivative_neg f x0 A
  -> Derivative_neg f x0 B -> A = B.
Proof. 
  intros f x0 A B [H0[H1 H2]] [H3[H4 H5]]. eapply Theorem3_2c; eauto. 
Qed.

(* 左导数值 *)
Definition DerivativeValue_neg f x := c \{ λ y', Derivative_neg f x y' \}.
Notation "f ’_[ x ]" := (DerivativeValue_neg f x)(at level 20).

Corollary Corollary_DerivativeValue_neg : ∀ f x y', Derivative_neg f x y' 
  -> f’_[x] = y'.
Proof.
  intros f x y' H0. assert (Derivative_neg f x (f ’_[x])).
  { assert (I1 : NotEmpty \{ λ y', Derivative_neg f x y' \}).
    { exists y'. apply Classifier1. assumption. }
    apply Axiomc in I1. applyClassifier1 I1. assumption. }
  eapply DerivativeUnique_neg; eauto.
Qed.

(* 定理5.1 可导一定连续 *)
Theorem Theorem5_1 : ∀ f x0, Derivable f x0 -> Continuous f x0.
Proof.
  intros. destruct H as [y[H[[δ1[]]]]].
  assert (x0 ∈ dom[f]). { apply H1, Classifier1. rewrite Rminus_diag, Abs_ge; lra. }
  split; auto. destruct H2 as [H2[δ2[H5[]]]].
  assert (∀ x, x ∈ Uº(x0; δ1) -> 0 < ∣(x - x0)∣ < δ1).
  { intros. applyClassifier1 H7. destruct H7. auto. }
  split; auto. exists δ1. repeat split; auto. red; intros. apply H1.
  applyClassifier1 H8. apply Classifier1. lra. intros.
  assert (∀ ε', ε' > 0 -> ∃ δ, 0 < δ
    /\ (∀ x, 0 < ∣(x - x0)∣ < δ -> (ε' + ∣y∣) * ∣(x - x0)∣ < ε)).
  { intros. exists (ε/(ε' + ∣y∣)).
    assert (0 < ε' + ∣y∣). { pose proof (Abs_Rge0 y). lra. }
    split. apply Rdiv_lt_0_compat; auto. intros. destruct H11.
    apply Rmult_lt_compat_l with (r := ε' + ∣y∣) in H12; auto.
    assert ((ε' + ∣y∣) * (ε/(ε' + ∣y∣)) = ε). { field; lra. }
    rewrite H13 in H12. auto. }
  pose proof H8. apply H9 in H10 as [x[]]. pose proof H8. 
  apply H6 in H12 as [x1[[]]]. destruct (Examp2 δ1 x x1) as [x2[H15[H16[]]]]; 
  auto. exists x2. split; auto. intros. destruct H19. 
  assert (0 < ∣(x3 - x0)∣ < x). lra. apply H11 in H21. 
  assert (0 < ∣(x3 - x0)∣ < x1). lra. apply H14 in H22. rewrite FunValue in H22.
  pose proof (Abs_abs_minus' ((f[x3] - f[x0])/(x3 - x0)) y).
  assert (∣((f[x3] - f[x0])/(x3 - x0))∣ - ∣y∣ < ε). lra. rewrite Abs_div in H24.
  assert (∣(f[x3] - f[x0])∣/∣(x3 - x0)∣ < ε + ∣y∣). lra.
  apply (Rmult_lt_compat_r (∣(x3 - x0)∣)) in H25; auto.
  unfold Rdiv in H25. rewrite Rmult_comm, (Rmult_comm (∣(f[x3] - f[x0])∣)),
  <- Rmult_assoc, Rinv_r_simpl_r in H25; lra. intro. rewrite H25, Abs_ge in H19; 
  lra.
Qed.

(* 自主增加推论, 定理6.5能用到 *)
(* 推论5.1a 左可导一定左连续 *)
Corollary Corollary5_1a : ∀ f x0, (∃ y, Derivative_neg f x0 y)
  -> ContinuousLeft f x0.
Proof.
  intros. destruct H as [y[H[[δ1[]]]]].
  assert (x0 ∈ dom[f]). { apply H1, Classifier1; split; lra. }
  split; auto. destruct H2 as [H2[δ2[H5[]]]].
  assert (∀ x, x ∈ U-º(x0; δ1) -> 0 < ∣(x - x0)∣ < δ1).
  { intros. applyClassifier1 H7. destruct H7. rewrite Abs_lt; lra. }
  split; auto. exists δ1. repeat split; auto. red; intros. apply H1.
  applyClassifier1 H8. apply Classifier1. lra. intros.
  assert (∀ ε', ε' > 0 -> ∃ δ, 0 < δ
    /\ (∀ x, 0 < ∣(x - x0)∣ < δ -> (ε' + ∣y∣) * ∣(x - x0)∣ < ε)).
  { intros. exists (ε/(ε' + ∣y∣)).
    assert (0 < ε' + ∣y∣). { pose proof (Abs_Rge0 y). lra. }
    split. apply Rdiv_lt_0_compat; auto. intros. destruct H11.
    apply Rmult_lt_compat_l with (r := ε' + ∣y∣) in H12; auto.
    assert ((ε' + ∣y∣) * (ε/(ε' + ∣y∣)) = ε). { field; lra. }
    rewrite H13 in H12. auto. }
  pose proof H8. apply H9 in H10 as [x[]]. pose proof H8. 
  apply H6 in H12 as [x1[[]]]. 
  destruct (Examp2 δ1 x x1) as [x2[H15[H16[]]]]; auto. exists x2. split; auto. 
  intros. destruct H19. assert (0 < ∣(x3 - x0)∣ < x).
  { split. apply Abs_not_eq_0. lra. rewrite Abs_lt; lra. }
  apply H11 in H21. assert (x0 - x1 < x3 < x0). lra. apply H14 in H22. 
  rewrite FunValue in H22. pose proof (Abs_abs_minus' ((f[x3] - f[x0])/(x3 - x0)) y).
  assert (∣((f[x3] - f[x0])/(x3 - x0))∣ - ∣y∣ < ε). lra.
  rewrite Abs_div in H24; [ | lra].
  assert (∣(f[x3] - f[x0])∣/∣(x3 - x0)∣ < ε + ∣y∣). lra.
  assert (0 < ∣(x3 - x0)∣). { apply Abs_not_eq_0; lra. }
  apply (Rmult_lt_compat_r (∣(x3 - x0)∣)) in H25; auto.
  unfold Rdiv in H25. rewrite Rmult_comm, (Rmult_comm (∣(f[x3] - f[x0])∣)),
  <- Rmult_assoc, Rinv_r_simpl_r in H25; lra.
Qed.

(* 推论5.1b 右可导一定右连续 *)
Corollary Corollary5_1b : ∀ f x0, (∃ y, Derivative_pos f x0 y)
  -> ContinuousRight f x0.
Proof.
  intros. destruct H as [y[H[[δ1[]]]]].
  assert (x0 ∈ dom[f]). { apply H1, Classifier1; split; lra. }
  split; auto. destruct H2 as [H2[δ2[H5[]]]].
  assert (∀ x, x ∈ U+º(x0; δ1) -> 0 < ∣(x - x0)∣ < δ1).
  { intros. applyClassifier1 H7. destruct H7. rewrite Abs_gt; lra. }
  split; auto. exists δ1. repeat split; auto. red; intros. apply H1.
  applyClassifier1 H8. apply Classifier1. lra. intros.
  assert (∀ ε', ε' > 0 -> ∃ δ, 0 < δ
    /\ (∀ x, 0 < ∣(x - x0)∣ < δ -> (ε' + ∣y∣) * ∣(x - x0)∣ < ε)).
  { intros. exists (ε/(ε' + ∣y∣)).
    assert (0 < ε' + ∣y∣). { pose proof (Abs_Rge0 y). lra. }
    split. apply Rdiv_lt_0_compat; auto. intros. destruct H11.
    apply Rmult_lt_compat_l with (r := ε' + ∣y∣) in H12; auto.
    assert ((ε' + ∣y∣) * (ε/(ε' + ∣y∣)) = ε). { field; lra. }
    rewrite H13 in H12. auto. }
  pose proof H8. apply H9 in H10 as [x[]]. pose proof H8. 
  apply H6 in H12 as [x1[[]]]. destruct (Examp2 δ1 x x1) as [x2[H15[H16[]]]]; 
  auto. exists x2. split; auto. intros. destruct H19.
  assert (0 < ∣(x3 - x0)∣ < x).
  { split. apply Abs_not_eq_0. lra. rewrite Abs_gt; lra. }
  apply H11 in H21. assert (x0 < x3 < x0 + x1). lra. apply H14 in H22. 
  rewrite FunValue in H22.
  pose proof (Abs_abs_minus' ((f[x3] - f[x0])/(x3 - x0)) y).
  assert (∣((f[x3] - f[x0])/(x3 - x0))∣ - ∣y∣ < ε). lra.
  rewrite Abs_div in H24; [ | lra].
  assert (∣(f[x3] - f[x0])∣/∣(x3 - x0)∣ < ε + ∣y∣). lra.
  assert (0 < ∣(x3 - x0)∣). { apply Abs_not_eq_0; lra. }
  apply (Rmult_lt_compat_r (∣(x3 - x0)∣)) in H25; auto.
  unfold Rdiv in H25. rewrite Rmult_comm, (Rmult_comm (∣(f[x3] - f[x0])∣)),
  <- Rmult_assoc, Rinv_r_simpl_r in H25; lra.
Qed.

(* 定理5.2 可导的充要条件: 左右均可导且导数相同 *)
Theorem Theorem5_2 : ∀ f x0 y, Derivative f x0 y
  <-> (Derivative_neg f x0 y /\ Derivative_pos f x0 y).
Proof.
  split; intros.
  - destruct H as [H[[δ[]]]]. apply Theorem3_1 in H2 as []. split; split; auto; 
    split; auto; exists δ; split; auto; red; intros; apply H1; applyClassifier1 H4; 
    apply Classifier1. destruct H4 as [H4[]]. rewrite Abs_lt; lra.
    rewrite H5, Rminus_diag, Abs_ge; lra. rewrite Abs_ge; lra.
  - destruct H. destruct H as [H[[δ1[]]]], H0 as [_[[δ2[]]]].
    destruct (Examp1 δ1 δ2) as [x[H6[]]]; auto. split; auto. split. exists x. 
    split; auto. red; intros. destruct (classic (z ∈ U-(x0; δ1))); auto. 
    apply H4. apply Classifier1. applyClassifier1 H9. assert (z >= x0).
    { destruct (Rge_or_gt z x0); auto. rewrite Abs_lt in H9. elim H10.
      apply Classifier1. lra. lra. }
    split; auto. rewrite Abs_ge in H9; lra. apply Theorem3_1; auto.
Qed.

(* 导函数 *)
Definition DerivativeFun f := \{\ λ x y, Derivative f x y \}\.
Definition DerivativeFun' f := \{\ λ x y, Derivative' f x y \}\.

Corollary Derivative_is_Fun : ∀ f, Function (DerivativeFun f).
Proof.
  intro f. unfold Function. intros x y z H1 H2. applyClassifier2 H1. 
  applyClassifier2 H2. destruct H1 as [H1[H3 H4]]. destruct H2 as [H2[H5 H6]]. 
  eapply Theorem3_2a; eauto.
Qed.

Corollary Derivative_is_Fun' : ∀ f, Function (DerivativeFun' f).
Proof.
  intro f. unfold Function. intros x y z H1 H2. applyClassifier2 H1. 
  applyClassifier2 H2. destruct H1 as [H[H3 H4]]. destruct H2 as [H0[H5 H6]]. 
  eapply Theorem3_2a; eauto.
Qed.

(* 极值 *)
(* 极大值 *)
Definition LocalMax f x0 := Function f /\ (∃ δ', δ' > 0 /\ U(x0; δ') ⊂ dom[f] 
  /\ (∀ x, x ∈ U(x0; δ') -> f[x] <= f[x0])).

(* 极小值 *)
Definition LocalMin f x0 := Function f /\ (∃ δ', δ' > 0 /\ U(x0; δ') ⊂ dom[f] 
  /\ (∀ x, x ∈ U(x0; δ') -> f[x0] <= f[x])).

(* 极值 *)
Definition Extremum f x0 := LocalMax f x0 \/ LocalMin f x0.

(* 费马定理 *)
Theorem Theorem5_3 : ∀ f x0, Derivable f x0 -> Extremum f x0 -> Derivative f x0 0.
Proof.
  intros f x0 [y0'[H0[[δ'[H2 H3]]H4]]] H5.
  assert (H6 : Function \{\ λ x y, y = (f[x] - f[x0])/(x - x0) \}\).
  { intros x y z I1 I2. applyClassifier2 I1; applyClassifier2 I2. rewrite I2; 
    assumption. }
  assert (H7 : ∀ x, \{\ λ x y, y = (f[x] - f[x0])/(x - x0) \}\ [x]
    = (f[x] - f[x0])/(x - x0)).
  { intro x. apply f_x_T; auto. apply Classifier2. reflexivity. }
  assert (H8 : y0' = 0).
  { apply NNPP. intro I1. apply Rdichotomy in I1. destruct I1 as [I1 | I1].
    - generalize (Theorem3_4b (\{\ λ x y, y =
        (f[x] - f[x0])/(x - x0) \}\) x0 y0' H4 I1). intro I2. 
      assert (I3 : 0 < ((- y0')/2) < - y0'). lra. apply I2 in I3 as I4. 
      destruct I4 as [δ[I4 I5]]. clear I2. destruct H5 as [I6 | I6].
      + destruct I6 as [I6[δ0'[I7[I8 I9]]]].
        assert (I10 : ∃ δ0, 0 < δ0 /\ δ0 < δ0' /\ δ0 < δ).
        { destruct (Rlt_or_le δ0' δ) as [J1 | J1].
          - exists (δ0'/2). repeat split; lra.
          - exists (δ/2). repeat split; lra. } destruct I10 as [δ0[I10[I11 I12]]].
        assert (I13 : x0 - δ0/2 ∈ U(x0; δ0')).
        { apply Classifier1. apply Abs_R. lra. }
        assert (I14 : x0 - δ0/2 ∈ Uº(x0; δ)).
        { apply Classifier1. split. apply Abs_not_eq_0. lra. apply Abs_R. lra. }
        apply I9 in I13. apply I5 in I14. rewrite H7 in I14.
        assert (I15 : (f[x0 - δ0/2] - f[x0])/(x0 - δ0/2 - x0) < 0). lra.
        assert (I16 : x0 - δ0/2 - x0 < 0). lra.
        apply Rmult_lt_gt_compat_neg_l with (r := x0 - δ0/2 - x0) in I15; auto.
        rewrite Rmult_0_r in I15.
        assert (I17 : (x0 - δ0/2 - x0) *((f [x0 - δ0/2] - f [x0])/
          (x0 - δ0/2 - x0)) = f[x0 - δ0/2] - f[x0]). { field. lra. }
        rewrite I17 in I15. lra.
      + destruct I6 as [I6[δ0'[I7[I8 I9]]]].
        assert (I10 : ∃ δ0, 0 < δ0 /\ δ0 < δ0' /\ δ0 < δ).
        { destruct (Rlt_or_le δ0' δ) as [J1 | J1].
          - exists (δ0'/2). repeat split; lra.
          - exists (δ / 2). repeat split; lra. }
        destruct I10 as [δ0[I10[I11 I12]]].
        assert (I13 : x0 + δ0/2 ∈ U(x0; δ0')).
        { apply Classifier1. apply Abs_R. lra. }
        assert (I14 : x0 + δ0/2 ∈ Uº(x0; δ)).
        { apply Classifier1. split. apply Abs_not_eq_0. lra. apply Abs_R. lra. }
        apply I9 in I13. apply I5 in I14. rewrite H7 in I14.
        assert (I15 : (f[x0 + δ0/2] - f[x0])/(x0 + δ0/2 - x0) < 0). lra.
        assert (I16 : x0 + δ0/2 - x0 > 0). lra.
        apply Rmult_lt_compat_l with (r := x0 + δ0/2 - x0) in I15; auto. 
        rewrite Rmult_0_r in I15.
        assert (I17 : (x0 + δ0/2 - x0) * ((f[x0 + δ0/2] - f[x0])/(x0 + δ0/2 - x0)) 
          = f[x0 + δ0/2] - f[x0]). { field. lra. } rewrite I17 in I15. lra.
    - generalize (Theorem3_4a (\{\ λ x y, y 
        = (f[x] - f[x0])/(x - x0) \}\) x0 y0' H4 I1). intro I2. 
      assert (I3 : 0 < (y0'/2) < y0'). lra. apply I2 in I3 as I4. 
      destruct I4 as [δ[I4 I5]]. clear I2. destruct H5 as [I6 | I6].
      + destruct I6 as [I6[δ0'[I7[I8 I9]]]]. 
        assert (I10 : ∃ δ0, 0 < δ0 /\ δ0 < δ0' /\ δ0 < δ).
        { destruct (Rlt_or_le δ0' δ) as [J1 | J1].
          - exists (δ0'/2). repeat split; lra.
          - exists (δ/2). repeat split; lra. } destruct I10 as [δ0[I10[I11 I12]]].
        assert (I13 : x0 + δ0/2 ∈ U(x0; δ0')).
        { apply Classifier1. apply Abs_R. lra. }
        assert (I14 : x0 + δ0/2 ∈ Uº(x0; δ)).
        { apply Classifier1. split. apply Abs_not_eq_0. lra. apply Abs_R. lra. }
        apply I9 in I13. apply I5 in I14. rewrite H7 in I14.
        assert (I15 : (f[x0 + δ0/2] - f[x0])/(x0 + δ0/2 - x0) > 0). lra.
        assert (I16 : x0 + δ0/2 - x0 > 0). lra.
        apply Rmult_lt_compat_l with (r := x0 + δ0/2 - x0) in I15; auto. 
        rewrite Rmult_0_r in I15.
        assert (I17 : (x0 + δ0/2 - x0) * ((f[x0 + δ0/2] - f[x0])/
          (x0 + δ0/2 - x0)) = f[x0 + δ0/2] - f[x0]). { field. lra. }
        rewrite I17 in I15. lra.
      + destruct I6 as [I6[δ0'[I7[I8 I9]]]].
        assert (I10 : ∃ δ0, 0 < δ0 /\ δ0 < δ0' /\ δ0 < δ).
        { destruct (Rlt_or_le δ0' δ) as [J1 | J1].
          - exists (δ0'/2). repeat split; lra.
          - exists (δ/2). repeat split; lra. } destruct I10 as [δ0[I10[I11 I12]]].
        assert (I13 : x0 - δ0/2 ∈ U(x0; δ0')).
        { apply Classifier1. apply Abs_R. lra. }
        assert (I14 : x0 - δ0/2 ∈ Uº(x0; δ)).
        { apply Classifier1. split. apply Abs_not_eq_0. lra. apply Abs_R. lra. }
        apply I9 in I13. apply I5 in I14. rewrite H7 in I14.
        assert (I15 : (f[x0 - δ0/2] - f[x0])/(x0 - δ0/2 - x0) > 0). lra.
        assert (I16 : x0 - δ0/2 - x0 < 0). lra.
        apply Rmult_lt_gt_compat_neg_l with (r := x0 - δ0/2 - x0) in I15; auto.
        rewrite Rmult_0_r in I15.
        assert (I17 : (x0 - δ0/2 - x0) * ((f[x0 - δ0/2] - f[x0])/(x0 - δ0/2 - x0)) 
          = f[x0 - δ0/2] - f[x0]). { field. lra. }
        rewrite I17 in I15. lra. }
  split; auto; split. exists δ'. split; auto. rewrite <- H8. rewrite H8 in *. auto.
Qed.

(* 5.2 求导法则 *)
(* 5.2.1 导数的四则运算 *)

(* 函数相加求导 *)
Theorem Theorem5_4a : ∀ u v x0, Derivable u x0 -> Derivable v x0
  -> Derivative (u \+ v) x0 (u’[x0] + v’[x0]).
Proof.
  intros u v x0 [y1 H0] [y2 H1]. apply Corollary_DerivativeValue_a in H0 as H2.
  apply Corollary_DerivativeValue_a in H1 as H3. rewrite H2; rewrite H3. 
  clear H2 H3. assert (H3 : Function \{\ λ x y, y = u[x] + v[x] \}\).
  { intros x y z I1 I2. applyClassifier2 I1; applyClassifier2 I2. rewrite I2; apply I1. } 
  split; auto. apply Corollary_plus_fun_a. 
  destruct H0 as [H0[[δ1'[H4 H5]]H6]], H1 as [H1[[δ2'[H7 H8]]H9]].
  generalize (Examp1 δ1' δ2' H4 H7); intros [δ'[H10[H11 H12]]]. split.
  - exists δ'. split; auto. intros x I1. applyClassifier1 I1. apply Classifier1.
    exists (u[x] + v[x]). apply Classifier2. repeat split; auto; 
    [apply H5 | apply H8]; apply Classifier1; lra.
  - assert (H13 : Function \{\ λ x y, y 
      = ((u \+ v)[x] - (u \+ v)[x0])/(x - x0) \}\).
    { intros x y z I1 I2. applyClassifier2 I1; applyClassifier2 I2. rewrite I2; 
      apply I1. } split; auto. exists δ'. split; [assumption | split].
    + intros x I1. apply Classifier1. exists (((u \+ v)[x] - (u \+ v)[x0])/(x - x0)).
      apply Classifier2. reflexivity.
    + intros ε H14. destruct H6 as [H6[δ3'[H15[H16 H17]]]], 
      H9 as [H9[δ4'[H18[H19 H20]]]]. assert (H21 : ε/2 > 0). lra. 
      apply H20 in H21 as H22. destruct H22 as [δ2[[H22 H26]H23]]. 
      apply H17 in H21 as [δ1[[H24 H27]H25]].
      generalize (Examp2 δ' δ1 δ2 H10 H24 H22). intros [δ[H28[H29[H30 H31]]]]. 
      exists δ. split; try lra. intros x H32.
      assert (H33 : \{\ λ x y, y = ((u \+ v)[x] - (u \+ v)[x0])/(x - x0) \}\ [x]
        = ((u \+ v)[x] - (u \+ v)[x0])/(x - x0)).
      { apply f_x_T; auto. apply Classifier2. reflexivity. }
      rewrite H33. clear H33. pose proof Corollary_plus_fun_b as H33.
      assert (x ∈ dom[u] /\ x ∈ dom[v]) as [].
      { split; [apply H5 | apply H8]; apply Classifier1; lra. }
      assert (x0 ∈ dom[u] /\ x0 ∈ dom[v]) as [].
      { split; [apply H5 | apply H8]; apply Classifier1;
        rewrite Rminus_diag,Abs_ge; lra. }
      rewrite H33; auto. rewrite H33; auto. 
      assert (H38 : 0 < ∣(x - x0)∣ < δ1). lra. apply H25 in H38.
      assert (H39 : 0 < ∣(x - x0)∣ < δ2). lra. apply H23 in H39.
      assert (H40 : \{\ λ x y, y = (u[x] - u[x0])/(x - x0) \}\ [x]
        = (u[x] - u[x0])/(x - x0)). 
      { apply f_x_T; auto. apply Classifier2. reflexivity. } 
      rewrite H40 in H38. clear H40.
      assert (H40 : (\{\ λ x y, y = (v[x] - v[x0])/(x - x0) \}\) [x]
        = (v[x] - v[x0])/(x - x0)).
      { apply f_x_T; auto. apply Classifier2. reflexivity. }
      rewrite H40 in H39. clear H40.
      assert (H40 : (u[x] + v[x] - (u[x0] + v[x0]))/(x - x0) - (y1 + y2)
        = ((u[x] - u[x0])/(x - x0) - y1) + ((v[x] - v[x0])/(x - x0) - y2)).
      { field. apply Examp4 in H32. apply H32. } 
      rewrite H40. generalize (Abs_plus_le ((u[x] - u[x0])/(x - x0) - y1)
        ((v[x] - v[x0])/(x - x0) - y2)). intro H41. lra.
Qed.

(* 函数相减求导 *)
Theorem Theorem5_4b : ∀ u v x0, Derivable u x0 -> Derivable v x0
  -> Derivative (u \- v) x0 (u’[x0] - v’[x0]).
Proof.
  intros u v x0 [y1 H0] [y2 H1]. apply Corollary_DerivativeValue_a in H0 as H2.
  apply Corollary_DerivativeValue_a in H1 as H3. rewrite H2; rewrite H3. 
  clear H2 H3. assert (H3 : Function (u \- v)). { apply Corollary_sub_fun_a. } 
  split; auto. destruct H0 as [H0[[δ1'[H4 H5]]H6]]. 
  destruct H1 as [H1[[δ2'[H7 H8]]H9]]. generalize (Examp1 δ1' δ2' H4 H7); 
  intros [δ'[H10[H11 H12]]]. split.
  - exists δ'. split; auto. intros x I1. applyClassifier1 I1. apply Classifier1.
    exists (u[x] - v[x]). apply Classifier2. repeat split; auto; 
    [apply H5 | apply H8]; apply Classifier1; lra.
  - assert (H13 : Function \{\ λ x y, y 
      = ((u \- v)[x] - (u \- v)[x0])/(x - x0) \}\).
    { intros x y z I1 I2. applyClassifier2 I1; applyClassifier2 I2. rewrite I2; 
      apply I1. } split; auto. exists δ'. split; [assumption | split].
    + intros x I1. apply Classifier1. exists (((u \- v)[x] - (u \- v)[x0])/(x - x0)).
      apply Classifier2. reflexivity.
    + intros ε H14. destruct H6 as [H6[δ3'[H15[H16 H17]]]].
      destruct H9 as [H9[δ4'[H18[H19 H20]]]]. assert (H21 : ε/2 > 0). lra.
      apply H20 in H21 as H22. destruct H22 as [δ2[[H22 H26]H23]].
      apply H17 in H21 as [δ1[[H24 H27]H25]].
      generalize (Examp2 δ' δ1 δ2 H10 H24 H22). intros [δ[H28[H29[H30 H31]]]].
      exists δ. split; try lra. intros x H32.
      assert (H33 : \{\ λ x y, y = ((u \- v)[x] - (u \- v)[x0])/(x - x0) \}\ [x]
        = ((u \- v)[x] - (u \- v)[x0])/(x - x0)).
      { apply f_x_T; auto. apply Classifier2. reflexivity. } rewrite H33. clear H33.
      assert (H33 : ∀ x1, x1 ∈ dom[u] -> x1 ∈ dom[v] 
        -> (u \- v)[x1] = u[x1] - v[x1]).
      { intros. rewrite Corollary_sub_fun_b; auto. }
      assert (x ∈ dom[u] /\ x ∈ dom[v]) as [].
      { split; [apply H5 | apply H8]; apply Classifier1; lra. }
      assert (x0 ∈ dom[u] /\ x0 ∈ dom[v]) as [].
      { split; [apply H5 | apply H8]; apply Classifier1; rewrite Abs_ge; lra. }
      rewrite H33; auto. rewrite H33; auto.
      assert (H38 : 0 < ∣(x - x0)∣ < δ1). lra. apply H25 in H38.
      assert (H39 : 0 < ∣(x - x0)∣ < δ2). lra. apply H23 in H39.
      assert (H40 : \{\ λ x y, y = (u[x] - u[x0])/(x - x0) \}\ [x]
        = (u[x] - u[x0])/(x - x0)).
      { apply f_x_T; auto. apply Classifier2. reflexivity. }
      rewrite H40 in H38. clear H40.
      assert (H40 : \{\ λ x y, y = (v[x] - v[x0])/(x - x0) \}\ [x]
        = (v[x] - v[x0])/(x - x0)).
      { apply f_x_T; auto. apply Classifier2. reflexivity. }
      rewrite H40 in H39. clear H40.
      assert (H40 : (u[x] - v[x] - (u[x0] - v[x0]))/(x - x0) - (y1 - y2)
        = ((u[x] - u[x0])/(x - x0) - y1) - ((v[x] - v[x0])/(x - x0) - y2)).
      { field. apply Examp4 in H32. apply H32. } rewrite H40.
      generalize (Abs_minus_le ((u[x] - u[x0])/(x - x0) - y1)
        ((v[x] - v[x0])/(x - x0) - y2)). intro H41. lra.
Qed.

(* 函数相乘求导 *)
Lemma Lemma5_5a : ∀ f x0, Derivable' f x0
  -> Derivable' \{\ λ h y, y = f[x0 + h] \}\ 0.
Proof.
  intros. destruct H as [y H]. destruct H as [H H1]. destruct H1 as [H1 H2]. 
  exists y. split.
  - unfold Function. intros. applyClassifier1 H0. destruct H0 as [x1[y1[H4 H5]]].
    applyClassifier1 H3. destruct H3 as [x2[y2[H3 H6]]]. apply ProdEqual in H4. 
    apply ProdEqual in H3. destruct H4 as [J1 J2]. destruct H3 as [J3 J4].
    rewrite <- J1 in H5. rewrite <- J3 in H6. rewrite <- J2 in H5.
    rewrite <- J4 in H6. rewrite H6, H5. auto.
  - split. exists 1. split. lra. intros x I1. apply Classifier1. exists (f[x0 + x]). 
    apply Classifier2. auto.
    assert (\{\ λ h0 y0, y0 = (\{\ λ h1 y1, y1 = f[x0 + h1] \}\ [0 + h0]
      - \{\ λ h1 y1, y1 = f[x0 + h1] \}\ [0])/h0 \}\
      = \{\ λ h0 y0, y0 = (f[x0 + h0] - f[x0])/h0 \}\).
    { apply AxiomI. split; intros.
      - applyClassifier1 H0. destruct H0 as [x'[y'[H0 H3]]]. apply Classifier1. 
        exists x',y'. split; auto.
        assert (J1: \{\ λ h1 y1, y1 = f[x0 + h1] \}\[0 + x'] = f[x0 + x']).
        { apply f_x_T. unfold Function. intros. applyClassifier1 H4. 
          destruct H4 as [x1[y1[H4 H6]]]. applyClassifier1 H5.
          destruct H5 as [x2[y2[H5 H7]]]. apply ProdEqual in H4. 
          apply ProdEqual in H5. destruct H4 as [J1 J2]. destruct H5 as [J3 J4].
          rewrite <- J1 in H6. rewrite <- J3 in H7. rewrite <- J2 in H6.
          rewrite <- J4 in H7. rewrite H6, H7. auto. apply Classifier2.
          rewrite <- Rplus_assoc. rewrite Rplus_0_r. auto. }
        rewrite J1 in H3. clear J1.
        assert (J1: \{\ λ h1 y1,y1 = f[x0 + h1] \}\ [0] = f[x0]).
        { apply f_x_T. unfold Function. intros. applyClassifier1 H4. 
          destruct H4 as [x1[y1[H4 H6]]]. applyClassifier1 H5.
          destruct H5 as [x2[y2[H5 H7]]]. apply ProdEqual in H4.
          apply ProdEqual in H5. destruct H4 as [J1 J2]. destruct H5 as [J3 J4].
          rewrite <- J1 in H6. rewrite <- J3 in H7. rewrite <- J2 in H6.
          rewrite <- J4 in H7. rewrite H6, H7. auto. apply Classifier2.
          rewrite Rplus_0_r. auto. } rewrite J1 in H3. clear J1. apply H3.
      - applyClassifier1 H0. destruct H0 as [x'[y'[H0 H3]]]. apply Classifier1. 
        exists x', y'. split; auto.
        assert (J1: \{\ λ h1 y1, y1 = f[x0 + h1] \}\ [0 + x'] = f[x0 + x']).
        { apply f_x_T. unfold Function. intros. applyClassifier1 H4. 
          destruct H4 as [x1[y1[H4 H6]]]. applyClassifier1 H5.
          destruct H5 as [x2[y2[H5 H7]]]. apply ProdEqual in H4.
          apply ProdEqual in H5. destruct H4 as [J1 J2]. destruct H5 as [J3 J4].
          rewrite <- J1 in H6. rewrite <- J3 in H7. rewrite <- J2 in H6.
          rewrite <- J4 in H7. rewrite H6, H7. auto. apply Classifier2.
          rewrite <- Rplus_assoc. rewrite Rplus_0_r. auto. } rewrite J1. clear J1.
        assert (J1: \{\ λ h1 y1,y1 = f[x0 + h1] \}\ [0] = f[x0]).
        { apply f_x_T. unfold Function. intros. applyClassifier1 H4.
          destruct H4 as [x1[y1[H4 H6]]]. applyClassifier1 H5.
          destruct H5 as [x2[y2[H5 H7]]]. apply ProdEqual in H4.
          apply ProdEqual in H5. destruct H4 as [J1 J2]. destruct H5 as [J3 J4].
          rewrite <- J1 in H6. rewrite <- J3 in H7. rewrite <- J2 in H6.
          rewrite <- J4 in H7. rewrite H6, H7. auto. apply Classifier2.
          rewrite Rplus_0_r. auto. } rewrite J1. clear J1. apply H3. }
    rewrite H0. apply H2.
Qed.

Lemma Lemma5_5b : ∀ f x0, Derivable' \{\ λ h y, y = f[x0 + h] \}\ 0
  -> limit \{\ λ h y, y = f[x0 + h] \}\ 0 (f[x0]).
Proof.
  intros. assert (H0: Derivable \{\ λ h y, y = f[x0 + h] \}\ 0).
  { pose proof H as H'. destruct H' as [y0 H']. exists y0.
    rewrite <- EquaDerivative in H'. apply H'. }
  apply Theorem5_1 in H0. destruct H0 as [H0 H1].
  assert (H2: \{\ λ h y, y = f[x0 + h] \}\ [0] = f[x0]).
  { apply f_x_T. unfold Function. intros. applyClassifier1 H2. 
    destruct H2 as [x1[y1[H2 H4]]]. applyClassifier1 H3. 
    destruct H3 as [x2[y2[H3 H5]]]. apply ProdEqual in H2. apply ProdEqual in H3. 
    destruct H2 as [J1 J2]. destruct H3 as [J3 J4]. rewrite <- J1 in H4. 
    rewrite <- J3 in H5. rewrite <- J2 in H4. rewrite <- J4 in H5. 
    rewrite H4, H5. auto. apply Classifier2. rewrite Rplus_0_r. auto. }
  rewrite H2 in H1. apply H1.
Qed.

Theorem Theorem5_5a : ∀ u v x0, Derivable' u x0 -> Derivable' v x0
  -> Derivative' (u \* v) x0 (u’[x0] * v[x0] + v’[x0] * u[x0]).
Proof.
  intros u v x0. intros [y1 H0]. intros [y2 H1].
  apply Corollary_DerivativeValue_b in H0 as H2. 
  apply Corollary_DerivativeValue_b in H1 as H3.
  assert (H4 : Function (u \* v)). { apply Corollary_mult_fun_a. }
  split; auto. destruct H0 as [H0[[δ1'[H5 H6]]H7]].
  destruct H1 as [H1[[δ2'[H8 H9]]H10]]. generalize (Examp1 δ1' δ2' H5 H8); 
  intros [δ'[H11[H12 H13]]]. split. exists δ'. split; auto. intros x I1. 
  applyClassifier1 I1. apply Classifier1. exists (u[x] * v[x]). apply Classifier2.
  repeat split; auto; [apply H6 | apply H9]; apply Classifier1; lra.
  set (f1 := \{\ λ h y, y = (u[x0 + h] - u[x0])/h \}\).
  set (g1 := \{\ λ h y, y = v[x0 + h] \}\).
  set (f2 := \{\ λ h y, y = (v[x0 + h] - v[x0])/h \}\).
  set (g2 := \{\ λ (h y : R), y = u[x0] \}\).
  set (φ := f1 \* g1 \+ f2 \* g2). assert (limit f1 0 y1); auto. 
  assert (limit f2 0 y2); auto. assert (limit g1 0 v[x0]). 
  { apply Lemma5_5b, Lemma5_5a. exists y2. split; eauto. }
  assert (limit g2 0 u[x0]).
  { assert (Function g2).
    { red; intros. applyClassifier2 H16. applyClassifier2 H17. subst; auto. }
    split; auto. exists 1. split. lra. split. red; intros. apply Classifier1.
    exists u[x0]. apply Classifier2; auto. intros. exists (1/2). split. lra.
    intros. replace g2[x] with u[x0]. rewrite Abs_ge; lra.
    assert ([x, u[x0]] ∈ g2 /\ [x, g2[x]] ∈ g2) as [].
    { split. apply Classifier2; auto. apply x_fx_T; auto. apply Classifier1.
      exists u[x0]. apply Classifier2; auto. } apply (H16 x); auto. }
  assert (limit φ 0 (u’[x0] * v[x0] + v’[x0] * u[x0])).
  { rewrite H2, H3. apply Theorem3_7a; apply Theorem3_7c; auto. }
  split. red; intros. applyClassifier2 H18. applyClassifier2 H19. subst; auto.
  exists δ1'. split; auto. split. red; intros. apply Classifier1.
  exists (((u \* v)[x0 + z] - (u \* v)[x0])/z). apply Classifier2; auto. intros.
  destruct H17 as [H17[x[H19[]]]]. apply H21 in H18 as [x1[[]]].
  generalize (Examp1 δ' x1 H11 H18); intros [x'[H24[H25 H26]]]. exists x'.
  split. lra. intros. assert (0 < ∣(x2 - 0)∣ < x1). lra. apply H23 in H28.
  apply H21 in H18.
  assert (φ[x2] = \{\ λ h y, y = ((u \* v)[x0 + h] - (u \* v)[x0])/h \}\ [x2]).
  { assert ([x2, φ[x2]] ∈ φ).
    { apply x_fx_T; auto. apply H20. apply Classifier1. lra. }
    assert ([x2, \{\ λ h y, y = ((u \* v)[x0 + h] - (u \* v)[x0])/h \}\ [x2]] ∈ φ).
    { apply Classifier2. rewrite Corollary_mult_fun_c, Corollary_mult_fun_c.
      assert (x2 ∈ dom[f1] /\ x2 ∈ dom[g1] /\ x2 ∈ dom[f2] /\ x2 ∈ dom[g2]).
      { repeat split; apply Classifier1; [exists ((u[x0 + x2] - u[x0])/x2) |
        exists v[x0 + x2] | exists ((v[x0 + x2] - v[x0])/x2) | exists u[x0]];
        apply Classifier2; auto. } destruct H30 as [H30[H31[]]].
      assert (x0 ∈ dom[u] /\ x0 ∈ dom[v]) as [].
      { split; [apply H6 | apply H9]; apply Classifier1; rewrite Abs_ge; lra. }
      assert ((x0 + x2) ∈ dom[u] /\ (x0 + x2) ∈ dom[v]) as [].
      { destruct H27. rewrite Rminus_0_r in H27, H36. split; [apply H6 | apply H9];
        apply Classifier1; replace (x0 + x2 - x0) with x2; try lra. }
      repeat split; try apply Classifier1; auto. apply Classifier1. rewrite FunValue.
      rewrite Corollary_mult_fun_b, Corollary_mult_fun_b,
      Corollary_mult_fun_b, Corollary_mult_fun_b; auto. unfold f1, f2, g1, g2.
      repeat rewrite FunValue. lra. } apply (H17 x2); auto. }
  rewrite <- H29; auto.
Qed.

Theorem Theorem5_5b : ∀ u v x0, Derivable u x0 -> Derivable v x0
  -> Derivative (u \* v) x0 (u’[x0] * v[x0] + v’[x0] * u[x0]).
Proof.
  intros. destruct H as [y'], H0 as [y0']. apply EquaDerivative in H.
  apply EquaDerivative in H0. apply EquaDerivative. apply Theorem5_5a; red; eauto.
Qed.

Corollary Corollary5_5 : ∀ v c x0, Derivable v x0
  -> Derivative (v \\* c) x0 (c * v’[x0]).
Proof.
  assert (∀ c x0, Derivative \{\ λ x y, y = c \}\ x0 0).
  { intros. split. red; intros. applyClassifier2 H. applyClassifier2 H0. subst; auto.
    split. exists 1. split. lra. red; intros. apply Classifier1. exists c.
    apply Classifier2; auto. split. red; intros. applyClassifier2 H. applyClassifier2 H0.
    subst; auto. exists 1. split. lra. split. red; intros. apply Classifier1.
    exists ((\{\ λ _ y1, y1 = c \}\[z] - \{\ λ _ y1, y1 = c \}\[x0])/(z - x0)).
    apply Classifier2; auto. intros. exists (1/2). split. lra. intros.
    rewrite FunValue,FunValue,FunValue,Rminus_diag. unfold Rdiv.
    rewrite Rmult_0_l,Abs_ge; lra. }
  intros. assert (v \\* c = v \* \{\ λ _ v, v = c \}\).
  { apply AxiomI; split; intros; destruct z; applyClassifier2 H1; destruct H1;
    apply Classifier2; split; auto. split. apply Classifier1. exists c.
    apply Classifier2; auto. rewrite FunValue; auto. destruct H2.
    rewrite FunValue in H3; auto. }
  rewrite H1. pose proof H0. pose proof (H c x0).
  pose proof H3. apply Corollary_DerivativeValue_a in H4.
  apply (Theorem5_5b v (\{\ λ _ v0, v0 = c \}\) x0) in H2.
  rewrite FunValue,H4,Rmult_0_l,Rplus_0_r,Rmult_comm in H2; auto.
  red; eauto.
Qed.

(* 函数相除求导 *)
Lemma Lemma5_6 : ∀ u (x0 : R), u [x0] <> 0 -> Derivable u x0 
  -> Derivative \{\ λ x y, y = 1/u[x] \}\ x0 (-(u’[x0]/(u[x0] * u[x0]))).
Proof.
  intros. apply EquaDerivative. split. red; intros. applyClassifier2 H1; 
  applyClassifier2 H2. subst; auto. split. exists 1. split. lra. red; intros. 
  apply Classifier1. exists (1/u[z]). apply Classifier2; auto. destruct H0.
  assert (limit (\{\ λ h y, y = -((u[x0 + h] - u[x0])/h) \}\
    \* (1 /// \{\ λ h y, y = u[x0 + h] * u[x0] \}\)) 0 ((-x) * (/(u[x0] * u[x0])))).
  { apply Theorem3_7c.
    - apply EquaDerivative in H0. destruct H0 as [H0[[x1[]][H3[x2[H4[]]]]]].
      split. red; intros. applyClassifier2 H7; applyClassifier2 H8. subst; auto.
      exists x2. split; auto. split; unfold Contain; intros. apply Classifier1.
      exists (-((u[x0 + z] - u[x0])/z)). apply Classifier2; auto.
      apply H6 in H7 as [x3[]]. exists x3. split; auto. intros. apply H8 in H9.
      rewrite FunValue. rewrite FunValue in H9.
      replace (-((u[x0 + x4] - u[x0])/x4) - -x)
      with (-((u[x0 + x4] - u[x0])/x4 - x)). rewrite <- Abs_eq_neg; auto. lra.
    - apply Lemma3_7d. assert (Derivable u x0). { exists x. auto. }
      apply Theorem5_1 in H1 as [H1[H2[x1[H3[]]]]]. split. red; intros.
      applyClassifier2 H6. applyClassifier2 H7. subst; auto. exists x1. split; auto.
      split. red; intros. apply Classifier1. exists (u[x0 + z] * u[x0]).
      apply Classifier2; auto. intros. 
      assert (∣(u[x0])∣ > 0). { apply Abs_not_eq_0. auto. }
      assert (ε/∣(u[x0])∣ > 0). { apply Rdiv_lt_0_compat; auto. }
      apply H5 in H8 as [x2[]]. exists x2. split; auto. intros.
      replace (x3 - 0) with (x3 + x0 - x0) in H10; [ | lra].
      apply H9 in H10. rewrite FunValue, <- Rmult_minus_distr_r, Abs_mult.
      apply (Rmult_lt_compat_r ∣(u[x0])∣) in H10; auto.
      unfold Rdiv in H10. rewrite (Rmult_comm ε),(Rmult_comm (/∣(u[x0])∣ * ε)),
      <- Rmult_assoc, Rinv_r_simpl_r, Rplus_comm in H10; auto. lra.
      apply Rmult_integral_contrapositive; auto. }
  destruct H1 as [H1[x1[H2[]]]]. split. red; intros. applyClassifier2 H5.
  applyClassifier2 H6. subst; auto. exists x1. split; auto. split. red; intros.
  apply Classifier1. exists ((\{\ λ x2 y1, y1 = 1/u[x2] \}\ [x0 + z] 
    - \{\ λ x2 y1, y1 = 1/u[x2] \}\ [x0])/z). apply Classifier2; auto. intros.
  apply H4 in H5 as [x2[]]. exists x2. split; auto. intros.
  assert (x3 ∈ Uº(0; x1)). { apply Classifier1. lra. }
  assert (x3 <> 0).
  { intro. applyClassifier1 H8. rewrite H9, Abs_ge, Rminus_0_r in H8; lra. }
  assert (u[x0 + x3] * u [x0] <> 0).
  { apply H3 in H8. rewrite Corollary_mult_fun_c, Corollary_div_fun_d in H8.
    applyClassifier1 H8. destruct H8. applyClassifier1 H10. destruct H10.
    applyClassifier1 H11. rewrite FunValue in H11; auto. }
  assert (u[x0 + x3] <> 0). { intro. rewrite H11, Rmult_0_l in H10; auto. }
  apply H6 in H7. rewrite Corollary_mult_fun_b, Corollary_div_fun_f, FunValue,
  FunValue in H7. rewrite FunValue, FunValue, FunValue.
  apply Corollary_DerivativeValue_a in H0. rewrite H0.
  assert (-((u[x0 + x3] - u[x0])/x3) * (1/(u[x0 + x3] * u[x0]))
    = (1/u[x0 + x3] - 1/u[x0])/x3).
  { rewrite <- Rdiv_opp_l. unfold Rdiv. rewrite Rmult_1_l, Rmult_assoc,
    (Rmult_comm (/x3)), <- (Rmult_assoc _ _ (/x3)). apply Rmult_eq_compat_r.
    rewrite Rmult_1_l, Rmult_1_l, Ropp_minus_distr, Rmult_minus_distr_r,
    Rinv_mult, (Rmult_comm (/u[x0 + x3])), <- Rmult_assoc, Rinv_r_simpl_r,
    (Rmult_comm (/u[x0])), <- Rmult_assoc, Rinv_r_simpl_r; auto. }
  assert (-x */(u[x0] * u[x0]) = -(x/(u[x0] * u[x0]))). lra.
  rewrite H12, H13 in H7. auto. apply Classifier1. exists (u[x0 + x3] * u[x0]).
  apply Classifier2; auto. rewrite FunValue; auto. apply Classifier1.
  exists (-((u[x0 + x3] - u[x0])/x3)). apply Classifier2; auto.
  rewrite Corollary_div_fun_d. apply Classifier1. split. apply Classifier1.
  exists (u[x0 + x3] * u[x0]). apply Classifier2; auto. apply Classifier1.
  rewrite FunValue; auto.
Qed.

Theorem Theorem5_6 : ∀ u v (x0: R), Derivable u x0 -> Derivable v x0 -> v[x0] <> 0 
  -> Derivative (u // v)  x0 ((u’[x0] * v[x0] - u[x0] * v’[x0])/(v[x0] * v[x0])).
Proof.
  intros u v x0 H H0 H2. apply Lemma5_6 in H0 as H1; auto. pose proof H as [u' J2].
  apply (EquaDerivative u x0 u') in J2 as J1. pose proof H0 as [v' J3].
  apply (EquaDerivative v x0 v') in J3 as J4. unfold Rdiv.
  assert (∃ g, g = \{\ λ x y,y = 1/v[x] \}\).
  { exists \{\ λ x y,y = 1/v[x] \}\; auto.  }
  destruct H3 as [g]. rewrite <- H3 in H1. apply EquaDerivative.
  assert (Function g).
  { rewrite H3. red; intros. applyClassifier2 H4; applyClassifier2 H5. subst; auto. }
  assert (forall x, g [x] = /v[x]).
  { intros. apply f_x_T; auto. rewrite H3. apply Classifier2; auto. lra. }
  assert (u // v = \{\ λ x y, x ∈ dom[u] /\ x ∈ dom[v]
    /\ v[x] <> 0 /\ y = u[x] * g[x] \}\).
  { apply AxiomI. split; intros.
    - applyClassifier1 H6. apply Classifier1. destruct H6 as [x[y[H6[H7[H8[]]]]]].
      exists x, y. repeat split; auto. rewrite H5; auto.
    - applyClassifier1 H6. apply Classifier1. destruct H6 as [x[y[H6[H7[H8[]]]]]].
      exists x, y. repeat split; auto. rewrite H5 in H10; auto. }
  rewrite H6. apply Corollary_DerivativeValue_a in H1 as H7.
  apply Corollary_DerivativeValue_a in J2 as H8.
  assert (u’[x0] * g[x0] + u[x0] * g’[x0]
    = (u’[x0] * v[x0] - u[x0] * v’[ x0]) * /(v[x0] * v[x0])).
  { unfold Rminus. rewrite Rmult_plus_distr_r. rewrite Rmult_assoc. 
    replace (v[x0] * /(v[x0] * v[x0])) with (/v[x0]). rewrite H5. 
    apply Rplus_eq_compat_l. rewrite H7. lra.
    replace (/(v [x0] * v [x0])) with (/v[x0] * /v[x0]).
    rewrite <- Rmult_assoc. rewrite Rinv_r; auto; lra.
    rewrite Rinv_mult; auto; lra. }
  rewrite <- H9. assert (u[x0] * g’[x0] = g’[x0] * u[x0]). lra. rewrite H10.
  assert (Derivative' (u \* g) x0 (u’[x0] * g[x0] + g’[x0] * u[x0])).
  { apply (Theorem5_5a u g x0); red; eauto. apply EquaDerivative in H1; eauto. }
  destruct H11 as [H11[_ H13]]. split. red; intros. applyClassifier2 H12.
  applyClassifier2 H14. destruct H12 as [_[_[]]], H14 as [_[_[]]]. subst; auto.
  pose proof J1; pose proof H0. destruct H12 as [_[[x[]]_]].
  apply Theorem5_1 in H14 as [].
  assert (∃ δ, δ > 0 /\ (∀ x, x ∈ Uº(x0; δ) -> v[x] <> 0)).
  { destruct (Req_appart_dec v[x0] 0) as [H17 | [H17 | H17]]. contradiction.
    pose proof (Theorem3_4b v x0 v[x0] H16 H17 (-v[x0]/2)).
    assert (0 < -v[x0]/2 < -v[x0]). lra. apply H18 in H19 as [x1[]]. exists x1. 
    split; auto. intros. apply H20 in H21. intro. rewrite H22 in H21. lra. 
    pose proof (Theorem3_4a v x0 v[x0] H16 H17 (v[x0]/2)).
    assert (0 < v[x0]/2 < v[x0]). lra. apply H18 in H19 as [x1[]]. exists x1. 
    split; auto. intros. apply H20 in H21. intro. rewrite H22 in H21. lra. } 
  destruct H17 as [x1[]]. destruct H16 as [H16[x2[H19[H20 _]]]].
  destruct (Examp2 x x1 x2 H12 H17 H19) as [x3[H21[H22[]]]].
  assert (Uº(x0; x) ⊂ U(x0; x) /\ Uº(x0; x3) ⊂ U(x0; x3)) as [].
  { split; red; intros; applyClassifier1 H25; apply Classifier1; lra. } split.
  exists x3. split; auto. red; intros. apply Classifier1. exists (u[z] * g[z]).
  destruct (classic (z = x0)) as [Hc|Hc]. rewrite Hc.
  apply Classifier2; repeat split; auto. apply H15. apply Classifier1.
  rewrite Rminus_diag, Abs_ge; auto. lra.
  assert (z ∈ Uº(x0; x) /\ z ∈ Uº(x0; x3)) as [].
  { assert (0 < ∣(z - x0)∣). apply Abs_not_eq_0. lra. split; apply Classifier1;
    split; try lra; applyClassifier1 H27; lra. }
  apply Classifier2; repeat split; auto; [apply H20 | apply H18]; apply Classifier1; 
  applyClassifier1 H29; try lra.
  destruct H13 as [H13[x4[H27[]]]]. split. red; intros. applyClassifier2 H30.
  applyClassifier2 H31. subst; auto. destruct (Examp1 x3 x4 H21 H27) as [x5[H30[]]]. 
  exists x5. split; auto. split. red; intros. apply Classifier1. 
  exists ((\{\ λ x6 y1, (x6 ∈ dom[u]) /\ (x6 ∈ dom[v])
      /\ v[x6] <> 0 /\ y1 = u[x6] * g[x6] \}\ [x0 + z]
    - \{\ λ x6 y1, (x6 ∈ dom[u]) /\ (x6 ∈ dom[v]) /\ v[x6] <> 0
      /\ y1 = u[x6] * g[x6] \}\ [x0])/z). apply Classifier2; auto. intros.
  apply H29 in H33 as [x6[[]]]. destruct (Examp1 x5 x6 H30 H33) as [x7[H36[]]]. 
  exists x7. split. lra. intros. rewrite FunValue.
  assert (∀ x, x ∈ dom[u] -> x ∈ dom[v] -> v[x] <> 0
    -> \{\ λ x4 y, x4 ∈ dom[u] /\ x4 ∈ dom[v] /\ v[x4] <> 0
      /\ y = u[x4] * g[x4] \}\ [x] = u[x] * g[x]).
  { intros. assert (Function \{\ λ x4 y, x4 ∈ dom[u] /\ x4 ∈ dom[v]
      /\ v[x4] <> 0 /\ y = u[x4] * g[x4] \}\).
    { red; intros. applyClassifier2 H43. applyClassifier2 H44.
      destruct H43 as [_[_[]]], H44 as [_[_[]]]. subst; auto. }
    assert ([x9, (u[x9] * g[x9])] ∈ \{\ λ x4 y, x4 ∈ dom[u] /\ x4 ∈ dom[v]
        /\ v[x4] <> 0 /\ y = u[x4] * g[x4] \}\
      /\ [x9, (\{\ λ x4 y, x4 ∈ dom[u] /\ x4 ∈ dom[v]
        /\ v[x4] <> 0 /\ y = u[x4] * g[x4] \}\ [x9])] ∈ \{\ λ x4 y, x4 ∈ dom[u]
        /\ x4 ∈ dom[v] /\ v[x4] <> 0 /\ y = u[x4] * g[x4] \}\) as [].
    { split. apply Classifier2; auto. apply x_fx_T; auto. apply Classifier1.
      exists (u[x9] * g[x9]). apply Classifier2; auto. } apply (H43 x9); auto. }
  assert (x0 ∈ dom[u]) as I1.
  { apply H15. apply Classifier1. rewrite Rminus_diag, Abs_ge; auto. lra. }
  assert (x0 + x8 ∈ dom[u]) as I2.
  { apply H15. apply Classifier1. replace (x0 + x8 - x0) with x8.
    rewrite Rminus_0_r in H39. lra. lra. }
  assert (x0 + x8 ∈ dom[v]) as I3.
  { apply H20. apply Classifier1. replace (x0 + x8 - x0) with x8. 
    rewrite Rminus_0_r in H39. lra. lra. }
  assert (x0 + x8 ∈ dom[g]) as I4.
  { apply Classifier1. exists (1/v[x0 + x8]). rewrite H3. apply Classifier2; auto. }
  rewrite H40, H40; auto. assert (0 < ∣(x8 - 0)∣ < x6). lra.
  apply H35 in H41. rewrite FunValue, Corollary_mult_fun_b,
  Corollary_mult_fun_b in H41; auto. apply Classifier1. exists (1/v[x0]).
  rewrite H3. apply Classifier2; auto. apply H18. apply Classifier1.
  replace (x0 + x8 - x0) with x8. rewrite Rminus_0_r in H39. lra. lra.
Qed.


(* 反函数的导数 *)
Lemma Lemma5_7 : ∀ f g x0 δ, Inverse_Function f g -> δ > 0 
  -> U(x0; δ) ⊂ dom[f] -> ContinuousOpen f (x0 - δ) (x0 + δ)
  -> DStrictlyMonotonicFun f U(x0; δ)
  -> ∃ a b, a = Rbasic_fun.Rmin f[x0 - δ/2] f[x0 + δ/2] 
    /\ b = Rbasic_fun.Rmax f[x0 - δ/2] f[x0 + δ/2]
    /\ \(a, b\) ⊂ dom[f ﹣¹] /\ (∀ y, y ∈ \(a, b\) 
  -> Continuous f ﹣¹ y /\ DStrictlyMonotonicFun f ﹣¹ \(a, b\)).
Proof.
  intros. red in H1. pose proof H as H'. red in H. destruct H. 
  pose proof H2 as H2'. red in H2. pose proof H3 as H3'. red in H3.  
  assert (x0 - δ/2 ∈ U(x0; δ)).
  { apply Classifier1. assert ((x0 - δ/2 - x0) = (x0 - x0 - δ/2)). lra. rewrite H5. 
    rewrite Abs_lt. lra. lra. }
  assert (x0 + δ/2 ∈ U(x0; δ)).
  { apply Classifier1. assert ((x0 + δ/2 - x0) = (x0 - x0 + δ/2)). lra. rewrite H6. 
    rewrite Abs_gt. lra. lra. }
  assert (ContinuousClose f (x0 - δ/2) (x0 + δ/2)). 
  { red in H. destruct H. red. split. red. intros. apply H2. lra.
    assert (Continuous f (x0 - δ/2)). { apply H2. lra. }
    assert (Continuous f (x0 + δ/2)). { apply H2. lra. }
    apply Theorem4_1 in H8. destruct H8. apply Theorem4_1 in H9. destruct H9.
    split; auto. }
  destruct H3; pose proof H3 as I3; red in H3; destruct H3 as [H3[H8 H9]].  
  - exists (f[x0 - δ/2]), (f[x0 + δ/2]). 
    apply (H9 (x0 - δ/2)(x0 + δ/2)) in H5 as H5'; auto. split. 
    unfold Rbasic_fun.Rmin. destruct Rle_dec. auto. lra. split. 
    unfold Rbasic_fun.Rmax. destruct Rle_dec. auto. lra. split. red. intros y H10.
    pose proof (Inverse_P1 f). destruct H11. applyClassifier1 H10. rewrite H11.
    apply (Theorem4_7 f (x0 - δ/2) (x0 + δ/2) y) in H7 as H13; auto. 
    destruct H13 as [x[H14 H14']]. rewrite <- H14'. 
    assert (x ∈ dom[f]). { apply H1. apply Classifier1. apply Abs_R. lra. }
    red in H. destruct H. apply fx_ran_T; auto. lra.  
    + intros. assert (ContinuousClose (f ﹣¹) f[x0 - δ/2] f[x0 + δ/2]).
      { apply (Theorem4_8a f (f ﹣¹) (x0 - δ/2) (x0 + δ/2)); auto. rewrite <- H4. 
        auto. lra. red. red in I3. destruct I3 as [I1[I2 I3]]. split; auto. split. 
        - intros x' I4. apply Classifier1. exists f[x']. apply x_fx_T; auto. 
          apply H1. apply Classifier1. apply Abs_R. applyClassifier1 I4. lra. 
        - intros. apply I3; auto. apply Classifier1. apply Abs_R. applyClassifier1 H11.
          lra. apply Classifier1. apply Abs_R. applyClassifier1 H12. lra. }
      red in H11. destruct H11 as [H11[H12 H13]]. red in H11. applyClassifier1 H10. 
      apply H11 in H10; auto. split; auto. red. left.
      assert (DStrictlyIncreaseFun (f﹣¹) (\[ f[x0 - δ/2], f[x0 + δ/2] \])).  
      { rewrite <- H4. apply (Lemma_4_8a f g (x0 - δ/2) (x0 + δ/2)); auto. lra. 
        red in I3. destruct I3 as [I1[I2 I3]]. red. split; auto. split. 
        intros x' I4. apply Classifier1. exists f[x']. apply x_fx_T; auto. apply H1. 
        apply Classifier1. apply Abs_R. applyClassifier1 I4. lra. intros. apply I3. 
        apply Classifier1. applyClassifier1 H14. apply Abs_R. lra. apply Classifier1. 
        applyClassifier1 H15. apply Abs_R. lra. auto. }
      red in H14. destruct H14 as [H14[H15 H16]]. red. split; auto. split.
      * intros y0 H17. applyClassifier1 H17. 
        apply (Theorem4_7 f (x0 - δ/2) (x0 + δ/2) y0) in H7 as H18; auto.
        destruct H18 as [x'[H18 H18']]. apply Classifier1. exists x'. apply Classifier2. 
        rewrite <- H18'. apply x_fx_T; auto. apply H1. apply Classifier1. 
        apply Abs_R. lra. lra.
      * intros. apply H16; auto. apply Classifier1. applyClassifier1 H17. destruct H17.
        split. left; auto. left; auto. apply Classifier1. applyClassifier1 H18. 
        destruct H18. split. left; auto. left; auto.
    + lra.
  - exists (f[x0 + δ/2]), (f[x0 - δ/2]). 
    apply (H9 (x0 - δ/2)(x0 + δ/2)) in H5 as H5'; auto. split. 
    unfold Rbasic_fun.Rmin. destruct Rle_dec. lra. auto. split. 
    unfold Rbasic_fun.Rmax. destruct Rle_dec. auto. lra. auto. split. red. 
    intros y H10. pose proof (Inverse_P1 f). destruct H11. applyClassifier1 H10. 
    rewrite H11. apply (Theorem4_7 f (x0 - δ/2) (x0 + δ/2) y) in H7 as H13; auto. 
    destruct H13 as [x[H14 H14']]. rewrite <- H14'. 
    assert (x ∈ dom[f]). { apply H1. apply Classifier1. apply Abs_R. lra. }
    red in H. destruct H. apply fx_ran_T; auto. lra.  
    + intros. assert (ContinuousClose (f ﹣¹) f[x0 + δ/2] f[x0 - δ/2]).
      { apply (Theorem4_8_b f (f ﹣¹) (x0 - δ/2) (x0 + δ/2)); auto. 
        rewrite <- H4. auto. lra. red. red in I3. destruct I3 as [I1[I2 I3]].
        split; auto. split. 
        - intros x' I4. apply Classifier1. exists f[x']. apply x_fx_T; auto. 
          apply H1. apply Classifier1. apply Abs_R. applyClassifier1 I4. lra. 
        - intros. apply I3; auto. apply Classifier1. apply Abs_R. applyClassifier1 H11.
          lra. apply Classifier1. apply Abs_R. applyClassifier1 H12. lra. }
      red in H11. destruct H11 as [H11[H12 H13]]. red in H11. applyClassifier1 H10. 
      apply H11 in H10; auto. split; auto. red. right.
      assert (DStrictlyDecreaseFun (f﹣¹) (\[ f[x0 + δ/2], f[x0 - δ/2] \])).  
      { rewrite <- H4. apply (Lemma_4_8b f g (x0 - δ/2) (x0 + δ/2)); auto. lra. 
        red in I3. destruct I3 as [I1[I2 I3]]. red. split; auto. split. 
        intros x' I4. apply Classifier1. exists f[x']. apply x_fx_T; auto. apply H1. 
        apply Classifier1. apply Abs_R. applyClassifier1 I4. lra. intros. apply I3. 
        apply Classifier1. applyClassifier1 H14. apply Abs_R. lra. apply Classifier1. 
        applyClassifier1 H15. apply Abs_R. lra. auto. }
      red in H14. destruct H14 as [H14[H15 H16]]. red. split; auto. split. 
      * intros y0 H17. applyClassifier1 H17.
        apply (Theorem4_7 f (x0 - δ/2) (x0 + δ/2) y0) in H7 as H18; auto.
        destruct H18 as [x'[H18 H18']]. apply Classifier1. exists x'. apply Classifier2. 
        rewrite <- H18'. apply x_fx_T; auto. apply H1. apply Classifier1. 
        apply Abs_R. lra. lra. 
      * intros. apply H16; auto. apply Classifier1. applyClassifier1 H17. destruct H17.
        split. left; auto. left; auto. apply Classifier1. applyClassifier1 H18. 
        destruct H18. split. left; auto. left; auto.
    + lra.
Qed.

Theorem Theorem5_7 : ∀ f g x0 y0, Inverse_Function f g -> [x0, y0] ∈ f
  -> (∃ δ, δ > 0 /\ U(x0; δ) ⊂ dom[f]
    /\ ContinuousOpen  f (x0 - δ) (x0 + δ)
    /\ DStrictlyMonotonicFun f U(x0; δ))
  -> Derivative f x0 (f’[x0]) -> f’[x0] <> 0 -> Derivative f﹣¹ y0 (1/f’[x0]).
Proof.
  intros f g x0 y0 H1 H2' H3 H4 H5. destruct H3 as [δ[H3[H7[H8 H8']]]].
  apply (Lemma5_7 f g x0 δ) in H1 as H1'; auto. 
  destruct H1' as [a[b[L1[L2[L3 L4]]]]]. red in H1. pose proof H1 as h1.
  destruct H1 as [[H1 H1']_]. assert (J1 : x0 - δ < x0 < x0 + δ). lra.
  assert (J1' :x0 ∈ U(x0; δ)). { apply Classifier1. rewrite Abs_ge; lra. }
  assert (K2 : y0 ∈ \( a, b \)).
  { apply Classifier1. red in H8. apply H8 in J1 as H. destruct H as [K1 K2]. 
    red in K2. 
    assert (Q1 :(x0 - δ/2)∈ U(x0; δ)).
    { apply Classifier1.  replace (x0 - δ/2 - x0) with (-(δ/2)).
       rewrite <- Abs_eq_neg. rewrite Abs_gt; lra. lra. }
    assert (Q2: (x0 + δ/2)∈ U(x0; δ)).
    { apply Classifier1. replace (x0+δ/2-x0) with (δ/2). rewrite Abs_gt; lra. lra. }
    assert (H2: f[x0] = y0). { apply f_x_T; auto. }
    assert ([y0, x0] ∈ f ﹣¹). { apply Classifier1. exists y0,x0. split; auto. }
    apply f_x_T in H; auto. red in H8'. destruct H8'.  
    - red in H0. destruct H0 as [H14[K2' K3]].
      apply (K3 (x0 - δ/2) x0) in Q1 as H0'; auto. 
      apply (K3 x0 (x0 + δ/2)) in Q2 as H'; auto. unfold Rbasic_fun.Rmin in L1. 
      destruct Rle_dec in L1. rewrite L1. rewrite <- H2. split; auto.
      unfold Rbasic_fun.Rmax in L2; destruct Rle_dec in L2; rewrite L2; auto;
      lra. unfold Rbasic_fun.Rmax in L2; destruct Rle_dec in L2; rewrite L2; 
      auto; lra. lra. lra.
    - red in H0. destruct H0 as [H14[K2' K3]]. 
      apply (K3 (x0 - δ/2) x0) in Q1 as H0'; auto. 
      apply (K3 x0 (x0 + δ/2)) in Q2 as H'; auto. unfold Rbasic_fun.Rmin in L1. 
      destruct Rle_dec in L1. rewrite L1. rewrite <- H2.  split; auto. lra.
      unfold Rbasic_fun.Rmax in L2; destruct Rle_dec in L2; rewrite L2; auto;
      lra. unfold Rbasic_fun.Rmax in L2; destruct Rle_dec in L2; rewrite L2; 
      auto; lra. lra. lra. }
  apply L4 in K2 as H. destruct H as [H' H'']. 
  apply (EquaContinuous f ﹣¹ y0) in H'. red in H'. destruct H' as [H0' H].   
  red in H8. apply H8 in J1 as H3'. apply (EquaContinuous f x0) in H3'.
  red in H3'. destruct H3' as [H3' H'].
  apply (EquaDerivative (f﹣¹) y0 ((1/f’[ x0]))); auto.
  apply (EquaDerivative f x0 (f’[x0])) in H4. red in H4. 
  destruct H4 as [_[H4 H9]].
  assert (K1 : ∀ x, \{\ λ h y, y = (f[x0 + h] - f[x0])/h \}\ [x] 
    = (f[x0 + x] - f[x0])/x). { intros. rewrite FunValue; auto. }
  assert (H9': limit \{\ λ h y,y = h/(f[x0 + h] - f[x0]) \}\ 0 (1/f’[x0])). 
  { apply (Lemma3_7d \{\ λ h y,y = (f[x0 + h] - f[x0])/h \}\ 0 (f’[ x0])) in H9; 
    auto. unfold limit. unfold limit in H9. destruct H9 as [I1[δ'[I2[I3 I4]]]]. 
    assert (L7 : Function \{\ λ h y, y = h/(f[x0 + h] - f[x0]) \}\). 
    { red; intros. applyClassifier2 H0; applyClassifier2 H2. subst; auto. } 
    split; auto. exists δ'. split; auto. split. intros z H6. apply Classifier1. 
    exists (z/(f[x0 + z] - f[x0])). apply Classifier2; auto. intros. 
    apply I4 in H0 as H2. clear I4. destruct H2 as [δ''[[J0' J1'']J2]].
    pose proof (Examp3 δ' δ δ''). apply H2 in I2 as I2'; auto. clear H2.
    destruct I2' as [δ0[J3[J4[J5 J6]]]]. exists δ0. split; auto. intros.
    assert (0 < ∣(x - 0)∣ < δ''). lra. apply J2 in H6. clear J2. 
    assert ((1 /// \{\ λ h y,y = (f[x0 + h] - f[x0])/h \}\) [x] 
      = 1/((f[x0 + x] - f [x0])/x)).
    { apply f_x_T; auto. apply Classifier2; auto. split. apply Classifier1. 
      exists ((f[x0 + x] - f[x0])/x). apply Classifier2; auto.
      assert (\{\ λ h y, y = (f[x0 + h] - f [x0])/h \}\ [x] 
        = (f[x0 + x] - f[x0])/x). { rewrite FunValue; auto. } split.  
      - rewrite H9. assert (0 < ∣(x - 0)∣ < δ). lra.
        assert ((x0 + x) ∈ (U(x0; δ))).
        { apply Classifier1. replace (x0 + x - x0) with x. rewrite Rminus_0_r in H10.
          lra. lra. } red in H8'. destruct H8'. 
        + red in H12. destruct H12 as [_[_ H12]]. rewrite Rminus_0_r in H2.
          destruct H2. apply Abs_not_eq_0 in H2. unfold Rdiv. 
          apply Rmult_integral_contrapositive. split.
          * pose proof (Rge_lt x 0). destruct H14.
            -- destruct H14. apply (H12 x0 (x0 + x)) in J1'; auto. lra. lra.
               rewrite H14 in H2. lra.
            -- apply (H12 (x0 + x) x0) in H11; auto. lra. lra.
          * apply Rinv_neq_0_compat; auto.
        + red in H12. destruct H12 as [_[_ H16]]. rewrite Rminus_0_r in H2.
          destruct H2. apply Abs_not_eq_0 in H2. unfold Rdiv. 
          apply Rmult_integral_contrapositive. split.
          * pose proof (Rge_lt x 0). destruct H13.
            -- destruct H13. apply (H16 x0 (x0 + x)) in J1'; auto. lra. lra.
               rewrite H13 in H6. lra.
             -- apply (H16 (x0 + x) x0) in H11; auto. lra. lra.
          * apply Rinv_neq_0_compat; auto. 
      - rewrite H9. lra. }
    rewrite H9 in H6. 
    assert (\{\ λ h y, y = h/(f[x0 + h] - f[x0]) \}\ [x] 
      = (x/(f[x0 + x] - f[x0]))). { rewrite FunValue; auto. } rewrite H10.
    assert ((1/(((f[x0 + x] - (f[x0]))/x)) = x/(f[x0 + x] - f[x0]))).
    { unfold Rdiv. rewrite Rmult_1_l.
      rewrite (Rinv_mult (f[x0 + x] - f[x0]) (/x)). 
      rewrite (Rinv_inv x). apply Rmult_comm. }
    rewrite H11 in H6. replace (/f’[x0]) with (1/f’[ x0]) in H6. auto. lra. }
  red. unfold limit in H9'. split; auto.
  assert (K3 : ∃ δ', δ' > 0 /\ U(y0; δ') ⊂ \( a, b \)).
  { exists (Rbasic_fun.Rmin ∣(y0 - a)∣ ∣(b -y0)∣). unfold Rbasic_fun.Rmin. 
    destruct Rle_dec. pose proof (Abs_Rge0 (y0 - a)). split. destruct H0; auto.
    apply <- Abs_eq_0 in H0. apply Rminus_diag_uniq in H0. rewrite H0 in K2.
    applyClassifier1 K2. destruct K2. lra. intros z H6'. applyClassifier1 H6'. 
    apply Classifier1. split.
     - applyClassifier1 K2. destruct K2 as [K2 K2']. 
       assert (H13 : ∣(y0 - a)∣ = y0 - a). { rewrite Abs_ge; lra. } 
       rewrite H13 in H6'. clear H13. pose proof (Rge_lt (z - y0) 0). destruct H2. 
       + apply (Rminus_ge z y0) in H2. apply (Rge_gt_trans (z) (y0) (a)); auto.
       + assert (∣(z - y0)∣ = y0 - z). rewrite Abs_lt; lra. rewrite H6 in H6'. 
         lra.
     - applyClassifier1 K2. destruct K2 as [K2 K2']. 
       assert (∣(z - y0)∣ < ∣(b - y0)∣). lra. assert (∣(b - y0)∣ = b - y0). 
       apply Abs_ge; lra. rewrite H6 in H2. pose proof (Rge_lt (z - y0) 0). 
       destruct H10.
       + assert (∣(z-y0)∣ = z-y0). rewrite Abs_ge; lra. rewrite H11 in H2. lra.
       + apply (Rminus_lt z y0) in H10. apply (Rlt_trans (z) (y0) (b)); auto.
     - apply Rnot_le_lt in n. split. pose proof (Abs_Rge0 (b - y0)). destruct H0; 
       auto. apply <- Abs_eq_0 in H0. apply Rminus_diag_uniq in H0. 
       rewrite H0 in K2. applyClassifier1 K2. destruct K2. lra. intros z H6'.
       applyClassifier1 H6'. apply Classifier1. split. applyClassifier1 K2. 
       destruct K2 as [K2 K2']. assert (∣(b - y0)∣ = b - y0).
       { rewrite Abs_ge; lra. } 
       rewrite H0 in H6'. pose proof (Rge_lt (z - y0) 0). destruct H2. 
       + apply (Rminus_ge z y0) in H2. apply (Rge_gt_trans (z) (y0) (a)); auto.
       + assert (∣(z - y0)∣ = y0 - z). rewrite Abs_lt; lra. assert (y0 > a). 
         lra. assert(∣(y0 - a)∣ = y0 - a). apply Abs_ge; lra. 
         assert (∣(z - y0)∣ < ∣(y0 - a)∣). lra. rewrite H11 in H12. 
         rewrite H6 in H12. lra.
       + applyClassifier1 K2. destruct K2 as [K2 K2']. assert (∣(b - y0)∣ = b - y0). 
         apply Abs_ge; lra. rewrite H0 in H6'. pose proof (Rge_lt (z - y0) 0).
         destruct H2. assert (∣(z - y0)∣ = z - y0). rewrite Abs_ge; lra. 
         rewrite H6 in H6'. lra. apply (Rminus_lt z y0) in H2.
         apply (Rlt_trans (z) (y0) (b)); auto. }
  destruct K3 as [δ'[K3 K4]]. split. exists δ'. split; auto. unfold Contain in *.
  intros. apply L3. apply K4; auto. unfold limit in H. unfold limit in H'. red. 
  split. unfold Function. intros. applyClassifier2 H0. applyClassifier2 H2; rewrite H2; 
  auto. destruct H9' as [K5[δ1[K6[K7 K8]]]]. exists δ1. split; auto. split. 
  - intros z K9. apply Classifier1. exists (((f ﹣¹)[y0 + z] - (f ﹣¹)[y0])/z).
    apply Classifier2; auto.
  - intros. apply K8 in H0 as K8'. destruct K8' as [δ1'[K9 K10]].
    destruct K9 as [K9 K9']. destruct H as [H Q4]. destruct Q4 as [δ2[Q4[Q5 Q6]]].
    destruct H' as [J0'[δ3[J2 [J3 J4]]]]. apply Q6 in K9 as Q6'.
    apply J4 in K6 as J4'. destruct J4' as [δ3'[[J5 J7]J6]]. apply Q6 in J5 as J5'. 
    destruct Q6' as [δ2'[[Q7' Q6']Q7]]. destruct J5' as [δ2''[[J7' J6']J8]].
    pose proof (Examp3 δ1' δ' δ2' δ2'') as H13. pose proof K9 as H13'.
    apply H13 in H13'; auto. clear H13. 
    destruct H13' as [δ0[H13[H14[H15[H16 H17]]]]]. exists δ0. split; auto. 
    split; auto. lra. intros y1 H13'. assert (0 < ∣(y1 - 0)∣ < δ2'). lra.
    assert (L5 : 0 < ∣(y1 - 0)∣ < δ2''). lra. apply Q7 in H2 as Q7''. 
    apply J8 in L5 as L5'.   
    assert (K11 : ∀ y1, \{\ λ δx δy, δy = (f ﹣¹)[y0 + δx] - (f ﹣¹)[y0] \}\ [y1] 
      = (f ﹣¹)[y0 + y1] - (f ﹣¹)[y0]). 
    { intros. apply f_x_T; auto. apply Classifier2; auto. } 
    rewrite K11 in Q7''.  rewrite K11 in L5'. rewrite Rminus_0_r in Q7''. 
    rewrite Rminus_0_r in L5'.
    assert (H19 : ∃ δx, δx = (f ﹣¹)[y0 + y1] - (f ﹣¹)[y0]).
    { exists ((f ﹣¹)[y0 + y1] - (f ﹣¹)[y0]); auto. } destruct H19 as [δx].   
    assert (H20 : δx <> 0). 
    { assert (0 < ∣(y1 - 0)∣ < δ'). lra. red in H1'. 
      assert ((y0 + y1) ∈ U(y0; δ')). apply Classifier1. 
      replace (y0 + y1 - y0) with (y1 - 0); lra.
      assert ((y0 + y1) ∈ \( a, b \)). { apply K4; auto. } 
      red in H''. destruct H'' as [H''|H'']; red in H''; 
      destruct H'' as [_[_ H'']]; destruct H10; clear Q6 J4 K8 K10; 
      rewrite Rminus_0_r in H18; apply Abs_not_eq_0 in H10;
      apply Rdichotomy in H10; destruct H10. apply (H''(y0 + y1) y0) in H12; 
      auto; lra. apply (H'' y0 (y0 + y1)) in K2; auto; lra.
      apply (H''(y0 + y1) y0) in H12; auto; lra. apply (H'' y0 (y0 + y1)) in K2; 
      auto; lra. } rewrite <- H6 in Q7''. rewrite <- H6 in L5'.
    assert (H21 : 0 < ∣(δx - 0)∣ < δ1').
    { rewrite Rminus_0_r. split; auto. apply Abs_not_eq_0; auto. } 
    apply K10 in H21.
    assert (H21' : 0 < ∣(δx - 0)∣ < δ3').
    { rewrite Rminus_0_r. split; auto. apply Abs_not_eq_0; auto. }
    apply J6 in H21'. clear K10. clear J6.
    assert (H22 : ∀ δx, \{\ λ h y, y = h/(f[x0 + h] - f[x0]) \}\ [δx] 
      = δx/(f[x0 + δx] - f[x0])). 
    { intros. apply f_x_T; auto. apply Classifier2; auto. } rewrite H22 in H21. 
    assert (H23: \{\ λ h y,y = ((f ﹣¹)[y0 + h] - (f ﹣¹)[y0])/h \}\ [y1] 
      = ((f ﹣¹)[y0 + y1] - (f ﹣¹)[y0])/y1). { rewrite FunValue; auto. }
    rewrite H23.
    assert (H24 : ∀δx, \{\ λ δx δy, δy = f[x0 + δx] - f[x0] \}\ [δx] 
      = f[x0 + δx] - f[x0]). { intros. apply f_x_T; auto. apply Classifier2; auto. } 
    rewrite H24 in H21'. clear H23 H24 H22. rewrite <- H6.
    assert (H22 : ∃ δy, δy = f[x0 + δx] - f[x0]).
    { exists (f[x0 + δx] - f[x0]); auto. } destruct H22 as [δy]. 
    assert (H23 : δy = y1).
    { rewrite H10. rewrite H6.
      assert((f ﹣¹)[y0] = x0). { apply f_x_T; auto. apply Classifier2; auto. }
      rewrite H11. rewrite Rplus_comm.   
      replace ((f ﹣¹)[y0 + y1] - x0 + x0) with (f ﹣¹)[y0 + y1]. 
      assert (f[(f ﹣¹)[y0 + y1]] = y0 + y1). 
      { assert (y0 + y1 ∈ dom[ f ﹣¹]). apply L3. apply K4. apply Classifier1; 
        replace (y0 + y1 - y0) with y1; destruct H13'; rewrite Rminus_0_r in H18; 
        lra. destruct h1. rewrite <- H19. apply (Inverse_P3 f g); auto. 
        split; auto. rewrite H19; auto. }
      rewrite H12. assert(f[x0] = y0). { apply f_x_T; auto. } 
      rewrite H18. lra. lra. }
    rewrite <- H10 in H21. rewrite <- H23; auto.
Qed.

(* 复合函数的导数引理 *)
Lemma Lemma5_8a : ∀ f x0, Derivable f x0 -> Function f 
  /\ (∃ δ, δ > 0 /\ U(x0; δ) ⊂ dom[f] 
  /\ (∃ h, Continuous h x0 /\ ∀ x, x ∈ U(x0; δ) 
  -> f[x] - f[x0] = h[x] * (x - x0) /\ h[x0] = f’[x0])).
Proof.
  intros. split; intros. 
  - unfold Derivable in H. destruct H as [y0'].
    apply Corollary_DerivativeValue_a in H as H7. unfold Derivative in H. 
    destruct H as [H[H1 H2]]. auto. 
  - red in H. destruct H as [y0']. apply Corollary_DerivativeValue_a in H as H7.
    unfold Derivative in H. destruct H as [H[H1 H2]]. destruct H1 as [δ[H1 J3]].
    unfold limit in H2. destruct H2 as [H2[δ' [H3 [H4 H5]]]]. exists δ. 
    split; auto. split; auto.
    assert (∃ h, h = \{\ λ x y, x = x0 /\ y = y0' \/ x ∈ Uº(x0; δ)
      /\ y = (f[x] - f[x0])/(x - x0) \}\).
    { exists \{\ λ x y, x = x0 /\ y = y0' \/ x ∈ Uº(x0; δ)
        /\ y = (f[x] - f[x0])/(x - x0) \}\. auto. }
    destruct H0 as [h]. exists h. 
    assert (K1 :[x0, y0'] ∈ h). { rewrite H0. apply Classifier2. left. split; auto. }
    assert (Function h). 
    { rewrite H0. unfold Function. intros. applyClassifier2 H6. applyClassifier2 H8. 
      destruct H6 as [[H6 H12]|[H6 H12]]; destruct H8 as [[H8 H13]|[H8 H13]]. 
      rewrite H13; auto. applyClassifier1 H8. rewrite H6 in H8. destruct H8. 
      rewrite Rminus_diag_eq in H8. rewrite Abs_ge in H8. lra. right; auto. auto.
      applyClassifier1 H6. rewrite H8 in H6. destruct H6. rewrite Rminus_diag_eq in H6.
      rewrite Abs_ge in H6. lra. right; auto. auto. rewrite H13. auto. }
    assert (h[x0] = y0'). 
    { apply f_x_T. auto. rewrite H0. apply Classifier2. left. split; auto.  }
    repeat split; auto.
    + apply Classifier1. exists y0'. auto.
    + exists δ. split; auto. split. intros z H11. apply Classifier1. 
      exists ((f[z] - f[x0])/(z - x0)). rewrite H0. apply Classifier2. right.
      split; auto. intros. apply H5 in H9. destruct H9 as [δ2[H9 H12]].
      pose proof (Examp1 δ2 δ); auto. destruct H9 as [H9 K2]. apply H10 in H9; 
      auto. clear H10. destruct H9 as [δ3[K3[K4 K5]]]. exists δ3. split; auto. 
      intros. assert (0 < ∣(x - x0)∣ < δ2). lra. apply H12 in H10 as H14. 
      assert (\{\ λ x1 y,y = (f[x1] - f[x0])/(x1 - x0) \}\ [x] 
        = (f[x] - f[x0])/(x - x0) ). { apply f_x_T; auto. apply Classifier2; auto. }
      rewrite H11 in H14.  
      assert (h[x] = (f[x] - f[x0])/(x - x0)).
      { apply f_x_T; auto. rewrite H0. apply Classifier2. right. split; auto.
        apply Classifier1; auto. lra. } rewrite H13. rewrite H8. auto.
    + applyClassifier1 H9. assert (H11: ∣(x - x0)∣ >= 0). { apply Abs_Rge0. } 
      destruct H11.
      * apply Abs_not_eq_0 in H10 as J2; apply Rinv_neq_0_compat in J2 as H12.  
        apply (Rmult_eq_reg_r (/(x - x0))); auto. rewrite Rmult_assoc.
        rewrite (Rinv_r (x - x0)); auto. rewrite Rmult_1_r.   
        assert (h[x] = (f[x] - f[x0])/(x - x0)).
        { apply f_x_T; auto. rewrite H0. apply Classifier2. right. split; auto.
          apply Classifier1; auto. } rewrite H11; auto.
        * destruct (classic (x = x0)). rewrite H11. lra. 
          apply Rminus_eq_contra in H11. apply Abs_not_eq_0 in H11. lra.
    + rewrite H7; auto.
Qed.

Lemma Lemma5_8b : ∀ f h x0, Function f /\ (∃ δ, δ > 0 /\ U(x0; δ) ⊂ dom[f] 
  /\ (Continuous h x0 /\ ∀x, x ∈ U(x0; δ) -> f[x] - f[x0] = h[x] * (x - x0))) 
  -> Derivative f x0 h[x0].
Proof. 
  intros. destruct H as [H1 H2]. destruct H2 as [δ[H2[H3[H4 H5]]]]. 
  unfold Derivative. split; auto.  
  assert (H9: Function \{\ λ x y,y = (f[x] - f[x0])/(x - x0) \}\).
  { unfold Function. intros. applyClassifier2 H0. applyClassifier2 H. rewrite H; auto. }
  unfold Continuous in H4. destruct H4 as [H4 H6]. split.
  + exists δ; split; auto.
  + red in H6. red. destruct H6 as [H6[δ'[H7[H8 H10]]]]. split; auto. exists δ'. 
    split; auto. split.
    * intros x I1. apply Classifier1. exists ((f[x] - f[x0])/(x - x0)). 
      apply Classifier2. auto.
    * intros. pose proof H as H'. apply H10 in H'. destruct H' as [δ1[H' H'']]. 
      destruct H' as [H' H0]. pose proof (Examp2 δ δ' δ1). pose proof H2 as H2'. 
      apply H11 in H2'; auto. destruct H2' as [δ2[H12[H13[H14 H15]]]]. exists δ2. 
      split. auto. intros.
      assert (0 < ∣(x - x0)∣ < δ1).
      { split. lra. destruct H16. apply (Rlt_trans (∣(x - x0)∣) δ2 δ1); auto. }
      apply H'' in H17. 
      assert (\{\ λ x1 y, y = (f[x1] - f[x0])/(x1 - x0) \}\ [x]
        = (f[x] - f[x0])/(x - x0)). { apply f_x_T; auto. apply Classifier2. auto. }
      rewrite H18. clear H18.
      assert (x ∈ U(x0; δ)). { apply Classifier1. destruct H16. lra. }
      apply H5 in H18.
      apply (Rmult_eq_compat_r (/(x - x0)) (f[x] - f[x0]) (h[x] * (x - x0))) in H18.
      assert ((f[x] - f[x0]) * /(x - x0) = (f[x] - f[x0])/(x - x0)). lra. 
      rewrite H19 in H18. assert (h[x] * (x - x0) * /(x - x0) = h[x]).
      apply (Rinv_r_simpl_l (x - x0) (h[x])). destruct H16.
      apply Abs_not_eq_0 in H16. auto. rewrite H20 in H18. rewrite H18. apply H17.
Qed.

(* 引理 复合函数及乘法的连续性 *)
Lemma Lemma5_8c : ∀ F Φ H φ x0 u0, Continuous Φ x0 -> φ[x0] = u0 
  -> Continuous F u0 -> Continuous φ x0 -> H = \{\ λ x y,y = F[φ[x]] * Φ[x] \}\ 
  -> Continuous H x0.
Proof. 
  intros. assert(Continuous (F ◦ φ) x0). apply (Theorem4_5 _ _ _ u0); auto.
  assert (K1 : Function H).
  { rewrite H4. red; intros. applyClassifier2 H6; applyClassifier2 H7. subst; auto. } 
  assert (H12 : Function ((F ◦ φ) \* Φ)).
  { unfold Function. intros x y z I1 I2. applyClassifier2 I1. applyClassifier2 I2.
    destruct I2 as [I2 [I3 I4]]. rewrite I4. apply I1. }
  assert(Continuous ((F ◦ φ) \* Φ) x0). { apply Theorem4_4c; auto. }
  unfold Continuous in *. split. 
  - apply Classifier1. exists (F[φ[x0]] * Φ[x0]). rewrite H4. apply Classifier2; auto. 
  - destruct H6 as [H9 I1]. unfold limit in I1. split; auto. 
    destruct I1 as [I1[δ1[I4[I5 I6]]]]. exists δ1. split; auto. split.
      + red. intros. apply Classifier1. rewrite H4. exists (F[φ[z]] * Φ[z]).
        apply Classifier2; auto.
      + intros. apply I6 in H6. destruct H6 as [δ[]]. exists δ. split; auto.
        intros. assert(H[x] = F[φ[x]] * Φ[x]). rewrite H4. rewrite FunValue; auto.
        assert(H[x0] = F[φ[x0]] * Φ[x0]). rewrite H4. rewrite FunValue; auto. 
        apply H7 in H8 as H13. destruct H2 as [_[H2 _]]. destruct H3 as [_[H3 _]].    
        assert(((F ◦ φ) \* Φ)[x] = F[φ[x]] * Φ[x]).
        { assert (x ∈ Uº(x0; δ1)). { apply Classifier1. lra. } red in I5. 
          apply I5 in H14. applyClassifier1 H14. destruct H14 as [y]. 
          applyClassifier2 H14. destruct H14 as [H14[]]. apply f_x_T; auto.
          apply Classifier2. repeat split; auto.
          rewrite (Comp_Fun_P3 F φ); auto. }
        assert(((F ◦ φ) \* Φ)[x0] = F[φ[x0]] * Φ[x0]).
        { apply f_x_T; auto. apply Classifier2. repeat split; try tauto. 
          rewrite (Comp_Fun_P3 F φ); try tauto. }
        rewrite H14, H15 in H13. rewrite H10, H11; auto.
Qed.

(* 复合函数求导 *)
Theorem Theorem5_8 : ∀ f φ x0 u0, Derivable φ x0 -> φ[x0] = u0 
  -> Derivable f u0 -> Derivative (f ◦ φ) x0 (f’[u0] * φ’[x0]).
Proof.  
  intros. pose proof H as H'. apply Lemma5_8a in H. 
  destruct H as [H3[δ[H4[H5[Φ[H6 H7]]]]]]. pose proof H1 as H1'. 
  apply Lemma5_8a in H1. destruct H1 as [H8[δ'[H9[H10[F[H11 H12]]]]]].
  apply Theorem5_1 in H' as J1. apply Theorem5_1 in H1' as J2. red in J1, J2.
  assert (∃ H, H = \{\ λ x y, y = F [φ[x]] * Φ[x] \}\).
  { exists (\{\ λ x1 y, y = F[φ[x1]] * Φ[x1] \}\). auto. }
  destruct H as [H I2].
  assert (Continuous H x0). { apply (Lemma5_8c F Φ H φ x0 u0); auto. } 
  assert(I1: x0 ∈ dom[f ◦ φ]). 
  { rewrite (Comp_Fun_P2 f φ); auto. apply Classifier1. split; try tauto.
    apply Classifier1. rewrite H0. tauto. }
  assert (Function (f ◦ φ) /\ ∃ δ, δ > 0 /\ U(x0; δ) ⊂ dom[(f ◦ φ)]
    /\ (Continuous H x0 /\ ∀x, x ∈ U(x0; δ) -> (f ◦ φ)[x] - (f ◦ φ)[x0]
      = H [x] * (x - x0))).
  { split.
    - apply Comp_Fun_P1; auto.
    - destruct J1 as [J1[J4[δ1[J5[J6 J7]]]]]. 
      destruct J2 as [J2[J8[δ2[J9[J10 J11]]]]]. 
      apply (Examp1 δ2 δ') in J9 as J9'; auto. destruct J9' as [δ2'[J9'[J12 J13]]].
      apply J7 in J9' as J7'. destruct J7' as [δ3[J7' J14]].
      destruct J7' as [L1 L2]. apply (Examp1 δ3 δ) in L1 as L1'; auto.
      destruct L1' as [δ4[L3[L4 L5]]]. exists δ4. split. lra. 
      assert(I3: ∀x, x ∈ U(x0; δ4) -> x ∈ U(x0; δ) /\ φ[x] ∈ U(u0; δ')).
      { intros. applyClassifier1 H2. destruct(classic (x = x0)). split.
        - apply Classifier1. subst x0. rewrite Abs_ge; lra.
        - apply Classifier1. rewrite H13. rewrite H0. rewrite Abs_ge; lra.
        - split; apply Classifier1. lra. 
          assert(∣(φ[x] - φ[x0])∣ < δ2'). 
          { apply J14. split; auto. apply Abs_not_eq_0; lra. lra. } 
          rewrite <-H0. lra. }
      assert (U(x0; δ4) ⊂ dom[f ◦ φ]).
      { intros x K1. rewrite (Comp_Fun_P2 f φ); auto. apply Classifier1.
        split. destruct(classic (φ[x] = φ[x0])).
        + apply Classifier1. rewrite H2. rewrite H0; auto.
        + apply Classifier1.  apply J10. apply Classifier1. rewrite <- H0. split. 
          apply Abs_not_eq_0; lra. destruct(classic (x = x0)).
          -- rewrite H13. rewrite Abs_ge; lra.
          -- assert(∣(φ[x] - φ[x0])∣ < δ2'). 
             { apply J14. applyClassifier1 K1. split; auto. apply Abs_not_eq_0; lra.
               lra. } lra.
        + destruct (classic (x = x0)). rewrite H2; auto. apply J6. apply Classifier1.
          applyClassifier1 K1. split. apply Abs_not_eq_0; lra. lra. }
      split; auto. split; auto.
      + intros. repeat rewrite (Comp_Fun_P3 f φ); auto.
        apply I3 in H13 as []. apply H12 in H14 as []. apply H7 in H13 as [].
        rewrite H0,H14. rewrite <- H0,H13.
        assert (\{\ λ x y, y = F[φ[x]] * Φ[x] \}\ [x] = F[φ[x]] * Φ[x]).
        { rewrite FunValue; auto. } rewrite I2, H17. lra. }
  apply (Lemma5_8b (f ◦ φ) H x0) in H2. rewrite I2 in H2. 
  assert (\{\ λ x y, y = F[φ[x]] * Φ[x] \}\ [x0] = F[φ[x0]] * Φ[x0]). 
  { rewrite FunValue; auto. } rewrite H13 in H2.
  assert (Function f /\ (∃ δ, δ > 0 /\ U(u0; δ) ⊂ dom[ f]
    /\ (Continuous F u0 /\ ∀ u, u ∈ U(u0; δ) -> f[u] - f[u0] = F[u] * (u-u0)))).
  { split; auto. exists δ'. split; auto. split; auto. split; auto. intros.
    apply H12 in H14. destruct H14. auto. }
  apply (Lemma5_8b f F u0) in H14.
  assert (Function φ /\ (∃ δ, δ > 0 /\ U(x0; δ) ⊂ dom[φ]
    /\ (Continuous Φ x0 /\ ∀ x, x ∈ U(x0; δ) -> φ[x] - φ[x0] = Φ[x] * (x-x0)))).
  { split; auto. exists δ. split; auto. split; auto. split; auto. intros.
    apply H7 in H15. destruct H15. auto. }
  apply (Lemma5_8b φ Φ x0) in H15. apply Corollary_DerivativeValue_a in H15.
  apply Corollary_DerivativeValue_a in H14.
  rewrite H15. rewrite H14. rewrite <- H0. auto.
Qed.

(* 定义指数运算 *)
Fixpoint PowR r n :=
  match n with
    | O => 1
    | S n => Rmult r (PowR r n)
  end.
Notation "r ^ n" := (PowR r n).

Fact PowR_Fact1 : ∀ x0 n k, x0^(n + k) = (x0^n) * (x0^k).
Proof.
  intros. generalize dependent n. induction k.
  - simpl. intros. rewrite Nat.add_0_r. rewrite Rmult_1_r. auto.
  - induction n. simpl. rewrite Rmult_1_l. auto. simpl. rewrite IHn. 
    rewrite <- Rmult_assoc. simpl. auto.
Qed.

Fact PowR_Fact2 : ∀ x0 k, x0^(2 * k) = (x0^2)^k.
Proof.
  intros. induction k.
  - simpl. auto.
  - simpl. rewrite Rmult_1_r.  simpl in IHk. rewrite Rmult_1_r in IHk.
    rewrite <-IHk. rewrite Nat.add_0_r. rewrite <-Nat.add_1_r.
    assert(x0^(k + k + 1) = x0^(k + k) * x0^1). { apply PowR_Fact1. }
    rewrite Nat.add_assoc,H. simpl. rewrite Rmult_1_r. rewrite <-Rmult_assoc. 
    rewrite <-Rmult_comm. rewrite <-Rmult_assoc. auto.
Qed.

Fact PowR_Fact3 : ∀ x0 k, x0 > 0 -> x0^k > 0.
Proof.
  intros. induction k. simpl. lra. simpl. apply Rmult_gt_0_compat; auto.
Qed.

Fact PowR_Fact4 : ∀ x0 y0 n, (x0^n) * (y0^n) = (x0 * y0)^n.
Proof.
  intros. generalize dependent n. induction n.
  - simpl. lra. 
  - simpl. rewrite <- IHn. field. 
Qed.

Fact PowR_Fact5 : ∀ n, (0 < n)%nat -> 0^n = 0.
Proof.
  intros. destruct n. elim (@ Nat.lt_irrefl 0); auto. simpl. rewrite Rmult_0_l; 
  auto.
Qed.

Fact PowR_Fact6 : ∀ x n, x^n = 0 -> x = 0.
Proof.
  intros. induction n. simpl in H. exfalso. lra. simpl in H. 
  apply Rmult_integral in H as []; auto.
Qed.

Fact PowR_Fact7 : ∀ x, 0 <= x^2.
Proof.
  intros. simpl. rewrite Rmult_1_r. destruct (Rle_or_lt 0 x). apply Rmult_le_pos; 
  auto. assert (0 <= -x) by lra. replace (x * x) with (-x * -x); [ |lra]. 
  apply Rmult_le_pos; auto.
Qed.

Fact PowR_Fact8 : ∀ x, x <> 0 <-> 0 < x^2.
Proof.
  split; intros. destruct (PowR_Fact7 x); auto. symmetry in H0.
  apply PowR_Fact6 in H0. contradiction. intro. rewrite H0 in H. simpl in H.
  rewrite Rmult_0_l in H. lra.
Qed.

(* 一些关于幂函数极限和导数的基本事实 *)
Fact EleFun_Fact1 : ∀ a n, Function \{\ λ x y, y = (x - a)^n \}\.
Proof.
  intros a n x1 y1 z1 I1 I2. applyClassifier2 I1; applyClassifier2 I2. rewrite I2. 
  assumption.
Qed.

Fact EleFun_Fact2 : ∀ a c n, Function \{\ λ x y, y = c * (x - a)^n \}\.
Proof.
  intros a c n x1 y1 z1 I1 I2. applyClassifier2 I1; applyClassifier2 I2. rewrite I2. 
  assumption.
Qed.

Fact EleFun_Fact3 : ∀ a x n, \{\ λ x y, y = (x - a)^n \}\ [x] = (x - a)^n.
Proof.
  intros a x n. apply f_x_T; try apply EleFun_Fact1. apply Classifier2. reflexivity.
Qed.

Fact EleFun_Fact4 : ∀ a c x n, \{\ λ x y, y = c*(x - a)^n \}\ [x] = c*(x - a)^n.
Proof.
  intros a c x n. apply f_x_T; try apply EleFun_Fact2. apply Classifier2. reflexivity.
Qed.

Fact EleFun_Fact5 : ∀ a, Function \{\ λ x y, y = x - a \}\.
Proof.
  intros a x1 y1 z1 I1 I2. applyClassifier2 I1; applyClassifier2 I2. rewrite I2. 
  assumption.
Qed.

Fact EleFun_Fact6 : ∀ a x, \{\ λ x y, y = x - a \}\ [x] = x - a.
Proof.
  intros a x. apply f_x_T; try apply EleFun_Fact5. apply Classifier2. reflexivity.
Qed.

Fact EleFun_Fact7 : ∀ a x0 n, limit \{\ λ x y, y = (x - a)^n \}\ x0 ((x0 - a)^n).
Proof.
  intros a x0 n. generalize dependent x0. induction n as [ | n IHn].
  - intro x0. split; try apply EleFun_Fact1. exists 2. split; try lra. split.
    + intros x H0. simpl. apply Classifier1. exists 1. apply Classifier2. reflexivity.
    + intros ε H0. exists 1. split; try lra. intros x H1. rewrite EleFun_Fact3.
      simpl. apply Abs_R. lra.
  - intros x0. simpl.
    assert (H0 : \{\ λ x y, y = (x - a) * (x - a)^n \}\ 
      = \{\ λ x y, y = x - a \}\ \* \{\ λ x y, y = (x - a)^n \}\).
    { apply AxiomI. intros [x y]. split; intros I1; applyClassifier2 I1; 
      apply Classifier2.
      - repeat split.
        + apply Classifier1. exists (x - a). apply Classifier2. reflexivity.
        + apply Classifier1. exists ((x - a)^n). apply Classifier2. reflexivity.
        + rewrite EleFun_Fact6. rewrite EleFun_Fact3. assumption.
      - destruct I1 as [I1[I2 I3]]. rewrite I3. rewrite EleFun_Fact6. 
        rewrite EleFun_Fact3. reflexivity. }
    rewrite H0. apply Theorem3_7c; auto. split; try apply EleFun_Fact5. exists 1.
    split; [lra | split].
    + intros x I1. apply Classifier1. exists (x - a). apply Classifier2. reflexivity.
    + intros ε I1. assert (I2 : 1 > 0). lra. generalize (Examp1 ε 1 I1 I2).
      intros [δ[I3[I4 I5]]]. exists δ. split; [lra | intros x I6].
      rewrite EleFun_Fact6. assert (I7 : x - a - (x0 - a) = x - x0). field. 
      rewrite I7. lra.
Qed.

Fact EleFun_Fact8 : ∀ a x0 n, Derivative \{\ λ x y, y = (x - a)^n \}\ x0 
  (INR n * ((x0 - a)^(n - 1))).
Proof.
  intros a x0 n. split; try apply EleFun_Fact1. split.
  - exists 1. split; try lra. intros x I1. apply Classifier1. exists ((x - a)^n). 
    apply Classifier2. reflexivity.
  - rewrite EleFun_Fact3.
    assert (H1 : \{\ λ x y, y 
        = (\{\ λ x1 y0, y0 = (x1 - a)^n \}\ [x] - (x0 - a) ^ n)/(x - x0) \}\
      = \{\ λ x y, y = ((x - a)^n - (x0 - a)^n)/(x - x0) \}\).
    { apply AxiomI. intros [x y]. split; intros I1; apply Classifier2; 
      applyClassifier2 I1.
      - rewrite EleFun_Fact3 in I1. assumption.
      - rewrite EleFun_Fact3. assumption. } rewrite H1. clear H1.
    assert (H0 : ∀ x0 n, Function \{\ λ x y, y 
      = ((x - a)^n - (x0 - a)^n)/(x - x0) \}\).
    { intros x1 n0. intros x2 y2 z2 I1 I2. applyClassifier2 I1; applyClassifier2 I2.
      rewrite I2. assumption. }
    induction n as [ | n IHn].
    + split; auto. exists 1. split; try lra; split.
      * intros x I1. simpl. apply Classifier1. exists ((1 - 1)/(x - x0)). 
        apply Classifier2. reflexivity.
      * intros ε I1. exists (1/2). split; try lra. intros x [I2 I3].
        apply Abs_not_eq_0 in I2.
        assert (I4 : \{\ λ x1 y, y = ((x1-a)^0-(x0-a)^0)/(x1-x0) \}\ [x] = 0).
        { apply f_x_T; auto. apply Classifier2.  simpl. field. assumption. }
        rewrite I4. simpl. apply Abs_R. lra.
    + assert (H1 : ∀ x, ((x - a)^(S n) - (x0 - a)^(S n))/(x - x0)
        = (x - a)^n*(x - x0)/(x - x0)+(x0 - a)*((x - a)^n - (x0 - a)^n)/(x - x0)).
      { intros x. simpl.
        assert (I1 : (x - a) * (x - a)^n - (x0 - a) * (x0 - a)^n
          = (x - a)^n * (x - x0) + (x0 - a) * ((x - a)^n - (x0 - a)^n)).
        field. rewrite I1. rewrite Rdiv_plus_distr. reflexivity. }
      assert (H2 : (INR (S n) * (x0 - a)^(S n - 1)) 
        = (x0 - a)^n + INR n * (x0 - a)^n).
      { rewrite S_INR. assert (I1 : (S n - 1 = n)%nat). 
        { simpl. lia. } rewrite I1. field. }
      rewrite H2. clear H2.
      assert (H2 : Function \{\ λ x y, y = (x - a)^n * (x - x0)/(x - x0) \}\).
      { intros x y z I1 I2. applyClassifier2 I1; applyClassifier2 I2. rewrite I2; 
        assumption. }
      assert (H3 : Function \{\ λ x y, y 
        = (x0 - a) * ((x - a)^n - (x0 - a)^n)/(x - x0) \}\).
      { intros x y z I1 I2. applyClassifier2 I1; applyClassifier2 I2. rewrite I2; 
        assumption. }
      assert (H4: ∀ x, \{\ λ x1 y0, y0 = (x1 - a)^n * (x1 - x0)/(x1 - x0) \}\ [x]
        = (x - a)^n * (x - x0)/(x - x0)).
      { intro x. apply f_x_T; auto. apply Classifier2. reflexivity. }
      assert (H5 : ∀ x, \{\ λ x1 y0, y0
          = (x0 - a) * ((x1 - a)^n - (x0 - a)^n)/(x1 - x0) \}\ [x] 
        = (x0 - a) * ((x - a)^n - (x0 - a)^n)/(x - x0)).
      { intro x. apply f_x_T; auto. apply Classifier2. reflexivity. }
      assert (H6 : \{\ λ x y, y = ((x - a)^(S n) - (x0 - a)^S n)/(x - x0) \}\
        = \{\ λ x y, y = (x - a)^n * (x - x0)/(x - x0) \}\ 
          \+ \{\ λ x y, y = (x0 - a) * ((x - a)^n - (x0 - a)^n)/(x - x0) \}\).
      { apply AxiomI. intros [x y]; split; intro I1; applyClassifier2 I1; 
        apply Classifier2.
        - repeat split.
          + apply Classifier1. exists ((x - a)^n * (x - x0)/(x - x0)). 
            apply Classifier2. reflexivity.
          + apply Classifier1. exists ((x0 - a) * ((x - a)^n - (x0 - a)^n)/(x - x0)).
            apply Classifier2. reflexivity.
          + rewrite H4; rewrite H5. rewrite I1. apply H1.
        - destruct I1 as [I1[I4 I5]]. rewrite H4 in I5. rewrite H5 in I5.
          rewrite I5. symmetry. apply H1. }
      rewrite H6. clear H6. apply Theorem3_7a.
      * generalize (EleFun_Fact7 a x0 n). unfold limit. intros [I2[δ'[I3[I4 I5]]]].
        split; auto. exists δ'. split; [assumption | split].
        -- intros x I1. apply Classifier1. exists ((x - a)^n * (x - x0)/(x - x0)).
           apply Classifier2. reflexivity.
        -- intros ε I1. apply I5 in I1 as I6. destruct I6 as [δ[I6 I7]]. 
           exists δ; split; [assumption | intros x I8]. apply I7 in I8 as I9.
           rewrite EleFun_Fact3 in I9. apply Examp4 in I8 as [I8 I10]. rewrite H4.
            assert (I11 : (x - a)^n * (x - x0)/(x - x0) = (x - a)^n). field; auto.
            rewrite I11. assumption.
      * assert (I1 : INR n * (x0 - a)^n = (x0 - a) * (INR n * (x0 - a)^(n - 1))).
        { destruct n.
          - simpl. field.
          - rewrite <- Rmult_assoc. rewrite (Rmult_comm (x0 - a) (INR (S n))).
            rewrite Rmult_assoc. simpl (S n - 1)%nat. rewrite Nat.sub_0_r. auto. }
        rewrite I1. clear I1. 
        assert (I1 : Function \{\ λ x y : R, y = x0 - a \}\).
        { intros x1 y1 z1 I1 I2. applyClassifier2 I1; applyClassifier2 I2. rewrite I2. 
          assumption. }
        assert (I2 : ∀ x, \{\ λ x y :R, y = x0 - a \}\ [x] = x0 - a).
        { intros x. apply f_x_T; auto. apply Classifier2. reflexivity. }
        assert (I3 : Function \{\ λ x y, y = ((x-a)^n - (x0-a)^n)/(x-x0) \}\).
        { intros x1 y1 z1 J1 J2. applyClassifier2 J1; applyClassifier2 J2. rewrite J2. 
          assumption. }
        assert (I4 : ∀ x, \{\ λ x y, y = ((x - a)^n - (x0 - a)^n)/(x - x0) \}\ [x]
          = ((x - a)^n - (x0 - a)^n)/(x - x0)).
        { intros x. apply f_x_T; auto. apply Classifier2. reflexivity. }
        assert (I5 : \{\λ x y, y = (x0 - a) * ((x - a)^n - (x0 - a)^n)/(x - x0)\}\
          = \{\ λ x y, y = x0 - a \}\
            \* \{\ λ x y, y = ((x - a)^n - (x0 - a)^n)/(x - x0) \}\).
        { apply AxiomI. intros [x y]; split; intro J1; applyClassifier2 J1; 
          apply Classifier2.
          - rewrite I4. rewrite I2. repeat split.
            + apply Classifier1. exists (x0 - a). apply Classifier2. reflexivity.
            + apply Classifier1. exists (((x - a)^n - (x0 - a)^n)/(x - x0)).
              apply Classifier2. reflexivity.
            + lra.
          - destruct J1 as [J1[J2 J3]]. rewrite I4 in J3. rewrite I2 in J3. lra. }
        rewrite I5. clear I5. apply Theorem3_7c; auto. split; auto. exists 2. 
        split; [lra | split].
        -- intros x J1. apply Classifier1. exists (x0 - a). apply Classifier2. 
           reflexivity.
        -- intros ε J1. exists 1. split; [lra | intros x J2]. rewrite I2. 
           apply Abs_R. lra.
Qed.

Fact EleFun_Fact9 : ∀ u c x0, Derivable u x0 
  -> Derivative \{\ λ x y, y = c * u[x] \}\ x0 (c * u’[x0]).
Proof.
  intros u c x0 [y H0]. apply Corollary_DerivativeValue_a in H0 as H1.
  rewrite H1. clear H1. split. red; intros. applyClassifier2 H; applyClassifier2 H1.
  subst; auto. destruct H0 as [H0[[δ'[H1 H2]] H3]]. split.
  - exists δ'. split; auto. intros x I1. apply Classifier1. exists (c * u[x]).
    apply Classifier2. reflexivity.
  - assert (H4 : Function \{\ λ x y0, y0 = (\{\ λ x1 y1, y1 = c * u[x1] \}\ [x] 
      - \{\ λ x1 y1, y1 = c * u[x1] \}\ [x0])/(x - x0) \}\ ).
    { intros x1 y1 z1 I1 I2. applyClassifier2 I1; applyClassifier2 I2. rewrite I2; 
      assumption. } split; auto. exists δ'. split; [assumption | split].
    + intros x I1. apply Classifier1. exists ((\{\ λ x1 y1, y1 = c * u[x1] \}\ [x] 
      - \{\ λ x1 y1, y1 = c * u[x1] \}\ [x0])/(x - x0)).
      apply Classifier2. reflexivity.
    + intros ε H5. unfold limit in H3. destruct H3 as [H3[δ1'[H6[H7 H8]]]].
      assert (H16 : ∀ x, \{\ λ x y0, y0 = (\{\ λ x1 y1, y1 = c * u[x1] \}\ [x] 
          - \{\ λ x1 y1, y1 = c * u[x1] \}\ [x0])/(x - x0) \}\ [x] 
        = (\{\ λ x1 y1, y1 = c * u[x1] \}\ [x] 
          - \{\ λ x1 y1, y1 = c * u[x1] \}\ [x0])/(x - x0)).
      { intros x. apply f_x_T; auto. apply Classifier2. reflexivity. }
      destruct classic with (P := c = 0) as [J0 | J0].
      * exists (δ'/2). split; [lra | intros x H9]. rewrite H16. 
        rewrite FunValue, FunValue. rewrite J0 in *. apply Examp4 in H9. 
        apply Abs_R. assert (I1 : (0 * u [x] - 0 * u[x0])/(x - x0) - 0 * y = 0).
        { field. apply H9. } rewrite I1. lra.
      * assert (J1 : ∣(c)∣ > 0). { apply Abs_not_eq_0. assumption. }
        assert (J2 : ε/∣(c)∣ > 0). { apply Rdiv_lt_0_compat; assumption. }
        apply H8 in J2 as H9. destruct H9 as [δ1[[H9 H10] H11]].
        generalize (Examp1 δ' δ1 H1 H9). intros [δ[H12[H13 H14]]]. exists δ. 
        split; [lra | intros x H15]. rewrite H16. clear H16. 
        rewrite FunValue, FunValue. assert (H16 : 0 < ∣(x - x0)∣ < δ1). lra.
        apply H11 in H16.
        assert (H17 : \{\ λ x y, y = (u[x] - u[x0])/(x - x0) \}\ [x] 
          = (u[x] - u[x0])/(x - x0)).
        { apply f_x_T; auto. apply Classifier2. reflexivity. }
        rewrite H17 in H16. apply Examp4 in H15.
        assert (H18 : (c * u[x] - c * u[x0])/(x - x0) - c * y 
          = c * ((u[x] - u[x0])/(x - x0) - y)). { field. apply H15. }
        rewrite H18. rewrite Abs_mult.
        apply Rmult_lt_compat_l with (r := ∣c∣) in H16; auto. 
        assert (H19 : ∣c∣ * (ε/∣c∣) = ε). { field. lra. }
        rewrite H19 in H16. assumption.
Qed.

Fact EleFun_Fact10 : ∀ a c x0 n, Derivative \{\ λ x y, y = c * (x - a)^n \}\ x0
  (c * INR n * (x0 - a)^(n - 1)).
Proof.
  intros a c x0 n.
  assert (H0 : ∃ u, u = \{\ λ x y, y = (x - a)^n \}\).
  { exists \{\ λ x y, y = (x - a)^n \}\. reflexivity. }
  destruct H0 as [u H0].
  assert (H1 : \{\ λ x y, y = c * (x - a)^n \}\ = \{\ λ x y, y = c * u[x] \}\).
  { rewrite H0. apply AxiomI. intros [x y]; split; intros I1; applyClassifier2 I1; 
    apply Classifier2.
    - rewrite EleFun_Fact3. assumption.
    - rewrite EleFun_Fact3 in I1. assumption. }
  rewrite H1. generalize (EleFun_Fact8 a x0 n). intro H2. rewrite <- H0 in H2.
  assert (H3 : c * INR n * (x0 - a)^(n - 1) = c * u’[x0]).
  { apply Corollary_DerivativeValue_a in H2 as H3. rewrite H3. field. }
  rewrite H3. apply EleFun_Fact9. exists (INR n * (x0 - a) ^ (n - 1)). assumption.
Qed.

Fact EleFun_Fact11 : ∀ f g x0 y0, Function g -> 
  (∃ δ, 0 < δ /\ (∀ x, x ∈ U(x0; δ) -> x ∈ dom[g] /\ f[x] = g[x]))
  -> Derivative f x0 y0 -> Derivative g x0 y0.
Proof.
  intros f g x0 y0 H0 [δ[H1 H2]] H3. split; [auto | split].
  - exists δ. split; auto. intros x I1. apply H2. assumption.
  - unfold limit. unfold Derivative in H3. destruct H3 as [H3[[δ'[I1 I2]]I3]].
    unfold limit in I3. destruct I3 as [I3[δ1'[I4[I5 I6]]]]. split.
    + intros x y z J1 J2. applyClassifier2 J1; applyClassifier2 J2. rewrite J2; assumption.
    + exists δ1'. split; [auto | split].
      * intros x J1. apply Classifier1. exists ((g[x] - g[x0])/(x - x0)).
        apply Classifier2. reflexivity.
      * intros ε J1. apply I6 in J1 as J2. destruct J2 as [δ1[[J2 J3]J4]].
        generalize (Examp1 δ δ1 H1 J2). intros [δ2[J5[J6 J7]]]. exists δ2. 
        split; try lra. intros x J8. assert (J9 : 0 < ∣(x - x0)∣ < δ1). lra.
        apply J4 in J9.
        assert (J10 : \{\ λ x y, y = (f[x] - f[x0])/(x - x0) \}\ [x]
          = (f[x] - f[x0])/(x - x0)).
        { apply f_x_T; auto. apply Classifier2. reflexivity. } 
        rewrite J10 in J9. clear J10.
        assert (J10 : \{\ λ x y, y = (g[x] - g[x0])/(x - x0) \}\ [x]
          = (g[x] - g[x0])/(x - x0)).
        { apply f_x_T.
          - intros x1 y1 z1 K1 K2. applyClassifier2 K1; applyClassifier2 K2.
            rewrite K2; assumption.
          - apply Classifier2. reflexivity. }
        rewrite J10. assert (J11 : x ∈ U(x0; δ)). { apply Classifier1. lra. }
        apply H2 in J11 as [J11 J12]. rewrite <- J12.
        assert (J13 : x0 ∈ U(x0; δ)). { apply Classifier1. apply Abs_R. lra. }
        apply H2 in J13 as [J14 J15]. rewrite <- J15. assumption.
Qed.

Fact EleFun_Fact12 : ∀ c, Function \{\ λ x y : R, y = c \}\.
Proof.
  intros c x y z I1 I2. applyClassifier2 I1; applyClassifier2 I2. rewrite I2; assumption.
Qed.

Fact EleFun_Fact13 : ∀ c x, \{\ λ x y : R, y = c \}\ [x] = c.
Proof.
  intros c x. apply f_x_T; try apply EleFun_Fact12. apply Classifier2. reflexivity.
Qed.

Fact EleFun_Fact14 : ∀ c x0, Derivative \{\ λ x y, y = c \}\ x0 0.
Proof.
  intros c x. split; [apply EleFun_Fact12 | split].
  - exists 1. split; [lra | intros x0 I1]. apply Classifier1. exists c.
    apply Classifier2. reflexivity.
  - unfold limit. split.
    + intros x1 y1 z1 I1 I2. applyClassifier2 I1; applyClassifier2 I2.
      rewrite I2; assumption.
    + exists 2. split; [lra | split].
      * intros x0 I1. apply Classifier1.
        exists ((\{\ λ _ y1 : R, y1 = c \}\ [x0] 
          - \{\ λ _ y1 : R, y1 = c \}\ [x])/(x0 - x)).
        apply Classifier2. reflexivity.
      * intros ε I1. exists 1. split; [lra | intros x0 I2].
        assert (I3 : \{\ λ x1 y, y = (\{\ λ _ y0 : R, y0 = c \}\ [x1]
          - \{\ λ _ y0 : R,y0 = c \}\ [x])/(x1 - x) \}\ [x0] = 0).
        { apply f_x_T.
          - intros x1 y1 z1 J1 J2. applyClassifier2 J1; applyClassifier2 J2.
            rewrite J2; assumption.
          - apply Classifier2. rewrite EleFun_Fact13. rewrite EleFun_Fact13.
            apply Examp4 in I2. field. apply I2. } rewrite I3. apply Abs_R. lra.
Qed.

Fact EleFun_Fact15 : ∀ c x0, limit \{\ λ _ y : R, y = c\}\ x0 c.
Proof.
  intros c x0. split.
  - apply EleFun_Fact12.
  - exists 2. split; [lra | split].
    + intros x H0. apply Classifier1. exists c. apply Classifier2. reflexivity.
    + intros ε H0. exists 1. split; [lra | intros x H1]. rewrite EleFun_Fact13. 
      apply Abs_R. lra.
Qed.

Fact EleFun_Fact16 : ∀ a c x0 n, limit
  \{\ λ x y, y = c * (x - a)^n \}\ x0 (c * (x0 - a)^n).
Proof.
  intros a c x0 n.
  assert (H0 : \{\ λ x y, y = c * (x - a)^n \}\ =
    \{\ λ x y, y = c \}\ \* \{\ λ x y, y = (x - a)^n \}\).
  { apply AxiomI. intros [x y];
    split; intro I1; applyClassifier2 I1; apply Classifier2.
    - repeat split.
      + apply Classifier1. exists c. apply Classifier2. reflexivity.
      + apply Classifier1. exists ((x - a) ^ n). apply Classifier2. reflexivity.
      + rewrite EleFun_Fact13. rewrite EleFun_Fact3. assumption.
    - destruct I1 as [I1[I2 I3]]. rewrite I3. rewrite EleFun_Fact13.
      rewrite EleFun_Fact3. reflexivity. }
  rewrite H0. apply Theorem3_7c. apply EleFun_Fact15. apply EleFun_Fact7.
Qed.


(* 高阶导函数 *)
Fixpoint dN f (n : nat) :=
  match n with
  | O => f
  | S m => \{\ λ x y, Derivative (dN f m) x y \}\
  end.

Corollary dN_Corollary_a : ∀ f (x0 : R) (n : nat), x0 ∈ dom[dN f n] ->
  (∀ k, (k < n)%nat -> ∃ δ, δ > 0 /\ U(x0; δ) ⊂ dom[dN f k]).
Proof.
  intros f x0 n. induction n as [ | n IHn].
  - simpl. intros H0 k H1. apply Nat.nlt_0_r in H1. contradiction.
  - intros H0 k H1. applyClassifier1 H0. destruct H0 as [y H0]. applyClassifier2 H0.
    destruct H0 as [H0[[δ'[H2 H3]]H4]]. assert (H5 : x0 ∈ dom[dN f n]). 
    { apply H3. apply Classifier1. apply Abs_R. lra. } generalize (IHn H5). 
    intros H6. assert (k < n \/ k = n)%nat as []; auto. lia.
    exists δ'. rewrite H. split; auto.
Qed.

Corollary dN_Corollary_b : ∀ f x0 n, x0 ∈ dom[dN f n]
  -> (∃ δ, δ > 0 /\ (∀ k, (k < n)%nat -> U(x0; δ) ⊂ dom[dN f k])).
Proof.
  intros f x0 n H0. induction n as [ | n IHn].
  - exists 1. split; [lra | intros k I1]. apply Nat.nlt_0_r in I1. contradiction.
  - apply dN_Corollary_a with (k := n) in H0 as I1; try apply Nat.lt_succ_diag_r.
    destruct I1 as [δ1[I1 I2]].
    assert (I3 : x0 ∈ dom[dN f n]).
    { apply I2. apply Classifier1. apply Abs_R. lra. }
    apply IHn in I3 as [δ2[I3 I4]]. generalize (Examp1 δ1 δ2 I1 I3).
    intros [δ[I5[I6 I7]]]. exists δ. split; auto. intros k I8.
    assert (k < n \/ k = n)%nat as []. lia.
    + apply I4 in H. intros x I9. apply H. applyClassifier1 I9. apply Classifier1. lra.
    + rewrite H. intros x I9. apply I2. applyClassifier1 I9. apply Classifier1. lra.
Qed.


(* 高阶导数的一些事实和性质 *)

Fact dN_Fact1 : ∀ f n, Function f -> Function (dN f n).
Proof.
  intros f n H0. destruct n as [|n].
  - simpl. assumption.
  - simpl. intros x y z I1 I2. applyClassifier2 I1; applyClassifier2 I2.
    eapply DerivativeUnique; eauto.
Qed.

Fact dN_Fact2 : ∀ f n, dom[dN f n] ⊂ dom[f].
Proof.
  red; intros. induction n. simpl in H; auto. apply IHn. applyClassifier1 H.
  destruct H. applyClassifier2 H. destruct H as [H[[x0[]]_]]. apply H1.
  apply Classifier1. rewrite Rminus_diag,Abs_ge; auto. lra.
Qed.

Fact dN_Fact3 : ∀ x n f, (dN f (S n))[x] = (dN f n)’[x].
Proof.
  intros x n f. simpl. unfold Value.
  assert (I1 : \{ λ y, [x, y] ∈ \{\ λ x1 y0, Derivative (dN f n) x1 y0 \}\ \} 
    = \{ λ y', Derivative (dN f n) x y' \}).
  { apply AxiomI; intros y; split; intro J1; applyClassifier1 J1; apply Classifier1.
    - applyClassifier2 J1. assumption.
    - apply Classifier2. assumption. }
  rewrite I1. reflexivity.
Qed.

(* 定义运算：n*(n-1)*(n-2)*...*(n-m+1) *)
Fixpoint mult_NM (n m : nat) :=
  match n, m with
  | O, _ => 1%nat
  | S n', O => 1%nat
  | S n', S m' => ((S n') * (mult_NM n' m'))%nat
  end.

Corollary mult_NM_ne_0 : ∀ n k, (mult_NM n k <> 0)%nat.
Proof.
  intros n. induction n as [ | n IHn].
  - intros k. induction k as [ | k IHk]; simpl; auto.
  - intros k. destruct k as [ | k].
    + simpl. auto.
    + simpl. generalize (IHn k); intros H0. apply not_eq_sym in H0. lia.
Qed.

Fact dN_Fact4 : ∀ a c n k, (k <= n)%nat
  -> dN (\{\ λ x y, y = c * (x - a)^n \}\) k
    = \{\ λ x y, y = c * (INR (mult_NM n k)) * (x - a)^(n - k) \}\.
Proof.
  intros a c n k H0. generalize dependent n. generalize dependent c.
  induction k as [ | k IHk].
  - intros c n H0. simpl. rewrite Nat.sub_0_r.
    assert (I1 : c * INR (mult_NM n 0) = c). { destruct n; simpl; field. }
    rewrite I1. reflexivity.
  - intros c n I1. simpl. rewrite IHk; auto; [ |lia].
    assert (I3 : c * INR (mult_NM n k) * INR(n - k) = c * INR (mult_NM n (S k))).
    { rewrite Rmult_assoc. rewrite <- mult_INR.
      assert (I3 : ∀ n, (0 < n -> k < n 
        -> mult_NM n k * (n - k) = mult_NM n (S k))%nat).
      { clear I1 IHk. intros m. generalize dependent k. 
        induction m as [ | m IHm].
        - intros k J1 J2. apply Nat.lt_irrefl in J1. contradiction.
        - intros k J1 K2. assert (k < m \/ k = m)%nat as []. lia.
          + destruct k.
            * simpl. destruct m.
              -- simpl. reflexivity.
              -- simpl. rewrite <- plus_n_O. rewrite Nat.mul_1_r. reflexivity.
            * assert (J2 : ∀ n0 m0, (mult_NM (S n0) (S m0) 
                = (S n0) * mult_NM n0 m0)%nat). 
              { intros n0 m0. simpl. reflexivity. }
              rewrite J2. rewrite J2. rewrite <- IHm; auto.
              assert (J3 : (S m - S k = m - k)%nat). { simpl. reflexivity. }
              rewrite J3. lia. lia. lia.
          + rewrite <-H in *. replace (S k - k)%nat with 1%nat; [ |lia].
            rewrite Nat.mul_1_r. clear IHm J1 K2 H. induction k. simpl; auto.
            replace (mult_NM (S (S k)) (S k))
            with ((S (S k)) * (mult_NM (S k) k))%nat; auto.
            replace (mult_NM (S (S k)) (S (S k)))
            with ((S (S k)) * (mult_NM (S k) (S k)))%nat; auto. }
      rewrite I3; auto. generalize (Nat.lt_0_succ k). intro I4.
      eapply Nat.lt_le_trans; eauto. }
    apply AxiomI. intros [x y]; split; intro I4; applyClassifier2 I4;
    apply Classifier2.
    + generalize (EleFun_Fact10 a (c * INR (mult_NM n k)) x (n - k)). intro I5.
      assert (I6 : y = (c*INR (mult_NM n k)*INR (n - k)*PowR (x - a) (n - k - 1))).
      { eapply DerivativeUnique; eauto. }
      rewrite I6. rewrite I3. rewrite <- Nat.sub_add_distr. rewrite Nat.add_1_r.
      reflexivity.
    + pattern (S k) at 2 in I4. rewrite <- Nat.add_1_r in I4.
      rewrite Nat.sub_add_distr in I4. rewrite <- I3 in I4. rewrite I4.
      apply EleFun_Fact10.
Qed.

Fact dN_Fact5 : ∀ a n k, (k <= n)%nat -> dN (\{\ λ x y, y = (x - a)^n \}\) k
  = \{\ λ x y, y = (INR (mult_NM n k)) * (x - a)^(n - k) \}\.
Proof.
  intros a n k H0.
  assert (H1 : \{\ λ x y, y = PowR (x - a) n \}\ 
    = \{\ λ x y, y = 1 * PowR (x - a) n \}\).
  { apply AxiomI; intros [x y]; split; intro I1; applyClassifier2 I1; 
    apply Classifier2; lra. }
  rewrite H1. rewrite dN_Fact4; auto. apply AxiomI; intros [x y]; split; 
  intro I1; applyClassifier2 I1; apply Classifier2; lra.
Qed.

Fact dN_Fact6 : ∀ a c n k, (n < k)%nat
  -> (dN (\{\ λ x y, y = c * (x - a)^n \}\) k) = \{\ λ x y, y = 0 \}\.
Proof.
  intros a c n k H0. induction k as [|k IHk].
  - apply Nat.nlt_0_r in H0. contradiction.
  - assert (n < k \/ n = k)%nat as []. lia.
    + apply IHk in H as I1. simpl. rewrite I1. apply AxiomI. intros [x y]; 
      split; intro J1; applyClassifier2 J1; apply Classifier2.
      * generalize (EleFun_Fact14 0 x). intros J2. eapply DerivativeUnique; eauto.
      * rewrite J1. apply EleFun_Fact14.
    + rewrite <-H. simpl. rewrite (dN_Fact4 a c n n (le_n n)). 
      rewrite Nat.sub_diag. simpl. apply AxiomI. intros [x y]; split; intro I1;
      applyClassifier2 I1; apply Classifier2.
      * generalize (EleFun_Fact14 (c * INR (mult_NM n n) * 1) x). intros I2. 
        eapply DerivativeUnique; eauto.
      * rewrite I1. apply EleFun_Fact14.
Qed.

Fact dN_Fact7 : ∀ f g n x, x ∈ dom[dN f n] -> x ∈ dom[dN g n]
  -> [x, (dN f n)[x] + (dN g n)[x]] ∈ (dN (f \+ g) n).
Proof.
  intros f g n. induction n as [|n IHn].
  - intros x H0 H1. simpl in *. apply Classifier2; auto.
  - intros x H0 H1. simpl (dN (f \+ g) (S n)). apply Classifier2. rewrite dN_Fact3.
    rewrite dN_Fact3. apply dN_Corollary_a with (k := n) in H0 as H2;
    try apply Nat.lt_succ_diag_r. destruct H2 as [δ1[H2 H3]].
    apply dN_Corollary_a with (k := n) in H1 as H4; try apply Nat.lt_succ_diag_r.
    destruct H4 as [δ2[H4 H5]].
    assert (H6 : Derivative ((dN f n) \+ (dN g n)) x (dN f n’[x] + dN g n’[x])).
    { apply Theorem5_4a.
      - applyClassifier1 H0. destruct H0 as [y H0]. applyClassifier2 H0. exists y.
        assumption.
      - applyClassifier1 H1. destruct H1 as [y H1]. applyClassifier2 H1. exists y.
        assumption. }
    apply EleFun_Fact11 with (f := (dN f n) \+ (dN g n)); auto.
    + apply dN_Fact1. apply Corollary_plus_fun_a.
    + generalize (Examp1 δ1 δ2 H2 H4). intros [δ[I1[I2 I3]]]. exists δ. 
      split; auto. intros x0 I4. split.
      * apply Classifier1. exists ((dN f n) [x0] + (dN g n) [x0]).
        applyClassifier1 I4. apply IHn; [apply H3 | apply H5]; apply Classifier1; lra.
      * assert (I5 : ((dN f n) \+ (dN g n))[x0] = (dN f n) [x0] + (dN g n) [x0]).
        { rewrite Corollary_plus_fun_b; auto; [apply H3 | apply H5];
          applyClassifier1 I4; apply Classifier1; lra. } rewrite I5. symmetry. apply f_x_T.
        -- apply dN_Fact1. apply Corollary_plus_fun_a.
        -- applyClassifier1 I4. apply IHn; [apply H3 | apply H5]; apply Classifier1; lra.
Qed.

Fact dN_Fact8 : ∀ f g n x, x ∈ dom[dN f n] -> x ∈ dom[dN g n]
  -> (dN f n)[x] + (dN g n)[x] = (dN (f \+ g) n)[x].
Proof.
  intros. pose proof (dN_Fact7 f g n x H H0).
  assert ([x, (dN (f \+ g) n)[x]] ∈ (dN (f \+ g) n)).
  { apply x_fx_T. apply dN_Fact1. apply Corollary_plus_fun_a. apply Classifier1; 
    eauto. } assert (Function (dN (f \+ g) n)).
  { apply dN_Fact1. apply Corollary_plus_fun_a. } apply (H3 x); auto.
Qed.

Fact dN_Fact9 : ∀ f g n, dom[dN (f \+ g) n] ⊂ dom[dN f n] ∩ dom[dN g n]
  -> (dN f n) \+ (dN g n) = (dN (f \+ g) n).
Proof.
  intros. apply AxiomI; split; intros; destruct z. applyClassifier2 H0.
  destruct H0 as [H0[]]. rewrite H2. apply dN_Fact7; auto.
  apply Classifier2. assert (Function (dN (f \+ g) n)).
  { apply dN_Fact1. apply Corollary_plus_fun_a. }
  assert (x ∈ dom[dN (f \+ g) n]). { apply Classifier1; eauto. }
  apply H in H2. applyClassifier1 H2. destruct H2. repeat split; auto. 
  apply (H1 x); auto. apply dN_Fact7; auto.
Qed.

Fact dN_Fact10 : ∀ f g n x, x ∈ dom[dN f n] -> x ∈ dom[dN g n]
  -> [x, (dN f n)[x] - (dN g n)[x]] ∈ (dN (f \- g) n).
Proof.
  intros f g n. induction n as [ | n IHn].
  - intros x H0 H1. simpl in *. apply Classifier2; auto.
  - intros x H0 H1. simpl (dN (f \- g) (S n)). apply Classifier2. rewrite dN_Fact3.
    rewrite dN_Fact3. apply dN_Corollary_a with (k := n) in H0 as H2;
    try apply Nat.lt_succ_diag_r. destruct H2 as [δ1[H2 H3]].
    apply dN_Corollary_a with (k := n) in H1 as H4; try apply Nat.lt_succ_diag_r.
    destruct H4 as [δ2[H4 H5]].
    assert (H6 : Derivative ((dN f n) \- (dN g n)) x (dN f n’[x] - dN g n’[x])).
    { apply Theorem5_4b.
      - applyClassifier1 H0. destruct H0 as [y H0]. applyClassifier2 H0. exists y.
        assumption.
      - applyClassifier1 H1. destruct H1 as [y H1]. applyClassifier2 H1. exists y.
        assumption. }
    apply EleFun_Fact11 with (f := (dN f n) \- (dN g n)); auto.
    + apply dN_Fact1. apply Corollary_sub_fun_a.
    + generalize (Examp1 δ1 δ2 H2 H4). intros [δ[I1[I2 I3]]]. exists δ. 
      split; auto. intros x0 I4. split.
      * apply Classifier1. exists ((dN f n)[x0] - (dN g n)[x0]). applyClassifier1 I4.
        apply IHn; [apply H3 | apply H5]; apply Classifier1; lra.
      * assert (I5 : ((dN f n) \- (dN g n))[x0] = (dN f n)[x0] - (dN g n)[x0]).
        { rewrite Corollary_sub_fun_b; auto; [apply H3 | apply H5];
          applyClassifier1 I4; apply Classifier1; lra. } rewrite I5. symmetry. apply f_x_T.
        -- apply dN_Fact1. apply Corollary_sub_fun_a.
        -- applyClassifier1 I4. apply IHn; [apply H3 | apply H5]; apply Classifier1; lra.
Qed.

Fact dN_Fact11 : ∀ f g n x, x ∈ dom[dN f n] -> x ∈ dom[dN g n]
  -> (dN f n)[x] - (dN g n)[x] = (dN (f \- g) n)[x].
Proof.
  intros. pose proof (dN_Fact10 f g n x H H0).
  assert ([x, (dN (f \- g) n)[x]] ∈ (dN (f \- g) n)).
  { apply x_fx_T. apply dN_Fact1. apply Corollary_sub_fun_a. apply Classifier1; 
    eauto. } assert (Function (dN (f \- g) n)). 
  { apply dN_Fact1. apply Corollary_sub_fun_a. } apply (H3 x); auto.
Qed.

Fact dN_Fact12 : ∀ f g n, dom[dN (f \- g) n] ⊂ dom[dN f n] ∩ dom[dN g n]
  -> (dN f n) \- (dN g n) = (dN (f \- g) n).
Proof.
  intros. apply AxiomI; split; intros; destruct z. applyClassifier2 H0.
  destruct H0 as [H0[]]. rewrite H2. apply dN_Fact10; auto. apply Classifier2. 
  assert (Function (dN (f \- g) n)). { apply dN_Fact1. apply Corollary_sub_fun_a. }
  assert (x ∈ dom[dN (f \- g) n]). { apply Classifier1; eauto. }
  apply H in H2. applyClassifier1 H2. destruct H2. repeat split; auto.
  apply (H1 x); auto. apply dN_Fact10; auto.
Qed.

Fact dN_Fact13 : ∀ f g n, dom[dN (f \- g) n] ⊂ dom[dN f n] ∩ dom[dN g n]
  -> (dN f n) \- (dN g n) = (dN (f \- g) n).
Proof.
  intros. apply AxiomI; split; intros; destruct z. applyClassifier2 H0.
  destruct H0 as [H0[]]. rewrite H2. apply dN_Fact10; auto. apply Classifier2. 
  assert (Function (dN (f \- g) n)).
  { apply dN_Fact1. apply Corollary_sub_fun_a. }
  assert (x ∈ dom[dN (f \- g) n]). { apply Classifier1; eauto. } 
  apply H in H2. applyClassifier1 H2. destruct H2. repeat split; auto.
  apply (H1 x); auto. apply dN_Fact10; auto.
Qed.

Fact dN_Fact14 : ∀ c n, (0 < n)%nat
  -> (dN \{\ λ u v, v = c \}\ n) = \{\ λ u v, v = 0 \}\.
Proof.
  intros. induction n. elim (Nat.lt_irrefl 0); auto. 
  destruct (Nat.eq_0_gt_0_cases n).
  - rewrite H0. simpl. apply AxiomI; split; intros; applyClassifier1 H1;
    destruct H1 as [x[y[]]]. rewrite H1. apply Classifier2.
    pose proof (EleFun_Fact14 c x). eapply DerivativeUnique; eauto.
    rewrite H1. apply Classifier2. rewrite H2. apply EleFun_Fact14.
  - apply IHn in H0. simpl. rewrite H0. apply AxiomI; split; intros;
    applyClassifier1 H1; destruct H1 as [x[y[]]]; rewrite H1; apply Classifier2.
    pose proof (EleFun_Fact14 0 x). eapply DerivativeUnique; eauto.
    rewrite H2. apply EleFun_Fact14.
Qed.

(* 定义: 可微  *)
Definition Differentiable f x0 := Function f
  /\ (∃ δ o A, δ > 0 /\ U(x0; δ) ⊂ dom[f]
    /\ InfinitesimalHigherOrder o \{\ λ x y, y = x \}\ 0
    /\ (∀ δx, (δx + x0) ∈ U(x0; δ) -> f[x0 + δx] - f[x0] = A * δx + o[δx])).

Theorem Theorem5_9a : ∀ f x0, Differentiable f x0 -> Derivable f x0.
Proof.
  intros. destruct H as [H[δ[o[A[H0[H1[]]]]]]].
  assert (∀ x, x ∈ Uº(0; δ) -> (f[x0 + x] - f[x0])/x = A + o[x]/x).
  { intros. assert (x <> 0).
    { applyClassifier1 H4. intro. rewrite H5, Rminus_0_r, Abs_ge in H4; lra. }
    assert (x + x0 ∈ U(x0; δ)).
    { apply Classifier1. replace (x + x0 - x0) with x. applyClassifier1 H4. 
      rewrite Rminus_0_r in H4. destruct H4; auto. lra. }
    apply H3 in H6. rewrite H6, Rdiv_plus_distr. unfold Rdiv.
    rewrite Rinv_r_simpl_l; auto. }
  exists A. apply EquaDerivative. split; auto. split; eauto. split. red; intros.
  applyClassifier2 H5. applyClassifier2 H6. subst; auto. exists δ. split; auto.
  split. red; intros. apply Classifier1. exists ((f[x0 + z] - f[x0])/z).
  apply Classifier2; auto. intros. destruct H2 as [H2[H6[H7[δ1[H8[]]]]]].
  rewrite Corollary_div_fun_c in H9. apply H10 in H5 as [δ2[[] ]].
  destruct (Examp1 δ δ2 H0 H5) as [δ3[H13[]]]. exists δ3. split; auto. intros. 
  assert (0 < ∣(x - 0)∣ < δ2). lra. apply H12 in H17.
  rewrite FunValue, H4. replace (A + o[x]/x - A) with (o[x]/x); [ | lra].
  rewrite Corollary_div_fun_b, FunValue, Rminus_0_r in H17; auto.
  assert (x ∈ Uº(0; δ1)). { apply Classifier1. lra. } apply H9 in H18. 
  applyClassifier1 H18. tauto. apply Classifier1. exists x. apply Classifier2; auto.
  rewrite FunValue. intro. rewrite H18, Rminus_diag, Abs_ge in H16; lra. 
  apply Classifier1; lra.
Qed.

Theorem Theorem5_9b : ∀ f x0, Derivable f x0 -> Differentiable f x0
  /\ (∃ δ o, δ > 0 /\ U(x0; δ) ⊂ dom[f]
    /\ InfinitesimalHigherOrder o \{\ λ x y, y = x \}\ 0
    /\ (∀ δx, (δx + x0) ∈ U(x0; δ) -> f[x0 + δx] - f[x0] = f’[x0] * δx + o[δx])).
Proof.
  intros. destruct H. pose proof H. apply Corollary_DerivativeValue_a in H0.
  pose proof H. apply EquaDerivative in H1 as [H1[[δ[]] ]].
  set (o := \{\ λ u v, v = (f[x0 + u] - f[x0])\}\ \- \{\ λ u v, v = f’[x0] * u \}\).
  assert (InfinitesimalHigherOrder o \{\ λ x1 y, y = x1 \}\ 0).
  { split; [ | split].
    - assert (limit (\{\ λ u v, v = f[x0 + u] - f[x0] \}\) 0 0).
      { assert (Continuous f x0). { apply Theorem5_1. exists x; auto. }
        destruct H5 as [H5[H6[δ1[H7[]]]]]. split. red; intros. applyClassifier2 H10. 
        applyClassifier2 H11. subst; auto. exists δ1. split; auto. split. 
        red; intros. apply Classifier1. exists (f[x0 + z] - f[x0]). 
        apply Classifier2; auto. intros. apply H9 in H10 as [δ2[]]. exists δ2. 
        split; auto. intros. assert (x1 - 0 = x1 + x0 - x0). lra. 
        rewrite H13 in H12. apply H11 in H12. rewrite FunValue.
        rewrite Rplus_comm, Rminus_0_r; auto. }
      assert (limit (\{\ λ u v, v = f’[x0] * u \}\) 0 0).
      { split. red; intros. applyClassifier2 H6. applyClassifier2 H7. subst; auto.
        exists δ. split; auto. split. red; intros. apply Classifier1.
        exists (f’[x0] * z). apply Classifier2; auto. intros.
        destruct (classic (∣(f’[x0])∣ = 0)). exists (δ/2). split. lra.
        intros. rewrite FunValue, Rminus_0_r, Abs_mult, H7, Rmult_0_l; auto.
        assert (0 < ∣(f’[x0])∣).
        { destruct (Abs_Rge0 (f’[x0])); auto. rewrite H8 in H7. lra. }
        assert (0 < (ε/∣(f’[x0])∣)).
        { unfold Rdiv. apply Rmult_lt_0_compat; auto. apply Rinv_0_lt_compat; 
          auto. } destruct (Examp1 δ (ε/∣(f’[x0])∣) H2 H9) as [δ1[H10[]]]. 
        exists (δ1). split. lra. intros. rewrite FunValue, Rminus_0_r, Abs_mult.
        rewrite Rminus_0_r in H13. assert (∣x1∣ < ε/(∣(f’[x0])∣)). lra.
        apply (Rmult_lt_compat_l (∣(f’[x0])∣)) in H14; auto. unfold Rdiv in H14.
        rewrite <- Rmult_assoc, Rinv_r_simpl_m in H14; auto. }
      assert (limit o 0 (0 - 0)). { apply Theorem3_7b; auto. }
      red. rewrite Rminus_diag in H7; auto.
    - split. red; intros. applyClassifier2 H5. applyClassifier2 H6. subst; auto.
      exists δ. split; auto. split. red; intros. apply Classifier1. exists z.
      apply Classifier2; auto. intros. destruct (Examp1 ε δ H5 H2) as [x1[H6[]]].
      exists x1. split; auto. intros. rewrite FunValue. lra.
    - split. apply Corollary_div_fun_a. exists δ. split; auto. split.
      red; intros. rewrite Corollary_div_fun_c. apply Classifier1. split.
      unfold o. rewrite Corollary_sub_fun_c. apply Classifier1. split.
      apply Classifier1. exists (f[x0 + z] - f[x0]). apply Classifier2; auto.
      apply Classifier1. exists (f’[x0] * z). apply Classifier2; auto.
      apply Classifier1. split. apply Classifier1. exists z. apply Classifier2; auto.
      apply Classifier1. rewrite FunValue. intro. applyClassifier1 H5.
      rewrite H6, Rminus_diag, Abs_ge in H5; lra. destruct H4 as [H4[δ1[H5[]]]]. 
      intros. apply H7 in H8 as [x1[[] ]]. 
      destruct (Examp1 x1 δ H8 H2) as [x2[H11[]]]. exists x2. split. lra.
      intros. assert (x3 <> 0). 
      { intro. rewrite H15, Rminus_0_r, Abs_ge in H14; lra. }
      rewrite Corollary_div_fun_b, FunValue. unfold o.
      rewrite Corollary_sub_fun_b, FunValue, FunValue, H0, Rminus_0_r.
      assert (0 < ∣(x3 - 0)∣ < x1). lra. apply H10 in H16.
      rewrite FunValue in H16. rewrite Rdiv_minus_distr. unfold Rdiv.
      rewrite Rinv_r_simpl_l; auto. apply Classifier1. exists (f[x0 + x3] - f[x0]).
      apply Classifier2; auto. apply Classifier1. exists (f’[x0] * x3).
      apply Classifier2; auto. unfold o. rewrite Corollary_sub_fun_c.
      apply Classifier1. split. apply Classifier1. exists (f[x0 + x3] - f[x0]).
      apply Classifier2; auto. apply Classifier1. exists (f’[x0] * x3).
      apply Classifier2; auto. apply Classifier1. exists x3. apply Classifier2; auto.
      rewrite FunValue; auto. }
  assert (∀ δx, (δx + x0) ∈ U(x0; δ) -> f[x0 + δx] - f[x0] = f’[x0] * δx + o[δx]).
  { intros. unfold o. rewrite Corollary_sub_fun_b, FunValue, FunValue. lra.
    apply Classifier1. exists (f[x0 + δx] - f[x0]). apply Classifier2; auto.
    apply Classifier1. exists (f’[x0] * δx). apply Classifier2; auto. }
  split. split; auto. exists δ, o, (f’[x0]); auto. exists δ, o; auto.
Qed.

(* 定义 函数在x处微分的记号 *)
Definition ɗ f x dx := (f’[x] * dx).

Property DifferentialPlus : ∀ f g x dx, Derivable f x -> Derivable g x
  -> ɗ (f \+ g) x dx = ɗ f x dx + ɗ g x dx.
Proof.
  intros. assert (Derivative (f \+ g) x (f’[x] + g’[x])).
  { apply Theorem5_4a; auto. }
  apply Corollary_DerivativeValue_a in H1. unfold ɗ. rewrite H1. lra.
Qed.

Property DifferentialMinus : ∀ f g x dx, Derivable f x -> Derivable g x
  -> ɗ (f \- g) x dx = ɗ f x dx - ɗ g x dx.
Proof.
  intros. assert (Derivative (f \- g) x (f’[x] - g’[x])).
  { apply Theorem5_4b; auto. }
  apply Corollary_DerivativeValue_a in H1. unfold ɗ. rewrite H1. lra.
Qed.

Property DifferentialMult : ∀ f g x dx, Derivable f x -> Derivable g x
  -> ɗ (f \* g) x dx = (g[x] * (ɗ f x dx)) + (f[x] * (ɗ g x dx)).
Proof.
  intros. assert (Derivative (f \* g) x ((f’[x] * g[x]) + (g’[x] * f[x]))).
  { apply Theorem5_5b; auto. }
  apply Corollary_DerivativeValue_a in H1. unfold ɗ. rewrite H1. lra.
Qed.

Property DifferentialDiv : ∀ f g x dx, Derivable f x -> Derivable g x -> g[x] <> 0
  -> ɗ (f // g) x dx = ((g[x] * (ɗ f x dx)) - (f[x] * (ɗ g x dx)))/((g[x])^2).
Proof.
  intros.
  assert (Derivative (f // g) x (((f’[x] * g[x]) - (f[x] * g’[x]))/(g[x]*g[x]))).
  { apply Theorem5_6; auto. }
  apply Corollary_DerivativeValue_a in H2. unfold ɗ. rewrite H2. simpl.
  unfold Rdiv. rewrite Rmult_assoc,(Rmult_comm _ dx),<-Rmult_assoc,Rmult_1_r. lra.
Qed.

Property DifferentialComp : ∀ f g x dx, Derivable g x -> Derivable f g[x]
  -> ɗ (f ◦ g) x dx = f’[g[x]] * (ɗ g x dx).
Proof.
  intros. assert (Derivative (f ◦ g) x (f’[g[x]] * g’[x])).
  { apply Theorem5_8; auto. }
  apply Corollary_DerivativeValue_a in H1. unfold ɗ. rewrite H1. lra.
Qed.

(* 高阶微分 *)
Fixpoint ɗn f n x dx :=
  match n with
  |0 => f[x]
  |S k => ɗ \{\ λ u v, v = ɗn f k u dx \}\ x dx
  end.

Property DifferentialHO : ∀ f n x dx, Function f -> x ∈ dom[dN f n]
  -> ɗn f n x dx = (dN f n)[x] * dx^n.
Proof.
  intros. destruct n. simpl. lra. simpl ɗn. unfold ɗ.
  assert (\{\ λ u v, v = ɗn f n u dx \}\’[x] = (dN f n)’[x] * dx^n).
  { generalize dependent x. induction n.
    - intros. simpl. assert (Function (dN f 1)). { apply dN_Fact1; auto. }
      apply x_fx_T in H0; auto. applyClassifier2 H0.
      assert (\{\ λ u v, v = f[u] \}\ = \{\ λ u v, v = 1 * f[u] \}\).
      { apply AxiomI; split; intros; destruct z; applyClassifier2 H2;
        apply Classifier2; subst; lra. } rewrite H2.
      assert (Derivative \{\ λ u v, v = 1 * f[u] \}\ x (1 * f’[x])).
      { apply EleFun_Fact9. red; eauto. }
      apply Corollary_DerivativeValue_a in H3. rewrite H3; lra.
    - assert (\{\ λ u v, v = ɗn f (S n) u dx \}\
        = \{\ λ u v, v = dx * \{\ λ a b, b = ɗn f n a dx \}\’[u] \}\).
      { apply AxiomI; split; intros; destruct z. applyClassifier2 H0.
        apply Classifier2. rewrite H0. unfold ɗ. lra. applyClassifier2 H0.
        apply Classifier2. rewrite H0. simpl. unfold ɗ. lra. }
      intros. rewrite H0.
      assert (\{\ λ u v, v = dx * \{\ λ a b, b = ɗn f n a dx \}\’[u] \}\
        |[dom[dN f (S n)]]
        = \{\ λ u v, v = dx * dx^n * (dN f (S n))[u] \}\|[dom[dN f (S n)]]).
      { apply AxiomI; split; intros; destruct z. applyClassifier1 H2. destruct H2.
        applyClassifier2 H2. applyClassifier2 H3. destruct H3. apply Classifier1. split.
        apply Classifier2. rewrite dN_Fact3,H2,IHn; auto. lra. apply Classifier2; auto.
        applyClassifier1 H2. destruct H2. apply Classifier1; split; auto.
        applyClassifier2 H2. applyClassifier2 H3. destruct H3. apply Classifier2.
        rewrite IHn,<-dN_Fact3; auto. simpl. lra. }
      assert (Derivable (dN f (S n)) x).
      { apply x_fx_T in H1. applyClassifier2 H1. red. eauto.
        apply dN_Fact1; auto. }
      assert (Derivative \{\ λ u v, v = dx * dx^n * (dN f (S n))[u] \}\
        x (dx * dx^n * (dN f (S n))’[x])). { apply EleFun_Fact9; auto. }
      assert (Function (\{\ λ u v, v = dx * dx^n * (dN f (S n))[u] \}\
        |[dom[dN f (S n)]])).
      { red; intros. applyClassifier1 H5. applyClassifier1 H6. destruct H5,H6.
        applyClassifier2 H5. applyClassifier2 H6. subst; auto. }
      assert (Function (\{\ λ u v, v = dx * dx^n * (dN f (S n))[u] \}\)).
      { red; intros. applyClassifier2 H6. applyClassifier2 H7. subst; auto. }
      assert (Derivative (\{\ λ u v, v = dx * dx^n * (dN f (S n))[u] \}\
        |[dom[dN f (S n)]]) x (dx * dx^n * (dN f (S n))’[x])).
      { apply (EleFun_Fact11 (\{\ λ u v, v = dx * dx^n * (dN f (S n))[u] \}\));
        auto. destruct H3 as [x0[_[[δ[]]_]]]. exists δ. split; auto. intros.
        apply RestrictFun with (D := dom[dN f (S n)]) in H6 as [_[]].
        split. rewrite H6. apply Classifier1. split; auto. apply Classifier1.
        exists (dx * dx^n * (dN f (S n))[x1]). apply Classifier2; auto. symmetry.
        apply H9. rewrite H6. apply Classifier1. split; auto. apply Classifier1.
        exists (dx * dx^n * (dN f (S n))[x1]). apply Classifier2; auto. }
      rewrite <-H2 in H7.
      assert (Function \{\ λ u v, v = dx * \{\ λ a b, b = ɗn f n a dx \}\’[u] \}\).
      { red; intros. applyClassifier2 H8. applyClassifier2 H9. subst; auto. }
      assert (Derivative
        (\{\ λ u v, v = dx * \{\ λ a b, b = ɗn f n a dx \}\’[u] \}\)
        x (dx * dx^n * (dN f (S n))’[x])).
      { apply (EleFun_Fact11
          (\{\ λ u v, v = dx * \{\ λ a b, b = ɗn f n a dx \}\’[u] \}\
          |[dom[dN f (S n)]])); auto. destruct H3 as [x0[_[[δ[]]_]]].
        exists δ. split; auto. intros.
        apply RestrictFun with (D := dom[dN f (S n)]) in H8 as [_[]].
        split. apply Classifier1. exists (dx * \{\ λ a b, b = ɗn f n a dx \}\’[x1]).
        apply Classifier2; auto. rewrite H11; auto. rewrite H8. apply Classifier1.
        split; auto. apply Classifier1.
        exists (dx * \{\ λ a b, b = ɗn f n a dx \}\’[x1]). apply Classifier2; auto. }
      apply Corollary_DerivativeValue_a in H9. rewrite H9. simpl. lra. }
  rewrite H1. rewrite dN_Fact3. simpl. lra.
Qed.




