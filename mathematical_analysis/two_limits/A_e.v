(** A_e *)
(* 极限值 (1 + 1/n)^n = e *)

(* 读入文件 *)
Require Export two_limits.A_series.


Lemma limit_e_Lemma1 : ∀ a b n, (0 < n)%nat -> 0 < a < b -> a^n < b^n.
Proof.
  intros a b n H0 H1. induction n as [| n IHn].
  - exfalso. apply Nat.lt_irrefl in H0. assumption.
  - assert (0 < n \/ 0 = n)%nat as []. lia. simpl. apply IHn in H.
    assert (∀ x0 k, x0 > 0 -> x0^k > 0).
    { intros. induction k. simpl. lra. simpl. apply Rmult_gt_0_compat; auto. }
    assert (a * a^n < a * b^n). { apply Rmult_lt_compat_l; auto. lra. }
    assert (a * b^n < b * b^n).
    { apply Rmult_lt_compat_r; auto. apply H2; lra. lra. } lra.
    rewrite <-H. simpl. lra.
Qed.

Lemma limit_e_Lemma2 : ∀ a b n, 0 < a < b -> (0 < n)%nat
  -> (b^(S n)) - (a^(S n)) < (INR (S n)) * (b^n) * (b - a).
Proof.
  intros a b n H0. induction n as [| n IHn].
  - intro H1. apply Nat.lt_irrefl in H1. exfalso. assumption.
  - intro H1. apply PeanoNat.lt_n_Sm_le in H1.
    assert (0 < n \/ 0 = n)%nat. lia. apply or_comm in H.
    destruct H as [H|H]. rewrite <-H in *.
    simpl. rewrite Rmult_1_r in *. rewrite Rmult_1_r.
    assert (H2 : b*b - a*a = (b + a) * (b - a)). field.
    rewrite H2. apply Rmult_lt_compat_r; lra. apply IHn in H as H2.
    assert (H3 : b^(S (S n)) - a^(S (S n))
      = b * (b^(S n) - a^(S n)) + (a^(S n)) * (b - a)). simpl. field. rewrite H3.
    assert (H4 : b * (b^(S n) - a^(S n)) + a^(S n) * (b - a)
      < b * (INR (S n) * b^n * (b - a)) + a^(S n) * (b - a)).
    { apply Rplus_lt_compat_r. apply Rmult_lt_compat_l; lra. }
    apply Rlt_trans with
    (r2 := b * ((INR (S n)) * b^n * (b - a)) + a^(S n) * (b - a)); auto.
    rewrite <-Rmult_assoc,<-Rmult_assoc,<-Rmult_plus_distr_r.
    apply Rmult_lt_compat_r; try lra.
    assert (H5 : (INR (S (S n))) * b^(S n) = b * (INR (S n)) * b^n + b^(S n)).
    simpl. field. rewrite H5. apply Rplus_lt_compat_l,limit_e_Lemma1; auto.
Qed.

Lemma limit_e_Lemma3 : ∀ a b n, 0 < a < b -> (0 < n)%nat
  -> a^(S n) > b^n * ((INR (S n)) * a - (INR n) * b).
Proof.
  intros a b n H0 H1. generalize (limit_e_Lemma2 a b n H0 H1). intro H2.
  assert (H3 : a^(S n) > b^(S n) - (INR (S n)) * b^n * (b - a)). lra.
  assert (H4 : b^(S n) - (INR (S n)) * b^n * (b - a)
    = b^n * ((INR (S n)) * a - (INR n) * b)).
  { simpl PowR. rewrite S_INR. field. } rewrite <-H4. assumption.
Qed.

Lemma limit_e_Lemma4 : ∀ n, ∃ m, (n = m + m \/ n = m + m + 1)%nat.
Proof.
  intro n. induction n as [|n IHn].
  - exists 0%nat. left. simpl. reflexivity.
  - destruct IHn as [m[IHn|IHn]]. exists m. right. rewrite IHn,Nat.add_1_r.
    reflexivity. exists (S m). left. rewrite IHn. rewrite Nat.add_1_r.
    simpl. rewrite (Nat.add_comm m (S m)). simpl. reflexivity.
Qed.

Theorem limit_e : ∃ e, limit_seq \{\ λ n v, v = (1 + 1/(INR (S n)))^(S n) \}\ e.
Proof.
  assert (H0 : IsSeq \{\ λ n v, v = (1 + 1/(INR (S n)))^(S n) \}\).
  { split. unfold Function. intros x y z I1 I2. apply ->Classifier2 in I1.
    lazy beta in I1. apply ->Classifier2 in I2. lazy beta in I2. rewrite I2; auto.
    apply AxiomI. intro n; split; intro I1. apply Classifier1. reflexivity.
    apply Classifier1. exists ((1 + 1/(INR (S n)))^(S n)). apply Classifier2. auto. }
  assert (H1 : ∀ n, \{\ λ n v, v = (1 + 1/(INR (S n)))^(S n) \}\[n]
    = (1 + 1/(INR (S n)))^(S n)).
  { destruct H0 as [H0 I1]. intro n. apply f_x_T; auto. apply Classifier2. auto. }
  generalize Nat.lt_0_succ. intro H2.
  assert (H3 : IncreaseSeq \{\ λ n v, v = (1 + 1/(INR (S n)))^(S n) \}\).
  { unfold IncreaseSeq. split; auto. intro n. rewrite H1. rewrite H1.
    assert (H3 : 0 < (1 + 1/(INR (S (S n)))) < (1 + 1/(INR (S n)))).
    { generalize (pos_INR n). intro I1. rewrite S_INR. rewrite S_INR.
      assert (I2 : 0 < (INR n) + 1 < (INR n) + 1 + 1). lra.
      assert (I3 : 0 < ((INR n) + 1) * ((INR n) + 1 + 1)).
      { apply Rmult_gt_0_compat; lra. }
      assert (I4 : /((INR n) + 1 + 1) < /((INR n) + 1)).
      { apply Rinv_lt_contravar; lra. }
      assert (I5 : 0 < /((INR n) + 1 + 1)).
      { apply Rinv_0_lt_compat; lra. } lra. }
    generalize (limit_e_Lemma3 (1 + 1/(INR (S (S n))))
      (1 + 1/(INR (S n))) (S n) H3 (H2 n)). intro H4.
    assert (H5 : (INR (S (S n))) * (1 + 1/(INR (S (S n))))
      - (INR (S n)) * (1 + 1/(INR (S n))) = 1).
    { rewrite S_INR. rewrite S_INR. field. generalize (pos_INR n).
      intro I1. split; lra. } rewrite H5 in H4. lra. }
  apply Theorem2_9. left. auto. unfold BoundedSeq. split; auto. exists 4.
  assert (H4 : ∀ n, (1 + 1/(2 * (INR (S n))))^((S n) + (S n)) < 2 * 2).
  { intro n. assert (H5 : 0 < 1 < 1 + 1/(2 * (INR (S n)))).
    { split; try lra. rewrite S_INR. generalize (pos_INR n). intro H5.
      assert (H6 : 2 * ((INR n) + 1) > 0). lra.
      assert (H7 : 1/(2 * ((INR n) + 1)) > 0).
      { apply Rdiv_lt_0_compat; lra. } lra. }
    generalize (limit_e_Lemma3 1 (1 + 1/(2 * (INR (S n)))) (S n) H5 (H2 n)).
    intro H6. assert (H7 : ∀ n, 1^n = 1).
    { intro n0. induction n0 as [|n0 IHn]. simpl. reflexivity.
      simpl. rewrite IHn. field. } rewrite H7 in H6.
    assert (H8 : (INR (S (S n))) * 1 - (INR (S n)) * (1 + 1/(2 * (INR (S n))))
      = 1/2).
    { rewrite S_INR. field. rewrite S_INR. generalize (pos_INR n). lra. }
    rewrite H8 in H6. assert (H9 : (1 + 1/(2 * (INR (S n))))^(S n) < 2). lra.
    assert (H10 : ∀ a m k, a^m * a^k = a^(m + k)).
    { intros a m k. induction m as [|m IHm]. simpl. field.
      simpl. rewrite Rmult_assoc. rewrite IHm. reflexivity. }
    assert (H11 : ∀ a m, a > 0 -> 0 < a^m).
    { intros a m I1. induction m as [|m IHm]. simpl. lra.
      simpl. apply Rmult_lt_0_compat; auto. }
    assert (H12 : 0 < 1 + 1/(2 * (INR (S n)))).
    { rewrite S_INR. generalize (pos_INR n). intro I1.
      assert (I2 : 2 * ((INR n) + 1) > 0). lra.
      assert (I3 : 1/(2 * ((INR n) + 1)) > 0).
      { apply Rdiv_lt_0_compat; lra. } lra. }
    assert (H13 : ((1 + 1/(2 * (INR (S n))))^(S n))
      * ((1 + 1/(2 * (INR (S n))))^(S n)) < 2 * 2).
    { apply Rmult_le_0_lt_compat; auto; left; apply H11; auto. }
    rewrite H10 in H13. auto. } intro n. rewrite H1.
  assert (H5 : ∀ n, (1 + 1/(INR (S n)))^(S n) > 0).
  { intro n0. unfold IncreaseSeq in H3. induction n0 as [|n0 IHn].
    simpl. lra. destruct H3 as [H3 I1]. generalize (I1 n0). intro I2.
    rewrite H1 in I2. rewrite H1 in I2. lra. } rewrite Abs_gt; auto.
  assert (H6 : ∀ n, 2 * (INR (S n)) = (INR (S n)) + (INR (S n))).
  intro n0. field. apply ->EqualIncrease in H3. destruct H3 as [H3 H7].
  assert (H8 : (n < n + (S n))%nat).
  { apply Nat.lt_lt_add_l. apply Nat.lt_succ_diag_r. }
  apply H7 in H8 as H9. rewrite H1 in H9. rewrite H1 in H9.
  assert (H10 : (S (n + (S n)) = (S n) + (S n))%nat). { simpl. reflexivity. }
  assert (H11 : (INR ((S n) + (S n)) = 2 * (INR (S n))%nat)).
  { rewrite plus_INR. ring. } rewrite H10,H11 in H9. generalize (H4 n).
  intro H12. lra.
Qed.

(* 定理: 用来定义e指数函数的级数是收敛的 *)
Theorem eSeries_Convergence : ∀ x,
  Convergence (Series \{\ λ n v, v = (x^n)/(INR (n!)) \}\ ).
Proof.
  intro x. assert (H0 : ∃ u, u = \{\ λ n v, v = (x^n)/(INR (n!)) \}\ ).
  { exists \{\ λ n v, v = (x^n)/(INR (n!)) \}\; reflexivity. }
  destruct H0 as [u H0]. assert (H1 : IsSeq u).
  { rewrite H0. split. intros x0 y0 z0 I1 I2. applyClassifier2 I1; applyClassifier2 I2.
    rewrite I2. assumption. apply AxiomI.
    intro n; split; intro I1; apply Classifier1; applyClassifier1 I1; auto.
    exists ((x^n)/(INR (n!))). apply Classifier2. reflexivity. }
  assert (H2 : ∀ n, u[n] = (x^n)/(INR (n!))).
  { intro n. apply f_x_T; try apply H1. rewrite H0. apply Classifier2. reflexivity. }
  assert (H9 : ∀ n, 0 < (INR (n!))).
  { intro n. apply lt_0_INR. apply Factorial_Fact1. }
  destruct classic with (P := x = 0) as [H6|H6].
  - rewrite H6 in *. assert (H3 : ∃ n, 0^n = 1 ). { exists 0%nat. simpl. auto. }
    assert (H3' : ∀ n, 0^(n+1) = 0 ).
    { induction n as [|n]. simpl. lra. simpl. lra. }
    exists 1. rewrite <-H0. apply Series_P1 in H1 as H4. split; auto.
    intros ε H5. exists 0%nat. intros n H7. rewrite Series_P2; auto.
    assert (H8 : ∀ k, Σ u k = 1).
    { intro k. induction k as [|k IHk]. simpl. rewrite H2. simpl. lra.
      simpl. rewrite H2. rewrite IHk. simpl. lra. }
    rewrite H8. rewrite Abs_ge; lra.
  - rewrite <-H0. apply Series_T4; auto. unfold AbsoluteConvergence.
    assert (H3 : ∃ absu, absu = \{\ λ k v, v = ∣(u[k])∣ \}\). eauto.
    destruct H3 as [absu H3]. rewrite <-H3.
    assert (H4 : IsSeq absu).
    { rewrite H3. split. intros x0 y0 z0 I1 I2.
      applyClassifier2 I1; applyClassifier2 I2. rewrite I2. assumption.
      apply AxiomI. intro k; split; intro I1; apply Classifier1; applyClassifier1 I1;
      auto. exists (∣(u[k])∣). apply Classifier2. reflexivity. }
    assert (H5 : ∀ k, absu[k] = ∣(u[k])∣).
    { intro k. apply f_x_T; try apply H4. rewrite H3. apply Classifier2. auto. }
    assert (H20 : ∀ a k, a <> 0 -> a^k <> 0).
    { intros a k J1. induction k as [|k IHk]. simpl. lra.
      simpl. apply Rmult_integral_contrapositive_currified; auto. }
    assert (H7 : ∀ n, 0 < absu[n]).
    { intro n. rewrite H5. rewrite H2. apply Abs_not_eq_0.
      assert (I1 : /(INR (n!)) <> 0).
      { apply Rinv_neq_0_compat. apply Rgt_not_eq. apply H9. }
      apply Rmult_integral_contrapositive_currified; auto. }
    apply Series_T3; auto. exists 0. split; try lra.
    assert (H8 : ∃ u', u' = \{\ λ n v, v = absu[S n]/absu[n] \}\).
     { exists \{\ λ n v, v = absu[S n]/absu[n] \}\; reflexivity. }
    destruct H8 as [u' H8]. rewrite <-H8.
    assert (H10 : IsSeq u').
    { rewrite H8. split. intros x0 y0 z0 I1 I2.
      applyClassifier2 I1; applyClassifier2 I2. rewrite I2. assumption.
      apply AxiomI. intro k; split; intro I1; apply Classifier1; applyClassifier1 I1;
      auto. exists (absu[S k]/absu[k]). apply Classifier2. reflexivity. }
     assert (H11 : ∀ k, u'[k] = absu[S k]/absu[k]).
    { intro k. apply f_x_T; try apply H10. rewrite H8. apply Classifier2. auto. }
    split; auto. intros ε H12. destruct classic with (P := x > 0) as [H13|H13].
    + generalize (Archimedes ε x H12 H13). intros [N H14]. exists N.
      intros n H15. assert (H16 : 0 < u'[n]).
      { rewrite H11. apply Rdiv_lt_0_compat; apply H7. }
      rewrite Rminus_0_r. rewrite Abs_gt; auto. rewrite H11,H5,H5.
      assert (H17 : ∀ k, u[k] <> 0).
      { intros k I1. generalize (H7 k). intro I2. apply Rlt_not_eq in I2.
        apply I2. rewrite H5,I1. rewrite Abs_ge; lra. } rewrite <-Abs_div; auto.
      assert (H18 : ∀ a k, a <> 0 -> (a^(S k))/(a^k) = a).
      { intros a k I1. simpl. field. apply H20; assumption. } rewrite H2,H2.
      assert (H19 : x^(S n) / (INR ((S n)!)) / (x^n / (INR (n!)))
        = (x^(S n) / (x^n)) * (INR (n!)) / (INR ((S n)!))).
        { field. repeat split; [apply H20; auto| | ];
          apply Rgt_not_eq,lt_0_INR,Factorial_Fact1. }
      rewrite H19; clear H19. rewrite H18; try lra.
      assert (H19 : INR ((S n)!) = (INR (S n)) * (INR (n!))).
      { assert (I1 : ∀ k, (S k)! = ((S k) * k!)%nat).
        { intro k. simpl. auto. } rewrite I1. apply mult_INR. } rewrite H19.
      assert (x * (INR (n!)) / ((INR (S n)) * (INR (n!))) = (x/(INR (S n)))).
      { field. split. apply not_0_INR. intro. discriminate H.
        apply not_0_INR. apply Nat.neq_sym.
        assert (0 < n!)%nat. { apply Factorial_Fact1. } lia. }
      rewrite H. clear H. assert (H21 : 0 < (INR (S n))).
      { apply lt_0_INR. apply Nat.lt_0_succ. }
      rewrite Abs_div; try apply Rgt_not_eq; auto.
      rewrite Abs_gt; try lra. rewrite Abs_gt; try lra.
      assert (H22 : (INR n) < (INR (S n))). { apply lt_INR. lia. }
      assert (H23 : 0 < (INR n)). { apply lt_0_INR,(Nat.lt_lt_0 N); auto. }
      apply Rmult_gt_reg_l with (r := INR (S n)); try lra.
      assert (H24 : (INR (S n)) * (x/(INR (S n))) = x). { field; try lra. }
      rewrite H24. clear H24. apply Rmult_lt_compat_r with (r := ε) in H22; auto.
      apply Rlt_trans with (r2 := (INR n) * ε); auto. apply lt_INR in H15.
      apply Rmult_lt_compat_r with (r := ε) in H15; auto. lra.
    + assert (H13' : x < 0).
      { apply (Rnot_gt_le x 0) in H13. destruct H13; auto. contradiction. }
      clear H13. apply Ropp_gt_lt_0_contravar in H13'.
      generalize (Archimedes ε (-x)%nat H12 H13'). intros [N H14]. exists N.
      intros n H15. assert (H16 : 0 < u'[n]).
      { rewrite H11. apply Rdiv_lt_0_compat; apply H7. }
      rewrite Rminus_0_r. rewrite Abs_gt; auto. rewrite H11,H5,H5.
      assert (H17 : ∀ k, u[k] <> 0).
      { intros k I1. generalize (H7 k). intro I2. apply Rlt_not_eq in I2.
        apply I2. rewrite H5,I1,Abs_ge; lra. } rewrite <-Abs_div; auto.
      assert (H18 : ∀ a k, a <> 0 -> (a^(S k))/(a^k) = a).
      { intros a k I1. simpl. field. apply H20; assumption. } rewrite H2,H2.
      assert (H19 : x^(S n) / INR ((S n)!) / (x^n / (INR (n!)))
        = x^(S n) / (x^n) * (INR (n!)) / (INR ((S n)!))).
        { field. repeat split; [apply H20; assumption| | ];
          apply Rgt_not_eq,lt_0_INR,Factorial_Fact1. }
      rewrite H19; clear H19. rewrite H18; try lra.
      assert (H19 : INR ((S n)!) = (INR (S n)) * INR (n!)).
      { assert (I1 : ∀ k, (S k)! = ((S k) * (k!))%nat).
        { intro k. simpl. auto. } rewrite I1. apply mult_INR. } rewrite H19.
      assert (x * (INR (n!)) / ((INR (S n)) * (INR (n!))) = x/(INR (S n))).
      { field. split. apply not_0_INR. intro. discriminate H.
        apply not_0_INR. assert (0 < n!)%nat. { apply Factorial_Fact1. } lia. }
      rewrite H. clear H. assert (H21 : 0 < (INR (S n))).
      { apply lt_0_INR. apply Nat.lt_0_succ. }
      rewrite Abs_div; try apply Rgt_not_eq; auto.
      rewrite Abs_lt; try lra. rewrite Abs_gt; try lra.
      assert (H22 : (INR n) < (INR (S n))). { apply lt_INR. lia. }
      assert (H23 : 0 < (INR n)). { apply lt_0_INR,(Nat.lt_lt_0 N); auto. }
      apply Rmult_gt_reg_l with (r := INR (S n)); try lra.
      assert (H24 : (INR (S n)) * (-x / (INR (S n))) = -x ). { field; try lra. }
      rewrite H24. clear H24. apply Rmult_lt_compat_r with (r := ε) in H22; auto.
      apply Rlt_trans with (r2 := (INR n) * ε); auto. apply lt_INR in H15.
      apply Rmult_lt_compat_r with (r := ε) in H15; auto. lra.
Qed.

(* 定义 exp 函数 *)
Definition exp :=
  \{\ λ x y, limit_seq (Series \{\ λ n v, v = (x^n)/(INR (n!)) \}\) y \}\.

(* exp是一个函数 *)
Property exp_Function : Function exp.
Proof.
  intros x y z H0 H1. applyClassifier2 H0. applyClassifier2 H1.
  eapply Theorem2_2; eauto.
Qed.

(* exp的定义域为全体实数 *)
Property exp_dom : dom[exp] = Full R.
Proof.
  apply AxiomI. intro x; split; intro H0; apply Classifier1; applyClassifier1 H0; auto.
  generalize (eSeries_Convergence x). intros [y H1]. exists y. apply Classifier2.
  assumption.
Qed.

Property exp_value : ∀ x,
  limit_seq (Series \{\ λ k v, v = (x^k)/(INR (k!)) \}\) exp[x].
Proof.
  intro x. assert (H0 : x ∈ dom[exp]).
  { rewrite exp_dom. apply Classifier1. reflexivity. }
  apply x_fx_T in H0; try apply exp_Function. applyClassifier2 H0. auto.
Qed.








