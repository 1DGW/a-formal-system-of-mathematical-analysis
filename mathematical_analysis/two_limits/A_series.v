(** A_series *)
(* 级数基本概念 *)

(* 读入文件 *)
Require Export A_3.


(* 定义：数列前n项和 *)
Fixpoint Σ (x : Seq) (n : nat) :=
  match n with
  | 0%nat => x[0%nat]
  | S n => Σ x n + x[S n]
  end.

(* 定义：级数 数列的所有项求和的表达式, 以数列形式表示 *)
Definition Series u := \{\ λ n v, v = Σ u n \}\.


(**** 关于级数的若干性质 ****)

(* 级数是给定数列的有限和数列 *)
Property Series_P1 : ∀ u, IsSeq u -> IsSeq (Series u).
Proof.
  intros. split.
  - unfold Function. intros x y z H1 H2. applyClassifier2 H1.
    applyClassifier2 H2. rewrite H2. assumption.
  - apply AxiomI. intro z; split; intro H1. apply Classifier1. reflexivity.
    apply Classifier1. exists (Σ u z). apply Classifier2. reflexivity.
Qed.

(* 级数的前n项求和 *)
Property Series_P2 : ∀ u n, IsSeq u -> (Series u)[n] = Σ u n.
Proof.
  intros. apply Series_P1 in H as []. apply f_x_T; auto. apply Classifier2; auto.
Qed.

(* 如果一个级数去掉前面有限项后收敛, 则原级数收敛 *)
Property Series_P3 : ∀ u, IsSeq u
  -> (∃ M, Convergence (Series \{\ λ n v, v = u[(n + M)%nat] \}\))
  -> Convergence (Series u).
Proof.
  intros u H0 [M H1]. induction M as [|M IHM].
  - assert (H2 : \{\ λ n v, v = u [(n + 0)%nat] \}\ = u).
    { apply AxiomI. intro z. split; intro I1.
      - applyClassifier1 I1. destruct I1 as [x[y[I1 I2]]]. rewrite I1. rewrite I2.
        rewrite Nat.add_0_r. destruct H0 as [H0 I3]. apply x_fx_T; auto.
        rewrite I3. apply Classifier1. reflexivity.
      - apply Classifier1. destruct z as [x y]. exists x,y. split; auto.
        rewrite Nat.add_0_r. apply f_x_T in I1; try apply H0. rewrite I1.
        reflexivity. } rewrite H2 in H1. assumption.
  - apply IHM. destruct H1 as [A H1]. exists (A + u[M]).
    assert (H2 : IsSeq (Series \{\ λ n v, v = u [(n + M)%nat] \}\)).
    { unfold IsSeq. split. unfold Function. intros x y z I1 I2.
      applyClassifier2 I1. applyClassifier2 I2. rewrite I2. assumption.
      apply AxiomI. intro z. split; intro I1. apply Classifier1. reflexivity.
      apply Classifier1. exists (Σ \{\ λ n v, v = u [(n + M)%nat] \}\ z).
      apply Classifier2. reflexivity. }
    split; auto. intros ε H3. destruct H1 as [H1 H4]. apply H4 in H3 as [N H5].
    exists (S N). assert (H7 : ∀ N, IsSeq \{\ λ n v, v = u [(n + N)%nat] \}\).
    { intro N0. split. unfold Function. intros x y z I1 I2. applyClassifier2 I1.
      applyClassifier2 I2. rewrite I2. assumption. apply AxiomI.
      intro z; split; intro I1. apply Classifier1. reflexivity. apply Classifier1.
      exists (u[(z + N0)%nat]). apply Classifier2. reflexivity. }
    assert (H8 : ∀ n K, \{\ λ n v, v = u [(n + K)%nat] \}\[n] = u[(n + K)%nat]).
    { intros n K. apply f_x_T; try apply H7. apply Classifier2. reflexivity. }
    assert (H9 : ∀ n, u[M] + Σ \{\ λ n0 v, v = u [(n0 + S M)%nat] \}\ n
      = Σ \{\ λ n0 v, v = u[(n0 + M)%nat] \}\ (S n)).
    { intro n. induction n as [|n IHn]. simpl. rewrite H8. rewrite H8.
      rewrite H8. simpl. reflexivity. simpl. repeat rewrite H8.
      rewrite <-Rplus_assoc. rewrite IHn. simpl. rewrite H8.
      rewrite Nat.add_succ_l. rewrite <-plus_n_Sm. reflexivity. }
    intros n H10. rewrite Series_P2; auto. assert (H11 : ∃ n0, n = S n0).
    { apply Nat.neq_0_r. apply not_eq_sym. lia. } destruct H11 as [n0 H11].
    rewrite H11 in *. apply PeanoNat.lt_S_n in H10. apply H5 in H10 as H12.
    generalize (H9 n0). intro H13. rewrite Series_P2 in H12; auto.
    assert (H14 : (Σ \{\ λ n1 v, v = u[(n1 + M)%nat] \}\ (S n0)) - (A + u[M])
      = (Σ \{\ λ n v, v = u[(n + S M)%nat] \}\ n0) - A). { rewrite <-H13. field. }
    rewrite H14. assumption.
Qed.

(* 如果一个级数收敛, 则去掉前面有限项后依然收敛 *)
Property Series_P4 : ∀ u M, IsSeq u -> Convergence (Series u)
  -> Convergence (Series \{\ λ n v, v = u[(n + M)%nat] \}\).
Proof.
  intros u M H0 H1. induction M as [|M IHM].
  - assert (H2 : \{\ λ n v, v = u [(n + 0)%nat] \}\ = u).
    { apply AxiomI. intro z. split; intro I1. applyClassifier1 I1.
      destruct I1 as [x[y[I1 I2]]]. rewrite I1. rewrite I2. rewrite Nat.add_0_r.
      destruct H0 as [H0 I3]. apply x_fx_T; auto. rewrite I3. apply Classifier1.
      reflexivity. apply Classifier1. destruct z as [x y]. exists x, y. split; auto.
      rewrite Nat.add_0_r. apply f_x_T in I1; try apply H0. rewrite I1.
      reflexivity. } rewrite H2. assumption.
  - unfold Convergence in IHM. destruct IHM as [a[H2 H3]]. exists (a - u[M]).
    assert (H21 : IsSeq \{\ λ n v, v = u[(n + S M)%nat] \}\).
    { split. unfold Function. intros x y z I1 I2. applyClassifier2 I1.
      applyClassifier2 I2. rewrite I2. assumption. apply AxiomI.
      intro n; split; intro I1. apply Classifier1. reflexivity. apply Classifier1.
      exists (u[(n + S M)%nat]). apply Classifier2. reflexivity. }
    apply Series_P1 in H21 as H20. split; auto. intros ε H4. apply H3 in H4
    as [N H5]. exists N. intros n H6. apply Nat.lt_lt_succ_r in H6 as H7.
    apply H5 in H7 as H8. rewrite Series_P2; auto.
    assert (H9 : IsSeq \{\ λ n0 v, v = u[(n0 + M)%nat] \}\).
    { split. unfold Function. intros x y z I1 I2. applyClassifier2 I1.
      applyClassifier2 I2. rewrite I2. assumption. apply AxiomI.
      intro n0; split; intro I1. apply Classifier1. reflexivity. apply Classifier1.
      exists (u[(n0 + M)%nat]). apply Classifier2. reflexivity. }
    rewrite Series_P2 in H8; auto.
    assert (H10 : ∀ n, (Σ \{\ λ n v, v = u[(n + M)%nat] \}\ (S n)) - a
      = (Σ \{\ λ n0 v, v = u[(n0 + S M)%nat] \}\ n) - (a - u[M])).
    { intro n0. induction n0 as [|n0 IHn].
      - simpl. assert (I1 : \{\ λ n0 v, v = u[(n0 + M)%nat] \}\[0%nat] = u[M]).
        { apply f_x_T; try apply H9. apply Classifier2. rewrite plus_O_n. auto. }
        assert (I2 : \{\ λ n0 v, v = u[(n0 + M)%nat] \}\[1%nat] = u[S M]).
        { apply f_x_T; try apply H9. apply Classifier2.
          rewrite (Nat.add_1_l M); auto. }
        assert (I3 : \{\ λ n0 v, v = u[(n0 + S M)%nat] \}\[0%nat] = u[S M]).
        { apply f_x_T; try apply H21. apply Classifier2. rewrite plus_O_n; auto. }
        rewrite I1. rewrite I2. rewrite I3. field.
      - assert (I1 : ∀ n1, \{\ λ n0 v, v = u[(n0 + M)%nat] \}\[n1]
          = u[(n1 + M)%nat]).
        { intro n1. apply f_x_T; try apply H9. apply Classifier2; auto. }
        simpl in IHn. rewrite I1 in IHn. simpl. rewrite I1. rewrite I1.
        assert (I2 : ∀ n1, \{\ λ n0 v, v = u[(n0 + S M)%nat] \}\[n1]
          = u[(n1 + S M)%nat]).
        { intro n1. apply f_x_T; try apply H21. apply Classifier2; auto. }
        rewrite I2. assert (I3 : (S (S n0) + M)%nat = (S n0 + S M)%nat).
        { simpl. rewrite Nat.add_succ_r. reflexivity. }
        rewrite I3. lra. } rewrite H10 in H8. assumption.
Qed.


(*************************)


(* 定义指数运算 *)
Fixpoint PowR r n :=
  match n with
    | O => 1
    | S n => Rmult r (PowR r n)
  end.
Notation "r ^ n" := (PowR r n).

(* Notation "r ^ n" := (Rpow_def.pow r n). *)

(* 等比级数 *)
(* 首项为a，公比为q的数列 *)
Definition Eq_Ratio_Seq a q := \{\ λ n v, v = a * (q^n) \}\.

(**** 关于等比数列的性质 ****)
Property Eq_Ratio_Seq_P1 : ∀ a q, IsSeq (Eq_Ratio_Seq a q).
Proof.
  intros a q. split. unfold Function. intros x y z I1 I2.
  applyClassifier2 I1; applyClassifier2 I2. rewrite I2; assumption.
  apply AxiomI. intro m; split; intro I1; apply Classifier1; applyClassifier1 I1; auto.
  exists (a * (q^m)). apply Classifier2. reflexivity.
Qed.

(* 等比数列前n项和 *)
Property Eq_Ratio_Seq_P2 : ∀ a q n, q <> 1
  -> Σ (Eq_Ratio_Seq a q) n = a * (1 - (q^(S n))) / (1 - q).
Proof.
  intros a q n H0. generalize (Eq_Ratio_Seq_P1 a q). intros [H1 H2].
  assert (H3 : ∀ m, \{\ λ m v, v = a * (q^m) \}\[m] = a * (q^m)).
  { intro m. apply f_x_T; auto. apply Classifier2. reflexivity. }
  induction n as [|n IHn]. simpl. rewrite H3. simpl. field. lra.
  simpl. rewrite IHn. rewrite H3. simpl. field. lra.
Qed.

(* 等比级数收敛于 a/(1 - q) *)
Property Eq_Ratio_Seq_P3 : ∀ a q, -1 < q < 1
  -> limit_seq (Series (Eq_Ratio_Seq a q)) (a/(1 - q)).
Proof.
  intros a q H0. generalize (Eq_Ratio_Seq_P1 a q). intro H1.
  apply Series_P1 in H1 as H3. destruct H1 as [H1 H2]. split; auto. intros ε H4.
  destruct classic with (P := (q = 0)) as [H5|H5].
  - rewrite H5 in *. exists (0%nat). intros m H6.
    rewrite Series_P2; [ |split]; auto.
    assert (H7 : ∀ k, ∣((Σ \{\ λ m v, v = a * (0^m) \}\ k) - a/(1 - 0))∣ < ε).
    { intro k. induction k as [|k IHk].
      - simpl. assert (I1 : \{\ λ m v, v = a * (0^m) \}\[0%nat] = a).
        { apply f_x_T; auto. apply Classifier2. simpl. field. }
        rewrite I1. assert (I2 : a - a/(1 - 0) = 0). field.
        rewrite I2. rewrite Abs_ge; lra.
      - simpl. assert (I1 : \{\ λ m v, v = a * (0^m) \}\[S k] = 0).
        { apply f_x_T; auto. apply Classifier2. simpl. field. } rewrite I1.
        assert (I2 : (Σ \{\ λ m v, v = a * (0^m) \}\ k) + 0 - a/(1 - 0)
          = (Σ \{\ λ m v, v = a * (0^m) \}\ k) - a/(1 - 0)). field.
        rewrite I2. assumption. } apply H7.
  - destruct classic with (P := (a = 0)) as [H6|H6].
    + rewrite H6 in *. exists (0%nat). intros m H7.
      rewrite Series_P2; [ |split]; auto.
      assert (H8 : ∀ k, Σ \{\ λ m v, v = 0 * (q^m) \}\ k = 0).
      { intro k. induction k as [|k IHk].
        - simpl. assert (I1 : \{\ λ m v, v = 0 * (q^m) \}\[0%nat] = 0).
          { apply f_x_T; auto. apply Classifier2. field. } rewrite I1. reflexivity.
        - simpl. assert (I1 : \{\ λ m v, v = 0 * (q^m) \}\[S k] = 0).
          { apply f_x_T; auto. apply Classifier2. field. }
          rewrite I1. rewrite IHk. field. } unfold Eq_Ratio_Seq. rewrite (H8 m).
      assert (H9 : 0 - 0/(1 - q) = 0). field. lra. rewrite H9,Abs_ge; lra.
    + assert (H7 : 0 < ∣q∣ < 1).
      { apply Rdichotomy in H5. destruct H5 as [H5|H5]. rewrite Abs_lt; auto.
        lra. rewrite Abs_gt; auto. lra. } apply Abs_not_eq_0 in H6 as H8.
      assert (H9 : 0 < (/∣a∣) * ((/∣q∣) - 1)).
      { apply Rmult_lt_0_compat. apply Rinv_0_lt_compat. assumption.
        destruct H7 as [H7 H9]. apply Rinv_lt_contravar in H9 as H11; lra. }
      assert (H10 : 0 < /(ε * (1 - q))).
      { apply Rinv_0_lt_compat. apply Rmult_lt_0_compat; lra. }
      generalize (Archimedes ((/∣a∣) * ((/∣q∣) - 1)) (/(ε * (1 - q))) H9 H10).
      intros [N H11]. exists N. intros m H12. rewrite Series_P2; [ |split]; auto.
      rewrite Eq_Ratio_Seq_P2; try lra.
      assert (H13 : a * (1 - q^(S m)) / (1 - q) - a/(1 - q)
        = - (a * (q^(S m)) / (1 - q))). field; lra.
      rewrite H13. clear H13. rewrite <-Abs_eq_neg.
      assert (H13 : 1 - q > 0). lra. rewrite Abs_div; try lra.
      rewrite (Abs_gt (1 - q)); auto. apply (Rmult_lt_reg_r (1 - q)); auto.
      assert (H14 : ∣(a * (q^(S m)))∣ / (1 - q) * (1 - q) = ∣(a * (q^(S m)))∣).
      field; try lra. rewrite H14. clear H14. rewrite Abs_mult.
      assert (H14 : ∀ k, q^k <> 0).
      { intros. intro. induction k; simpl in H. lra.
        apply Rmult_integral in H as []; auto. }
      assert (H15 : 0 < ∣(q^(S m))∣). { apply Abs_not_eq_0. apply H14. }
      assert (H16 : ∣a∣ * ∣(q^(S m))∣ <> 0).
      { apply Rmult_integral_contrapositive_currified; apply Rgt_not_eq;
        assumption. } rewrite <-(Rinv_inv (∣a∣ * ∣(q^(S m))∣)); auto.
      assert (H17 : ε * (1 - q) <> 0).
      { apply Rmult_integral_contrapositive_currified; apply Rgt_not_eq;
        assumption. } rewrite <-Rinv_inv; auto.
      assert (H18 : 0 < /(ε * (1 - q)) * /(∣a∣ * ∣(q^(S m))∣)).
      { apply Rmult_lt_0_compat; auto. apply Rinv_0_lt_compat.
        apply Rmult_lt_0_compat; auto. } apply Rinv_lt_contravar; auto.
      rewrite (Rinv_mult (∣a∣) (∣(q^(S m))∣)); try lra.
      assert (H19 : ∀ k, /∣(q^k)∣ = (/∣q∣) ^ k).
      { intro k. induction k as [|k IHk]. simpl. rewrite Abs_gt; lra. simpl.
        rewrite Abs_mult. rewrite Rinv_mult; try lra. rewrite IHk. auto. }
      rewrite H19. assert (H20 : 1 < /∣q∣).
      { apply Rdichotomy in H5. destruct H5 as [I1|I1]. rewrite Abs_lt; auto.
        rewrite <- Rinv_1. apply Rinv_lt_contravar; lra. rewrite Abs_gt; auto.
        rewrite <- Rinv_1. apply Rinv_lt_contravar; lra. }
      assert (∀ p n, 1 < p -> (p - 1) * (INR n) < p^n).
      { intros. induction n as [|n IHn]. simpl. lra. rewrite S_INR. simpl.
        rewrite Rmult_plus_distr_l. assert (p = 1 + (p - 1)). field.
        pattern p at 3. rewrite H21,Rmult_plus_distr_r,Rmult_1_l,Rmult_1_r.
        apply Rplus_lt_le_compat; auto. assert (p - 1 = (p - 1) * 1). field.
        pattern (p - 1) at 1. rewrite H22. assert (0 <= p - 1). lra.
        apply Rmult_le_compat_l; auto. assert (∀ m0, 1 <= p^m0).
        { intro m0. induction m0 as [|m0 IHm0]. simpl. right. reflexivity.
          simpl. apply Rmult_le_compat_l with (r := p) in IHm0; lra. }
        apply H24. } generalize (H (/∣q∣) (S m) H20). intro H21.
      assert (H22 : 0 < /∣a∣). { apply Rinv_0_lt_compat. assumption. }
      apply Rmult_lt_compat_l with (r := /∣a∣) in H21; auto.
      apply Rlt_trans with (r2 := (/∣a∣) * ((/∣q∣ - 1) * (INR (S m)))); auto.
      assert (H23 : (INR N) * (/∣a∣ * (/∣q∣ - 1))
        < /∣a∣ * ((/∣q∣ - 1) * (INR (S m)))).
      { rewrite Rmult_comm,<-Rmult_assoc. apply Rmult_lt_compat_l.
        apply Rmult_lt_0_compat; lra. apply lt_INR,Nat.lt_lt_succ_r; auto. } lra.
Qed.


(* 正项级数审敛法 *)

(* 定理1: 正项级数收敛的充分必要条件为：部分和数列有界 *)
Theorem Series_T1 : ∀ u, IsSeq u -> (∀ n, 0 <= u[n])
  -> Convergence (Series u) <-> BoundedSeq (Series u).
Proof.
  intros u H0 H1. split; intro H2.
  - split; try apply Series_P1; auto. apply Theorem2_3 in H2 as [M[]]. eauto.
  - apply Theorem2_9; auto. unfold MonotonicSeq. left. unfold IncreaseSeq.
    split; try apply Series_P1; auto. intro n. rewrite Series_P2; auto.
    rewrite Series_P2; auto. simpl. generalize (H1 (S n)). intro H3.
    apply Rplus_le_compat_l with (r := Σ u n) in H3.
    rewrite Rplus_0_r in H3. assumption.
Qed.

(* 比较审敛法 *)
Theorem Series_T2 : ∀ u v, IsSeq u -> IsSeq v
  -> (∀ n, 0 <= u[n]) -> (∀ n, 0 <= v[n]) -> (∀ n, u[n] <= v[n])
  -> Convergence (Series v) -> Convergence (Series u).
Proof.
  intros u v H0 H1 H2 H3 H4 H5. apply Series_T1 in H5 as H6; auto.
  unfold BoundedSeq in H6. destruct H6 as [H6 [M H7]].
  assert (H8 : ∀ n, 0 <= (Series v)[n]).
  { intro n. rewrite Series_P2; auto. induction n as [|n IHn].
    simpl. apply H3. simpl. apply Rplus_le_le_0_compat; auto. }
  assert (H9 : ∀ n, 0 <= (Series u)[n]).
  { intro n. rewrite Series_P2; auto. induction n as [|n IHn].
    simpl. apply H2. simpl. apply Rplus_le_le_0_compat; auto. }
  assert (H10 : ∀ n, Σ u n <= Σ v n).
  { intro n. induction n as [|n IHn]. simpl. apply H4.
    simpl. apply Rplus_le_compat; auto. }
  apply Series_T1; auto. split. apply Series_P1; auto.
  exists M. intro n. generalize (H9 n). intro H11. apply Rle_ge in H11.
  rewrite Abs_ge; auto. rewrite Series_P2; auto.
  apply Rle_trans with (r2 := Σ v n); auto.
  generalize (H7 n). intro H12. generalize (H8 n). intro H13.
  apply Rle_ge in H13. rewrite Abs_ge in H12; auto.
  rewrite Series_P2 in H12; auto.
Qed.

(* 特殊情形下的比较审敛 *)
Lemma Lemma_Corollary_ST2 : ∀ u a k, limit_seq u a
  -> limit_seq \{\ λ n v, v = k * u[n] \}\ (k * a).
Proof.
  intros u a k [H0 H1]. assert (H2 : IsSeq \{\ λ n v, v = k * u[n] \}\).
  { split. unfold Function. intros x y z I1 I2. applyClassifier2 I1.
    applyClassifier2 I2. rewrite I2. assumption. apply AxiomI.
    intro z; split; intro I1. apply Classifier1. reflexivity. apply Classifier1.
    exists (k * u[z]). apply Classifier2. reflexivity. }
  split; auto. intros ε H3. destruct H2 as [H2 H6].
  destruct classic with (P := k = 0) as [H4|H4].
  - rewrite H4 in *. exists 0%nat. intros n H5.
    assert (H7 : \{\ λ n0 v, v = 0 * u[n0] \}\[n] = 0).
    { apply f_x_T; auto. apply Classifier2. field. } rewrite H7.
    assert (H8 : 0 - 0 * a = 0). field. rewrite H8. rewrite Abs_ge; lra.
  - apply Abs_not_eq_0 in H4 as H5. assert (H7 : ε/∣k∣ > 0).
    { apply Rdiv_lt_0_compat; auto. }
    apply H1 in H7 as [N H8]. exists N. intros n H9. apply H8 in H9 as H10.
    assert (H11 : \{\ λ n0 v, v = k * u[n0] \}\[n] = k * u[n]).
    { apply f_x_T; auto. apply Classifier2. reflexivity. }
    rewrite H11. assert (H12 : k * u[n] - k * a = k * (u[n] - a)). field.
    rewrite H12. rewrite Abs_mult. apply Rmult_lt_compat_l with (r := ∣k∣)
    in H10; auto. assert (H13 : ∣k∣ * (ε/∣k∣) = ε). field; try lra.
    rewrite H13 in H10. assumption.
Qed.

Corollary Corollary_Series_T2 : ∀ u v, IsSeq u -> IsSeq v
  -> (∀ n, 0 <= u[n]) -> (∀ n, 0 <= v[n]) -> Convergence (Series v)
  -> (∃ N k, (k > 0) /\ (∀ n, (N <= n)%nat -> u[n] <= k * v[n]))
  -> Convergence (Series u).
Proof.
  intros u v H0 H1 H2 H3 H4 [N[k[H5 H6]]].
  assert (H7 : ∃ u', u' = \{\ λ n x, x = u[(n + N)%nat] \}\).
  { exists \{\ λ n x, x = u[(n + N)%nat] \}\; reflexivity. }
  destruct H7 as [u' H7].
  assert (H8 : ∃ v', v' = \{\ λ n x, x = k * v[(n + N)%nat] \}\).
  { exists \{\ λ n x, x = k * v[(n + N)%nat] \}\; reflexivity. }
  destruct H8 as [v' H8]. apply Series_P3; auto. exists N. rewrite <-H7.
  assert (H9 : IsSeq u').
  { rewrite H7. split. unfold Function. intros x y z I1 I2.
    applyClassifier2 I1; applyClassifier2 I2. rewrite I2; assumption.
    apply AxiomI. intro n; split; intro I1; apply Classifier1; auto.
    exists (u[(n + N)%nat]). apply Classifier2. reflexivity. }
  assert (H10 : IsSeq v').
  { rewrite H8. split. unfold Function. intros x y z I1 I2.
    applyClassifier2 I1; applyClassifier2 I2. rewrite I2; assumption.
    apply AxiomI. intro n; split; intro I1; apply Classifier1; auto.
    exists (k * v[(n + N)%nat]). apply Classifier2. reflexivity. }
  assert (H11 : ∀ n, u'[n] = u[(n + N)%nat]).
  { intro n. apply f_x_T; try apply H9. rewrite H7. apply Classifier2. auto. }
  assert (H12 : ∀ n, v'[n] = k * v[(n + N)%nat]).
  { intro n. apply f_x_T; try apply H10. rewrite H8. apply Classifier2. auto. }
  apply (Series_T2 u' v'); auto.
  - intro n. rewrite H11. apply H2.
  - intro n. rewrite H12. apply Rmult_le_pos; auto. left; assumption.
  - intro n. rewrite H11; rewrite H12. apply H6. lia.
  - generalize (Series_P4 v N H1 H4). intros [a I1]. exists (k * a).
    assert (I2 : IsSeq \{\ λ n v0, v0 = v[(n + N)%nat] \}\).
    { split. unfold Function. intros x y z J1 J2.
      applyClassifier2 J1; applyClassifier2 J2. rewrite J2; assumption.
      apply AxiomI. intro n; split; intro J1; apply Classifier1; auto.
      exists (v[(n + N)%nat]). apply Classifier2. reflexivity. }
    assert (I3 : ∀ n0, \{\ λ n v0, v0 = v[(n + N)%nat] \}\[n0] = v[(n0 + N)%nat]).
    { intro n0. apply f_x_T; try apply I2. apply Classifier2. reflexivity. }
    assert (I4 : Series v' = \{\ λ n x,
      x = k * (Series \{\ λ n v0, v0 = v[(n + N)%nat] \}\)[n] \}\).
    { assert (J2 : ∀ n, Σ v' n = k * (Σ \{\ λ n v0, v0 = v[(n + N)%nat] \}\ n)).
      { intro n. induction n as [|n IHn]. simpl. rewrite H12. rewrite I3.
        reflexivity. simpl. rewrite Rmult_plus_distr_l. rewrite <-IHn.
        rewrite I3. rewrite H12. reflexivity. } apply AxiomI.
      intros [x y]; split; intro J1; apply Classifier2.
      - applyClassifier2 J1. rewrite Series_P2; auto. rewrite J1. apply J2.
      - applyClassifier2 J1. rewrite Series_P2 in J1; auto. rewrite J1,J2; auto. }
    rewrite I4. apply Lemma_Corollary_ST2. apply I1.
Qed.

(* 比值审敛法 *)
Theorem Series_T3 : ∀ u, IsSeq u -> (∀ n, 0 < u[n])
  -> (∃ ρ, limit_seq \{\ λ n v, v = u[S n]/u[n] \}\ ρ /\ ρ < 1)
  -> Convergence (Series u).
Proof.
  intros u H0 H1 [ρ[H2 H3]]. assert (H4 : ∃ ε, ε = (1 - ρ)/2). eauto.
  destruct H4 as [ε H4]. assert (H5 : 0 < ε). lra.
  assert (H6 : ∀ m, \{\ λ n v, v = u[S n]/u[n] \}\[m] = u[S m]/u[m]).
  { intros. rewrite FunValue; auto. }
  assert (H7 : 0 <= ρ).
  { apply lim_a in H2 as I1. assert (I2 : ∃ x, x = \{\ λ (n : nat) v, v = 0 \}\).
    eauto. destruct I2 as [x I2]. assert (I3 : IsSeq x).
    { rewrite I2. split. intros x0 y0 z0 J1 J2.
      applyClassifier2 J1; applyClassifier2 J2. rewrite J2; assumption. apply AxiomI.
      intro n; split; intro J1; apply Classifier1; applyClassifier1 J1; auto. exists 0.
      apply Classifier2. reflexivity. }
    assert (I4 : ∀ m, x[m] = 0).
    { intro m. apply f_x_T; try apply I3. rewrite I2. apply Classifier2. auto. }
    assert (I5 : limit_seq x 0).
    { split; auto. intros ε0 J1. exists (0%nat). intros n J2.
      rewrite I4. rewrite Abs_ge; lra. }
    apply lim_a in I5 as I6. rewrite <-I6. rewrite <-I1. apply Theorem2_5.
    exists 0. assumption. exists ρ; assumption. exists (0%nat). intros n J1.
    rewrite I4. rewrite H6. left. apply Rdiv_lt_0_compat; auto. }
  assert (H8 : 0 < ρ + ε < 1). lra. assert (H9 : ∃ r, r = ρ + ε). eauto.
  destruct H9 as [r H9]. destruct H2 as [[H2 H10]H11]. apply H11 in H5 as [N H12].
  assert (H13 : ∃ m, (∀ n, (m <= n)%nat -> u[S n]/u[n] < r)).
  { exists (S N). intros n I1. apply Nat.le_succ_l in I1. apply H12 in I1 as I2.
    rewrite H6 in I2. rewrite H9. apply Abs_R in I2. lra. }
  destruct H13 as [m H13]. rewrite <-H9 in H8.
  assert (H14 : ∀ n, u[(n + m)%nat] <= u[m] * r^n).
  { intro n. induction n as [|n IHn]. simpl. lra. simpl.
    assert (I1 : u[S (n + m)%nat] < r * u[(n + m)%nat]).
    { generalize (H13 (n + m)%nat (Nat.le_add_l m n)). intro J1.
      apply Rmult_lt_compat_r with (r := u[(n + m)%nat]) in J1; auto.
      assert (J2 : u[S (n + m)] / u[(n + m)%nat] * u[(n + m)%nat] = u[S (n + m)]).
      { field. apply Rgt_not_eq. apply H1. } rewrite J2 in J1. assumption. }
    left. apply Rlt_le_trans with (r2 := r * u[(n + m)%nat]); auto.
    assert (I2 : u[m] * (r * r^n) = r * (u[m] * r^n)). field. rewrite I2.
    apply Rmult_le_compat_l; auto. left; apply H8. }
  apply Series_P3; auto. exists m.
  assert (H15 : ∃ v, v = \{\ λ n w, w = u[m] * r^n \}\). eauto.
  destruct H15 as [v H15].
  assert (H16 : ∃ u', u' = \{\ λ n w, w = u[(n + m)%nat] \}\). eauto.
  destruct H16 as [u' H16]. rewrite <-H16. assert (H17 : -1 < r < 1). lra.
  generalize (Eq_Ratio_Seq_P3 (u[m]) r H17). intro H18.
  unfold Eq_Ratio_Seq in H18. rewrite <-H15 in H18.
  assert (H19 : IsSeq v).
  { rewrite H15. split. intros x0 y0 z0 J1 J2. applyClassifier2 J1; applyClassifier2 J2.
    rewrite J2; assumption. apply AxiomI. intro n; split; intro J1; apply Classifier1;
    applyClassifier1 J1; auto. exists (u[m] * r^n). apply Classifier2. reflexivity. }
  assert (H20 : IsSeq u').
  { rewrite H16. split. intros x0 y0 z0 J1 J2. applyClassifier2 J1; applyClassifier2 J2.
    rewrite J2; assumption. apply AxiomI. intro n; split; intro J1; apply Classifier1;
    applyClassifier1 J1; auto. exists (u[(n + m)%nat]). apply Classifier2. reflexivity. }
  assert (H21 : ∀ n, v[n] = u[m] * r^n).
  { intro n. apply f_x_T; try apply H19. rewrite H15. apply Classifier2; auto. }
  assert (H22 : ∀ n, u'[n] = u[(n + m)%nat]).
  { intro n. apply f_x_T; try apply H20. rewrite H16. apply Classifier2; auto. }
  apply Series_T2 with (v := v); auto. intro n. rewrite H22. left. apply H1.
  intro n. rewrite H21. apply Rle_trans with (r2 := u[(n + m)%nat]); auto. left.
  apply H1. intro n. rewrite H21; rewrite H22. apply H14. exists (u[m]/(1 - r)).
  apply H18.
Qed.

(* 定义: 绝对收敛 *)
Definition AbsoluteConvergence u :=
  Convergence (Series \{\ λ n v, v = ∣(u[n])∣ \}\).

(* 定理: 若一个级数绝对收敛，则该级数一定收敛 *)
Theorem Series_T4 : ∀ u, IsSeq u -> AbsoluteConvergence u
  -> Convergence (Series u).
Proof.
  intros u H10 [a H0].
  assert (H1 : ∃ v, v = \{\ λ n w, w = (u[n] + ∣(u[n])∣)/2 \}\). eauto.
  destruct H1 as [v H1]. assert (H2 : IsSeq v).
  { rewrite H1. split. intros x0 y0 z0 I1 I2. applyClassifier2 I1; applyClassifier2 I2.
    rewrite I2. assumption. apply AxiomI. intro n; split; intro I1; apply Classifier1;
    applyClassifier1 I1; auto. exists ((u[n] + ∣(u[n])∣)/2). apply Classifier2; auto. }
  assert (H3 : ∀ n, v[n] = (u[n] + ∣(u[n])∣)/2).
  { intro n. apply f_x_T; try apply H2. rewrite H1. apply Classifier2; auto. }
  assert (H4 : IsSeq \{\ λ n v, v = ∣(u[n])∣ \}\).
  { split. intros x0 y0 z0 I1 I2. applyClassifier2 I1; applyClassifier2 I2.
    rewrite I2. assumption. apply AxiomI. intro n; split; intro I1; apply Classifier1;
    applyClassifier1 I1; auto. exists (∣(u[n])∣). apply Classifier2; auto. }
  assert (H5 : ∀ n, \{\ λ n v, v = ∣(u[n])∣ \}\[n] = ∣(u[n])∣).
  { intro n. apply f_x_T; try apply H4. apply Classifier2. reflexivity. }
  assert (H6 : Convergence (Series v)).
  { apply Series_T2 with (v := \{\ λ n v, v = ∣(u[n])∣ \}\); auto.
    - intro n. rewrite H3. destruct (Rle_or_lt 0 u[n]) as [I1|I1].
      apply Rle_ge in I1. rewrite Abs_ge; auto. lra. + rewrite Abs_lt; auto. lra.
    - intro n. rewrite H5. apply Rge_le. apply Abs_Rge0.
    - intro n. rewrite H3; rewrite H5. destruct (Rle_or_lt 0 u[n]) as [I1|I1].
      apply Rle_ge in I1. rewrite Abs_ge; auto. lra. pattern (∣(u[n])∣) at 1.
      rewrite Abs_lt; auto. generalize (Abs_Rge0 u[n]). intro I2. lra.
    - exists a. assumption. }
  assert (H7 : ∀ n, u[n] = 2 * v[n] - ∣(u[n])∣).
  { intro n. rewrite H3. destruct (Rle_or_lt 0 u[n]) as [I1|I1].
    apply Rle_ge in I1. rewrite Abs_ge; auto. lra. rewrite Abs_lt; auto. lra. }
  destruct H6 as [b H6]. exists (2*b - a). apply Series_P1 in H10 as H11.
  split; auto. intros ε H12. assert (2/3 * ε > 0 /\ 1/3 * ε > 0) as [H13 H14]. lra.
  apply H6 in H14 as H15. destruct H15 as [N2 H15]. apply H0 in H14 as H16.
  destruct H16 as [N1 H16]. generalize (Max_nat_2 N1 N2). intros [N[H17 H18]].
  exists N. intros n H19. rewrite Series_P2; auto.
  assert (H20 : ∀ k, Σ u k = 2 * (Σ v k) - (Σ \{\ λ n v, v = ∣(u[n])∣ \}\ k)).
  { intro k. induction k as [|k IHk]; simpl. rewrite H5. apply H7. rewrite H5.
    assert (I1 : 2 * (Σ v k + v[S k])
      - (Σ \{\ λ n v, v = ∣(u[n])∣ \}\ k + ∣(u[S k])∣)
    = 2 * (Σ v k) - (Σ \{\ λ n v, v = ∣(u[n])∣ \}\ k)
      + 2 * v[S k] - ∣(u[S k])∣ ). field. rewrite I1. clear I1. rewrite <-IHk.
    pattern (u[S k]) at 1. rewrite H7. unfold Rminus. rewrite <-Rplus_assoc.
    reflexivity. } rewrite H20.
  assert (H21 : 2 * (Σ v n) - (Σ \{\ λ n v, v = ∣(u[n])∣ \}\ n) - (2*b - a)
    = 2 * (Σ v n - b) - ((Σ \{\ λ n v, v = ∣(u[n])∣ \}\ n) - a)). field.
  rewrite H21. clear H21. generalize (Abs_minus_le (2 * (Σ v n - b))
  (Σ \{\ λ n v, v = ∣(u[n])∣ \}\ n - a)). intro H21. apply Rle_lt_trans with
  (r2 := ∣(2 * (Σ v n - b))∣ + ∣(Σ \{\ λ n v, v = ∣(u[n])∣ \}\ n - a)∣); auto.
  clear H21. assert (H21 : ε = 2 * (1/3 * ε) + (1/3) * ε). field. rewrite H21.
  clear H21. apply Rplus_lt_compat. rewrite Abs_mult, Abs_ge; try lra.
  assert (H21 : (n > N2)%nat). { apply Nat.lt_trans with (m := N); auto. }
  generalize (H15 n H21); intro H22. rewrite Series_P2 in H22; auto. lra.
  assert (I1 : (n > N1)%nat). { apply Nat.lt_trans with (m := N); auto. }
  generalize (H16 n I1); intro I2. rewrite Series_P2 in I2; auto.
Qed.



(* 定义: 阶乘 *)
Fixpoint Factorial (n : nat) :=
  match n with
  | 0%nat => 1%nat
  | S n => ((S n) * Factorial n)%nat
  end.

Notation "n !" := (Factorial n)(at level 10).

(* Notation "n !" := (Coq.Arith.Factorial.fact n)(at level 10). *)

Fact Factorial_Fact1 : ∀ n, (0 < n!)%nat.
Proof. intros n. induction n as [|n IHn]; simpl; lia. Qed.




