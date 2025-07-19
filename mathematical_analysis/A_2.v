(** A_2 *)
(* 数列极限 *)

(* 读入文件 *)
Require Export A_1.


(* 2.1 数列极限的概念 *)
(* 定义：数列 *)
Definition Seq := @set (@prod nat R).
Definition IsSeq (f : Seq) := Function f /\ dom[f] = Full nat.

(* 数列极限的两种定义 *)
Definition limit_seq f a := IsSeq f
  /\ ∀ ε, ε > 0 -> (∃ N, ∀ n, (n > N)%nat -> ∣(f[n] - a)∣ < ε).
Definition limit_seq' f a := IsSeq f
  /\ ∀ ε, ε > 0 -> Finite \{ λ u, f[u] ∉ U(a; ε) \}.

Definition lim f := c (\{ λ a, limit_seq f a \}).

(* 两种定义等价 *)
Fact EqualLimit : ∀ f a, limit_seq f a <-> limit_seq' f a.
Proof.
  intros x a. unfold limit_seq; unfold limit_seq'. split; intro H1.
  - destruct H1 as [J1 H1]. split; auto. intros ε H2. apply H1 in H2 as H3. 
    destruct H3 as [N H3]. assert (H4 : ∃ A, A = \{ λ u, (u <= N)%nat \}). 
    { exists \{ λ u, (u <= N)%nat \}. auto. } 
    destruct H4 as [A H4]. assert (H5 : \{ λ u, x [u] ∉ U(a; ε) \} ⊂ A).
    { intros z H5. applyClassifier1 H5. rewrite H4. apply <- Classifier1. 
      apply NNPP. intro H6. apply Nat.nle_gt in H6. apply H3 in H6 as H7.
      apply H5. apply <- Classifier1. auto. }
    apply SubSetFinite with (A := A); auto. unfold Finite.
    left. rewrite H4. apply NatFinite.
  - destruct H1 as [J1 H1]. split; auto.
    intros ε H2. apply H1 in H2 as H3. destruct H3 as [H3 | H3].
    + apply finite_maxN in H3 as H4. destruct H4 as [N H4]. exists N.
      intros n H5. unfold maxN in H4. destruct H4 as [H4 H6]. apply NNPP.
      intro H7. assert (H8 : n ∈ \{ λ u : nat, x [u] ∉ U(a; ε) \}).
      { apply <- Classifier1. intro I1. applyClassifier1 I1. auto. }
      apply H6 in H8 as H9. lia.
    + exists 0%nat. intros n H4. apply NNPP. intro H5.
      assert (H6 : n ∈ \{ λ u : nat, x [u] ∉ U(a; ε) \}).
      { apply <- Classifier1. intro I1. apply H5. applyClassifier1 I1. auto. }
      rewrite H3 in H6. applyClassifier1 H6. auto.
Qed.

(* 定义: 收敛数列 *)
Definition Convergence f := ∃ a, limit_seq f a.

(* 定义: 发散数列 *)
Definition Divergence f := IsSeq f /\ (∀ a, ~ limit_seq f a).

(* 定义：无穷小数列 *)
Definition Infinitesmal f := limit_seq f 0.

(* 定理2.1 *)
Theorem Theorem2_1 : ∀ f a, IsSeq f
  -> limit_seq f a <-> Infinitesmal \{\ λ u v, v = f[u] - a \}\.
Proof.
  intros x a H0. split; intro H1.
  - unfold Infinitesmal. unfold limit_seq in *. destruct H1 as [H1 H2].
    assert (H10 : IsSeq \{\ λ u v, v = x [u] - a \}\ ).
    { unfold IsSeq in *. destruct H1 as [H1 H3]. split.
      - unfold Function. intros x0 y0 z0 I1 I2. applyClassifier2 I1.
        applyClassifier2 I2. rewrite I2. auto.
      - apply AxiomI. intro z; split; intro I1.
        + apply <- Classifier1. auto.
        + apply <- Classifier1. exists (x[z] - a). apply <- Classifier2. auto. }
    split; auto. intros ε H3. apply H2 in H3 as H4. destruct H4 as [N H4].
    exists N. intros n H5. apply H4 in H5 as H6. apply Abs_R. 
    apply Abs_R in H6 as H7. destruct H10 as [H10 H11].
    assert (H8 : \{\ λ u v, v = x [u] - a \}\ [n] = x[n] - a).
    { apply f_x_T; auto. apply <- Classifier2. auto. }
    rewrite H8. rewrite Rminus_0_r. auto.
  - unfold Infinitesmal in H1. unfold limit_seq in *. destruct H1 as [H1 H2].
    split; auto. intros ε H3. apply H2 in H3 as H4. destruct H4 as [N H4]. 
    exists N. intros n H5. apply H4 in H5 as H6. rewrite Rminus_0_r in H6.
    assert (H7 : \{\ λ u v, v = x [u] - a \}\ [n] = x[n] - a).
    { apply f_x_T; try apply H1. apply <- Classifier2. auto. }
    rewrite H7 in H6. auto.
Qed.

(* 定义：无穷大数列 *)
Definition Infiniteseries f := IsSeq f
  /\ ∀ M, M > 0 -> (∃ N, ∀ n, (n > N)%nat -> ∣(f[n])∣ > M).

(* 定义：正无穷大数列 *)
Definition PosInfiniteseries f := IsSeq f
  /\ ∀ M, M > 0 -> (∃ N, ∀ n, (n > N)%nat -> f[n] > M).
(* 定义：负无穷大数列 *)
Definition NegInfiniteseries f := IsSeq f
  /\ ∀ M, M > 0 -> (∃ N, ∀ n, (n > N)%nat -> f[n] < -M).

(* 2.2 收敛数列的性质 *)
(* 定理2.2: 唯一性 *)
Theorem Theorem2_2 : ∀ f a b, limit_seq f a -> limit_seq f b -> a = b.
Proof.
  intros x a b H0 H1. apply NNPP. intro H2. apply EqualLimit in H0 as H3.
  unfold limit_seq' in H3. destruct H3 as [H3 H4]. assert (H5 : ∣(b-a)∣/2 > 0).
  { assert (I1 : a > b \/ a < b).
    { destruct (total_order_T a b) as [[I2 | I2] | I2]; auto. exfalso; auto. }
    destruct I1 as [I1 | I1].
    - apply Rplus_lt_compat_l with (r := -a) in I1 as I2. rewrite Rplus_comm in I2. 
      pattern (-a + a) at 1 in I2. rewrite Rplus_comm in I2. 
      rewrite Rplus_opp_r in I2. apply Abs_lt in I2 as I3. 
      rewrite Ropp_plus_distr in I3. rewrite Ropp_involutive in I3.
      apply Rplus_lt_compat_l with (r := -b) in I1 as I4. rewrite Rplus_comm in I4. 
      rewrite Rplus_opp_r in I4. unfold Rminus. rewrite I3. 
      assert (I5 : 0 < 2). { apply Rlt_0_2. }
      apply Rinv_0_lt_compat in I5. unfold Rdiv.
      apply Rmult_lt_compat_l with (r := /2) in I4; auto.
      rewrite Rmult_0_r in I4. rewrite Rmult_comm in I4. auto.
    - apply Rplus_lt_compat_l with (r := -a) in I1 as I2. rewrite Rplus_comm in I2. 
      pattern (-a + b) at 1 in I2. rewrite Rplus_comm in I2. 
      rewrite Rplus_opp_r in I2. unfold Rminus.
      assert (I3 : ∣(b + -a)∣ = b + -a). { apply Abs_ge. left; auto. } rewrite I3. 
      assert (I4 : /2 > 0). { apply Rinv_0_lt_compat. apply Rlt_0_2. }
      apply Rmult_lt_compat_l with (r := /2) in I2; auto.
      rewrite Rmult_0_r in I2. rewrite Rmult_comm in I2. unfold Rdiv. auto. }
  apply H4 in H5 as H6.
  assert (H7 : \{ λ u, x [u] ∈ U(b; ∣(b - a)∣/2) \}
    ⊂ \{ λ u, x [u] ∉ U(a; ∣(b - a)∣/2) \}).
  { intros z I1. applyClassifier1 I1. apply <- Classifier1. applyClassifier1 I1. intro I2. 
    applyClassifier1 I2. apply Abs_R in I1. apply Abs_R in I2. destruct I1 as [I1 I3]. 
    destruct I2 as [I2 I4]. assert (I5 : b-a>=0 \/ b-a<0).
    { destruct (total_order_T (b-a) 0) as [[I5 | I5] | I5].
      - right; auto.
      - left; right; auto.
      - left; left; auto. }
    assert (I6 : ∣(b-a)∣ = a-b \/ ∣(b-a)∣ = b-a).
    { destruct I5 as [I5 | I5].
      - right. apply Abs_ge. auto.
      - left. apply Abs_lt in I5. rewrite I5. apply Ropp_minus_distr. }
    destruct I6 as [I6 | I6].
    - rewrite I6 in *. unfold Rminus in *.
      apply Rplus_lt_compat_r with (r := b) in I3. rewrite Rplus_assoc in I3. 
      rewrite Rplus_opp_l in I3. rewrite Rplus_0_r in I3. unfold Rdiv in *.
      assert (I7 : b = 2 * b * /2).
      { assert ( I7 : b * 2 = 2 * b). { apply Rmult_comm. }
        apply Rmult_eq_compat_r with (r := /2) in I7.
        assert (I8 : 2 <> 0). { apply Rgt_not_eq. apply Rlt_0_2. }
        rewrite Rinv_r_simpl_l in I7; auto. }
      pattern b at 2 in I3. rewrite I7 in I3. rewrite <- Rmult_plus_distr_r in I3.
      assert (I8 : a + -b + 2 * b = a + b).
      { assert (J1 : a + -b + 2 * b = a + (-b + 2 * b)). { apply Rplus_assoc. }
        rewrite J1. apply Rplus_eq_compat_l.
        assert (J2 : 2 * b = b + b). lra.
        apply Rplus_eq_compat_l with (r := -b) in J2. rewrite <- Rplus_assoc in J2.
        rewrite Rplus_opp_l in J2. rewrite Rplus_0_l in J2. auto. }
      rewrite I8 in I3. apply Rplus_lt_compat_r with (r := a) in I2.
      pattern (x[z] + - a + a) at 1 in I2. rewrite Rplus_assoc in I2.
      rewrite Rplus_opp_l in I2. rewrite Rplus_0_r in I2.
      assert (I9 : - ((a + - b) * / 2) + a = (a + b) * / 2).
      { assert (I9 : a = 2 * a * /2).
        { assert ( I9 : a * 2 = 2 * a). { apply Rmult_comm. }
          apply Rmult_eq_compat_r with (r := /2) in I9.
          assert (I10 : 2 <> 0). { apply Rgt_not_eq. apply Rlt_0_2. }
          rewrite Rinv_r_simpl_l in I9; auto. }
        rewrite Ropp_mult_distr_l. pattern a at 2. rewrite I9. 
        rewrite <- Rmult_plus_distr_r. rewrite Ropp_plus_distr. 
        rewrite Ropp_involutive. rewrite Rplus_assoc. pattern (b + 2 * a) at 1.
        rewrite Rplus_comm. rewrite <- Rplus_assoc.
        assert (I10 : - a + 2 * a = a).
        { assert (J1 : 2 * a = a + a). lra.
          apply Rplus_eq_compat_l with (r := -a) in J1. 
          rewrite <- Rplus_assoc in J1.
          rewrite Rplus_opp_l in J1. rewrite Rplus_0_l in J1. auto. }
        rewrite I10. auto. }
      rewrite I9 in I2. apply Rlt_asym in I3. auto.
    - rewrite I6 in *. unfold Rminus in *. unfold Rdiv in *.
      apply Rplus_lt_compat_r with (r := b) in I1.
      pattern (x [z] + - b + b) at 1 in I1. rewrite Rplus_assoc in I1.
      rewrite Rplus_opp_l in I1. rewrite Rplus_0_r in I1.
      assert (I9 : - ((b + - a) * / 2) + b = (b + a) * / 2).
      { assert (I9 : b = 2 * b * /2). 
          { assert ( I9 : b * 2 = 2 * b). { apply Rmult_comm. }
          apply Rmult_eq_compat_r with (r := /2) in I9.
          assert (I10 : 2 <> 0). { apply Rgt_not_eq. apply Rlt_0_2. }
          rewrite Rinv_r_simpl_l in I9; auto. }
        rewrite Ropp_mult_distr_l. pattern b at 2. rewrite I9. 
        rewrite <- Rmult_plus_distr_r. rewrite Ropp_plus_distr. 
        rewrite Ropp_involutive. rewrite Rplus_assoc. pattern (a + 2 * b) at 1.
        rewrite Rplus_comm. rewrite <- Rplus_assoc.
        assert (I10 : - b + 2 * b = b). 
          { assert (J1 : 2 * b = b + b). lra.
          apply Rplus_eq_compat_l with (r := -b) in J1.
          rewrite <- Rplus_assoc in J1. rewrite Rplus_opp_l in J1. 
          rewrite Rplus_0_l in J1. auto. }
        rewrite I10. auto. }
      rewrite I9 in I1. apply Rplus_lt_compat_r with (r := a) in I4.
      rewrite Rplus_assoc in I4. rewrite Rplus_opp_l in I4. 
      rewrite Rplus_0_r in I4.
      assert (I7 : a = 2 * a * /2).
      { assert ( I7 : a * 2 = 2 * a). { apply Rmult_comm. }
        apply Rmult_eq_compat_r with (r := /2) in I7.
        assert (I8 : 2 <> 0). { apply Rgt_not_eq. apply Rlt_0_2. }
        rewrite Rinv_r_simpl_l in I7; auto. }
      pattern a at 2 in I4. rewrite I7 in I4. rewrite <- Rmult_plus_distr_r in I4.
      assert (I8 : b + - a + 2 * a = b + a).
      { assert (J1 : b + - a + 2 * a = b + (-a + 2 * a)). { apply Rplus_assoc. }
        rewrite J1. apply Rplus_eq_compat_l.
        assert (J2 : 2 * a = a + a). lra.
        apply Rplus_eq_compat_l with (r := -a) in J2. rewrite <- Rplus_assoc in J2.
        rewrite Rplus_opp_l in J2. rewrite Rplus_0_l in J2. auto. }
      rewrite I8 in I4. apply Rlt_asym in I4. auto. }
  apply SubSetFinite in H7 as H8; auto. unfold limit_seq in H1. 
  destruct H1 as [H1 H10]. apply H10 in H5 as H11. destruct H8 as [H8 | H8].
  - apply finite_maxN in H8 as H9. destruct H9 as [N1 H9]. 
    destruct H11 as [N2 H11].
    unfold maxN in H9. destruct H9 as [H9 H12]. applyClassifier1 H9.
    destruct (Nat.le_gt_cases N1 N2) as [I1 | I1].
    + apply Nat.le_le_succ_r in I1 as I2.
      assert (I3 : ((S N2) > N2)%nat). lia.
      apply H11 in I3 as I4.
      assert (I5 : (S N2) ∈ \{ λ u, x [u] ∈ U(b; ∣(b - a)∣/2) \}).
      { apply <- Classifier1. apply <- Classifier1. auto. }
      apply H12 in I5 as I6. lia.
    + assert (I2 : ((S N1) > N2)%nat). lia.
      apply H11 in I2 as I3.
      assert (I4 : (S N1) ∈ \{ λ u, x [u] ∈ U(b; ∣(b - a)∣/2) \}).
      { apply <- Classifier1. apply <- Classifier1. auto. }
      apply H12 in I4. assert (I5 : (N1 < (S N1))%nat). 
      { apply Nat.lt_succ_diag_r. } lia.
  - destruct H11 as [N H11]. assert (H12 : ((S N) > N)%nat). lia.
    apply H11 in H12 as H13.
    assert (H14 : (S N) ∈ \{ λ u, x [u] ∈ U(b; ∣(b - a)∣/2) \}).
    { apply <- Classifier1. apply <- Classifier1. auto. }
    rewrite H8 in H14. applyClassifier1 H14. auto.
Qed.

Corollary lim_a : ∀ f a, limit_seq f a -> lim f = a.
Proof.
  intros f a H0. assert (H1 : lim f ∈ \{ λ a, limit_seq f a \}).
  { assert (H1 : NotEmpty \{ λ a, limit_seq f a \}).
    { unfold NotEmpty. exists a. apply <- Classifier1. auto. }
    apply Axiomc in H1. apply H1. }
  applyClassifier1 H1. apply Theorem2_2 with (f := f); auto.
Qed.

(* 定理2.3: 有界性 *)
Lemma Lemma2_3 : ∀ f, Convergence f -> (∃ M, ∀ n, ∣(f[n])∣ <= M).
Proof.
  intros f H0. unfold Convergence in H0. destruct H0 as [a H0].
  unfold limit_seq in H0. destruct H0 as [H0 H1]. assert (H2 : 1 > 0).
  { apply Rlt_0_1. }
  apply H1 in H2 as H3. destruct H3 as [N H3].
  assert (H4 : ∀ N2, ∃ M1, ∀ n : nat, (n <= N2)%nat -> ∣(f[n])∣ <= M1).
  { intro N2. induction N2 as [|N2 H4].
    - exists (∣(f[0%nat])∣). intros n I1. assert (n = 0)%nat. lia.
      rewrite H. right; auto.
    - destruct H4 as [M1 H4]. destruct (Rge_lt M1 (∣(f[S N2])∣)) as [I1 | I1].
      + exists M1. intros n I2. apply Nat.le_succ_r in I2.
        destruct I2 as [I2 | I2]; auto. rewrite I2. destruct I1 as [I1 | I1];
        [left | right]; auto.
      + exists (∣(f[S N2])∣). intros n I2. apply Nat.le_succ_r in I2.
        destruct I2 as [I2 | I2].
        * apply H4 in I2. left. destruct I2 as [I2 | I2].
          -- apply Rlt_trans with (r2 := M1); auto.
          -- rewrite I2; auto.
        * rewrite I2. right; auto. }
  assert (H5 : ∃ M1, ∀ n, (n <= N)%nat -> ∣(f[n])∣ <= M1). auto.
  destruct H5 as [M1 H5]. destruct (Rge_lt a 0) as [H6 | H6].
  - assert (H7 : ∀ n, (n > N)%nat -> ∣(f[n])∣ < 1 + a).
    { intros n I1. apply H3 in I1. apply Abs_R in I1 as I2.
      destruct I2 as [I2 I3]. apply Abs_R.
      apply Rplus_lt_compat_r with (r := a) in I3. unfold Rminus in I3.
      rewrite Rplus_assoc in I3. rewrite Rplus_opp_l in I3.
      rewrite Rplus_0_r in I3. split; auto.
      apply Rplus_lt_compat_r with (r := a) in I2. unfold Rminus in I2.
      rewrite Rplus_assoc in I2. rewrite Rplus_opp_l in I2.
      rewrite Rplus_0_r in I2. rewrite Ropp_plus_distr.
      apply Rge_le in H6 as I4. apply Ropp_0_le_ge_contravar in I4 as I5.
      apply Rge_le in I5 as I6.
      assert (I7 : -a <= a).
      { apply Rle_trans with (r2 := 0); auto. }
      apply Rplus_le_compat_l with (r := -(1)) in I7.
      destruct I7 as [I7 | I7].
      - apply Rlt_trans with (r2 := - (1) + a); auto.
      - rewrite I7. auto. }
    destruct (Rge_lt M1 (1 + a)) as [H8 | H8].
    + exists M1. intro n. destruct (Nat.le_gt_cases n N) as [H9 | H9]; auto.
      apply H7 in H9. destruct H8 as [H8 | H8].
      * left. apply Rlt_trans with (r2 := 1 + a); auto.
      * rewrite H8. left; auto.
    + exists (1 + a). intro n. destruct (Nat.le_gt_cases n N) as [H9 | H9].
      * apply H5 in H9. left. destruct H9 as [H9 | H9].
        -- apply Rlt_trans with (r2 := M1); auto.
        -- rewrite H9; auto.
      * apply H7 in H9. left; auto.
  - assert (H7 : ∀ n, (n > N)%nat -> ∣(f[n])∣ < 1 - a).
    { intros n I1. apply H3 in I1. apply Abs_R in I1 as I2.
      destruct I2 as [I2 I3]. apply Abs_R.
      apply Rplus_lt_compat_r with (r := a) in I2. unfold Rminus in I2.
      rewrite Rplus_assoc in I2. rewrite Rplus_opp_l in I2.
      rewrite Rplus_0_r in I2. unfold Rminus. rewrite Ropp_plus_distr.
      rewrite Ropp_involutive. split; auto.
      apply Rplus_lt_compat_r with (r := a) in I3. unfold Rminus in I3.
      rewrite Rplus_assoc in I3. rewrite Rplus_opp_l in I3.
      rewrite Rplus_0_r in I3. apply Ropp_gt_lt_0_contravar in H6 as I4.
      assert (I5 : a < -a).
      { apply Rlt_trans with (r2 := 0); auto. }
      apply Rplus_lt_compat_l with (r := 1) in I5.
      apply Rlt_trans with (r2 := 1 + a); auto. }
    destruct (Rge_lt M1 (1 - a)) as [H8 | H8].
    + exists M1. intro n. destruct (Nat.le_gt_cases n N) as [H9 | H9]; auto.
      apply H7 in H9. destruct H8 as [H8 | H8].
      * left. apply Rlt_trans with (r2 := 1 - a); auto.
      * rewrite H8. left; auto.
    + exists (1 - a). intro n. destruct (Nat.le_gt_cases n N) as [H9 | H9].
      * apply H5 in H9. left. destruct H9 as [H9 | H9].
        -- apply Rlt_trans with (r2 := M1); auto.
        -- rewrite H9; auto.
      * apply H7 in H9. left; auto.
Qed.

Theorem Theorem2_3 : ∀ x, Convergence x -> (∃ M, M > 0 /\ (∀ n, ∣(x[n])∣ <= M)).
Proof.
  intros x H0. apply Lemma2_3 in H0 as H1. destruct H1 as [M H1].
  assert (H2 : M >= 0).
  { generalize (H1 0%nat). intro H2. apply Rle_ge.
    apply Rle_trans with (r2 := ∣(x[0%nat])∣); auto. apply Rge_le.
    apply Abs_Rge0. }
  destruct H2 as [H2 | H2].
  - exists M. split; auto.
  - exists (M+1). split.
    + rewrite H2. rewrite Rplus_0_l. apply Rlt_0_1.
    + intro n. generalize (H1 n). intro H3.
      apply Rle_trans with (r2 := M); auto.
      left. apply Rlt_n_Sn.
Qed.

(* 定理2.4: 保号性 *)
Theorem Theorem2_4a : ∀ x a, limit_seq x a -> a > 0 
  -> (∀ a', a' ∈ \(0, a\) -> (∃ N, (∀ n, (n > N)%nat -> x[n] > a'))).
Proof.
  intros x a H0 H1 a' H2. applyClassifier1 H2. destruct H2 as [H2 H3].
  unfold limit_seq in H0. destruct H0 as [H0 H4].
  assert (H5 : a - a' > 0).
  { apply Rgt_minus. auto. }
  apply H4 in H5 as H6. destruct H6 as [N H6]. exists N. intros n H7.
  apply H6 in H7 as H8. apply Abs_R in H8. destruct H8 as [H8 H9].
  rewrite Ropp_minus_distr in H8. apply Rplus_lt_reg_r with (r := -a).
  apply H8.
Qed.

Corollary Corollary2_4a : ∀ x a b, limit_seq x b -> a < b
  -> (∃ N, (∀ n, (n > N)%nat -> (a + b)/2 < x[n])).
Proof.
  intros. set (z := \{\ λ n v, v = x[n] - a \}\).
  assert (IsSeq z).
  { split. red; intros. applyClassifier2 H1. applyClassifier2 H2. rewrite H1, H2; auto.
    apply AxiomI; split; intros. applyClassifier1 H1. destruct H1.
    apply Classifier1; auto. apply Classifier1. exists (x[z0] - a).
    apply Classifier2; auto. }
  assert (∀ n, z[n] = x[n] - a).
  { intros. assert (n ∈ dom[z]).
    { destruct H1. rewrite H2. apply Classifier1; auto. }
    destruct H1. apply x_fx_T in H2; auto. applyClassifier2 H2; auto. }
  assert (limit_seq z (b - a)).
  { split; auto. intros. destruct H. apply H4 in H3 as [N]. exists N. intros.
    rewrite H2. replace (x[n] - a - (b - a)) with (x[n] - b); [auto | lra]. }
  assert (b - a > 0) by lra. pose proof (Theorem2_4a z (b - a) H3 H4).
  assert ((b - a)/2 ∈ \(0, b - a\)). { apply Classifier1; lra. }
  apply H5 in H6 as [N]. exists N. intros. apply H6 in H7. rewrite H2 in H7. lra.
Qed.

Theorem Theorem2_4b : ∀ x a, limit_seq x a -> a < 0 
  -> (∀ a', a' ∈ \(a, 0\) -> (∃ N, (∀ n, (n > N)%nat -> x[n] < a'))).
Proof.
  intros x a H0 H1 a' H2. applyClassifier1 H2. destruct H2 as [H2 H3].
  unfold limit_seq in H0. destruct H0 as [H0 H4].
  assert (H5 : a' - a > 0).
  { apply Rgt_minus. auto. }
  apply H4 in H5 as H6. destruct H6 as [N H6]. exists N. intros n H7.
  apply H6 in H7 as H8. apply Abs_R in H8. destruct H8 as [H8 H9].
  apply Rplus_lt_reg_r with (r := -a). auto.
Qed.

Corollary Corollary2_4b : ∀ x a b, limit_seq x a -> a < b
  -> (∃ N, (∀ n, (n > N)%nat -> x[n] < (a + b)/2)).
Proof.
  intros. set (z := \{\ λ n v, v = x[n] - b \}\).
  assert (IsSeq z).
  { split. red; intros. applyClassifier2 H1. applyClassifier2 H2. rewrite H1, H2; auto.
    apply AxiomI; split; intros. applyClassifier1 H1. destruct H1.
    apply Classifier1; auto. apply Classifier1. exists (x[z0] - b).
    apply Classifier2; auto. }
  assert (∀ n, z[n] = x[n] - b).
  { intros. assert (n ∈ dom[z]).
    { destruct H1. rewrite H2. apply Classifier1; auto. }
    destruct H1. apply x_fx_T in H2; auto. applyClassifier2 H2; auto. }
  assert (limit_seq z (a - b)).
  { split; auto. intros. destruct H. apply H4 in H3 as [N]. exists N. intros.
    rewrite H2. replace (x[n] - b - (a - b)) with (x[n] - a); [auto | lra]. }
  assert (a - b < 0) by lra. pose proof (Theorem2_4b z (a - b) H3 H4).
  assert ((a - b)/2 ∈ \(a - b, 0\)). { apply Classifier1; lra. }
  apply H5 in H6 as [N]. exists N. intros. apply H6 in H7. rewrite H2 in H7. lra.
Qed.

Corollary Corollary2_4 : ∀ x y a b, limit_seq x a -> limit_seq y b -> a < b
  -> (∃ N, (∀ n, (n > N)%nat -> x[n] < y[n])).
Proof.
  intros. apply (Corollary2_4b x a b) in H as [N1]; auto.
  apply (Corollary2_4a y a b) in H0 as [N2]; auto. exists (Nat.max N1 N2).
  intros. apply (Rlt_trans _ ((a + b)/2)); [apply H | apply H0].
  apply (Nat.le_lt_trans N1 (Nat.max N1 N2)); auto. lia.
  apply (Nat.le_lt_trans N2 (Nat.max N1 N2)); auto. lia.
Qed.

Lemma Max_nat_3 : ∀ N0 N1 N2, ∃ N, (N > N0 /\ N > N1 /\ N > N2)%nat.
Proof.
  intros N0 N1 N2.
  destruct (Nat.le_gt_cases N0 N1) as [H6 | H6].
  - destruct (Nat.le_gt_cases N1 N2) as [H7 | H7].
    + exists (S N2). lia.
    + exists (S N1). lia.
  - destruct (Nat.le_gt_cases N0 N2) as [H7 | H7].
    + exists (S N2). lia.
    + exists (S N0). lia.
Qed.

(* 定理2.5: 保不等式性 *)
Theorem Theorem2_5 : ∀ x y, Convergence x -> Convergence y 
  -> (∃ N0, ∀ n, (n > N0)%nat -> x[n] <= y[n]) -> lim x <= lim y.
Proof.
  intros x y H0 H1 H2. destruct H2 as [N0 H2].
  destruct H0 as [a H0]. destruct H1 as [b H1].
  assert (H3 : ∀ ε, ε > 0 -> a < b + (ε + ε)).
  { intros ε H3. apply H0 in H3 as H4. destruct H4 as [N1 H4].
    apply H1 in H3 as H5. destruct H5 as [N2 H5].
    destruct (Max_nat_3 N0 N1 N2) as [N [H6 [H7 H8]]].
    apply H2 in H6. apply H4 in H7.
    apply H5 in H8. apply Abs_R in H7. apply Abs_R in H8.
    destruct H7 as [H7 H9]. destruct H8 as [H8 H10].
    apply Rplus_lt_compat_r with (r := a) in H7.
    unfold Rminus in H7. rewrite Rplus_assoc in H7. rewrite Rplus_opp_l in H7.
    rewrite Rplus_0_r in H7. apply Rplus_lt_compat_r with (r := b) in H10.
    unfold Rminus in H10. rewrite Rplus_assoc in H10.
    rewrite Rplus_opp_l in H10. rewrite Rplus_0_r in H10.
    assert (H11 : x[N] < ε + b).
    { apply Rle_lt_trans with (r2 := y[N]); auto. }
    rewrite <- Rplus_assoc. assert (H12 : - ε + a < ε + b).
    { apply Rlt_trans with (r2 := x[N]); auto. }
    rewrite Rplus_comm in H12. pattern (ε + b) in H12.
    rewrite Rplus_comm in H12. apply Rplus_lt_compat_r with (r := ε) in H12.
    rewrite Rplus_assoc in H12. rewrite Rplus_opp_l in H12.
    rewrite Rplus_0_r in H12. auto. }
  apply lim_a in H0 as H4. apply lim_a in H1 as H5.
  rewrite H4. rewrite H5. apply NNPP. intro H6. apply Rnot_le_gt in H6 as H7.
  generalize Rlt_0_2. intro H8.
  apply Rplus_gt_compat_l with (r := a) in H7 as H9.
  generalize (Rplus_diag b). intro H10.
  apply Rplus_eq_compat_r with (r := -b) in H10.
  pattern (b + b + - b) in H10. rewrite Rplus_assoc in H10.
  rewrite Rplus_opp_r in H10. rewrite Rplus_0_r in H10.
  rewrite H10 in H9. rewrite (Rplus_diag a) in H9.
  rewrite <- Rplus_assoc in H9. pattern (a + 2 * b) in H9.
  rewrite Rplus_comm in H9. rewrite Rplus_assoc in H9.
  apply Rinv_0_lt_compat in H8 as H11.
  apply Rmult_gt_compat_r with (r := /2) in H9 as H12; auto.
  apply Rgt_not_eq in H8 as H13. rewrite Rinv_r_simpl_m in H12; auto.
  rewrite Rmult_plus_distr_r in H12. rewrite Rinv_r_simpl_m in H12; auto.
  assert (H14 : (a + - b) > 0).
  { apply Rplus_gt_compat_r with (r := -b) in H7 as H14.
    rewrite Rplus_opp_r in H14. auto. }
  assert (H15 : (a + - b) * /2 > 0).
  { apply Rmult_gt_0_compat; auto. }
  assert (H16 : (a + - b) * /2 * /2 > 0).
  { apply Rmult_gt_0_compat; auto. }
  apply H3 in H16 as H17. rewrite Rplus_diag in H17.
  rewrite <-Rmult_assoc in H17. rewrite Rinv_r_simpl_m in H17; auto.
  apply Rlt_asym in H17. auto.
Qed.

Corollary Corollary2_5a : ∀ x x0 a, limit_seq x x0
  -> (∃ N0, ∀ n, (N0 < n)%nat -> a <= x[n]) -> a <= x0.
Proof.
  intros x x0 a H0 [N0 H1].
  assert (H2 : ∃ y, y = \{\ λ (n : nat) v, v = a \}\).
  { exists (\{\ λ (n : nat) v, v = a \}\); reflexivity. }
  destruct H2 as [y H2]. assert (H3 : IsSeq y).
  { split.
    - intros n v1 v2 I1 I2. rewrite H2 in I1; rewrite H2 in I2.
      applyClassifier2 I1; applyClassifier2 I2. rewrite I2. assumption.
    - apply AxiomI. intro n; split; intro I1.
      + apply Classifier1. reflexivity.
      + apply Classifier1. exists a. rewrite H2. apply Classifier2.
        reflexivity. }
  assert (H7 : ∀ n, y[n] = a).
  { intro n. apply f_x_T; try apply H3. rewrite H2. apply Classifier2.
    reflexivity. }
  assert (H4 : limit_seq y a).
  { split; auto. intros ε I1. exists 0%nat. intros n I2.
    rewrite H7. unfold Rminus. rewrite Rplus_opp_r.
    rewrite Abs_ge; lra. }
  apply lim_a in H0 as H5. apply lim_a in H4 as H6.
  rewrite <- H5; rewrite <- H6. apply Theorem2_5.
  - exists a. assumption.
  - exists x0. assumption.
  - exists N0. intros n H8. rewrite H7. apply H1. assumption.
Qed.

Corollary Corollary2_5b : ∀ x x0 a, limit_seq x x0
  -> (∃ N0, ∀ n, (N0 < n)%nat -> x[n] <= a) -> x0 <= a.
Proof.
  intros x x0 a H0 [N0 H1].
  assert (H2 : ∃ y, y = \{\ λ (n : nat) v, v = a \}\).
  { exists (\{\ λ (n : nat) v, v = a \}\); reflexivity. }
  destruct H2 as [y H2]. assert (H3 : IsSeq y).
  { split.
    - intros n v1 v2 I1 I2. rewrite H2 in I1; rewrite H2 in I2.
      applyClassifier2 I1; applyClassifier2 I2. rewrite I2. assumption.
    - apply AxiomI. intro n; split; intro I1.
      + apply Classifier1. reflexivity.
      + apply Classifier1. exists a. rewrite H2. apply Classifier2.
        reflexivity. }
  assert (H7 : ∀ n, y[n] = a).
  { intro n. apply f_x_T; try apply H3. rewrite H2. apply Classifier2.
    reflexivity. }
  assert (H4 : limit_seq y a).
  { split; auto. intros ε I1. exists 0%nat. intros n I2.
    rewrite H7. unfold Rminus. rewrite Rplus_opp_r.
    rewrite Abs_ge; lra. }
  apply lim_a in H0 as H5. apply lim_a in H4 as H6.
  rewrite <- H5; rewrite <- H6. apply Theorem2_5.
  - exists x0. assumption.
  - exists a. assumption.
  - exists N0. intros n H8. rewrite H7. apply H1. assumption.
Qed.

(* 定理2.6 迫敛性*)
Theorem Theorem2_6 : ∀ x y z a, limit_seq x a -> limit_seq y a -> IsSeq z 
  -> (∃ N, ∀ n, (n > N)%nat -> x[n] <= z[n] <= y[n]) -> limit_seq z a.
Proof.
  intros x y z a H1 H2 H3 H4. destruct H4 as [N H4]. unfold limit_seq in *.
  split; auto. intros ε H5. destruct H1 as [H1 H6]. destruct H2 as [H2 H7].
  apply H6 in H5 as H8. apply H7 in H5 as H9.
  destruct H9 as [N2 H9]. destruct H8 as [N1 H8].
  destruct (Max_nat_3 N N1 N2) as [N0 [H10 [H11 H12]]]. exists N0. intros n H13.
  assert (n > N /\ n > N1 /\ n > N2)%nat as [H14[H15 H16]]. lia.
  apply H4 in H14 as H17. apply H9 in H16 as H19. apply H8 in H15 as H18.
  apply Abs_R. apply Abs_R in H18. apply Abs_R in H19.
  destruct H17 as [H17 H20]. destruct H18 as [H18 H21].
  apply Rplus_lt_compat_r with (r := a) in H18. destruct H19 as [H19 H22].
  apply Rplus_lt_compat_r with (r := a) in H22.
  unfold Rminus in *. rewrite Rplus_assoc in H18. rewrite Rplus_opp_l in H18.
  rewrite Rplus_0_r in H18. rewrite Rplus_assoc in H22.
  rewrite Rplus_opp_l in H22. rewrite Rplus_0_r in H22. split.
  - apply Rplus_lt_reg_r with (r := a). rewrite Rplus_assoc.
    rewrite Rplus_opp_l. rewrite Rplus_0_r.
    apply Rlt_le_trans with (r2 := x[n]); auto.
  - apply Rplus_lt_reg_r with (r := a). rewrite Rplus_assoc.
    rewrite Rplus_opp_l. rewrite Rplus_0_r.
    apply Rle_lt_trans with (r2 := y[n]); auto.
Qed.

Lemma Max_nat_2 : ∀ N0 N1, ∃ N, (N > N0 /\ N > N1)%nat.
Proof.
  intros N0 N1. generalize (Max_nat_3 N0 N1 N1). intro H0.
  destruct H0 as [N [H0 [H1 H2]]]. exists N. split; auto.
Qed.

(* 定理2.7 四则运算法则 *)
(* x,y是收敛数列,则 x+y 收敛,且有 lim(x+y) = limx+limy *)
Theorem Theorem2_7a : ∀ x y, Convergence x -> Convergence y 
  -> Convergence \{\ λ n v, v = x[n] + y[n] \}\ 
  /\ lim \{\ λ n v, v = x[n] + y[n] \}\ = lim x + lim y.
Proof.
  intros x y H0 H1. destruct H0 as [a H0]. destruct H1 as [b H1].
  assert (H2 : ∀ ε, ε > 0 -> (∃ N : nat, ∀ n : nat, (n > N)%nat ->
    ∣((x[n]+y[n]) - (a+b))∣ < 2 * ε)).
  { intros ε H2. apply H0 in H2 as H3. destruct H3 as [N1 H3].
    apply H1 in H2 as H4. destruct H4 as [N2 H4].
    generalize (Max_nat_2 N1 N2). intro H5.
    destruct H5 as [N [H5 H6]]. exists N. intros n H7.
    assert (n > N1 /\ n > N2)%nat as [H8 H9]. lia.
    apply H3 in H8 as H10. apply H4 in H9 as H11.
    assert (H12 : ∣(x[n] - a)∣ + ∣(y[n] - b)∣ < ε + ε).
    { apply Rplus_lt_compat; auto. } rewrite Rplus_diag in H12.
    assert (H13 : x [n] + y [n] - (a + b) = x[n] - a + (y[n] - b)). field.
    rewrite H13. generalize (Abs_plus_le (x[n]-a) (y[n]-b)).
    intro H14. eapply Rle_lt_trans; eauto. }
  assert (H3 : limit_seq \{\ λ n v, v = x[n] + y[n] \}\ (a+b)).
  { unfold limit_seq. assert (H3 : Function \{\ λ n v, v = x[n] + y[n] \}\).
    { unfold Function. intros x0 y0 z0 I1 I2. applyClassifier2 I1.
      applyClassifier2 I2. rewrite I2; auto. }
    split.
    - split; auto. apply AxiomI. intro z; split; intro I1.
      + apply <- Classifier1. auto.
      + apply <- Classifier1. exists (x[z] + y[z]). apply <- Classifier2.
        auto.
    - intros ε I1. generalize Rlt_0_2. intro I2.
      apply Rinv_0_lt_compat in I2 as I3.
      apply Rmult_gt_compat_r with (r := /2) in I1 as I4; auto.
      rewrite Rmult_0_l in I4. apply H2 in I4 as I5.
      destruct I5 as [N I5]. exists N. rewrite <- Rmult_assoc in I5.
      apply Rgt_not_eq in I2 as I6. rewrite Rinv_r_simpl_m in I5; auto.
      intros n I7.
      assert (I8 : \{\ λ n v, v = x[n] + y[n] \}\ [n] = x[n] + y[n] ).
      { apply f_x_T; auto. apply <- Classifier2. auto. }
      rewrite I8. auto. }
  split.
  - exists (a+b). auto.
  - apply lim_a in H0 as H4. apply lim_a in H1 as H5.
    rewrite H4; rewrite H5. apply lim_a. auto.
Qed.

Corollary Corollary2_7a : ∀ x y a b, limit_seq x a 
  -> limit_seq y b -> limit_seq \{\ λ n v, v = x[n] + y[n] \}\ (a + b).
Proof.
  intros x y a b H0 H1. apply lim_a in H0 as H3. apply lim_a in H1 as H4.
  assert (H5 : Convergence x). { exists a; auto. }
  assert (H6 : Convergence y). { exists b; assumption. }
  generalize (Theorem2_7a x y H5 H6). intros [H7 H8].
  rewrite H3 in H8; rewrite H4 in H8. unfold lim in H8.
  assert (H9 : NotEmpty \{  λ c, limit_seq
    \{\ λ(n : nat)(v : R), v = x [n] + y [n] \}\ c \}).
  { unfold NotEmpty. destruct H7 as [c H7].
    exists c. apply Classifier1. assumption. }
  apply Axiomc in H9. rewrite H8 in H9.
  applyClassifier1 H9. assumption.
Qed.

(* x,y是收敛数列,则 x-y 收敛,且有 lim(x-y) = limx-limy *)
Theorem Theorem2_7b : ∀ x y, Convergence x -> Convergence y 
  -> Convergence \{\ λ n v, v = x[n] - y[n] \}\ 
  /\ lim \{\ λ n v, v = x[n] - y[n] \}\ = lim x - lim y.
Proof.
  intros x y H0 H1. assert (H2 : ∃ y', y' = \{\ λ n v, v = -(y[n]) \}\ ).
  { exists \{\ λ n v, v = -(y[n]) \}\; auto. }
  destruct H2 as [y' H2]. assert (H3 : IsSeq y').
  { split.
    - unfold Function. intros x0 y0 z0 I1 I2. rewrite H2 in *.
      applyClassifier2 I1. applyClassifier2 I2. rewrite I2. auto.
    - apply AxiomI. intro z; split; intro I1.
      + apply <- Classifier1. auto.
      + apply <- Classifier1. rewrite H2. exists (-y[z]). apply <- Classifier2.
        auto. }
  assert (H4 : \{\ λ n v, v = x[n] - y[n] \}\ = \{\ λ n v, v = x[n] + y'[n] \}\).
  { assert (I0 : ∀ x0, y'[x0] = -y[x0]).
    { intro x0. destruct H3 as [H3 I1]. apply f_x_T; auto. rewrite H2.
      apply <- Classifier2. auto. }
    apply AxiomI. intro z; split; intro I1.
    - applyClassifier1 I1. destruct I1 as [x0 [y0 [I2 I3]]]. rewrite I2 in *.
      apply <- Classifier2. rewrite I0. auto.
    - applyClassifier1 I1. destruct I1 as [x0 [y0 [I2 I3]]]. rewrite I2 in *.
      apply <- Classifier2. rewrite I0 in I3. auto. }
  rewrite H4. generalize H1. intro H5. unfold limit_seq in H1.
  destruct H1 as [b H1]. assert (H6 : limit_seq y' (-b)).
  { split; auto. destruct H1 as [H1 I1]. intros ε I2. apply I1 in I2 as I3.
    destruct I3 as [N I3]. exists N. intros n I4.
    assert (I5 : y'[n] = -y[n]).
    { apply f_x_T; try apply H3. rewrite H2. apply <- Classifier2. auto. }
    rewrite I5. assert (I6 : -y[n] - -b = -(y[n] - b)). field.
    rewrite I6. rewrite <- Abs_eq_neg. auto. }
  assert (H7 : Convergence y').
  { exists (-b). auto. }
  apply (Theorem2_7a x y') in H7 as H8; auto. destruct H8 as [H8 H9].
  split; auto. assert (H10 : lim y' = - lim y).
  { apply lim_a in H1 as I1. rewrite I1. apply lim_a. auto. }
  rewrite H10 in H9. auto.
Qed.

Corollary Corollary2_7b : ∀ x y a b, limit_seq x a 
  -> limit_seq y b -> limit_seq \{\ λ n v, v = x[n] - y[n] \}\ (a - b).
Proof.
  intros x y a b H0 H1. apply lim_a in H0 as H3. apply lim_a in H1 as H4.
  assert (H5 : Convergence x). { exists a; auto. }
  assert (H6 : Convergence y). { exists b; assumption. }
  generalize (Theorem2_7b x y H5 H6). intros [H7 H8].
  rewrite H3 in H8; rewrite H4 in H8. unfold lim in H8.
  assert (H9 : NotEmpty \{  λ c, limit_seq
    \{\ λ (n : nat)(v : R), v = x [n] - y [n] \}\ c \}).
  { unfold NotEmpty. destruct H7 as [c H7]. exists c. apply Classifier1. assumption. }
  apply Axiomc in H9. rewrite H8 in H9. applyClassifier1 H9. assumption.
Qed.

(* x,y是收敛数列,则 x*y 收敛,且有 lim(x*y) = limx*limy *)
Theorem Theorem2_7c : ∀ x y, Convergence x -> Convergence y 
  -> Convergence \{\ λ n v, v = x[n] * y[n] \}\ 
  /\ lim \{\ λ n v, v = x[n] * y[n] \}\ = lim x * lim y.
Proof.
  intros x y H0 H1. apply Theorem2_3 in H1 as H2. destruct H2 as [M [I1 H2]].
  destruct H0 as [a H0]. destruct H1 as [b H1].
  assert (H3 : ∀ ε, ε > 0 -> (∃ N : nat, ∀ n : nat, (n > N)%nat
    -> ∣((x[n]*y[n]) - (a*b))∣ < (M + ∣a∣) * ε)).
  { intros ε H3. apply H0 in H3 as H4. destruct H4 as [N1 H4].
    apply H1 in H3 as H5. destruct H5 as [N2 H5].
    generalize (Max_nat_2 N1 N2). intro H6. destruct H6 as [N [H6 H7]].
    exists N. intros n H8.
    assert (H9 : x [n] * y [n] - a * b = (x[n] - a) * y[n] + a * (y[n] - b)).
    field. rewrite H9.
    generalize (Abs_plus_le ((x[n] - a) * y[n]) (a * (y[n] - b))). intro H10.
    apply Rle_lt_trans with (r2 :=
      ∣((x[n] - a) * y[n])∣ + ∣(a * (y[n] - b))∣); auto.
    repeat rewrite Abs_mult.
    assert (H11 : ∣(x[n] - a)∣ * ∣(y[n])∣ < M * ε).
    { generalize (H2 n). intro H11. assert (H12 : (n > N1)%nat). lia.
      apply H4 in H12 as H13. 
      assert (H14 : 0 <= ∣(y[n])∣). { apply Rge_le. apply Abs_Rge0. }
      assert (H15 : 0 <= ∣(x[n] - a)∣). { apply Rge_le. apply Abs_Rge0. }
      rewrite (Rmult_comm M ε). destruct H11 as [H11 | H11].
      - apply Rmult_le_0_lt_compat; auto.
      - rewrite H11. apply Rmult_lt_compat_r; auto. }
    assert (H13 : (n > N2)%nat). lia.
    apply H5 in H13 as H14. generalize (Abs_Rge0 a). intro H15.
    assert (H16 : ∣a∣ * ∣(y[n] - b)∣ <= ∣a∣ * ε).
    { destruct H15 as [H15 | H15].
      - left. apply Rmult_lt_compat_l; auto.
      - rewrite H15. repeat rewrite Rmult_0_l. right; auto. }
    rewrite Rmult_plus_distr_r. apply Rplus_lt_le_compat; auto. }
  assert (H4 : IsSeq \{\ λ n v, v = x[n] * y[n] \}\ ).
  { unfold IsSeq. split.
    - unfold Function. intros x0 y0 z0 I2 I3. applyClassifier2 I2.
      applyClassifier2 I3. rewrite I3. auto.
    - apply AxiomI. intro z; split; intro I2.
      + apply <- Classifier1. auto.
      + apply <- Classifier1. exists (x[z] * y[z]). apply <- Classifier2. auto. }
  assert (H5 : limit_seq \{\ λ n v, v = x[n] * y[n] \}\ (a*b) ).
  { split; auto. intros ε I2. assert (I3 : (M + ∣a∣) > 0).
    { rewrite <- (Rplus_0_l 0). apply Rplus_gt_ge_compat; auto.
      apply Abs_Rge0. }
    apply Rinv_0_lt_compat in I3 as I4.
    apply Rdiv_lt_0_compat with (a := ε) in I3 as I5; auto. apply H3 in I5 as I6.
    assert ( I7 : (M + ∣a∣) * (ε / (M + ∣a∣)) = ε).
    { field. apply Rgt_not_eq. auto. }
    rewrite I7 in I6. destruct I6 as [N I6]. exists N. intros n I8.
    apply I6 in I8 as I9.
    assert (I10 : \{\ λ n v, v = x[n] * y[n] \}\ [n] = x [n] * y [n] ).
    { apply f_x_T; try apply H4. apply <- Classifier2. auto. }
    rewrite I10. auto. }
  split.
  - exists (a*b). auto.
  - apply lim_a in H0 as H6. apply lim_a in H1 as H7. rewrite H6.
    rewrite H7. apply lim_a. auto.
Qed.

(* y是收敛数列,y(n),lim y均不等于0,则lim /y[n] = /(lim y)  *)
Lemma Lemma2_7d : ∀ y, Convergence y -> (∀ n, y[n] <> 0) -> lim y <> 0 
  -> limit_seq (\{\ λ n v, v = /y[n] \}\) (/(lim y)).
Proof.
  intros y H0 H1 H2. destruct H0 as [b H0].
  apply lim_a in H0 as H3. rewrite H3 in *.
  assert (H4 : ∃ N3 : nat, ∀ n : nat, (n > N3)%nat -> ∣(y[n])∣ > ∣b∣ / 2).
  { apply Rdichotomy in H2 as H4. destruct H4 as [H4 | H4].
    - assert (H5 : (b / 2) ∈ \(b, 0\)).
      { apply <- Classifier1. split.
        - unfold Rdiv. pattern b at 2. rewrite <- (Rmult_1_r b).
          assert (H5 : /2 < 1).
          { assert (H6 : 2 > 1).
            { generalize Rlt_0_1. intro H5.
              apply Rplus_lt_compat_l with (r := 1) in H5.
              rewrite Rplus_0_r in H5. assert (H6 : 1+1=2). field.
              rewrite H6 in H5. auto. }
            assert (H7 : 1 = /1). field. rewrite H7.
            apply Rinv_lt_contravar; auto. rewrite Rmult_1_l. apply Rlt_0_2. }
          apply Rmult_lt_gt_compat_neg_l; auto.
        - assert (H5 : /2 > 0).
          { apply Rinv_0_lt_compat. apply Rlt_0_2. }
          unfold Rdiv. rewrite <- (Rmult_0_l (/2)).
          apply Rmult_lt_compat_r; auto. }
      assert (H6 : (∀ a' : R, a' ∈ \(b, 0\) ->
        (∃ N, (∀ n, (n > N)%nat -> y[n] < a')))).
      { apply Theorem2_4b; auto. }
      apply H6 in H5 as H7. destruct H7 as [N H7]. exists N. intros n H8.
      assert (H9 : y[n] < 0).
      { apply H7 in H8. applyClassifier1 H5. destruct H5 as [H5 H9].
        apply Rlt_trans with (r2 := b/2); auto. }
      apply Abs_lt in H4 as H10. apply Abs_lt in H9 as H11.
      rewrite H10; rewrite H11. rewrite Rdiv_opp_l. apply Ropp_lt_gt_contravar.
      auto.
    - assert (H5 : (b / 2) ∈ \(0, b\)).
      { apply <- Classifier1. split.
        - assert (H5 : /2 > 0).
          { apply Rinv_0_lt_compat. apply Rlt_0_2. }
          unfold Rdiv. apply Rmult_gt_0_compat; auto.
        - unfold Rdiv. pattern b at 2. rewrite <- (Rmult_1_r b).
          assert (H5 : /2 < 1).
          { assert (H6 : 2 > 1).
            { generalize Rlt_0_1. intro H5.
              apply Rplus_lt_compat_l with (r := 1) in H5.
              rewrite Rplus_0_r in H5. assert (H6 : 1+1=2). field.
              rewrite H6 in H5. auto. }
            assert (H7 : 1 = /1). field. rewrite H7.
            apply Rinv_lt_contravar; auto. rewrite Rmult_1_l. apply Rlt_0_2. }
          apply Rmult_lt_compat_l; auto. }
      assert (H6 : (∀ a' : R, a' ∈ \(0, b\) ->
        (∃ N, (∀ n, (n > N)%nat -> y[n] > a')))).
      { apply Theorem2_4a; auto. }
      apply H6 in H5 as H7. destruct H7 as [N H7]. exists N. intros n H8.
      assert (H9 : y[n] > 0).
      { apply H7 in H8. applyClassifier1 H5. destruct H5 as [H5 H9].
        apply Rlt_trans with (r2 := b/2); auto. }
      apply Abs_gt in H4 as H10. apply Abs_gt in H9 as H11.
      rewrite H10; rewrite H11. auto. }
  assert (H5 : ∀ ε, ε > 0 -> (∃ N : nat, ∀ n : nat, (n > N)%nat ->
    ∣((/y[n]) - (/b))∣ < 2 * ε/(b*b))).
  { intros ε H5. apply H0 in H5 as H6. destruct H6 as [N2 H6].
    destruct H4 as [N3 H4]. generalize (Max_nat_2 N2 N3). intro H7.
    destruct H7 as [N [H7 H8]]. exists N. intros n H9.
    assert (H10 : (n > N2)%nat). lia.
    assert (H11 : (n > N3)%nat). lia.
    apply H4 in H11 as H12. apply H6 in H10 as H13.
    generalize (H1 n). intro H14.
    assert (H15 : /y[n] - /b = -((y[n] - b) / (y[n] * b))).
    { field; split; auto. }
    rewrite H15. rewrite <- Abs_eq_neg.
    generalize (Rmult_integral_contrapositive_currified y[n] b H14 H2).
    intro H16. rewrite Abs_div; auto. rewrite Abs_mult.
    assert (H17 : (∣b∣ / 2) * ∣(y[n])∣ > 0).
    { apply Abs_not_eq_0 in H14 as I1. apply Abs_not_eq_0 in H2 as I2.
      apply Rmult_gt_0_compat; auto. apply Rmult_gt_0_compat; auto.
      apply Rinv_0_lt_compat. apply Rlt_0_2. }
    apply Rinv_lt_contravar in H12 as H18; auto.
    unfold Rdiv in *. assert (H19 : ∣b∣ <> 0).
    { apply Rgt_not_eq. apply Abs_not_eq_0; auto. }
    assert (H20 : /2 <>0).
    { apply Rinv_neq_0_compat. apply Rgt_not_eq. apply Rlt_0_2. }
    rewrite Rinv_mult in H18; auto.
    assert (H21 : 2 <> 0).
    { apply Rgt_not_eq. apply Rlt_0_2. }
    rewrite Rinv_inv in H18; auto. assert (H22 : ∣(y[n])∣ <> 0).
    { apply Rgt_not_eq. apply Abs_not_eq_0. auto. }
    assert (H23 : / (∣(y[n])∣ * ∣b∣) > 0).
    { apply Rinv_0_lt_compat.
      apply Rmult_gt_0_compat; apply Abs_not_eq_0; auto. }
    apply Rmult_lt_compat_r with (r := / (∣(y[n])∣ * ∣b∣))
      in H13 as H24; auto.
    apply Rlt_trans with (r2 := ε * / (∣(y[n])∣ * ∣b∣)); auto.
    rewrite Rinv_mult; auto. rewrite <- Rmult_assoc.
    rewrite (Rmult_comm ε (/ ∣(y[n])∣)). rewrite Rmult_assoc.
    assert (H25 : ε * / ∣b∣ > 0).
    { apply Rmult_gt_0_compat; auto. apply Rinv_0_lt_compat.
      apply Abs_not_eq_0. auto. }
    apply Rmult_lt_compat_r with (r := ε * / ∣b∣) in H18 as H26; auto.
    assert (H27 : / ∣b∣ * 2 * (ε * / ∣b∣) =
      2 * ε * / (∣b∣ * ∣b∣)).
    { field; auto. }
    rewrite H27 in H26. assert (H28 : ∣b∣ * ∣b∣ = b * b).
    { apply Rdichotomy in H2 as I1. destruct I1 as [I1 | I1].
      - apply Abs_lt in I1 as I2. rewrite I2. field.
      - apply Abs_gt in I1 as I2. rewrite I2. auto. }
    rewrite <- H28. auto. }
  assert (I0 : IsSeq \{\ λ n v, v = /y[n] \}\ ).
  { split.
    - unfold Function. intros x0 y0 z0 H6 H7. applyClassifier2 H6.
      applyClassifier2 H7. rewrite H7; auto.
    - apply AxiomI. intro z; split; intro H6.
      + apply <- Classifier1; auto.
      + apply Classifier1. exists (/y[z]). apply Classifier2. auto. }
  split; auto.
  intros ε H6. assert (H7 : ε * (b * b) / 2 > 0).
  { unfold Rdiv. rewrite (Rmult_assoc ε (b*b) (/2)).
    apply Rmult_gt_0_compat; auto. assert (H7 : b * b > 0).
    { apply Rdichotomy in H2 as I1. destruct I1 as [I1 | I1].
      - apply Ropp_gt_lt_0_contravar in I1 as I2.
        assert (I3 : b*b = (-b)*(-b)). field. rewrite I3.
        apply Rmult_gt_0_compat; auto.
      - apply Rmult_gt_0_compat; auto. }
    apply Rmult_gt_0_compat; auto. apply Rinv_0_lt_compat. apply Rlt_0_2. }
  apply H5 in H7 as H8. assert (H9 : 2 * (ε * (b * b) / 2) / (b * b) = ε ).
  { field; auto. }
  rewrite H9 in H8. destruct H8 as [N H10]. exists N. intros n H11.
  assert (H12 : \{\ λ(n0 : nat)(v : R),v = / y [n0] \}\ [n] = /y[n]).
  { destruct I0 as [I0 I1]. apply f_x_T; auto. apply Classifier2. auto. }
  rewrite H12. auto.
Qed.

(* x y是收敛数列,y(n),lim y 均不为0,lim(x/y) = limx/limy *)
Theorem Theorem2_7d : ∀ x y, Convergence x -> Convergence y -> (∀ n, y[n] <> 0) 
  -> lim y <> 0 -> Convergence \{\ λ n v, v = x[n] / y[n] \}\ 
  /\ lim \{\ λ n v, v = x[n] / y[n] \}\ = lim x / lim y.
Proof.
  intros x y H0 H1 H2 H3. 
  assert (H4 : limit_seq \{\ λ n v, v = /y[n] \}\ (/(lim y))).
  { apply Lemma2_7d; auto. }
  assert (H5 : ∃ y', y' = \{\ λ n v, v = /y[n] \}\ ).
  { exists \{\ λ n v, v = /y[n] \}\. auto. } destruct H5 as [y' H5].
  assert (H6 : \{\ λ n v, v = x[n] / y[n] \}\ = \{\ λ n v, v = x[n] * y'[n] \}\).
  { apply AxiomI. intro z; split; intro I1.
    - applyClassifier1 I1. destruct I1 as [x0 [y0 [I1 I2]]]. rewrite I1 in *.
      apply Classifier2. assert (I3 : y'[x0] = /y[x0]).
      { rewrite H5. apply f_x_T; try apply H4. apply Classifier2. auto. }
      rewrite I3. auto.
    - applyClassifier1 I1. destruct I1 as [x0 [y0 [I1 I2]]]. rewrite I1 in *.
      apply Classifier2. assert (I3 : y'[x0] = /y[x0]).
      { rewrite H5. apply f_x_T; try apply H4. apply Classifier2. auto. }
      rewrite I3 in I2. auto. }
  rewrite H6. assert (H7 : Convergence y'). { rewrite H5. exists (/ lim y). auto. }
  assert (H8 : lim y' = / lim y). { rewrite H5. apply lim_a. auto. }
  unfold Rdiv. rewrite <- H8. apply Theorem2_7c; auto.
Qed.

(* 定义: nat型的严格增函数 *)
Definition StrictlyIncreaseFun_nat (f : @set (@prod nat nat)) := Function f 
  /\ (∀ x1 y1 x2 y2, [x1, y1] ∈ f -> [x2, y2] ∈ f -> x1 < x2 -> y1 < y2)%nat.

Fact fn_ge_n : ∀ f n, dom[f] = Full nat -> StrictlyIncreaseFun_nat f 
  -> (f[n] >= n)%nat.
Proof.
  intros f n H0. induction n as [|n IHn]; intro H1.
  - apply Nat.le_0_l.
  - apply IHn in H1 as H2. generalize (Nat.lt_succ_diag_r n). intro H3.
    assert (H4 : n ∈ dom[f]). { rewrite H0. apply Classifier1. auto. }
    assert (H5 : S n ∈ dom[f]). { rewrite H0. apply Classifier1. auto. }
    apply x_fx_T in H4 as H6; try apply H1.
    apply x_fx_T in H5 as H7; try apply H1.
    assert (H8 : (f[n] < f[S n])%nat).
    { destruct H1 as [H1 H8]. apply (H8 n f[n] (S n) f[S n]); auto. } lia.
Qed.

(* 定义1 子列(y 是 x 的子列) *)
Definition SubSeq x y := IsSeq x /\ IsSeq y  /\ (∃ f, StrictlyIncreaseFun_nat f 
  /\ dom[f] = Full nat /\ (∀ n : nat, y[n] = x[f[n]])).

(* 定理2.8 数列收敛的充要条件 *)
Theorem Theorem2_8 : ∀ x, IsSeq x 
 -> (Convergence x <-> (∀ y, SubSeq x y -> Convergence y)).
Proof.
  intros x H12. split.
  - intros H0 y H1. destruct H0 as [a H0]. destruct H1 as [H1 [H2 [f [H3 [H4 H5]]]]].
    exists a. unfold limit_seq. split; auto. intros ε H6. destruct H0 as [H0 H7]. 
    apply H7 in H6 as H8. destruct H8 as [N H8]. exists N. intros n H9. rewrite H5. 
    assert (H10 : (f[n] >= n)%nat). { apply fn_ge_n; auto. }
    assert (H11 : (f[n] > N)%nat). { apply Nat.lt_le_trans with (m := n); auto. }
    auto.
  - intro H0. assert (H1 : SubSeq x x).
    { split; auto; split; auto. exists (\{\ λ (u v : nat), u = v \}\).
      assert (H1 : Function \{\ λ (u v : nat), u = v \}\ ).
      { unfold Function. intros x0 y0 z0 I1 I2.
        applyClassifier2 I1. applyClassifier2 I2. rewrite <- I1. auto. }
      split; [idtac | split].
      - split; auto. intros x1 y1 x2 y2 I1 I2 I3. applyClassifier2 I1. 
        applyClassifier2 I2. rewrite <- I1; rewrite <- I2. auto.
      - apply AxiomI; split; intro I1.
        + apply Classifier1; auto.
        + apply Classifier1. exists z. apply Classifier2; auto.
      - intro n. assert (H2 : \{\ λ (u v : nat), u = v \}\[n] = n).
        { apply f_x_T; auto. apply Classifier2. auto. } rewrite H2. auto. }
    apply H0 in H1. auto.
Qed.

(* 收敛数列的任意子列具有相同极限 *)
Fact SubSeqEqual : ∀ x a, limit_seq x a -> (∀ y, SubSeq x y -> limit_seq y a).
Proof.
  intros x a H0 y H1. unfold SubSeq in H1. destruct H1 as [H1 [H2 [f [H3 [H4 H5]]]]].
  split; auto. intros ε H6. destruct H0 as [H0 H7]. apply H7 in H6 as [N H8].
  exists N. intros n H9. rewrite H5. generalize (fn_ge_n f n H4 H3). intro H10.
  apply H8. generalize (Nat.lt_le_trans N n f[n] H9 H10). intro H11. apply H11.
Qed.

(* 2.3 数列极限存在的条件 *)
(* 定义:单调增数列 *)
Definition IncreaseSeq x  := IsSeq x /\ (∀ n, x[n] <= x[S n]).
(* 定义:单调减数列 *)
Definition DecreaseSeq x := IsSeq x /\ (∀ n, x[n] >= x[S n]).

(* 定义: 单调数列 *)
Definition MonotonicSeq x := IncreaseSeq x \/ DecreaseSeq x.

(* 单调增数列的等价性 *)
Fact EqualIncrease : ∀ x, IncreaseSeq x 
  <-> (IsSeq x /\ (∀ n1 n2, (n1 < n2)%nat -> x[n1] <= x[n2])).
Proof.
  intro x; split; intro H0.
  - destruct H0 as [H0 H1]. split; auto. intros n1 n2. induction n2 as [|n2 IHn2].
    + intro H2. exfalso. apply (Nat.nlt_0_r n1). auto.
    + destruct (Nat.lt_total n1 n2) as [H2 | [H2 | H2]]; intro H3.
      * apply Rle_trans with (r2 := x[n2]); auto.
      * rewrite <- H2. auto.
      * exfalso. lia.
  - destruct H0 as [H0 H1]. split; auto.
Qed.

(* 单调减数列的等价性 *)
Fact EqualDecrease : ∀ x, DecreaseSeq x 
  <-> (IsSeq x /\ (∀ n1 n2, (n1 < n2)%nat -> x[n1] >= x[n2])).
Proof.
  intro x; split; intro H0.
  - destruct H0 as [H0 H1]. split; auto. intros n1 n2. induction n2 as [|n2 IHn2].
    + intro H2. exfalso. apply (Nat.nlt_0_r n1). auto.
    + destruct (Nat.lt_total n1 n2) as [H2 | [H2 | H2]]; intro H3.
      * apply Rge_trans with (r2 := x[n2]); auto.
      * rewrite <- H2. auto.
      * exfalso. lia.
  - destruct H0 as [H0 H1]. split; auto.
Qed.

(* 定义: 有界数列 *)
Definition BoundedSeq x := IsSeq x /\ (∃ M, ∀ n, ∣(x[n])∣ <= M).

(* 定理2.9 单调有界定理 *)
Theorem Theorem2_9 : ∀ x, MonotonicSeq x -> BoundedSeq x -> Convergence x.
Proof.
  intros x H0 H1. destruct H1 as [H [M H1]].
  assert (H2 : IsSeq x). { destruct H0 as [H0 | H0]; apply H0. }
  destruct H2 as [H2 H3]. assert (H4 : NotEmpty ran[x]).
  { unfold NotEmpty. exists (x[0%nat]). apply fx_ran_T; auto.
    rewrite H3. apply Classifier1. auto. }
  apply Sup_inf_principle in H4 as H5. destruct H5 as [H5 H6], H0 as [H0 | H0].
  - assert (H7 : ∃M : R,Upper ran[x] M).
    { exists M. unfold Upper. intros xn I1. applyClassifier1 I1. destruct I1 as [n I1].
      apply f_x_T in I1 as I2; auto. rewrite <- I2. generalize (H1 n). intro I3.
      apply Abs_le_R in I3. apply I3. }
    apply H5 in H7 as H8. destruct H8 as [a H8]. exists a. unfold sup in H8.
    destruct H8 as [H8 H9]. unfold limit_seq. repeat split; auto. intros ε H10. 
    assert (H11 : a - ε < a).
    { apply Ropp_lt_gt_0_contravar in H10 as H11.
      apply Rplus_lt_compat_l with (r := a) in H11 as H12.
      rewrite Rplus_0_r in H12. auto. }
    apply H9 in H11 as H12. destruct H12 as [xN [H12 H13]]. applyClassifier1 H12. 
    destruct H12 as [N H12]. exists N. apply EqualIncrease in H0 as H14. 
    destruct H14 as [H14 H15]. apply f_x_T in H12 as H16; auto. 
    rewrite <- H16 in H13. intros n H17. apply H15 in H17 as H18.
    apply Rlt_le_trans with (r1 := a - ε) in H18 as H19; auto.
    apply Abs_R. unfold Upper in H8. assert (H20 : x[n] ∈ ran[x]).
    { apply fx_ran_T; auto. rewrite H3. apply Classifier1. auto. }
    apply H8 in H20 as H21. assert (H22 : a < a + ε).
    { apply Rplus_lt_compat_l with (r := a) in H10. rewrite Rplus_0_r in H10. auto. }
    assert (H24 : x[n] < a + ε). { apply Rle_lt_trans with (r2 := a); auto. } split.
    + apply Rplus_lt_reg_l with (r := a).
      assert (H23 : a + (x [n] - a) = x[n]). field. rewrite H23. auto.
    + apply Rplus_lt_reg_l with (r := a).
      assert (H23 : a + (x [n] - a) = x[n]). field. rewrite H23. auto.
  - assert (H7 : ∃L : R,Lower ran[ x] L).
    { exists (-M). unfold Lower. intros xn I1. applyClassifier1 I1. destruct I1 as [n I1]. 
      apply f_x_T in I1 as I2; auto. rewrite <- I2. generalize (H1 n). intro I3.
      apply Abs_le_R in I3. apply Rle_ge. apply I3. }
    apply H6 in H7 as H8. destruct H8 as [a H8]. exists a. unfold inf in H8.
    destruct H8 as [H8 H9]. unfold limit_seq. repeat split; auto.
    intros ε H10. assert (H11 : a < a + ε).
    { apply Rplus_lt_compat_l with (r := a) in H10 as H12.
      rewrite Rplus_0_r in H12. auto. }
    apply H9 in H11 as H12. destruct H12 as [xN [H12 H13]]. applyClassifier1 H12. 
    destruct H12 as [N H12]. exists N. apply EqualDecrease in H0 as H14. 
    destruct H14 as [H14 H15]. apply f_x_T in H12 as H16; auto.
    rewrite <- H16 in H13. intros n H17. apply H15 in H17 as H18. 
    apply Rge_le in H18. apply Rle_lt_trans with (r3 := a + ε) in H18 as H19; auto.
    apply Abs_R. unfold Lower in H8. assert (H20 : x[n] ∈ ran[x]).
    { apply fx_ran_T; auto. rewrite H3. apply Classifier1. auto. }
    apply H8 in H20 as H21. assert (H22 : a - ε < a).
    { apply Ropp_lt_gt_0_contravar in H10 as H22.
      apply Rplus_lt_compat_l with (r := a) in H22. rewrite Rplus_0_r in H22. auto. }
    assert (H24 : a - ε < x[n]).
    { apply Rlt_le_trans with (r2 := a); auto. apply Rge_le. auto. } split.
    + apply Rplus_lt_reg_l with (r := a).
      assert (H23 : a + (x [n] - a) = x[n]). field. rewrite H23. auto.
    + apply Rplus_lt_reg_l with (r := a).
      assert (H23 : a + (x [n] - a) = x[n]). field. rewrite H23. auto.
Qed.


(* 定义: 数列 x 第 n 项之后的最大项 *)
Definition Max_Seq_n x n m :=
  IsSeq x /\ (n <= m)%nat /\ (∀ i, (n <= i)%nat -> x[i] <= x[m]).

Fixpoint Fun_Lemma2_10 x n :=
  match n with
  | 0 => c \{ λ m, Max_Seq_n x 1 m \}
  | S n => c \{ λ m, Max_Seq_n x (S (Fun_Lemma2_10 x n)) m \}
  end.

Fixpoint Fun_Lemma2_10' x n k :=
  match n with
  | 0 => k
  | S n => c \{ λ (m : nat), (m > (Fun_Lemma2_10' x n k))%nat
        /\ x[m] > x[Fun_Lemma2_10' x n k] \}
  end.

(* 定理: 任何数列都存在单调子列 *)

(* x是有界数列,y是x的子列,推得y是有界数列 *)
Lemma Lemma2_10a : ∀ x y, BoundedSeq x -> SubSeq x y -> BoundedSeq y.
Proof.
  intros x y H0 H1. unfold BoundedSeq in *. unfold SubSeq in H1.
  destruct H0 as [H0 H2], H1 as [H1 [H3 [f [H4 [H5 H6]]]]]. clear H1. split; auto. 
  destruct H2 as [M H2]. exists M. intro n. rewrite H6. apply H2.
Qed.

(* 数列x的片段存在一个最大项x[k] *)
Lemma Lemma2_10b : ∀ x m n, IsSeq x -> (m >= n)%nat -> (∃ k, (k >= n)%nat 
  /\ (k <= m)%nat /\ (∀ i, (i >= n)%nat -> (i <= m)%nat -> x[i] <= x[k])).
Proof.
  intros x m n H0 H1. induction m as [|m IHm].
  - assert (n = 0)%nat. lia. rewrite <-H. exists n. repeat split; auto.
    intros i I1 I2. assert (i = n). lia. rewrite H2. right. reflexivity.
  - generalize (Nat.lt_ge_cases m n). intro H2. destruct H2 as [H2 | H2].
    + exists n. split; auto. split; auto. apply Nat.le_antisymm in H2 as H3; auto.
      rewrite <-H3. intros i I1 I2. apply Nat.le_antisymm in I2 as I3; auto.
      rewrite I3. right; reflexivity.
    + apply IHm in H2 as H3. destruct H3 as [k [H3 [H4 H5]]].
      generalize (Rlt_or_le x[k] x[S m]). intro H6. destruct H6 as [H6 | H6].
      * exists (S m). repeat split; auto. intros i H7 H8.
        assert (i = S m \/ i < S m)%nat as []. lia.
        -- rewrite H. right; reflexivity.
        -- assert (i <= m)%nat. lia. apply H5 in H9; auto. lra.
      * exists k. repeat split; auto. intros i H7 H8.
        assert (i = S m \/ i < S m)%nat as []. lia.
        -- rewrite H. apply H6.
        -- assert (i <= m)%nat. lia. auto.
Qed.

(* x是一个数列,存在一个y数列是x的子列,且这个子列是单调数列 *)
Lemma Lemma2_10c : ∀ x, IsSeq x -> (∃ y, SubSeq x y /\ MonotonicSeq y).
Proof.
  intros x H0. destruct classic with (P := ∀ (k : nat),
    ∃ (m : nat), Max_Seq_n x k m) as [H1 | H1].
  - assert (H2 : ∃ (y : Seq), y = \{\ λ n v, v = x [Fun_Lemma2_10 x n] \}\).
    { exists \{\ λ n v, v = x [Fun_Lemma2_10 x n] \}\; auto. }
    destruct H2 as [y H2]. exists y.
    assert (H3 : ∀ (n : nat), ((Fun_Lemma2_10 x n) < (Fun_Lemma2_10 x (S n)))%nat).
    { intro n. induction n as [|n IHn].
      - simpl. assert (I1 :  c \{ λ m : nat, Max_Seq_n x (S (c \{ λ m0 : nat,
        Max_Seq_n x 1 m0 \})) m \} ∈ \{ λ m : nat, Max_Seq_n x
        (S (c \{ λ m0 : nat, Max_Seq_n x 1 m0 \})) m \}).
        { apply Axiomc. unfold NotEmpty.
          generalize (H1 (S (c \{ λ m0 : nat, Max_Seq_n x 1 m0 \}))).
          intro I1. destruct I1 as [m I1]. exists m. apply <- Classifier1. auto. }
        applyClassifier1 I1. destruct I1 as [I1 [I2 I3]]. lia.
      - simpl. assert (I1 : c \{ λ m : nat, Max_Seq_n x
          (S (c \{ λ m0 : nat, Max_Seq_n x (S (Fun_Lemma2_10 x n)) m0 \})) m \}
              ∈ \{ λ m : nat, Max_Seq_n x (S (c \{ λ m0 : nat,
           Max_Seq_n x (S (Fun_Lemma2_10 x n)) m0 \})) m \}).
        { apply Axiomc. unfold NotEmpty. generalize (H1 (S (c \{ λ m0 : nat,
          Max_Seq_n x (S (Fun_Lemma2_10 x n)) m0 \}))). intro I1.
          destruct I1 as [m I1]. exists m. apply Classifier1. auto. }
        applyClassifier1 I1. destruct I1 as [I1 [I2 I3]]. lia. }
    assert (H4 : ∃ f, f = \{\ λ n v, v = Fun_Lemma2_10 x n \}\).
    { exists \{\ λ n v, v = Fun_Lemma2_10 x n \}\; auto. }
    destruct H4 as [f H4]. assert (H5 : StrictlyIncreaseFun_nat f).
    { assert (I1 : Function f).
      { unfold Function. intros x0 y0 z0 I1 I2. rewrite H4 in *.
        applyClassifier2 I1. applyClassifier2 I2. rewrite I2. auto. }
      split; auto. intros x1 y1 x2. induction x2 as [|x2 IHx2].
      - intros y2 I2 I3 I4. exfalso. apply (Nat.nlt_0_r x1). auto.
      - destruct (Nat.lt_total x1 x2) as [I2 | [I2 | I2]]; intros y2 I3 I4 I5.
        + assert (I6 : [x2, f[x2]] ∈ f).
          { apply x_fx_T; auto. apply Classifier1.
            exists (Fun_Lemma2_10 x x2). rewrite H4. apply Classifier2. auto. }
          apply Nat.lt_trans with (m := f[x2]).
          * apply IHx2; auto.
          * rewrite H4 in I4. apply -> Classifier2 in I4; lazy beta in I4.
            pattern f at 2 in I6. rewrite H4 in I6. applyClassifier2 I6.
            rewrite I6. rewrite I4. apply H3.
        + rewrite <- I2 in *. rewrite H4 in I3. applyClassifier2 I3.
          rewrite H4 in I4. apply -> Classifier2 in I4. lazy beta in I4.
          rewrite I3; rewrite I4. apply H3.
        + exfalso. lia. }
    assert (H6 : IsSeq y).
    { split.
      - unfold Function. intros x0 y0 z0 I1 I2. rewrite H2 in *.
        applyClassifier2 I1. applyClassifier2 I2. rewrite I2. auto.
      - apply AxiomI; intro z; split; intro I1.
        + apply Classifier1. auto.
        + apply Classifier1. exists (x[Fun_Lemma2_10 x z]).
          rewrite H2. apply Classifier2. auto. }
    assert (H7 : dom[f] = Full nat).
    { apply AxiomI; intro z; split; intro I1.
      - apply Classifier1. auto.
      - apply Classifier1. exists (Fun_Lemma2_10 x z).
        rewrite H4. apply Classifier2. auto. } split.
    + unfold SubSeq. split; auto; split; auto. exists f. split; auto; split; auto.
      intro n. assert (I1 : n ∈ dom[y]).
      { destruct H6 as [H6 I1]. rewrite I1. apply Classifier1; auto. }
      apply x_fx_T in I1 as I2; try apply H6. pattern y at 2 in I2. 
      rewrite H2 in I2. applyClassifier2 I2. rewrite I2.
      assert (I3 : n ∈ dom[f]). { rewrite H7. apply Classifier1; auto. }
      apply x_fx_T in I3 as I4; try apply H5. pattern f at 2 in I4. 
      rewrite H4 in I4. applyClassifier2 I4. rewrite I4. reflexivity.
    + unfold MonotonicSeq. right. unfold DecreaseSeq. split; auto.
      intro n. assert (I1 : ∀ m : nat, m ∈ dom[y]).
      { intro m. destruct H6 as [H6 I1]. rewrite I1. apply Classifier1; auto. }
      generalize (I1 n). intro I2. generalize (I1 (S n)). intro I3.
      apply x_fx_T in I2 as I4; try apply H6.
      apply x_fx_T in I3 as I5; try apply H6.
      pattern y at 2 in I4; rewrite H2 in I4. pattern y at 2 in I5; rewrite H2 in I5.
      applyClassifier2 I4. apply -> Classifier2 in I5. lazy beta in I5. destruct n as [|n].
      * assert (I6 : Max_Seq_n x 1%nat (Fun_Lemma2_10 x 0)).
        { assert (I6 : (Fun_Lemma2_10 x 0) ∈ \{ λ (m : nat), Max_Seq_n x 1%nat m \}).
          { simpl. apply Axiomc. unfold NotEmpty. generalize (H1 1%nat).
            intro I6. destruct I6 as [m I6]. exists m. apply Classifier1. apply I6. }
          apply -> Classifier1 in I6. lazy beta in I6. auto. }
        rewrite I4. rewrite I5. unfold Max_Seq_n in I6. destruct I6 as [I6 [I7 I8]].
        assert (I9 : (1 <= (Fun_Lemma2_10 x 1))%nat).
        { apply Nat.le_trans with (m := (Fun_Lemma2_10 x 0)); auto.
          apply Nat.lt_le_incl. apply H3. }
        apply I8 in I9. apply Rle_ge. auto.
      * rewrite I4. rewrite I5.
        assert (I6 : Max_Seq_n x (S (Fun_Lemma2_10 x n)) (Fun_Lemma2_10 x (S n))).
        { assert (I6 : (Fun_Lemma2_10 x (S n)) ∈
            \{ λ (m : nat), Max_Seq_n x (S (Fun_Lemma2_10 x n)) m \}).
          { simpl Fun_Lemma2_10 at 1. apply Axiomc. unfold NotEmpty.
            generalize (H1 (S (Fun_Lemma2_10 x n))). intro I6. 
            destruct I6 as [m I6]. exists m. apply Classifier1. apply I6. }
          apply -> Classifier1 in I6. lazy beta in I6. auto. }
        unfold Max_Seq_n in I6. destruct I6 as [I6 [I7 I8]].
        assert (I9 : ((S (Fun_Lemma2_10 x n)) <= (Fun_Lemma2_10 x (S (S n))))%nat).
        { apply Nat.le_trans with (m := (Fun_Lemma2_10 x (S n))); auto.
          apply Nat.lt_le_incl. apply H3. }
        apply I8 in I9. apply Rle_ge. auto.
  - assert (∃ k, ~ (∃ m, Max_Seq_n x k m)) as [k H1'].
    { apply NNPP; intro. elim H1. intros. apply NNPP; intro. elim H; eauto. }
    assert (H2 : ∀ m : nat, ~ (Max_Seq_n x k m)).
    { intros. intro. elim H1'; eauto. }
    assert (H3 : ∃ (y : Seq), y = \{\ λ n v, v = x[Fun_Lemma2_10' x n k] \}\).
    { exists \{\ λ n v, v = x[Fun_Lemma2_10' x n k] \}\; auto. }
    destruct H3 as [y H3]. exists y.
    assert (H4 : ∀ (n1 : nat), (n1 >= k)%nat 
      -> (∃ (n2 : nat), (n2 > n1)%nat /\ x[n2] > x[n1])).
    { intros n1 I1. apply NNPP; intro.
      assert (I2 : ∀ n2, ~ ((n2 > n1)%nat /\ x[n2] > x[n1])).
      { intros. intro. elim H; eauto. } apply H1'.
      generalize (Lemma2_10b x n1 k H0 I1). intro I3. destruct I3 as [m [I3 [I4 I5]]].
      exists m. unfold Max_Seq_n. split; auto; split; auto. intros i I6. 
      generalize (Nat.lt_ge_cases n1 i). intro I7. destruct I7 as [I7 | I7]; auto.
      generalize (I2 i). intro I8. apply not_and_or in I8.
      destruct I8 as [I8 | I8]; [exfalso | idtac]; auto.
      apply Rnot_gt_le in I8. apply Rle_trans with (r2 := x[n1]); auto. }
    assert (H5 : ∀ (n : nat), ((Fun_Lemma2_10' x n k) >= k)%nat).
    { intro n. induction n as [|n IHn].
      - simpl. auto.
      - assert (I1 : (Fun_Lemma2_10' x (S n) k) ∈ \{ λ (m : nat),
          (m > (Fun_Lemma2_10' x n k))%nat /\ x[m] > x[Fun_Lemma2_10' x n k] \}).
        { apply Axiomc. unfold NotEmpty. apply H4 in IHn as I1.
          destruct I1 as [m [I1 I2]]. exists m. apply Classifier1. split; auto. }
        apply -> Classifier1 in I1. lazy beta in I1. destruct I1 as [I1 I2].
        apply Nat.lt_le_incl. eapply Nat.le_lt_trans; eauto. }
    assert (H6 : ∀ (n : nat),
      ((Fun_Lemma2_10' x n k) < (Fun_Lemma2_10' x (S n) k))%nat).
    { intro n.
      assert (I1 : (Fun_Lemma2_10' x (S n) k) ∈ \{ λ (m : nat),
        (m > (Fun_Lemma2_10' x n k))%nat /\ x[m] > x[Fun_Lemma2_10' x n k] \} ).
      { apply Axiomc. unfold NotEmpty.
        generalize (H4 (Fun_Lemma2_10' x n k) (H5 n)). intro I1.
        destruct I1 as [n2 [I1 I2]]. exists n2. apply Classifier1. split; auto. }
      apply -> Classifier1 in I1. lazy beta in I1. apply I1. }
    assert (H7 : ∃ f, f = \{\ λ n v, v = Fun_Lemma2_10' x n k \}\).
    { exists \{\ λ n v, v = Fun_Lemma2_10' x n k \}\; auto. }
    destruct H7 as [f H7]. assert (H8 : StrictlyIncreaseFun_nat f).
    { assert (I1 : Function f).
      { unfold Function. intros x0 y0 z0 I1 I2. rewrite H7 in *.
        applyClassifier2 I1. applyClassifier2 I2. rewrite I2. auto. }
      split; auto. intros x1 y1 x2. induction x2 as [|x2 IHx2].
      - intros y2 I2 I3 I4. exfalso. apply (Nat.nlt_0_r x1). auto.
      - destruct (Nat.lt_total x1 x2) as [I2 | [I2 | I2]]; intros y2 I3 I4 I5.
        + assert (I6 : [x2, f[x2]] ∈ f).
          { apply x_fx_T; auto. apply Classifier1.
            exists (Fun_Lemma2_10' x x2 k). rewrite H7. apply Classifier2. auto. }
          apply Nat.lt_trans with (m := f[x2]).
          * apply IHx2; auto.
          * rewrite H7 in I4. apply -> Classifier2 in I4; lazy beta in I4.
            pattern f at 2 in I6. rewrite H7 in I6. applyClassifier2 I6.
            rewrite I6. rewrite I4. apply H6.
        + rewrite <- I2 in *. rewrite H7 in I3. applyClassifier2 I3. rewrite H7 in I4. 
          apply -> Classifier2 in I4. lazy beta in I4. rewrite I3; rewrite I4. apply H6.
        + lia. }
    assert (H9 : IsSeq y).
    { split.
      - unfold Function. intros x0 y0 z0 I1 I2. rewrite H3 in *.
        applyClassifier2 I1. applyClassifier2 I2. rewrite I2. auto.
      - apply AxiomI; intro z; split; intro I1.
        + apply Classifier1. auto.
        + apply Classifier1. exists (x[Fun_Lemma2_10' x z k]).
          rewrite H3. apply Classifier2. auto. }
    assert (H10 : dom[f] = Full nat).
    { apply AxiomI; intro z; split; intro I1.
      - apply Classifier1. auto.
      - apply Classifier1. exists (Fun_Lemma2_10' x z k).
        rewrite H7. apply Classifier2. auto. } split.
    + unfold SubSeq. split; auto; split; auto. exists f. split; auto; split; auto.
      intro n. assert (I1 : n ∈ dom[y]).
      { destruct H9 as [H9 I1]. rewrite I1. apply Classifier1; auto. }
      apply x_fx_T in I1 as I2; try apply H9. pattern y at 2 in I2. 
      rewrite H3 in I2. applyClassifier2 I2. rewrite I2.
      assert (I3 : n ∈ dom[f]). { rewrite H10. apply Classifier1; auto. }
      apply x_fx_T in I3 as I4; try apply H8. pattern f at 2 in I4. 
      rewrite H7 in I4. applyClassifier2 I4. rewrite I4. reflexivity.
    + left. unfold IncreaseSeq. split; auto. intro n.
      assert (I1 : ∀ m : nat, m ∈ dom[y]).
      { intro m. destruct H9 as [H9 I1]. rewrite I1. apply Classifier1; auto. }
      generalize (I1 n). intro I2. generalize (I1 (S n)). intro I3.
      apply x_fx_T in I2 as I4; try apply H9.
      apply x_fx_T in I3 as I5; try apply H9. pattern y at 2 in I4. 
      rewrite H3 in I4. applyClassifier2 I4. pattern y at 2 in I5. rewrite H3 in I5.
      apply -> Classifier2 in I5; lazy beta in I5. rewrite I4; rewrite I5.
      assert (I6 : (Fun_Lemma2_10' x (S n) k) ∈ \{ λ (m : nat),
        (m > (Fun_Lemma2_10' x n k))%nat /\ x[m] > x[Fun_Lemma2_10' x n k] \}).
      { apply Axiomc. generalize (H4 (Fun_Lemma2_10' x n k) (H5 n)). intro I6. 
        destruct I6 as [m [I6 I7]]. exists m. apply Classifier1; split; auto. }
      apply -> Classifier1 in I6; lazy beta in I6. destruct I6 as [I6 I7]. left; auto.
Qed.

(* 定理2.10 致密性定理——有界数列必有收敛的子数列 *)
Theorem Theorem2_10 : ∀ x, BoundedSeq x -> (∃ y, SubSeq x y /\ Convergence y).
Proof.
  intros x H0. assert (H1 : ∀ (y : Seq), SubSeq x y -> BoundedSeq y).
  { intro y. apply Lemma2_10a. auto. } destruct H0 as [H0 [M H2]]. 
  apply Lemma2_10c in H0 as H3. destruct H3 as [y [H3 H4]]. 
  exists y. split; auto. apply H1 in H3. apply Theorem2_9; auto.
Qed.

(* 定理2.11 柯西收敛准则 *)
Theorem Theorem2_11 : ∀ x, IsSeq x -> (Convergence x <-> 
  (∀ ε, ε > 0 -> ∃ N, ∀ n m, (n > N)%nat -> (m > N)%nat -> ∣ (x[n] - x[m])∣ < ε)).
Proof.
  intros x H0. split.
  - intros H1 ε H2. destruct H1 as [A H1]. assert (H3 : ε / 2 > 0).
    { generalize (Rinv_0_lt_compat 2 Rlt_0_2). intro I1.
      apply Rmult_gt_0_compat; auto. }
    apply H1 in H3 as H4. destruct H4 as [N H4]. exists N. intros n m H5 H6. 
    apply H4 in H5 as H7. apply H4 in H6 as H8.
    assert (H9 : ∣(x[n] - x[m])∣ <= ∣(x[n] - A)∣ + ∣(x[m] - A)∣).
    { assert (I1 : x[n] - x[m] = (x[n] - A) - (x[m] - A)). field.
      rewrite I1. apply Abs_minus_le. }
    apply Rle_lt_trans with (r2 := ∣(x[n] - A)∣ + ∣(x[m] - A)∣); auto.
    assert (H10 : ε = ε/2 + ε/2). field. rewrite H10. apply Rplus_lt_compat; auto.
  - intro H1. assert (H2 : BoundedSeq x).
    { unfold BoundedSeq. split; auto. 
      generalize (H1 1 Rlt_0_1). intro I1.  destruct I1 as [N0 I1].
      assert (I2 : ∀ n : nat, (n > N0)%nat -> ∣(x[n] - x[S N0])∣ < 1).
      { intros n I2. apply I1; auto. }
      assert (I3 : ∀ n : nat, (n > N0)%nat -> ∣(x[n])∣ < ∣(x[S N0])∣ + 1).
      { intros n I3. apply I2 in I3 as I4.
        apply Rplus_lt_compat_l with (r := ∣(x[S N0])∣) in I4 as I5.
        apply Rle_lt_trans with (r2 := ∣(x[S N0])∣ + ∣(x[n] - x[S N0])∣);
        auto. assert (I6 : x[n] = x[S N0] + (x[n] - x[S N0])). field.
        pattern x[n] at 1. rewrite I6. apply Abs_plus_le. }
      assert (I4 : ∀ N : nat, ∃ M0, ∀ n : nat, (n <= N)%nat -> ∣(x[n])∣ <= M0).
      { intro N. induction N as [|N IHN].
        - exists (∣(x[0%nat])∣). intros n J1. assert (n = 0)%nat. lia.
          rewrite H. right. reflexivity.
        - destruct IHN as [M0 IHN].
          destruct (Rlt_or_le M0 ∣(x[S N])∣) as [J1 | J1].
          + exists (∣(x[S N])∣). intros n J2.
            assert (n < S N \/ n = S N)%nat as []. lia.
            * left. apply Rle_lt_trans with (r2 := M0); auto. apply IHN. lia.
            * rewrite H. right; reflexivity.
          + exists M0. intros n J2. assert (n < S N \/ n = S N)%nat as []. lia.
            * apply IHN. lia.
            * rewrite H. auto. }
      generalize (I4 N0). intro I5. destruct I5 as [M0 I5].
      destruct (Rlt_or_le M0 (∣(x[S N0])∣ + 1)) as [I6 | I6].
      - exists (∣(x[S N0])∣ + 1). intro n. generalize (Nat.le_gt_cases n N0).
        intro I7. destruct I7 as [I7 | I7].
        + left. apply Rle_lt_trans with (r2 := M0); auto.
        + left. auto.
      - exists M0. intro n. generalize (Nat.le_gt_cases n N0).
        intro I7. destruct I7 as [I7 | I7]; auto.
        left. apply Rlt_le_trans with (r2 := (∣(x[S N0])∣ + 1)); auto. }
    apply Theorem2_10 in H2 as H3. destruct H3 as [y [H3 H4]].
    destruct H4 as [a H4]. exists a. unfold limit_seq. split; auto.
    intros ε H5. assert (H6 : ε/2 > 0).
    { generalize (Rinv_0_lt_compat 2 Rlt_0_2). intro I1.
      apply Rmult_gt_0_compat; auto. }
    apply H1 in H6 as H7. destruct H7 as [N H7]. exists N.
    intros n H8. assert (H9 : ∀ m, (m > N)%nat -> ∣(x[n] - y[m])∣ < ε/2).
    { intros m I6. assert (I7 : ∃ m1, (m1 > N)%nat /\ y[m] = x[m1]).
      { unfold SubSeq in H3. destruct H3 as [H3 [I1 [f [I2 [I3 I4]]]]].
        exists (f[m]). split; auto. apply fn_ge_n with (n := m) in I2 as I5; auto.
        apply Nat.lt_le_trans with (m := m); auto. }
      destruct I7 as [m1 [I7 I8]]. rewrite I8. auto. }
    assert (H10 : ∃ z : Seq, z = \{\ λ m v, v = ∣(x[n] - y[m])∣ \}\).
    { exists \{\ λ m v, v = ∣(x[n] - y[m])∣ \}\; auto. }
    destruct H10 as [z H10]. assert (H11 : IsSeq z).
    { unfold IsSeq. split.
      - unfold Function. rewrite H10. intros x0 y0 z0 I1 I2.
        applyClassifier2 I1. applyClassifier2 I2. rewrite I2. apply I1.
      - apply AxiomI. intro z0; split; intro I1.
        + apply Classifier1. reflexivity.
        + apply Classifier1. exists (∣(x[n] - y[z0])∣). rewrite H10.
          apply Classifier2. reflexivity. }
    assert (H12 : limit_seq z (∣(x[n] - a)∣)).
    { unfold limit_seq in H4. destruct H4 as [H4 I1]. split; auto. intros ε0 I2. 
      apply I1 in I2 as I3. destruct I3 as [N0 I3]. exists N0. intros n0 I4. 
      apply I3 in I4 as I5. assert (I6 : z[n0] = ∣(x[n] - y[n0])∣).
      { apply f_x_T; try apply H11. rewrite H10. apply Classifier2. reflexivity. }
      rewrite I6. apply Rle_lt_trans with (r2 := ∣(y[n0] - a)∣); auto.
      assert (I7 : y[n0] - a = -((x[n] - y[n0]) - (x[n] - a))). field.
      rewrite I7. rewrite <- Abs_eq_neg. apply Abs_abs_minus. }
    assert (H13 : ∃ w : Seq, w = \{\ λ m v, v = ε/2 \}\).
    { exists \{\ λ m v, v = ε/2 \}\. reflexivity. }
    destruct H13 as [w H13]. assert (H14 : IsSeq w).
    { split.
      - unfold Function. rewrite H13. intros x0 y0 z0 I1 I2.
        applyClassifier2 I1. applyClassifier2 I2. rewrite I2. apply I1.
      - apply AxiomI. intro z0; split; intro I1.
        + apply Classifier1. reflexivity.
        + apply Classifier1. exists (ε/2). rewrite H13. apply Classifier2. reflexivity. }
    assert (H15 : limit_seq w (ε/2)).
    { split; auto. intros ε0 I1. exists 0%nat. intros n0 I2.
      assert (I3 : w[n0] = ε/2).
      { apply f_x_T; try apply H14. rewrite H13. apply Classifier2. reflexivity. }
      rewrite I3. unfold Rminus. rewrite Rplus_opp_r. rewrite Abs_ge; auto.
      right; auto. }
    assert (H16 : lim z <= lim w).
    { apply Theorem2_5; [exists (∣(x[n] - a)∣) | exists (ε/2) | idtac]; auto.
      exists N. intros n0 I1. assert (I2 : z[n0] = ∣(x[n] - y[n0])∣).
      { apply f_x_T; try apply H11. rewrite H10. apply Classifier2. reflexivity. }
      assert (I3 : w[n0] = ε/2).
      { apply f_x_T; try apply H14. rewrite H13. apply Classifier2. reflexivity. }
      rewrite I2. rewrite I3. left. apply H9. apply I1. }
    rewrite lim_a with (a := (∣(x[n] - a)∣)) in H16; auto.
    rewrite lim_a with (a := (ε/2)) in H16; auto.
    apply Rle_lt_trans with (r2 := ε/2); auto. lra.
Qed.
