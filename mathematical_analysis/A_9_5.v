(** A_9_5 *)
(* 微积分学基本定理 · 定积分计算(续) *)

Require Export A_9_4.

(* 定积分唯一性 *)
Lemma Def_Integral_Uni : ∀ f a b J1 J2, Def_Integral f a b J1
  -> Def_Integral f a b J2 -> J1 = J2.
Proof.
  intros. destruct H as [H[H1[]]], H0 as [_[_[_]]].
  destruct (classic (J1 = J2)) as [H4|H4]. auto.
  assert (0 < ∣(J2 - J1)∣). { apply Rgt_lt,Abs_not_eq_0. lra. }
  assert (0 < ∣(J2 - J1)∣/2) as H5a. lra.
  pose proof H5a. apply H3 in H6 as [δ1[]].
  pose proof H5a. apply H0 in H8 as [δ2[]].
  destruct (Examp2 δ1 δ2 (b-a)) as [δ[H10[H11[]]]]; auto. lra.
  assert (0 < δ <= b - a). lra. apply Seg_Exists in H14 as [T[n[]]]; auto.
  set (ξ := \{\ λ u v, v = (T[u] + T[S u])/2 \}\).
  assert (SegPoints T ξ (S n)).
  { red; intros. destruct H14 as [_[_[_[]]]]. apply H14 in H16.
    unfold ξ. rewrite FunValue. lra. }
  pose proof H16. apply H7 in H17; auto; [ |rewrite <-H15; auto].
  pose proof H16. apply H9 in H18; auto; [ |rewrite <-H15; auto].
  assert (∣(((IntegralSum f T n ξ) - J1) - ((IntegralSum f T n ξ) - J2))∣
    <= ∣((IntegralSum f T n ξ) - J1)∣ + ∣((IntegralSum f T n ξ) - J2)∣).
  { apply Abs_minus_le. }
  replace ((((IntegralSum f T n ξ) - J1) - ((IntegralSum f T n ξ) - J2)))
  with (J2 - J1) in H19; [ |lra].
  assert (∣((IntegralSum f T n ξ) - J1)∣ + ∣((IntegralSum f T n ξ) - J2)∣
    < ∣(J2 - J1)∣/2 + ∣(J2 - J1)∣/2). lra.
  replace (∣(J2 - J1)∣/2 + ∣(J2 - J1)∣/2) with (∣(J2 - J1)∣) in H20; [ |lra].
  exfalso. lra.
Qed.

(* 子区间可积性 *)
Lemma Subset_Def_Integral : ∀ f a b c d, (∃ J, Def_Integral f a b J)
  -> a <= c -> c < d -> d <= b -> (∃ J, Def_Integral f c d J).
Proof.
  intros. assert (a < b). lra. apply (Property9_4_4a f a b) in H3 as [H3 _].
  destruct H0. assert (a < c < b). lra. apply H3 in H4 as [J1[J2[]]]; auto.
  destruct H2. assert (c < d < b). lra. apply (Property9_4_4a f c b) in H6
  as [J3[J4[]]]; eauto. lra. rewrite H2. eauto. rewrite <-H0.
  destruct H2. assert (a < d < b). lra. apply H3 in H4 as [J1[J2[]]]; eauto.
  rewrite H2; eauto.
Qed.

(* 变上限积分函数 *)
Definition VarUp_Integral_Fun f c := \{\ λ x y, (x < c -> Def_Integral f x c (-y))
  /\ (x = c -> y = 0) /\ (c < x -> Def_Integral f c x y) \}\.

(* 函数的验证 *)
Corollary VarUp_Function : ∀ f c, Function (VarUp_Integral_Fun f c).
Proof.
  intros. red; intros. applyClassifier2 H. applyClassifier2 H0.
  destruct H as [H[]], H0 as [H0[]].
  destruct (Rtotal_order x c) as [H5|[H5|H5]]; pose proof H5.
  apply H in H5. apply H0 in H6. apply (Def_Integral_Uni f x c (-y))
  in H6; auto. lra. rewrite H1,H3; auto. apply H2 in H5. apply H4 in H6.
  apply (Def_Integral_Uni f c x y) in H6; auto.
Qed.

(* 变上限积分函数的定义域 *)
Corollary VarUp_dom_a : ∀ f c, dom[VarUp_Integral_Fun f c]
  = \{ λ x, (∃ a b, a <= c <= b /\ a <= x <= b /\ ∃ J, Def_Integral f a b J)
    \/ x = c \}.
Proof.
  intros. pose proof (VarUp_Function f c). apply AxiomI; split; intros.
  - apply Classifier1 in H0 as []. applyClassifier2 H0. destruct H0 as [H0[]].
    apply Classifier1. destruct (Rtotal_order z c) as [H3|[H3|H3]]; auto; left;
    [exists z,c|exists c,z]; split; try lra; split; eauto; lra.
  - apply Classifier1. apply Classifier1 in H0 as [[a[b[H0[H1[J]]]]]|].
    destruct (Rtotal_order c z) as [H3|[H3|H3]].
    assert (∃ J, Def_Integral f c z J) as [J1].
    { apply (Subset_Def_Integral f a b c z); eauto; lra. }
    exists J1. apply Classifier2; split; [ |split]; intros; auto; exfalso; lra.
    exists 0. apply Classifier2; split; [ |split]; intros; auto; exfalso; lra.
    assert (∃ J, Def_Integral f z c J) as [J1].
    { apply (Subset_Def_Integral f a b z c); eauto; lra. }
    exists (-J1). apply Classifier2; split; [ |split]; intros; try (exfalso; lra).
    replace (-(-J1)) with J1; auto. lra. exists 0. apply Classifier2; split;
    [ |split]; intros; auto; exfalso; lra.
Qed.

Corollary VarUp_dom_b : ∀ f c a b, (∃ J, Def_Integral f a b J) -> a <= c <= b
  -> \[a, b\] ⊂ dom[VarUp_Integral_Fun f c].
Proof.
  intros. rewrite VarUp_dom_a. red; intros. applyClassifier1 H1. apply Classifier1.
  left. exists a,b. split; [ |split]; auto. lra.
Qed.

(* 上限大于下限时的取值 *)
Corollary VarUp_Value_gt : ∀ f c x, x ∈ dom[VarUp_Integral_Fun f c]
  -> c < x -> Def_Integral f c x ((VarUp_Integral_Fun f c)[x]).
Proof.
  intros. apply x_fx_T in H. applyClassifier2 H. destruct H as [H[]]; auto.
  apply VarUp_Function.
Qed.

(* 上限等于下限时的取值 *)
Corollary VarUp_Value_eq : ∀ f c, (VarUp_Integral_Fun f c)[c] = 0.
Proof.
  intros. assert (c ∈ dom[VarUp_Integral_Fun f c]).
  { rewrite VarUp_dom_a. apply Classifier1; auto. }
  apply x_fx_T in H. applyClassifier2 H. destruct H as [H[]]; auto.
  apply VarUp_Function.
Qed.

(* 上限小于下限时的取值 *)
Corollary VarUp_Value_lt : ∀ f c x, x ∈ dom[VarUp_Integral_Fun f c]
  -> x < c -> Def_Integral f x c (-(VarUp_Integral_Fun f c)[x]).
Proof.
  intros. apply x_fx_T in H. applyClassifier2 H. destruct H as [H[]]; auto.
  apply VarUp_Function.
Qed.


(* 变下限积分函数 *)
Definition VarLow_Integral_Fun f c := \{\ λ x y, (x < c -> Def_Integral f x c y)
  /\ (x = c -> y = 0) /\ (c < x -> Def_Integral f c x (-y)) \}\.

(* 函数的验证 *)
Corollary VarLow_Function : ∀ f c, Function (VarLow_Integral_Fun f c).
Proof.
  intros. red; intros. applyClassifier2 H. applyClassifier2 H0.
  destruct H as [H[]], H0 as [H0[]].
  destruct (Rtotal_order x c) as [H5|[H5|H5]]; pose proof H5.
  apply H in H5. apply H0 in H6. apply (Def_Integral_Uni f x c y) in H6; auto.
  rewrite H1,H3; auto. apply H2 in H5. apply H4 in H6.
  apply (Def_Integral_Uni f c x (-y)) in H6; auto. lra.
Qed.

(* 变下限积分函数的定义域 *)
Corollary VarLow_dom_a : ∀ f c, dom[VarLow_Integral_Fun f c]
  = \{ λ x, (∃ a b, a <= c <= b /\ a <= x <= b /\ ∃ J, Def_Integral f a b J)
    \/ x = c \}.
Proof.
  intros. pose proof (VarLow_Function f c). apply AxiomI; split; intros.
  - apply Classifier1 in H0 as []. applyClassifier2 H0. destruct H0 as [H0[]].
    apply Classifier1. destruct (Rtotal_order z c) as [H3|[H3|H3]]; auto; left;
    [exists z,c|exists c,z]; split; try lra; split; eauto; lra.
  - apply Classifier1. apply Classifier1 in H0 as [[a[b[H0[H1[J]]]]]|].
    destruct (Rtotal_order c z) as [H3|[H3|H3]].
    assert (∃ J, Def_Integral f c z J) as [J1].
    { apply (Subset_Def_Integral f a b c z); eauto; lra. }
    exists (-J1). apply Classifier2; split; [ |split]; intros; auto;
    try (exfalso; lra). replace (-(-J1)) with J1; auto. lra.
    exists 0. apply Classifier2; split; [ |split]; intros; auto; exfalso; lra.
    assert (∃ J, Def_Integral f z c J) as [J1].
    { apply (Subset_Def_Integral f a b z c); eauto; lra. }
    exists J1. apply Classifier2; split; [ |split]; intros; auto; exfalso; lra.
    exists 0. apply Classifier2; split; [ |split]; intros; auto; exfalso; lra.
Qed.

Corollary VarLow_dom_b : ∀ f c a b, (∃ J, Def_Integral f a b J) -> a <= c <= b
  -> \[a, b\] ⊂ dom[VarLow_Integral_Fun f c].
Proof.
  intros. rewrite VarLow_dom_a. red; intros. applyClassifier1 H1. apply Classifier1.
  left. exists a,b. split; [ |split]; auto. lra.
Qed.

(* 下限大于上限时的取值 *)
Corollary VarLow_Value_gt : ∀ f c x, x ∈ dom[VarLow_Integral_Fun f c]
  -> c < x -> Def_Integral f c x (-(VarLow_Integral_Fun f c)[x]).
Proof.
  intros. apply x_fx_T in H. applyClassifier2 H. destruct H as [H[]]; auto.
  apply VarLow_Function.
Qed.

(* 下限等于上限时的取值 *)
Corollary VarLow_Value_eq : ∀ f c, (VarLow_Integral_Fun f c)[c] = 0.
Proof.
  intros. assert (c ∈ dom[VarLow_Integral_Fun f c]).
  { rewrite VarLow_dom_a. apply Classifier1; auto. }
  apply x_fx_T in H. applyClassifier2 H. destruct H as [H[]]; auto.
  apply VarLow_Function.
Qed.

(* 下限小于上限时的取值 *)
Corollary VarLow_Value_lt : ∀ f c x, x ∈ dom[VarLow_Integral_Fun f c]
  -> x < c -> Def_Integral f x c ((VarLow_Integral_Fun f c)[x]).
Proof.
  intros. apply x_fx_T in H. applyClassifier2 H. destruct H as [H[]]; auto.
  apply VarLow_Function.
Qed.

(* 变上限积分函数 和 变下限积分函数 取值的关系 *)
(* 二者取值是相反数关系 *)
Corollary VarUp_and_VarLow_Value : ∀ f c,
  dom[VarUp_Integral_Fun f c] = dom[VarLow_Integral_Fun f c]
  /\ (∀ x, x ∈ dom[VarUp_Integral_Fun f c]
    -> (VarUp_Integral_Fun f c)[x] = -(VarLow_Integral_Fun f c)[x]).
Proof.
  intros. split. rewrite VarUp_dom_a,VarLow_dom_a; auto. intros.
  assert (x ∈ dom[VarLow_Integral_Fun f c]).
  { rewrite VarLow_dom_a,<-VarUp_dom_a; auto. }
  destruct (Rtotal_order x c) as [H1|[H1|H1]].
  apply VarUp_Value_lt in H; auto. apply VarLow_Value_lt in H0; auto.
  apply (Def_Integral_Uni f x c ((VarLow_Integral_Fun f c)[x])) in H; auto. lra.
  rewrite H1,VarUp_Value_eq,VarLow_Value_eq. lra.
  apply VarUp_Value_gt in H; auto. apply VarLow_Value_gt in H0; auto.
  apply (Def_Integral_Uni f c x ((VarUp_Integral_Fun f c)[x])) in H0; auto.
Qed.

(* 函数积分小于等于上界乘区间长度 *)
Lemma Lemma9_9 : ∀ f c M x1 x2, c <= x1 < x2
  -> x1 ∈ dom[VarUp_Integral_Fun f c] -> x2 ∈ dom[VarUp_Integral_Fun f c]
  -> (∀ x, x1 <= x <= x2 -> ∣(f[x])∣ <= M)
  -> ∣((VarUp_Integral_Fun f c)[x1] - (VarUp_Integral_Fun f c)[x2])∣
    <= M * (x2 - x1).
Proof.
  intros. assert (c < x1 \/ c = x1) as []. lra.
  pose proof H0. pose proof H1. apply VarUp_Value_gt in H4,H5; auto; [ |lra].
  assert (∃ J, Def_Integral f c x2 J). eauto. assert (c < x1 < x2). lra.
  apply (Property9_4_4a f c x2) in H7 as [J0[J1[_]]]; auto; [ |lra].
  assert (x2 ∈ dom[VarUp_Integral_Fun f x1]).
  { rewrite VarUp_dom_a. apply Classifier1. left. exists x1,x2.
    split; [ |split]; eauto; lra. }
  assert (Def_Integral f x1 x2 ((VarUp_Integral_Fun f x1)[x2])).
  { apply VarUp_Value_gt; auto. lra. }
  assert (J1 = (VarUp_Integral_Fun f x1)[x2]).
  { apply (Def_Integral_Uni f x1 x2); auto. }
  assert ((VarUp_Integral_Fun f c)[x1] + J1 = (VarUp_Integral_Fun f c)[x2]).
  { symmetry. apply (Property9_4_4b f c x2 x1); auto. apply Classifier1. lra. }
  rewrite Abs_eq_neg. replace (-((VarUp_Integral_Fun f c)[x1]
    - (VarUp_Integral_Fun f c)[x2])) with J1; [ |lra].
  assert (∃ J, Def_Integral f x1 x2 J). eauto.
  apply Property9_4_6a in H12 as [J2]. assert (∣J1∣ <= J2).
  { apply (Property9_4_6b f x1 x2); auto. }
  assert (Def_Integral \{\ λ u v, v = M \}\ x1 x2 (M * (x2 - x1))).
  { apply Lemma9_7. lra. }
  assert (J2 <= M * (x2 - x1)).
  { eapply Corollary9_4_5; eauto. intros. rewrite FunValue.
    assert (x ∈ dom[\{\ λ u v, (u ∈ dom[f]) /\ v = ∣(f[u])∣ \}\]).
    { destruct H7 as [_[_[]]]. apply Classifier1. exists ∣(f[x])∣.
      apply Classifier2; auto. }
    apply x_fx_T in H16. applyClassifier2 H16. destruct H16 as []. rewrite H17.
    apply H2. applyClassifier1 H15. lra. red; intros. applyClassifier2 H17.
    applyClassifier2 H18. destruct H17 as [], H18 as [].
    rewrite H19,H20; auto. } lra.
  rewrite <-H3,VarUp_Value_eq. rewrite <-H3 in *. clear dependent x1.
  rewrite Abs_eq_neg. replace (-(0 - (VarUp_Integral_Fun f c)[x2])) with
  ((VarUp_Integral_Fun f c)[x2]); [ |lra].
  apply VarUp_Value_gt in H1; [ |lra]. assert (∃ J, Def_Integral f c x2 J).
  eauto. apply Property9_4_6a in H3 as [J]. pose proof H3 as [H4[H5[H6 _]]].
  pose proof H3. eapply Property9_4_6b in H7; eauto.
  assert (Def_Integral \{\ λ u v, v = M \}\ c x2 (M * (x2 - c))).
  { apply Lemma9_7; auto. }
  assert (J <= M * (x2 - c)).
  { eapply Corollary9_4_5; eauto. intros. rewrite FunValue. pose proof H9.
    apply H6,x_fx_T in H10; auto. applyClassifier2 H10. destruct H10 as []; auto.
    rewrite H11. apply H2. applyClassifier1 H9. lra. } lra.
Qed.

Theorem Theorem9_9a : ∀ f a b, (∃ J, Def_Integral f a b J)
  -> ContinuousClose (VarUp_Integral_Fun f a) a b.
Proof.
  intros. assert (DBoundedFun f (\[a, b\])).
  { destruct H. apply (Theorem9_2 f a b x); auto. destruct H; auto.
    destruct H as [_[]]; auto. }
  assert (\[a, b\] ⊂ dom[VarUp_Integral_Fun f a]).
  { apply VarUp_dom_b; auto. destruct H as [J[_[]]]. lra. }
  assert (∀ x, a < x < b -> ∃ δ, δ > 0 /\ Uº(x; δ) ⊂ \[a, b\]).
  { intros. destruct (Examp1 (x-a) (b-x)) as [δ[H3[]]]; try lra.
    exists δ. split; auto. red; intros. apply Classifier1 in H6 as [].
    apply Abs_R in H7. apply Classifier1. lra. }
  pose proof H0 as [H3[H4[M]]]. assert (0 <= M).
  { assert (∣(f[a])∣ <= M).
    { apply H5. apply Classifier1. destruct H as [J[_[]]]. lra. }
    assert (∣(f[a])∣ >= 0). apply Abs_Rge0. lra. } destruct H6.
  - split; [ |split]. red; intros. split. apply H1. apply Classifier1. lra. split.
    apply VarUp_Function. pose proof (H2 x H7) as [δ[]]. exists δ. split; auto.
    split. red; auto. intros. assert (0 < ε/M). { apply Rdiv_lt_0_compat; auto. }
    destruct (Examp1 δ (ε/M)) as [δ1[H12[]]]; auto. exists δ1. split. auto.
    intros. destruct (classic (x0 = x)) as [H16|H16].
    rewrite H16,Rminus_diag,Abs_ge; auto. lra.
    assert (∣((VarUp_Integral_Fun f a)[x0] - (VarUp_Integral_Fun f a)[x])∣
      <= M * ∣(x0 - x)∣).
    { assert (x ∈ \[a, b\] /\ x0 ∈ \[a, b\]) as [].
      { split. apply Classifier1; lra. apply H9. apply Classifier1. lra. }
      assert (x0 < x \/ x < x0) as []. lra. rewrite (Abs_lt (x0 - x)); [ |lra].
      replace (-(x0 - x)) with (x - x0); [ |lra]. apply Lemma9_9; auto.
      applyClassifier1 H18. lra. intros. apply H5. applyClassifier1 H17.
      applyClassifier1 H18. apply Classifier1. lra.
      rewrite (Abs_ge (x0 - x)); [ |lra]. rewrite Abs_eq_neg.
      replace (-((VarUp_Integral_Fun f a)[x0] - (VarUp_Integral_Fun f a)[x]))
      with ((VarUp_Integral_Fun f a)[x] - (VarUp_Integral_Fun f a)[x0]); [ |lra].
      apply Lemma9_9; auto. applyClassifier1 H17. lra. intros. apply H5.
      applyClassifier1 H17. applyClassifier1 H18. apply Classifier1. lra. }
    assert (M * ∣(x0 - x)∣ < M * δ1 < M * (ε/M)) as [].
    { split; apply Rmult_lt_compat_l; auto. lra. } unfold Rdiv in H19.
    rewrite <-Rmult_assoc,Rinv_r_simpl_m in H19. lra. lra.
    red; intros. split. apply H1,Classifier1. destruct H as [J[_[]]]. lra. split.
    apply VarUp_Function. assert (a < b). { destruct H as [J[_[]]]; auto. }
    exists (b - a). split. lra. split. red; intros. rewrite VarUp_dom_a.
    apply Classifier1. left. applyClassifier1 H8. exists a,b. split; [ |split]; auto;
    lra. intros. assert (0 < ε/M). { apply Rdiv_lt_0_compat; auto. }
    destruct (Examp1 (b-a) (ε/M)) as [δ1[H10[]]]; auto. lra. exists δ1.
    split. auto. intros. rewrite Abs_eq_neg.
    replace (-((VarUp_Integral_Fun f a)[x] - (VarUp_Integral_Fun f a)[a]))
    with ((VarUp_Integral_Fun f a)[a] - (VarUp_Integral_Fun f a)[x]); [ |lra].
    assert (∣((VarUp_Integral_Fun f a)[a] - (VarUp_Integral_Fun f a)[x])∣
      <= M * (x - a)).
    { apply Lemma9_9; try (apply H1,Classifier1; lra). lra.
      intros. apply H5,Classifier1. lra. }
    assert (M * (x-a) < M * δ1 < M * (ε/M)).
    { split; apply Rmult_lt_compat_l; auto. lra. }
    unfold Rdiv in H15. rewrite <-Rmult_assoc,Rinv_r_simpl_m in H15. lra. lra.
    red; intros. split. apply H1,Classifier1. destruct H as [J[_[]]]. lra. split.
    apply VarUp_Function. assert (a < b). { destruct H as [J[_[]]]; auto. }
    exists (b - a). split. lra. split. red; intros. rewrite VarUp_dom_a.
    apply Classifier1. left. applyClassifier1 H8. exists a,b. split; [ |split]; auto;
    lra. intros. assert (0 < ε/M). { apply Rdiv_lt_0_compat; auto. }
    destruct (Examp1 (b-a) (ε/M)) as [δ1[H10[]]]; auto. lra. exists δ1.
    split. auto. intros.
    assert (∣((VarUp_Integral_Fun f a)[x] - (VarUp_Integral_Fun f a)[b])∣
      <= M * (b - x)).
    { apply Lemma9_9; try (apply H1,Classifier1; lra). lra.
      intros. apply H5,Classifier1. lra. }
    assert (M * (b-x) < M * δ1 < M * (ε/M)).
    { split; apply Rmult_lt_compat_l; auto. lra. }
    unfold Rdiv in H15. rewrite <-Rmult_assoc,Rinv_r_simpl_m in H15. lra. lra.
  - rewrite <-H6 in H5. assert (a < b). { destruct H as [J[_[]]]; auto. }
    split; [ |split]; red; intros; split;
    try (rewrite VarUp_dom_a; apply Classifier1; left). exists a,b.
    split; [ |split]; auto; lra. split. apply VarUp_Function. pose proof H8.
    apply H2 in H9 as [δ[]]. exists δ. split; auto. split. red; auto. intros.
    exists (δ/2). split. lra. intros.
    assert (∣((VarUp_Integral_Fun f a)[x0] - (VarUp_Integral_Fun f a)[x])∣
      <= 0 * ∣(x - x0)∣).
    { assert (x0 ∈ \[a, b\]). { apply H10,Classifier1. lra. }
      destruct (Rtotal_order x x0) as [H14|[]]. rewrite Abs_eq_neg,
      (Abs_eq_neg (x-x0)). replace (-(x - x0)) with (x0 - x); [ |lra].
      replace (-((VarUp_Integral_Fun f a)[x0] - (VarUp_Integral_Fun f a)[x]))
      with ((VarUp_Integral_Fun f a)[x] - (VarUp_Integral_Fun f a)[x0]); [ |lra].
      rewrite (Abs_ge (x0 - x)); [ |lra]. apply Lemma9_9; try (apply H1); auto.
      lra. apply Classifier1. lra. intros. apply H5,Classifier1.
      applyClassifier1 H13. lra. rewrite H14,Rminus_diag,Rmult_0_l,Abs_ge; lra.
      rewrite (Abs_ge (x-x0)); [ |lra]. apply Lemma9_9; try (apply H1); auto.
      applyClassifier1 H13. lra. apply Classifier1. lra. intros. apply H5,Classifier1.
      applyClassifier1 H13. lra. } rewrite Rmult_0_l in H13. lra.
    exists a,b. split; [ |split]; auto; lra. split. apply VarUp_Function.
    exists (b-a). split. lra. split. red; intros. applyClassifier1 H8.
    apply H1,Classifier1. lra. intros. exists ((b-a)/2).
    split. lra. intros. rewrite Abs_eq_neg.
    replace (-((VarUp_Integral_Fun f a)[x] - (VarUp_Integral_Fun f a)[a]))
    with ((VarUp_Integral_Fun f a)[a] - (VarUp_Integral_Fun f a)[x]); [ |lra].
    assert (∣((VarUp_Integral_Fun f a)[a] - (VarUp_Integral_Fun f a)[x])∣
      <= 0 * (x - a)).
    { apply Lemma9_9; try (apply H1,Classifier1; lra). lra. intros.
      apply H5,Classifier1. lra. } lra.
    exists a,b. split; [ |split]; auto; lra. split. apply VarUp_Function.
    exists (b-a). split. lra. split. red; intros. applyClassifier1 H8.
    apply H1,Classifier1. lra. intros. exists ((b-a)/2). split. lra. intros.
    assert (∣((VarUp_Integral_Fun f a)[x] - (VarUp_Integral_Fun f a)[b])∣
      <= 0 * (b - x)).
    { apply Lemma9_9; try (apply H1,Classifier1; lra). lra. intros.
      apply H5,Classifier1. lra. } lra.
Qed.

Theorem Theorem9_9b : ∀ f a b, (∃ J, Def_Integral f a b J)
  -> ContinuousClose (VarLow_Integral_Fun f b) a b.
Proof.
  intros. assert (a < b). { destruct H as [J[_[]]]; auto. }
  assert (\[a, b\] ⊂ dom[VarLow_Integral_Fun f b]
    /\ \[a, b\] ⊂ dom[VarUp_Integral_Fun f a]) as [].
  { split; [apply VarLow_dom_b|apply VarUp_dom_b]; auto; lra. }
  assert (dom[(VarLow_Integral_Fun f b)|[\[a, b\]]] = \[a, b\]
    /\ dom[(VarUp_Integral_Fun f a)|[\[a, b\]]] = \[a, b\]) as [].
  { split; apply AxiomI; split; intros; try (apply Classifier1 in H3 as [];
    apply Classifier1 in H3 as []; applyClassifier2 H4; tauto); pose proof H3;
    [apply H1,Classifier1 in H4 as []|apply H2,Classifier1 in H4 as []];
    apply Classifier1; exists x; apply Classifier1; split; auto;
    apply Classifier2; split; auto; apply Classifier1; auto. }
  assert ((VarLow_Integral_Fun f b)|[\[a, b\]]
    = \{\ λ u v, v = (VarUp_Integral_Fun f a)[b] \}\
      \- (VarUp_Integral_Fun f a)|[\[a, b\]]).
  { apply AxiomI; split; intros; destruct z. apply Classifier1 in H5 as [].
    applyClassifier2 H6. destruct H6 as [H6 _]. apply Classifier2; split.
    apply Classifier1. exists (VarUp_Integral_Fun f a)[b]. apply Classifier2; auto.
    split. rewrite H4; auto. rewrite FunValue. pose proof (VarUp_Function f a).
    pose proof @RestrictFun. apply (H8 R R _ (\[a, b\])) in H7. clear H8.
    destruct H7 as [H7[]]. rewrite H9. apply f_x_T in H5. pose proof H6.
    apply Classifier1 in H10 as []. destruct H10. pose proof H0. pose proof H10.
    apply (VarUp_Value_gt f) in H12,H13; try (apply H2,Classifier1; lra).
    destruct H11. pose proof H11. apply (VarLow_Value_lt f) in H14;
    [ |apply H1,Classifier1; lra].
    assert ((VarUp_Integral_Fun f a)[x] + (VarLow_Integral_Fun f b)[x]
      = (VarUp_Integral_Fun f a)[b]).
    { symmetry. eapply Property9_4_4b; eauto. apply Classifier1; auto. }
    rewrite <-H5,<-H15. lra. rewrite <-H5,<-H11,VarLow_Value_eq. lra.
    rewrite <-H5,H10,VarUp_Value_eq,Rminus_0_r. pose proof H0. pose proof H0.
    apply (VarUp_Value_gt f) in H12; apply (VarLow_Value_lt f) in H13; auto.
    eapply Def_Integral_Uni; eauto. apply H1,Classifier1; lra. apply H2,Classifier1; lra.
    apply H1,Classifier1; lra. apply VarLow_Function. rewrite H4; auto.
    applyClassifier2 H5. destruct H5 as [H5[]]. rewrite FunValue in H7.
    rewrite H4 in H6. destruct (RestrictFun (VarUp_Integral_Fun f a) (\[a, b\]))
    as [H8[]]. apply VarUp_Function. rewrite H10 in H7; [ |rewrite H4; auto].
    clear H9 H10. apply Classifier1. split;
    [ |apply Classifier2; split; auto; apply Classifier1; auto].
    pose proof H6. apply Classifier1 in H9 as []. destruct H9. pose proof H9.
    apply (VarUp_Value_gt f) in H11; auto. pose proof H0.
    apply (VarUp_Value_gt f) in H12; auto; [ |apply H2,Classifier1; lra].
    destruct H10. pose proof H10. apply (VarLow_Value_lt f) in H13; auto.
    assert ((VarUp_Integral_Fun f a)[b] = (VarUp_Integral_Fun f a)[x]
      + (VarLow_Integral_Fun f b)[x]).
    { eapply Property9_4_4b; eauto. apply Classifier1; lra. }
    assert (y = (VarLow_Integral_Fun f b)[x]). lra. rewrite H15.
    apply x_fx_T; auto. apply VarLow_Function. rewrite H7,H10,Rminus_diag.
    apply Classifier2; split; [ |split]; intros; auto; exfalso; lra.
    rewrite H7,H9,VarUp_Value_eq,Rminus_0_r. pose proof H0. pose proof H0.
    apply (VarUp_Value_gt f) in H11. apply (VarLow_Value_lt f) in H12.
    replace ((VarUp_Integral_Fun f a)[b]) with ((VarLow_Integral_Fun f b)[a]).
    apply x_fx_T. apply VarLow_Function. apply H1,Classifier1; lra.
    eapply Def_Integral_Uni; eauto. apply H1,Classifier1; lra.
    apply H2,Classifier1; lra. }
  assert (ContinuousClose \{\ λ u v, v = (VarUp_Integral_Fun f a)[b] \}\ a b).
  { assert (∀ x, Continuous \{\ λ u v, v = (VarUp_Integral_Fun f a)[b] \}\ x).
    { intros. split. apply Classifier1. exists (VarUp_Integral_Fun f a)[b].
      apply Classifier2; auto. split. red; intros. applyClassifier2 H6.
      applyClassifier2 H7. rewrite H6,H7; lra. exists 1. split. lra. split.
      red; intros. apply Classifier1. exists (VarUp_Integral_Fun f a)[b].
      apply Classifier2; auto. intros. exists (1/2). split. lra. intros.
      rewrite FunValue,FunValue,Rminus_diag,Abs_ge; auto. lra. }
    split. red; intros; auto. split; apply Theorem4_1; auto. }
  assert (ContinuousClose ((VarUp_Integral_Fun f a)|[\[a, b\]]) a b).
  { assert (∀ h, ContinuousClose h a b -> ContinuousClose (h|[\[a, b\]]) a b).
    { intros. destruct H7 as [H7[]].
      assert (Function h). { destruct H8 as [_[]]; auto. }
      destruct (RestrictFun h (\[a, b\]) H10) as [H11[]].
      split. red; intros. pose proof H14. apply H7 in H15 as [].
      assert (x ∈ dom[h|[\[a, b\]]]).
      { rewrite H12. apply Classifier1; split; auto. apply Classifier1; lra. }
      split; auto. rewrite H13; auto. destruct H16 as [_[x0[H16[]]]].
      split; auto. destruct (Examp2 (x-a) (b-x) x0) as [x1[H20[H21[]]]];
      try lra. exists x1. split; auto.
      assert (Uº(x; x1) ⊂ Uº(x; x0) /\ Uº(x; x1) ⊂ \[a, b\]) as [].
      { split; red; intros; apply Classifier1 in H24 as []. apply Classifier1. lra.
        apply Abs_not_eq_0 in H24. apply Abs_R in H25. apply Classifier1. lra. }
      split. rewrite H12. red; intros. apply Classifier1; auto. intros.
      apply H19 in H26 as [x2[]]. destruct (Examp1 x1 x2) as [x3[H28[]]]; auto.
      lra. exists x3. split; auto. intros. rewrite H13. apply H27. lra.
      rewrite H12. apply Classifier1; split; [apply H25|apply H18]; apply Classifier1;
      lra. split. destruct H8 as [H8[_[x0[H14[]]]]]. split. rewrite H12.
      apply Classifier1; split; auto. apply Classifier1; lra. split; auto.
      destruct (Examp1 x0 (b-a)) as [x1[H17[]]]; try lra. exists x1. split; auto.
      assert (U+º(a; x1) ⊂ U+º(a; x0) /\ U+º(a; x1) ⊂ \[a, b\]) as [].
      { split; red; intros; apply Classifier1 in H20 as []; apply Classifier1; lra. }
      split. rewrite H12. red; intros. apply Classifier1; split; auto. intros.
      apply H16 in H22 as [x2[]]. destruct (Examp1 x1 x2) as [x3[H24[]]]; try lra.
      exists x3. split; auto. intros. rewrite H13,H13. apply H23. lra.
      rewrite H12. apply Classifier1; split; auto. apply Classifier1; lra. rewrite H12.
      apply Classifier1; split. apply H21,Classifier1. lra. apply H15,Classifier1. lra.
      destruct H9 as [H9[_[x0[H14[]]]]]. split. rewrite H12.
      apply Classifier1; split; auto. apply Classifier1; lra. split; auto.
      destruct (Examp1 x0 (b-a)) as [x1[H17[]]]; try lra. exists x1. split; auto.
      assert (U-º(b; x1) ⊂ U-º(b; x0) /\ U-º(b; x1) ⊂ \[a, b\]) as [].
      { split; red; intros; apply Classifier1 in H20 as []; apply Classifier1; lra. }
      split. rewrite H12. red; intros. apply Classifier1; split; auto. intros.
      apply H16 in H22 as [x2[]]. destruct (Examp1 x1 x2) as [x3[H24[]]]; try lra.
      exists x3. split; auto. intros. rewrite H13,H13. apply H23. lra.
      rewrite H12. apply Classifier1; split; auto. apply Classifier1; lra. rewrite H12.
      apply Classifier1; split. apply H21,Classifier1. lra. apply H15,Classifier1. lra. }
    apply H7,Theorem9_9a; auto. }
  apply (Lemma6_10r _ (\[a, b\])). apply VarLow_Function. rewrite H5.
  apply Lemma6_10m; auto.
Qed.

(* a到y的积分减a到x的积分等于x到y的积分 *)
Lemma Lemma9_10 : ∀ f a x y, x ∈ dom[VarUp_Integral_Fun f a]
  -> y ∈ dom[VarUp_Integral_Fun f a]
  -> (VarUp_Integral_Fun f a)[y] - (VarUp_Integral_Fun f a)[x]
    = (VarUp_Integral_Fun f x)[y] /\ y ∈ dom[VarUp_Integral_Fun f x].
Proof.
  intros. assert (y ∈ dom[VarUp_Integral_Fun f x]).
  { rewrite VarUp_dom_a in *. apply Classifier1 in H as [[a0[b0[H[]]]]|].
    apply Classifier1 in H0 as [[a1[b1[H0[]]]]|]. apply Classifier1. left.
    assert (a0 < b0 /\ a1 < b1 /\ a0 <= b1 /\ a1 <= b0) as [H5[H6[]]].
    { destruct H2 as [J1[_[]]], H4 as [J2[_[]]]. split; auto. split; auto. lra. }
    destruct (Rle_or_lt a1 a0), (Rle_or_lt b1 b0). exists a1,b0. split. lra.
    split. lra. destruct H10. apply (Lemma9_5c f a1 b1 b0); auto.
    apply (Subset_Def_Integral f a0 b0); auto. lra. rewrite <-H10; auto.
    exists a1,b1. split; auto. lra. exists a0,b0. split; auto. split; auto.
    lra. exists a0,b1. split. lra. split. lra. apply (Lemma9_5c f a0 a1); auto.
    apply (Subset_Def_Integral f a0 b0); auto. lra. rewrite H0. apply Classifier1.
    left. eauto. apply Classifier1 in H0 as [[a0[b0[H0[]]]]|]. apply Classifier1. left.
    rewrite H. eauto. apply Classifier1. right. rewrite H,H0; auto. } split; auto.
  destruct (Rtotal_order a y) as [H2|[]], (Rtotal_order a x) as [H3|[]].
  pose proof H2. pose proof H3. apply (VarUp_Value_gt f) in H4,H5; auto.
  destruct (Rtotal_order x y) as [H6|[]]. pose proof H6.
  apply (VarUp_Value_gt f) in H6; auto.
  assert ((VarUp_Integral_Fun f a)[y] = (VarUp_Integral_Fun f a)[x]
    + (VarUp_Integral_Fun f x)[y]).
  { eapply Property9_4_4b; eauto. apply Classifier1; lra. } lra.
  rewrite H6 in *. rewrite VarUp_Value_eq. lra. pose proof H6.
  apply (VarUp_Value_lt f) in H6; auto.
  assert ((VarUp_Integral_Fun f a)[x] = (VarUp_Integral_Fun f a)[y]
    - (VarUp_Integral_Fun f x)[y]).
  { eapply Property9_4_4b; eauto. apply Classifier1; lra. } lra.
  rewrite H3,VarUp_Value_eq. lra. assert (x < y). lra.
  pose proof H2. pose proof H3. pose proof H4. apply (VarUp_Value_gt f)
  in H5,H7; auto. apply Rgt_lt,(VarUp_Value_lt f) in H6; auto.
  assert ((VarUp_Integral_Fun f x)[y]
    = -(VarUp_Integral_Fun f a)[x] + (VarUp_Integral_Fun f a)[y]).
  { eapply Property9_4_4b; eauto. apply Classifier1; lra. } lra.
  rewrite <-H2 in *. rewrite VarUp_Value_eq. pose proof H3.
  apply (VarUp_Value_gt f) in H3; auto. apply Rlt_gt,(VarUp_Value_lt f) in H4;
  auto. apply (Def_Integral_Uni f a x (VarUp_Integral_Fun f a)[x]) in H4; auto.
  lra. rewrite <-H2,<-H3,VarUp_Value_eq. lra. rewrite H2 in *.
  rewrite VarUp_Value_eq,Rminus_0_l. pose proof H3. apply (VarUp_Value_gt f)
  in H3; auto. apply Rgt_lt,(VarUp_Value_lt f) in H4; auto.
  eapply Def_Integral_Uni; eauto. assert (y < x). lra. pose proof H2.
  pose proof H3. pose proof H4. apply Rgt_lt in H5.
  apply (VarUp_Value_gt f) in H6; auto. apply (VarUp_Value_lt f) in H5,H7; auto.
  assert (-(VarUp_Integral_Fun f x)[y]
    = -(VarUp_Integral_Fun f a)[y] + (VarUp_Integral_Fun f a)[x]).
  { eapply Property9_4_4b; eauto. apply Classifier1; lra. } lra.
  rewrite H3,VarUp_Value_eq. lra. destruct (Rtotal_order x y) as [H4|[]].
  pose proof H2. pose proof H3. pose proof H4. apply Rgt_lt in H5,H6.
  apply (VarUp_Value_lt f) in H5,H6; auto. apply (VarUp_Value_gt f) in H7; auto.
  assert (-(VarUp_Integral_Fun f a)[x]
    = (VarUp_Integral_Fun f x)[y] - (VarUp_Integral_Fun f a)[y]).
  { eapply Property9_4_4b; eauto. apply Classifier1; lra. } lra.
  rewrite H4,VarUp_Value_eq. lra. pose proof H2. pose proof H3. pose proof H4.
  apply Rgt_lt,(VarUp_Value_lt f) in H5,H6,H7; auto.
  assert (-(VarUp_Integral_Fun f a)[y]
    = -(VarUp_Integral_Fun f x)[y] - (VarUp_Integral_Fun f a)[x]).
  { eapply Property9_4_4b; eauto. apply Classifier1; lra. } lra.
Qed.

(* 原函数存在性 *)
Theorem Theorem9_10 : ∀ f a b, a < b -> ContinuousClose f a b
  -> (∀ x, x ∈ \(a, b\) -> Derivative (VarUp_Integral_Fun f a) x f[x])
    /\ Derivative_pos (VarUp_Integral_Fun f a) a f[a]
    /\ Derivative_neg (VarUp_Integral_Fun f a) b f[b].
Proof.
  intros. assert (∃ J, Def_Integral f a b J). { apply Theorem9_4; auto. }
  assert (\[a, b\] ⊂ dom[f] /\ \[a, b\] ⊂ dom[VarUp_Integral_Fun f a]) as [].
  { split. destruct H1 as [J[_[_[]]]]; auto. apply VarUp_dom_b; auto. lra. }
  assert (Function f /\ Function (VarUp_Integral_Fun f a)) as [].
  { destruct H1 as [J[]]. split; auto. apply VarUp_Function. } split; [ |split].
  - intros. split; auto. assert (∃ δ, δ > 0 /\ U(x; δ) ⊂ \(a, b\)) as [δ[]].
    { apply Classifier1 in H6 as []. destruct (Rle_or_lt (x-a) (b-x));
      [exists (x - a)|exists (b - x)]; split; try lra; red; intros;
      apply Classifier1; apply Classifier1,Abs_R in H9; lra. }
    split. exists δ. split; auto. red; intros. apply H3,Classifier1.
    apply H8,Classifier1 in H9 as []; lra.
    split. red; intros. applyClassifier2 H9. applyClassifier2 H10. rewrite H9,H10; auto. exists δ. split; auto.
    split. red; intros. apply Classifier1. exists
    (((VarUp_Integral_Fun f a)[z] - (VarUp_Integral_Fun f a)[x])/(z - x)).
    apply Classifier2; auto. intros. assert (a < x < b). { applyClassifier1 H6; auto. }
    destruct H0 as [H0 _]. apply H0 in H10 as [_[_[δ1[H10[]]]]].
    pose proof H9. apply H12 in H13 as [δ2[]].
    destruct (Examp1 δ δ2) as [δ3[H15[]]]; auto. lra. exists δ3. split. auto.
    intros. assert (\(a, b\) ⊂ \[a, b\]).
    { red; intros. applyClassifier1 H19. apply Classifier1. lra. }
    pose proof H6. apply H19,H3 in H20. rewrite FunValue.
    apply (Lemma9_10 f a x x0) in H20 as []; auto;
    [ |apply H3,H19,H8,Classifier1; lra].
    assert (x0 ∈ U(x; δ) /\ x ∈ U(x; δ)) as [].
    { split; apply Classifier1. lra. rewrite Abs_ge; lra. }
    assert (Continuous f x0 /\ Continuous f x) as [].
    { apply H8,Classifier1 in H22 as [], H23 as []. split; apply H0; auto. }
    rewrite H20. destruct (Rtotal_order x0 x) as [H26|[]].
    + assert (ContinuousClose f x0 x).
      { split. red; intros. apply H0.
        assert (x1 ∈ U(x; δ)).
        { apply Classifier1. rewrite Abs_lt; [ |lra].
          rewrite Abs_lt in H18; [ |lra]. lra. }
        apply H8,Classifier1 in H28 as []; auto. split; apply Theorem4_1; auto. }
      apply Theorem9_7 in H27 as [x1[]]; auto. pose proof H26.
      apply Rlt_gt,(VarUp_Value_lt f) in H29; auto.
      assert (-(VarUp_Integral_Fun f x)[x0] = f[x1] * (x - x0)).
      { eapply Def_Integral_Uni; eauto. }
      assert ((VarUp_Integral_Fun f x)[x0] = f[x1] * (x0 - x)). lra.
      rewrite H31. unfold Rdiv. rewrite Rinv_r_simpl_l; [ |lra].
      destruct (classic (x1 = x)) as [H32|H32]. rewrite H32,Abs_ge; lra.
      apply H14. applyClassifier1 H27. rewrite Abs_lt; [ |lra].
      rewrite Abs_lt in H18; lra.
    + rewrite H26,Abs_ge in H18; [ |lra]. exfalso. lra.
    + assert (ContinuousClose f x x0).
      { split. red; intros. apply H0.
        assert (x1 ∈ U(x; δ)).
        { apply Classifier1. rewrite Abs_ge; [ |lra].
          rewrite Abs_ge in H18; [ |lra]. lra. }
        apply H8,Classifier1 in H28 as []; auto. split; apply Theorem4_1; auto. }
      apply Theorem9_7 in H27 as [x1[]]; auto. pose proof H26.
      apply Rlt_gt,(VarUp_Value_gt f) in H29; auto.
      assert ((VarUp_Integral_Fun f x)[x0] = f[x1] * (x0 - x)).
      { eapply Def_Integral_Uni; eauto. } unfold Rdiv.
      rewrite H30,Rinv_r_simpl_l; [ |lra].
      destruct (classic (x1 = x)) as [H31|H31]. rewrite H31,Abs_ge; lra.
      apply H14. applyClassifier1 H27. rewrite Abs_ge; [ |lra].
      rewrite Abs_ge in H18; [ |lra]. lra.
  - split; auto. assert (U+(a; (b-a)) ⊂ dom[VarUp_Integral_Fun f a]).
    { red; intros. apply H3,Classifier1. applyClassifier1 H6. lra. }
    split. exists (b-a). split; auto. lra. split. red; intros.
    applyClassifier2 H7. applyClassifier2 H8. rewrite H7,H8; auto.
    pose proof H0 as [_[[H7[H8[δ[H9[]]]]] _]]. exists δ. split; auto. split.
    red; intros. apply Classifier1. exists (((VarUp_Integral_Fun f a)[z]
      - (VarUp_Integral_Fun f a)[a]) / (z - a)). apply Classifier2; auto.
    intros. pose proof H12. apply H11 in H13 as [δ1[]].
    destruct (Examp1 (b-a) δ1) as [δ2[H15[]]]; auto. lra. lra. exists δ2.
    split. lra. intros. rewrite FunValue,VarUp_Value_eq,Rminus_0_r. destruct H18.
    pose proof H18. apply (VarUp_Value_gt f) in H20; [ |apply H6,Classifier1; lra].
    assert (ContinuousClose f a x).
    { destruct H0 as [H0[]]. split. red; intros. apply H0. lra. split; auto.
      apply Theorem4_1. apply H0. lra. }
    apply Theorem9_7 in H21 as [x0[]]; auto.
    replace ((VarUp_Integral_Fun f a)[x]) with (f[x0] * (x - a)).
    unfold Rdiv. rewrite Rinv_r_simpl_l; [ |lra]. destruct (classic (x0 = a)).
    rewrite H23,Abs_ge; lra. apply H14. applyClassifier1 H21. lra.
    eapply Def_Integral_Uni; eauto.
  - split; auto. assert (U-(b; (b-a)) ⊂ dom[VarUp_Integral_Fun f a]).
    { red; intros. apply H3,Classifier1. applyClassifier1 H6. lra. }
    split. exists (b-a). split; auto. lra. split. red; intros.
    applyClassifier2 H7. applyClassifier2 H8. rewrite H7,H8; auto.
    pose proof H0 as [_[_[H7[H8[δ[H9[]]]]]]]. exists δ. split; auto. split.
    red; intros. apply Classifier1. exists (((VarUp_Integral_Fun f a)[z]
      - (VarUp_Integral_Fun f a)[b]) / (z - b)). apply Classifier2; auto.
    intros. pose proof H12. apply H11 in H13 as [δ1[]].
    destruct (Examp1 (b-a) δ1) as [δ2[H15[]]]; auto. lra. lra. exists δ2.
    split. lra. intros. rewrite FunValue.
    assert (x ∈ dom[VarUp_Integral_Fun f a] /\ b ∈ dom[VarUp_Integral_Fun f a]).
    { split; apply H3,Classifier1; lra. } destruct H19. pose proof H19.
    apply (Lemma9_10 f a x b) in H21 as []; auto. pose proof H18 as [_].
    apply (VarUp_Value_gt f) in H23; auto. assert (ContinuousClose f x b).
    { destruct H0 as [H0[]]. split. red; intros. apply H0. lra. split; auto.
      apply Theorem4_1,H0. lra. } apply Theorem9_7 in H24 as [x0[]]; [ |lra].
    assert ((VarUp_Integral_Fun f x)[b] = f[x0] * (b - x)).
    { eapply Def_Integral_Uni; eauto. } rewrite H26 in H21.
    replace ((VarUp_Integral_Fun f a)[x] - (VarUp_Integral_Fun f a)[b]) with
    (f[x0] * (x - b)); [ |lra]. unfold Rdiv. rewrite Rinv_r_simpl_l; [ |lra].
    destruct (classic (x0 = b)). rewrite H27,Abs_ge; auto; lra.
    apply H14. applyClassifier1 H24. lra.
Qed.

(* 变上限积分函数是被积函数的原函数 *)
Corollary Corollary9_10a : ∀ f a b, a < b -> ContinuousClose f a b
  -> Primitive_Close f (VarUp_Integral_Fun f a) a b.
Proof.
  intros. assert (Function f). { destruct H0 as [_[[_[]]]]; auto. }
  split; auto. split. apply VarUp_Function. split; auto.
  assert (\[a, b\] ⊂ dom[f] /\ \[a, b\] ⊂ dom[VarUp_Integral_Fun f a]) as [].
  { pose proof H0. apply Theorem9_4 in H2 as [J[_[H2[]]]]; auto. split; auto.
    apply VarUp_dom_b; [ |lra]. apply Theorem9_4; auto. }
  split; auto. split; auto. apply Theorem9_10; auto.
Qed.

(* 变上限积分函数与任意原函数只相差一个常数 *)
Corollary Corollary9_10b : ∀ f F a b, a < b
  -> ContinuousClose f a b -> Primitive_Close f F a b
  -> ∃ C, (∀ x, x ∈ \[a, b\] -> F[x] = (VarUp_Integral_Fun f a)[x] + C).
Proof.
  intros. pose proof H0. apply Corollary9_10a in H2; auto.
  pose proof H1 as [H3[H4[H5[H6[H7[H8[]]]]]]].
  pose proof H2 as [_[H11[_[_[H12[H13[]]]]]]]; auto.
  assert (Primitive_Open f F a b
    /\ Primitive_Open f (VarUp_Integral_Fun f a) a b).
  { assert (\(a, b\) ⊂ dom[f] /\ \(a, b\) ⊂ dom[F]
      /\ \(a, b\) ⊂ dom[VarUp_Integral_Fun f a]) as [H16[]].
    { split; [ |split]; red; intros; [apply H6|apply H7|apply H12];
      apply Classifier1; applyClassifier1 H16; lra. } split; split; auto. }
  apply Theorem8_2b in H16 as [C]; auto.
  assert (ContinuousRight F a /\ ContinuousRight (VarUp_Integral_Fun f a) a).
  { split; apply Corollary5_1b; eauto. } destruct H17 as [[][]].
  assert (ContinuousLeft F b /\ ContinuousLeft (VarUp_Integral_Fun f a) b).
  { split; apply Corollary5_1a; eauto. } destruct H21 as [[][]].
  assert (limit_pos (F \- (VarUp_Integral_Fun f a)) a
    (F[a] - (VarUp_Integral_Fun f a)[a])). { apply Lemma6_10e; auto. }
  assert (limit_neg (F \- (VarUp_Integral_Fun f a)) b
    (F[b] - (VarUp_Integral_Fun f a)[b])). { apply Lemma6_10i; auto. }
  assert (limit_pos (F \- (VarUp_Integral_Fun f a)) a C).
  { split. apply Corollary_sub_fun_a. exists (b-a). split. lra. split.
    red; intros. rewrite Corollary_sub_fun_c. apply Classifier1; split;
    [apply H7|apply H12]; apply Classifier1; applyClassifier1 H27; lra.
    intros. exists ((b-a)/2). split. lra. intros.
    assert (x ∈ \(a, b\) /\ x ∈ \[a, b\]) as [].
    { split; apply Classifier1; lra. } rewrite Corollary_sub_fun_b; auto.
    rewrite H16; auto. rewrite Abs_ge; lra. }
  assert (limit_neg (F \- (VarUp_Integral_Fun f a)) b C).
  { split. apply Corollary_sub_fun_a. exists (b-a). split. lra. split.
    red; intros. rewrite Corollary_sub_fun_c. apply Classifier1; split;
    [apply H7|apply H12]; apply Classifier1; applyClassifier1 H28; lra.
    intros. exists ((b-a)/2). split. lra. intros.
    assert (x ∈ \(a, b\) /\ x ∈ \[a, b\]) as [].
    { split; apply Classifier1; lra. } rewrite Corollary_sub_fun_b; auto.
    rewrite H16; auto. rewrite Abs_ge; lra. }
  exists C. intros. apply Classifier1 in H29 as [[][]].
  assert (x ∈ \(a, b\)). { apply Classifier1; auto. } apply H16 in H31. lra.
  rewrite H30. assert (F[b] - (VarUp_Integral_Fun f a)[b] = C).
  { eapply Theorem3_2c; eauto. } lra. rewrite H29.
  assert (F[a] - (VarUp_Integral_Fun f a)[a] = C). { eapply Theorem3_2b; eauto. }
  lra. exfalso. lra.
Qed.

(* 牛顿-莱布尼兹公式的另一证明: 利用变上限积分函数证明 *)
Corollary Corollary9_10c : ∀ f F a b, a < b -> ContinuousClose f a b
  -> Primitive_Close f F a b -> Def_Integral f a b (F[b] - F[a]).
Proof.
  intros. pose proof H1. apply Corollary9_10b in H2 as [C]; auto.
  assert (F[b] = (VarUp_Integral_Fun f a)[b] + C
    /\ F[a] = (VarUp_Integral_Fun f a)[a] + C) as [].
  { split; apply H2,Classifier1; lra. }
  rewrite H3,H4,VarUp_Value_eq.
  replace ((VarUp_Integral_Fun f a)[b] + C - (0 + C)) with
  (VarUp_Integral_Fun f a)[b]; [ |lra]. apply VarUp_Value_gt; auto.
  assert (\[a, b\] ⊂ dom[VarUp_Integral_Fun f a]).
  { apply VarUp_dom_b. apply Theorem9_4; auto. lra. }
  apply H5,Classifier1; lra.
Qed.


Lemma Lemma9_11a : ∀ f T a b n, (∃ J, Def_Integral f a b J) -> Seg T a b (S n)
  -> (VarUp_Integral_Fun f a)[b]
    = Σ \{\ λ u v, v = (VarUp_Integral_Fun f T[u])[T[S u]] \}\ n.
Proof.
  intros. generalize dependent T. generalize dependent b. induction n; intros.
  - simpl. rewrite FunValue. destruct H0 as [_[_[_[_[]]]]]. rewrite H0,H1; auto.
  - set (T1 := \{\ λ u v, (u <= (S n))%nat /\ v = T[u] \}\).
    assert (Function T1).
    { red; intros. applyClassifier2 H1. applyClassifier2 H2.
      destruct H1,H2. lra. }
    assert (dom[T1] = \{ λ u, (u <= S n)%nat \}).
    { apply AxiomI; split; intros. apply Classifier1 in H2 as [].
      applyClassifier2 H2. destruct H2. apply Classifier1; auto.
      applyClassifier1 H2. apply Classifier1. exists T[z]. apply Classifier2; auto. }
    assert (∀ k, (k <= S n)%nat -> T1[k] = T[k]).
    { intros. assert (k ∈ dom[T1]). { rewrite H2. apply Classifier1; auto. }
      apply x_fx_T in H4; auto. applyClassifier2 H4. destruct H4; auto. }
    assert (Seg T1 a T[S n] (S n)).
    { destruct H0 as [_[_[_[H0[]]]]]. split; auto. split. lia. split; auto.
      split. intros. rewrite H3,H3; auto. lia. rewrite H3,H3; auto. lia. }
    assert (a < T[S n] < b).
    { pose proof H0 as [_[_[_[_[]]]]]. rewrite <-H5,<-H6.
      split; apply (Seg_StrictlyIncrease_a T a b (S (S n))); auto; lia. }
    assert (∃ J, Def_Integral f a T[S n] J).
    { destruct (Property9_4_4a f a b) as [H6 _]. destruct H as [J[_[]]]; auto.
      apply H6 in H5 as [J1[J2[]]]; eauto. }
    pose proof H4. apply IHn in H7; auto. simpl. rewrite FunValue.
    assert (Σ \{\ λ u v, v = (VarUp_Integral_Fun f T [u])[T[S u]] \}\ n
      = Σ \{\ λ u v, v = (VarUp_Integral_Fun f T1 [u])[T1[S u]] \}\ n).
    { apply Σ_Fact5. intros. rewrite FunValue,FunValue,H3,H3; auto; lia. }
    rewrite H8,<-H7. pose proof H0 as [_[_[_[_[]]]]]. rewrite H10.
    assert (\[a, b\] ⊂ dom[VarUp_Integral_Fun f a]).
    { apply VarUp_dom_b; auto. lra. }
    assert (b ∈ dom[VarUp_Integral_Fun f a]
      /\ T[S n] ∈ dom[VarUp_Integral_Fun f a]) as [].
    { split; apply H11,Classifier1; lra. }
    apply (Lemma9_10 f a T[S n]) in H12 as []; auto. lra.
Qed.

Lemma Lemma9_11b : ∀ f g φ T a b n, (∃ J, Def_Integral f a b J)
  -> (∃ J, Def_Integral g a b J) -> Seg T a b (S n)
  -> Σ \{\ λ u v, v = (VarUp_Integral_Fun (f \* g) T[u])[T[S u]] \}\ n
    = Σ \{\ λ u v, v = (VarUp_Integral_Fun ((g \- \{\ λ i j, j = φ u \}\) \* f)
      T[u])[T[S u]] \}\ n
    + Σ \{\ λ u v, v = (φ u) * (VarUp_Integral_Fun f T[u])[T[S u]] \}\ n.
Proof.
  intros. assert (∀ h h1 h2 n, (∀ k, (k <= n)%nat -> h[k] = h1[k] + h2[k])
    -> Σ h n = Σ h1 n + Σ h2 n).
  { intros. induction n0. simpl. apply H2. lia. simpl. rewrite IHn0,H2. lra.
    lia. intros. apply H2. lia. }
  apply H2. intros. rewrite FunValue,FunValue,FunValue.
  assert (∀ x h r, x ∈ dom[h] -> (h \\* r)[x] = h[x] * r).
  { intros. assert (x ∈ dom[h \\* r]). { rewrite Corollary_mult_fun_d; auto. }
    assert (Function (h \\* r)).
    { red; intros. applyClassifier2 H6. applyClassifier2 H7.
      destruct H6 as [], H7 as []. lra. }
    apply x_fx_T in H5; auto. applyClassifier2 H5. tauto. }
  assert ((g \- \{\ λ i j, j = φ k \}\) \* f = (f \* g) \- (f \\* (φ k))).
  { apply AxiomI; split; intros; destruct z. applyClassifier2 H5.
    destruct H5 as [H5[]]. rewrite Corollary_sub_fun_c in H5.
    apply Classifier1 in H5 as []. apply Classifier2; split.
    rewrite Corollary_mult_fun_c. apply Classifier1; auto. split.
    rewrite Corollary_mult_fun_d; auto. rewrite Corollary_mult_fun_b,H4; auto.
    rewrite Corollary_sub_fun_b,FunValue in H7; auto. lra.
    applyClassifier2 H5. destruct H5 as [H5[]]. rewrite Corollary_mult_fun_c in H5.
    apply Classifier1 in H5 as []. apply Classifier2; split; [ |split]; auto.
    rewrite Corollary_sub_fun_c. apply Classifier1; split; auto. apply Classifier1.
    exists (φ k). apply Classifier2; auto. rewrite Corollary_mult_fun_b,H4 in H7;
    auto. rewrite Corollary_sub_fun_b,FunValue; auto. lra. apply Classifier1.
    exists (φ k). apply Classifier2; auto. } rewrite H5. clear H5.
  assert (T[k] < T[S k]). { destruct H1 as [_[_[_[]]]]. apply H1. lia. }
  assert (a <= T[k] /\ T[S k] <= b) as [].
  { pose proof H1 as [_[_[_[_[]]]]]. rewrite <-H6,<-H7.
    split; apply (Seg_Increase_a T a b (S n)); auto; lia. }
  assert (\[a, b\] ⊂ dom[VarUp_Integral_Fun (f \* g) T[k]]
    /\ \[a, b\] ⊂ dom[VarUp_Integral_Fun ((f \* g) \- (f \\* (φ k))) T[k]]
    /\ \[a, b\] ⊂ dom[VarUp_Integral_Fun f T[k]]) as [H8[]].
  { assert (∃ J, Def_Integral (f \* g) a b J). { apply Property9_4_3; auto. }
    split; [ |split]; apply VarUp_dom_b; auto; try lra. destruct H8 as [J1].
    destruct H as [J2]. exists (J1 - (φ k) * J2). apply Property9_4_2b; auto.
    apply Property9_4_1; auto. }
  pose proof H5. pose proof H5. pose proof H5.
  apply (VarUp_Value_gt (f \* g)) in H11; [ |apply H8,Classifier1; lra].
  apply (VarUp_Value_gt ((f \* g) \- (f \\* (φ k))) T[k]) in H12;
  [ |apply H9,Classifier1; lra].
  apply (VarUp_Value_gt f T[k]) in H13; [ |apply H10,Classifier1; lra].
  apply (Property9_4_1 f T[k] T[S k] _ (φ k)) in H13.
  assert (f \* g = ((f \* g) \- (f \\* (φ k))) \+ (f \\* (φ k))).
  { apply AxiomI; split; intros; destruct z. applyClassifier2 H14.
    destruct H14 as [H14[]]. apply Classifier2; split; [ |split].
    rewrite Corollary_sub_fun_c. rewrite Corollary_mult_fun_c,Corollary_mult_fun_d.
    apply Classifier1; split; auto. apply Classifier1; auto.
    rewrite Corollary_mult_fun_d; auto.
    rewrite Corollary_sub_fun_b,H4,Corollary_mult_fun_b; auto. lra.
    rewrite Corollary_mult_fun_c. apply Classifier1; auto.
    rewrite Corollary_mult_fun_d; auto. applyClassifier2 H14.
    destruct H14 as [H14[]]. rewrite Corollary_sub_fun_c in H14.
    apply Classifier1 in H14 as []. rewrite Corollary_sub_fun_b in H16; auto.
    rewrite Corollary_mult_fun_c in H14. apply Classifier1 in H14 as [].
    apply Classifier2; repeat split; auto.
    rewrite Corollary_mult_fun_b in H16; auto. lra. }
  assert (Def_Integral (f \* g) T[k] T[S k]
    ((VarUp_Integral_Fun ((f \* g) \- (f \\* (φ k))) T[k])[T[S k]]
    + (φ k) * (VarUp_Integral_Fun f T[k])[T[S k]])).
  { rewrite H14 at 1. apply Property9_4_2a; auto. }
  eapply Def_Integral_Uni; eauto.
Qed.

Lemma Lemma9_11c : ∀ f g a b, (∃ J, Def_Integral f a b J)
  -> (∃ J, Def_Integral g a b J) -> (∀ ε, ε > 0 -> ∃ T n, Seg T a b (S n)
    /\ (∀ φ, (φ = (fun k => g[T[k]]) \/ φ = (fun k => g[T[S k]]))
      -> ∣(Σ \{\ λ u v, v = (VarUp_Integral_Fun
      ((g \- \{\ λ i j, j = φ u \}\) \* f) T[u])[T[S u]] \}\ n)∣ < ε)).
Proof.
  intros. assert (Function f /\ a < b) as []. { destruct H as [J[H[]]]; auto. }
  pose proof H as [J]. apply Theorem9_2 in H4 as [_[H4[M]]]; auto.
  set (L := M + 1). assert (∀ x, x ∈ \[a, b\] -> ∣(f[x])∣ < L).
  { intros. apply H5 in H6. unfold L. lra. }
  assert (0 < L).
  { assert ((a+b)/2 ∈ \[a, b\]). { apply Classifier1. lra. } apply H5 in H7.
    assert (M < L). { unfold L. lra. } pose proof (Abs_Rge0 (f[(a+b)/2])). lra. }
  pose proof H0. apply Theorem9_3b in H8 as []; auto.
  assert (ε/L > 0). { apply Rlt_gt,Rdiv_lt_0_compat; auto. } pose proof H10.
  apply H9 in H11 as [T[n[]]]. exists T,n. split; auto.
  assert (∀ h m, ∣(Σ \{\ λ u v, v = h u \}\ m)∣
    <= Σ \{\ λ u v, v = ∣(h u)∣ \}\ m).
  { intros. induction m. simpl. rewrite FunValue,FunValue. lra.
    simpl. rewrite FunValue,FunValue.
    assert (∣((Σ \{\ λ u v, v = (h u) \}\ m) + (h (S m)))∣
      <= ∣(Σ \{\ λ u v, v = (h u) \}\ m)∣ + ∣(h (S m))∣).
    { apply Abs_plus_le. } lra. }
  assert (∀ h c d T0 m, Seg T0 c d (S m)
    -> (∀ k, (k <= m)%nat -> (∃ J, Def_Integral (h k) T0[k] T0[S k] J))
    -> Σ \{\ λ u v, v = ∣((VarUp_Integral_Fun (h u) T0[u])[T0[S u]])∣ \}\ m
      <= Σ \{\ λ u v, v = (VarUp_Integral_Fun \{\ λ i j, i ∈ dom[h u]
        /\ j = ∣((h u)[i])∣ \}\ T0[u])[T0[S u]] \}\ m).
  { intros. apply Rge_le,Σ_Fact3. intros. rewrite FunValue,FunValue.
    assert (\[T0[i], T0[S i]\] ⊂ dom[VarUp_Integral_Fun \{\ λ u v, u ∈ dom[h i]
      /\ v = ∣((h i)[u])∣ \}\ T0[i]]
      /\ \[T0[i], T0[S i]\] ⊂ dom[VarUp_Integral_Fun (h i) T0[i]]).
    { assert (T0[i] <= T0[i] <= T0[S i]).
      { split. lra. apply (Seg_Increase_a T0 c d (S m)); auto. lia. }
      split; apply VarUp_dom_b; auto. apply Property9_4_6a; auto. } destruct H17.
    assert (T0[S i] ∈ \[T0[i], T0[S i]\]).
    { apply Classifier1; split; [ |lra].
      apply Rle_ge,(Seg_Increase_a T0 c d (S m)); auto. lia. }
    assert (T0[i] < T0[S i]). { destruct H14 as [_[_[_[]]]]. apply H14; lia. }
    pose proof H20. pose proof H20. apply (VarUp_Value_gt (h i)) in H21; auto.
    apply (VarUp_Value_gt \{\ λ u v, u ∈ dom[h i] /\ v = ∣((h i)[u])∣ \}\)
    in H22; auto. apply Rle_ge. eapply Property9_4_6b; eauto. } intros.
  pose proof (H13 (fun u => (VarUp_Integral_Fun
  ((g \- \{\ λ i j, j = φ u \}\) \* f) T[u])[T[S u]]) n). simpl in H16.
  assert (∀ k, (k <= n)%nat -> ∃ J,
    Def_Integral ((g \- \{\ λ i j, j = φ k \}\) \* f) T[k] T[S k] J).
  { intros. assert (T[k] < T[S k] /\ a <= T[k] /\ T[S k] <= b) as [H18[]].
    { pose proof H11 as [_[_[_[H18[]]]]]. split. apply H18. lia. rewrite <-H19,
      <-H20. split; apply (Seg_Increase_a T a b (S n)); auto; lia. }
    apply Property9_4_3. assert (∃ J1, Def_Integral g T[k] T[S k] J1) as [J1].
    { apply (Subset_Def_Integral g a b); auto. }
    exists (J1 - (φ k) * (T[S k] - T[k])). apply Property9_4_2b; auto.
    apply Lemma9_7; auto. apply (Subset_Def_Integral f a b); auto. }
  intros. apply (H14 _ a b) in H17; auto.
  assert (Σ \{\ λ u v, v = (amp g (\[T[u], T[S u]\])) * (T[S u] - T[u]) * L \}\ n
    >= Σ \{\ λ u v, v = (VarUp_Integral_Fun \{\ λ i j,
      i ∈ dom[(g \- \{\ λ i0 j0, j0 = φ u \}\) \* f]
      /\ j = ∣(((g \- \{\ λ i0 j0, j0 = φ u \}\) \* f) [i])∣ \}\
      T[u])[T[S u]] \}\ n).
  { apply Σ_Fact3. intros. rewrite FunValue,FunValue.
    assert (T[i] < T[S i] /\ a <= T[i] /\ T[S i] <= b) as [H19[]].
    { pose proof H11 as [_[_[_[H19[]]]]]. split. apply H19. lia.
      rewrite <-H20,<-H21. split; apply (Seg_Increase_a T a b (S n)); auto; lia. }
    assert (\[T[i], T[S i]\] ⊂ dom[VarUp_Integral_Fun
      \{\ λ u v, u ∈ dom[(g \- \{\ λ i0 j, j = φ i \}\) \* f] /\
      v = ∣(((g \- \{\ λ i0 j, j = φ i \}\) \* f)[u])∣ \}\ T[i]]).
    { apply VarUp_dom_b. apply Property9_4_6a. pose proof H. pose proof H0.
      apply (Subset_Def_Integral f a b T[i] T[S i]) in H22 as [J1]; auto.
      apply (Subset_Def_Integral g a b T[i] T[S i]) in H23 as [J2]; auto.
      apply Property9_4_3; eauto. exists (J2 - (φ i) * (T[S i] - T[i])).
      apply Property9_4_2b; auto. apply Lemma9_7; auto. lra. }
    assert (T[S i] ∈ \[T[i], T[S i]\]). { apply Classifier1. lra. }
    apply H22,(VarUp_Value_gt _ T[i] T[S i]) in H23; auto.
    assert (Def_Integral (\{\ λ u v, v = (amp g (\[T[i], T[S i]\])) * L \}\)
      T[i] T[S i] ((amp g (\[T[i], T[S i]\])) * L * (T[S i] - T[i]))).
    { apply Lemma9_7; auto. } replace ((amp g (\[T[i], T[S i]\])) * (T[S i]
    - T[i]) * L) with ((amp g (\[T[i], T[S i]\])) * L * (T[S i] - T[i])); [ |lra].
    assert (∀ x, x ∈ \[T[i], T[S i]\]
      -> (\{\ λ u v, u ∈ dom[(g \- \{\ λ i0 j, j = φ i \}\) \* f] /\
      v = ∣(((g \- \{\ λ i0 j, j = φ i \}\) \* f)[u])∣ \}\)[x]
      <= (\{\ λ u v, v = (amp g (\[T[i], T[S i]\])) * L \}\)[x]).
    { intros. rewrite FunValue. pose proof H23 as [H26[_[H27 _]]].
      pose proof H25. apply H27,x_fx_T in H28; auto. applyClassifier2 H28.
      destruct H28; auto. rewrite H29. rewrite Corollary_mult_fun_c in H28.
      apply Classifier1 in H28 as []. rewrite Corollary_mult_fun_b; auto.
      rewrite Corollary_sub_fun_c in H28. apply Classifier1 in H28 as [].
      rewrite Corollary_sub_fun_b,FunValue; auto. rewrite Abs_mult.
      apply Rmult_le_compat; try (apply Rge_le,Abs_Rge0).
      assert (∃ J1, Def_Integral g T[i] T[S i] J1) as [J1].
      { apply (Subset_Def_Integral g a b); auto. }
      apply Theorem9_2 in H32; auto. apply Lemma9_4_3c in H32 as [H32 _]; auto.
      apply H32,Classifier1. destruct H15. exists x,T[i]. split; auto. split.
      apply Classifier1; lra. rewrite H15. auto. exists x,T[S i]. split; auto. split.
      apply Classifier1; lra. rewrite H15. auto. exists ((T[i] + T[S i])/2).
      apply Classifier1. lra. destruct H0 as [J2[]]; auto.
      assert (\[T[i], T[S i]\] ⊂ \[a, b\]).
      { red; intros. apply Classifier1 in H32 as []. apply Classifier1. lra. }
      apply H32,H6 in H25. lra. }
    apply Rle_ge. eapply Corollary9_4_5; eauto. }
  assert ((Σ \{\ λ u v, v = (amp g (\[T[u], T[S u]\]))
    * (T[S u] - T[u]) * L \}\ n) < ε).
  { assert (∀ h m r, Σ \{\ λ u v, v = (h u) * r \}\ m
      = r * Σ \{\ λ u v, v = (h u) \}\ m).
    { intros. induction m; simpl. rewrite FunValue,FunValue. lra.
      rewrite IHm,FunValue,FunValue. lra. } replace ε with (L * (ε/L)).
    rewrite H19. apply Rmult_lt_compat_l; auto. unfold Rdiv.
    rewrite <-Rmult_assoc,Rinv_r_simpl_m; auto. lra. } lra.
Qed.

Lemma Lemma9_11d : ∀ f g a b m M T n, (∃ J, Def_Integral f a b J)
  -> Seg T a b (S n) -> Function g -> \[a, b\] ⊂ dom[g]
  -> (∀ x, x ∈ \[a, b\] -> 0 <= g[x])
  -> (∀ x1 x2, x1 ∈ \[a, b\] -> x2 ∈ \[a, b\] -> x1 < x2 -> g[x2] <= g[x1])
  -> (∀ x, x ∈ \[a, b\] -> m <= (VarUp_Integral_Fun f a)[x] <= M)
  -> m * g[a]
    <= (Σ \{\ λ u v, v = g[T[u]] * (VarUp_Integral_Fun f T[u])[T[S u]] \}\ n)
    <= M * g[a].
Proof.
  intros. assert (a < b). { destruct H as [J[_[]]]; auto. }
  assert (\[a, b\] ⊂ dom[VarUp_Integral_Fun f a]).
  { apply VarUp_dom_b; auto. destruct H as [J[_[]]]. lra. }
  assert (∀ k, (k < S n)%nat -> T[k] < T[S k] /\ a <= T[k] /\ T[S k] <= b).
  { intros. pose proof H0 as [_[_[_[H9[]]]]]. split. apply H9. lia.
    rewrite <-H10,<-H11. split; apply (Seg_Increase_a T a b (S n)); auto; lia. }
  assert (Σ \{\ λ u v, v = g[T[u]] * (VarUp_Integral_Fun f T[u])[T[S u]] \}\ n
    = Σ \{\ λ u v, v = g[T[u]] * ((VarUp_Integral_Fun f a)[T[S u]]
      - (VarUp_Integral_Fun f a)[T[u]]) \}\ n).
  { apply Σ_Fact5. intros. rewrite FunValue,FunValue. replace
    ((VarUp_Integral_Fun f a)[T[S x]] - (VarUp_Integral_Fun f a)[T[x]]) with
    ((VarUp_Integral_Fun f T[x])[T[S x]]); auto. symmetry. apply H8 in H9
    as [H9[]]. apply Lemma9_10; apply H7,Classifier1; lra. } rewrite H9. clear H9.
  assert (n = 0 \/ 0 < n)%nat as []. lia. rewrite H9. simpl. rewrite FunValue.
  pose proof H0 as [_[_[_[H10[]]]]]. rewrite H11,VarUp_Value_eq,Rminus_0_r.
  assert (T[1%nat] ∈ \[a, b\]). { rewrite <-H11,<-H12. apply Classifier1; split;
  [apply Rle_ge| ]; apply (Seg_Increase_a T a b (S n)); auto; lia. }
  apply H5 in H13. assert (0 <= g[a]). { apply H3,Classifier1. lra. } destruct H13.
  split; rewrite (Rmult_comm _ g[a]); apply Rmult_le_compat_l; auto.
  assert (∀ h1 h2 k, (0 < k)%nat -> (h2 0%nat) = 0
    -> Σ \{\ λ u v, v = (h1 u) * ((h2 (S u)) - (h2 u)) \}\ k
    = Σ \{\ λ u v, v = (h2 (S u)) * ((h1 u) - (h1 (S u))) \}\ (k - 1)%nat
      + (h2 (S k)) * (h1 k)).
  { intros. destruct k. exfalso. lia. clear H10. induction k; simpl.
    rewrite FunValue,FunValue,FunValue,H11,Rminus_0_r. lra.
    rewrite FunValue,FunValue,FunValue. simpl in IHk. rewrite FunValue in IHk.
    rewrite IHk. replace (k-0)%nat with k; [ |lia]. lra. }
  pose proof (H10 (fun u => g[T[u]]) (fun u => (VarUp_Integral_Fun f a)[T[u]]) n).
  simpl in H11. rewrite H11; auto; [ |destruct H0 as [_[_[_[_[]]]]];
  rewrite H0,VarUp_Value_eq; auto]. clear H10 H11.
  assert ((Σ \{\ λ u v, v = m * (g[T[u]] - g[T[S u]]) \}\ (n - 1)%nat)
    <= (Σ \{\ λ u v, v = (VarUp_Integral_Fun f a)[T[S u]]
      * (g[T[u]] - g[T[S u]]) \}\ (n - 1)%nat)
    <= (Σ \{\ λ u v, v = M * (g[T[u]] - g[T[S u]]) \}\ (n - 1)%nat)).
  { assert (∀ i, (i <= (n - 1))%nat -> 0 <= g[T[i]] - g[T[S i]]).
    { intros. assert (i < S n)%nat. lia. apply H8 in H11 as [H11[]].
      pose proof H11. apply H4 in H14; [lra| | ]; apply Classifier1; lra. }
    assert (∀ i, (i <= (n - 1))%nat -> T[S i] ∈ \[a, b\]).
    { intros. assert (i < S n)%nat. lia. apply H8 in H12 as [H12[]].
      apply Classifier1; lra. }
    split; apply Rge_le; apply Σ_Fact3; intros; rewrite FunValue,FunValue;
    apply Rle_ge; apply Rmult_le_compat_r; auto; apply H5; auto. }
  assert (m * g[T[n]] <= (VarUp_Integral_Fun f a)[T[S n]] * g[T[n]]
    <= M * g[T[n]]).
  { assert (T[n] ∈ \[a, b\] /\ T[S n] ∈ \[a, b\]) as [].
    { pose proof H0 as [_[_[_[_[]]]]]. rewrite <-H11,<-H12. split.
      apply Classifier1; split; [apply Rle_ge| ]; apply (Seg_Increase_a T a b (S n));
      auto; lia. apply Classifier1; lra. } apply H3 in H11. apply H5 in H12 as [].
    split; apply Rmult_le_compat_r; auto. }
  assert ((Σ \{\ λ u v, v = m * (g[T[u]] - g[T[S u]]) \}\ (n - 1)%nat)
      + m * g[T[n]]
    <= (Σ \{\ λ u v, v = (VarUp_Integral_Fun f a)[T[S u]] * (g[T[u]] - g[T[S u]])
      \}\ (n - 1)%nat) + (VarUp_Integral_Fun f a)[T[S n]] * g[T[n]]
    <= (Σ \{\ λ u v, v = M * (g[T[u]] - g[T[S u]]) \}\ (n - 1)%nat)
      + M * g[T[n]]). lra.
  assert (∀ k h r, (0 < k)%nat -> Σ \{\ λ u v, v = r * ((h u) - (h (S u))) \}\
    (k-1)%nat + r * (h k) = r * (h 0%nat)).
  { intros. destruct k. exfalso. lia. induction k. simpl. rewrite FunValue. lra.
    simpl. simpl in IHk. replace (k - 0)%nat with k in IHk; [ |lia].
    rewrite FunValue. rewrite <-IHk. lra. lia. }
  destruct H0 as [_[_[_[_[]]]]]. rewrite H13,H13,H0 in H12; auto.
Qed.

Lemma Lemma9_11e : ∀ f g a b m M T n, (∃ J, Def_Integral f a b J)
  -> Seg T a b (S n) -> Function g -> \[a, b\] ⊂ dom[g]
  -> (∀ x, x ∈ \[a, b\] -> 0 <= g[x])
  -> (∀ x1 x2, x1 ∈ \[a, b\] -> x2 ∈ \[a, b\] -> x1 < x2 -> g[x1] <= g[x2])
  -> (∀ x, x ∈ \[a, b\] -> m <= (VarLow_Integral_Fun f b)[x] <= M)
  -> m * g[b]
    <= (Σ \{\ λ u v, v = g[T[S u]] * (VarUp_Integral_Fun f T[u])[T[S u]] \}\ n)
    <= M * g[b].
Proof.
  intros. assert (a < b). { destruct H as [J[_[]]]; auto. }
  assert (\[a, b\] ⊂ dom[VarUp_Integral_Fun f b]).
  { apply VarUp_dom_b; auto. destruct H as [J[_[]]]. lra. }
  assert (∀ k, (k < S n)%nat -> T[k] < T[S k] /\ a <= T[k] /\ T[S k] <= b).
  { intros. pose proof H0 as [_[_[_[H9[]]]]]. split. apply H9. lia.
    rewrite <-H10,<-H11. split; apply (Seg_Increase_a T a b (S n)); auto; lia. }
  assert (Σ \{\ λ u v, v = g[T[S u]] * (VarUp_Integral_Fun f T[u])[T[S u]] \}\ n
    = Σ \{\ λ u v, v = g[T[S u]] * ((VarLow_Integral_Fun f b)[T[u]]
      - (VarLow_Integral_Fun f b)[T[S u]]) \}\ n).
  { apply Σ_Fact5. intros. rewrite FunValue,FunValue. replace
    ((VarLow_Integral_Fun f b)[T[x]] - (VarLow_Integral_Fun f b)[T[S x]]) with
    ((VarUp_Integral_Fun f T[x])[T[S x]]); auto.
    destruct (VarUp_and_VarLow_Value f b).
    assert (T[x] ∈ \[a, b\] /\ T[S x] ∈ \[a, b\]) as [].
    { apply H8 in H9 as [H9[]]. split; apply Classifier1; lra. }
    pose proof H12. pose proof H13. apply H7,H11 in H14,H15.
    replace ((VarLow_Integral_Fun f b)[T[x]] - (VarLow_Integral_Fun f b)[T[S x]])
    with ((VarUp_Integral_Fun f b)[T[S x]] - (VarUp_Integral_Fun f b)[T[x]]);
    [ |lra]. symmetry. apply Lemma9_10; auto. } rewrite H9. clear H9.
  assert (n = 0 \/ 0 < n)%nat as []. lia. rewrite H9. simpl. rewrite FunValue.
  pose proof H0 as [_[_[_[H10[]]]]]. rewrite <-H9,H12,VarLow_Value_eq,Rminus_0_r.
  assert (T[n] ∈ \[a, b\]). { rewrite <-H11,<-H12. apply Classifier1; split;
  [apply Rle_ge| ]; apply (Seg_Increase_a T a b (S n)); auto; lia. }
  apply H5 in H13. assert (0 <= g[b]). { apply H3,Classifier1. lra. } destruct H13.
  split; rewrite (Rmult_comm _ g[b]); apply Rmult_le_compat_l; auto.
  assert (∀ h1 h2 k, (0 < k)%nat -> h2 (S k) = 0
    -> Σ \{\ λ u v, v = (h1 (S u)) * ((h2 u) - (h2 (S u))) \}\ k
    = Σ \{\ λ u v, v = (h2 (S u)) * ((h1 (S (S u))) - (h1 (S u))) \}\
     (k - 1)%nat + (h2 0%nat) * (h1 1%nat)).
  { intros. assert (Σ \{\ λ u v, v = (h1 (S u)) * ((h2 u) - (h2 (S u))) \}\ k
      = Σ \{\ λ u v, v = (h2 (S u)) * ((h1 (S (S u))) - (h1 (S u))) \}\
      (k - 1)%nat + (h2 0%nat) * (h1 1%nat) - (h2 (S k)) * (h1 (S k))).
    { destruct k. exfalso. lia. clear H10 H11. induction k. simpl.
      rewrite FunValue,FunValue,FunValue. lra. simpl.
      rewrite FunValue,FunValue,FunValue. simpl in IHk. rewrite FunValue in IHk.
      rewrite IHk. replace (k - 0)%nat with k. lra. lia. }
    rewrite H11 in H12. lra. }
  pose proof (H10 (fun u => g[T[u]]) (fun u => (VarLow_Integral_Fun f b)[T[u]]) n).
  simpl in H11. rewrite H11; auto; [ |destruct H0 as [_[_[_[_[]]]]];
  rewrite H12,VarLow_Value_eq; auto]. clear H10 H11.
  assert ((Σ \{\ λ u v, v = m * (g[T[S (S u)]] - g[T[S u]]) \}\ (n - 1)%nat)
    <= (Σ \{\ λ u v, v = (VarLow_Integral_Fun f b)[T[S u]]
      * (g[T[S (S u)]] - g[T[S u]]) \}\ (n - 1)%nat)
    <= (Σ \{\ λ u v, v = M * (g[T[S (S u)]] - g[T[S u]]) \}\ (n - 1)%nat)).
  { assert (∀ i, (i <= (n - 1))%nat -> 0 <= g[T[S (S i)]] - g[T[S i]]).
    { intros. assert (S i < S n)%nat. lia. apply H8 in H11 as [H11[]].
      pose proof H11. apply H4 in H14; [lra| | ]; apply Classifier1; lra. }
    assert (∀ i, (i <= (n - 1))%nat -> T[S i] ∈ \[a, b\]).
    { intros. assert (i < S n)%nat. lia. apply H8 in H12 as [H12[]].
      apply Classifier1; lra. }
    split; apply Rge_le; apply Σ_Fact3; intros; rewrite FunValue,FunValue;
    apply Rle_ge; apply Rmult_le_compat_r; auto; apply H5; auto. }
  assert (m * g[T[1%nat]] <= (VarLow_Integral_Fun f b)[T[0%nat]] * g[T[1%nat]]
    <= M * g[T[1%nat]]).
  { assert (T[0%nat] ∈ \[a, b\] /\ T[1%nat] ∈ \[a, b\]) as [].
    { pose proof H0 as [_[_[_[_[]]]]]. rewrite <-H11,<-H12. split.
      apply Classifier1; lra. apply Classifier1; split; [apply Rle_ge| ];
      apply (Seg_Increase_a T a b (S n)); auto; lia. } apply H3 in H12.
    apply H5 in H11 as []. split; apply Rmult_le_compat_r; auto. }
  assert ((Σ \{\ λ u v, v = m * (g[T[S (S u)]] - g[T[S u]]) \}\ (n - 1)%nat)
      + m * g[T[1%nat]]
    <= (Σ \{\ λ u v, v = (VarLow_Integral_Fun f b)[T[S u]] * (g[T[S (S u)]]
      - g[T[S u]]) \}\ (n - 1)%nat)
      + (VarLow_Integral_Fun f b)[T[0%nat]] * g[T[1%nat]]
    <= (Σ \{\ λ u v, v = M * (g[T[S (S u)]] - g[T[S u]]) \}\ (n - 1)%nat)
      + M * g[T[1%nat]]). lra.
  assert (∀ k h r, (0 < k)%nat -> Σ \{\ λ u v, v = r * ((h (S (S u)))
    - (h (S u))) \}\ (k-1)%nat + r * (h 1%nat) = r * (h (S k))).
  { intros. destruct k. exfalso. lia. clear H13. induction k. simpl.
    rewrite FunValue. lra. simpl in *. replace (k - 0)%nat with k in IHk; [ |lia].
    rewrite FunValue. replace (Σ \{\ λ u v, v = r * (h (S (S u)) - h (S u)) \}\ k)
    with (r * (h (S (S k))) - r * (h 1%nat)); lra. } destruct H0 as [_[_[_[_[]]]]].
  rewrite (H13 n (fun u => g[T[u]])),(H13 n (fun u => g[T[u]])),H14 in H12; auto.
Qed.

Lemma Lemma9_11f : ∀ f g a b m M, (∃ J, Def_Integral f a b J)
  -> Function g -> \[a, b\] ⊂ dom[g] -> (∀ x, x ∈ \[a, b\] -> 0 <= g[x])
  -> (∀ x1 x2, x1 ∈ \[a, b\] -> x2 ∈ \[a, b\] -> x1 < x2 -> g[x2] <= g[x1])
  -> (∀ x, x ∈ \[a, b\] -> m <= (VarUp_Integral_Fun f a)[x] <= M)
  -> m * g[a] <= (VarUp_Integral_Fun (f \* g) a)[b] <= M * g[a].
Proof.
  intros. assert (a < b). { destruct H as [J[_[]]]; auto. }
  assert (∃ J, Def_Integral g a b J). { apply Theorem9_6b; auto. }
  assert (∀ ε, ε > 0 -> -ε + m * g[a]
    <= (VarUp_Integral_Fun (f \* g) a)[b] <= ε + M * g[a]).
  { intros. pose proof H7. apply (Lemma9_11c f g a b) in H8 as [T[n[]]]; auto.
    pose proof (H9 (fun k => g[T[k]])). simpl in H10. clear H9.
    assert ((fun k => g[T[k]]) = (fun k => g[T[k]]) \/ (fun k => g[T[k]])
      = (fun k => g[T[S k]])); auto. apply H10,Abs_R in H9. clear H10.
    assert (m * g[a] <= (Σ \{\ λ u v, v = g[T[u]]
      * (VarUp_Integral_Fun f T[u])[T[S u]] \}\ n) <= M * g[a]).
    { apply (Lemma9_11d f g a b); auto. }
    rewrite (Lemma9_11a (f \* g) T a b n),
    (Lemma9_11b f g (fun k => g[T[k]]) T a b n); auto. lra.
    apply Property9_4_3; auto. }
  assert (∀ x y z, (∀ ε, ε > 0 -> -ε + x <= y <= ε + z) -> x <= y <= z).
  { intros. split. destruct (Rle_or_lt x y); auto. assert (x - y > 0). lra.
    assert (0 < (x-y)/2 < x - y) as []. lra. apply H8 in H11 as [].
    exfalso. lra. destruct (Rle_or_lt y z); auto. assert (y - z > 0). lra.
    assert (0 < (y-z)/2 < y - z) as []. lra. apply H8 in H11 as [].
    exfalso. lra. } apply H8; auto.
Qed.

Lemma Lemma9_11g : ∀ f g a b m M, (∃ J, Def_Integral f a b J)
  -> Function g -> \[a, b\] ⊂ dom[g] -> (∀ x, x ∈ \[a, b\] -> 0 <= g[x])
  -> (∀ x1 x2, x1 ∈ \[a, b\] -> x2 ∈ \[a, b\] -> x1 < x2 -> g[x1] <= g[x2])
  -> (∀ x, x ∈ \[a, b\] -> m <= (VarLow_Integral_Fun f b)[x] <= M)
  -> m * g[b] <= (VarUp_Integral_Fun (f \* g) a)[b] <= M * g[b].
Proof.
  intros. assert (a < b). { destruct H as [J[_[]]]; auto. }
  assert (∃ J, Def_Integral g a b J). { apply Theorem9_6a; auto. }
  assert (∀ ε, ε > 0 -> -ε + m * g[b]
    <= (VarUp_Integral_Fun (f \* g) a)[b] <= ε + M * g[b]).
  { intros. pose proof H7. apply (Lemma9_11c f g a b) in H8 as [T[n[]]]; auto.
    pose proof (H9 (fun k => g[T[S k]])). simpl in H10. clear H9.
    assert ((fun k => g[T[S k]]) = (fun k => g[T[k]]) \/ (fun k => g[T[S k]])
      = (fun k => g[T[S k]])); auto. apply H10,Abs_R in H9. clear H10.
    assert (m * g[b] <= (Σ \{\ λ u v, v = g[T[S u]]
      * (VarUp_Integral_Fun f T[u])[T[S u]] \}\ n) <= M * g[b]).
    { apply (Lemma9_11e f g a b); auto. }
    rewrite (Lemma9_11a (f \* g) T a b n),
    (Lemma9_11b f g (fun k => g[T[S k]]) T a b n); auto. lra.
    apply Property9_4_3; auto. }
  assert (∀ x y z, (∀ ε, ε > 0 -> -ε + x <= y <= ε + z) -> x <= y <= z).
  { intros. split. destruct (Rle_or_lt x y); auto. assert (x - y > 0). lra.
    assert (0 < (x-y)/2 < x - y) as []. lra. apply H8 in H11 as [].
    exfalso. lra. destruct (Rle_or_lt y z); auto. assert (y - z > 0). lra.
    assert (0 < (y-z)/2 < y - z) as []. lra. apply H8 in H11 as [].
    exfalso. lra. } apply H8; auto.
Qed.


(* 积分第二中值定理 *)
Theorem Theorem9_11a : ∀ f g a b, (∃ J, Def_Integral f a b J)
  -> Function g -> \[a, b\] ⊂ dom[g] -> (∀ x, x ∈ \[a, b\] -> 0 <= g[x])
  -> (∀ x1 x2, x1 ∈ \[a, b\] -> x2 ∈ \[a, b\] -> x1 < x2 -> g[x2] <= g[x1])
  -> ∃ ξ, ξ ∈ \[a, b\] /\ (VarUp_Integral_Fun (f \* g) a)[b]
    = g[a] * (VarUp_Integral_Fun f a)[ξ].
Proof.
  intros. assert (a < b). { destruct H as [J[_[]]]; auto. }
  pose proof H. apply Theorem9_9a in H5. pose proof H5.
  apply Theorem4_6 in H6 as [[M[H6[H7[x1[]]]]][m[H10[H11[x2[]]]]]]; auto.
  assert ((∀ x, x ∈ \[a, b\] -> m <= (VarUp_Integral_Fun f a)[x] <= M)).
  { intros. split; [apply H11|apply H7]; auto. } apply (Lemma9_11f f g) in H14;
  auto. assert (0 <= g[a]) as []. { apply H2,Classifier1; lra. }
  destruct H14. destruct H14. destruct H16.
  assert (m < ((VarUp_Integral_Fun (f \* g) a)[b])/(g[a]) < M).
  { assert (0 < /(g[a])). { apply Rinv_0_lt_compat; auto. } split.
    apply (Rmult_lt_compat_r (/(g[a]))) in H14; auto. rewrite Rinv_r_simpl_l
    in H14; auto. lra. apply (Rmult_lt_compat_r (/(g[a]))) in H16; auto.
    rewrite Rinv_r_simpl_l in H16; auto. lra. }
  assert (∃ ξ, a < ξ < b /\ (VarUp_Integral_Fun f a)[ξ]
    = ((VarUp_Integral_Fun (f \* g) a)[b])/(g[a])) as [ξ[]].
  { destruct (Rtotal_order x1 x2) as [H18|[]]. assert (∃ ξ, x1 < ξ < x2 /\
    (VarUp_Integral_Fun f a)[ξ] = ((VarUp_Integral_Fun (f \* g) a)[b])/(g[a])).
    { apply Theorem4_7; auto. destruct H5 as [H5[]]. apply Classifier1 in H8 as [].
      apply Classifier1 in H12 as []. split. red; intros. apply H5. lra.
      destruct H8. split. apply Theorem4_1,H5. lra. destruct H22.
      apply Theorem4_1,H5. lra. rewrite H22; auto. rewrite H8. split; auto.
      destruct H22. apply Theorem4_1,H5. lra. rewrite H22; auto.
      rewrite H9,H13. auto. } destruct H19 as [ξ[]]. exists ξ. split; auto.
    applyClassifier1 H8. applyClassifier1 H12. lra. rewrite <-H9,<-H13,H18 in H17.
    exfalso. lra. assert (∃ ξ, x2 < ξ < x1 /\ (VarUp_Integral_Fun f a)[ξ]
      = ((VarUp_Integral_Fun (f \* g) a)[b])/(g[a])) as [ξ[]].
    { apply Theorem4_7; auto. destruct H5 as [H5[]]. apply Classifier1 in H8 as [].
      apply Classifier1 in H12 as []. split. red; intros. apply H5. lra. split.
      destruct H12. apply Theorem4_1,H5. lra. rewrite H12; auto. destruct H21.
      apply Theorem4_1,H5. lra. rewrite H21; auto. rewrite H9,H13. auto. }
    exists ξ. split; auto. applyClassifier1 H8. applyClassifier1 H12. lra. }
  exists ξ. split. apply Classifier1. lra. rewrite H19. unfold Rdiv.
  rewrite <-Rmult_assoc,Rinv_r_simpl_m; auto. lra. exists x1. split; auto.
  rewrite H16,H9. lra. exists x2. split; auto. rewrite H13,<-H14. lra.
  assert (∀ x, x ∈ \[a, b\] -> g[x] = 0).
  { intros. pose proof (H2 x H16). pose proof H16. apply Classifier1 in H18 as [].
    destruct H18. apply H3 in H18; auto. lra. apply Classifier1. lra.
    rewrite H18; auto. } exists a. split. apply Classifier1. lra.
  rewrite VarUp_Value_eq,Rmult_0_r.
  assert (\[a, b\] ⊂ dom[VarUp_Integral_Fun (f \* g) a]).
  { apply VarUp_dom_b. apply Property9_4_3; auto. apply Theorem9_6b; auto. lra. }
  pose proof H4. apply (VarUp_Value_gt (f \* g) a) in H18.
  assert (Def_Integral (f \* g) a b (0 * (b - a))).
  { destruct H as [J[_[_[]]]]. apply Lemma9_6; auto. apply Corollary_mult_fun_a.
    rewrite Corollary_mult_fun_c. red; intros. apply Classifier1; auto. intros.
    rewrite Corollary_mult_fun_b; auto. rewrite H16; auto. lra. }
  rewrite Rmult_0_l in H19. eapply Def_Integral_Uni; eauto.
  apply H17,Classifier1; lra.
Qed.

Theorem Theorem9_11b : ∀ f g a b, (∃ J, Def_Integral f a b J)
  -> Function g -> \[a, b\] ⊂ dom[g] -> (∀ x, x ∈ \[a, b\] -> 0 <= g[x])
  -> (∀ x1 x2, x1 ∈ \[a, b\] -> x2 ∈ \[a, b\] -> x1 < x2 -> g[x1] <= g[x2])
  -> ∃ ξ, ξ ∈ \[a, b\] /\ (VarUp_Integral_Fun (f \* g) a)[b]
    = g[b] * (VarLow_Integral_Fun f b)[ξ].
Proof.
  intros. assert (a < b). { destruct H as [J[_[]]]; auto. }
  pose proof H. apply Theorem9_9b in H5. pose proof H5.
  apply Theorem4_6 in H6 as [[M[H6[H7[x1[]]]]][m[H10[H11[x2[]]]]]]; auto.
  assert ((∀ x, x ∈ \[a, b\] -> m <= (VarLow_Integral_Fun f b)[x] <= M)).
  { intros. split; [apply H11|apply H7]; auto. } apply (Lemma9_11g f g) in H14;
  auto. assert (0 <= g[b]) as []. { apply H2,Classifier1; lra. }
  destruct H14. destruct H14. destruct H16.
  assert (m < ((VarUp_Integral_Fun (f \* g) a)[b])/(g[b]) < M).
  { assert (0 < /(g[b])). { apply Rinv_0_lt_compat; auto. } split.
    apply (Rmult_lt_compat_r (/(g[b]))) in H14; auto. rewrite Rinv_r_simpl_l
    in H14; auto. lra. apply (Rmult_lt_compat_r (/(g[b]))) in H16; auto.
    rewrite Rinv_r_simpl_l in H16; auto. lra. }
  assert (∃ ξ, a < ξ < b /\ (VarLow_Integral_Fun f b)[ξ]
    = ((VarUp_Integral_Fun (f \* g) a)[b])/(g[b])) as [ξ[]].
  { destruct (Rtotal_order x1 x2) as [H18|[]]. assert (∃ ξ, x1 < ξ < x2 /\
    (VarLow_Integral_Fun f b)[ξ] = ((VarUp_Integral_Fun (f \* g) a)[b])/(g[b])).
    { apply Theorem4_7; auto. destruct H5 as [H5[]]. apply Classifier1 in H8 as [].
      apply Classifier1 in H12 as []. split. red; intros. apply H5. lra.
      destruct H8. split. apply Theorem4_1,H5. lra. destruct H22.
      apply Theorem4_1,H5. lra. rewrite H22; auto. rewrite H8. split; auto.
      destruct H22. apply Theorem4_1,H5. lra. rewrite H22; auto.
      rewrite H9,H13. auto. } destruct H19 as [ξ[]]. exists ξ. split; auto.
    applyClassifier1 H8. applyClassifier1 H12. lra. rewrite <-H9,<-H13,H18 in H17.
    exfalso. lra. assert (∃ ξ, x2 < ξ < x1 /\ (VarLow_Integral_Fun f b)[ξ]
      = ((VarUp_Integral_Fun (f \* g) a)[b])/(g[b])) as [ξ[]].
    { apply Theorem4_7; auto. destruct H5 as [H5[]]. apply Classifier1 in H8 as [].
      apply Classifier1 in H12 as []. split. red; intros. apply H5. lra. split.
      destruct H12. apply Theorem4_1,H5. lra. rewrite H12; auto. destruct H21.
      apply Theorem4_1,H5. lra. rewrite H21; auto. rewrite H9,H13. auto. }
    exists ξ. split; auto. applyClassifier1 H8. applyClassifier1 H12. lra. }
  exists ξ. split. apply Classifier1. lra. rewrite H19. unfold Rdiv.
  rewrite <-Rmult_assoc,Rinv_r_simpl_m; auto. lra. exists x1. split; auto.
  rewrite H16,H9. lra. exists x2. split; auto. rewrite H13,<-H14. lra.
  assert (∀ x, x ∈ \[a, b\] -> g[x] = 0).
  { intros. pose proof (H2 x H16). pose proof H16. apply Classifier1 in H18 as [].
    destruct H19. apply H3 in H19; auto. lra. apply Classifier1. lra.
    rewrite H19; auto. } exists b. split. apply Classifier1. lra.
  rewrite VarLow_Value_eq,Rmult_0_r.
  assert (\[a, b\] ⊂ dom[VarUp_Integral_Fun (f \* g) a]).
  { apply VarUp_dom_b. apply Property9_4_3; auto. apply Theorem9_6a; auto. lra. }
  pose proof H4. apply (VarUp_Value_gt (f \* g) a) in H18.
  assert (Def_Integral (f \* g) a b (0 * (b - a))).
  { destruct H as [J[_[_[]]]]. apply Lemma9_6; auto. apply Corollary_mult_fun_a.
    rewrite Corollary_mult_fun_c. red; intros. apply Classifier1; auto. intros.
    rewrite Corollary_mult_fun_b; auto. rewrite H16; auto. lra. }
  rewrite Rmult_0_l in H19. eapply Def_Integral_Uni; eauto.
  apply H17,Classifier1; lra.
Qed.

Corollary Corollary9_11 : ∀ f g a b, (∃ J, Def_Integral f a b J)
  -> Function g -> \[a, b\] ⊂ dom[g]
  -> ((∀ x1 x2, x1 ∈ \[a, b\] -> x2 ∈ \[a, b\] -> x1 < x2 -> g[x1] <= g[x2])
    \/ (∀ x1 x2, x1 ∈ \[a, b\] -> x2 ∈ \[a, b\] -> x1 < x2 -> g[x2] <= g[x1]))
  -> ∃ ξ, ξ ∈ \[a, b\] /\ (VarUp_Integral_Fun (f \* g) a)[b]
    = g[a] * (VarUp_Integral_Fun f a)[ξ] + g[b] * (VarLow_Integral_Fun f b)[ξ].
Proof.
  intros. assert (a < b). { destruct H as [J[_[]]]; auto. }
  assert (∃ J, Def_Integral g a b J).
  { destruct H2; [apply Theorem9_6a|apply Theorem9_6b]; auto. }
  assert (\[a, b\] ⊂ dom[VarUp_Integral_Fun f a]
    /\ \[a, b\] ⊂ dom[VarLow_Integral_Fun f b]
    /\ \[a, b\] ⊂ dom[VarUp_Integral_Fun (f \* g) a]) as [H5[]].
  { split; [apply VarUp_dom_b|split; [apply VarLow_dom_b|apply VarUp_dom_b]];
    auto; try lra. apply Property9_4_3; auto. }
  assert (∀ φ r x, x ∈ dom[φ] -> (φ \\* r)[x] = r * φ[x]) as Ht1.
  { intros. assert (x ∈ dom[φ \\* r]). rewrite Corollary_mult_fun_d; auto.
    apply x_fx_T in H9. applyClassifier2 H9. destruct H9. lra. red; intros.
    applyClassifier2 H10. applyClassifier2 H11. destruct H10 as [], H11 as [].
    rewrite H12,H13; auto. }
  assert (∀ f1 f2 r, f1 \* (f2 \- \{\ λ u v, v = r \}\)
    = (f1 \* f2) \- (f1 \\* r)) as Ht2.
  { intros. apply AxiomI; split; intros; destruct z. applyClassifier2 H8.
    destruct H8 as [H8[]]. pose proof H9. rewrite Corollary_sub_fun_c in H11.
    apply Classifier1 in H11 as []. apply Classifier2; split.
    rewrite Corollary_mult_fun_c. apply Classifier1; auto. split.
    rewrite Corollary_mult_fun_d; auto.
    rewrite H10,Corollary_mult_fun_b,Corollary_sub_fun_b,FunValue,Ht1; auto. lra.
    applyClassifier2 H8. destruct H8 as [H8[]]. rewrite Corollary_mult_fun_c in H8.
    rewrite Corollary_mult_fun_d in H9. apply Classifier1 in H8 as [_].
    apply Classifier2. split; auto. split. rewrite Corollary_sub_fun_c.
    apply Classifier1; split; auto. apply Classifier1. exists r.
    apply Classifier2; auto.
    rewrite H10,Corollary_mult_fun_b,Corollary_sub_fun_b,Ht1,FunValue; auto.
    lra. apply Classifier1. exists r. apply Classifier2; auto. }
  destruct H2.
  - set (h := g \- \{\ λ u v, v = g[a] \}\).
    assert (Function h /\ dom[h] = dom[g]) as [].
    { split. apply Corollary_sub_fun_a. unfold h. rewrite Corollary_sub_fun_c.
      apply AxiomI; split; intros. apply Classifier1 in H8 as []; auto. apply
      Classifier1; split; auto. apply Classifier1. exists g[a]. apply Classifier2; auto. }
    pose proof H1. rewrite <-H9 in H10. assert (∀ x1 x2, x1 ∈ \[a, b\]
      -> x2 ∈ \[a, b\] -> x1 < x2 -> h[x1] <= h[x2]).
    { intros. unfold h. rewrite Corollary_sub_fun_b,Corollary_sub_fun_b; auto;
      try (apply Classifier1; exists g[a]; apply Classifier2; auto).
      rewrite FunValue,FunValue. apply H2 in H13; auto. lra. }
    assert (∀ x, x ∈ \[a, b\] -> 0 <= h[x]).
    { intros. unfold h. rewrite Corollary_sub_fun_b; auto. rewrite FunValue.
      pose proof H12. apply Classifier1 in H13 as [[]]. apply H2 in H13; auto.
      lra. apply Classifier1; lra. rewrite H13. lra. apply Classifier1. exists g[a].
      apply Classifier2; auto. } pose proof H.
    apply (Theorem9_11b f h a b) in H13 as [ξ[]]; auto.
    assert (\[a, b\] ⊂ dom[VarUp_Integral_Fun (f \* h) a]
      /\ \[a, b\] ⊂ dom[VarUp_Integral_Fun (f \\* g[a]) a]) as [].
    { split. apply VarUp_dom_b. apply Property9_4_3; auto. apply Theorem9_6a;
      auto. lra. apply VarUp_dom_b. destruct H as [J]. exists (g[a] * J).
      apply Property9_4_1; auto. lra. } pose proof H3. pose proof H3.
    apply (VarUp_Value_gt (f \* h)) in H17; [ |apply H15,Classifier1; lra].
    apply (VarUp_Value_gt (f \\* g[a])) in H18; [ |apply H16,Classifier1; lra].
    pose proof H3. apply (VarUp_Value_gt (f \* g)) in H19;
    [ |apply H7,Classifier1; lra].
    assert (Def_Integral (f \* h) a b ((VarUp_Integral_Fun (f \* g) a)[b]
      - (VarUp_Integral_Fun (f \\* g[a]) a)[b])).
    { assert (f \* h = (f \* g) \- (f \\* g[a])). apply Ht2. rewrite H20.
      apply Property9_4_2b; auto. }
    assert ((VarUp_Integral_Fun (f\*h) a)[b] = (VarUp_Integral_Fun (f\*g) a)[b]
      - (VarUp_Integral_Fun (f\\*g[a]) a)[b]). { eapply Def_Integral_Uni; eauto. }
    rewrite H14 in H21. pose proof H3. apply (VarUp_Value_gt f) in H22;
    [ |apply H5,Classifier1; lra]. apply (Property9_4_1 f a b _ (g[a])) in H22.
    assert ((VarUp_Integral_Fun (f \\* g[a]) a) [b]
      = g[a] * (VarUp_Integral_Fun f a)[b]). { eapply Def_Integral_Uni; eauto. }
    rewrite H23 in H21. unfold h in H21. rewrite Corollary_sub_fun_b in H21.
    rewrite FunValue in H21. exists ξ. split; auto.
    assert ((VarUp_Integral_Fun f a)[b] - (VarLow_Integral_Fun f b)[ξ]
      = (VarUp_Integral_Fun f a)[ξ]).
    { assert (ξ ∈ dom[VarUp_Integral_Fun f a] /\ b ∈ dom[VarUp_Integral_Fun f a]).
      { split; auto. apply H5; auto. apply Classifier1; lra. } destruct H24.
      pose proof H24. apply (Lemma9_10 f a ξ b) in H26 as []; auto.
      pose proof H13. apply Classifier1 in H28 as []. destruct H29. pose proof H29.
      apply (VarUp_Value_gt f) in H29; auto. apply (VarLow_Value_lt f) in H30;
      auto. assert ((VarLow_Integral_Fun f b)[ξ] = (VarUp_Integral_Fun f ξ)[b]).
      { eapply Def_Integral_Uni; eauto. } rewrite H31. lra.
      rewrite H29,VarLow_Value_eq. lra. } rewrite <-H24. lra.
    apply H1,Classifier1; lra. apply Classifier1. exists g[a]. apply Classifier2; auto.
  - set (h := g \- \{\ λ u v, v = g[b] \}\).
    assert (Function h /\ dom[h] = dom[g]) as [].
    { split. apply Corollary_sub_fun_a. unfold h. rewrite Corollary_sub_fun_c.
      apply AxiomI; split; intros. apply Classifier1 in H8 as []; auto. apply
      Classifier1; split; auto. apply Classifier1. exists g[b]. apply Classifier2; auto. }
    pose proof H1. rewrite <-H9 in H10. assert (∀ x1 x2, x1 ∈ \[a, b\]
      -> x2 ∈ \[a, b\] -> x1 < x2 -> h[x2] <= h[x1]).
    { intros. unfold h. rewrite Corollary_sub_fun_b,Corollary_sub_fun_b; auto;
      try (apply Classifier1; exists g[b]; apply Classifier2; auto).
      rewrite FunValue,FunValue. apply H2 in H13; auto. lra. }
    assert (∀ x, x ∈ \[a, b\] -> 0 <= h[x]).
    { intros. unfold h. rewrite Corollary_sub_fun_b; auto. rewrite FunValue.
      pose proof H12. apply Classifier1 in H13 as [H13[]]. apply H2 in H14; auto.
      lra. apply Classifier1; lra. rewrite H14. lra. apply Classifier1. exists g[b].
      apply Classifier2; auto. } pose proof H.
    apply (Theorem9_11a f h a b) in H13 as [ξ[]]; auto.
    assert (\[a, b\] ⊂ dom[VarUp_Integral_Fun (f \* h) a]
      /\ \[a, b\] ⊂ dom[VarUp_Integral_Fun (f \\* g[b]) a]) as [].
    { split. apply VarUp_dom_b. apply Property9_4_3; auto. apply Theorem9_6b;
      auto. lra. apply VarUp_dom_b. destruct H as [J]. exists (g[b] * J).
      apply Property9_4_1; auto. lra. } pose proof H3. pose proof H3.
    apply (VarUp_Value_gt (f \* h)) in H17; [ |apply H15,Classifier1; lra].
    apply (VarUp_Value_gt (f \\* g[b])) in H18; [ |apply H16,Classifier1; lra].
    pose proof H3. apply (VarUp_Value_gt (f \* g)) in H19;
    [ |apply H7,Classifier1; lra].
    assert (Def_Integral (f \* h) a b ((VarUp_Integral_Fun (f \* g) a)[b]
      - (VarUp_Integral_Fun (f \\* g[b]) a)[b])).
    { assert (f \* h = (f \* g) \- (f \\* g[b])). apply Ht2. rewrite H20.
      apply Property9_4_2b; auto. }
    assert ((VarUp_Integral_Fun (f\*h) a)[b] = (VarUp_Integral_Fun (f\*g) a)[b]
      - (VarUp_Integral_Fun (f\\*g[b]) a)[b]). { eapply Def_Integral_Uni; eauto. }
    rewrite H14 in H21. pose proof H3. apply (VarUp_Value_gt f) in H22;
    [ |apply H5,Classifier1; lra]. apply (Property9_4_1 f a b _ (g[b])) in H22.
    assert ((VarUp_Integral_Fun (f \\* g[b]) a) [b]
      = g[b] * (VarUp_Integral_Fun f a)[b]). { eapply Def_Integral_Uni; eauto. }
    rewrite H23 in H21. unfold h in H21. rewrite Corollary_sub_fun_b in H21.
    rewrite FunValue in H21. exists ξ. split; auto.
    assert ((VarUp_Integral_Fun f a)[b] - (VarUp_Integral_Fun f a)[ξ]
      = (VarLow_Integral_Fun f b)[ξ]).
    { assert (ξ ∈ dom[VarUp_Integral_Fun f a] /\ b ∈ dom[VarUp_Integral_Fun f a]).
      { split; auto. apply H5; auto. apply Classifier1; lra. } destruct H24.
      pose proof H24. apply (Lemma9_10 f a ξ b) in H26 as []; auto.
      pose proof H13. apply Classifier1 in H28 as []. destruct H29. pose proof H29.
      apply (VarUp_Value_gt f) in H29; auto. apply (VarLow_Value_lt f) in H30;
      auto. assert ((VarLow_Integral_Fun f b)[ξ] = (VarUp_Integral_Fun f ξ)[b]).
      { eapply Def_Integral_Uni; eauto. } rewrite H31. lra.
      rewrite H29,VarLow_Value_eq. lra. } rewrite <-H24. lra.
    apply H1,Classifier1; lra. apply Classifier1. exists g[b]. apply Classifier2; auto.
Qed.

(* 原函数在区间两端的可导性可以扩展 *)
Lemma Lemma9_12a : ∀ f a b, (∃ F, Primitive_Close f F a b)
  -> (∃ F, Primitive_Close f F a b /\ Derivative F a f[a]
    /\ Derivative F b f[b]).
Proof.
  intros. destruct H as [F[H[H0[H1[H2[H3[H4[]]]]]]]].
  set (F1 := \{\ λ u v, (u < a -> v = f[a] * (u - a) + F[a])
    /\ (a <= u <= b -> v = F[u]) /\ (b < u -> v = f[b] * (u - b) + F[b]) \}\).
  assert (Function F1).
  { red; intros. applyClassifier2 H7. applyClassifier2 H8.
    destruct H7 as [H7[]], H8 as [H8[]].
    assert (x < a \/ a <= x <= b \/ b < x) as [H13|[]]. lra.
    rewrite H7,H8; auto. rewrite H9,H11; auto. rewrite H10,H12; auto. }
  assert (dom[F1] = Full R).
  { apply AxiomI; split; intros. apply Classifier1; auto. apply Classifier1.
    assert (z < a \/ a <= z <= b \/ b < z) as [H9|[]]. lra.
    exists (f[a] * (z - a) + F[a]). apply Classifier2; repeat split; intros;
    exfalso; lra. exists F[z]. apply Classifier2; repeat split; intros; exfalso;
    lra. exists (f[b] * (z - b) + F[b]). apply Classifier2; repeat split; intros;
    exfalso; lra. }
  assert (\[a, b\] ⊂ dom[F1]). { red; intros. rewrite H8. apply Classifier1; auto. }
  assert (∀ x, x ∈ dom[F1]). { rewrite H8. intros. apply Classifier1; auto. }
  assert (∀ x, x < a -> F1[x] = f[a] * (x - a) + F[a]).
  { intros. pose proof (H10 x). apply x_fx_T in H12; auto.
    applyClassifier2 H12. destruct H12 as [H12[]];  auto. }
    assert (∀ x, x ∈ \[a, b\] -> F1[x] = F[x]).
  { intros. pose proof (H10 x). apply x_fx_T in H13; auto.
    applyClassifier2 H13. destruct H13 as [_[]]; auto. apply H13.
    applyClassifier1 H12; lra. }
  assert (∀ x, b < x -> F1[x] = f[b] * (x - b) + F[b]).
  { intros. pose proof (H10 x). apply x_fx_T in H14; auto. applyClassifier2 H14.
    destruct H14 as [H14[]]; auto. }
  assert (∀ x, x ∈ \(a, b\) -> Derivative F1 x f[x]).
  { intros. pose proof H14. apply H4 in H15 as [_[_[_[x0[H15[]]]]]].
    split; auto. split. exists 1. split. lra. red; intros; auto. split.
    red; intros. applyClassifier2 H18. applyClassifier2 H19. rewrite H18,H19; auto.
    exists x0. split; auto. split. red; intros. apply Classifier1. exists
    ((F1[z] - F1[x])/(z - x)). apply Classifier2; auto. intros. apply H17 in H18
    as [x1[]]. assert (∃ δ, δ > 0 /\ Uº(x; δ) ⊂ \[a, b\]) as [δ[]].
    { apply Classifier1 in H14 as []. destruct (Rle_or_lt (x-a) (b-x)).
      exists (x-a). split. lra. red; intros. apply Classifier1 in H22 as [].
      apply Abs_R in H23. apply Classifier1. lra. exists (b-x). split. lra.
      red; intros. apply Classifier1 in H22 as []. apply Abs_R in H23.
      apply Classifier1. lra. } destruct (Examp1 δ x1) as [x2[H22[]]]; try lra.
    exists x2. split. lra. intros. rewrite FunValue,H12,H12.
    assert (0 < ∣(x3-x)∣ < x1). lra. apply H19 in H26. rewrite FunValue in H26;
    auto. apply Classifier1. applyClassifier1 H14. lra. apply H21,Classifier1. lra. }
  assert (Derivative F1 a f[a]).
  { apply Theorem5_2; split; split; auto; split; try (exists 1; split; try lra;
    rewrite H8; red; intros; apply Classifier1; auto). split. red; intros.
    applyClassifier2 H15. applyClassifier2 H16. rewrite H15,H16; auto. exists 1.
    split. lra. split. red; intros. apply Classifier1. exists ((F1[z] - F1[a])/(z-a)).
    apply Classifier2; auto. intros. exists (1/2). split. lra. intros.
    rewrite FunValue,H11,H12. replace (f[a] * (x - a) + F[a] - F[a]) with
    (f[a] * (x - a)); [ |lra]. unfold Rdiv. rewrite Rinv_r_simpl_l,Abs_ge; lra.
    apply Classifier1; lra. lra. pose proof H5 as [_[_[_[x0[H15[]]]]]]. split.
    red; intros. applyClassifier2 H18. applyClassifier2 H19. rewrite H18,H19; auto.
    exists x0. split; auto. split. red; intros. apply Classifier1. exists
    ((F1[z] - F1[a])/(z-a)). apply Classifier2; auto. intros. apply H17 in H18
    as [x1[]]. destruct (Examp1 x1 (b-a)) as [x2[H20[]]]; try lra. exists x2.
    split. lra. intros. rewrite FunValue,H12,H12; try (apply Classifier1; lra).
    assert (a < x < a + x1). lra. apply H19 in H24.
    rewrite FunValue in H24; auto. }
  assert (Derivative F1 b f[b]).
  { apply Theorem5_2; split; split; auto; split; try (exists 1; split; try lra;
    rewrite H8; red; intros; apply Classifier1; auto). split. red; intros.
    applyClassifier2 H16. applyClassifier2 H17. rewrite H16,H17; auto.
    pose proof H6 as [_[_[_[x0[H16[]]]]]]. exists x0. split; auto.
    split. red; intros. apply Classifier1. exists ((F1[z] - F1[b])/(z-b)).
    apply Classifier2; auto. intros. apply H18 in H19 as [x1[]].
    destruct (Examp1 x1 (b-a)) as [x2[H21[]]]; try lra. exists x2. split. lra.
    intros. rewrite FunValue,H12,H12; try (apply Classifier1; lra).
    assert (b - x1 < x < b). lra. apply H20 in H25. rewrite FunValue in H25;
    auto. split. red; intros. applyClassifier2 H16. applyClassifier2 H17.
    rewrite H16,H17; auto. exists 1. split. lra. split. red; intros.
    apply Classifier1. exists ((F1[z] - F1[b])/(z-b)). apply Classifier2; auto.
    intros. exists (1/2). split. lra. intros. rewrite FunValue,H13,H12.
    replace (f[b] * (x - b) + F[b] - F[b]) with (f[b] * (x - b)); [ |lra].
    unfold Rdiv. rewrite Rinv_r_simpl_l,Abs_ge; lra. apply Classifier1; lra. lra. }
  exists F1. split; auto. split; auto. split; auto. split; auto. split; auto.
  split; auto. split; auto. split; apply Theorem5_2; auto.
Qed.

(* 函数在闭区间内有界且开区间上连续, 则可积 *)
Lemma Lemma9_12b : ∀ f a b, a < b -> DBoundedFun f (\[a, b\])
  -> ContinuousOpen f a b -> ∃ J, Def_Integral f a b J.
Proof.
  intros. destruct (classic (ContinuousRight f a)) as [H2|H2];
  destruct (classic (ContinuousLeft f b)) as [H3|H3]. apply Theorem9_4; auto.
  split; auto. apply Lemma9_5b; auto. split; auto. apply Lemma9_5a; auto.
  split; auto. apply Theorem9_5; auto.
  set (h := \{\ λ u v, (u <= 1)%nat /\ (u = 0%nat -> v = a)
    /\ (u = 1%nat -> v = b) \}\). left. exists 1%nat,h.
  assert (Function1_1 h).
  { split; red; intros. applyClassifier2 H4. applyClassifier2 H5.
    destruct H4 as [H4[]], H5 as [_[]]. assert (x = 0 \/ x = 1)%nat as []. lia.
    rewrite H6,H5; auto. rewrite H7,H8; auto. applyClassifier2 H4.
    applyClassifier2 H5. applyClassifier2 H4. applyClassifier2 H5.
    destruct H4 as [H4[]], H5 as [H5[]]. assert (y = 0 \/ y = 1)%nat as []. lia.
    assert (z = 0 \/ z = 1)%nat as []. lia. rewrite H10,H11; auto.
    apply H6 in H10. apply H9 in H11. exfalso. lra. assert (z = 0 \/ z = 1)%nat
    as []. lia. apply H7 in H10. apply H8 in H11. exfalso. lra. lia. }
  split; auto. destruct H4. split; apply AxiomI; split; intros.
  apply Classifier1 in H6 as []. applyClassifier2 H6. destruct H6.
  apply Classifier1; auto. applyClassifier1 H6. apply Classifier1.
  assert (z = 0 \/ z = 1)%nat as []. lia.
  exists a. apply Classifier2; repeat split; auto. intros. exfalso. lia.
  exists b. apply Classifier2; repeat split; auto. intros. exfalso. lia.
  apply Classifier1 in H6 as []. applyClassifier2 H6. destruct H6 as [H6[]].
  apply Classifier1. assert (x = 0 \/ x = 1)%nat as []. lia. apply H7 in H9.
  split. lra. split; auto. split; intros; exfalso; lra. apply H8 in H9. split. lra.
  split; [ |split]; auto; intros; exfalso; lra. apply Classifier1 in H6 as [H6[H7[]]].
  apply Classifier1. assert (z = a \/ a < z < b \/ z = b) as [H10|[]]. lra.
  exists 0%nat. apply Classifier2; split. lia. split; auto. intros. exfalso. lia.
  pose proof (H9 H10). elim H11. apply H1; auto. exists 1%nat.
  apply Classifier2; split. lia. split; auto. intros. exfalso. lia.
Qed.

(* 函数复合后在开区间内的连续性 *)
Lemma Lemma9_12c : ∀ f φ a b α β, a < b -> α < β -> ContinuousClose f a b
  -> ContinuousOpen φ α β -> Continuous φ α -> Continuous φ β
  -> \{ λ u, ∃ x, x ∈ \[α, β\] /\ u = φ[x] \} ⊂ \[a, b\]
  -> ContinuousOpen (f ◦ φ) α β.
Proof.
  intros. red; intros. assert (φ[x] ∈ \[a, b\]).
  { apply H5,Classifier1. exists x. split; auto. apply Classifier1. lra. }
  assert (Continuous φ x). { apply H2; auto. }
  pose proof H8. destruct H9 as [H9[H10[x0[H11[]]]]].
  assert (x ∈ dom[f ◦ φ] /\ ∃ δ, δ > 0 /\ Uº(x; δ) ⊂ dom[f ◦ φ]
    /\ Uº(x; δ) ⊂ \[α, β\]) as [H15[x1[H16[]]]].
  { pose proof H1 as [H14[[H15[]][H18[]]]]. rewrite (Comp_Fun_P2 f φ); auto.
    split. apply Classifier1; split; auto. apply Classifier1.
    apply Classifier1 in H7 as []. destruct H7. destruct H21.
    assert (Continuous f φ[x]) as []; auto.
    rewrite H21; auto. rewrite H7; auto. destruct (Examp2 x0 (x-α) (β-x))
    as [x1[H21[H22[]]]]; try lra. exists x1. split; auto. split; red; intros.
    apply Classifier1; split. apply Classifier1. assert (φ[z] ∈ \[a, b\]).
    { apply H5,Classifier1. exists z. split; auto. apply Classifier1.
      apply Classifier1 in H25 as []. apply Abs_R in H26. lra. }
    apply Classifier1 in H26 as []. destruct H26. destruct H27.
    assert (Continuous f φ[z]) as []; auto. rewrite H27; auto.
    rewrite H26; auto. apply H12,Classifier1. applyClassifier1 H25. lra.
    apply Classifier1. apply Classifier1 in H25 as []. apply Abs_R in H26. lra. }
  pose proof H7. apply Classifier1 in H18 as []. destruct H18. destruct H19.
  apply (Theorem4_5 φ f x φ[x]); auto. apply H1; auto.
  - pose proof H1 as [_[_[H20[H21[x2[H22[]]]]]]]. split; auto. split.
    apply Comp_Fun_P1; auto. exists x1. split; auto. split; auto. intros.
    rewrite H19 in *. pose proof H25. apply H24 in H26 as [x3[[]]].
    pose proof H26. apply H13 in H29 as [x4[]]. destruct (Examp2 x1 x3 x4)
    as [x5[H31[H32[]]]]; try lra. exists x5. split; auto. intros.
    rewrite (Comp_Fun_P3 f φ),(Comp_Fun_P3 f φ); auto;
    [ |apply H14,Classifier1; lra]. rewrite H19. assert (φ[x6] ∈ \[a, b\]).
    { apply H5,Classifier1. exists x6. split; auto. apply H17,Classifier1. lra. }
    apply Classifier1 in H36 as [_[]]. apply H28. assert (0 < ∣(x6 - x)∣ < x4).
    lra. apply H30,Abs_R in H37. lra. rewrite H36,Abs_ge; lra.
  - pose proof H1 as [_[[H20[H21[x2[H22[]]]]]_]]. split; auto. split.
    apply Comp_Fun_P1; auto. exists x1. split; auto. split; auto. intros.
    rewrite H18 in *. pose proof H25. apply H24 in H26 as [x3[[]]].
    pose proof H26. apply H13 in H29 as [x4[]]. destruct (Examp2 x1 x3 x4)
    as [x5[H31[H32[]]]]; try lra. exists x5. split; auto. intros.
    rewrite (Comp_Fun_P3 f φ),(Comp_Fun_P3 f φ); auto;
    [ |apply H14,Classifier1; lra]. rewrite H18. assert (φ[x6] ∈ \[a, b\]).
    { apply H5,Classifier1. exists x6. split; auto. apply H17,Classifier1. lra. }
    apply Classifier1 in H36 as [[]_]. apply H28. assert (0 < ∣(x6 - x)∣ < x4).
    lra. apply H30,Abs_R in H37. lra. rewrite H36,Abs_ge; lra.
Qed.


Require Export A_9_2. (* 定理9.12和9.13需要使用牛顿莱布尼兹公式 *)

Theorem Theorem9_12 : ∀ f φ a b α β, a < b -> ContinuousClose f a b
  -> Function φ -> (∃ J, Def_Integral (dN φ 1%nat) α β J) -> φ[α] = a
  -> φ[β] = b -> \{ λ u, ∃ x, x ∈ \[α, β\] /\ u = φ[x] \} ⊂ \[a, b\]
  -> (VarUp_Integral_Fun f a)[b]
    = (VarUp_Integral_Fun ((f ◦ φ) \* (dN φ 1%nat)) α)[β].
Proof.
  intros. assert (α < β). { destruct H2 as [J[_[]]]; auto. }
  assert (∃ F, Primitive_Close f F a b). { apply Corollary9_10a in H0; eauto. }
  apply Lemma9_12a in H7 as [F[[H7[H8[_[H9[H10[H11 _]]]]]][]]].
  pose proof (dN_Fact2 φ 1%nat). assert (\[α, β\] ⊂ dom[dN φ 1%nat]).
  { destruct H2 as [J[_[_[]]]]; auto. }
  assert (\[α, β\] ⊂ dom[f ◦ φ] /\ \[α, β\] ⊂ dom[F ◦ φ]) as [].
  { rewrite (Comp_Fun_P2 f φ); auto. rewrite (Comp_Fun_P2 F φ); auto.
    split; red; intros; apply Classifier1; split; auto; apply Classifier1;
    [apply H9|apply H10]; apply H5,Classifier1; eauto. }
  assert (Primitive_Close ((f ◦ φ) \* (dN φ 1%nat)) (F ◦ φ) α β).
  { split. apply Corollary_mult_fun_a. split. apply Comp_Fun_P1; auto. split;
    auto. split. rewrite Corollary_mult_fun_c. red; intros. apply Classifier1; auto.
    split; auto. split. intros. assert (\(α, β\) ⊂ \[α, β\]).
    { red; intros. applyClassifier1 H19. apply Classifier1; lra. }
    rewrite Corollary_mult_fun_b; auto. rewrite dN_Fact3. simpl.
    rewrite (Comp_Fun_P3 f φ); auto.
    assert (Derivative F φ[x] f[φ[x]]).
    { assert (φ[x] ∈ \[a, b\]). { apply H5,Classifier1; eauto. }
      apply Classifier1 in H20 as []. destruct H20. destruct H21.
      apply H11,Classifier1; lra. rewrite H21; auto. rewrite H20; auto. }
    pose proof H20. apply Corollary_DerivativeValue_a in H21. rewrite <-H21.
    apply Theorem5_8; auto. apply H19,H15,x_fx_T in H18. applyClassifier2 H18.
    red; eauto. apply dN_Fact1; auto. red; eauto.
    rewrite Corollary_mult_fun_b,Corollary_mult_fun_b,dN_Fact3,dN_Fact3,
    (Comp_Fun_P3 f φ),(Comp_Fun_P3 f φ); auto; try apply H16;
    try apply H15; try (apply Classifier1; lra). simpl. rewrite H3,H4.
    pose proof H12. pose proof H13. apply Corollary_DerivativeValue_a in H18,H19.
    rewrite <-H18,<-H19. split; apply Theorem5_2,Theorem5_8; auto; red; eauto.
    assert (α ∈ \[α, β\]). apply Classifier1; lra. apply H15,x_fx_T in H20.
    applyClassifier2 H20; eauto. apply dN_Fact1; auto. assert (β ∈ \[α, β\]).
    apply Classifier1; lra. apply H15,x_fx_T in H20. applyClassifier2 H20; eauto.
    apply dN_Fact1; auto. }
  assert (∃ J, Def_Integral ((f ◦ φ) \* (dN φ 1%nat)) α β J).
  { apply Property9_4_3; auto. apply Lemma9_12b; auto.
    apply Theorem9_4 in H0 as [J]; auto. apply Theorem9_2 in H0; auto.
    destruct H0 as [_[_[M]]]. split. apply Comp_Fun_P1; auto. split; auto.
    exists M. intros. rewrite (Comp_Fun_P3 f φ); auto. apply H0,H5.
    apply Classifier1; eauto. assert (∀ x, x ∈ \[α, β\] -> Continuous φ x).
    { intros. apply Theorem5_1. apply H15,x_fx_T in H19. applyClassifier2 H19.
      red; eauto. apply dN_Fact1; auto. } apply (Lemma9_12c f φ a b); auto;
    try (red; intros); apply H19,Classifier1; lra. }
  assert (Primitive_Open ((f ◦ φ) \* (dN φ 1%nat)) (F ◦ φ) α β).
  { destruct H18 as [H18[H20[H21[H22[H23[H24[]]]]]]]. split; auto. split; auto.
    split; auto. split; [ |split]; auto; red; intros; [apply H22|apply H23];
    apply Classifier1 in H27 as []; apply Classifier1; lra. }
  assert (ContinuousClose (F ◦ φ) α β).
  { destruct H18 as [_[_[_[_[_[H18[]]]]]]]. split. red; intros.
    apply Theorem5_1. red. exists (((f ◦ φ) \* (dN φ 1%nat))[x]).
    apply H18,Classifier1; lra. split. apply Corollary5_1b; eauto.
    apply Corollary5_1a; eauto. }
  assert (Def_Integral ((f ◦ φ) \* (dN φ 1%nat)) α β ((F ◦ φ)[β] - (F ◦ φ)[α])).
  { apply Theorem9_1; auto. }
  rewrite (Comp_Fun_P3 F φ),(Comp_Fun_P3 F φ) in H22; auto;
  try (apply H17,Classifier1; lra). rewrite H3,H4 in H22.
  assert (\[a, b\] ⊂ dom[VarUp_Integral_Fun f a]
    /\ \[α, β\] ⊂ dom[VarUp_Integral_Fun ((f ◦ φ) \* (dN φ 1%nat)) α]) as [].
  { split; apply VarUp_dom_b; auto; try lra. apply Theorem9_4; auto. }
  pose proof H6. apply (VarUp_Value_gt ((f ◦ φ) \* (dN φ 1%nat))) in H25.
  assert ((VarUp_Integral_Fun ((f ◦ φ) \* (dN φ 1%nat)) α)[β]
    = F[b] - F[a]). { eapply Def_Integral_Uni; eauto. } rewrite H26. clear H26.
  pose proof H. apply (VarUp_Value_gt f) in H26.
  assert (Def_Integral f a b (F[b] - F[a])).
  { apply Corollary9_10c; auto. split; auto. split; auto. split; auto.
    split; auto. split; auto. split; auto. split; apply Theorem5_2; auto. }
  eapply Def_Integral_Uni; eauto. apply H23,Classifier1; lra. apply H24,Classifier1; lra.
Qed.

Theorem Theorem9_13 : ∀ u v a b, a < b
  -> (∀ x, x ∈ \[a, b\] -> Derivable u x /\ Derivable v x)
  -> (∃ J1, Def_Integral (dN u 1%nat) a b J1)
  -> (∃ J2, Def_Integral (dN v 1%nat) a b J2)
  -> (VarUp_Integral_Fun (u \* ((dN v 1%nat))) a)[b]
    = ((u \* v)[b] - (u \* v)[a]) - (VarUp_Integral_Fun ((dN u 1%nat) \* v) a)[b].
Proof.
  intros. assert (ContinuousClose u a b /\ ContinuousClose v a b) as [].
  { assert (∀ x, x ∈ \[a, b\] -> Continuous u x /\ Continuous v x).
    { intros. apply H0 in H3 as []. apply Theorem5_1 in H3,H4; auto. }
    split; split; try (red; intros; apply H3,Classifier1; lra); split;
    apply Theorem4_1,H3,Classifier1; lra. }
  assert (∃ J, Def_Integral ((u \* (dN v 1%nat)) \+ ((dN u 1%nat) \* v)) a b J).
  { apply Theorem9_4 in H3,H4; auto.
    assert ((∃ J1, Def_Integral (u \* (dN v 1%nat)) a b J1)
      /\ (∃ J2, Def_Integral ((dN u 1%nat) \* v) a b J2)) as [[J1][J2]].
    { split; apply Property9_4_3; auto. } exists (J1 + J2).
    apply Property9_4_2a; auto. }
  assert (\[a, b\] ⊂ dom[u] /\ \[a, b\] ⊂ dom[v] /\ \[a, b\] ⊂ dom[dN u 1%nat]
    /\ \[a, b\] ⊂ dom[dN v 1%nat]) as [H6[H7[]]].
  { apply Theorem9_4 in H3,H4; auto. destruct H1 as [J1[_[_[]]]],
    H2 as [J2[_[_[]]]], H3 as [J3[_[_[]]]], H4 as [J4[_[_[]]]]; auto. }
  assert (\(a, b\) ⊂ \[a, b\]).
  { red; intros. applyClassifier1 H10. apply Classifier1. lra. }
  assert (Primitive_Open ((u \* (dN v 1%nat)) \+ ((dN u 1%nat) \* v))
    (u \* v) a b).
  { split. apply Corollary_plus_fun_a. split. apply Corollary_mult_fun_a.
    split; auto. split. rewrite Corollary_plus_fun_c,Corollary_mult_fun_c,
    Corollary_mult_fun_c. red; intros. apply Classifier1; split; apply Classifier1; auto.
    split. rewrite Corollary_mult_fun_c. red; intros. apply Classifier1; auto.
    intros. rewrite Corollary_plus_fun_b,Corollary_mult_fun_b,
    Corollary_mult_fun_b,dN_Fact3,dN_Fact3; auto;
    try (rewrite Corollary_mult_fun_c; apply Classifier1; auto). simpl.
    rewrite Rplus_comm,(Rmult_comm (u[x])). apply Theorem5_5b; apply H0; auto. }
  assert (ContinuousClose (u \* v) a b).
  { assert (∀ x, x ∈ \[a, b\] -> Continuous u x /\ Continuous v x).
    { intros. split; apply Theorem5_1; apply H0; auto. }
    split; [red; intros|split; apply Theorem4_1]; apply Theorem4_4c;
    apply H12,Classifier1; lra. }
  pose proof H11. apply Theorem9_1 in H13; auto.
  assert (\[a, b\] ⊂ dom[VarUp_Integral_Fun ((dN u 1%nat) \* v) a]
    /\ \[a, b\] ⊂ dom[VarUp_Integral_Fun (u \* (dN v 1%nat)) a]) as [].
  { split; apply VarUp_dom_b; try lra; apply Property9_4_3; auto;
    apply Theorem9_4; auto. } pose proof H. pose proof H.
  apply (VarUp_Value_gt ((dN u 1%nat) \* v)) in H16; [ |apply H14,Classifier1; lra].
  apply (VarUp_Value_gt (u \* (dN v 1%nat))) in H17; [ |apply H15,Classifier1; lra].
  assert ((VarUp_Integral_Fun (u \* (dN v 1%nat)) a)[b]
    + (VarUp_Integral_Fun ((dN u 1%nat) \* v) a)[b] = (u \* v)[b] - (u \* v)[a]).
  { apply (Def_Integral_Uni ((u \* (dN v 1%nat)) \+ ((dN u 1%nat) \* v)) a b);
    auto. apply Property9_4_2a; auto. } lra.
Qed.


















