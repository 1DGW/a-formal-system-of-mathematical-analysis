(** A_1 *)
(* 实数与函数基础 *)

(* 读入文件 *)
Require Export A_0.


(****************** 实数 ******************)

(* 读取实数库和实数线性运算策略lra *)
Require Export Coq.Reals.RIneq.
Require Export Coq.micromega.Lra.

(* 打开实数辖域 *)
Open Scope R_scope.

(* 1.1 实数 *)
(* 实数的Archimedes性 *)
Property Archimedes : ∀ a b, 0 < a -> 0 < b -> ∃ (n : nat), (INR n) * a > b.
Proof.
  intros a b H0 H7. assert (H1 : b/a > 0).
  { apply Rmult_gt_0_compat; try lra. apply Rinv_0_lt_compat. apply H0. }
  generalize (archimed (b/a)). intros [H2 H3]. clear H3.
  assert (H3 : IZR (up (b / a)) > 0). lra. apply lt_0_IZR in H3 as H4. 
  exists (Z.to_nat (up (b / a))). rewrite INR_IZR_INZ. apply Z.lt_le_incl in H4.
  rewrite Z2Nat.id; auto. apply Rmult_lt_compat_r with (r := a) in H2; auto.
  assert (H6 : b/a*a = b). field. lra. rewrite H6 in H2. apply H2.
Qed.

Print INR.

(* 定义：绝对值函数 *)
Definition Abs := \{\ λ x y , (x < 0 /\ y = -x) \/ (x >= 0 /\ y = x) \}\.
Notation "∣ x ∣" := (Abs[x])(at level 5, x at level 0).

(* Abs是函数 *)
Fact Fun_Abs : Function Abs.
Proof.
  unfold Abs. unfold Function. intros x y z H0 H1. applyClassifier2 H0. 
  applyClassifier2 H1. destruct H0,H1,H0,H.
  + rewrite <- H2 in H1. auto. 
  + apply Rlt_not_ge in H. contradiction.
  + apply Rlt_not_ge in H0. contradiction.
  + rewrite <- H2 in H1. auto.
Qed.

(* 绝对值不等式 *)
Fact Abs_Rge0 : ∀ x, ∣x∣ >= 0.
Proof.
  intro x. destruct (total_order_T x 0) as [[H0 | H0] | H0].
  - assert (H1 : [x, -x] ∈ Abs). { apply <- Classifier2. left. auto. }
    apply f_x_T in H1; try apply Fun_Abs. rewrite H1. left. 
    apply Ropp_gt_lt_0_contravar. auto.
  - assert (H1 : [x, -x] ∈ Abs). 
    { apply <- Classifier2. right. split.
      - right; auto.
      - rewrite H0. apply Ropp_0. }
    rewrite H0 in *. rewrite Ropp_0 in H1.
    apply f_x_T in H1; try apply Fun_Abs. rewrite H1. right; auto.
  - assert (H1 : [x, x] ∈ Abs).
    { apply <- Classifier2. right. split; auto. left; auto. }
    apply f_x_T in H1; try apply Fun_Abs. rewrite H1. left; auto.
Qed.

Fact Abs_ge : ∀ a, a >= 0 -> ∣a∣ = a.
Proof.
  intros a H0. 
  assert (H1 : [a, a] ∈ Abs). { apply <- Classifier2. right. split; auto. } 
  apply f_x_T; auto. apply Fun_Abs.
Qed.

Fact Abs_gt : ∀ a, a > 0 -> ∣a∣ = a.
Proof. intros a H0. apply Rgt_ge in H0. apply Abs_ge; auto. Qed.

Fact Abs_lt : ∀ a, a < 0 -> ∣a∣ = -a.
Proof.
  intros a H0. 
  assert (H1 : [a, -a] ∈ Abs). { apply <- Classifier2. left. split; auto. }
  apply f_x_T; auto. apply Fun_Abs.
Qed.

Fact Abs_not_eq_0 : ∀ a, a <> 0 <-> ∣a∣ > 0.
Proof.
  intro a. split; intro H0.
  - apply Rdichotomy in H0 as H1. destruct H1 as [H1 | H1].
    + rewrite Abs_lt; auto. apply Ropp_gt_lt_0_contravar; auto.
    + rewrite Abs_gt; auto.
  - intro H1. rewrite Abs_ge in H0.
    + apply Rgt_not_eq in H0. auto.
    + right; auto.
Qed.

Fact Rge_lt :∀ r1 r2 : R, r1 >= r2 \/ r1 < r2.
Proof.
  intros. destruct (total_order_T r1 r2) as [[ | ] | ]; auto;
  left; [right|left]; auto.
Qed.

(* 绝对值的性质 *)
Fact Abs_eq_neg : ∀ a, ∣a∣ = ∣(-a)∣.
Proof.
  intro a. destruct (Rge_lt a 0) as [H0 | H0].
  - apply Abs_ge in H0 as H1. rewrite H1. destruct H0 as [H0 | H0].
    + apply Ropp_lt_gt_0_contravar in H0 as H2. apply Abs_lt in H2 as H3.
      rewrite H3. rewrite Ropp_involutive; auto.
    + rewrite H0. rewrite Ropp_0. symmetry. apply Abs_ge. right; auto.
  - apply Abs_lt in H0 as H1. apply Ropp_gt_lt_0_contravar in H0 as H2.
    apply Rgt_ge in H2 as H3. apply Abs_ge in H3 as H4. rewrite H4. auto.
Qed.

Fact Abs_eq_0 : ∀ a, a = 0 <-> ∣a∣ = 0.
Proof.
  intros. split; intro H0.
  - rewrite H0. apply Abs_ge. lra. 
  - pose proof (Abs_not_eq_0 a). pose proof (Req_dec a 0).
    destruct H1. auto. rewrite H0 in H. apply H in H1. lra.
Qed.

Fact Abs_neg_pos : ∀ a, -∣a∣ <= a <= ∣a∣.
Proof.
  intro a. destruct (Rge_lt a 0) as [H0 | H0].
  - apply Abs_ge in H0 as H1. rewrite H1. split.
    + destruct H0 as [H0 | H0].
      * left. apply (Ropp_lt_gt_0_contravar a) in H0 as H2.
        apply Rlt_trans with (r2 := 0); auto.
      * rewrite H0. rewrite Ropp_0. right; auto.
    + right; auto.
  - apply Abs_lt in H0 as H1. rewrite H1. rewrite Ropp_involutive. split.
    + right; auto.
    + apply Ropp_gt_lt_0_contravar in H0 as H2. left.
      apply Rlt_trans with (r2 := 0); auto.
Qed.

Fact Abs_R : ∀ a b, ∣a∣ < b <-> -b < a < b.
Proof.
  intros a b. split.
  - intro H0. assert (H2 : b > 0). 
    { destruct (Abs_Rge0 a) as [H1 | H1].
      - apply Rlt_trans with (r2 := ∣a∣); auto.
      - rewrite <- H1. auto. }
    destruct (total_order_T a 0) as [[H1 | H1] | H1].
    + apply Abs_lt in H1 as H3. rewrite H3 in H0. split.
      * apply Ropp_lt_cancel. rewrite Ropp_involutive. auto.
      * apply Rlt_trans with (r2 := 0); auto.
    + rewrite H1. split; auto. apply Ropp_lt_gt_0_contravar. auto.
    + assert (H3 : ∣a∣ = a). { apply Abs_ge. left; auto. }
      rewrite H3 in H0. split; auto. apply Rlt_trans with (r2 := 0); auto.
      apply Ropp_lt_gt_0_contravar. auto.
  - intro H0. destruct H0 as [H0 H1].
    destruct (total_order_T a 0) as [[H2 | H2] | H2].
    + apply Abs_lt in H2 as H3. rewrite H3. apply Ropp_lt_cancel.
      rewrite Ropp_involutive. auto.
    + assert (H3 : ∣a∣ = a). { apply Abs_ge. right; auto. } rewrite H3. auto.
    + assert (H3 : ∣a∣ = a). { apply Abs_ge. left; auto. } rewrite H3. auto.
Qed.

Fact Abs_le_R : ∀ a b, ∣a∣ <= b <-> -b <= a <= b.
Proof.
  intros a b. split; intro H0.
  - destruct H0 as [H0 | H0].
    + apply Abs_R in H0 as H1. split.
      * left; apply H1.
      * left; apply H1.
    + rewrite <- H0. apply Abs_neg_pos.
  - assert (H5 : b >= 0).
    { apply NNPP. destruct H0 as [H0 H1].
      intro H2. destruct (Rge_lt b 0) as [H3 | H3]; auto.
      apply Ropp_gt_lt_0_contravar in H3 as H4.
      assert (I1 : -b <= b). { apply Rle_trans with (r2 := a); auto. }
      apply (Rle_not_gt (-b) b); auto. apply Rlt_trans with (r2 := 0); auto. }
    destruct H0 as [H0 H1]. destruct H0 as [H0 | H0].
    + destruct H1 as [H1 | H1].
      * left. apply Abs_R. split; auto.
      * rewrite H1 in *. right. apply Abs_ge; auto.
    + apply Ropp_eq_compat in H0. rewrite Ropp_involutive in H0.
      rewrite H0 in *. destruct H5 as [H5 | H5].
      * apply Ropp_lt_gt_0_contravar in H5. rewrite Ropp_involutive in H5.
        right. apply Abs_lt; auto.
      * rewrite H5. apply Ropp_eq_compat in H5. rewrite Ropp_involutive in H5. 
        rewrite Ropp_0 in H5. rewrite H5. right. apply Abs_ge. right; auto.
Qed.

Fact Abs_plus_le : ∀ a b, ∣(a + b)∣ <= ∣a∣+∣b∣.
Proof.
  intros a b. generalize (Abs_neg_pos a). intro H0. generalize (Abs_neg_pos b). 
  intro H1. destruct H0 as [H0 H2]. destruct H1 as [H1 H3]. apply Abs_le_R. split.
  - rewrite Ropp_plus_distr. apply Rplus_le_compat; auto.
  - apply Rplus_le_compat; auto.
Qed.

Fact Abs_minus_le : ∀ a b, ∣(a - b)∣ <= ∣a∣+∣b∣.
Proof.
  intros a b. generalize (Abs_neg_pos a). intro H0. generalize (Abs_neg_pos (-b)). 
  intro H1. rewrite <- Abs_eq_neg in H1. destruct H0 as [H0 H2]. 
  destruct H1 as [H1 H3]. apply Abs_le_R. split.
  - rewrite Ropp_plus_distr. apply Rplus_le_compat; auto.
  - apply Rplus_le_compat; auto.
Qed.

Fact Abs_abs_minus : ∀ a b, ∣(∣a∣-∣b∣)∣ <= ∣(a - b)∣.
Proof.
  intros a b. destruct (Rlt_or_le a 0) as [H0 | H0].
  - apply Abs_lt in H0 as H1. destruct (Rlt_or_le b 0) as [H2 | H2].
    + apply Abs_lt in H2 as H3. rewrite H1; rewrite H3. right. 
      assert (H4 : -a - -b = - (a - b)). field.
      rewrite H4. rewrite <- Abs_eq_neg. reflexivity.
    + apply Rle_ge in H2. apply Abs_ge in H2 as H3.
      rewrite H1; rewrite H3. assert (H4 : a - b < 0).
      { apply Rge_le in H2. apply Ropp_0_le_ge_contravar in H2 as H4.
        apply Rge_le in H4. unfold Rminus. assert (H5 : 0 = 0 + 0). field.
        rewrite H5. apply Rplus_lt_le_compat; auto. }
      apply Abs_lt in H4 as H5. rewrite H5. assert (H6 : -(a - b) = -a + b).
      field. rewrite H6. generalize (Rlt_or_le (-a - b) 0). intro H7.
      destruct H7 as [H7 | H7].
      * apply Abs_lt in H7 as H8. rewrite H8. assert (H9 : -(-a - b) = a + b).
        field. rewrite H9. apply Rplus_le_compat_r.
        apply Ropp_gt_lt_0_contravar in H0 as H10. left.
        apply Rlt_trans with (r2 := 0); auto.
      * apply Rle_ge in H7. apply Abs_ge in H7 as H8. rewrite H8.
        unfold Rminus. apply Rplus_le_compat_l. apply Rge_le in H2.
        apply Ropp_0_le_ge_contravar in H2 as H9.
        apply Rge_le in H9. eapply Rle_trans; eauto.
  - apply Rle_ge in H0 as H1. apply Abs_ge in H1 as H2.
    rewrite H2. destruct (Rlt_or_le b 0) as [H3 | H3].
    + apply Abs_lt in H3 as H4. rewrite H4. assert (H5 : a-b > 0).
      { apply Ropp_gt_lt_0_contravar in H3 as I1. unfold Rminus.
        assert (I2 : 0 = 0 + 0). field. rewrite I2.
        apply Rplus_ge_gt_compat; auto. }
      apply Abs_gt in H5 as H6. rewrite H6.
      generalize (Rlt_or_le (a - -b) 0). intro H7.
      destruct H7 as [H7 | H7].
      * apply Abs_lt in H7 as H8. rewrite H8.
        assert (H9 : -(a - -b) = -a - b). field. rewrite H9.
        unfold Rminus. apply Rplus_le_compat_r.
        apply Ropp_0_le_ge_contravar in H0 as H10. apply Rge_le in H10.
        eapply Rle_trans; eauto.
      * apply Rle_ge in H7. apply Abs_ge in H7 as H8. rewrite H8.
        assert (H9 : a - -b = a+b). field. rewrite H9. unfold Rminus.
        apply Rplus_le_compat_l. lra.
    + apply Rle_ge in H3 as H4. apply Abs_ge in H4 as H5.
      rewrite H5. right. reflexivity.
Qed.

Fact Abs_abs_minus' : ∀ a b, ∣a∣-∣b∣ <= ∣(a - b)∣.
Proof.
  intros a b. generalize (Abs_neg_pos (∣a∣ - ∣b∣)). intro H0.
  destruct H0 as [H0 H1]. generalize (Abs_abs_minus a b). intro H2. lra.
Qed.

Fact Abs_mult : ∀ a b, ∣(a * b)∣ = ∣a∣ * ∣b∣.
Proof.
  intros a b. destruct (Rge_lt a 0) as [H0 | H0].
  - apply Abs_ge in H0 as H1. destruct (Rge_lt b 0) as [H2 | H2].
    + apply Abs_ge in H2 as H3. rewrite H1; rewrite H3.
      apply Rmult_ge_compat_r with (r := b) in H0 as H4; auto.
      rewrite Rmult_0_l in H4. apply Abs_ge in H4 as H5. auto.
    + apply Abs_lt in H2 as H3. rewrite H1; rewrite H3.
      destruct H0 as [H0 | H0].
      * apply Rmult_lt_gt_compat_neg_l with (r := b) in H0 as H4; auto.
        rewrite (Rmult_comm b a) in H4. rewrite Rmult_0_r in H4.
        apply Abs_lt in H4 as H5. rewrite H5.
        apply Ropp_mult_distr_r.
      * rewrite H0 in *. repeat rewrite Rmult_0_l. auto.
  - apply Abs_lt in H0 as H1. rewrite H1. destruct (Rge_lt b 0) as [H2 | H2].
    + destruct H2 as [H2 | H2].
      * apply Rmult_lt_gt_compat_neg_l with (r := a) in H2 as H4; auto.
        rewrite Rmult_0_r in H4.
        apply Abs_lt in H4 as H5. rewrite H5.
        assert (H6 : ∣b∣ = b).
        { apply Abs_ge. left; auto. }
        rewrite H6. apply Ropp_mult_distr_l.
      * rewrite H2 in *. rewrite Rmult_0_r. assert (H3 : ∣0∣ = 0).
        { apply Abs_ge. right; auto. }
        rewrite H3. rewrite Rmult_0_r. auto.
    + apply Rmult_lt_gt_compat_neg_l with (r := a) in H2 as H3; auto.
      rewrite Rmult_0_r in H3. apply Abs_lt in H2 as H4.
      rewrite H4. assert (H5 : ∣(a*b)∣ = a*b). { apply Abs_ge. left; auto. }
      rewrite H5. rewrite Rmult_opp_opp. auto.
Qed.

Fact Abs_div : ∀ a b, b <> 0 -> ∣(a / b)∣ = ∣a∣ / ∣b∣.
Proof.
  intros a b H0. unfold Rdiv in *. rewrite Abs_mult.
  assert (H1 : ∣(/b)∣ = /∣b∣).
  { destruct (Rge_lt b 0) as [H1 | H1].
    - destruct H1 as [H1 | H1].
      + apply Rinv_0_lt_compat in H1 as H2. assert (H3 : ∣(/b)∣ = / b).
        { apply Abs_ge. left; auto. }
        rewrite H3. assert (H4 : ∣b∣ = b). { apply Abs_ge. left; auto. }
        rewrite H4. auto.
      + exfalso; auto.
    - apply Rinv_lt_0_compat in H1 as H2. apply Abs_lt in H1. apply Abs_lt in H2. 
      rewrite H1. rewrite H2. apply Ropp_inv_permute_depr; auto. }
  rewrite H1. auto.
Qed.

(* 几个例子 *)
Example Examp1 : ∀ a b, a > 0 -> b > 0 -> ∃ c, c > 0 /\ c < a /\ c < b.
Proof.
  intros a b H0 H1. destruct (Rlt_or_le a b) as [H2 | H2].
  - exists (a/2). repeat split; lra.
  - exists (b/2). repeat split; lra.
Qed.

Example Examp2 : ∀ a b c, a > 0 -> b > 0 -> c > 0
  -> ∃ d, d > 0 /\ d < a /\ d < b /\ d < c.
Proof.
  intros a b c H0 H1 H2. destruct (Rlt_or_le a b) as [H3 | H3].
  - destruct (Rlt_or_le a c) as [H4 | H4].
    + exists (a/2). repeat split; lra.
    + exists (c/2). repeat split; lra.
  - destruct (Rlt_or_le b c) as [H4 | H4].
    + exists (b/2). repeat split; lra.
    + exists (c/2). repeat split; lra.
Qed.

Example Examp3 : ∀ a b c d, a > 0 -> b > 0 -> c > 0 -> d > 0 
  -> ∃ e, e > 0 /\ e < a /\ e < b /\ e < c /\ e < d.
Proof.
  intros a b c d H H1 H2 H3. destruct (Rlt_or_le a b). 
  - destruct (Rlt_or_le a c).
    + destruct (Rlt_or_le a d);
      [ exists (a / 2) | exists (d / 2)]; repeat split; lra.
    + destruct (Rlt_or_le c d);
      [ exists (c / 2)| exists (d / 2)]; repeat split; lra.
  - destruct (Rlt_or_le b c) as [L1 | L1].
      + destruct (Rlt_or_le d b) as [L2|L2];
        [ exists (d / 2) | exists (b / 2)]; repeat split; lra.
      + destruct (Rlt_or_le c d) as [L2|L2];
        [ exists (c / 2) | exists (d / 2)]; repeat split; lra.
Qed.

Example Examp4 : ∀ a b, 0 < ∣a∣ < b -> a <> 0 /\ -b < a < b.
Proof.
  intros a b [H0 H1]. apply Abs_not_eq_0 in H0.
  apply Abs_R in H1. split; assumption.
Qed.

(* 关于实数运算的一些简单性质 *)
Fact Rmult_le_le : ∀ a b, a < 0 /\ b < 0 -> a * b > 0.
Proof.
  intros. destruct H. rewrite <- Rmult_opp_opp. apply Ropp_gt_lt_0_contravar in H.
  apply Ropp_gt_lt_0_contravar in H0. apply Rmult_gt_0_compat; auto.
Qed.

Fact Rmult_leq_le : ∀ a b, a <= 0 /\ b < 0 -> a * b >= 0.
Proof.
  intros. destruct H. destruct H.
  - left. apply Rmult_le_le; auto.
  - right. apply Rmult_eq_0_compat_r; auto.
Qed.

Fact Rmult_le_gr : ∀ a b, a < 0 /\ b > 0 -> a * b < 0.
Proof.  
  intros. destruct H. apply (Rmult_lt_gt_compat_neg_l a 0 b) in H; auto. lra.
Qed.

Fact Rmult_gre_gr : ∀ a b, a >= 0 /\ b > 0 -> a * b >= 0.
Proof.
  intros. destruct H. destruct H.
  - left. apply Rmult_gt_0_compat; auto.
  - right. apply Rmult_eq_0_compat_r; auto.
Qed.

Fact Rmult_gre_le : ∀ a b, a >= 0 /\ b < 0 -> a * b <= 0.
Proof.
  intros. destruct H. destruct H.
  - left. rewrite Rmult_comm. apply Rmult_le_gr; auto. 
  - right. apply Rmult_eq_0_compat_r; auto.
Qed.

Fact Rmult_leq_gre : ∀ a b, a <= 0 /\ b > 0 -> a * b <= 0.
Proof.
  intros. destruct H. destruct H.
  - left. apply Rmult_le_gr; auto. 
  - right. apply Rmult_eq_0_compat_r; auto.
Qed.

(************************ 数集⋅确界原理 ******************)
(* 1.2.1 区间与邻域 *)
(* 有限区间 *)
(* 开区间 *)
Definition OpenInterval1 a b := \{ λ x, x > a /\ x < b \}.
Notation "\( a , b \)" := (OpenInterval1 a b) (at level 5).

(* 闭区间 *)
Definition CloseInterval a b := \{ λ x, x >= a /\ x <= b \}.
Notation "\[ a , b \]" := (CloseInterval a b) (at level 5).

(* 半开半闭区间 *)
Definition CloseOpen a b := \{ λ x, x >= a /\ x < b \}.
Notation "\[ a , b \)" := (CloseOpen a b)(at level 5).
Definition OpenClose a b := \{ λ x, x > a /\ x <= b \}.
Notation "\( a , b \]" := (OpenClose a b)(at level 5).

(* 无限区间 *)
(* 正无穷 *)
Definition ClosePositiveInf a := \{ λ x, x >= a \}.
Notation "\[ a , +∞ \)" := (ClosePositiveInf a)(at level 5).
Definition OpenPositiveInf a := \{ λ x, x > a \}.
Notation "\( a , +∞ \)" := (OpenPositiveInf a)(at level 5).

(* 负无穷 *)
Definition CloseNegativeInf a := \{ λ x, x <= a \}.
Notation "\( -∞ , a \]" := (CloseNegativeInf a)(at level 5).
Definition OpenNegativeInf a := \{ λ x, x < a \}.
Notation "\( -∞ , a \)" := (OpenNegativeInf a)(at level 5).

Notation "\( -∞ , +∞ \)" := (Full R) (at level 5).

(* 邻域 *)
Definition Neighbor a δ := \{ λ x, ∣(x-a)∣ < δ \}.
Notation "U( a ; δ )" := (Neighbor a δ)(a, δ at level 0, at level 4).
(* 左邻域 *)
Definition leftNeighbor a δ := \(a-δ, a\].
Notation "U-( a ; δ )" := (leftNeighbor a δ)(a, δ at level 0, at level 4).
(* 右邻域 *)
Definition rightNeighbor a δ := \[a, a+δ\).
Notation "U+( a ; δ )" := (rightNeighbor a δ)(a, δ at level 0, at level 4).
(* 去心邻域 *)
Definition Neighbor0 a δ := \{ λ x, 0 < ∣(x-a)∣ < δ \}.
Notation "Uº( a ; δ )" := (Neighbor0 a δ)(a, δ at level 0, at level 4).
(* 左去心邻域 *)
Definition leftNeighbor0 a δ := \(a-δ, a\).
Notation "U-º( a ; δ )" := (leftNeighbor0 a δ)(a, δ at level 0, at level 4).
(* 右去心邻域 *)
Definition rightNeighbor0 a δ := \(a, a+δ\).
Notation "U+º( a ; δ )" := (rightNeighbor0 a δ)(a, δ at level 0, at level 4).
(* 无穷邻域 *)
Definition Neighbor_infinity M := \{ λ x, 0 < M < ∣x∣ \}.
Notation "U(∞) M" := (Neighbor_infinity M)(at level 5).
(* 正无穷邻域 *)
Definition PNeighbor_infinity M := \{ λ x, M < x \}.
Notation "U(+∞) M" := \(M , +∞\)(at level 5).
(* 负无穷邻域 *)
Definition NNeighbor_infinity M := \{ λ x, x < M \}.
Notation "U(-∞) M" := \(-∞ , M\)(at level 5).

(* 有界集⋅确界原理 *)
(* 上界 *)
Definition Upper S M := ∀ x, x ∈ S -> x <= M.
(* 下界 *)
Definition Lower S L := ∀ x, x ∈ S -> x >= L.

(* 有界集 *)
Definition Bounded S := ∃ M L : R, (Upper S M) /\ (Lower S L).
(* 无界集 *)
Definition unBounded S := ~ (Bounded S).

(* 上确界 *)
Definition sup S η := (Upper S η) /\ (∀ a, a < η -> (∃ x0, x0 ∈ S /\ x0 > a)).
(* 下确界 *)
Definition inf S ξ := (Lower S ξ) /\ (∀ b, b > ξ -> (∃ x0, x0 ∈ S /\ x0 < b)).



(* 引理: 上确界原理 *)
Lemma Sup_principle : ∀ A, NotEmpty A -> ((∃ M, Upper A M) -> (∃ η, sup A η)).
Proof.
  intros A H0 H1. destruct H1 as [M H1]. unfold Upper in H1.
  assert (H2 : ∃ E, E = (fun x => x ∈ A)). { exists (fun x => x ∈ A). auto. }
  destruct H2 as [E H2]. assert (H3 : is_upper_bound E M).
  { unfold is_upper_bound. intros x H3. apply H1. rewrite H2 in H3. auto. }
  assert (H4 : bound E). { unfold bound. exists M. auto. }
  unfold NotEmpty in H0. assert (H5 : ∃ x : R, E x).
  { destruct H0 as [x H0]. exists x. rewrite H2. auto. }
  apply completeness in H5 as η; auto. destruct η as [η H6]. exists η. 
  unfold is_lub in H6. destruct H6 as [H6 H7]. unfold sup. split.
  - unfold Upper. intros x H8. unfold is_upper_bound in H6. 
    apply H6. rewrite H2. auto.
  - intros a H8. apply NNPP. intro H9.
    assert (H10 : ∀ x0, ~ (x0 ∈ A /\ x0 > a)).
    { intros. intro. elim H9; eauto. }
    assert (H11 : is_upper_bound E a).
    { unfold is_upper_bound. intros x H11.
      assert (H12 : ~ (x ∈ A /\ x > a)). { apply H10. }
      apply not_and_or in H12. rewrite H2 in H11. destruct H12 as [H12 | H12].
      - exfalso; auto.
      - apply Rnot_gt_le. auto. }
    apply H7 in H11 as H12. apply Rle_not_gt in H12. auto.
Qed.

(* 定理: 确界原理 *)
Theorem Sup_inf_principle : ∀ A, NotEmpty A 
  -> ((∃ M, Upper A M) -> (∃ η, sup A η)) /\ ((∃ L, Lower A L) -> (∃ ξ, inf A ξ)).
Proof.
  intros A H0. split.
  - apply Sup_principle. auto.
  - assert (H1 : ∃ B, B = \{ λ x, (-x) ∈ A \}). 
    { exists \{ λ x, (-x) ∈ A \}; auto. }
    destruct H1 as [B H1]. assert (H2 : NotEmpty B).
    { unfold NotEmpty in *. destruct H0 as [x H0]. exists (-x).
      rewrite H1. apply <- Classifier1. rewrite Ropp_involutive. auto. }
    intro H3. destruct H3 as [L H3]. assert (H4 : ∃ M, Upper B M).
    { exists (-L). unfold Upper. intros x H4. unfold Lower in H3. rewrite H1 in H4.
      applyClassifier1 H4. apply H3 in H4. apply Ropp_ge_contravar in H4. 
      rewrite Ropp_involutive in H4. apply Rge_le. auto. }
    apply Sup_principle in H4 as H5; auto. destruct H5 as [η H5]. exists (-η).
    unfold inf. unfold sup in H5. destruct H5 as [H5 H6]. split.
    + unfold Lower. unfold Upper in H5. intros x H7. apply Ropp_ge_cancel. 
      rewrite Ropp_involutive. apply Rle_ge. apply H5. rewrite H1. 
      apply <- Classifier1. rewrite Ropp_involutive. auto.
    + intros b H7. apply Ropp_gt_contravar in H7. rewrite Ropp_involutive in H7.
      apply H6 in H7 as H8. destruct H8 as [x [H8 H9]]. exists (-x). split.
      * rewrite H1 in H8. applyClassifier1 H8. auto.
      * apply Ropp_lt_cancel. rewrite Ropp_involutive. auto.
Qed.

Print bound.
Print is_upper_bound.
Check completeness.
Print is_lub.


(*********************** 具有某些特性的函数 *********************)
(* 1.3.1 有界函数 *)
(* 有上界函数 *)
Definition UpBoundedFun f D := Function f /\ D ⊂ dom[f]
  /\ ∃ M, (∀ x : R, x ∈ D -> f[x] <= M).
(* 有下界函数 *)
Definition LowBoundedFun f D := Function f /\ D ⊂ dom[f]
  /\ ∃ L, (∀ x : R, x ∈ D -> f[x] >= L).

(* 有界函数 *)
Definition BoundedFun (f : (@set (@prod R R))) := Function f 
  /\ ∃ M, (∀ (x y : R), [x, y] ∈ f -> ∣y∣ <= M).
(* D上的有界函数 *)
Definition DBoundedFun f D := Function f /\ D ⊂ dom[f]
  /\ ∃ M, (∀ x : R, x ∈ D -> ∣(f[x])∣ <= M).

(* 最大值 *)
Definition DMaxValue f D m := D ⊂ dom[f]
  /\ (∀ x : R, x ∈ D -> f[x] <= m) /\ (∃ x0, x0 ∈ D /\ f[x0] = m).
(* 最小值 *)
Definition DMinValue f D m := D ⊂ dom[f]
  /\ (∀ x : R, x ∈ D -> m <= f[x]) /\ (∃ x0, x0 ∈ D /\ f[x0] = m).

(* 1.3.2 单调函数 *)
(* 增函数 *)
Definition IncreaseFun f := Function f
  /\ (∀ (x1 y1 x2 y2 : R), [x1, y1] ∈ f -> [x2, y2] ∈ f -> x1 < x2 -> y1 <= y2).
(* 严格增函数 *)
Definition StrictlyIncreaseFun f := Function f
  /\ (∀ (x1 y1 x2 y2 : R), [x1, y1] ∈ f -> [x2, y2] ∈ f -> x1 < x2 -> y1 < y2).
(* D上的增函数 *)
Definition DIncreaseFun f D := Function f /\ D ⊂ dom[f]
  /\ (∀ x1 x2, x1 ∈ D -> x2 ∈ D -> x1 < x2 -> f[x1] <= f[x2]).
(* D上的严格增函数 *)
Definition DStrictlyIncreaseFun f D := Function f /\ D ⊂ dom[f]
  /\ (∀ x1 x2, x1 ∈ D -> x2 ∈ D -> x1 < x2 -> f[x1] < f[x2]).

(* 减函数 *)
Definition DecreaseFun f := Function f
  /\ (∀ (x1 y1 x2 y2 : R), [x1, y1] ∈ f -> [x2, y2] ∈ f -> x1 < x2 -> y1 >= y2).
(* 严格减函数 *)
Definition StrictlyDecreaseFun f := Function f
  /\ (∀ (x1 y1 x2 y2 : R), [x1, y1] ∈ f -> [x2, y2] ∈ f -> x1 < x2 -> y1 > y2).
(* D上的减函数 *)
Definition DDecreaseFun f D := Function f /\ D ⊂ dom[f]
  /\ (∀ (x1 x2 : R), x1 ∈ D -> x2 ∈ D -> x1 < x2 -> f[x1] >= f[x2]).
(* D上的严格减函数 *)
Definition DStrictlyDecreaseFun f D := Function f /\ D ⊂ dom[f]
  /\ (∀ (x1 x2 : R), x1 ∈ D -> x2 ∈ D -> x1 < x2 -> f[x1] > f[x2]).

(* 单调函数 *)
Definition MonotonicFun f := IncreaseFun f \/ DecreaseFun f.
(* 严格单调函数 *)
Definition StrictlyMonotonicFun f := StrictlyIncreaseFun f \/ StrictlyDecreaseFun f.
(* D上的单调函数 *)
Definition DMonotonicFun f D := DIncreaseFun f D \/ DDecreaseFun f D.
(* D上的严格单调函数 *)
Definition DStrictlyMonotonicFun f D := DStrictlyIncreaseFun f D
  \/ DStrictlyDecreaseFun f D.

(* 定理1.2 *)
Theorem Theorem1_2a : ∀ f, StrictlyIncreaseFun f -> StrictlyIncreaseFun (f﹣¹).
Proof.
  intros f H0. unfold StrictlyIncreaseFun in *. destruct H0 as [H0 H1]. split.
  - unfold Function in *. intros x y z H2 H3. 
    apply -> Classifier2 in H2; simpl in H2. apply -> Classifier2 in H3; simpl in H3.
    destruct (total_order_T y z) as [[H4 | H4] | H4].
    + apply (H1 y x z x) in H4 as H5; auto. exfalso.
      apply Rlt_not_ge with (r1 := x) (r2 := x); auto. right; auto.
    + auto.
    + apply (H1 z x y x) in H4 as H5; auto. exfalso.
      apply Rlt_not_ge with (r1 := x) (r2 := x); auto. right; auto.
  - intros x1 y1 x2 y2 H2 H3 H4. apply -> Classifier2 in H2;
    simpl in H2. apply -> Classifier2 in H3; simpl in H3.
    destruct (total_order_T y1 y2) as [[H5 | H5] | H5].
    + auto.
    + exfalso. rewrite <- H5 in H3. apply (H0 y1 x1 x2) in H2 as H6; auto.
      apply Rlt_not_ge with (r1 := x1) (r2 := x2); auto. right; auto.
    + exfalso. apply (H1 y2 x2 y1 x1) in H2 as H6; auto.
      apply Rlt_not_ge with (r1 := x1) (r2 := x2); auto. left; auto.
Qed.

Theorem Theorem1_2b : ∀ f, StrictlyDecreaseFun f -> StrictlyDecreaseFun (f﹣¹).
Proof.
  intros f H0. unfold StrictlyDecreaseFun in *. destruct H0 as [H0 H1]. split.
  - unfold Function in *. intros x y z H2 H3. 
    apply -> Classifier2 in H2; simpl in H2. apply -> Classifier2 in H3; simpl in H3.
    destruct (total_order_T y z) as [[H4 | H4] | H4].
    + apply (H1 y x z x) in H4 as H5; auto. exfalso.
      apply Rlt_not_ge with (r1 := x) (r2 := x); auto. left; auto.
    + auto.
    + apply (H1 z x y x) in H4 as H5; auto. exfalso.
      apply Rlt_not_ge with (r1 := x) (r2 := x); auto. left; auto.
  - intros x1 y1 x2 y2 H2 H3 H4. apply -> Classifier2 in H2;
    simpl in H2. apply -> Classifier2 in H3; simpl in H3.
    destruct (total_order_T y1 y2) as [[H5 | H5] | H5].
    + exfalso. apply (H1 y1 x1 y2 x2) in H2 as H6; auto.
      apply Rlt_not_ge with (r1 := x1) (r2 := x2); auto. left; auto.
    + exfalso. rewrite <- H5 in H3. apply (H0 y1 x1 x2) in H2 as H6; auto.
      apply Rlt_not_ge with (r1 := x1) (r2 := x2); auto. right; auto.
    + auto.
Qed.

(* 奇偶函数 *)
(* 奇函数 *)
Definition OddFun f := Function f
  /\ (∀ x, x ∈ dom[f] -> (-x) ∈ dom[f] /\ f[-x] = -f[x]).
(* 偶函数 *)
Definition EvenFun (f : @set (@prod R R)) := Function f
  /\ (∀ x, x ∈ dom[f] -> (-x) ∈ dom[f] /\ f[-x] = f[x]).

(* 周期函数 *)
(* 周期函数 *)
Definition PeriodicFun (f : @set (@prod R R)) σ := Function f /\ 0 <= σ
  /\ (∀ x, x ∈ dom[f] -> (x + σ) ∈ dom[f] /\ f[x + σ] = f[x])
  /\ (∀ x, x ∈ dom[f] -> (x - σ) ∈ dom[f] /\ f[x - σ] = f[x]).

Corollary Corollary_PFun : ∀ f σ, PeriodicFun f σ 
  -> (∀ n, PeriodicFun f ((INR n) * σ)).
Proof.
  intros. induction n.
  - simpl. rewrite Rmult_0_l. destruct H as [H[H0[]]].
    repeat split; intros; try rewrite Rplus_0_r; try rewrite Rminus_0_r; auto.
    apply Rge_refl.
  - assert ((INR (S n)) * σ = (INR n) * σ + 1 * σ).
    { rewrite <-Rmult_plus_distr_r,S_INR; auto. }
    rewrite Rmult_1_l in H0. destruct H as [H[H1[]]].
    destruct IHn as [H4[H5[]]]. split; intros; auto. split.
    rewrite H0. apply Rplus_le_le_0_compat; auto. split; intros.
    + rewrite H0,<-Rplus_assoc. pose proof H8.
      apply H6 in H8 as []. rewrite <-H10. apply (H2 (x + (INR n) * σ)); auto.
    + rewrite H0. assert (x - ((INR n) * σ + σ) = x - (INR n) * σ - σ). lra.
      rewrite H9. pose proof H8. apply H7 in H8 as []. rewrite <-H11.
      apply (H3 (x - (INR n) * σ)); auto.
Qed.

(* 函数的四则运算 *)
Definition plus_fun (f g : @set (@prod R R)) := (\{\ λ x y, x ∈ dom[f]
  /\ x ∈ dom[g] /\ y = f[x] + g[x] \}\).
Notation "f \+ g" := (plus_fun f g) (at level 45, left associativity).
Definition plus'_fun (f : @set (@prod R R)) a := (\{\ λ x y, x ∈ dom[f]
  /\ y = f[x] + a \}\).
Notation "f \\+ a" := (plus'_fun f a)(at level 45, left associativity).

Corollary Corollary_plus_fun_a : ∀ f g, Function (f \+ g).
Proof.
  intros. unfold Function; intros. applyClassifier2 H. applyClassifier2 H0.
  destruct H as [H[]], H0 as [H0[]]. rewrite H2,H4; auto.
Qed.

Corollary Corollary_plus_fun_b : ∀ f g x, x ∈ dom[f] -> x ∈ dom[g]
  -> (f \+ g)[x] = f[x] + g[x].
Proof.
  intros. pose proof (Corollary_plus_fun_a f g). apply f_x_T; auto.
  apply Classifier2; auto.
Qed.

Corollary Corollary_plus_fun_c : ∀ f g, dom[(f \+ g)] = dom[f] ∩ dom[g].
Proof.
  intros. apply AxiomI; split; intros. applyClassifier1 H. destruct H.
  applyClassifier2 H. destruct H as [H []]. apply Classifier1; auto. applyClassifier1 H. 
  destruct H. apply Classifier1. exists (f[z] + g[z]). apply Classifier2; auto.
Qed.

Definition sub_fun (f g : @set (@prod R R)) := (\{\ λ x y, x ∈ dom[f]
  /\ x ∈ dom[g] /\ y = f[x] - g[x] \}\).
Notation "f \- g" := (sub_fun f g)(at level 45, left associativity).
Definition sub'_fun (f : @set (@prod R R)) a := (\{\ λ x y, x ∈ dom[f]
  /\ y = f[x] - a \}\).
Notation "f \\- a" := (sub'_fun f a)(at level 45, left associativity).

Corollary Corollary_sub_fun_a : ∀ f g, Function (f \- g).
Proof.
  intros. unfold Function; intros. applyClassifier2 H. applyClassifier2 H0.
  destruct H as [H[]], H0 as [H0[]]. rewrite H2,H4; auto.
Qed.

Corollary Corollary_sub_fun_b : ∀ f g x, x ∈ dom[f] -> x ∈ dom[g]
  -> (f \- g)[x] = f[x] - g[x].
Proof.
  intros. pose proof (Corollary_sub_fun_a f g). apply f_x_T; auto.
  apply Classifier2; auto.
Qed.

Corollary Corollary_sub_fun_c : ∀ f g, dom[(f \- g)] = dom[f] ∩ dom[g].
Proof.
  intros. apply AxiomI; split; intros. applyClassifier1 H. destruct H.
  applyClassifier2 H. destruct H as [H []]. apply Classifier1; auto. applyClassifier1 H. 
  destruct H. apply Classifier1. exists (f[z] - g[z]). apply Classifier2; auto.
Qed.

Definition mult_fun (f g : @set (@prod R R)) := (\{\ λ x y, x ∈ dom[f]
  /\ x ∈ dom[g] /\ y = f[x] * g[x] \}\).
Notation "f \* g" := (mult_fun f g) (at level 40, left associativity).
Definition mult'_fun (f : @set (@prod R R)) a := (\{\ λ x y, x ∈ dom[f]
  /\ y = f[x] * a \}\).
Notation "f \\* a" := (mult'_fun f a)(at level 40, left associativity).

Corollary Corollary_mult_fun_a : ∀ f g, Function (f \* g).
Proof.
  intros. unfold Function; intros. applyClassifier2 H. applyClassifier2 H0.
  destruct H as [H[]], H0 as [H0[]]. rewrite H2,H4; auto.
Qed.

Corollary Corollary_mult_fun_b : ∀ f g x, x ∈ dom[f] -> x ∈ dom[g]
  -> (f \* g)[x] = f[x] * g[x].
Proof.
  intros. pose proof (Corollary_mult_fun_a f g). apply f_x_T; auto.
  apply Classifier2; auto.
Qed.

Corollary Corollary_mult_fun_c : ∀ f g, dom[(f \* g)] = dom[f] ∩ dom[g].
Proof.
  intros. apply AxiomI; split; intros. applyClassifier1 H. destruct H.
  applyClassifier2 H. destruct H as [H []]. apply Classifier1; auto. applyClassifier1 H. 
  destruct H. apply Classifier1. exists (f[z] * g[z]). apply Classifier2; auto.
Qed.

Corollary Corollary_mult_fun_d : ∀ f a, dom[f \\* a] = dom[f].
Proof.
  intros. apply AxiomI; split; intros. applyClassifier1 H.
  destruct H as [y]. applyClassifier2 H; tauto. apply Classifier1. exists (f[z] * a).
  apply Classifier2; auto.
Qed.

Definition div_fun (f g : @set (@prod R R)) := (\{\ λ x y, x ∈ dom[f]
  /\ x ∈ dom[g] /\ g[x] <> 0 /\ y = f[x] / g[x] \}\).
Notation "f // g" := (div_fun f g)(at level 40, left associativity).
Definition div'_fun (f : @set (@prod R R)) a := (\{\ λ x y, x ∈ dom[f]
  /\ f[x] <> 0 /\ y = a / f[x] \}\).
Notation "a /// f" := (div'_fun f a)(at level 40, left associativity).

Corollary Corollary_div_fun_a : ∀ f g, Function (f // g).
Proof.
  intros. unfold Function; intros. applyClassifier2 H. applyClassifier2 H0.
  destruct H as [_[_[]]], H0 as [_[_[]]]. rewrite H1,H2; auto.
Qed.

Corollary Corollary_div_fun_b : ∀ f g x, x ∈ dom[f] -> x ∈ dom[g]
  -> g[x] <> 0 -> (f // g)[x] = f[x] / g[x].
Proof.
  intros. pose proof (Corollary_div_fun_a f g). apply f_x_T; auto.
  apply Classifier2; auto.
Qed.

Corollary Corollary_div_fun_c : ∀ f g, dom[(f // g)]
  = dom[f] ∩ dom[g] ∩ \{ λ u, g[u] <> 0 \}.
Proof.
  intros. apply AxiomI; split; intros. applyClassifier1 H. destruct H.
  applyClassifier2 H. destruct H as [H [H0 []]]. apply Classifier1; split; auto.
  apply Classifier1; split; auto. apply Classifier1; auto.
  applyClassifier1 H. destruct H. applyClassifier1 H0. destruct H0.
  applyClassifier1 H1. apply Classifier1. exists (f[z]/g[z]). apply Classifier2; auto.
Qed.

Corollary Corollary_div_fun_d : ∀ f, dom[1 /// f] = dom[f] ∩ \{ λ u, f[u] <> 0 \}.
Proof.
  intros. apply AxiomI; split; intros.
  - applyClassifier1 H. destruct H. applyClassifier2 H. destruct H as [H[H0[]]].
    apply Classifier1. split; auto.
  - applyClassifier1 H. destruct H. applyClassifier1 H0. apply Classifier1.
    exists (1/f[z]). apply Classifier2; auto.
Qed.

Corollary Corollary_div_fun_e : ∀ f, Function (1 /// f).
Proof.
  intros. red; intros. applyClassifier2 H. applyClassifier2 H0.
  destruct H as [_[]], H0 as [_[]]. subst; auto.
Qed.

Corollary Corollary_div_fun_f : ∀ f x, x ∈ dom[f] -> f[x] <> 0
  -> (1 /// f)[x] = 1/f[x].
Proof.
  intros. assert ([x, 1/f[x]] ∈ (1 /// f)). { apply Classifier2; auto. }
  assert ([x, (1 /// f)[x]] ∈ (1 /// f)).
  { apply x_fx_T. apply Corollary_div_fun_e. rewrite Corollary_div_fun_d.
    apply Classifier1; split; auto. }
  apply (Corollary_div_fun_e f x); auto.
Qed.




