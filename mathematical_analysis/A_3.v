(** A_3 *)
(* 函数极限 *)

(* 读入文件 *)
Require Export A_2.


(* 3.1 函数极限的概念 *)
(* x 趋于 +∞ 时的极限*)
Definition limit_pos_inf f A := Function f /\ (∃ a, \[a, +∞\) ⊂ dom[f] 
  /\ (∀ ε, ε > 0 -> ∃ M, M >= a /\ (∀ x, x > M -> ∣(f[x] - A)∣ < ε))).
(* x 趋于 -∞ 时的极限*)
Definition limit_neg_inf f A:= Function f /\ (∃ a, \(-∞, a\] ⊂ dom[f] 
  /\ (∀ ε, ε > 0 -> ∃ M, M <= a /\ (∀ x, x < M -> ∣(f[x] - A)∣< ε))).
(* x 趋于 ∞ 时的极限*)
Definition limit_inf f A := Function f /\ (∃ a, \(-∞, -a\] ∪ \[a, +∞\) ⊂ dom[f]
  /\ (∀ ε, ε > 0 -> ∃ M, M >= a /\ (∀ x, ∣x∣ > M -> ∣(f[x] - A)∣< ε))).

(* 函数极限的等价 *)
Fact limit_inf_equal : ∀ f A, 
  limit_inf f A <-> limit_pos_inf f A /\ limit_neg_inf f A.
Proof.
  intros f A. split; intro H0.
  - split.
    + destruct H0 as [H0 [a [H1 H2]]]. split; auto. exists a. split.
      * intros z I1. apply H1. apply Classifier1. right. apply I1.
      * intros ε H3. apply H2 in H3 as H4. destruct H4 as [M [H4 H5]].
        exists M. split; auto. intros x H6. apply H5.
        apply Rlt_le_trans with (r2 := x); auto. apply Abs_neg_pos.
    + destruct H0 as [H0 [a [H1 H2]]]. split; auto. exists (-a). split.
      * intros z I1. apply H1. apply Classifier1. left. apply I1.
      * intros ε H3. apply H2 in H3 as H4. destruct H4 as [M [H4 H5]]. 
        exists (-M). split; try lra. intros x H6. apply H5.
        assert (H7 : M < -x). lra. apply Rlt_le_trans with (r2 := -x); auto.
        rewrite Abs_eq_neg. apply Abs_neg_pos.
  - destruct H0 as [[H0 [a1 [H1 H2]]] [H3 [a2 [H4 H5]]]]. split; auto. 
    assert (H6 : ∃ a, a > a1 /\ -a < a2).
    { destruct (Rlt_or_le a1 (-a2)) as [I1 | I1].
      - exists (-a2 + 1). split; lra.
      - exists (a1 + 1). split; lra. }
    destruct H6 as [a [H6 H7]]. exists a. split.
    + intros z I1. applyClassifier1 I1. destruct I1 as [I1 | I1].
      * apply H4. applyClassifier1 I1. apply Classifier1. lra.
      * apply H1. applyClassifier1 I1. apply Classifier1. lra.
    + intros ε H8. apply H2 in H8 as H9. apply H5 in H8 as H10.
      destruct H9 as [M1 [H9 H11]]. destruct H10 as [M2 [H10 H12]].
      assert (H13 : ∃ M, M >= a /\ M >= M1 /\ (-M) <= M2).
      { destruct (Rlt_or_le M1 (-M2)) as [I2 | I2].
        - destruct (Rlt_or_le a (-M2)) as [I3 | I3].
          + exists (-M2). repeat split; lra.
          + exists a. repeat split; lra.
        - destruct (Rlt_or_le a M1) as [I3 | I3].
          + exists M1. repeat split; lra.
          + exists a. repeat split; lra. }
      destruct H13 as [M [H13 [H14 H15]]]. exists M. split; try lra.
      intros x H16. destruct (Rlt_or_le x 0) as [H17 | H17].
      * rewrite Abs_lt in H16; auto. apply H12. lra.
      * apply Rle_ge in H17. rewrite Abs_ge in H16; auto. apply H11. lra.
Qed.

(* x 趋于 x0 时的极限 *)
(* 函数极限的 ε-δ 定义 *)
Definition limit f x0 A := Function f /\ (∃ δ', δ' > 0 /\ Uº(x0; δ') ⊂ dom[f]
  /\ (∀ ε, ε > 0 -> ∃ δ, 0 < δ < δ' /\ (∀ x, 0 < ∣(x - x0)∣ < δ 
    -> ∣(f[x] - A)∣ < ε))).
(*Definition limitU f x0 A δ' := Function f /\ (δ' > 0 /\ Uº(x0; δ') ⊂ dom[f]
  /\ (∀ ε, ε > 0 -> ∃ δ, 0 < δ < δ' /\ (∀ x, 0 < ∣(x - x0)∣ < δ 
    -> ∣(f[x] - A)∣ < ε))).*)

(* 左极限 *)
Definition limit_neg f x0 A := Function f /\ (∃ δ', δ' > 0 /\ U-º(x0; δ') ⊂ dom[f]
  /\ (∀ ε, ε > 0 -> ∃ δ, 0 < δ < δ' /\ (∀ x, x0 - δ < x < x0 
    -> ∣(f[x] - A)∣ < ε))).
(* 右极限 *)
Definition limit_pos f x0 A := Function f /\ (∃ δ', δ' > 0 /\ U+º(x0; δ') ⊂ dom[f]
  /\ (∀ ε, ε > 0 -> ∃ δ, 0 < δ < δ' /\ (∀ x, x0 < x < x0 + δ 
    -> ∣(f[x] - A)∣ < ε))).

(* 定理3.1 *)
Theorem Theorem3_1 : ∀ f x0 A,
  limit f x0 A <-> (limit_pos f x0 A /\ limit_neg f x0 A).
Proof.
  intros f x0 A. split; intro H0.
  - destruct H0 as [H0 [δ' [H1 [H2 H3]]]]. split.
    + split; auto. exists δ'. split; auto. split.
      * intros z I1. apply H2. applyClassifier1 I1. apply Classifier1. split.
        -- apply Abs_not_eq_0. lra.
        -- apply Abs_R. split; lra.
      * intros ε H4. apply H3 in H4 as H5. destruct H5 as [δ [H5 H6]].
        exists δ. split; auto. intros x H7. apply H6. split.
        -- apply Abs_not_eq_0. lra.
        -- apply Abs_R. split; lra.
    + split; auto. exists δ'. split; auto. split.
      * intros z I1. apply H2. applyClassifier1 I1. apply Classifier1. split.
        -- apply Abs_not_eq_0. lra.
        -- apply Abs_R. split; lra.
      * intros ε H4. apply H3 in H4 as H5. destruct H5 as [δ [H5 H6]].
        exists δ. split; auto. intros x H7. apply H6. split.
        -- apply Abs_not_eq_0. lra.
        -- apply Abs_R. split; lra.
  - destruct H0 as [[H0 [δ0' [H1 [H2 H3]]]] [H4 [δ1' [H5 [H6 H7]]]]].
    split; auto. assert (H8 : ∃ δ', δ' > 0 /\ δ' <= δ0' /\ δ' <= δ1').
    { destruct (Rlt_or_le δ0' δ1') as [I1 | I1].
      - exists δ0'. split; lra.
      - exists δ1'. split; lra. }
    destruct H8 as [δ' [H8 [H9 H10]]]. exists δ'. split; auto. split.
    + intros z I1. applyClassifier1 I1. destruct I1 as [I1 I2].
      apply Abs_R in I2. destruct (Rlt_or_le (z - x0) 0) as [I3 | I3].
      * apply H6. apply Classifier1. split; lra.
      * apply H2. apply Classifier1. apply Abs_not_eq_0 in I1. split; lra.
    + intros ε H11. apply H3 in H11 as H12. apply H7 in H11 as H13.
      destruct H12 as [δ0 [H12 H14]]. destruct H13 as [δ1 [H13 H15]].
      assert (H16 : ∃ δ, 0 < δ < δ' /\ δ <= δ0 /\ δ <= δ1).
      { destruct (Rlt_or_le δ0 δ1) as [I1 | I1].
        - destruct (Rlt_or_le δ0 δ') as [I2 | I2].
          + exists δ0. split; lra.
          + exists (δ'/2). repeat split; lra.
        - destruct (Rlt_or_le δ1 δ') as [I2 | I2].
          + exists δ1. split; lra.
          + exists (δ'/2). repeat split; lra. }
      destruct H16 as [δ [H16 [H17 H18]]].
      exists δ. split; auto. intros x H19. destruct H19 as [H19 H20].
      apply Abs_not_eq_0 in H19. apply Abs_R in H20.
      destruct (Rlt_or_le (x - x0) 0) as [H21 | H21]; [apply H15 | apply H14]; lra.
Qed.

(* 3.2 函数极限的性质 *)
(* 定理3.2 唯一性 *)
Theorem Theorem3_2a : ∀ f x0 A B, limit f x0 A -> limit f x0 B -> A = B.
Proof.
  intros f x0 A B H0 H1.
  assert (H2 : ∀ ε : R, ε > 0 -> ∣(A - B)∣ < 2 * ε).
  { intros ε I1. destruct H0 as [H0 [δ1' [I2 [I3 I4]]]].
    destruct H1 as [H1 [δ2' [I5 [I6 I7]]]]. apply I4 in I1 as I8.
    apply I7 in I1 as I9. destruct I8 as [δ1 [I10 I11]].
    destruct I9 as [δ2 [I12 I13]].
    assert (I14 : ∃ x, 0 < ∣(x - x0)∣ < δ1 /\ 0 < ∣(x - x0)∣ < δ2).
    { destruct (Rlt_or_le δ1 δ2) as [J1 | J1].
      - exists (x0 + δ1/2). assert (J2 : x0 + δ1/2 - x0 = δ1/2). field.
        rewrite J2. assert (J3 : δ1/2 > 0). lra. rewrite Abs_gt; auto.
        repeat split; lra.
      - exists (x0 + δ2/2). assert (J2 : x0 + δ2/2 - x0 = δ2/2). field.
        rewrite J2. assert (J3 : δ2/2 > 0). lra. rewrite Abs_gt; auto.
        repeat split; lra. }
    destruct I14 as [x [I14 I15]]. apply I11 in I14.
    apply I13 in I15. generalize (Abs_minus_le (f[x] - A) (f[x] - B)).
    intro I16. assert (I17 : f[x] - A - (f[x] - B) = -(A - B)). field.
    rewrite I17 in I16. rewrite <- Abs_eq_neg in I16. lra. }
  apply NNPP. intro H3. assert (H4 : A-B <> 0). lra. apply Abs_not_eq_0 in H4.
  assert (H5 : ∣(A - B)∣/4 > 0). lra. apply H2 in H5. lra.
Qed.

Theorem Theorem3_2b : ∀ f x0 A B, limit_pos f x0 A -> limit_pos f x0 B -> A = B.
Proof.
  intros f x0 A B H0 H1.
  assert (H2 : ∀ ε, ε > 0 -> ∣(A - B)∣ < 2 * ε).
  { intros ε I1. destruct H0 as [H0 [δ1' [I2 [I3 I4]]]].
    destruct H1 as [H1 [δ2' [I5 [I6 I7]]]]. apply I4 in I1 as I8.
    apply I7 in I1 as I9. destruct I8 as [δ1 [I10 I11]].
    destruct I9 as [δ2 [I12 I13]].
    assert (I14 : ∃ x, x0 < x < x0 + δ1 /\ x0 < x < x0 + δ2).
    { destruct (Rlt_or_le δ1 δ2) as [J1 | J1].
      - exists (x0 + δ1/2). lra.
      - exists (x0 + δ2/2). lra. }
    destruct I14 as [x [I14 I15]]. apply I11 in I14. apply I13 in I15.
    generalize (Abs_minus_le (f[x] - A) (f[x] - B)). intro I16.
    assert (I17 : f[x] - A - (f[x] - B) = -(A - B)). field.
    rewrite I17 in I16. rewrite <- Abs_eq_neg in I16. lra. }
  apply NNPP. intro H3. assert (H4 : A - B <> 0). lra. apply Abs_not_eq_0 in H4.
  assert (H5 : ∣(A - B)∣/4 > 0). lra. apply H2 in H5. lra.
Qed.

Theorem Theorem3_2c : ∀ f x0 A B, limit_neg f x0 A -> limit_neg f x0 B -> A = B.
Proof.
  intros f x0 A B H0 H1.
  assert (H2 : ∀ ε, ε > 0 -> ∣(A - B)∣ < 2 * ε).
  { intros ε I1. destruct H0 as [H0 [δ1' [I2 [I3 I4]]]].
    destruct H1 as [H1 [δ2' [I5 [I6 I7]]]]. apply I4 in I1 as I8.
    apply I7 in I1 as I9. destruct I8 as [δ1 [I10 I11]].
    destruct I9 as [δ2 [I12 I13]].
    assert (I14 : ∃ x, x0 - δ1 < x < x0 /\ x0 - δ2 < x < x0).
    { destruct (Rlt_or_le δ1 δ2) as [J1 | J1].
      - exists (x0 - δ1/2). lra.
      - exists (x0 - δ2/2). lra. }
    destruct I14 as [x [I14 I15]]. apply I11 in I14.
    apply I13 in I15. generalize (Abs_minus_le (f[x] - A) (f[x] - B)).
    intro I16. assert (I17 : f[x] - A - (f[x] - B) = -(A - B)). field.
    rewrite I17 in I16. rewrite <- Abs_eq_neg in I16. lra. }
  apply NNPP. intro H3. assert (H4 : A-B <> 0). lra. apply Abs_not_eq_0 in H4.
  assert (H5 : ∣(A - B)∣ / 4 > 0). lra. apply H2 in H5. lra.
Qed.

(* 定理3.3 局部有界性 *)
Theorem Theorem3_3a : ∀ f x0, (∃ A, limit f x0 A) 
  -> ∃ δ, δ > 0 /\ DBoundedFun f Uº(x0; δ).
Proof.
  intros f x0 H0. destruct H0 as [A H0]. destruct H0 as [H0 [δ' [I2 [I3 I4]]]].
  generalize (I4 1 Rlt_0_1). intro I5. destruct I5 as [δ [I5 I6]]. exists δ.
  split; try lra. repeat split; auto.
  - intros x I7. applyClassifier1 I7. apply I3. apply Classifier1. lra.
  - exists (∣A∣ + 1). intros x I7. applyClassifier1 I7. apply I6 in I7.
    generalize (Abs_abs_minus' (f[x]) A). intro I8. lra.
Qed.

Theorem Theorem3_3b : ∀ f x0, (∃ A, limit f x0 A) -> (∃ δ, δ > 0
  /\ (∃ M, M > 0 /\ (∀ x, x ∈ Uº(x0; δ) -> ∣(f[x])∣ <= M))).
Proof.
  intros f x0 H0. destruct H0 as [A H0]. destruct H0 as [H0 [δ' [I2 [I3 I4]]]].
  generalize (I4 1 Rlt_0_1). intro I5. destruct I5 as [δ [I5 I6]]. exists δ.
  split; try lra. exists (∣A∣ + 1). split.
  - generalize (Abs_Rge0 A). intro I7. lra.
  - intros x I7. applyClassifier1 I7. apply I6 in I7.
    generalize (Abs_abs_minus' (f[x]) A). intro I8. lra.
Qed.

(* 定理3.4 局部保号性 *)
Theorem Theorem3_4a : ∀ f x0 A, limit f x0 A -> A > 0 -> (∀ r, 0 < r < A
  -> (∃ δ, δ > 0 /\ (∀ x, x ∈ Uº(x0; δ) -> 0 < r < f[x]))).
Proof.
  intros f x0 A H0 H1 r H2. destruct H0 as [H0 [δ' [H3 [H4 H5]]]].
  assert (H6 : A - r > 0). lra. apply H5 in H6 as H7.
  destruct H7 as [δ [H7 H8]]. exists δ. split; try lra.
  intros x H9. applyClassifier1 H9. apply H8 in H9 as H10. apply Abs_R in H10. lra.
Qed.

Theorem Theorem3_4b : ∀ f x0 A, limit f x0 A -> A < 0 -> (∀ r, 0 < r < -A 
  -> (∃ δ, δ > 0 /\ (∀ x, x ∈ Uº(x0; δ) -> f[x] < -r < 0))).
Proof.
  intros f x0 A H0 H1 r H2. destruct H0 as [H0 [δ' [H3 [H4 H5]]]].
  assert (H6 : -(A + r) > 0). lra. apply H5 in H6 as H7.
  destruct H7 as [δ [H7 H8]]. exists δ. split; try lra.
  intros x H9. applyClassifier1 H9. apply H8 in H9 as H10. apply Abs_R in H10. lra.
Qed.

(* 定理3.5 保不等式性 *)
Theorem Theorem3_5 : ∀ f g x0 A B, limit f x0 A -> limit g x0 B
  -> (∃ δ', δ' > 0 /\ (∀ x, x ∈ Uº(x0; δ') -> f[x] <= g[x])) -> A <= B.
Proof.
  intros f g x0 A B H0 H1 [δ' [H2 H10]].
  destruct H0 as [H0 [δ1' [H3 [H4 H5]]]]. destruct H1 as [H1 [δ2' [H6 [H7 H8]]]].
  assert (H9 : ∀ ε, ε > 0 -> A < (B + 2 * ε)).
  { intros ε I1. apply H5 in I1 as I2. destruct I2 as [δ1 [I2 I3]].
    apply H8 in I1 as I4. destruct I4 as [δ2 [I4 I5]].
    assert (I6 : ∃ δ, δ > 0 /\ δ <= δ' /\ δ <= δ1 /\ δ <= δ2).
    { destruct (Rlt_or_le δ' δ1) as [J1 | J1].
      - destruct (Rlt_or_le δ' δ2) as [J2 | J2];
          [exists δ' | exists δ2]; repeat split; lra.
      - destruct (Rlt_or_le δ1 δ2) as [J2 | J2];
          [exists δ1 | exists δ2]; repeat split; lra. }
    destruct I6 as [δ [I6 [I7 [I8 I9]]]].
    assert (I10 : ∃ x, x ∈ Uº(x0; δ') /\ 0 < ∣(x - x0)∣ < δ1
      /\ 0 < ∣(x - x0)∣ < δ2).
    { exists (x0 + δ/2). assert (J1 : x0 + δ/2 - x0 > 0). lra.
      rewrite Abs_gt; auto. split; [idtac | split]; try lra.
      apply Classifier1. rewrite Abs_gt; auto. lra. }
    destruct I10 as [x [I10 [I11 I12]]].
    apply H10 in I10. apply I3 in I11. apply I5 in I12.
    apply Abs_R in I11. apply Abs_R in I12. lra. }
  apply Rnot_gt_le. intro H11. assert (H12 : (A - B)/4 > 0). lra.
  apply H9 in H12 as H13. lra.
Qed.

(* 定理3.6 迫敛性 *)
Theorem Theorem3_6 : ∀ f g h x0 A, Function h -> limit f x0 A -> limit g x0 A 
  -> (∃ δ', δ' > 0 /\ Uº(x0; δ') ⊂ dom[h] /\ (∀ x, x ∈ Uº(x0; δ') 
  -> f[x] <= h[x] <= g[x])) -> limit h x0 A.
Proof.
  intros f g h x0 A H0 H1 H2 [δ' [H3 [H4 H5]]]. unfold limit. split; auto.
  exists δ'. repeat split; auto. intros ε H6.
  destruct H1 as [H1 [δ1' [H7 [H8 H9]]]], H2 as [H2 [δ2' [H10 [H11 H12]]]].
  apply H12 in H6 as H14. apply H9 in H6 as H13.
  destruct H13 as [δ1 [H15 H16]], H14 as [δ2 [H17 H18]].
  assert (H19 : ∃ δ, δ > 0 /\ δ < δ' /\ δ < δ1 /\ δ < δ2).
  { destruct (Rlt_or_le δ' δ1) as [J1 | J1].
    - destruct (Rlt_or_le δ' δ2) as [J2 | J2];
      [exists (δ'/2) | exists (δ2/2)]; repeat split; lra.
    - destruct (Rlt_or_le δ1 δ2) as [J2 | J2];
      [exists (δ1/2) | exists (δ2/2)]; repeat split; lra. }
  destruct H19 as [δ [H19 [H20 [H21 H22]]]]. exists δ. split; try lra.
  intros x H23. assert (H24 : x ∈ Uº(x0; δ')). { apply Classifier1. lra. }
  assert (H25 : 0 < ∣(x - x0)∣ < δ1). lra.
  assert (H26 : 0 < ∣(x - x0)∣ < δ2). lra.
  apply H5 in H24. apply H16 in H25. apply H18 in H26. apply Abs_R.
  apply Abs_R in H25. apply Abs_R in H26. lra.
Qed.

(* 定理3.7 四则运算 *)
Theorem Theorem3_7a : ∀ f g x0 A B, limit f x0 A -> limit g x0 B
  -> limit (f \+ g) x0 (A + B).
Proof.
  intros f g x0 A B [H0 [δ1' [H1 [H2 H3]]]] [H4 [δ2' [H5 [H6 H7]]]].
  assert (H8 : ∃ h, h = f \+ g).
  { exists \{\ λ x y, x ∈ dom[f] /\ x ∈ dom[g] /\ y = f[x] + g[x] \}\; auto. }
  destruct H8 as [h H8]. rewrite <- H8.
  assert (H9 : Function h).
  { unfold Function. rewrite H8. intros x y z I1 I2. applyClassifier2 I1.
    applyClassifier2 I2. destruct I2 as [I2 [I3 I4]]. rewrite I4. apply I1. }
  split; auto. assert (H10 : ∃ δ', δ' > 0 /\ δ' <= δ1' /\ δ' <= δ2').
  { destruct (Rlt_or_le δ1' δ2') as [I1 | I1]; [exists δ1' | exists δ2']; lra. }
  destruct H10 as [δ' [H10 [H11 H12]]]. exists δ'.
  assert (H13 : dom[h] = dom[f] ∩ dom[g]).
  { apply AxiomI. intro x; split; intro I1.
    - applyClassifier1 I1. destruct I1 as [y I1]. apply Classifier1. rewrite H8 in I1. 
      applyClassifier2 I1. split; apply I1.
    - apply Classifier1. exists (f[x] + g[x]). rewrite H8. apply Classifier2. 
      applyClassifier1 I1. destruct I1 as [I1 I2]. repeat split; auto. }
  split; auto. split.
  - intros z I1. applyClassifier1 I1. rewrite H13.
    destruct I1 as [I1 I2]. apply Classifier1. split.
    + apply H2. apply Classifier1. split; auto. lra.
    + apply H6. apply Classifier1. split; auto. lra.
  - intros ε H14. assert (H30 : ε/2 > 0). lra.
    apply H7 in H30 as H16; apply H3 in H30 as H15.
    destruct H15 as [δ1 [H15 H17]]. destruct H16 as [δ2 [H16 H18]].
    assert (H19 : ∃ δ, δ > 0 /\ δ < δ' /\ δ < δ1 /\ δ < δ2).
    { destruct (Rlt_or_le δ' δ1) as [J1 | J1].
      - destruct (Rlt_or_le δ' δ2) as [J2 | J2];
        [exists (δ'/2) | exists (δ2/2)]; repeat split; lra.
      - destruct (Rlt_or_le δ1 δ2) as [J2 | J2];
        [exists (δ1/2) | exists (δ2/2)]; repeat split; lra. }
    destruct H19 as [δ [H19 [H20 [H21 H22]]]]. exists δ. split; try lra.
    intros x H23. assert (H24 : 0 < ∣(x - x0)∣ < δ1). lra.
    assert (H25 : 0 < ∣(x - x0)∣ < δ2). lra. apply H17 in H24. apply H18 in H25.
    assert (H26 : h[x] = f[x] + g[x]).
    { apply f_x_T; auto. rewrite H8. apply Classifier2. repeat split; auto.
      - apply H2. apply Classifier1. lra.
      - apply H6. apply Classifier1. lra. }
    rewrite H26. generalize (Abs_plus_le (f[x] - A) (g[x] - B)). intro H27.
    assert (H28 : f[x] + g[x] - (A + B) = f[x] - A + (g[x] - B)). field.
    rewrite H28. lra.
Qed.

Lemma Lemma3_7b : ∀ f x0 A, limit f x0 A -> limit (f \\* (-1)) x0 (-A).
Proof.
  intros f x0 A H0. destruct H0 as [H0 [δ' [H2 [H3 H4]]]].
  assert (H5 : Function (f \\* -1)).
  { unfold Function. intros x y z I1 I2. applyClassifier2 I1. applyClassifier2 I2.
    destruct I2 as [I2 I3]. rewrite I3. apply I1. }
  unfold limit. split; auto. exists (δ').
  assert (H6 : Uº(x0; δ') ⊂ dom[f \\* -1]).
  { intros x I1. apply Classifier1. exists (-f[x]).
    apply Classifier2. split; auto. field. }
  repeat split; auto. intros ε H7. apply H4 in H7 as H8. 
  destruct H8 as [δ [H9 H10]]. exists δ. split; auto. intros x H11. 
  apply H10 in H11 as H12. apply Abs_R. apply Abs_R in H12.
  assert (H13 : (f \\* -1)[x] = -f[x]).
  { apply f_x_T; auto. apply Classifier2. split; try field.
    apply H3. apply Classifier1. lra. } rewrite H13. lra.
Qed.

Theorem Theorem3_7b : ∀ f g x0 A B, limit f x0 A -> limit g x0 B
  -> limit (f \- g) x0 (A - B).
Proof.
  intros f g x0 A B H0 H1. apply Lemma3_7b in H1 as H2.
  assert (H3 : (f \- g) = (f \+ (g \\* -1))).
  { apply AxiomI. assert (H3 : ∀ x, x ∈ dom[g] -> (g \\* -1)[x] = -g[x]).
    { intros x J1. apply f_x_T; try apply H2. apply Classifier2.
      split; [auto | field]. } intro z; split; intro I1.
    - applyClassifier1 I1. destruct I1 as [x [y [I1 I2]]]. rewrite I1.
      apply Classifier2. destruct I2 as [I2 [I3 I4]]. split; auto. split.
      + apply Classifier1. exists (-g[x]). apply Classifier2. split; [auto | field].
      + rewrite H3; auto.
    - applyClassifier1 I1. destruct I1 as [x [y [I1 I2]]]. rewrite I1.
      apply Classifier2. destruct I2 as [I2 [I3 I4]]. split; auto.
      assert (I5 : x ∈ dom[g]).
      { applyClassifier1 I3. destruct I3 as [y' I3]. applyClassifier2 I3. apply I3. }
      split; auto. rewrite H3 in I4; auto. }
  rewrite H3. unfold Rminus. apply Theorem3_7a; auto.
Qed.

Theorem Theorem3_7c : ∀ f g x0 A B, limit f x0 A -> limit g x0 B
  -> limit (f \* g) x0 (A * B).
Proof.
  intros f g x0 A B [H0 [δ1' [H1 [H2 H3]]]] [H4 [δ2' [H5 [H6 H7]]]].
  assert (H14 : (∃ δ3', δ3' > 0 /\ (∃ M, M > 0 /\ (∀ x, x ∈ Uº(x0; δ3')
    -> ∣(g[x])∣ <= M)))).
  { apply Theorem3_3b. exists B. split; auto. exists δ2'. repeat split; auto. }
  destruct H14 as [δ3' [H14 H15]].
  assert (H8 : ∃ δ', δ' > 0 /\ δ' <= δ1' /\ δ' <= δ2' /\ δ' <= δ3').
  { destruct (Rlt_or_le δ1' δ2') as [J1 | J1].
    - destruct (Rlt_or_le δ1' δ3') as [J2 | J2];
      [exists (δ1'/2) | exists (δ3'/2)]; repeat split; lra.
    - destruct (Rlt_or_le δ2' δ3') as [J2 | J2];
      [exists (δ2'/2) | exists (δ3'/2)]; repeat split; lra. }
  destruct H8 as [δ' [H8 [H9 [H10 H11]]]].
  assert (H12 : Function (f \* g)).
  { unfold Function. intros x y z I1 I2. applyClassifier2 I1. applyClassifier2 I2.
    destruct I2 as [I2 [I3 I4]]. rewrite I4. apply I1. }
  split; auto. exists (δ'). split; auto.
  assert (H13 : Uº(x0; δ') ⊂ dom[f \* g]).
  { intros x I1. apply Classifier1. exists (f[x] * g[x]). apply Classifier2. 
    repeat split; [apply H2 | apply H6]; apply Classifier1; applyClassifier1 I1; lra. }
  split; auto. destruct H15 as [M H15]. intros ε H16. destruct H15 as [H15 H17].
  generalize (Abs_Rge0 A). intro H18.
  assert (H19 : ε/(M + ∣A∣) > 0).
  { apply  Rmult_gt_0_compat; auto. apply Rinv_0_lt_compat. lra. }
  apply H7 in H19 as H21. apply H3 in H19 as H20.
  destruct H20 as [δ1 [H22 H23]]. destruct H21 as [δ2 [H24 H25]].
  assert (H26 : ∃ δ, δ > 0 /\ δ <= δ1 /\ δ <= δ2 /\ δ < δ').
  { destruct (Rlt_or_le δ1 δ2) as [J1 | J1].
    - destruct (Rlt_or_le δ1 δ') as [J2 | J2];
      [exists (δ1/2) | exists (δ'/2)]; repeat split; lra.
    - destruct (Rlt_or_le δ2 δ') as [J2 | J2];
      [exists (δ2/2) | exists (δ'/2)]; repeat split; lra. }
  destruct H26 as [δ [H26 [H27 [H28 H29]]]].
  exists δ. split; [lra | idtac]. intros x H30.
  assert (H31 : 0 < ∣(x - x0)∣ < δ1). lra.
  assert (H32 : 0 < ∣(x - x0)∣ < δ2). lra.
  assert (H33 : (f \* g)[x] = f[x] * g[x]).
  { apply f_x_T; auto. apply Classifier2.
    repeat split; [apply H2 | apply H6]; apply Classifier1; lra. }
  rewrite H33. clear H33. apply H23 in H31 as H33. apply H25 in H32 as H34.
  assert (H35 : f[x]*g[x] - A*B = (f[x] - A)*g[x] + A*(g[x] - B)). field.
  rewrite H35. generalize (Abs_plus_le ((f[x] - A)*g[x]) (A*(g[x] - B))).
  intro H36. generalize (Abs_mult (f[x] - A) (g[x])). intro H37. 
  generalize (Abs_mult A (g[x] - B)). intro H38. rewrite H37 in H36.
  rewrite H38 in H36. apply Rle_lt_trans
  with (r2 := ∣(f[x] - A)∣ * ∣(g[x])∣ + ∣A∣ * ∣(g[x] - B)∣); auto.
  assert (H39 : ∣(g[x])∣ <= M). { apply H17. apply Classifier1. lra. }
  assert (H40 : ε = (ε/(M + ∣A∣)) * M + ∣A∣ * (ε/(M + ∣A∣))).
  field; lra. rewrite H40. apply Rplus_lt_le_compat.
  - destruct H39 as [H39 | H39].
    + apply Rmult_le_0_lt_compat; auto; apply Rge_le; apply Abs_Rge0.
    + rewrite H39. apply Rmult_lt_compat_r; auto.
  - apply Rmult_le_compat_l; lra.
Qed.

Lemma Lemma3_7d : ∀ f x0 A, limit f x0 A -> A <> 0 -> limit (1 /// f) x0 (/A).
Proof.
  intros f x0 A H0 H1.
  assert (H2 : ∃ δ1', δ1' > 0 /\ (∀ x, x ∈ Uº(x0; δ1') -> f[x] <> 0)).
  { apply Rdichotomy in H1 as I1. destruct I1 as [I1 | I1].
    - generalize (Theorem3_4b f x0 A H0 I1). intro I2.
      assert (I3 : 0 < -A/2 < -A). lra. apply I2 in I3 as I4.
      destruct I4 as [δ [I4 I5]]. exists δ. split; auto. intros x I6.
      apply I5 in I6. lra.
    - generalize (Theorem3_4a f x0 A H0 I1). intro I2.
      assert (I3 : 0 < A/2 < A). lra. apply I2 in I3 as I4.
      destruct I4 as [δ [I4 I5]]. exists δ. split; auto.
      intros x I6. apply I5 in I6. lra. }
  destruct H2 as [δ1' [H2 H3]].
  assert (H4 : ∃ δ1, δ1 > 0 /\ (∀ x, x ∈ Uº(x0; δ1) -> ∣(f[x])∣ > ∣A∣/2)).
  { apply Rdichotomy in H1 as I1. destruct I1 as [I1 | I1].
    - generalize (Theorem3_4b f x0 A H0 I1). intro I2. 
      assert (I3 : 0 < -A/2 < -A). lra. apply I2 in I3 as I4.
      destruct I4 as [δ1 [I4 I5]]. exists δ1. split; auto. intros z I6.
      apply I5 in I6. assert (I7 : f[z] < 0). lra.
      repeat rewrite Abs_lt; auto. lra.
    - generalize (Theorem3_4a f x0 A H0 I1). intro I2.
      assert (I3 : 0 < A/2 < A). lra. apply I2 in I3 as I4.
      destruct I4 as [δ1 [I4 I5]]. exists δ1. split; auto. intros z I6.
      apply I5 in I6. assert (I7 : f[z] > 0). lra.
      repeat rewrite Abs_gt; auto. lra. }
  destruct H4 as [δ1 [H5 H6]].
  assert (H7 : ∀ ε, ε > 0 -> ∃ δ, δ > 0 /\ Uº(x0; δ) ⊂ dom[ f]
    /\ (∀ x, x ∈ Uº(x0; δ) -> ∣(1/f[x] - 1/A)∣ < (2 * ε)/(A * A))).
  { intros ε I1. destruct H0 as [H0 [δ2' [I2 [I3 I4]]]]. apply I4 in I1 as I5.
    destruct I5 as [δ2 [I6 I7]].
    assert (I8 : ∃ δ, δ > 0 /\ δ < δ1' /\ δ < δ1 /\ δ < δ2).
    { destruct (Rlt_or_le δ1' δ1) as [J1 | J1].
      - destruct (Rlt_or_le δ1' δ2) as [J2 | J2];
        [exists (δ1'/2) | exists (δ2/2)]; repeat split; lra.
      - destruct (Rlt_or_le δ1 δ2) as [J2 | J2];
        [exists (δ1/2) | exists (δ2/2)]; repeat split; lra. }
    destruct I8 as [δ [I8 [I9 [I10 I11]]]]. exists δ.
    assert (I12 : Uº(x0; δ) ⊂ dom[f]).
    { intros x J1. apply I3. apply Classifier1. applyClassifier1 J1. lra. }
    repeat split; auto. intros x I13. assert (I14 : f[x] <> 0).
    { apply H3. apply Classifier1. applyClassifier1 I13. lra. }
    assert (I15 : 1/f[x] - 1/A = -((f[x] - A)/(f[x] * A))).
    { field. split; auto. } rewrite I15. rewrite <- Abs_eq_neg.
    assert (I16 : f[x] * A <> 0).
    { apply Rmult_integral_contrapositive_currified; auto. }
    rewrite Abs_div; auto. rewrite Abs_mult. clear I15.
    assert (I17 : ∣(f[x])∣ > ∣A∣/2).
    { apply H6. apply Classifier1. applyClassifier1 I13. lra. }
    assert (I18 : ∣A∣ > 0). { apply Abs_not_eq_0. apply H1. }
    assert (I19 : (∣(f[x])∣ * ∣A∣) > (∣A∣/2) * ∣A∣).
    { apply Rmult_gt_compat_r; auto. }
    assert (I20 : ∣A∣/2 * ∣A∣ = (A * A)/2).
    { apply Rdichotomy in H1. destruct H1 as [H1 | H1].
      - rewrite Abs_lt; auto. field.
      - rewrite Abs_gt; auto. field. }
    assert (I21 : 0 < (∣A∣/2 * ∣A∣) * (∣(f[x])∣ * ∣A∣)).
    { apply Rmult_gt_0_compat; apply Rmult_gt_0_compat; lra. }
    apply Rinv_lt_contravar in I19; auto. clear I21. rewrite I20 in I19.
    assert (I21 : 0 <= ∣(f[x] - A)∣). { apply Rge_le. apply Abs_Rge0. }
    apply Rlt_le in I19 as I22. 
    apply Rmult_le_compat_l with (r := ∣(f[x] - A)∣) in I22; auto.
    assert (I23 : (A * A)/2 > 0). { rewrite <- I20. apply Rmult_gt_0_compat; lra. }
    apply Rle_lt_trans with (r2 := ∣(f[x] - A)∣ * /((A * A)/2)); auto.
    assert (I24 : ∣(f[x] - A)∣ < ε). { apply I7. applyClassifier1 I13. lra. }
    apply Rinv_0_lt_compat in I23.
    apply Rmult_lt_compat_r with (r := /((A * A)/2)) in I24; auto.
    assert (I25 : ε * /((A * A)/2) = (2 * ε)/(A * A)). { field; auto. }
    rewrite <- I25. assumption. }
  unfold limit. assert (H8 : Function (1 /// f)).
  { unfold Function. intros x y z I1 I2. applyClassifier2 I1. applyClassifier2 I2.
    destruct I2 as [I2 [I3 I4]]. rewrite I4. apply I1. }
  destruct H0 as [H0 [δ2' [H9 [H10 H11]]]].
  assert (H12 : ∃ δ', δ' > 0 /\ δ' <= δ1' /\ δ' <= δ2').
  { destruct (Rlt_or_le δ1' δ2') as [I1 | I1]; [exists δ1' | exists δ2']; lra. }
  destruct H12 as [δ' [H13 [H14 H15]]]. split; auto. exists δ'. repeat split; auto.
  - intros x I1. apply Classifier1. exists (1/f[x]). apply Classifier2. repeat split;
    [apply H10 | apply H3]; apply Classifier1; applyClassifier1 I1; lra.
  - intros ε H16.
    assert (H17 : (A * A * ε)/2 > 0).
    { assert (I1 : (A * A) > 0).
      { apply Rdichotomy in H1. destruct H1 as [H1 | H1].
        - apply Ropp_gt_lt_0_contravar in H1 as I1.
          assert (I2 : (-A) * (-A) = A * A). field.
          rewrite <- I2. apply Rmult_gt_0_compat; auto.
        - apply Rmult_gt_0_compat; auto. }
      assert (I2 : (A * A * ε)/2 = (A * A) * (ε/2)).
      field. rewrite I2. apply Rmult_gt_0_compat; auto. lra. }
    apply H7 in H17 as H18. destruct H18 as [δ2 [H18 [H19 H20]]].
    assert (H21 : ∃ δ, δ > 0 /\ δ < δ2 /\ δ < δ').
    { destruct (Rlt_or_le δ2 δ') as [I1 | I1];
      [exists (δ2/2) | exists (δ'/2)]; lra. }
    destruct H21 as [δ [H21 [H22 H23]]]. exists δ. split; try lra. intros x H24.
    assert (H25 : (1 /// f)[x] = 1/f[x]).
    { apply f_x_T; auto. apply Classifier2. repeat split; auto.
      - apply H10. apply Classifier1. lra.
      - apply H3. apply Classifier1. lra. } rewrite H25.
    assert (H26 : (2 * ((A * A * ε)/2)) / (A * A) = ε). { field; auto. }
    rewrite H26 in H20. assert (H27 : /A = 1/A). field; auto. rewrite H27.
    apply H20. apply Classifier1. lra.
Qed.

Theorem Theorem3_7d : ∀ f g x0 A B, limit f x0 A -> limit g x0 B
  -> B <> 0 -> limit (f // g) x0 (A/B).
Proof.
  intros f g x0 A B H0 H1 H2. apply Lemma3_7d in H1 as H3; auto.
  assert (H4 : f // g = f \* (1 /// g)).
  { apply AxiomI. 
    assert (I6 : ∀ x, x ∈ dom[g] -> g[x] <> 0 -> (1 /// g)[x] = /g[x]).
    { intros x J1 J2. apply f_x_T; try apply H3. apply Classifier2.
      repeat split; auto. field. auto. }
    intro z; split; intro I1.
    - applyClassifier1 I1. destruct I1 as [x [y [I1 [I2 [I3 [I4 I5]]]]]].
      rewrite I1. apply Classifier2. repeat split; auto.
      + apply Classifier1. exists (1/g[x]). apply Classifier2. repeat split; auto.
      + rewrite I6; auto.
    - applyClassifier1 I1. destruct I1 as [x [y [I1 [I2 [I3 I4]]]]]. rewrite I1.
      apply Classifier2. split; auto. applyClassifier1 I3. destruct I3 as [y' I3].
      applyClassifier2 I3. destruct I3 as [I3 [I5 I7]]. rewrite I6 in I4; auto. }
  rewrite H4. apply Theorem3_7c; auto.
Qed.

(* 3.3 函数极限存在的条件 *)
(* 定理3.8 归结原则: Heine定理 *)
Theorem Theorem3_8 : ∀ f x0 δ' A, Function f -> δ' > 0 -> Uº(x0; δ') ⊂ dom[f] 
  -> limit f x0 A <-> (∀ x, IsSeq x -> ran[x] ⊂ Uº(x0; δ') -> limit_seq x x0
  -> limit_seq \{\ λ n v, v = f[x[n]] \}\ A).
Proof.
  intros f x0 δ' A H0 H1 H2. split.
  - intro H3. destruct H3 as [H3 [δ1' [H4 [H5 H6]]]].
    intros x H7 H8 H9. unfold limit_seq.
    assert (H10 : IsSeq \{\ λ n v, v = f[x[n]] \}\ ).
    { unfold IsSeq. split.
      - unfold Function. intros x1 y1 z1 I1 I2.
        applyClassifier2 I1. applyClassifier2 I2. rewrite I2; auto.
      - apply AxiomI. intro z; split; intro I1.
        + apply Classifier1. reflexivity.
        + apply Classifier1. exists (f[x[z]]). apply Classifier2. reflexivity. }
    split; auto. intros ε H11. apply H6 in H11 as H12.
    destruct H12 as [δ [[H12 H13] H14]]. apply H9 in H12 as H15.
    destruct H15 as [N H15]. exists N. intros n H16. apply H15 in H16 as H17.
    assert (H18 : ∣(x[n] - x0)∣ > 0).
    { assert (I2 : x[n] ∈ ran[x]).
      { destruct H7 as [I2 I3]. apply fx_ran_T; auto.
        rewrite I3. apply Classifier1. reflexivity. }
      apply H8 in I2. applyClassifier1 I2. apply I2. }
    assert (H19 : 0 < ∣(x[n] - x0)∣ < δ). lra. apply H14 in H19.
    assert (H20 : (\{\ λ n0 v, v = f[x[n0]] \}\)[n] = f[x[n]]).
    { apply f_x_T; try apply H10. apply Classifier2. reflexivity. }
    rewrite H20. apply H19.
  - intro H3. apply NNPP. intro H4. unfold limit in H4. apply not_and_or in H4.
    destruct H4 as [H4 | H4]; auto. apply not_ex_all_not with (n := δ') in H4.
    apply not_and_or in H4; destruct H4 as [H4 | H4]; auto.
    apply not_and_or in H4; destruct H4 as [H4 | H4]; auto.
    apply not_all_ex_not in H4. destruct H4 as [ε0 H4].
    apply imply_to_and in H4. destruct H4 as [H4 H5].
    assert (H6 : ∀ δ, ~ (0 < δ < δ'
      /\ (∀ x, 0 < ∣(x - x0)∣ < δ -> ∣(f[x] - A)∣ < ε0))).
    { apply not_ex_all_not; apply H5. }
    assert (H7 : ∃ x, x
      = \{\ λ n v, v = c \{ λ u, 0 < ∣(u - x0)∣ < δ'/(INR (n + 2))
        /\ ∣(f[u] - A)∣ >= ε0 \} \}\).
    { exists (\{\ λ n v, v = c \{ λ u, 0 < ∣(u - x0)∣ < δ'/(INR (n + 2))
      /\ ∣(f[u] - A)∣ >= ε0 \} \}\); reflexivity. } destruct H7 as [x H7].
    assert (H8 : IsSeq x).
    { split.
      - unfold Function. rewrite H7. intros x1 y1 z1 I1 I2.
        applyClassifier2 I1; applyClassifier2 I2. rewrite I2; apply I1.
      - apply AxiomI. intro z; split; intro I1.
        + apply Classifier1. reflexivity.
        + apply Classifier1. exists (c \{ λ u, 0 < ∣(u - x0)∣
            < δ'/(INR (z + 2)) /\ ∣(f[u] - A)∣ >= ε0 \}).
          rewrite H7. apply Classifier2. reflexivity. }
    generalize H8. intro H9. destruct H9 as [H9 H10].
    assert (H11 : ∀ δ, 0 < δ < δ'
      -> NotEmpty \{ λ u, 0 < ∣(u - x0)∣ < δ /\ ∣(f[u] - A)∣ >= ε0 \}).
    { intros δ I1. generalize (H6 δ). intro I2. apply not_and_or in I2.
      destruct I2 as [I2 | I2]; [exfalso; auto | idtac].
      apply not_all_ex_not in I2. destruct I2 as [u I2].
      apply imply_to_and in I2. destruct I2 as [I2 I3].
      exists u. apply Classifier1. split; auto; lra. }
    assert (H12 : ∀ n, 0 < δ'/(INR (n + 2)) < δ').
    { intro n. assert (I1 : 2 <= INR (n + 2)).
      { assert (I1 : 2 = INR (2%nat)). { simpl. field. }
        rewrite I1. apply le_INR. rewrite Nat.add_comm. apply Nat.le_add_r. }
      assert (I2 : INR (n + 2) > 1). lra.
      assert (I3 : 0 < 1 * (INR (n + 2))). lra.
      apply Rinv_lt_contravar in I2; auto.
      apply Rmult_lt_compat_l with (r := δ') in I2; auto.
      assert (I4 : δ' * /1 = δ'). field. rewrite I4 in I2. split; auto.
      apply Rmult_gt_0_compat; auto. apply Rinv_0_lt_compat. lra. }
    assert (H13 : ran[x] ⊂ Uº(x0; δ')).
    { intros u I1. applyClassifier1 I1. destruct I1 as [n I1].
      rewrite H7 in I1. applyClassifier2 I1. generalize (H12 n). intro I2.
      apply H11 in I2 as I3. apply Axiomc in I3. rewrite <- I1 in I3.
      applyClassifier1 I3. destruct I3 as [I3 I4]. apply Classifier1. lra. }
    assert (H14 : limit_seq x x0).
    { split; auto. intros ε I1. assert (I2 : ∃ N, δ'/(INR (N + 2)) < ε).
      { generalize (Archimedes ε δ' I1 H1). intros [N J1]. exists N.
        rewrite Rmult_comm in J1. assert (J2 : INR (N + 2) > INR N).
        { apply lt_INR. apply Nat.lt_add_pos_r. apply Nat.lt_0_2. }
        generalize (pos_INR N). intro J3. assert (J4 : 0 < INR (N + 2)). lra.
        apply Rmult_lt_compat_l with (r := ε) in J2; auto.
        assert (J5 : δ' < ε * INR (N + 2)). lra.
        apply Rinv_0_lt_compat in J4 as J6.
        apply Rmult_lt_compat_r with (r := / INR (N + 2)) in J5; auto.
        assert (J7 : ε * INR (N + 2) * /INR (N + 2) = ε). field. lra.
        rewrite J7 in J5. apply J5. }
      destruct I2 as [N I2]. exists N. intros n I3.
      assert (I4 : n ∈ dom[x]). { rewrite H10. apply Classifier1. reflexivity. }
      apply x_fx_T in I4 as I5; auto. pattern x at 2 in I5.
      rewrite H7 in I5. applyClassifier2 I5. generalize (H12 n). intro I6.
      apply H11 in I6 as I7. apply Axiomc in I7. rewrite <- I5 in I7.
      applyClassifier1 I7. destruct I7 as [I7 I8].
      assert (I9 : δ'/(INR (n + 2)) < δ'/(INR (N + 2))).
      { apply Rmult_lt_compat_l; auto. assert (I9 : INR (n + 2) > INR (N + 2)).
        { apply lt_INR. lia. }
        generalize (pos_INR N). intro I10. assert (I11 : INR (N + 2) > INR N).
        { apply lt_INR. apply Nat.lt_add_pos_r. apply Nat.lt_0_2. }
        apply Rinv_lt_contravar; auto. apply Rmult_gt_0_compat; lra. } lra. }
    generalize (H3 x H8 H13 H14). intros [H15 H16].
    generalize (H16 ε0 H4). intros [N H17].
    assert (H18 : (S N) ∈ dom[x]). { rewrite H10. apply Classifier1. reflexivity. }
    apply x_fx_T in H18 as H19; auto. pattern x at 2 in H19.
    rewrite H7 in H19. apply -> Classifier2 in H19. lazy beta in H19.
    generalize (H12 (S N)). intro H20. apply H11 in H20. apply Axiomc in H20.
    rewrite <- H19 in H20. apply -> Classifier1 in H20. lazy beta in H20.
    destruct H20 as [H20 H21]. assert (S N > N)%nat. lia. apply H17 in H.
    assert (H23 : (\{\ λ n v, v = f[x[n]] \}\)[S N] = f[x[S N]]).
    { apply f_x_T; try apply H15. apply Classifier2. reflexivity. }
    rewrite H23 in H. lra.
Qed.

Corollary Corollary3_8a : ∀ f x0 δ' A, Function f -> δ' > 0 -> U+º(x0; δ') ⊂ dom[f] 
  -> limit_pos f x0 A -> ∀ x, IsSeq x -> ran[x] ⊂ U+º(x0; δ') -> limit_seq x x0
  -> limit_seq \{\ λ n v, v = f[x[n]] \}\ A.
Proof.
  intros f x0 δ' A H0 H1 H2 H3. destruct H3 as [H3 [δ1' [H4 [H5 H6]]]].
  intros x H7 H8 H9. unfold limit_seq.
  assert (H10 : IsSeq \{\ λ n v, v = f[x[n]] \}\ ).
  { unfold IsSeq. split.
    - unfold Function. intros x1 y1 z1 I1 I2.
      applyClassifier2 I1. applyClassifier2 I2. rewrite I2; auto.
    - apply AxiomI. intro z; split; intro I1.
      + apply Classifier1. reflexivity.
      + apply Classifier1. exists (f[x[z]]). apply Classifier2. reflexivity. }
  split; auto. intros ε H11. apply H6 in H11 as H12.
  destruct H12 as [δ [[H12 H13] H14]]. apply H9 in H12 as H15.
  destruct H15 as [N H15]. exists N. intros n H16. apply H15 in H16 as H17.
  assert (H18 : x0 < x[n]).
  { assert (I2 : x[n] ∈ ran[x]).
    { destruct H7 as [I2 I3]. apply fx_ran_T; auto.
      rewrite I3. apply Classifier1. reflexivity. }
    apply H8 in I2. applyClassifier1 I2. lra. }
  apply Abs_R in H17. assert (H19 : x0 < x[n] < x0 + δ). lra.
  apply H14 in H19. assert (H20 : (\{\ λ n0 v, v = f[x[n0]] \}\)[n] = f[x[n]]).
  { apply f_x_T; try apply H10. apply Classifier2. reflexivity. }
  rewrite H20. apply H19.
Qed.

Corollary Corollary3_8b : ∀ f x0 δ' A, Function f -> δ' > 0 -> U-º(x0; δ') ⊂ dom[f] 
  -> limit_neg f x0 A -> ∀ x, IsSeq x -> ran[x] ⊂ U-º(x0; δ') -> limit_seq x x0
  -> limit_seq \{\ λ n v, v = f[x[n]] \}\ A.
Proof.
  intros f x0 δ' A H0 H1 H2 H3. destruct H3 as [H3 [δ1' [H4 [H5 H6]]]].
  intros x H7 H8 H9. unfold limit_seq.
  assert (H10 : IsSeq \{\ λ n v, v = f[x[n]] \}\).
  { unfold IsSeq. split.
    - unfold Function. intros x1 y1 z1 I1 I2.
      applyClassifier2 I1. applyClassifier2 I2. rewrite I2; auto.
    - apply AxiomI. intro z; split; intro I1.
      + apply Classifier1. reflexivity.
      + apply Classifier1. exists (f[x[z]]). apply Classifier2. reflexivity. }
  split; auto. intros ε H11. apply H6 in H11 as H12.
  destruct H12 as [δ [[H12 H13] H14]]. apply H9 in H12 as H15.
  destruct H15 as [N H15]. exists N. intros n H16. apply H15 in H16 as H17.
  assert (H18 : x[n] < x0).
  { assert (I2 : x[n] ∈ ran[x]).
    { destruct H7 as [I2 I3]. apply fx_ran_T; auto.
      rewrite I3. apply Classifier1. reflexivity. }
    apply H8 in I2. applyClassifier1 I2. lra. }
  apply Abs_R in H17. assert (H19 : x0 - δ < x[n] < x0). lra.
  apply H14 in H19. assert (H20 : (\{\ λ n0 v, v = f[x[n0]] \}\)[n] = f[x[n]]).
  { apply f_x_T; try apply H10. apply Classifier2. reflexivity. }
  rewrite H20. apply H19.
Qed.

Theorem Theorem3_8' : ∀ f x0 A, Function f -> x0 ∈ dom[f] -> f[x0] = A
  -> limit f x0 A -> ∀ x, IsSeq x -> ran[x] ⊂ dom[f] -> limit_seq x x0
  -> limit_seq \{\ λ n v, v = f[x[n]] \}\ A.
Proof.
  intros f x0 A H0 H1 H2 H3. destruct H3 as [H3 [δ1' [H4 [H5 H6]]]].
  intros x H7 H8 H9. unfold limit_seq.
  assert (H10 : IsSeq \{\ λ n v, v = f[x[n]] \}\ ).
  { unfold IsSeq. split.
    - unfold Function. intros x1 y1 z1 I1 I2. applyClassifier2 I1.
      applyClassifier2 I2. rewrite I2; auto.
    - apply AxiomI. intro z; split; intro I1.
      + apply Classifier1. reflexivity.
      + apply Classifier1. exists (f[x[z]]). apply Classifier2. reflexivity. }
  split; auto. intros ε H11. apply H6 in H11 as H12. 
  destruct H12 as [δ [[H12 H13] H14]]. apply H9 in H12 as H15.
  destruct H15 as [N H15]. exists N. intros n H16. apply H15 in H16 as H17.
  assert (H18 : ∣(x[n] - x0)∣ >= 0). { apply Abs_Rge0. }
  assert (H19 : 0 <= ∣(x[n] - x0)∣ < δ). lra.
  assert (H21 : ∣(f[x[n]] - A)∣ < ε).
  { assert (I1 : 0 < ∣(x[n] - x0)∣ < δ \/ ∣(x[n] - x0)∣ = 0).
    lra. destruct I1 as [I1 | I1].
    - apply H14 in I1. assumption.
    - assert (I2 : x[n] - x0 = 0).
      { apply NNPP. intro J1. apply Abs_not_eq_0 in J1. lra. }
      apply Rminus_diag_uniq_sym in I2. rewrite <- I2. rewrite H2.
      unfold Rminus. rewrite Rplus_opp_r. rewrite Abs_ge; lra. }
  assert (H20 : (\{\ λ n0 v, v = f[x[n0]] \}\)[n] = f[x[n]]).
  { apply f_x_T; try apply H10. apply Classifier2. reflexivity. }
  rewrite H20. assumption.
Qed.

Corollary Corollary3_8'a : ∀ f x0 A, Function f -> x0 ∈ dom[f] -> f[x0] = A
  -> limit_pos f x0 A -> ∀ x, IsSeq x -> ran[x] ⊂ dom[f] -> (∀ n, x0 <= x[n])
  -> limit_seq x x0 -> limit_seq \{\ λ n v, v = f[x[n]] \}\ A.
Proof.
  intros f x0 A H0 H1 H2 H3. destruct H3 as [H3 [δ1' [H4 [H5 H6]]]].
  intros x H7 H8 H8' H9. unfold limit_seq.
  assert (H10 : IsSeq \{\ λ n v, v = f[x[n]] \}\ ).
  { unfold IsSeq. split.
    - unfold Function. intros x1 y1 z1 I1 I2. applyClassifier2 I1.
      applyClassifier2 I2. rewrite I2; auto.
    - apply AxiomI. intro z; split; intro I1.
      + apply Classifier1. reflexivity.
      + apply Classifier1. exists (f[x[z]]). apply Classifier2. reflexivity. }
  split; auto. intros ε H11. apply H6 in H11 as H12.
  destruct H12 as [δ [[H12 H13] H14]]. apply H9 in H12 as H15.
  destruct H15 as [N H15]. exists N. intros n H16. apply H15 in H16 as H17.
  assert (H19 : x0 <= x[n] < x0 + δ).
  { apply Abs_R in H17. generalize (H8' n); intro I1. lra. }
  assert (H21 : ∣(f[x[n]] - A)∣ < ε).
  { assert (I1 : x0 < x[n] < x0 + δ \/ x[n] = x0). lra. destruct I1 as [I1 | I1].
    - apply H14 in I1. assumption.
    - rewrite I1. rewrite H2. unfold Rminus.
      rewrite Rplus_opp_r. rewrite Abs_ge; lra. }
  assert (H20 : (\{\ λ n0 v, v = f[x[n0]] \}\)[n] = f[x[n]]).
  { apply f_x_T; try apply H10. apply Classifier2. reflexivity. }
  rewrite H20. assumption.
Qed.

Corollary Corollary3_8'b : ∀ f x0 A, Function f -> x0 ∈ dom[f] -> f[x0] = A
  -> limit_neg f x0 A -> ∀ x, IsSeq x -> ran[x] ⊂ dom[f] -> (∀ n, x[n] <= x0)
  -> limit_seq x x0 -> limit_seq \{\ λ n v, v = f[x[n]] \}\ A.
Proof.
  intros f x0 A H0 H1 H2 H3. destruct H3 as [H3 [δ1' [H4 [H5 H6]]]].
  intros x H7 H8 H8' H9. unfold limit_seq.
  assert (H10 : IsSeq \{\ λ n v, v = f[x[n]] \}\ ).
  { unfold IsSeq. split.
    - unfold Function. intros x1 y1 z1 I1 I2.
      applyClassifier2 I1. applyClassifier2 I2. rewrite I2; auto.
    - apply AxiomI. intro z; split; intro I1.
      + apply Classifier1. reflexivity.
      + apply Classifier1. exists (f[x[z]]). apply Classifier2. reflexivity. }
  split; auto. intros ε H11. apply H6 in H11 as H12.
  destruct H12 as [δ [[H12 H13] H14]]. apply H9 in H12 as H15.
  destruct H15 as [N H15]. exists N. intros n H16. apply H15 in H16 as H17.
  assert (H19 : x0 - δ < x[n] <= x0 ).
  { apply Abs_R in H17. generalize (H8' n); intro I1. lra. }
  assert (H21 : ∣(f[x[n]] - A)∣ < ε).
  { assert (I1 : x0 - δ < x[n] < x0 \/ x[n] = x0). lra. destruct I1 as [I1 | I1].
    - apply H14 in I1. assumption.
    - rewrite I1. rewrite H2. unfold Rminus.
      rewrite Rplus_opp_r. rewrite Abs_ge; lra. }
  assert (H20 : (\{\ λ n0 v, v = f[x[n0]] \}\)[n] = f[x[n]]).
  { apply f_x_T; try apply H10. apply Classifier2. reflexivity. }
  rewrite H20. assumption.
Qed.

(* 定理3.9 归结原则(右极限) *)
Fixpoint Fun_Theorem3_9 (f : @set (@prod R R)) n x0 δ' A ε0 :=
  match n with
  | O => c \{ λ u, x0 < u < x0 + δ'/2 /\ ∣(f[u] - A)∣ >= ε0 \}
  | S n' => c \{λ u, x0 < u < x0
      + ((Fun_Theorem3_9 f n' x0 δ' A ε0) - x0)/(INR (n' + 3))
      /\ ∣(f[u] - A)∣ >= ε0 \}
  end.

(* 归结原则(右极限) *)
Theorem Theorem3_9 : ∀ f x0 δ' A, Function f -> δ' > 0 -> U+º(x0; δ') ⊂ dom[f] 
  -> limit_pos f x0 A <-> ∀ x, DecreaseSeq x -> ran[x] ⊂ U+º(x0; δ')
  -> limit_seq x x0 -> limit_seq \{\ λ n v, v = f[x[n]] \}\ A.
Proof.
  intros f x0 δ' A H0 H1 H2. split.
  - intro H3. destruct H3 as [H3 [δ1' [H4 [H5 H6]]]].
    intros x [H7 H30] H8 H9. unfold limit_seq.
    assert (H10 : IsSeq \{\ λ n v, v = f[x[n]] \}\ ).
    { unfold IsSeq. split.
      - unfold Function. intros x1 y1 z1 I1 I2.
        applyClassifier2 I1. applyClassifier2 I2. rewrite I2; auto.
      - apply AxiomI. intro z; split; intro I1.
        + apply Classifier1. reflexivity.
        + apply Classifier1. exists (f[x[z]]). apply Classifier2. reflexivity. }
    split; auto. intros ε H11. apply H6 in H11 as H12.
    destruct H12 as [δ [[H12 H13] H14]]. apply H9 in H12 as H15.
    destruct H15 as [N H15]. exists N. intros n H16. apply H15 in H16 as H17.
    assert (H18 : x[n] - x0 > 0).
    { assert (I2 : x[n] ∈ ran[x]).
      { destruct H7 as [I2 I3]. apply fx_ran_T; auto. rewrite I3.
        apply Classifier1. reflexivity. } apply H8 in I2. applyClassifier1 I2. lra. }
    assert (H19 : x0 < x[n] < x0 + δ). { rewrite Abs_gt in H17; auto. lra. }
    apply H14 in H19. assert (H20 : (\{\ λ n0 v, v = f[x[n0]] \}\)[n] = f[x[n]]).
    { apply f_x_T; try apply H10. apply Classifier2. reflexivity. }
    rewrite H20. apply H19.
  - intro H3. apply NNPP. intro H4. unfold limit in H4. apply not_and_or in H4.
    destruct H4 as [H4 | H4]; auto. apply not_ex_all_not with (n := δ') in H4.
    apply not_and_or in H4; destruct H4 as [H4 | H4]; auto.
    apply not_and_or in H4; destruct H4 as [H4 | H4]; auto.
    apply not_all_ex_not in H4. destruct H4 as [ε0 H4].
    apply imply_to_and in H4. destruct H4 as [H4 H5].
    assert (H6 : ∀ δ, ~ (0 < δ < δ'
      /\ (∀ x, x0 < x < x0 + δ -> ∣(f[x] - A)∣ < ε0))).
    { apply not_ex_all_not; apply H5. }
    assert (H7 : ∃ x, x = \{\ λ n v, v = Fun_Theorem3_9 f n x0 δ' A ε0 \}\).
    { exists (\{\ λ n v, v = Fun_Theorem3_9 f n x0 δ' A ε0 \}\); reflexivity. }
    destruct H7 as [x H7]. assert (H8 : IsSeq x).
    { split.
      - unfold Function. rewrite H7. intros x1 y1 z1 J1 J2. applyClassifier2 J1.
        applyClassifier2 J2. rewrite J2. apply J1.
      - apply AxiomI. intro z; split; intro J1.
        + apply Classifier1. reflexivity.
        + apply Classifier1. exists (Fun_Theorem3_9 f z x0 δ' A ε0).
          rewrite H7. apply Classifier2. reflexivity. }
    assert (H9 : ∀ n, x[n] = Fun_Theorem3_9 f n x0 δ' A ε0).
    { intro n. apply f_x_T; try apply H8. rewrite H7. apply Classifier2. auto. }
    assert (H10 : ∀ n, x0 < (Fun_Theorem3_9 f n x0 δ' A ε0) < x0 + δ'
      /\ NotEmpty \{λ u, x0 < u
        < x0 + ((Fun_Theorem3_9 f n x0 δ' A ε0)-x0)/(INR (n + 3))
      /\ ∣(f[u] - A)∣ >= ε0 \}).
    { intro n. induction n as [|n IHn].
      - assert (I1 : x0 < (Fun_Theorem3_9 f 0 x0 δ' A ε0) < x0 + δ').
        { simpl. generalize (H6 (δ'/2)). intro I1. apply not_and_or in I1.
          destruct I1 as [I1 | I1]; try lra. apply not_all_ex_not in I1.
          destruct I1 as [xn I1]. apply imply_to_and in I1.
          assert (I2 : NotEmpty \{ λ u, x0 < u < x0 + δ'/2
            /\ ∣(f[u] - A)∣ >= ε0 \}). { exists xn. apply Classifier1. split; lra. }
          apply Axiomc in I2 as I3. applyClassifier1 I3. lra. }
        split; auto. generalize (H6 (((Fun_Theorem3_9 f 0 x0 δ' A ε0)-x0)/3)).
        intro I2. apply not_and_or in I2. destruct I2 as [I2 | I2]; try lra.
        apply not_all_ex_not in I2. destruct I2 as [xn I2].
        apply imply_to_and in I2. exists xn. apply Classifier1.
        assert (I3 : INR (0+3) = 3). { simpl. field. }
        rewrite I3. split; lra.
      - destruct IHn as [IHn1 IHn2].
        assert (I1 : x0 < (Fun_Theorem3_9 f (S n) x0 δ' A ε0) < x0 + δ').
        { apply Axiomc in IHn2. applyClassifier1 IHn2. simpl. split; try lra.
          assert (I1 : (Fun_Theorem3_9 f n x0 δ' A ε0 - x0)/(INR (n + 3))
             < (Fun_Theorem3_9 f n x0 δ' A ε0 - x0)).
          { assert (J1 : (Fun_Theorem3_9 f n x0 δ' A ε0 - x0) > 0). lra.
            assert (J2 : INR (n+3) > 1).
            { assert (K1 : 1 = INR 1). { simpl. reflexivity. }
              rewrite K1. apply lt_INR. apply Nat.lt_lt_add_l. lia. }
            assert (J3 : 0 < 1 * (INR (n+3))).
            { apply Rmult_gt_0_compat; try apply Rlt_0_1. lra. }
            apply Rinv_lt_contravar in J2; auto. apply Rmult_lt_compat_l
            with (r := (Fun_Theorem3_9 f n x0 δ' A ε0 -x0)) in J2; auto. lra. }
          lra. } split; auto. generalize
            (H6 (((Fun_Theorem3_9 f (S n) x0 δ' A ε0) - x0)/(INR (S n + 3)))).
        intro I2. apply not_and_or in I2. destruct I2 as [I2 | I2].
        + exfalso. apply I2.
          assert (I3 : (Fun_Theorem3_9 f (S n) x0 δ' A ε0 -x0)/(INR ((S n) + 3))
            < (Fun_Theorem3_9 f (S n) x0 δ' A ε0 -x0)).
          { assert (J1 : (Fun_Theorem3_9 f (S n) x0 δ' A ε0 -x0) > 0). lra.
            assert (J2 : (INR ((S n) + 3)) > 1).
            { assert (K1 : 1 = INR 1). { simpl. reflexivity. }
              rewrite K1. apply lt_INR. apply Nat.lt_lt_add_l. lia. }
            assert (J3 : 0 < 1 * (INR ((S n) + 3))).
            { apply Rmult_gt_0_compat; try apply Rlt_0_1. lra. }
            apply Rinv_lt_contravar in J2; auto. apply Rmult_lt_compat_l
            with (r := (Fun_Theorem3_9 f (S n) x0 δ' A ε0 -x0)) in J2; auto.
            lra. } split; try lra. assert (I4 : INR (S n + 3) > 0).
          { assert (J1 : 0 = (INR 0%nat)). reflexivity. rewrite J1.
            apply lt_INR. lia. }
          apply Rinv_0_lt_compat in I4. apply Rmult_gt_0_compat; lra.
        + apply not_all_ex_not in I2. destruct I2 as [xn I2].
          apply imply_to_and in I2. exists xn. apply Classifier1. split; lra. }
    assert (H11 : DecreaseSeq x).
    { split; auto. intro n. rewrite H9. rewrite H9. simpl. generalize (H10 n).
      intro I1. destruct I1 as [I1 I2]. apply Axiomc in I2. applyClassifier1 I2.
      assert (I3 : (Fun_Theorem3_9 f n x0 δ' A ε0 -x0)/(INR (n + 3))
        < (Fun_Theorem3_9 f n x0 δ' A ε0 -x0)).
      { assert (J1 : (Fun_Theorem3_9 f n x0 δ' A ε0 -x0) > 0). lra.
        assert (J2 : INR (n + 3) > 1).
        { assert (K1 : 1 = INR 1). { simpl. reflexivity. } rewrite K1.
          apply lt_INR. apply Nat.lt_lt_add_l. lia. }
        assert (J3 : 0 < 1 * (INR (n + 3))).
        { apply Rmult_gt_0_compat; try apply Rlt_0_1. lra. }
        apply Rinv_lt_contravar in J2; auto. apply Rmult_lt_compat_l
        with (r := (Fun_Theorem3_9 f n x0 δ' A ε0 -x0)) in J2; auto. lra. }
      lra. } assert (H12 : ran[ x] ⊂ U+º(x0; δ')).
    { intros z I1. applyClassifier1 I1. destruct I1 as [n I1].
      apply f_x_T in I1; try apply H8. rewrite <- I1. rewrite H9.
      apply Classifier1. apply H10. }
    assert (H13 : ∀ n, x0 < x[n] < x0 + δ'/(INR (n+2))).
    { intro n. rewrite H9. induction n as [|n IHn].
      - simpl. generalize (H10 0%nat). intro I1. destruct I1 as [I1 I2].
        assert (I3 : NotEmpty \{ λ u, x0 < u < x0 + δ'/2
          /\ ∣(f[u] - A)∣ >= ε0 \}).
        { destruct I2 as [xn I2]. exists xn. apply -> Classifier1 in I2.
          lazy beta in I2. destruct I2 as [I2 I3]. apply Classifier1. split; auto.
          assert (I4 : INR (0 + 3) = 3). { simpl. field. }
          rewrite I4 in I2. lra. } apply Axiomc in I3. applyClassifier1 I3. lra.
      - simpl Fun_Theorem3_9. assert (I1 : (S n + 2 = n + 3)%nat).
        { assert (J1 : (3 = 1 + 2)%nat). auto. rewrite J1. lia. }
        rewrite I1. generalize (H10 n). intro I2.
        destruct I2 as [I2 I3]. apply Axiomc in I3. applyClassifier1 I3.
        assert (I4 : (Fun_Theorem3_9 f n x0 δ' A ε0 -x0)/(INR (n + 3))
          < δ'/(INR (n + 3))).
        { assert (J1 : INR (n + 3) > 0).
          { assert (K1 : 0 = INR 0). { simpl. reflexivity. }
            rewrite K1. apply lt_INR. apply Nat.lt_lt_add_l.
            apply Nat.lt_lt_succ_r. apply Nat.lt_0_2. }
          apply Rinv_0_lt_compat in J1.
          apply Rmult_lt_compat_r; auto. lra. } lra. }
    assert (H14 : limit_seq x x0).
    { split; auto. intros ε I1. generalize (Archimedes ε δ'). intro I2.
      generalize (I2 I1 H1). intro I3. destruct I3 as [N I3]. exists N.
      intros n I4. generalize (H13 n). intro I5.
      assert (I6 : INR (n + 2) > INR N). { apply lt_INR. lia. }
      assert (I7 : x[n] - x0 > 0). lra. rewrite Abs_gt; auto.
      assert (I8 : 0 < INR N).
      { destruct (pos_INR N) as [J1 | J1]; auto. exfalso.
        rewrite <- J1 in I3. rewrite Rmult_0_l in I3. lra. }
      assert (I9 : 0 < INR (n + 2)). lra.
      assert (I10 : 0 < (INR N) * (INR (n + 2))).
      { apply Rmult_gt_0_compat; auto. }
      apply Rinv_lt_contravar in I6; auto.
      assert (I11 : δ'/(INR (n + 2)) < δ'/(INR N)).
      { apply Rmult_lt_compat_l; auto. }
      assert (I12 : δ'/(INR N) < ε).
      { apply Rmult_lt_reg_r with (r := INR N); auto.
        unfold Rdiv. rewrite Rmult_assoc. rewrite Rinv_l; lra. } lra. }
    generalize (H3 x H11 H12 H14). intro H15. unfold limit_seq in H15.
    destruct H15 as [H15 H16]. generalize (H16 ε0 H4). intro H17.
    destruct H17 as [N H17]. assert (S N > N)%nat. lia.
    generalize (H17 (S N) H). intro H18.
    assert (H19 : (\{\ λ n v, v = f[x[n]] \}\)[S N] = f[x[S N]]).
    { apply f_x_T; try apply H15. apply Classifier2. reflexivity. }
    rewrite H19 in H18. generalize (H9 (S N)). intro H20. simpl in H20.
    generalize (H10 N). intros [H21 H22]. apply Axiomc in H22.
    rewrite <- H20 in H22. applyClassifier1 H22. lra.
Qed.

(* 定理3.10 单调有界定理 *)
Theorem Theorem3_10 : ∀ f x0 δ', δ' > 0 -> DMonotonicFun f U+º(x0; δ')
  -> DBoundedFun f U+º(x0; δ') -> (∃ A, limit_pos f x0 A).
Proof.
  intros f x0 δ' H0 [H1 | H1] [H2 [H3 [M H4]]].
  - assert (H5 : ∃ Range, Range = \{ λ y,
       ∃ x, x ∈ U+º(x0; δ') /\ y = f[x] \}).
    { exists \{ λ y, ∃ x, x ∈ (U+º(x0; δ'))
        /\ y = f[x] \}; reflexivity. } destruct H5 as [Range H5].
    assert (H6 : NotEmpty Range).
    { exists (f[x0 + δ'/2]). rewrite H5. apply Classifier1.
      exists (x0 + δ'/2). split; auto. apply Classifier1. split; lra. }
    assert (H7 : (∃ L, Lower Range L)).
    { exists (-M). unfold Lower. intros y I1. rewrite H5 in I1.
      applyClassifier1 I1. destruct I1 as [x [I1 I2]]. rewrite I2.
      apply H4 in I1. apply Abs_le_R in I1. lra. }
    apply Sup_inf_principle in H6 as [H8 H9]. apply H9 in H7.
    destruct H7 as [A [H7 H10]]. exists A. unfold limit_pos. split; auto.
    exists δ'. repeat split; auto. intros ε H11.
    assert (H12 : A + ε > A). lra. apply H10 in H12 as H13.
    destruct H13 as [y' [H13 H14]]. unfold Lower in H7. apply H7 in H13 as H15.
    rewrite H5 in H13. applyClassifier1 H13. destruct H13 as [x' [H13 H16]].
    exists (x'-x0). applyClassifier1 H13. split; try lra. intros x H17.
    apply Abs_R. unfold DIncreaseFun in H1. destruct H1 as [H1 [H18 H19]].
    assert (H20 : x ∈ U+º(x0; δ')). { apply Classifier1. lra. }
    assert (H21 : x' ∈ U+º(x0; δ')). { apply Classifier1. lra. }
    generalize (H19 x x' H20 H21). intro H22. assert (H23 : f[x] ∈ Range).
    { rewrite H5. apply Classifier1. exists x. split; auto. } apply H7 in H23. lra.
  - assert (H5 : ∃ Range, Range = \{ λ y,
       ∃ x, x ∈ U+º(x0; δ') /\ y = f[x] \}).
    { exists \{ λ y, ∃ x, x ∈ U+º(x0; δ') /\ y = f[x] \}; auto. }
    destruct H5 as [Range H5]. assert (H6 : NotEmpty Range).
    { exists (f[x0 + δ'/2]). rewrite H5. apply Classifier1.
      exists (x0 + δ'/2). split; auto. apply Classifier1. split; lra. }
    assert (H7 : (∃ M, Upper Range M)).
    { exists M. unfold Upper. intros y I1. rewrite H5 in I1.
      applyClassifier1 I1. destruct I1 as [x [I1 I2]]. rewrite I2.
      apply H4 in I1. apply Abs_le_R in I1. lra. }
    apply Sup_inf_principle in H6 as [H8 H9]. apply H8 in H7.
    destruct H7 as [A [H7 H10]]. exists A. unfold limit_pos. split; auto.
    exists δ'. repeat split; auto. intros ε H11. assert (H12 : A - ε < A). lra.
    apply H10 in H12 as H13. destruct H13 as [y' [H13 H14]]. unfold Upper in H7.
    apply H7 in H13 as H15. rewrite H5 in H13. applyClassifier1 H13.
    destruct H13 as [x' [H13 H16]]. exists (x' - x0). applyClassifier1 H13.
    split; try lra. intros x H17. apply Abs_R. unfold DDecreaseFun in H1.
    destruct H1 as [H1 [H18 H19]].
    assert (H20 : x ∈ U+º(x0; δ')). { apply Classifier1. lra. }
    assert (H21 : x' ∈ U+º(x0; δ')). { apply Classifier1. lra. }
    generalize (H19 x x' H20 H21). intro H22. assert (H23 : f[x] ∈ Range).
    { rewrite H5. apply Classifier1. exists x. split; auto. } apply H7 in H23. lra.
Qed.

(* 定理3.11 柯西准则 *)
Theorem Theorem3_11 : ∀ f x0 δ', δ' > 0 -> Function f -> Uº(x0; δ') ⊂ dom[f] 
  -> (∃ A, limit f x0 A) <-> (∀ ε, ε > 0 -> (∃ δ, 0 < δ < δ' /\ (∀ x' x'', 
    x' ∈ Uº(x0; δ) -> x'' ∈ Uº(x0; δ) ->∣(f[x'] - f[x''])∣ < ε))).
Proof.
  intros f x0 δ' H0 H1 H2. split; intro H3.
  - destruct H3 as [A H3]. destruct H3 as [H3 [δ1' [H4 [H5 H6]]]]. intros ε H7.
    assert (H8 : ε/2 > 0). lra. apply H6 in H8 as H9.
    assert (H10 : ∃ δ, 0 < δ < δ'
      /\ (∀ x, 0 < ∣(x - x0)∣ < δ -> ∣(f[x] - A)∣ < ε/2)).
    { destruct H9 as [δ [I1 I2]]. destruct (Rlt_or_le δ' δ1') as [I3 | I3].
      - destruct (Rlt_or_le δ δ') as [I4 | I4].
        + exists δ. split; auto; lra.
        + exists (δ' / 2). split; try lra. intros x I5. apply I2. lra.
      - exists δ. split; try lra. intros x I4. apply I2. apply I4. }
    destruct H10 as [δ [H10 H11]]. exists δ. split; auto. intros x' x'' H12 H13.
    applyClassifier1 H12. applyClassifier1 H13. apply H11 in H12. apply H11 in H13.
    assert (H14 : f[x'] - f[x''] = (f[x'] - A) - (f[x''] - A)). field.
    rewrite H14. generalize (Abs_minus_le (f[x'] - A) (f[x''] - A)).
    intro H15. lra.
  - assert (H4 : ∀ x, IsSeq x -> ran[x] ⊂ Uº(x0; δ') -> limit_seq x x0
      -> Convergence \{\ λ n v, v = f[x[n]] \}\).
    { intros x I1 I2 I3. assert (I4 : IsSeq \{\ λ n v, v = f[x[n]] \}\).
      { split.
        - unfold Function. intros x1 y1 z1 J1 J2.
          applyClassifier2 J1; applyClassifier2 J2. rewrite J2. assumption.
        - apply AxiomI. intro z; split; intro J1.
          + apply Classifier1. reflexivity.
          + apply Classifier1. exists (f[x[z]]). apply Classifier2. reflexivity. }
      apply Theorem2_11; auto. intros ε I5. apply H3 in I5 as I6.
      destruct I6 as [δ [I6 I7]]. unfold limit_seq in I3. destruct I3 as [I3 I8].
      destruct I6 as [I6 I9]. apply I8 in I6 as I10. destruct I10 as [N I10].
      exists N. intros n m I11 I12. apply I10 in I11 as I13.
      apply I10 in I12 as I14.
      assert (I15 : ∀ n, (\{\ λ n0 v, v = f[x[n0]] \}\)[n] = f[x[n]]).
      { intro n0. apply f_x_T; try apply I4. apply Classifier2. reflexivity. }
      rewrite I15. rewrite I15. assert (I16 : ∀ n, ∣(x[n] - x0)∣ > 0).
      { intro n0. assert (J1 : x[n0] ∈ ran[x]).
        { apply fx_ran_T; try apply I1. destruct I1 as [I1 J1].
          rewrite J1. apply Classifier1. reflexivity. }
        apply I2 in J1. applyClassifier1 J1. apply J1. }
      apply I7; apply Classifier1; split; try lra; apply I16. }
    assert (H5 : ∃ x1, x1 = \{\ λ n v, v = x0 + δ'/(INR (S (S n))) \}\).
    { exists \{\ λ n v, v = x0 + δ'/(INR (S (S n))) \}\. reflexivity. }
    destruct H5 as [x1 H5]. assert (H6 : IsSeq x1).
    { unfold IsSeq. split.
      - unfold Function. rewrite H5. intros x y z I1 I2. applyClassifier2 I1.
        applyClassifier2 I2. rewrite I2. apply I1.
      - apply AxiomI. intro n; split; intro I1.
        + apply Classifier1. reflexivity.
        + apply Classifier1. exists (x0 + δ'/(INR (S (S n)))).
          rewrite H5. apply Classifier2. reflexivity. }
    assert (H7 : ran[x1] ⊂ Uº(x0; δ')).
    { intros y I1. applyClassifier1 I1. destruct I1 as [n I1].
      rewrite H5 in I1. apply -> Classifier2 in I1.
      assert (I2 : y = x0 + δ'/(INR (S (S n)))). { apply I1. }
      rewrite I2. apply Classifier1. assert (I4 : δ'/(INR (S (S n))) > 0).
      { rewrite S_INR. apply Rdiv_lt_0_compat; auto.
        generalize (pos_INR (S n)). intro I4. lra. }
      assert (I3 : x0 + δ'/(INR (S (S n))) - x0 = δ'/(INR (S (S n)))). lra.
      rewrite I3. split.
      - apply Abs_not_eq_0. apply Rgt_not_eq. auto.
      - apply Abs_gt in I4 as I5. rewrite I5. rewrite S_INR. rewrite S_INR.
        generalize (pos_INR n). intro I6. assert (I7 : (INR n) + 1 + 1 > 1). lra.
        unfold Rdiv. assert (I8 : 1 <= 1). right. reflexivity.
        apply Rinv_1_lt_contravar in I7 as I9; auto. rewrite Rinv_1 in I9.
        apply Rmult_lt_compat_l with (r := δ') in I9; auto.
        rewrite Rmult_1_r in I9. assumption. }
    assert (H8 : limit_seq x1 x0).
    { split; auto. intros ε I1. generalize (Archimedes ε δ' I1 H0). intro I2.
      destruct I2 as [N I2]. exists N. intros n I3.
      assert (I4 : x1[n] = x0 + δ'/(INR (S (S n)))).
      { apply f_x_T; try apply H6. rewrite H5. apply Classifier2. reflexivity. }
      rewrite I4. assert (I5 : x0 + δ'/(INR (S (S n))) - x0 = δ'/(INR (S (S n)))).
      lra. rewrite I5. assert (I6 : δ'/(INR (S (S n))) > 0).
      { rewrite S_INR. apply Rdiv_lt_0_compat; auto.
        generalize (pos_INR (S n)). intro I7. lra. }
      apply Abs_gt in I6. rewrite I6. rewrite S_INR. rewrite S_INR.
      assert (I7 : (INR n + 1 + 1) * ε > (INR N) * ε).
      { apply Rmult_gt_compat_r; auto.
        assert (I8 : INR n > INR N). { apply lt_INR. apply I3. } lra. }
      generalize (Rgt_trans (((INR n) + 1 + 1) * ε) (INR N * ε) δ' I7 I2).
      intro I8. assert (I9 : ((INR n) + 1 + 1) > 0).
      { generalize (pos_INR n). intro I9. lra. }
      unfold Rdiv. apply Rinv_0_lt_compat in I9 as I10.
      apply Rmult_gt_compat_r with (r := /((INR n) + 1 + 1)) in I8; auto.
      assert (I11 : ((INR n) + 1 + 1) * ε * /((INR n) + 1 + 1) = ε).
      field. lra. rewrite I11 in I8. apply I8. }
    generalize (H4 x1 H6 H7 H8). intro H9. destruct H9 as [A H9]. exists A.
    apply (Theorem3_8 f x0 δ' A H1 H0 H2). intros x H10 H11 H12.
    assert (H13 : ∃ z, z = \{\ λ n v, ∃ m, ((n = m + m)%nat /\ v = x1[m])
      \/ ((n = m + m + 1)%nat /\ v = x[m]) \}\).
    { exists \{\ λ n v, ∃ m, ((n = m + m)%nat /\ v = x1[m]) 
        \/ ((n = m + m + 1)%nat /\ v = x[m]) \}\. reflexivity. }
    destruct H13 as [z H13].
    assert (H14 : ∀ n, ∃ m, (n = m + m \/ n = m + m + 1)%nat).
    { intro n. induction n as [|n IHn].
      - exists 0%nat. left. simpl. reflexivity.
      - destruct IHn as [m [IHn | IHn]].
        + exists m. right. rewrite IHn. rewrite Nat.add_1_r. reflexivity.
        + exists (S m). left. rewrite IHn. rewrite Nat.add_1_r. simpl. 
          rewrite (Nat.add_comm m (S m)). simpl. reflexivity. }
    assert (H15 : ∀ n m1 m2, (n = m1 + m1)%nat
      -> (n = m2 + m2 + 1)%nat -> False).
    { intros n m1 m2 I1 I2. rewrite I1 in I2.
      assert (I3 : (m1 + m1 - (m2 + m2))%nat = 1%nat). { rewrite I2. lia. }
      assert (I4 : ∀ k, (2 * k = k + k)%nat).
      { intro k. induction k as [|k IHk].
        - simpl. reflexivity.
        - simpl. rewrite <- plus_n_O. reflexivity. }
      rewrite <- I4 in I3. rewrite <- I4 in I3.
      rewrite <- Nat.mul_sub_distr_l in I3.
      assert (I5 : ∀ k, (2 * k = 1)%nat -> False). { intros. lia. }
      apply (I5 (m1 - m2)%nat). assumption. }
    assert (H16 : ∀ k, (2 * k = k + k)%nat).
    { intro k. induction k as [|k IHk].
      - simpl. reflexivity.
      - simpl. rewrite <- plus_n_O. reflexivity. }
    assert (H17 : IsSeq z).
    { rewrite H13. split.
      - intros n v1 v2 I1 I2. applyClassifier2 I1. applyClassifier2 I2.
        destruct I1 as [m1 I1]. destruct I2 as [m2 I2]. destruct I1 as [I1 | I1].
        + destruct I2 as [I2 | I2].
          * destruct I1 as [I1 I3]. destruct I2 as [I2 I4].
            assert (I5 : m1 = m2).
            { rewrite I1 in I2. apply NNPP. intro I5. apply not_eq in I5. 
              destruct I5 as [I5 | I5]; lia. }
            rewrite I4. rewrite <- I5. assumption.
          * destruct I1 as [I1 I3]. destruct I2 as [I2 I4]. exfalso. 
            apply (H15 n m1 m2); auto.
        + destruct I2 as [I2 | I2].
          * destruct I1 as [I1 I3]. destruct I2 as [I2 I4]. exfalso. 
            apply (H15 n m2 m1); auto.
          * destruct I1 as [I1 I3]. destruct I2 as [I2 I4].
            assert (I5 : m1 = m2).
            { rewrite I1 in I2. apply NNPP. intro I5. apply not_eq in I5. 
              destruct I5 as [I5 | I5]; lia. } rewrite I4. rewrite <- I5. assumption.
      - apply AxiomI. intro k; split; intro I1.
        + apply Classifier1. reflexivity.
        + apply Classifier1. generalize (H14 k). intro I2.
          destruct I2 as [m [I2 | I2]].
          * exists (x1[m]). apply Classifier2. exists m. left. split; auto.
          * exists (x[m]). apply Classifier2. exists m. right. split; auto. }
    assert (H18 : ran[z] ⊂ Uº(x0; δ')).
    { intros v I1. applyClassifier1 I1. destruct I1 as [k I1]. rewrite H13 in I1.
      applyClassifier2 I1. destruct I1 as [m [[I1 I2] | [I1 I2]]].
      - apply H7. rewrite I2. destruct H6 as [H6 I3]. apply fx_ran_T; auto. 
        rewrite I3. apply Classifier1. reflexivity.
      - apply H11. rewrite I2. destruct H10 as [H10 I3]. apply fx_ran_T; auto.
        rewrite I3. apply Classifier1. reflexivity. }
    assert (H19 : limit_seq z x0).
    { split; auto. intros ε I1. apply H8 in I1 as I2. apply H12 in I1 as I3.
      destruct I3 as [N2 I3]. destruct I2 as [N1 I2].
      generalize (Max_nat_2 (N1 + N1)%nat (N2 + N2 + 1)%nat). intro I4. 
      destruct I4 as [N [I4 I5]]. exists N. intros n I6. generalize (H14 n).
      destruct H17 as [H17 I7]. intros [m [I8 | I8]].
      - assert (I9 : z[n] = x1[m]).
        { apply f_x_T; auto. rewrite H13. apply Classifier2. exists m. left. split;
          auto. } rewrite I9. generalize (Nat.lt_trans (N1 + N1)%nat N n I4 I6).
        intro I10. rewrite I8 in I10. assert (I11 : (N1 < m)%nat).
        { apply NNPP. intro J1. apply not_lt in J1. lia. } apply I2. assumption.
      - assert (I9 : z[n] = x[m]).
        { apply f_x_T; auto. rewrite H13. apply Classifier2.
          exists m. right. split; auto. }
        rewrite I9. generalize (Nat.lt_trans (N2 + N2 + 1)%nat N n I5 I6).
        intro I10. rewrite I8 in I10. assert (I11 : (N2 < m)%nat).
        { apply NNPP. intro J1. apply not_lt in J1. lia. } apply I3. assumption. }
    generalize (H4 x H10 H11 H12). intro H20.
    generalize (H4 z H17 H18 H19). intros [B H21].
    assert (H22 : SubSeq \{\ λ n v, v = f[z[n]] \}\ \{\ λ n v, v = f[x1[n]] \}\).
    { unfold SubSeq. destruct H20 as [C [H20 H22]]. destruct H21 as [H21 H23].
      destruct H9 as [H9 H24]. split; [idtac | split]; auto.
      exists \{\ λ m n, n = (m + m)%nat \}\.
      assert (I1 : StrictlyIncreaseFun_nat \{\ λ m n, n = (m + m)%nat \}\).
      { unfold StrictlyIncreaseFun_nat. split.
        - unfold Function. intros m n1 n2 I1 I2.
          applyClassifier2 I1. applyClassifier2 I2. rewrite I2. assumption.
        - intros m1 m2 n1 n2 I1 I2 I3. applyClassifier2 I1. applyClassifier2 I2.
          rewrite I1. rewrite I2. lia. }
      split; auto. split.
      - apply AxiomI. intro n; split; intro I2.
        + apply Classifier1. reflexivity.
        + apply Classifier1. exists (n + n)%nat. apply Classifier2. reflexivity.
      - intro n. assert (I2 : (\{\ λ n0 v, v = f[x1[n0]] \}\)[n] = f[x1[n]]).
        { apply f_x_T; try apply H9. apply Classifier2. reflexivity. }
        rewrite I2. assert (I3 : (\{\ λ m n0, n0 = (m + m)%nat \}\)[n]
          = (n + n)%nat).
        { apply f_x_T; try apply I1. apply Classifier2. reflexivity. }
        rewrite I3. assert (I4 : (\{\ λ n0 v, v = f[z[n0]] \}\)[(n + n)%nat]
          = f[z[(n + n)%nat]]).
        { apply f_x_T; try apply H21. apply Classifier2. reflexivity. }
        rewrite I4. assert (I5 : z[(n + n)%nat] = x1[n]).
        { apply f_x_T; try apply H17. rewrite H13. apply Classifier2.
          exists n. left. split; reflexivity. }
        rewrite I5. reflexivity. }
    assert (H23 : SubSeq \{\ λ n v, v = f[z[n]] \}\ \{\ λ n v, v = f[x[n]] \}\).
    { unfold SubSeq. destruct H20 as [C [H20 H23]]. destruct H21 as [H21 H24].
      split; [idtac | split]; auto. exists \{\ λ m n, n = (m + m + 1)%nat \}\.
      assert (I1 : StrictlyIncreaseFun_nat \{\ λ m n, n = (m + m + 1)%nat \}\).
      { unfold StrictlyIncreaseFun_nat. split.
        - unfold Function. intros m n1 n2 I1 I2.
          applyClassifier2 I1. applyClassifier2 I2. rewrite I2. assumption.
        - intros m1 m2 n1 n2 I1 I2 I3. applyClassifier2 I1. applyClassifier2 I2.
          rewrite I1. rewrite I2. lia. }
      split; auto. split.
      - apply AxiomI. intro n; split; intro I2.
        + apply Classifier1. reflexivity.
        + apply Classifier1. exists (n + n + 1)%nat. apply Classifier2. reflexivity.
      - intro n. assert (I2 : (\{\ λ n0 v, v = f[x[n0]] \}\)[n] = f[x[n]]).
        { apply f_x_T; try apply H20. apply Classifier2. reflexivity. }
        rewrite I2. assert (I3 : (\{\ λ m n0, n0 = (m + m + 1)%nat \}\)[n]
          = (n + n + 1)%nat).
        { apply f_x_T; try apply I1. apply Classifier2. reflexivity. }
        rewrite I3. assert (I4 : (\{\ λ n0 v, v = f[z[n0]] \}\)[(n + n + 1)%nat]
          = f[z[(n + n + 1)%nat]]).
        { apply f_x_T; try apply H21. apply Classifier2. reflexivity. }
        rewrite I4. assert (I5 : z[(n + n + 1)%nat] = x[n]).
        { apply f_x_T; try apply H17. rewrite H13. apply Classifier2. exists n. 
          right. split; reflexivity. } rewrite I5. reflexivity. }
    generalize (SubSeqEqual \{\ λ n v, v = f[z[n]] \}\ B H21).
    intro H24. apply H24 in H22. apply H24 in H23.
    generalize (Theorem2_2 \{\ λ n v, v = f[x1[n]] \}\ A B H9 H22).
    intro H25. rewrite H25. assumption.
Qed.

(* 3.5 无穷小量与无穷大量 *)
(* 无穷小量 *)
Definition Infinitesimal f x0 := limit f x0 0.

Corollary Corollary_Infinitesimal_a : ∀ f g x0, Infinitesimal f x0
  -> Infinitesimal g x0 -> Infinitesimal (f \+ g) x0.
Proof.
  intros. pose proof Theorem3_7a f g x0 0 0.
  replace (0 + 0) with 0 in H1; [ |lra]. apply H1; auto.
Qed.

Corollary Corollary_Infinitesimal_b : ∀ f g x0, Infinitesimal f x0
  -> Infinitesimal g x0 -> Infinitesimal (f \- g) x0.
Proof.
  intros. pose proof Theorem3_7b f g x0 0 0.
  replace (0 - 0) with 0 in H1; [ |lra]. apply H1; auto.
Qed.

Corollary Corollary_Infinitesimal_c : ∀ f g x0, Infinitesimal f x0
  -> Infinitesimal g x0 -> Infinitesimal (f \* g) x0.
Proof.
  intros. pose proof Theorem3_7c f g x0 0 0.
  replace (0 * 0) with 0 in H1; [ |lra]. apply H1; auto.
Qed.

Corollary Corollary_Infinitesimal_d : ∀ f g x0 δ, δ > 0 -> Infinitesimal f x0
  -> DBoundedFun g Uº(x0; δ) -> Infinitesimal (f \* g) x0.
Proof.
  intros. split. apply Corollary_mult_fun_a.
  destruct H0 as [H0[x[H3[]]]], H1 as [H1[H5[M]]].
  assert (∃ δ', δ' > 0 /\ Uº(x0; δ') ⊂ Uº(x0; x) /\ Uº(x0; δ') ⊂ Uº(x0; δ)).
  { destruct (Rlt_or_le x δ); [exists x | exists δ]; repeat split; auto;
    intros; auto; applyClassifier1 H8; apply Classifier1; lra. }
  destruct H7 as [δ' [H7 []]]. assert (Uº(x0; δ') ⊂ dom[f \* g]).
  { red; intros. apply Classifier1. exists (f[z] * g[z]). apply Classifier2; auto. }
  assert (∀ ε, ε > 0 -> ∃ δ, 0 < δ < δ'
    /\ (∀ x, 0 < ∣(x - x0)∣ < δ -> ∣(f[x] - 0)∣ < ε)).
  { intros. apply H4 in H11 as [x1[]]. destruct (Rlt_or_le x1 δ'). exists x1.
    split; auto. lra. exists (δ'/2). split. lra. intros. apply H12. lra. }
  assert (0 <= M) as [].
  { destruct (Rlt_or_le M 0); auto. assert ((x0 + δ/2) ∈ Uº(x0; δ)).
    { apply Classifier1. replace (x0 + δ/2 - x0) with (δ/2).
      rewrite Abs_ge; lra. lra. }
    apply H6 in H13. pose proof (Abs_Rge0 g [x0 + δ/2]).
    assert (0 < 0). lra. apply Rlt_irrefl in H15. elim H15. }
  - exists δ'. repeat split; auto. intros.
    assert (ε/M > 0). apply Rdiv_lt_0_compat; auto.
    apply H11 in H14 as [x1[]]. exists x1. split; auto. intros.
    assert (x2 ∈ Uº(x0; δ')). { apply Classifier1; lra. }
    rewrite Rminus_0_r,Corollary_mult_fun_b,Abs_mult; auto. apply H15 in H16.
    apply H9,H6 in H17. rewrite Rminus_0_r in H16. replace ε with (ε/M * M).
    destruct H17. apply Rmult_le_0_lt_compat; auto.
    destruct (Abs_Rge0 f[x2]); [left | right]; auto.
    destruct (Abs_Rge0 g[x2]); [left | right]; auto.
    rewrite H17. rewrite Rmult_comm,(Rmult_comm _ M).
    apply Rmult_lt_compat_l; auto. unfold Rdiv.
    rewrite Rmult_comm,<-Rmult_assoc. apply Rinv_r_simpl_m; auto. lra.
  - exists (δ'). repeat split; auto. intros. pose proof H13 as H13'.
    apply H11 in H13 as [x1[]]. exists x1. split; auto. intros.
    assert (x2 ∈ Uº(x0; δ')). { apply Classifier1; lra. }
    rewrite Rminus_0_r,Corollary_mult_fun_b,Abs_mult; auto.
    assert (∣(g[x2])∣ = 0).
    { apply H9,H6 in H16. rewrite <-H12 in H16. pose proof (Abs_Rge0 g[x2]). lra. }
    rewrite H17,Rmult_0_r; auto.
Qed.

 (* 高阶无穷小量 *)
Definition InfinitesimalHigherOrder f g x0 := Infinitesimal f x0
  /\ Infinitesimal g x0 /\ limit (f // g) x0 0.
Notation "o( g )(→ x0 )" := (\{ λ f, InfinitesimalHigherOrder f g x0 \}).
Notation "o(1)(→ x0 )" := (\{ λ f, Infinitesmal f x0 \}).

(* 同阶无穷小 *)
Definition InfinitesimalSameOrder f g x0 := Infinitesimal f x0
  /\ Infinitesimal g x0 /\ (∃ δ, 0 < δ /\ Uº(x0;δ) ⊂ dom[f]
  /\ Uº(x0;δ) ⊂ dom[g] /\ (∀ x, x ∈ Uº(x0;δ) -> g[x] <> 0)
  /\ (∃ K L, 0 < K <= L /\ (∀ x, x ∈ Uº(x0;δ) -> K <= ∣(f[x]/g[x])∣ <= L))).

Corollary Corollary_InfinitesimalSameOrder :
  ∀ f g x0, Infinitesimal f x0 -> Infinitesimal g x0
  -> (∃ c, c <> 0 /\ limit (f // g) x0 c) -> InfinitesimalSameOrder f g x0.
Proof.
  intros. destruct H1 as [c[]]. assert (∃ c, limit (f // g) x0 c); eauto.
  apply Theorem3_3a in H3 as [δ[H3[H4[H5[M]]]]]. split; [ | split]; auto.
  assert (∃ δ1, 0 < δ1 /\ (∀ x, x ∈ Uº(x0; δ1) -> ∣(c/2)∣ < ∣((f // g)[x])∣)).
  { destruct (Req_appart_dec 0 c) as [H7 | []]. elim H1; auto.
    apply Theorem3_4a with (r := c/2) in H2; auto; [ | lra].
    destruct H2 as [x[]]. exists x. split; auto. intros.
    apply H8 in H9 as []. rewrite Abs_ge,Abs_ge; auto; lra.
    apply Theorem3_4b with (r := -(c/2)) in H2; auto; [ | lra].
    destruct H2 as [x[]]. exists x. split; auto. intros.
    apply H8 in H9 as []. rewrite Abs_lt,Abs_lt; lra. }
  destruct H7 as [δ1[]].
  assert (∃ δ0, 0 < δ0 /\ δ0 <= δ /\ δ0 <= δ1) as [δ0[H9[]]].
  { destruct (Rlt_or_le δ δ1); [exists δ | exists δ1]; lra. }
  assert (Uº(x0; δ0) ⊂ dom[f // g]).
  { red; intros. apply H5. applyClassifier1 H12. apply Classifier1; lra. }
  rewrite Corollary_div_fun_c in H12. exists δ0. repeat split; auto;
  unfold Contain; intros; try (apply H12 in H13; applyClassifier1 H13;
  destruct H13; applyClassifier1 H14; destruct H14; applyClassifier1 H15); auto.
  assert (Uº(x0; δ0) ⊂ Uº(x0; δ1) /\ Uº(x0; δ0) ⊂ Uº(x0; δ)) as [].
  { split; red; intros; applyClassifier1 H13; apply Classifier1; lra. }
  assert ((x0 + δ0/2) ∈ Uº(x0; δ0)).
  { apply Classifier1. replace (x0 + δ0/2 - x0) with (δ0/2); [ |lra].
    rewrite Abs_ge; lra. }
  exists (∣(c/2)∣),M. split. pose proof H15. apply H13,H8 in H15.
  apply H14,H6 in H16. split; [ |lra]. destruct (Abs_Rge0 (c/2)); auto.
  rewrite <-Abs_eq_0 in H17. elim H1. lra. intros. pose proof H16.
  apply H12 in H16. applyClassifier1 H16. destruct H16. applyClassifier1 H18.
  destruct H18. applyClassifier1 H19. rewrite <-Corollary_div_fun_b; auto.
  split; [left | ]; auto.
Qed.

Notation "O( g )(→ x0 )" := (\{ λ f, Infinitesimal f x0
  /\ Infinitesimal g x0 /\ (∃ δ, 0 < δ /\ Uº(x0;δ) ⊂ dom[f]
  /\ Uº(x0;δ) ⊂ dom[g] /\ (∀ x, x ∈ Uº(x0;δ) -> g[x] <> 0)
  /\ (∃ L, 0 < L /\ (∀ x, x ∈ Uº(x0;δ) -> ∣(f[x]/g[x])∣ <= L))) \}).
Notation "O(1)(→ x0 )" := (\{ λ f, ∃ δ, 0 < δ /\ DBoundedFun f Uº(x0;δ) \}).

(* 等价无穷小 *)
Definition InfinitesimalEquivalent f g x0 := Infinitesimal f x0
  /\ Infinitesimal g x0 /\ limit (f // g) x0 1.
Notation "( f ~ g )(→ x0 )" := (InfinitesimalEquivalent f g x0).

Corollary Corollary_InfinitesimalEquivalent :
  ∀ f g x0, InfinitesimalEquivalent f g x0 -> InfinitesimalEquivalent g f x0.
Proof.
  intros. destruct H as [H[]]. split; [ | split]; auto. apply Lemma3_7d in H1;
  auto. rewrite Rinv_1 in H1. destruct H1 as [H1[x[H2[]]]].
  rewrite Corollary_div_fun_d,Corollary_div_fun_c in H3. split.
  apply Corollary_div_fun_a. exists x. split; auto.
  assert (Uº(x0; x) ⊂ dom[g // f]).
  { rewrite Corollary_div_fun_c. red; intros. apply H3 in H5.
    applyClassifier1 H5. destruct H5. applyClassifier1 H5. destruct H5.
    applyClassifier1 H7. destruct H7. apply Classifier1; split; auto.
    apply Classifier1; split; auto. applyClassifier1 H6. apply Classifier1. intro.
    rewrite Corollary_div_fun_b,H9 in H6; auto. unfold Rdiv in H6.
    rewrite Rmult_0_l in H6; auto. }
  split; auto. intros. apply H4 in H6 as [x1[]]. exists x1. split; auto.
  intros. assert (x2 ∈ Uº(x0; x)). { apply Classifier1. lra. }
  assert (x2 ∈ dom[f] /\ x2 ∈ dom[g] /\ g[x2] <> 0 /\ f[x2] <> 0) as [H10[H11[]]].
  { apply H3 in H9. applyClassifier1 H9. destruct H9. applyClassifier1 H9.
    destruct H9. applyClassifier1 H11. destruct H11. applyClassifier1 H12.
    applyClassifier1 H10. repeat split; auto. intro.
    rewrite Corollary_div_fun_b in H10; auto. unfold Rdiv in H10.
    rewrite H13,Rmult_0_l in H10; auto. }
  assert ((g // f)[x2] = (1 /// (f // g))[x2]).
  { rewrite <-Corollary_div_fun_c,<-Corollary_div_fun_d in H3.
    assert ([x2, (g[x2]/f[x2])] ∈ (g // f)). { apply Classifier2; auto. }
    assert ([x2, (g[x2]/f[x2])] ∈ (1 /// (f // g))).
    { apply Classifier2; repeat split; auto. rewrite Corollary_div_fun_c.
      apply Classifier1; split; auto. apply Classifier1; split; auto.
      apply Classifier1; auto. intro. rewrite Corollary_div_fun_b in H15; auto.
      assert ((f[x2]/g[x2]) * g[x2] = 0). { rewrite H15,Rmult_0_l; auto. }
      unfold Rdiv in H16. rewrite Rmult_comm,<-Rmult_assoc,Rinv_r_simpl_m in H16;
      auto. rewrite Corollary_div_fun_b; auto. unfold Rdiv.
      rewrite Rinv_mult,Rinv_inv,Rmult_1_l,Rmult_comm; auto. }
    pose proof (Corollary_div_fun_a g f). apply f_x_T in H14,H15; auto.
    rewrite H14,H15; auto. }
  rewrite H14; auto.
Qed.

Lemma Lemma3_12 : ∀ f A x0 a, Function f -> limit (f|[A]) x0 a -> limit f x0 a.
Proof.
  intros. destruct H0 as [H0[x[H1[]]]]. split; auto. exists x.
  apply RestrictFun with (D := A) in H as [H[]].
  repeat split; auto. red; intros. apply H2 in H6. rewrite H4 in H6.
  applyClassifier1 H6; tauto. intros. apply H3 in H6 as [x1[]]. exists x1.
  split; intros; auto. rewrite <-H5. apply H7 in H8; auto.
  apply H2,Classifier1. lra.
Qed.

(* 定理3.12 *)
Theorem Theorem3_12a : ∀ f g h x0 A, InfinitesimalEquivalent f g x0
  -> limit (f \* h) x0 A -> limit (g \* h) x0 A.
Proof.
  intros. assert ((g // f) \* (f \* h) = (g \* h)|[dom[f] ∩ \{ λ u, f[u] <> 0 \}]).
  { apply AxiomI; split; intros.
    - applyClassifier1 H1. destruct H1 as [x[y[H1[H2[]]]]]. rewrite H1.
      rewrite Corollary_div_fun_c in H2. rewrite Corollary_mult_fun_c in H3.
      applyClassifier1 H2; destruct H2. applyClassifier1 H5; destruct H5.
      applyClassifier1 H3; destruct H3. applyClassifier1 H6.
      rewrite Corollary_div_fun_b,Corollary_mult_fun_b in H4; auto.
      unfold Rdiv in H4. rewrite Rmult_comm,(Rmult_comm f[x]),Rmult_assoc,
      <-(Rmult_assoc f[x]),Rinv_r_simpl_m,Rmult_comm in H4; auto.
      apply Classifier1. split; apply Classifier2; split; auto.
      apply Classifier1; split; auto. apply Classifier1; auto.
    - applyClassifier1 H1. destruct H1. applyClassifier1 H1.
      destruct H1 as [x[y[H1[H3[]]]]]. rewrite H1 in H2.
      applyClassifier2 H2. destruct H2. applyClassifier1 H2; destruct H2.
      applyClassifier1 H7. rewrite H1. apply Classifier2. repeat split.
      rewrite Corollary_div_fun_c. repeat (apply Classifier1; split; auto).
      rewrite Corollary_mult_fun_c. apply Classifier1; auto.
      rewrite Corollary_mult_fun_b,Corollary_div_fun_b; auto.
      unfold Rdiv. rewrite Rmult_comm,(Rmult_comm f[x]),Rmult_assoc,
      <-(Rmult_assoc f[x]),Rinv_r_simpl_m,Rmult_comm; auto. }
  assert (limit ((g // f) \* (f \* h)) x0 (1 * A)).
  { apply Theorem3_7c; auto.
    apply Corollary_InfinitesimalEquivalent in H as [_[]]; auto. }
  rewrite Rmult_1_l,H1 in H2. apply Lemma3_12 in H2; auto.
  apply Corollary_mult_fun_a.
Qed.

Theorem Theorem3_12b : ∀ f g h x0 B, InfinitesimalEquivalent f g x0
  -> limit (h // f) x0 B -> limit (h // g) x0 B.
Proof.
  intros. assert ((h // f) \* (f // g) = (h // g)|[dom[f] ∩ \{ λ u, f[u] <> 0 \}]).
  { apply AxiomI; split; intros.
    - applyClassifier1 H1. destruct H1 as [x[y[H1[H2[]]]]]. rewrite H1.
      rewrite Corollary_div_fun_c in H2, H3. applyClassifier1 H2; destruct H2.
      applyClassifier1 H5; destruct H5. applyClassifier1 H3; destruct H3.
      applyClassifier1 H7; destruct H7. applyClassifier1 H6. applyClassifier1 H8.
      apply Classifier1. split. apply Classifier2. repeat split; auto.
      rewrite Corollary_div_fun_b, Corollary_div_fun_b in H4; auto.
      unfold Rdiv in H4. rewrite Rmult_comm,(Rmult_comm f[x]),Rmult_assoc,
      <-(Rmult_assoc f[x]),Rinv_r_simpl_m,Rmult_comm in H4; auto.
      apply Classifier2. split; apply Classifier1; auto.
    - applyClassifier1 H1. destruct H1. applyClassifier1 H1.
      destruct H1 as [x[y[H1[H3[H4[]]]]]]. rewrite H1 in H2.
      applyClassifier2 H2. destruct H2. applyClassifier1 H2; destruct H2.
      applyClassifier1 H7. applyClassifier1 H8. rewrite H1. apply Classifier2.
      repeat split; try rewrite Corollary_div_fun_c;
      repeat (apply Classifier1; split; auto). apply Classifier1; auto.
      apply Classifier1; auto. rewrite Corollary_div_fun_b; auto.
     rewrite Corollary_div_fun_b; auto. unfold Rdiv.
     rewrite Rmult_comm,(Rmult_comm f[x]),Rmult_assoc,
     <-(Rmult_assoc f[x]),Rinv_r_simpl_m,Rmult_comm; auto. }
  assert (limit ((h // f) \* (f // g)) x0 (B * 1)).
  { apply Theorem3_7c; auto. destruct H as [_[]]; auto. }
  rewrite Rmult_1_r,H1 in H2. apply Lemma3_12 in H2; auto.
  apply Corollary_div_fun_a.
Qed.

(* 无穷大量 *)
Definition limit_infinite f x0 := Function f /\ (∃ δ', δ' > 0 
  /\ Uº(x0;δ') ⊂ dom[f] /\ (∀ G, G > 0 -> ∃ δ, 0 < δ < δ'
  /\ (∀ x, 0 < ∣(x - x0)∣ < δ -> G < ∣(f[x])∣))).

Definition limit_infinite_pos f x0 := Function f /\ (∃ δ', δ' > 0
  /\ U+º(x0;δ') ⊂ dom[f] /\ (∀ G, G > 0 -> ∃ δ, 0 < δ < δ'
  /\ (∀ x, x0 < x < x0 + δ -> G < ∣(f[x])∣))).

Definition limit_infinite_neg f x0 := Function f /\ (∃ δ', δ' > 0 
  /\ U-º(x0;δ') ⊂ dom[f] /\ (∀ G, G > 0 -> ∃ δ, 0 < δ < δ'
  /\ (∀ x, x0 - δ < x < x0 -> G < ∣(f[x])∣))).

(* 定理3.13 *)
Theorem Theorem3_13a : ∀ f x0, (∃ δ', δ' > 0 /\ Uº(x0;δ') ⊂ dom[f] 
  /\ (∀ x, x ∈ Uº(x0;δ') -> f[x] <> 0))
  -> Infinitesimal f x0 -> limit_infinite (1 /// f) x0.
Proof.
  intros f x0 [δ' [H0 [H1 H2]]] H3. unfold Infinitesmal in H3.
  unfold limit in H3. destruct H3 as [H3 [δ0' [H4 [H5 H6]]]].
  assert (H7 : Function (1 /// f)).
  { unfold Function. intros x y z I1 I2. applyClassifier2 I1; applyClassifier2 I2.
    destruct I2 as [I2 [I3 I4]]. rewrite I4. apply I1. } split; auto.
  assert (H8 : ∃ δ1', δ1' > 0 /\ δ1' < δ' /\ δ1' < δ0').
  { destruct (Rlt_or_le δ' δ0') as [K1 | K1].
    - exists (δ'/2). split; lra.
    - exists (δ0'/2). split; lra. }
  destruct H8 as [δ1' [H8 [H9 H10]]]. exists δ1'.
  assert (H11 : Uº(x0; δ1') ⊂ dom[1 /// f]).
  { intros x I1. assert (I2 : x ∈ Uº(x0; δ')).
    { apply Classifier1. applyClassifier1 I1. lra. }
    apply Classifier1. exists (1/f[x]). apply Classifier2. repeat split; auto. }
  repeat split; auto. intros G H12. apply Rinv_0_lt_compat in H12 as H13.
  apply H6 in H13 as H14. destruct H14 as [δ0 [H14 H15]].
  assert (H16 : ∃ δ, δ > 0 /\ δ < δ0 /\ δ < δ1').
  { destruct (Rlt_or_le δ0 δ1') as [K1 | K1].
    - exists (δ0/2). split; lra.
    - exists (δ1'/2). split; lra. }
  destruct H16 as [δ [H16 [H17 H18]]]. exists δ. split; try lra. intros x H19.
  assert (H20 : 0 < ∣(x - x0)∣ < δ0). lra. apply H15 in H20 as H21.
  assert (H22 : x ∈ Uº(x0; δ')). { apply Classifier1. lra. }
  assert (H23 : (1 /// f) [x] = 1/f[x]).
  { apply f_x_T; auto. apply Classifier2. split; auto. }
  rewrite H23. apply H2 in H22 as H24. rewrite Abs_div; auto.
  assert (H25 : ∣1∣/∣(f[x])∣ = /∣(f[x])∣).
  { rewrite Abs_gt; lra. } rewrite H25. rewrite Rminus_0_r in H21.
  assert (H26 : 0 < ∣(f[x])∣ * (/G)).
  { apply Rmult_lt_0_compat; auto. apply Abs_not_eq_0; assumption. }
  apply Rinv_lt_contravar in H21; auto. rewrite Rinv_inv in H21. assumption.
Qed.

Theorem Theorem3_13b : ∀ f x0, limit_infinite f x0 -> Infinitesimal (1 /// f) x0.
Proof.
  intros. destruct H as [H[x[H0[]]]]. assert (Function (1 /// f)) as J.
  { red; intros. applyClassifier2 H3. applyClassifier2 H4.
    destruct H3 as [_[]], H4 as [_[]]. rewrite H5,H6; auto. }
  split; auto. assert (0 < 1). lra. apply H2 in H3 as [x1[]].
  assert (Uº(x0; x1) ⊂ dom[1 /// f]).
  { rewrite Corollary_div_fun_d. red; intros. apply Classifier1; split; auto.
    apply H1. applyClassifier1 H5. apply Classifier1. lra. apply Classifier1. intro.
    applyClassifier1 H5. apply H4 in H5. rewrite Abs_eq_0 in H6.
    rewrite H6 in H5. assert (0 < 1). lra. apply Rlt_asym in H5; auto. }
  exists x1. split. lra. split; auto. intros.
  assert (/ε > 0). { apply Rinv_0_lt_compat; auto. }
  assert (∀ x, x ∈ Uº(x0; x1) -> (1 /// f)[x] = 1/f[x]).
  { intros. assert ([x2, 1/f[x2]] ∈ (1 /// f)).
    { apply Classifier2. rewrite Corollary_div_fun_d in H5. apply H5 in H8.
      applyClassifier1 H8. destruct H8. applyClassifier1 H9. auto. }
    apply f_x_T in H9; auto. } pose proof H7.
  apply H2 in H9 as [x2[]]. destruct (Rlt_or_le x2 x1).
  - exists (x2). split. lra. intros.
    assert (x3 ∈ Uº(x0; x1)). { apply Classifier1; lra. }
    apply H10 in H12. rewrite H8; auto. assert (0 < ∣(f[x3])∣). lra.
    apply Rinv_lt_contravar in H12. rewrite Rminus_0_r. rewrite Abs_div.
    rewrite Abs_ge; [ | lra]. rewrite Rinv_inv in H12. unfold Rdiv.
    rewrite Rmult_1_l; auto. intro. rewrite H15 in H14.
    rewrite Abs_ge in H14. apply Rlt_irrefl in H14; auto. right; auto.
    apply Rmult_lt_0_compat; auto.
  - exists (x1/2). split. lra. intros.
    assert (0 < ∣(x3 - x0)∣ < x2). lra.
    assert (x3 ∈ Uº(x0; x1)). { apply Classifier1; lra. }
    apply H10 in H13. rewrite H8; auto. assert (0 < ∣(f[x3])∣). lra.
    apply Rinv_lt_contravar in H13. rewrite Rminus_0_r. rewrite Abs_div.
    rewrite Abs_ge; [ | lra]. rewrite Rinv_inv in H13. unfold Rdiv.
    rewrite Rmult_1_l; auto. intro. rewrite H16 in H15.
    rewrite Abs_ge in H15. apply Rlt_irrefl in H15; auto. right; auto.
    apply Rmult_lt_0_compat; auto.
Qed.