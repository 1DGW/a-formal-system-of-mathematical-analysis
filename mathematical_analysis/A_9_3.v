(** A_9_3 *)
(* 可积条件 *)

Require Export A_9_6.

(* 9.3.1 可积的必要条件 *)

(* 函数在区间上无界, 则在分割的某个小区间上无界 *)
Lemma Lemma9_2a : ∀ f T n a b, (Seg T a b (S n)) -> ~ DBoundedFun f (\[a, b\])
  -> (∃ k, (k <= n)%nat /\ ~ DBoundedFun f (\[T[k], T[S k]\])).
Proof.
  assert (∀ f T n a b, Seg T a b (S n)
    -> (∀ k, (k <= n)%nat -> DBoundedFun f (\[T[k], T[S k]\]))
    -> DBoundedFun f (\[a, b\])).
  { intros. generalize dependent T. generalize dependent a.
    generalize dependent b. induction n.
    - intros. pose proof (H0 0%nat). assert (0 <= 0)%nat. lia. apply H0 in H2.
      destruct H as [_[_[_[_[H H']]]]]. rewrite H in H2. rewrite H' in H2. auto.
    - intros. set(T' := \{\ λ i m, (i <= S n)%nat /\ m = T[i] \}\).
      assert(J1 : Function T').
      { red. intros. applyClassifier2 H2. applyClassifier2 H1. destruct H2,H1. lra. }
      assert(J2 : ∀ k, (k <= S n)%nat -> T'[k] = T[k]).
      { intros. apply f_x_T; auto. apply Classifier2. split; auto. }
      assert (Seg T' a (T[S n]) (S n)).
      { red in H. destruct H as [H[H'[H''[H1[H1' H1'']]]]].
        repeat split; auto. lia. apply AxiomI. split; intros. apply Classifier1.
        applyClassifier1 H2. destruct H2. applyClassifier2 H2. lia. apply Classifier1.
        applyClassifier1 H2. exists T[z]. apply Classifier2. split; auto. intros.
        repeat rewrite J2; [ |lia|lia]. apply H1; lia. rewrite J2. lra. lia. }
      assert (DBoundedFun f (\[a, T[S n]\])).
      { apply IHn in H1 as H1'. auto. intros.
        repeat rewrite J2; [ |lia|lia]. apply H0; lia. }
      pose proof (H0 (S n)). assert (S n <= S n)%nat. lia. apply H3 in H4.
      clear H3. destruct H as [H[H'[H5[H5' H5'']]]]. destruct H5'' as [J3 J4].
      rewrite J4 in H4. destruct H2 as [H2[H6 H6']]. destruct H4 as [_[H7 H7']].
      split; auto. cut((S n) < S (S n))%nat; intros; [ |lia]. split.
      + red; intros. applyClassifier1 H4. destruct (classic (z <= T [S n])).
        apply H6. apply Classifier1. split; lra. apply H7. apply Rnot_le_gt in H8.
        apply Classifier1. split; lra.
      + destruct H6' as [M H6']. destruct H7' as [M' H7'].
        exists (∣M∣ + ∣M'∣). intros. applyClassifier1 H4.
        assert(∀ M M', ∣M∣ + ∣M'∣ >= M).
        { intros. destruct(Abs_neg_pos M0). pose proof (Abs_Rge0 M'0). lra. }
        destruct (classic (x <= T[S n])). pose proof (H8 M M').
        assert(∣(f[x])∣ <= M). apply H6'. apply Classifier1; split; lra. lra.
        apply Rnot_le_gt in H9. pose proof (H8 M' M).
        assert(∣(f[x])∣ <= M'). apply H7'. apply Classifier1; split; lra. lra. }
    intros. apply NNPP. intro.
    assert (∀ k, (k <= n)%nat -> DBoundedFun f (\[T[k], T[S k]\])).
    { intros. red in H2. apply NNPP. intro. apply H2. exists k. split; auto. }
    apply (H f T n a b ) in H3; auto.
Qed.

(* 区间的平均分割 *)
Lemma Lemma9_2b : ∀ a b n, a < b
  -> ∃ T, T = \{\ λ k v, (k = O /\ v = a) \/ (k = S n /\ v = b)
      \/ ((0 < k < S n)%nat /\ v = (INR k) * (b - a) / (INR(S n)) + a) \}\
    /\ Seg T a b (S n).
Proof.
  intros a b n J.
  assert(∃ T, T = \{\ λ k v, (k = 0%nat /\ v = a) \/ (k = S n /\ v = b)
    \/ ((0< k < S n)%nat /\ v = (INR k) * (b - a) / (INR(S n)) + a) \}\).
  { exists \{\ λ k v, (k = 0%nat /\ v = a) \/ (k = S n /\ v = b)
    \/ ((0< k < S n)%nat /\ v = (INR k) * (b - a) / (INR(S n)) + a) \}\; auto. }
  destruct H as [T]. exists T. split. auto. assert(L1 : Function T).
  { rewrite H. red. intros. applyClassifier2 H0. applyClassifier2 H1.
    destruct H0 as [[H0 H0']|[[H0 H0']|[H0 H0']]];
    destruct H1 as [[H1 H1']|[[H1 H1']|[H1 H1']]]; try lia; lra. }
  split; auto. split. lia. assert(T[0%nat] = a).
  { rewrite H. apply f_x_T. rewrite <- H. auto. apply Classifier1.
    exists 0%nat,a. split; auto. }
  assert(T[S n] = b).
  { rewrite H. apply f_x_T. rewrite <-H. auto.
    apply Classifier1. exists (S n),b. split; auto. }
  assert(L4 : ∀ k, (0 < k < S n)%nat -> T[k] = (INR k) * (b - a) / (INR (S n)) + a).
  { intros. rewrite H. apply f_x_T. rewrite <- H; auto. apply Classifier1.
    exists k,((INR k) * (b - a) / (INR (S n)) + a). auto. }
  split. apply AxiomI. split; intros. rewrite H in H2. apply Classifier1. 
  applyClassifier1 H2. destruct H2 as [y]. applyClassifier2 H2.
  destruct H2 as [[H2 H2']|[[H2 H2']|[H2 H2']]];[lia|lia|lia].
  applyClassifier1 H2. apply Classifier1. rewrite H. destruct (classic (z = 0)%nat).
  exists a. apply Classifier2. left; split; auto. destruct(classic (z = S n)%nat).
  exists b. apply Classifier2. right;left. split; auto.
  exists ((INR z) * (b - a) / (INR (S n)) + a).
  apply Classifier2; right; right; split; [lia|auto]. split; auto.
  intros. destruct (Nat.eq_dec k O). rewrite e. destruct (Nat.eq_dec n O).
  rewrite e0 in H1. rewrite H0; rewrite H1; lra. rewrite (L4 1%nat).
  assert ((INR 1) * (b - a) / (INR (S n)) > 0).
  { apply Rmult_gt_0_compat. apply Rmult_gt_0_compat. simpl; lra. lra.
    apply Rinv_0_lt_compat. rewrite S_INR. rewrite Rplus_comm.
    apply Rplus_lt_le_0_compat. lra. apply pos_INR. }
  rewrite H0. lra. split; lia. rewrite (L4 k); [ |lia].
  destruct (Nat.eq_dec (S k) (S n)). rewrite e. rewrite H1. inversion e.
  apply (Rplus_lt_reg_r (-a) ((INR n) * (b - a) / (INR (S n)) + a) b).
  replace ((INR n) * (b - a) / (INR (S n)) + a + -a)
  with ((INR n) * (b - a) / (INR (S n))); [ |lra].
  replace (b + -a) with (b - a); [ |lra]. unfold Rdiv.
  rewrite Rmult_assoc,(Rmult_comm (b - a)),<-Rmult_assoc.
  apply (Rmult_lt_reg_r (/(b - a)) ((INR n) * / (INR (S n)) * (b - a)) (b - a)).
  apply Rinv_0_lt_compat; lra. rewrite Rmult_assoc. rewrite Rinv_r.
  rewrite Rmult_1_r. apply (Rmult_lt_reg_r (INR (S n)) ((INR n) * /(INR (S n))) 1).
  apply lt_0_INR. lia. rewrite Rmult_comm,<-Rmult_assoc,Rinv_r_simpl_m,Rmult_1_l.
  apply lt_INR. lia. apply not_0_INR. lia. lra. rewrite (L4 (S k)); [ |lia].
  apply (Rplus_lt_reg_r (-a) ((INR k) * (b - a) / (INR (S n)) + a)
  ((INR (S k)) * (b - a) / (INR (S n)) + a)).
  replace ((INR k) * (b - a) / (INR (S n)) + a + -a)
  with ((INR k) * (b - a) / (INR (S n))); [ |lra].
  replace ((INR (S k)) * (b - a) / (INR (S n)) + a + -a)
  with (INR (S k) * (b - a) / (INR (S n))); [ |lra]. unfold Rdiv.
  apply (Rmult_lt_reg_r (INR (S n)) ((INR k) * (b - a) * /(INR (S n)))
  ((INR (S k)) * (b - a) * /(INR (S n)))). apply lt_0_INR. lia.
  apply Rmult_lt_compat_r. apply lt_0_INR. lia. apply Rmult_lt_compat_r.
  apply Rinv_0_lt_compat,lt_0_INR. lia. apply Rmult_lt_compat_r. lra.
  apply lt_INR. lia.
Qed.

(* 区间的平均分割补充 *)
Lemma Lemma9_2c : ∀ a b n, a < b
  -> ∃ T, T = \{\ λ k v, (k = O /\ v = a) \/ (k = S n /\ v = b)
      \/ ((0 < k < S n)%nat /\ v = (INR k) * (b - a) / (INR (S n)) + a) \}\
    /\ Seg T a b (S n)
    /\ (∀ n', (n' <= n)%nat -> T[S n'] - T[n'] = (b - a)/(INR (S n))).
Proof.
  intros. apply (Lemma9_2b a b n) in H. destruct H as [T[]]. exists T.
  split; auto. split; auto. intros. destruct H0 as [H0[H2[H3[H4[]]]]].
  assert(∀ k, (0 < k < S n)%nat -> T[k] = (INR k) * (b - a) / (INR (S n)) + a).
  { intros. apply f_x_T; auto. rewrite H. apply Classifier2. right. right.
    split; auto. }
  destruct (Nat.eq_dec n' 0%nat). rewrite e. rewrite H5.
  destruct (Nat.eq_dec n 0%nat). subst n. rewrite H6.
  unfold Rdiv; rewrite RMicromega.Rinv_1; auto. rewrite H7; [ |lia].
  rewrite Rmult_1_l. unfold Rminus. rewrite Rplus_assoc. rewrite Rplus_opp_r. lra.
  destruct (Nat.eq_dec n' (S n)). subst n'. rewrite H6. rewrite H7; [ |lia].
  cut(INR (S (S n)) = INR (S n) + 1); intros. rewrite H8.
  unfold Rdiv; repeat rewrite Rmult_plus_distr_r. rewrite Rinv_r_simpl_m. lra.
  apply not_0_INR. apply Nat.neq_succ_0. rewrite (S_INR (S n)). auto.
  rewrite (H7 n'); [ |lia]. destruct (Nat.eq_dec n' n). subst n'. rewrite H6.
  unfold Rminus. rewrite Ropp_plus_distr. rewrite <-Rplus_comm.
  rewrite (Rmult_eq_reg_r (INR (S n)) (-((INR n) * (b + -a) / (INR (S n)))
    + -a + b) ((b + -a)/(INR (S n)))). auto.
  assert ((-((INR n) * (b + -a) / (INR (S n))) + -a + b)
    = -((INR n) * (b + -a) / (INR (S n))) + (-a + b)). lra.
  rewrite H8. clear H8. rewrite Rmult_plus_distr_r. unfold Rdiv.
  replace ((b + -a) * /(INR (S n)) * (INR (S n)))
  with ((b + -a) * (INR (S n)) * /(INR (S n))). rewrite Rinv_r_simpl_l.
  replace (-((INR n) * (b + -a) * /(INR (S n))) * (INR (S n)))
  with (-((INR n) * (b + -a))). replace (-a + b) with (b + -a).
  rewrite Ropp_mult_distr_l. replace ((b + -a) * (INR (S n)))
  with ((INR (S n)) * (b + -a)). rewrite <-Rmult_plus_distr_r.
  replace (-(INR n) + (INR (S n))) with (INR 1). simpl. lra.
  replace (INR (S n)) with (INR (1 + n)).
  replace (INR (1 + n)) with ((INR 1) + (INR n)). lra. rewrite plus_INR; auto.
  replace (1 + n)%nat with (S n). auto. simpl. auto. lra. lra.
  rewrite Ropp_mult_distr_l_reverse. apply Ropp_eq_compat.
  replace ((INR n) * (b + -a) * /(INR (S n)) * (INR (S n)))
  with ((INR n) * (b + -a) * (/(INR (S n)) * (INR (S n)))). rewrite Rinv_l. lra.
  apply not_0_INR. auto. lra. apply not_0_INR. auto. rewrite Rmult_assoc.
  rewrite Rmult_assoc. apply Rmult_eq_compat_l. apply Rmult_comm.
  apply not_0_INR. auto. apply not_eq_S in n2. rewrite H7; [ |lia].
  apply (Rmult_eq_reg_r (INR (S n)) ((INR (S n')) * (b - a) / (INR (S n)) + a
    - ((INR n') * (b - a) / (INR (S n)) + a)) ((b - a)/(INR (S n)))).
  replace ((INR (S n')) * (b - a) / (INR (S n)) + a
    - ((INR n') * (b - a) / (INR (S n)) + a))
  with ((INR (S n')) * (b - a) / (INR (S n))
    + (a - ((INR n') * (b - a) / (INR (S n)) + a))).
  rewrite Rmult_plus_distr_r,Rmult_minus_distr_r,Rmult_plus_distr_r.
  replace ((INR (S n')) * (b - a) / (INR (S n)) * (INR (S n)))
  with ((INR (S n')) * (b - a)). replace ((INR n') * (b - a) / (INR (S n))
    * (INR (S n))) with ((INR n') * (b - a)).
  replace ((b - a) / (INR (S n)) * (INR (S n))) with ((b - a)).
  replace ((a * (INR (S n)) - ((INR n') * (b - a) + a * (INR (S n)))))
  with (-(INR n') * (b - a)). rewrite <-Rmult_plus_distr_r.
  replace ((INR (S n')) + -(INR n')) with (INR 1). simpl. lra.
  replace (S n') with (1 + n')%nat. rewrite plus_INR. lra.
  simpl. auto. lra. unfold Rdiv. rewrite Rmult_assoc. rewrite Rinv_l. lra.
  apply not_0_INR. auto. unfold Rdiv. rewrite Rmult_assoc. rewrite Rinv_l. lra.
  apply not_0_INR. auto. unfold Rdiv. rewrite Rmult_assoc. rewrite Rinv_l. lra.
  apply not_0_INR. auto. lra. apply not_0_INR. auto.
Qed.

(* 阿基米德性的一种表述 *)
Lemma Lemma9_2d : ∀ A δ, A > 0 -> δ > 0 -> ∃ n, A/(INR(S n)) < δ.
Proof.
  intros. pose proof H0 as H0'. apply (Archimedes δ A) in H0; auto.
  destruct H0. exists x. assert (INR (S x) * δ > A).
  { replace (S x) with (x + 1)%nat; [ |lia]. rewrite plus_INR. simpl. lra. }
  apply (Rmult_lt_compat_r (/(INR (S x)))) in H1.
  rewrite Rmult_inv_r_id_m in H1; auto. apply not_0_INR. lia.
  apply Rinv_0_lt_compat. apply lt_0_INR. lia.
Qed.

(* 两个求和式只有一项不相等时, 求和值减去该项后相等 *)
Lemma Lemma9_2e : ∀ ξ ξ' k n, (0 <= k <= n)%nat
  -> (∀ i, i <> k -> (i < S n)%nat -> ξ'[i] = ξ[i])
  -> Σ ξ' n - ξ'[k] = Σ ξ n - ξ[k].
Proof.
  intros. generalize dependent k. induction n.
  - intros. simpl. assert (k = 0%nat). lia. rewrite H1. lra.
  - intros. destruct (classic (k = S n)). rewrite H1. simpl.
    assert (Σ ξ' n = Σ ξ n).
    { clear IHn. clear H. assert (∀ m, (m <= n)%nat -> ξ'[m] = ξ[m]).
      { intros. apply H0; [rewrite H1| ]; lia. } clear H0 H1. induction n. simpl.
      apply H; auto. simpl. rewrite H; auto. rewrite IHn; auto. }
    rewrite H2. lra. assert (0 <= k <= n)%nat. lia. apply IHn in H2. simpl.
    rewrite Rplus_comm. unfold Rminus in *. rewrite Rplus_assoc,H2.
    rewrite H0; auto. lra. intros. apply H0; auto.
Qed.


(* 定理9.2 可积的必要条件 *)
Theorem Theorem9_2 : ∀ f a b J, Function f -> a < b
  -> Def_Integral f a b J -> DBoundedFun f (\[a, b\]).
Proof.
  intros. red in H1. destruct H1 as [_[_[H1 H2]]].
  assert(∃ M, M > 0 /\ M > ∣J∣).
  { exists  (2 * ∣J∣ + 1). pose proof(Abs_Rge0 J); lra. }
  destruct H3 as [M[H3 H3']]. assert(M - ∣J∣ > 0). lra.
  apply H2 in H4 as H4'. destruct H4' as [δ[H6 H5]].
  assert (∃ n, (b - a)/(INR (S n)) < δ). { apply Lemma9_2d. lra. auto. }
  clear H2. destruct H7 as [n]. destruct (Lemma9_2c a b n H0) as [T[H8[H9 L1]]].
  apply NNPP. intro I1. assert(∃ k, (k <= n)%nat
    /\ ~ (DBoundedFun f (\[T[k], T[S k]\]))).
  { apply (Lemma9_2a f T n a b); auto. } destruct H7 as [k[H10 H11]].
  assert(∀ M, ∃ x, x ∈ \[T[k], T[S k]\] /\ ∣(f[x])∣ > M).
  { intros. red in H11. apply NNPP. intro. apply H11. red. split; auto. split.
    assert (\[T[k], T[S k]\] ⊂ \[a, b\]). apply (Seg_subInterval T a b n k); auto.
    red. intros. apply H1. apply H12. auto. exists M0. intros. apply NNPP. intro.
    apply H7. exists x. split; auto. apply Rnot_le_gt in H13. auto. }
  assert (∃ ξ, ξ = \{\ λ m v, v = T[m] \}\).
  { exists (\{\ λ m v, v = T[m] \}\). split; auto. } destruct H12 as [ξ' H13].
  assert(∃ G', G' = Σ \{\ λ i s, s = f[ξ'[i]] * (T[S i] - T[i]) \}\ n
    - f[ξ'[k]] * (T[S k] - T[k])). eauto. destruct H12 as [G'].
  assert((M + ∣G'∣)/(T[S k] - T[k]) > 0).
  { unfold Rdiv. apply Rmult_gt_0_compat. pose proof (Abs_Rge0 G'). lra.
    apply Rinv_0_lt_compat. red in H9. destruct H9 as [_[_[_[H9 _]]]].
    pose proof (H9 k). cut(k < S n)%nat; intros. apply H14 in H15; lra. lia. }
  pose proof (H7 ((M + ∣G'∣)/(T[S k] - T[k]))). destruct H15 as [x[H16 H17]].
  assert(K1 : Function \{\ λ m v, (m = k /\ v = x)
    \/ (m <> k /\ (m < S n)%nat /\ v = T[m]) \}\).
  { unfold Function. intros. applyClassifier2 H15; applyClassifier2 H18;
    destruct H15; destruct H18; [lra|lia|lia|lra]. }
  assert(∃ ξ, ξ = \{\ λ m v, (m = k /\ v = x)
    \/ (m <> k /\ (m < (S n))%nat /\ v = T[m]) \}\ /\ SegPoints T ξ (S n)).
  { exists \{\ λ m v, (m = k /\ v = x)
      \/ (m <> k /\ (m < S n)%nat /\ v = T[m]) \}\. split; auto.
    unfold SegPoints. intros. destruct (Nat.eq_dec k0 k).
    assert(\{\ λ m v, (m = k /\ v = x)
      \/ (m <> k /\ (m < S n)%nat /\ v = T[m]) \}\[k] = x).
    { apply f_x_T; auto. apply Classifier2. left; auto. }
    rewrite e. rewrite H18. applyClassifier1 H16. lra.
    assert(\{\ λ m v, (m = k /\ v = x)
      \/ (m <> k /\ (m < S n)%nat /\ v = T[m]) \}\[k0] = T[k0]).
    { apply f_x_T; auto. apply Classifier2. right. split; auto. }
    rewrite H18. destruct H9 as [_[_[_[H9 _]]]]. apply H9 in H15. lra. }
  destruct H15 as [ξ[H15 H15']]. assert ((mold T (S n)) < δ).
  { apply SegMold_Exists in H9 as H9'. destruct H9' as [x' H9'].
    assert (NotEmpty \{ λ x, SegMold T (S n) x \}).
    { exists x'. apply Classifier1. assumption. } apply Axiomc in H18.
    applyClassifier1 H18. destruct H18 as [H19' H20]. unfold mold.
    destruct H19' as [k'[H22 H21]]. rewrite <-H21. rewrite L1. lra. lia. }
  pose proof (H5 T ξ n H9 H15' H18).
  assert(∃ G, G = Σ \{\ λ i s, s = f[ξ[i]] * (T[S i] - T[i]) \}\ n
    - f[ξ[k]] * (T[S k] - T[k])). eauto. destruct H20 as [G].
  assert(Σ \{\ λ i s, s = f[ξ[i]] * (T[S i] - T[i]) \}\ n
    = f[ξ[k]] * (T[S k] - T[k]) + G). { rewrite H20; lra. }
  assert(G = G').
  { rewrite H20. rewrite H12. assert(∃ x', x' = f[ξ[k]] * (T[S k] - T[k])). eauto.
    destruct H22. assert(∃ F, F = \{\ λ i s, s = f[ξ'[i]] * (T[S i] - T[i]) \}\).
    eauto. destruct H23 as [F'].
    assert(K3 : ∀ x', x' <> k -> (x' < S n)%nat -> ξ'[x'] = ξ[x']).
    { intros. rewrite H13; rewrite FunValue. symmetry. rewrite H15.
      apply f_x_T; auto. apply Classifier2. right; auto. }
    assert(Function \{\ λ i s, s = f[ξ'[i]] * (T[S i] - T[i]) \}\).
    red; intros. applyClassifier2 H24. applyClassifier2 H25. subst; auto.
    assert (\{\ λ i s, s = f[ξ[i]] * (T[S i] - T[i]) \}\[k]
      = (f[ξ[k]] * (T[S k] - T[k]))).
    { apply f_x_T. red; intros. applyClassifier2 H25. applyClassifier2 H26.
      subst; auto. apply Classifier2; auto. } rewrite <-H25.
    assert(\{\ λ i s, s = f[ξ'[i]] * (T[S i] - T[i]) \}\[k]
      = f[ξ'[k]] * (T[S k] - T[k])).
    { apply f_x_T. red; intros. applyClassifier2 H26. applyClassifier2 H27.
      subst; auto. apply Classifier2; auto. } rewrite <-H26.
    apply Lemma9_2e; auto. lia. intros. repeat rewrite FunValue.
    rewrite K3; auto. } unfold IntegralSum in H19.
  rewrite H21 in H19. pose proof (Abs_abs_minus' (f[ξ[k]] * (T[S k] - T[k])) (-G)).
  rewrite <-Abs_eq_neg in H23. unfold Rminus in H23.
  rewrite Ropp_involutive in H23. assert(ξ[k] = x).
  { red in H15'. rewrite H15; apply f_x_T; auto. apply Classifier2; left; auto. }
  assert(∣(f[ξ[k]] * (T[S k] - T[k]))∣ - ∣G∣
    > (M + ∣G'∣) / (T[S k] - T[k]) * (T[S k] - T[k]) - ∣G∣).
  { cut(T[S k] - T[k] > 0). intros L4. unfold Rminus.
    apply Rplus_gt_compat_r. unfold Rdiv. pattern (T[S k] + -T[k]) at 1.
    rewrite (Rmult_comm _ (T[S k] + -T[k])),<-Rmult_assoc,Rinv_r_simpl_m.
    apply (Rmult_gt_compat_r (T[S k] - T[k])) in H17; auto.
    unfold Rdiv in H17. pattern (T[S k] - T[k]) in H17 at 1.
    rewrite (Rmult_comm _ (T[S k] - T[k])),<-Rmult_assoc,Rinv_r_simpl_m in H17.
    rewrite Abs_mult,(Abs_gt (T[S k] + - T[k])); auto. subst x. lra. lra.
    red in H9. destruct H9 as [_[_[_[H9 _]]]]. lra. apply Rgt_minus,H9; lia. }
  pose proof (Abs_abs_minus' (f[ξ[k]] * (T[S k] - T[k]) + G) J).
  assert(∣(f[ξ[k]] * (T[S k] - T[k]) + G)∣ < M). lra.
  assert((M + ∣G'∣) / (T[S k] - T[k]) * (T[S k] - T[k]) - ∣G∣ = M).
  rewrite <-H22. unfold Rdiv. rewrite Rmult_assoc; rewrite Rinv_l. lra.
  red in H9. destruct H9 as [_[_[_[H9 _]]]]. apply Rminus_eq_contra.
  apply Rgt_not_eq. apply H9. lia. unfold Rminus in *. lra.
Qed.


(* 9.3.2 可积的充要条件 *)

Print sup_fD. (* 函数值的上确界 *)
Print Up_sum. (* 上和 *)
Print inf_fD. (* 函数值的下确界 *)
Print Up_sum. (* 下和 *)


(* 充要条件中必须含有 有界 的条件, 否则无法讨论上和与下和 *)
Theorem Theorem9_3a : ∀ f a b, a < b -> (∃ J, Def_Integral f a b J)
  <-> ((DBoundedFun f (\[a, b\])) /\ (∀ δ, δ > 0
    -> ∃ T n, Seg T a b (S n) /\ (Up_sum f T n) - (Low_sum f T n) < δ)).
Proof.
  split; intros. pose proof H0 as [J]. apply Theorem9_2 in H1; auto.
  split; auto. apply Theorem9_15; auto. destruct H1; auto.
  destruct H0. apply Theorem9_15; auto.
Qed.

(* 定义 振幅 *)
Definition amp f D := (sup_fD f D) - (inf_fD f D).

(* 振幅乘区间长度之和 等于 上和减下和 *)
Corollary Corollary_amp : ∀ f T a b n, DBoundedFun f (\[a, b\]) -> Seg T a b (S n)
  -> (Up_sum f T n) - (Low_sum f T n)
    = Σ \{\ λ u v, v = (amp f (\[T[u], T[S u]\])) * (T[S u] - T[u]) \}\ n.
Proof. intros. rewrite <-(sum3_Fact f T a b); auto. Qed.

Theorem Theorem9_3b : ∀ f a b, a < b -> (∃ J, Def_Integral f a b J)
  <-> ((DBoundedFun f (\[a, b\])) /\ (∀ δ, δ > 0 -> ∃ T n, Seg T a b (S n)
    /\ (Σ \{\ λ u v, v = (amp f (\[T[u], T[S u]\])) * (T[S u] - T[u]) \}\ n) < δ)).
Proof.
  assert (∀ f T a b n, DBoundedFun f (\[a, b\]) -> Seg T a b (S n)
    -> (Up_sum f T n) - (Low_sum f T n)
      = Σ \{\ λ u v, v = (amp f (\[T[u], T[S u]\])) * (T[S u] - T[u]) \}\ n).
  { intros. rewrite <-(sum3_Fact f T a b); auto. }
  split; intros. pose proof H1 as [J]. apply Theorem9_2 in H2; auto.
  split; auto. intros. pose proof H2. apply Theorem9_15 in H4 as [H4 _]; auto.
  pose proof (H4 H1 δ H3) as [T[n[]]]. exists T,n. split; auto.
  rewrite <-(H f T a b); auto. destruct H2; auto. destruct H1.
  apply Theorem9_15; auto. intros. apply H2 in H3 as [T[n[]]].
  exists T,n. rewrite (H f T a b); auto.
Qed.

(* 9.3.3 可积函数类(可积的充分条件) *)
Theorem Theorem9_4 : ∀ f a b, a < b -> ContinuousClose f a b
 -> ∃J, Def_Integral f a b J.
Proof.
  intros. pose proof H0. apply Lemma4_6 in H1. pose proof H0.
  apply Theorem4_9 in H2 as [H2[]]. apply Theorem9_3b; auto. split; auto.
  intros. set (ε := δ/2). assert (b - a > 0). lra. assert (ε > 0). unfold ε. lra.
  assert (ε/(b-a) > 0). { apply Rlt_gt,Rdiv_lt_0_compat; auto. }
  apply H4 in H8 as [δ0[]]. destruct (Examp1 (δ0/2) (b-a)) as [r[H10[]]]; auto.
  lra. assert (0 < r <= b - a). lra. apply Seg_Exists in H13 as [T[n[]]]; auto.
  assert (ε/(b - a) * (Σ \{\ λ u v, v = T[S u] - T[u] \}\ n)
    = (Σ \{\ λ u v, v = ε/(b - a) * (T[S u] - T[u]) \}\ n)).
  { clear H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14.
    induction n. simpl. rewrite FunValue,FunValue; auto. simpl.
    rewrite FunValue,FunValue,Rmult_plus_distr_l,IHn; auto. }
  assert ((Σ \{\ λ u v, v = (amp f (\[T[u], T[S u]\])) * (T[S u] - T[u]) \}\ n)
    <= (Σ \{\ λ u v, v = ε/(b - a) * (T[S u] - T[u]) \}\ n)).
  { apply Rge_le,Σ_Fact3. intros. rewrite FunValue,FunValue.
    apply Rmult_ge_compat_r. destruct H13 as [H13[H17[H18[]]]].
    assert (i < S n)%nat. lia. apply H19 in H21. lra.
    assert ((\[T[i], T[S i]\]) ⊂ (\[a, b\])).
    { apply (Seg_subInterval T a b n); auto. }
    assert (DBoundedFun f (\[T[i], T[S i]\])).
    { destruct H1 as [H1[H18[]]]. split; auto. split; eauto. red; auto. }
    assert (NotEmpty (\[T[i], T[S i]\])).
    { exists ((T[i] + T[S i])/2). apply Classifier1. destruct H13 as [H13[H19[H20[]]]].
      assert (i < S n)%nat. lia. apply H21 in H23. lra. }
    pose proof H18. apply sup_Coro_1 in H20 as [H20a H20b]; auto.
    pose proof H18. apply inf_Coro_1 in H20 as [H21a H21b]; auto.
    assert (∀ x, x ∈ \[T[i], T[S i]\] -> f[x] ∈ ran[f|[\[T[i], T[S i]\]]]).
    { intros. apply Classifier1. exists x. apply Classifier1. split.
      apply x_fx_T; auto. apply Classifier2; split; auto. apply Classifier1; auto. }
    set (A := \{ λ u, ∃ x1 x2, x1 ∈ \[T[i], T[S i]\] /\ x2 ∈ \[T[i], T[S i]\]
      /\ ∣(x1 - x2)∣ < δ0 /\ u = ∣(f[x1] - f[x2])∣ \}).
    assert (Upper A (amp f (\[T[i], T[S i]\]))).
    { red; intros. apply Classifier1 in H21 as [x1[x2[H21[H22[]]]]].
      destruct (Rle_or_lt 0 (f[x1] - f[x2])). apply Rle_ge,Abs_ge in H25.
      apply H20,H20a in H21. apply H20,H21a in H22. rewrite H24,H25.
      unfold amp. lra. apply Abs_lt in H25. apply H20,H20a in H22.
      apply H20,H21a in H21. rewrite H24,H25. unfold amp. lra. }
    assert (sup A (amp f (\[T[i], T[S i]\]))).
    { split; auto. intros. set (m := ((amp f (\[T[i], T[S i]\])) - a0)/2).
      assert (0 < m). unfold m. lra.
      assert ((inf_fD f (\[a, b\])) <= (sup_fD f (\[a, b\]))).
      { apply sup_inf_Coro_2; auto. exists ((a + b)/2). apply Classifier1. lra. }
      assert ((sup_fD f (\[T[i], T[S i]\])) - m < (sup_fD f (\[T[i], T[S i]\]))
        /\ (inf_fD f (\[T[i], T[S i]\])) < (inf_fD f (\[T[i], T[S i]\])) + m)
      as []. split; lra. apply H20b in H25 as [y1[]]. apply H21b in H26 as [y2[]].
      apply Classifier1 in H25 as [x1], H26 as [x2]. apply Classifier1 in H25 as [],
      H26 as []. applyClassifier2 H29. applyClassifier2 H30.
      destruct H29 as [H29 _], H30 as [H30 _].
      assert (∣(x1 - x2)∣ < δ0).
      { assert (T[S i] - T[i] <= (mold T (S n))).
        { apply (SegMold_Max T a b (S n)); auto. lia. }
        applyClassifier1 H29. applyClassifier1 H30.
        assert (x1 - x2 <= T[S i] - T[i] /\ x2 - x1 <= T[S i] - T[i]) as [].
        lra. rewrite <-H14 in H31. destruct (Rle_or_lt 0 (x1-x2)).
        apply Rle_ge,Abs_ge in H34. rewrite <-H34 in H32. lra.
        apply Abs_lt in H34. rewrite Ropp_minus_distr in H34.
        rewrite <-H34 in H33. lra. }
      apply f_x_T in H25,H26; auto. exists (∣(y1-y2)∣). split.
      apply Classifier1. exists x1,x2. rewrite <-H25,<-H26; auto.
      assert (y1 - y2 > (amp f (\[T[i], T[S i]\])) - 2*m). unfold amp. lra.
      assert ((amp f (\[T[i], T[S i]\])) - 2*m = a0). unfold m. lra.
      rewrite H33 in H32. destruct (Rle_or_lt 0 a0). rewrite Abs_ge; auto.
      lra. assert (∣(y1-y2)∣ >= 0). apply Abs_Rge0. lra. }
    destruct (Rge_or_gt (ε/(b - a)) (amp f (\[T[i], T[S i]\]))); auto.
    apply H22 in H23 as [y[]]. apply Classifier1 in H23 as [x1[x2[H23[H25[]]]]].
    apply H9 in H26; auto. rewrite <-H27 in H26. exfalso. lra. }
  assert (Σ \{\ λ u v, v = ε/(b - a) * (T[S u] - T[u]) \}\ n = ε).
  { rewrite <-H15,(Lemma9_6_1c T n a b); auto. unfold Rdiv. rewrite
    Rmult_assoc,Rmult_comm,(Rmult_comm (/(b-a))),Rinv_r_simpl_r; auto. lra. }
  rewrite H17 in H16. assert (ε < δ). unfold ε. lra. exists T,n. split; auto. lra.
Qed.


(* 引理 若函数f在[a,b]的a处间断, 函数仍可积 *)
Lemma Lemma9_5a : ∀ f a b, a < b -> DBoundedFun f (\[a, b\])
  -> ContinuousOC f a b -> ~ ContinuousRight f a
  -> (∃ J, Def_Integral f a b J).
Proof.
  intros. pose proof H0. apply sup_inf_Coro_2 in H3.
  assert ((inf_fD f (\[a, b\])) <> (sup_fD f (\[a, b\]))).
  { intro. pose proof (sup_inf_Coro_3 f (\[a, b\]) H0 H4).
    elim H2. destruct H0 as [H0[]]. split. apply H6,Classifier1. lra.
    split; auto. exists (b-a). split. lra. split. red; intros.
    apply Classifier1 in H8 as []. apply H6,Classifier1. lra. intros.
    exists ((b-a)/2). split. lra. intros. rewrite H5,H5,Rminus_diag,Abs_ge; auto.
    lra. apply Classifier1. lra. apply Classifier1. lra. }
  destruct H3; [ |contradiction]. clear H4.
  apply Theorem9_3b; auto. split; auto. intros.
  set (ε := δ/(2 * ((sup_fD f (\[a, b\])) - (inf_fD f (\[a, b\]))))).
  assert (0 < ε). { apply Rdiv_lt_0_compat; lra. }
  destruct (Examp1 ε (b-a)) as [δ0[H6[]]]; auto. lra.
  assert (0 <= (amp f (\[a, a+δ0\]))).
  { unfold amp. assert (DBoundedFun f (\[a, a+δ0\])).
    { destruct H0 as [H0[H9[]]]. split; auto. assert (\[a, a+δ0\] ⊂ \[a, b\]).
      { red; intros. applyClassifier1 H11. apply Classifier1. lra. }
      split; eauto. red; auto. }
    apply sup_inf_Coro_2 in H9. lra. exists ((a + (a + δ0))/2).
    apply Classifier1. lra. }
  assert (((sup_fD f (\[a, b\])) - (inf_fD f (\[a, b\]))) * ε = δ/2).
  { unfold ε. unfold Rdiv. rewrite Rinv_mult,Rmult_comm,Rmult_assoc,
    Rmult_assoc,Rinv_l; auto; lra. }
  assert ((amp f (\[a, a+δ0\])) <= (sup_fD f (\[a, b\])) - (inf_fD f (\[a, b\]))).
  { assert (\[a, a+δ0\] ⊂ \[a, b\]).
    { red; intros. applyClassifier1 H11. apply Classifier1. lra. }
    assert (NotEmpty (\[a, a+δ0\])).
    { exists ((a + (a+δ0))/2). apply Classifier1. lra. }
    pose proof H11. apply (sup_Coro_2 f) in H11; auto.
    apply (inf_Coro_2 f) in H13; auto. unfold amp. lra. }
  assert ((amp f (\[a, a+δ0\])) * δ0 < δ/2).
  { destruct H11. rewrite <-H10. apply Rmult_gt_0_lt_compat; auto. lra.
    destruct H9. rewrite <-H10,H11. apply Rmult_lt_compat_l; auto. lra.
    rewrite <-H9. lra. }
  assert (ContinuousClose f (a + δ0) b).
  { destruct H1. split. red; intros. apply H1. lra. split; auto.
    apply Theorem4_1,H1. lra. }
  apply Theorem9_4 in H13; [ |lra]. apply Theorem9_3b in H13 as []; [ |lra].
  assert (δ/2 > 0). lra. apply H14 in H15 as [T[n[]]].
  set (T1 := \{\ λ u v, (u <= S (S n))%nat
    /\ (u = 0%nat -> v = a) /\ ((0 < u)%nat -> v = T[(u-1)%nat]) \}\).
  assert (Function T1).
  { red; intros. applyClassifier2 H17. applyClassifier2 H18.
    destruct H17 as [H17[]], H18 as [_[]].
    destruct x. rewrite H19,H18; auto. rewrite H20,H21; auto; lia. }
  assert (dom[T1] = \{ λ u, (u <= S (S n))%nat \}).
  { apply AxiomI; split; intros. apply Classifier1 in H18 as [].
    applyClassifier2 H18. destruct H18. apply Classifier1; auto.
    applyClassifier1 H18. apply Classifier1. destruct z. exists a.
    apply Classifier2. split; auto. split; auto. intros. exfalso. lia.
    exists T[z]. apply Classifier2. split. lia. split. intros. exfalso. lia.
    intros. simpl. rewrite Nat.sub_0_r; auto. }
  assert (∀ m, (m <= S n)%nat -> T1[S m] = T[m]).
  { intros. assert ((S m) ∈ dom[T1]). { rewrite H18. apply Classifier1. lia. }
    apply x_fx_T in H20; auto. applyClassifier2 H20. destruct H20 as [H20[]].
    rewrite H22. simpl. rewrite Nat.sub_0_r; auto. lia. }
  assert (Seg T1 a b (S (S n))).
  { split; auto. split. lia. split; auto. assert (T1[0%nat] = a).
    { apply (H17 0%nat). apply x_fx_T; auto. rewrite H18.
      apply Classifier1. lia. apply Classifier2. split. lia. split; auto.
      intros. exfalso. lia. }
    destruct H15 as [H15[H21[H22[H23[]]]]]. split. intros. destruct k.
    rewrite H20,H19,H24. lra. lia. rewrite H19,H19; try lia. apply H23. lia.
    split; auto. rewrite H19; auto. }
  exists T1,(S n). split; auto.
  assert (Σ \{\ λ u v, v = (amp f (\[T1[u], T1[S u]\]))
      * (T1[S u] - T1[u]) \}\ (S n)
    = (Σ \{\ λ u v, v = (amp f (\[T[u], T[S u]\])) * (T[S u] - T[u]) \}\ n)
      + (amp f (\[a, a+δ0\])) * δ0).
  { assert (∀ f n, Σ f (S n) = f[0%nat] + (Σ \{\ λ u v, v = f[S u] \}\ n)).
    { intros. induction n0. simpl. rewrite FunValue; auto.
      replace (Σ f0 (S (S n0))) with ((Σ f0 (S n0)) + f0[S (S n0)]); auto.
      rewrite IHn0. simpl. rewrite FunValue. lra. }
    destruct H15 as [_[_[_[_[]]]]], H20 as [_[_[_[_[]]]]].
    rewrite H21,FunValue,H20,H19,H15,Rplus_comm; [ |lia].
    replace (a + δ0 - a) with δ0; [ |lra]. apply Rplus_eq_compat_r,Σ_Fact5.
    intros. rewrite FunValue,FunValue,FunValue,H19,H19; auto. lia. }
  rewrite H21. lra. exists ((a + b)/2). apply Classifier1. lra.
Qed.

(* 引理 若函数f在[a,b]的b处间断, 函数仍可积 *)
Lemma Lemma9_5b : ∀ f a b, a < b -> DBoundedFun f (\[a, b\])
  -> ContinuousCO f a b -> ~ ContinuousLeft f b
  -> (∃ J, Def_Integral f a b J).
Proof.
  intros. pose proof H0. apply sup_inf_Coro_2 in H3.
  assert ((inf_fD f (\[a, b\])) <> (sup_fD f (\[a, b\]))).
  { intro. pose proof (sup_inf_Coro_3 f (\[a, b\]) H0 H4).
    elim H2. destruct H0 as [H0[]]. split. apply H6,Classifier1. lra.
    split; auto. exists (b-a). split. lra. split. red; intros.
    apply Classifier1 in H8 as []. apply H6,Classifier1. lra. intros.
    exists ((b-a)/2). split. lra. intros. rewrite H5,H5,Rminus_diag,Abs_ge; auto.
    lra. apply Classifier1. lra. apply Classifier1. lra. }
  destruct H3; [ |contradiction]. clear H4.
  apply Theorem9_3b; auto. split; auto. intros.
  set (ε := δ/(2 * ((sup_fD f (\[a, b\])) - (inf_fD f (\[a, b\]))))).
  assert (0 < ε). { apply Rdiv_lt_0_compat; lra. }
  destruct (Examp1 ε (b-a)) as [δ0[H6[]]]; auto. lra.
  assert (0 <= (amp f (\[b-δ0, b\]))).
  { unfold amp. assert (DBoundedFun f (\[b-δ0, b\])).
    { destruct H0 as [H0[H9[]]]. split; auto. assert (\[b-δ0, b\] ⊂ \[a, b\]).
      { red; intros. applyClassifier1 H11. apply Classifier1. lra. }
      split; eauto. red; auto. }
    apply sup_inf_Coro_2 in H9. lra. exists (((b - δ0) + b)/2).
    apply Classifier1. lra. }
  assert (((sup_fD f (\[a, b\])) - (inf_fD f (\[a, b\]))) * ε = δ/2).
  { unfold ε. unfold Rdiv. rewrite Rinv_mult,Rmult_comm,Rmult_assoc,
    Rmult_assoc,Rinv_l; auto; lra. }
  assert ((amp f (\[b-δ0, b\])) <= (sup_fD f (\[a, b\])) - (inf_fD f (\[a, b\]))).
  { assert (\[b-δ0, b\] ⊂ \[a, b\]).
    { red; intros. applyClassifier1 H11. apply Classifier1. lra. }
    assert (NotEmpty (\[b-δ0, b\])).
    { exists (((b-δ0) + b)/2). apply Classifier1. lra. }
    pose proof H11. apply (sup_Coro_2 f) in H11; auto.
    apply (inf_Coro_2 f) in H13; auto. unfold amp. lra. }
  assert ((amp f (\[b-δ0, b\])) * δ0 < δ/2).
  { destruct H11. rewrite <-H10. apply Rmult_gt_0_lt_compat; auto. lra.
    destruct H9. rewrite <-H10,H11. apply Rmult_lt_compat_l; auto. lra.
    rewrite <-H9. lra. }
  assert (ContinuousClose f a (b-δ0)).
  { destruct H1. split. red; intros. apply H1. lra. split; auto.
    apply Theorem4_1,H1. lra. }
  apply Theorem9_4 in H13; [ |lra]. apply Theorem9_3b in H13 as []; [ |lra].
  assert (δ/2 > 0). lra. apply H14 in H15 as [T[n[]]].
  set (T1 := T ∪ [[S (S n), b]]).
  assert (Function T1).
  { red; intros. applyClassifier1 H17. applyClassifier1 H18.
    destruct H15 as [H15[H19[H20[]]]]. destruct H17,H18. apply (H15 x); auto.
    applyClassifier1 H18. apply ProdEqual in H18 as [].
    assert (x ∈ dom[T]). { apply Classifier1; eauto. }
    rewrite H20 in H24. applyClassifier1 H24. rewrite H18 in H24. exfalso. lia.
    applyClassifier1 H17. apply ProdEqual in H17 as [].
    assert (x ∈ dom[T]). { apply Classifier1; eauto. }
    rewrite H20 in H24. applyClassifier1 H24. rewrite H17 in H24. exfalso. lia.
    applyClassifier1 H17. applyClassifier1 H18. apply ProdEqual in H17 as [], H18 as [].
    rewrite H23,H24; auto. }
  assert (dom[T1] = \{ λ u, (u <= S (S n))%nat \}).
  { destruct H15 as [H15[H18[H19[H20[]]]]]. apply AxiomI; split; intros.
    apply Classifier1 in H23 as []. apply Classifier1 in H23 as [].
    assert (z ∈ dom[T]). { apply Classifier1; eauto. }
    rewrite H19 in H24. applyClassifier1 H24; apply Classifier1. lia. applyClassifier1 H23.
    apply ProdEqual in H23 as []. rewrite H23. apply Classifier1. lia.
    applyClassifier1 H23. assert (z <= S n \/ z = S (S n))%nat as []. lia.
    apply Classifier1. exists T[z]. apply Classifier1. left. apply x_fx_T; auto.
    rewrite H19. apply Classifier1; auto. apply Classifier1. exists b. apply Classifier1.
    right. apply Classifier1. rewrite H24; auto. }
  assert (∀ m, (m <= S n)%nat -> T[m] = T1[m]).
  { intros. assert (m ∈ dom[T1]). { rewrite H18. apply Classifier1; auto. }
    apply x_fx_T in H20; auto. apply Classifier1 in H20 as [].
    apply f_x_T in H20; auto. destruct H15; auto. applyClassifier1 H20.
    apply ProdEqual in H20 as []. rewrite H20 in H19. exfalso. lia. }
  assert (Seg T1 a b (S (S n))).
  { split; auto. split. lia. split; auto.
    assert (T1[S (S n)] = b).
    { apply (H17 (S (S n))). apply x_fx_T; auto. rewrite H18.
      apply Classifier1. lia. apply Classifier1. right. apply Classifier1; auto. }
    destruct H15 as [H15[H21[H22[H23[]]]]]. split. intros.
    assert (k < S n \/ k = S n)%nat as []. lia. rewrite <-H19,<-H19; try lia.
    apply H23; auto. rewrite <-H19; [ |lia]. rewrite H27,H20,H25. lra.
    split; auto. rewrite <-H19; auto. lia. }
  exists T1,(S n). split; auto. simpl. rewrite FunValue.
  destruct H15 as [H15[H21[H22[H23[]]]]], H20 as [H20[H26[H27[H28[]]]]].
  rewrite <-H19,H25,H30; auto.
  assert (Σ \{\ λ u v, v = (amp f (\[T[u], T[S u]\])) * (T[S u] - T[u]) \}\ n
    = Σ \{\ λ u v, v = (amp f (\[T1[u], T1[S u]\])) * (T1[S u] - T1[u]) \}\ n).
  { apply Σ_Fact5. intros. rewrite FunValue,FunValue,<-H19,<-H19; auto. lia. }
  rewrite <-H31. lra. exists ((a + b)/2). apply Classifier1. lra.
Qed.

(* 引理 若函数f在[a1,a2]上可积, [a2,a3]上可积, 则[a1,a3]上可积 *)
Lemma Lemma9_5c : ∀ f a1 a2 a3, a1 < a2 < a3 -> (∃ J, Def_Integral f a1 a2 J)
  -> (∃ J, Def_Integral f a2 a3 J) -> (∃ J, Def_Integral f a1 a3 J).
Proof.
  intros. apply Theorem9_3b in H0 as [], H1 as []; try lra.
  apply Theorem9_3b. lra. assert (DBoundedFun f (\[a1, a3\])).
  { destruct H0 as [H0[H4[M1]]], H1 as [H1[H6[M2]]].
    assert (\[a1, a3\] = \[a1, a2\] ∪ \[a2, a3\]).
    { apply AxiomI; split; intros. apply Classifier1 in H8 as []. apply Classifier1.
      destruct (Rle_or_lt z a2); [left|right]; apply Classifier1; lra.
      apply Classifier1 in H8 as []; applyClassifier1 H8; apply Classifier1; lra. }
    split; auto. split. red; intros. rewrite H8 in H9.
    apply Classifier1 in H9 as []; auto. rewrite H8. destruct (Rle_or_lt M1 M2);
    [exists M2|exists M1]; intros; apply Classifier1 in H10 as []; auto.
    apply H5 in H10. lra. apply H7 in H10. lra. }
  split; auto. intros. assert (δ/2 > 0). lra. pose proof H6.
  apply H2 in H6 as [T1[n1[]]]. apply H3 in H7 as [T2[n2[]]].
  set (T := \{\ λ u v, (0 <= u <= ((S n1) + (S n2)))%nat
    /\ ((0 <= u <= (S n1))%nat -> v = T1[u])
    /\ (((S n1) < u <= ((S n1) + (S n2)))%nat -> v = T2[(u - (S n1))%nat]) \}\).
  assert (Function T).
  { red; intros. applyClassifier2 H10. applyClassifier2 H11.
    destruct H10 as [H10[]], H11 as [_[]].
    assert (0 <= x <= S n1 \/ S n1 < x <= (S n1) + (S n2))%nat as []. lia.
    rewrite H11,H12; auto. rewrite H13,H14; auto. }
  assert (dom[T] = \{ λ u, (u <= ((S n1) + (S n2)))%nat \}).
  { apply AxiomI; split; intros. apply Classifier1 in H11 as [].
    applyClassifier2 H11. destruct H11.
    apply Classifier1. lia. applyClassifier1 H11.
    assert (0 <= z <= S n1 \/ S n1 < z <= (S n1) + (S n2))%nat as []. lia.
    apply Classifier1. exists T1[z]. apply Classifier2. split. lia. split; auto.
    intros. exfalso. lia. apply Classifier1. exists T2[(z - (S n1))%nat].
    apply Classifier2. split. lia. split; auto. intros. exfalso. lia. }
  assert (∀ m, (m <= S n1)%nat -> T[m] = T1[m]).
  { intros. assert (m ∈ dom[T]). { rewrite H11. apply Classifier1. lia. }
    apply x_fx_T in H13; auto. applyClassifier2 H13. destruct H13 as [H13[]].
    rewrite H14; auto. lia. }
  assert (∀ m, ((S n1) < m <= (S n1) + (S n2))%nat
    -> T[m] = T2[(m - (S n1))%nat]).
  { intros. assert (m ∈ dom[T]). { rewrite H11. apply Classifier1. lia. }
    apply x_fx_T in H14; auto. applyClassifier2 H14. destruct H14 as [H14[]].
    rewrite H16; auto. }
  assert (Seg T a1 a3 ((S n1) + (S n2))%nat).
  { split; auto. split. lia. split; auto.
    destruct H6 as [H6[H14[H15[H16[]]]]], H7 as [H7[H19[H20[H21[]]]]].
    split. intros. assert (k <= S n1 \/ S n1 < k < (S n1) + (S n2))%nat as [].
    lia. assert (k <= n1 \/ k = S n1)%nat as []. lia. rewrite H12,H12; try lia.
    apply H16. lia. rewrite H26,H12,H13,H18,<-H22; try lia.
    replace (S (S n1) - S n1)%nat with 1%nat. apply H21. lia. lia.
    rewrite H13,H13; try lia.
    replace ((S k) - (S n1))%nat with (S (k - (S n1)%nat)); [ |lia].
    apply H21. lia. split. rewrite H12; auto. lia. rewrite H13; [ |lia].
    replace ((S n1) + (S n2) - (S n1))%nat with (S n2); auto. lia. }
  exists T,(n1 + (S n2))%nat. simpl in H14. split; auto.
  assert (∀ f m n, Σ f (S (m + n)%nat)
    = Σ f m + (Σ \{\ λ u v, v = f[S (u + m)%nat] \}\ n)).
  { intros. induction n. simpl. rewrite FunValue. simpl.
    replace (m+0)%nat with m; auto. simpl. rewrite FunValue.
    replace (m + S n)%nat with (S (m + n)%nat). rewrite IHn. simpl.
    replace (m + n)%nat with (n + m)%nat. lra. lia. lia. }
  replace (n1 + (S n2))%nat with (S (n1 + n2)%nat); [ |lia]. rewrite H15.
  assert (Σ \{\ λ u v, v = (amp f (\[T[u], T[S u]\])) * (T[S u] - T[u]) \}\ n1
    = Σ \{\ λ u v, v = (amp f (\[T1[u], T1[S u]\])) * (T1[S u] - T1[u]) \}\ n1).
  { apply Σ_Fact5. intros. rewrite FunValue,FunValue,H12,H12; auto. lia. }
  assert (Σ \{\ λ u v, v = \{\ λ u0 v0, v0 = (amp f (\[T[u0], T[S u0]\]))
    * (T[S u0] - T[u0]) \}\[S (u + n1)%nat] \}\ n2
    = Σ \{\ λ u v, v = (amp f (\[T2[u], T2[S u]\])) * (T2[S u] - T2[u]) \}\ n2).
  { apply Σ_Fact5. intros. rewrite FunValue,FunValue,FunValue. destruct x. simpl.
    destruct H6 as [_[_[_[_[]]]]], H7 as [_[_[_[_[]]]]].
    rewrite H12,H13,H18,H7; try lia.
    replace (S (S n1) - (S n1))%nat with 1%nat; auto. lia.
    rewrite H13,H13; try lia.
    replace ((S (S x + n1)) - (S n1))%nat with (S x); [ |lia].
    replace ((S (S (S x + n1))) - (S n1))%nat with (S (S x)); auto. lia. }
  rewrite H16,H17. lra.
Qed.

Theorem Theorem9_5 : ∀ f a b, a < b -> DBoundedFun f (\[a, b\])
  -> Finite (\{ λ u, a <= u <= b /\ (u = a -> ~ ContinuousRight f a)
    /\ (u = b -> ~ ContinuousLeft f b) /\ (a < u < b -> ~ Continuous f u) \})
  -> ∃ J, Def_Integral f a b J.
Proof.
  intros. destruct H1.
  - apply Fact9_6f in H1 as [n[h[H1[H2[]]]]]. generalize dependent h.
    generalize dependent a. generalize dependent b. induction n. exfalso. lia.
    intros. assert (n = 0 \/ 0 < n)%nat as []. lia.
    + assert (dom[h] = [0%nat]).
      { rewrite H3. apply AxiomI; split; intros. applyClassifier1 H6.
        apply Classifier1. lia. applyClassifier1 H6. apply Classifier1. lia. }
      assert (ran[h] = [h[0%nat]]).
      { destruct H2. apply AxiomI; split; intros. apply Classifier1 in H8 as [].
        assert (x ∈ dom[h]). { apply Classifier1; eauto. }
        apply f_x_T in H8; auto. rewrite <-H8. rewrite H6 in H9.
        applyClassifier1 H9. rewrite H9. apply Classifier1; auto. applyClassifier1 H8.
        rewrite H8. apply Classifier1. exists 0%nat. apply x_fx_T; auto.
        rewrite H6. apply Classifier1; auto. }
      assert (h[0%nat] ∈ ran[h]). { rewrite H7. apply Classifier1; auto. }
      assert (a <= h[0%nat] <= b).
      { rewrite H4 in H8. apply Classifier1 in H8 as []. auto. }
      assert (a = h[0%nat] \/ a < h[0%nat] < b \/ h[0%nat] = b) as [H10|[]]. lra.
      * assert (~ ContinuousRight f a).
        { rewrite H4 in H8. apply Classifier1 in H8 as [H8[]]. apply H11; auto. }
        assert (ContinuousOC f a b).
        { split. red; intros. apply NNPP; intro. assert (x ∈ ran[h]).
          { rewrite H4. apply Classifier1. split. lra. repeat split; intros; auto.
            exfalso. lra. }
          rewrite H7 in H14. applyClassifier1 H14. rewrite <-H10 in H14. lra.
          apply NNPP; intro. assert (b ∈ ran[h]).
          { rewrite H4. apply Classifier1. split. lra. repeat split; intros; auto.
            exfalso. lra. }
          rewrite H7 in H13. applyClassifier1 H13. rewrite <-H10 in H13. lra. }
        apply Lemma9_5a; auto.
      * assert (~ Continuous f h[0%nat]).
        { rewrite H4 in H8. apply Classifier1 in H8 as [_[_[]]]. apply H11; auto. }
        assert (\[a, h[0%nat]\] ⊂ \[a, b\] /\ \[h[0%nat], b\] ⊂ \[a, b\]) as [].
        { split; red; intros; applyClassifier1 H12; apply Classifier1; lra. }
        assert (DBoundedFun f (\[a, h[0%nat]\])
          /\ DBoundedFun f (\[h[0%nat], b\])) as [].
        { destruct H0 as [H0[H14[]]]. repeat split; eauto; try (red; auto). }
        assert (ContinuousCO f a h[0%nat]).
        { split. red; intros. apply NNPP; intro. assert (x ∈ ran[h]).
          { rewrite H4. apply Classifier1. split. lra. repeat split; intros; auto.
            exfalso. lra. exfalso. lra. }
          rewrite H7 in H18. applyClassifier1 H18. rewrite <-H18 in H16. lra.
          apply NNPP; intro. assert (a ∈ ran[h]).
          { rewrite H4. apply Classifier1. split. lra. repeat split; intros; auto.
            exfalso. lra. exfalso. lra. }
          rewrite H7 in H17. applyClassifier1 H17. lra. }
        assert (ContinuousOC f h[0%nat] b).
        { split. red; intros. apply NNPP; intro. assert (x ∈ ran[h]).
          { rewrite H4. apply Classifier1. split. lra. repeat split; intros; auto.
            exfalso. lra. exfalso. lra. }
          rewrite H7 in H19. applyClassifier1 H19. rewrite <-H19 in H17. lra.
          apply NNPP; intro. assert (b ∈ ran[h]).
          { rewrite H4. apply Classifier1. split. lra. repeat split; intros; auto.
            exfalso. lra. exfalso. lra. }
          rewrite H7 in H18. applyClassifier1 H18. lra. }
        assert (∃ J, Def_Integral f a h[0%nat] J).
        { destruct (classic (ContinuousLeft f h[0%nat])) as [H18|H18].
          apply Theorem9_4. lra. destruct H16. split; auto.
          apply Lemma9_5b; auto. lra. }
        assert (∃ J, Def_Integral f h[0%nat] b J).
        { destruct (classic (ContinuousRight f h[0%nat])) as [H19|H19].
          apply Theorem9_4. lra. destruct H17. split; auto.
          apply Lemma9_5a; auto. lra. }
        apply (Lemma9_5c f a h[0%nat] b); auto.
      * assert (~ ContinuousLeft f b).
        { rewrite H4 in H8. apply Classifier1 in H8 as [_[_[]]]. apply H8; auto. }
        assert (ContinuousCO f a b).
        { split. red; intros. apply NNPP; intro. assert (x ∈ ran[h]).
          { rewrite H4. apply Classifier1. split. lra. repeat split; intros; auto.
            exfalso. lra. }
          rewrite H7 in H14. applyClassifier1 H14. rewrite H10 in H14. lra.
          apply NNPP; intro. assert (a ∈ ran[h]).
          { rewrite H4. apply Classifier1. split. lra. repeat split; intros; auto.
            exfalso. lra. }
          rewrite H7 in H13. applyClassifier1 H13. rewrite H10 in H13. lra. }
        apply Lemma9_5b; auto.
    + intros. set (h1 := h — [[n, h[n]]]).
      assert (h[(n-1)%nat] < h[n]).
      { destruct H2. apply H6; try lia; rewrite H3; apply Classifier1; lia. }
      assert (h[(n-1)%nat] ∈ ran[h]).
      { apply Classifier1. exists (n-1)%nat. apply x_fx_T. destruct H2; auto.
        rewrite H3. apply Classifier1; lia. }
      assert (h[n] ∈ ran[h]).
      { apply Classifier1. exists n. apply x_fx_T. destruct H2; auto.
        rewrite H3. apply Classifier1; lia. }
      assert (a < h[n]). { rewrite H4 in H7. apply Classifier1 in H7 as []. lra. }
      assert (a <= h[(n-1)%nat]) as H9a.
      { rewrite H4 in H7. apply Classifier1 in H7 as []. lra. }
      assert (h[n] <= b). { rewrite H4 in H8. apply Classifier1 in H8 as []. lra. }
      set (b1 := (h[(n-1)%nat] + h[n])/2). assert (a < b1 < b). unfold b1. lra.
      assert (h[(n-1)%nat] < b1 < h[n]). unfold b1. lra.
      assert (\[a, b1\] ⊂ \[a, b\]).
      { red; intros. applyClassifier1 H13. apply Classifier1; lra. }
      assert (DBoundedFun f (\[a, b1\])).
      { destruct H0 as [H0[H14[]]]. split; auto. split; eauto. red; auto. }
      assert (dom[h1] = \{ λ u, (u < n)%nat \}).
      { apply AxiomI; split; intros. apply Classifier1 in H15 as [].
        apply Classifier1 in H15 as []. assert (z ∈ dom[h]). apply Classifier1; eauto.
        rewrite H3 in H17. applyClassifier1 H17. assert (z <> n).
        { intro. rewrite H18 in H16. apply f_x_T in H15.
          rewrite <-H15,H18 in H16. applyClassifier1 H16. elim H16.
          apply Classifier1; auto. destruct H2; auto. }
        apply Classifier1; lia. applyClassifier1 H15. apply Classifier1. exists h[z].
        apply Classifier1; split. apply x_fx_T. destruct H2; auto. rewrite H3.
        apply Classifier1; lia. apply Classifier1. intro. applyClassifier1 H16.
        apply ProdEqual in H16 as []. lia. }
      assert (Function h1).
      { red; intros. apply Classifier1 in H16 as [], H17 as [].
        destruct H2. apply (H2 x); auto. }
      assert (∀ k, (k < n)%nat -> h1[k] = h[k]).
      { intros. assert (k ∈ dom[h1]). { rewrite H15. apply Classifier1; auto. }
        apply x_fx_T in H18; auto. apply Classifier1 in H18 as [].
        apply f_x_T in H18; auto. destruct H2; auto. }
      assert (StrictlyIncreaseFun_Seq h1).
      { split; auto. intros. rewrite H15 in H18,H19. applyClassifier1 H18.
        applyClassifier1 H19. rewrite H17,H17; auto. destruct H2.
        apply H21; auto; rewrite H3; apply Classifier1; lia. }
      assert (ran[h1] = \{ λ u, a <= u <= b1
        /\ (u = a -> ~ ContinuousRight f a)
        /\ (u = b1 -> ~ ContinuousLeft f b1)
        /\ (a < u < b1 -> ~ Continuous f u) \}).
      { apply AxiomI; split; intros. apply Classifier1 in H19 as [].
        apply Classifier1 in H19 as []. assert (x <> n).
        { intro. applyClassifier1 H20. elim H20. apply Classifier1.
          apply f_x_T in H19. rewrite <-H19,H21; auto. destruct H2; auto. }
        assert (x ∈ dom[h]). { apply Classifier1; eauto. }
        rewrite H3 in H22. applyClassifier1 H22. assert (x < n)%nat. lia.
        assert (h[x] <= h[(n-1)%nat]).
        { assert (x < (n-1) \/ x = n-1)%nat as []. lia. destruct H2.
          apply H25 in H24; try (rewrite H3; apply Classifier1; lia). lra.
          rewrite H24. lra. }
        assert (z ∈ ran[h]). { apply Classifier1; eauto. }
        rewrite H4 in H25. apply Classifier1 in H25 as [H25 _]. destruct H2.
        apply f_x_T in H19; auto. rewrite <-H19 in H25. rewrite <-H19.
        apply Classifier1. split. lra.
        assert (x ∈ dom[h]). { rewrite H3. apply Classifier1; lia. }
        assert (h[x] ∈ ran[h]). { apply Classifier1. exists x. apply x_fx_T; auto. }
        rewrite H4 in H28. apply Classifier1 in H28 as [H28[H29[]]].
        split; auto. split. intros. exfalso. lra. intros. apply H31. lra.
        apply Classifier1 in H19 as [H19[H20[]]].
        destruct (classic (z = h[n])) as [H23|H23]. exfalso. lra.
        assert (z ∈ ran[h]).
        { rewrite H4. apply Classifier1. split. lra. split; auto. split; intros.
          exfalso. lra. assert (z < b1 \/ z = b1) as []. lra. apply H22. lra.
          pose proof (H21 H25). intro. apply Theorem4_1 in H27 as [].
          elim H26. rewrite <-H25; auto. }
        apply Classifier1 in H24 as []. apply Classifier1. exists x. apply Classifier1.
        split; auto. apply Classifier1. intro. applyClassifier1 H25.
        apply ProdEqual in H25 as []; auto. }
      assert (∀ y, y ∈ ran[h] -> y < h[n] -> y <= h[(n-1)%nat]).
      { intros. destruct H2. apply Classifier1 in H20 as [x].
        assert (x ∈ dom[h]). { apply Classifier1; eauto. }
        rewrite H3 in H23. applyClassifier1 H23. apply f_x_T in H20; auto.
        rewrite <-H20 in H21. assert (x < n \/ x = n)%nat as []. lia.
        assert (x < (n-1) \/ x = n-1)%nat as []. lia. rewrite <-H20.
        apply H22 in H25; try (rewrite H3; apply Classifier1; lia). lra.
        rewrite <-H20,H25; lra. rewrite H24 in H21. exfalso. lra. }
      assert (∃ J, Def_Integral f a b1 J).
      { apply IHn with (h := h1); auto. lra. }
      assert (∃J : R,Def_Integral f b1 b J).
      { assert (h[n] < b \/ h[n] = b) as []. lra.
        assert (ContinuousCO f b1 h[n]).
        { split. red; intros. apply NNPP; intro. assert (x ∈ ran[h]).
          { rewrite H4. apply Classifier1. split. lra. repeat split; intros; auto.
            exfalso. lra. exfalso. lra. }
          apply H20 in H25; auto. lra. lra. apply NNPP; intro.
          assert (b1 ∈ ran[h]).
          { rewrite H4. apply Classifier1. split. lra. repeat split; intros; auto.
            exfalso. lra. exfalso. lra. intro. apply Theorem4_1 in H25; tauto. }
          apply H20 in H24; lra. }
        assert (∀ y, y ∈ ran[h] -> y <= h[n]).
        { intros. destruct H2. apply Classifier1 in H24 as [x].
          assert (x ∈ dom[h]). { apply Classifier1; eauto. }
          rewrite H3 in H26. applyClassifier1 H26. apply f_x_T in H24; auto.
          assert (x < n \/ x = n)%nat as []. lia.
          apply H25 in H27; try (rewrite H3; apply Classifier1; lia). lra.
          rewrite <-H27,H24; lra. }
        assert (ContinuousOC f h[n] b).
        { split. red; intros. apply NNPP; intro. assert (x ∈ ran[h]).
          { rewrite H4. apply Classifier1. split. lra. repeat split; intros; auto.
            exfalso. lra. exfalso. lra. }
          apply H24 in H27; auto. lra. apply NNPP; intro. assert (b ∈ ran[h]).
          { rewrite H4. apply Classifier1. split. lra. repeat split; intros; auto.
            exfalso. lra. exfalso. lra. }
          apply H24 in H26; lra. }
        apply (Lemma9_5c f b1 h[n]). lra.
        destruct (classic (ContinuousLeft f h[n])). apply Theorem9_4. lra.
        destruct H23. split; auto. apply Lemma9_5b; auto. lra.
        destruct H0 as [H0[H27[]]]. assert (\[b1, h[n]\] ⊂ \[a, b\]).
        { red; intros. applyClassifier1 H29. apply Classifier1. lra. }
        split; auto. split; eauto. red; auto.
        destruct (classic (ContinuousRight f h[n])). apply Theorem9_4. lra.
        destruct H25. split; auto. apply Lemma9_5a; auto.
        destruct H0 as [H0[H27[]]]. assert (\[h[n], b\] ⊂ \[a, b\]).
        { red; intros. applyClassifier1 H29. apply Classifier1. lra. }
        split; auto. split; eauto. red; auto.
        assert (ContinuousCO f b1 b).
        { split. red; intros. apply NNPP; intro. assert (x ∈ ran[h]).
          { rewrite H4. apply Classifier1. split. lra. repeat split; intros; auto.
            exfalso. lra. exfalso. lra. }
          apply H20 in H25; auto. lra. lra. apply NNPP; intro.
          assert (b1 ∈ ran[h]).
          { rewrite H4. apply Classifier1. split. lra. repeat split; intros; auto.
            exfalso. lra. exfalso. lra. intro. apply Theorem4_1 in H25; tauto. }
          apply H20 in H24; lra. }
        assert (~ ContinuousLeft f b).
        { rewrite H4 in H8. apply Classifier1 in H8 as [H8[H24[]]]; auto. }
        apply Lemma9_5b; auto. lra. destruct H0 as [H0[H25[]]].
        assert (\[b1, b\] ⊂ \[a, b\]).
        { red; intros. applyClassifier1 H27. apply Classifier1. lra. }
        split; auto. split; eauto. red; auto. }
      apply (Lemma9_5c f a b1); auto.
  - assert (ContinuousClose f a b).
    { split; [ |split]; apply NNPP; intro.
      assert (∃ x, a < x < b /\ ~ Continuous f x) as [x[]].
      { apply NNPP; intro. elim H2. red. intros. apply NNPP; intro.
        elim H3; eauto. }
      assert (x ∈ Empty R).
      { rewrite <-H1. apply Classifier1. split. lra. repeat split; intros; auto.
        exfalso. lra. exfalso. lra. } applyClassifier1 H5. auto.
      assert (a ∈ Empty R).
      { rewrite <-H1. apply Classifier1. split. lra. repeat split; intros; auto.
        exfalso. lra. exfalso. lra. } applyClassifier1 H3. auto.
      assert (b ∈ Empty R).
      { rewrite <-H1. apply Classifier1. split. lra. repeat split; intros; auto.
        exfalso. lra. exfalso. lra. } applyClassifier1 H3. auto. }
    apply Theorem9_4; auto.
Qed.

(* 引理 常值函数的定积分 *)
Lemma Lemma9_6 : ∀ f a b r, a < b -> Function f -> \[a, b\] ⊂ dom[f]
  -> (∀ x, x ∈ \[a, b\] -> f[x] = r) -> Def_Integral f a b (r * (b - a)).
Proof.
  intros. split; auto. split; auto. split; auto.
  intros. exists 1. split. lra. intros. unfold IntegralSum.
  assert (Σ \{\ λ i s, s = f[ξ[i]] * (T[S i] - T[i]) \}\ n
    = Σ \{\ λ i s, s = r * (T[S i] - T[i]) \}\ n).
  { apply Σ_Fact5. intros. rewrite FunValue,FunValue. rewrite H2; auto.
    apply Classifier1. pose proof H4 as [H8[H9[H10[H11[]]]]]. rewrite <-H12,<-H13.
    pose proof H7. apply H5 in H14.
    assert (T[0%nat] <= T[x] /\ T[S x] <= T[S n]) as [].
    { split; apply (Seg_Increase_a T a b (S n)); auto; lia. } lra. }
  assert (Σ \{\ λ i s, s = r * (T[S i] - T[i]) \}\ n
    = r * (Σ \{\ λ i s, s = (T[S i] - T[i]) \}\ n)).
  { clear H3 H4 H5 H6 H7. induction n. simpl. rewrite FunValue,FunValue; auto.
    simpl. rewrite IHn,FunValue,FunValue. lra. }
  rewrite H7,H8,(Lemma9_6_1c T n a b),Rminus_diag,Abs_ge; auto. lra.
Qed.

Theorem Theorem9_6a : ∀ f a b, a < b -> Function f -> \[a, b\] ⊂ dom[f]
  -> (∀ x1 x2, x1 ∈ \[a, b\] -> x2 ∈ \[a, b\] -> x1 < x2 -> f[x1] <= f[x2])
  -> (∃ J, Def_Integral f a b J).
Proof.
  intros. assert (f[a] <= f[b]). { apply (H2 a b); auto; apply Classifier1; lra. }
  assert (∀ x, x ∈ \[a, b\] -> f[a] <= f[x] <= f[b]).
  { intros. apply Classifier1 in H4 as []. destruct H4,H5.
    split; [apply (H2 a x)|apply (H2 x b)]; auto; apply Classifier1; lra.
    rewrite H5. lra. rewrite H4. lra. exfalso. lra. }
  assert (DBoundedFun f (\[a, b\])).
  { split; auto. split; auto.
    assert (∃ M, ∣(f[a])∣ <= M /\ ∣(f[b])∣ <= M) as [M[]].
    { destruct (Rle_or_lt ∣(f[a])∣ ∣(f[b])∣). exists ∣(f[b])∣. lra.
      exists ∣(f[a])∣. lra. } exists M. intros. apply H4 in H7.
    pose proof (Abs_neg_pos f[a]). pose proof (Abs_neg_pos f[b]).
    apply Abs_le_R in H5,H6. apply Abs_le_R. lra. }
  destruct H3.
  - apply Theorem9_3b; auto. split; auto. intros. set (ε := δ/(f[b] - f[a])).
    assert (0 < ε). { apply Rdiv_lt_0_compat; lra. }
    destruct (Examp1 ε (b-a)) as [r[H8[]]]; auto. lra.
    assert (0 < r <= b - a). lra. apply Seg_Exists in H11 as [T[n[]]]; auto.
    assert (Σ \{\ λ u v, v = (amp f (\[T[u], T[S u]\])) * (T[S u] - T[u]) \}\ n
      <= Σ \{\ λ u v, v = (f[T[S u]] - f[T[u]]) * r \}\ n).
    { apply Rge_le,Σ_Fact3. intros. rewrite FunValue,FunValue.
      pose proof H11 as [H14[H15[_[H16[]]]]].
      assert (T[i] ∈ \[a, b\] /\ T[S i] ∈ \[a, b\]) as [].
      { split; apply Classifier1; rewrite <-H17,<-H18; split; try apply Rle_ge;
        apply (Seg_Increase_a T a b (S n)); auto; lia. }
      assert (f[T[i]] <= f[T[S i]]). { apply H2; auto. apply H16. lia. }
      assert (∀ x, T[i] <= x <= T[S i] -> f[T[i]] <= f[x] <= f[T[S i]]).
      { intros. assert (x ∈ \[a, b\]).
        { applyClassifier1 H19. applyClassifier1 H20. apply Classifier1; lra. }
        destruct H22 as [[][]]. split; apply H2; auto. rewrite H24. lra.
        rewrite <-H22. lra. rewrite H22,<-H24. lra. }
      assert (DBoundedFun f (\[T[i], T[S i]\])).
      { destruct H5 as [H5[H23[]]]. split; auto.
        assert (\[T[i], T[S i]\] ⊂ \[a, b\]).
        { red; intros. applyClassifier1 H25. applyClassifier1 H19. applyClassifier1 H20.
          apply Classifier1; lra. } split; eauto. red; auto. }
      assert (NotEmpty (\[T[i], T[S i]\])).
      { exists ((T[i] + T[S i])/2). assert (i < S n)%nat. lia.
        apply H16 in H24. apply Classifier1. lra. }
      assert (sup_fD f (\[T[i], T[S i]\]) = f[T[S i]]).
      { pose proof (sup_Coro_1 f (\[T[i], T[S i]\]) H23 H24).
        assert (sup ran[f|[\[T[i], T[S i] \]]] (f[T[S i]])).
        { split. red; intros. apply Classifier1 in H26 as [].
          apply Classifier1 in H26 as []. applyClassifier2 H27. destruct H27.
          applyClassifier1 H27. apply f_x_T in H26; auto. rewrite <-H26.
          apply H22. lra. intros. exists (f[T[S i]]). split; auto.
          apply Classifier1. exists T[S i]. apply Classifier1. split.
          apply x_fx_T; auto. apply Classifier2; split. apply Classifier1; split.
          assert (i < S n)%nat. lia. apply H16 in H27. lra. lra.
          apply Classifier1; auto. } destruct H25,H26.
        destruct (Rtotal_order (sup_fD f (\[T[i], T[S i]\])) (f[T[S i]])).
        apply H28 in H29 as [x[]]. apply H25 in H29. exfalso. lra.
        destruct H29; auto. apply Rgt_lt,H27 in H29 as [x[]].
        apply H26 in H29. exfalso. lra. }
      assert (inf_fD f (\[T[i], T[S i]\]) = f[T[i]]).
      { pose proof (inf_Coro_1 f (\[T[i], T[S i]\]) H23 H24).
        assert (inf ran[f|[\[T[i], T[S i] \]]] (f[T[i]])).
        { split. red; intros. apply Classifier1 in H27 as [].
          apply Classifier1 in H27 as []. applyClassifier2 H28. destruct H28.
          applyClassifier1 H28. apply f_x_T in H27; auto. rewrite <-H27.
          apply Rle_ge,H22. lra. intros. exists (f[T[i]]). split; auto.
          apply Classifier1. exists T[i]. apply Classifier1. split. apply x_fx_T; auto.
          apply Classifier2; split. apply Classifier1; split. lra.
          assert (i < S n)%nat. lia. apply H16 in H28. lra.
          apply Classifier1; auto. } destruct H26,H27.
        destruct (Rtotal_order (inf_fD f (\[T[i], T[S i]\])) (f[T[i]])).
        apply Rlt_gt,H28 in H30 as [x[]]. apply H27 in H30. exfalso. lra.
        destruct H30; auto. apply H29 in H30 as [x[]]. apply H26 in H30.
        exfalso. lra. }
      apply Rmult_ge_compat; unfold amp. rewrite H25,H26. lra.
      assert (i < S n)%nat. lia. apply H16 in H27. lra. rewrite H25,H26. lra.
      rewrite H12. apply Rle_ge,(SegMold_Max T a b (S n)); auto. lia. }
    assert (Σ \{\ λ u v, v = (f[T[S u]] - f[T[u]]) * r \}\ n
      = (Σ \{\ λ u v, v = (f[T[S u]] - f[T[u]]) \}\ n) * r).
    { clear dependent a. clear dependent b. clear H0 H6 H8 H12 H13.
      induction n. simpl. rewrite FunValue,FunValue. auto.
      simpl. rewrite IHn,FunValue,FunValue. lra. }
    assert (Σ \{\ λ u v, v = (f[T[S u]] - f[T[u]]) \}\ n
      = f[T[S n]] - f[T[0%nat]]).
    { clear dependent a. clear dependent b. clear dependent δ.
      clear dependent r. clear H0. induction n. simpl. rewrite FunValue.
      auto. simpl. rewrite IHn,FunValue. lra. }
    rewrite H14,H15 in H13. clear H14 H15.
    assert ((f[T[S n]] - f[T[0%nat]]) * r < (f[T[S n]] - f[T[0%nat]]) * ε).
    { apply Rmult_lt_compat_l; auto. destruct H11 as [_[_[_[_[]]]]].
      rewrite H11,H14. lra. }
    assert ((f[T[S n]] - f[T[0%nat]]) * ε = δ).
    { destruct H11 as [_[_[_[_[]]]]]. rewrite H11,H15. unfold ε.
      unfold Rdiv. rewrite <-Rmult_assoc,Rinv_r_simpl_m; auto. lra. }
    exists T,n. split; auto. lra.
  - exists (f[a] * (b - a)). apply Lemma9_6; auto. intros.
    apply H4 in H6. lra.
Qed.

Theorem Theorem9_6b : ∀ f a b, a < b -> Function f -> \[a, b\] ⊂ dom[f]
  -> (∀ x1 x2, x1 ∈ \[a, b\] -> x2 ∈ \[a, b\] -> x1 < x2 -> f[x2] <= f[x1])
  -> (∃ J, Def_Integral f a b J).
Proof.
  intros. assert (f[b] <= f[a]). { apply (H2 a b); auto; apply Classifier1; lra. }
  assert (∀ x, x ∈ \[a, b\] -> f[b] <= f[x] <= f[a]).
  { intros. apply Classifier1 in H4 as []. destruct H4,H5.
    split; [apply (H2 x b)|apply (H2 a x)]; auto; apply Classifier1; lra.
    rewrite H5. lra. rewrite H4. lra. exfalso. lra. }
  assert (DBoundedFun f (\[a, b\])).
  { split; auto. split; auto.
    assert (∃ M, ∣(f[a])∣ <= M /\ ∣(f[b])∣ <= M) as [M[]].
    { destruct (Rle_or_lt ∣(f[a])∣ ∣(f[b])∣). exists ∣(f[b])∣. lra.
      exists ∣(f[a])∣. lra. } exists M. intros. apply H4 in H7.
    pose proof (Abs_neg_pos f[a]). pose proof (Abs_neg_pos f[b]).
    apply Abs_le_R in H5,H6. apply Abs_le_R. lra. }
  destruct H3.
  - apply Theorem9_3b; auto. split; auto. intros. set (ε := δ/(f[a] - f[b])).
    assert (0 < ε). { apply Rdiv_lt_0_compat; lra. }
    destruct (Examp1 ε (b-a)) as [r[H8[]]]; auto. lra.
    assert (0 < r <= b - a). lra. apply Seg_Exists in H11 as [T[n[]]]; auto.
    assert (Σ \{\ λ u v, v = (amp f (\[T[u], T[S u]\])) * (T[S u] - T[u]) \}\ n
      <= Σ \{\ λ u v, v = (f[T[u]] - f[T[S u]]) * r \}\ n).
    { apply Rge_le,Σ_Fact3. intros. rewrite FunValue,FunValue.
      pose proof H11 as [H14[H15[_[H16[]]]]].
      assert (T[i] ∈ \[a, b\] /\ T[S i] ∈ \[a, b\]) as [].
      { split; apply Classifier1; rewrite <-H17,<-H18; split; try apply Rle_ge;
        apply (Seg_Increase_a T a b (S n)); auto; lia. }
      assert (f[T[S i]] <= f[T[i]]). { apply H2; auto. apply H16. lia. }
      assert (∀ x, T[i] <= x <= T[S i] -> f[T[S i]] <= f[x] <= f[T[i]]).
      { intros. assert (x ∈ \[a, b\]).
        { applyClassifier1 H19. applyClassifier1 H20. apply Classifier1; lra. }
        destruct H22 as [[][]]. split; apply H2; auto. rewrite H24. lra.
        rewrite <-H22. lra. rewrite H22,<-H24. lra. }
      assert (DBoundedFun f (\[T[i], T[S i]\])).
      { destruct H5 as [H5[H23[]]]. split; auto.
        assert (\[T[i], T[S i]\] ⊂ \[a, b\]).
        { red; intros. applyClassifier1 H25. applyClassifier1 H19. applyClassifier1 H20.
          apply Classifier1; lra. } split; eauto. red; auto. }
      assert (NotEmpty (\[T[i], T[S i]\])).
      { exists ((T[i] + T[S i])/2). assert (i < S n)%nat. lia.
        apply H16 in H24. apply Classifier1. lra. }
      assert (sup_fD f (\[T[i], T[S i]\]) = f[T[i]]).
      { pose proof (sup_Coro_1 f (\[T[i], T[S i]\]) H23 H24).
        assert (sup ran[f|[\[T[i], T[S i] \]]] (f[T[i]])).
        { split. red; intros. apply Classifier1 in H26 as [].
          apply Classifier1 in H26 as []. applyClassifier2 H27. destruct H27.
          applyClassifier1 H27. apply f_x_T in H26; auto. rewrite <-H26.
          apply H22. lra. intros. exists (f[T[i]]). split; auto.
          apply Classifier1. exists T[i]. apply Classifier1. split.
          apply x_fx_T; auto. apply Classifier2; split. apply Classifier1; split.
          lra. assert (i < S n)%nat. lia. apply H16 in H27. lra.
          apply Classifier1; auto. } destruct H25,H26.
        destruct (Rtotal_order (sup_fD f (\[T[i], T[S i]\])) (f[T[i]])).
        apply H28 in H29 as [x[]]. apply H25 in H29. exfalso. lra.
        destruct H29; auto. apply Rgt_lt,H27 in H29 as [x[]].
        apply H26 in H29. exfalso. lra. }
      assert (inf_fD f (\[T[i], T[S i]\]) = f[T[S i]]).
      { pose proof (inf_Coro_1 f (\[T[i], T[S i]\]) H23 H24).
        assert (inf ran[f|[\[T[i], T[S i] \]]] (f[T[S i]])).
        { split. red; intros. apply Classifier1 in H27 as [].
          apply Classifier1 in H27 as []. applyClassifier2 H28. destruct H28.
          applyClassifier1 H28. apply f_x_T in H27; auto. rewrite <-H27.
          apply Rle_ge,H22. lra. intros. exists (f[T[S i]]). split; auto.
          apply Classifier1. exists T[S i]. apply Classifier1. split. apply x_fx_T; auto.
          apply Classifier2; split. apply Classifier1; split. assert (i < S n)%nat. lia.
          apply H16 in H28. lra. lra. apply Classifier1; auto. } destruct H26,H27.
        destruct (Rtotal_order (inf_fD f (\[T[i], T[S i]\])) (f[T[S i]])).
        apply Rlt_gt,H28 in H30 as [x[]]. apply H27 in H30. exfalso. lra.
        destruct H30; auto. apply H29 in H30 as [x[]]. apply H26 in H30.
        exfalso. lra. }
      apply Rmult_ge_compat; unfold amp. rewrite H25,H26. lra.
      assert (i < S n)%nat. lia. apply H16 in H27. lra. rewrite H25,H26. lra.
      rewrite H12. apply Rle_ge,(SegMold_Max T a b (S n)); auto. lia. }
    assert (Σ \{\ λ u v, v = (f[T[u]] - f[T[S u]]) * r \}\ n
      = (Σ \{\ λ u v, v = (f[T[u]] - f[T[S u]]) \}\ n) * r).
    { clear dependent a. clear dependent b. clear H0 H6 H8 H12 H13.
      induction n. simpl. rewrite FunValue,FunValue. auto.
      simpl. rewrite IHn,FunValue,FunValue. lra. }
    assert (Σ \{\ λ u v, v = (f[T[u]] - f[T[S u]]) \}\ n
      = f[T[0%nat]] - f[T[S n]]).
    { clear dependent a. clear dependent b. clear dependent δ.
      clear dependent r. clear H0. induction n. simpl. rewrite FunValue.
      auto. simpl. rewrite IHn,FunValue. lra. }
    rewrite H14,H15 in H13. clear H14 H15.
    assert ((f[T[0%nat]] - f[T[S n]]) * r < (f[T[0%nat]] - f[T[S n]]) * ε).
    { apply Rmult_lt_compat_l; auto. destruct H11 as [_[_[_[_[]]]]].
      rewrite H11,H14. lra. }
    assert ((f[T[0%nat]] - f[T[S n]]) * ε = δ).
    { destruct H11 as [_[_[_[_[]]]]]. rewrite H11,H15. unfold ε.
      unfold Rdiv. rewrite <-Rmult_assoc,Rinv_r_simpl_m; auto. lra. }
    exists T,n. split; auto. lra.
  - exists (f[a] * (b - a)). apply Lemma9_6; auto. intros. apply H4 in H6. lra.
Qed.













