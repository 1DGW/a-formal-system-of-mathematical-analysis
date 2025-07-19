(** A_9_1 *)
(* 定积分概念 *)

Require Export A_8.

(* 定义：T为闭区间[a, b]的分割 *)
Definition Seg T a b n := Function T
  /\ (0 < n)%nat /\ dom[T] = \{ λ u, (u <= n)%nat \}
  /\ (∀ k, (k < n)%nat -> T[k] < T[S k]) /\ T[0%nat] = a /\ T[n] = b.

(* 用于分割的T序列是单增的 *)
Corollary Seg_StrictlyIncrease_a : ∀ T a b n, Seg T a b n
  -> (∀ n1 n2, (n1 <= n)%nat -> (n2 <= n)%nat -> (n1 < n2)%nat -> T[n1] < T[n2]).
Proof.
  intros. generalize dependent n1. induction n2; intros.
  - exfalso. apply (Nat.nlt_0_r n1). auto.
  - assert (∀ n1, (n1 <= n)%nat -> (n1 < n2)%nat -> T[n1] < T[n2]).
    { intros. apply IHn2; auto. lia. } destruct H as [H[]].
    assert (T[n2] < T[S n2]). { apply H5; lia. }
    destruct (classic (n1 = n2)).
    + rewrite H7; auto.
    + assert (T[n1] < T[n2]). { apply H3; lia. } lra.
Qed.

Corollary Seg_StrictlyIncrease_b : ∀ T a b n, Seg T a b n
  -> (∀ n1 n2, (n1 <= n)%nat -> (n2 <= n)%nat -> T[n1] < T[n2] -> (n1 < n2)%nat).
Proof.
  intros. destruct (Nat.lt_total n1 n2) as [H3 | []]; auto.
  rewrite H3 in H2. apply Rlt_irrefl in H2. elim H2.
  apply (Seg_StrictlyIncrease_a T a b n) in H3; auto.
  apply Rlt_asym in H2. elim H2; auto.
Qed.

Corollary Seg_Increase_a : ∀ T a b n, Seg T a b n
  -> (∀ n1 n2, (n1 <= n)%nat -> (n2 <= n)%nat -> (n1 <= n2)%nat -> T[n1] <= T[n2]).
Proof.
  intros. generalize dependent n1. induction n2; intros.
  - assert (n1 = 0%nat). lia. rewrite H3; lra.
  - assert (∀ n1, (n1 <= n)%nat -> (n1 <= n2)%nat -> T[n1] <= T[n2]).
    { intros. apply IHn2; auto. lia. } destruct H as [H[]].
    assert (T[n2] <= T[S n2]).
    { assert (T[n2] < T[S n2]). apply H5; lia. lra. }
    destruct (classic (n1 = S n2)).
    + rewrite H7. lra.
    + assert (T[n1] <= T[n2]). { apply H3; auto. lia. } lra.
Qed.

Corollary Seg_Increase_b : ∀ T a b n, Seg T a b n
  -> (∀ n1 n2, (n1 <= n)%nat -> (n2 <= n)%nat -> T[n1] <= T[n2] -> (n1 <= n2)%nat).
Proof.
  intros. destruct (Nat.le_gt_cases n1 n2); auto.
  apply (Seg_StrictlyIncrease_a T a b n) in H3; auto. exfalso. lra.
Qed.

(* 用于分割的T序列是单值映射的 *)
Corollary Seg_Injective : ∀ T a b n, Seg T a b n -> (∀ n1 n2, (n1 <= n)%nat
  -> (n2 <= n)%nat -> T[n1] = T[n2] -> n1 = n2).
Proof.
  intros. destruct (classic (n1 = n2)); auto. assert (n1 < n2 \/ n2 < n1)%nat. lia.
  destruct H4; apply (Seg_StrictlyIncrease_a T a b n H) in H4; auto; lra.
Qed.

(* 分割的小区间是整个区间的子区间 *)
Corollary Seg_subInterval : ∀ T a b n k, Seg T a b (S n)
  -> (k <= n)%nat -> \[T[k], T[S k] \] ⊂ \[ a, b \].
Proof.
  intros. pose proof H as H'. red in H. destruct H as [H[H1[_[H2 [H3 H4]]]]].
  destruct (Nat.eq_0_gt_0_cases k). subst k.
  - rewrite H3. red. intros. applyClassifier1 H5. apply Classifier1. split. tauto.
    rewrite <- H4. destruct H0. tauto. assert ((1 < S(S m))%nat). lia.
    apply (Seg_StrictlyIncrease_a T a b (S (S m))) in H6; auto. lra.
  - apply (Seg_StrictlyIncrease_a T a b (S n)) in H5 as H6'; auto.
    rewrite H3 in H6'. red. intros. applyClassifier1 H6. apply Classifier1.
    split. lra. rewrite <-H4. destruct H6. destruct H0. auto.
    assert ((S k < S (S m))%nat). lia.
    apply (Seg_StrictlyIncrease_a T a b (S (S m))) in H8; auto. lra. lia. lia.
Qed.

(* 有界函数经过分割后在每个小区间上都有界 *)
Corollary Seg_DBounded : ∀ f T a b n, Seg T a b (S n) -> DBoundedFun f (\[a,b\])
  -> (∀ i, (i <= n)%nat -> DBoundedFun f (\[T[i], T[S i]\])).
Proof.
  intros. destruct H0 as [H0[H2[]]].
  assert(\[T[i], T[S i]\] ⊂ \[a, b\] ).
  { apply (Seg_subInterval _ a b n); auto. }
  repeat split; auto. red; intros. apply H4 in H5. apply H2; auto.
  exists x. intros. apply H3. apply H4; auto.
Qed.

Corollary Seg_a_leq_b : ∀ T a b n , Seg T a b n -> a <= b.
Proof.
  intros. destruct H as [H[H1[H2[H3 [H4 H4']]]]]. rewrite <- H4', <- H4.
  left. apply (Seg_StrictlyIncrease_a T a b n); auto. split; auto. lia.
Qed.

Corollary Seg_a_less_b : ∀ T a b n , Seg T a b (S n) -> a < b.
Proof.
  intros. red in H. destruct H as [H[H1[H2[H3 [H4 H4']]]]]. rewrite <-H4',<-H4.
  apply (Seg_StrictlyIncrease_a T a b (S n)); auto. split; auto. lia.
Qed.

(* 分割都是一一函数 *)
Corollary Seg_is_Function1_1: ∀ T, (∃ a b n, Seg T a b n) -> Function1_1 T.
Proof.
  intros. destruct H as [a[b[n[H[H0[H1[H2[]]]]]]]]. split; auto.
  red; intros. applyClassifier2 H5; applyClassifier2 H6.
  assert (y ∈ dom[T] /\ z ∈ dom[T]) as []. { split; apply Classifier1; eauto. }
  rewrite H1 in H7,H8. applyClassifier1 H7; applyClassifier1 H8.
  apply (Seg_Injective T a b n); auto. repeat split; auto.
  apply f_x_T in H5, H6; auto. subst. auto.
Qed.

(* 定义 ：x为分割T的模(最大的小区间长度) *)
Definition SegMold T n x := (∃ k, (k < n)%nat /\ T[S k] - T[k] = x)
  /\ (∀ m, (m < n)%nat -> T[S m] - T[m] <= x).
Definition mold T n := c \{ λ x, SegMold T n x \}.

(* 任何分割都存在模 *)
Corollary SegMold_Exists : ∀ T a b n, Seg T a b n -> ∃ x, SegMold T n x.
Proof.
  intros T a b n [H3 [H0 [_ [H1 []]]]]. clear H H2. induction n as [|n IHn].
  - apply Nat.lt_irrefl in H0. contradiction.
  - destruct (classic (n = 0%nat)).
    + rewrite H. exists (T[1%nat] - T[0%nat]). split; intros; eauto.
      assert (m = 0%nat). lia. rewrite H4. lra.
    + assert (∀ k, (k < n)%nat -> T[k] < T[S k]). { intros. apply H1. lia. }
      assert (∃ x, SegMold T n x) as [x[[k[]]]]. { apply IHn; auto. lia. }
      destruct (Rlt_or_le x (T[S n] - T[n])) as [].
      * exists (T[S n] - T[n]). split; intros; eauto. destruct (classic (m = n)).
        rewrite H9. lra. assert (T[S m] - T[m] <= x). { apply H6. lia. } lra.
      * exists x. split; intros; eauto. destruct (classic (m = n)).
        rewrite H9; auto. apply H6. lia.
Qed.

(* 模的唯一性 *)
Corollary SegMold_Unique : ∀ T a b n, Seg T a b n
  -> ∃ x, \{ λ x, SegMold T n x \} = [x].
Proof.
  intros T a b n [H3 [H0 [_ [H1 []]]]]. clear H H2. induction n as [|n IHn].
  - apply Nat.lt_irrefl in H0. contradiction.
  - destruct (classic (n = 0%nat)).
    + rewrite H. exists (T[1%nat] - T[0%nat]). apply AxiomI; split; intros.
      * applyClassifier1 H2; destruct H2 as [[m [H2 H2']]]. apply Classifier1. 
        assert (m = 0%nat). lia. subst m. auto.
      * apply Classifier1. red. applyClassifier1 H2. split. exists 0%nat.
        split; [lia|auto]. intros. assert (m = 0%nat). lia. subst m. lra.
    + assert (∀ k, (k < n)%nat -> T[k] < T[S k]). { intros. apply H1. lia. }
      assert((0 < n)%nat). lia. apply IHn in H4; auto. destruct H4.
      assert(SegMold T n x). { cut(x ∈ [x]); intros. rewrite <- H4 in H5.
      applyClassifier1 H5; auto. apply Classifier1; auto.  }  
      destruct (Rlt_or_le x (T[S n] - T[n])) as [].
      * exists (T[S n] - T[n]). apply AxiomI; split; intros;
        applyClassifier1 H7; apply Classifier1.
        destruct H5 as [[k2[]]], H7 as [[k1[]]].
        destruct(classic (k1 = n)). subst k1. auto. assert(k1 < n)%nat. lia.
        apply H9 in H13. assert(n < S n)%nat. lia. apply H11 in H14. lra. split.
        exists n. split; [lia|auto]. intros. destruct H5 as [[k[]]].
        destruct(classic (m = n)). subst m; lra. assert(m < n)%nat. lia.
        apply H10 in H12; lra.
      * exists x. destruct H5 as [[k2[]]].
        apply AxiomI; split; intros; applyClassifier1 H9; apply Classifier1.
        destruct H9 as [[k1[]]]. assert(k2 < S n)%nat. lia. 
        apply H11 in H12. destruct(classic (k1 = n)). subst k1. lra.
        assert(k1 < n)%nat. lia. apply H8 in H14. lra. split. exists k2.
        split; [lia|lra]. intros. destruct(classic (m = n)). subst m. lra.
        subst z. apply H8. lia.
Qed.

(* 分割的任何小区间长度均小于等于模(模最大) *)
Corollary SegMold_Max : ∀ T a b n k, (k < n)%nat -> Seg T a b n
  -> T[S k] - T[k] <= (mold T n).
Proof.
  intros T a b n k H0 H1. apply SegMold_Exists in H1 as H2. destruct H2 as [x H2].
  assert (NotEmpty \{ λ x, SegMold T n x \}). { exists x. apply Classifier1; auto. }
  apply Axiomc in H. applyClassifier1 H. destruct H as [H3 H4]. auto.
Qed.

(* 分割的存在性 任何小于等于b - a的正实数r都对应有以r为模的分割 *)
Corollary Seg_Exists : ∀ a b r, a < b -> 0 < r <= (b - a)
  -> ∃ T n, Seg T a b (S n) /\ r = mold T (S n).
Proof.
  intros. destruct H0 as [H0[]]. assert (0 < (b - a) - r). lra.
  apply (Archimedes r (b - a - r)) in H2 as [n]; auto. assert (0 < n)%nat.
  { destruct n. simpl in H2. rewrite Rmult_0_l in H2. exfalso. lra. lia. }
  set (T := \{\ λ u v, (u <= S n)%nat /\ (u = 0%nat -> v = a)
    /\ (u = 1%nat -> v = a + r) /\ ((1 < u <= S n)%nat
      -> v = a + r + (INR (u-1)%nat) * (b - a - r)/(INR n)) \}\).
  assert (Function T).
  { red; intros. applyClassifier2 H4. destruct H4 as [H4[H6[]]].
    applyClassifier2 H5. destruct H5 as [H9[H10[]]].
    assert (x = 0 \/ x = 1 \/ 1 < x <= S n)%nat. lia. destruct H12 as [H12|[]];
    [rewrite H6,H10|rewrite H7,H5|rewrite H8,H11]; auto. }
  assert (dom[T] = \{ λ u, (u <= S n)%nat \}).
  { apply AxiomI; split; intros. applyClassifier1 H5. destruct H5.
    applyClassifier2 H5. destruct H5. apply Classifier1; auto. applyClassifier1 H5.
    apply Classifier1. assert (z = 0 \/ z = 1 \/ 1 < z <= (S n))%nat. lia.
    destruct H6 as [H6|[]]; [exists a|exists (a+r)|
    exists (a + r + (INR (z-1)%nat) * (b - a - r)/(INR n))]; apply Classifier2;
    split; auto; split; intros; auto; try (split; intros; auto); exfalso; lia. }
  assert (T[0%nat] = a /\ T[1%nat] = a + r) as [].
  { assert (0%nat ∈ dom[T] /\ 1%nat ∈ dom[T]) as [].
    { rewrite H5. split; apply Classifier1; lia. }
    apply x_fx_T,Classifier2 in H6 as [_[H6[]]], H7 as [_[H7[]]]; auto. }
  assert (∀ k, (1 < k <= S n)%nat -> T[k] = a + r + (INR (k-1)%nat)
    * (b - a - r)/(INR n)).
  { intros. assert (k ∈ dom[T]). { rewrite H5. apply Classifier1. lia. }
    apply x_fx_T,Classifier2 in H9 as [_[H9[]]]; auto. }
  assert (0 < (INR n)). apply lt_0_INR; auto. assert (T[S n] = b).
  { rewrite H8; [ |lia]. simpl. unfold Rdiv.
    rewrite Nat.sub_0_r,Rinv_r_simpl_m; lra. }
  assert (SegMold T (S n) r).
  { split. exists 0%nat. split. lia. rewrite H6,H7. lra. intros. destruct m.
    rewrite H6,H7. lra. destruct m. rewrite H8,H7; [ |lia]. simpl.
    replace (a + r + 1 * (b - a - r)/(INR n) - (a + r))
    with ((b - a - r)/(INR n)); [ |lra]. apply (Rmult_gt_compat_r (/(INR n)))
    in H2; [ |apply Rlt_gt,Rinv_0_lt_compat; auto].
    rewrite Rinv_r_simpl_m in H2; lra. rewrite H8,H8; try lia.
    replace (S (S (S m)) - 1)%nat with (S (S m)); [ |lia].
    replace (S (S m) - 1)%nat with (S m); [ |lia].
    replace (a + r + (INR (S (S m))) * (b - a - r)/(INR n)
      - (a + r + (INR (S m)) * (b - a - r)/(INR n))) with
    (((INR (S (S m))) * (b - a - r))/(INR n)
      - ((INR (S m)) * (b - a - r))/(INR n)); [ |lra].
    rewrite <-Rdiv_minus_distr,<-Rmult_minus_distr_r,<-minus_INR; [ |lia].
    replace (S (S m) - (S m))%nat with 1%nat; [ |lia]. simpl. rewrite Rmult_1_l.
    apply (Rmult_gt_compat_r (/(INR n))) in H2;
    [ |apply Rlt_gt,Rinv_0_lt_compat; auto]. rewrite Rinv_r_simpl_m in H2; lra. }
  assert (Seg T a b (S n)).
  { split; auto. split; auto. split; auto. split; auto. intros.
    destruct k. rewrite H6,H7. lra. destruct k. rewrite H7,H8; [ |lia]. simpl.
    assert (0 < (b - a - r)/(INR n)). { apply Rdiv_lt_0_compat; auto. lra. }
    lra. rewrite H8,H8; try lia. apply Rplus_lt_compat_l. unfold Rdiv.
    rewrite Rmult_assoc,Rmult_assoc. apply Rmult_lt_compat_r.
    apply Rdiv_lt_0_compat; auto. lra. apply lt_INR. lia. }
  exists T,n. split; auto. apply SegMold_Unique in H12 as [M].
  assert (r ∈ [M] /\ (mold T (S n)) ∈ [M]) as [].
  { rewrite <-H12. split; [ |apply Axiomc; exists r]; apply Classifier1; auto. }
  applyClassifier1 H13. applyClassifier1 H14. rewrite H13,H14; auto.
  set (T := \{\ λ u v, (0 <= u <= 1)%nat /\ ((u = 0)%nat -> v = a)
    /\ ((u = 1)%nat -> v = b) \}\).
  assert (Function T).
  { red; intros. applyClassifier2 H2. destruct H2 as [H2[]].
    applyClassifier2 H3. destruct H3 as [H3[]].
    assert (x = 0 \/ x = 1)%nat as []. lia.
    rewrite H4,H6; auto. rewrite H5,H7; auto. }
  assert (dom[T] = \{ λ u, (u <= 1)%nat \}).
  { apply AxiomI; split; intros. applyClassifier1 H3. destruct H3 as [].
    applyClassifier2 H3. destruct H3 as [H3[]]. apply Classifier1; lia.
    applyClassifier1 H3. apply Classifier1.
    assert (z = 0 \/ z = 1)%nat as []; [lia|exists a|exists b];
    apply Classifier2; split; try lia; split; auto; intros; exfalso; lia. }
  assert (T[0%nat] = a /\ T[1%nat] = b) as [].
  { assert (0%nat ∈ dom[T] /\ 1%nat ∈ dom[T]) as [].
    { split; rewrite H3; apply Classifier1; lia. }
    apply x_fx_T in H4,H5; auto. applyClassifier2 H4. destruct H4 as [H4[]].
    applyClassifier2 H5. destruct H5 as [H5[]]; auto. }
  assert (SegMold T 1%nat r).
  { split. exists 0%nat. split. lia. rewrite H4,H5; auto. intros.
    destruct m; [ |exfalso; lia]. rewrite H4,H5. lra. }
  assert (Seg T a b 1%nat).
  { split; auto. split. lia. split; auto. split; auto. intros.
    destruct k; [ |exfalso; lia]. rewrite H4,H5; auto. }
  exists T,0%nat. split; auto. apply SegMold_Unique in H7 as [M].
  assert (r ∈ [M] /\ (mold T 1%nat) ∈ [M]) as [].
  { rewrite <-H7; split; [ |apply Axiomc; exists r]; apply Classifier1; auto. }
  applyClassifier1 H8. applyClassifier1 H9. rewrite H8,H9; auto.
Qed.


(* 定义：分割T上的点序列ξ *)
Definition SegPoints T ξ n := (∀ k, (k < n)%nat -> T[k] <= ξ[k] <= T[S k]).


(* 积分和 *)
Definition IntegralSum (f : (@set (@prod R R))) T n ξ :=
  Σ \{\ λ i s, s = f[ξ[i]] * (T[S i] - T[i]) \}\ n.

(* 定义3 : J为f在区间[a, b]上的定积分 *)
Definition Def_Integral f a b J := Function f /\ a < b /\ \[a, b\] ⊂ dom[f]
  /\ ∀ ε, 0 < ε -> (∃ δ, 0 < δ
    /\ (∀ T ξ n, Seg T a b (S n) -> SegPoints T ξ (S n) -> (mold T (S n) < δ)
      -> ∣((IntegralSum f T n ξ) - J)∣ < ε)).


