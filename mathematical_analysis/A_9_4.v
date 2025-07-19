(** A_9_4 *)
(* 定积分的性质 *)

Require Export A_9_3.

Lemma Lemma9_4_1 : ∀ A J k ε, k <> 0 -> ε > 0 -> ∣(A - J)∣ < ε/(∣k∣)
  -> ∣(k*A - k*J)∣ < ε.
Proof.
  intros. rewrite <- Rmult_minus_distr_l. rewrite Abs_mult. 
  apply (Rmult_lt_compat_r Abs[k]) in H1. unfold Rdiv in H1. 
  rewrite Rmult_assoc in H1. rewrite Rinv_l in H1. lra.
  apply Abs_not_eq_0 in H; lra. apply Abs_not_eq_0; auto.
Qed.

Property Property9_4_1 : ∀ f a b J k, Def_Integral f a b J
  -> Def_Integral (f \\* k) a b (k * J).
Proof.
  intros. assert (a < b). { destruct H as [_[]]; auto. }
  pose proof H as H0'. destruct H0' as [H0'[H3[H1 _]]].
  assert(I1 : Function (f \\* k)).
  { unfold Function. intros. applyClassifier2 H2. applyClassifier2 H4. lra. }
  assert(I2 : ∀ x, x ∈ (\[a, b\]) -> (f \\* k)[x] = k * f[x]).
  { intros. apply f_x_T; auto. apply Classifier2. split; auto. lra. }
  assert(I3 : \[a, b\] ⊂ dom[(f \\* k)]).
  { red; intros. apply Classifier1. exists (k * f[z]).
    apply Classifier2. split; auto; lra. }
  destruct (classic (k = 0)) as [Hc|Hc].
  - subst k. replace (0 * J) with (0 * (b - a)); [ |lra].
    apply Lemma9_6; auto. intros. rewrite I2; auto. lra.
  - repeat split; auto. intros.
    destruct H as [_[_[_ H5]]]. apply Abs_not_eq_0 in Hc as H6.
    assert(ε/(∣k∣) > 0).
    { unfold Rdiv. apply Rmult_gt_0_compat; auto.
      apply Rinv_0_lt_compat in H6; auto. }
    apply H5 in H. clear H5. destruct H as [δ[]]. exists δ. split; auto.
    intros. apply (H4 T ξ _) in H5 as H5'; auto. clear H4.
    assert(∀ i, (i <= n)%nat -> ξ[i] ∈ \[a, b\]).
    { intros. apply (Seg_subInterval _ _ _ _ i) in H5; auto. apply H5.
      assert(i < S n)%nat. lia. apply H7 in H9. apply Classifier1; lra. }
    assert(∀ i, (i <= n)%nat
      -> Σ \{\ λ i s, s = (f \\* k)[ξ[i]] * (T[S i] - T[i])\}\ i
      = k * (Σ \{\ λ i s, s = f[ξ[i]] * (T[S i] - T[i]) \}\ i)).
    { intros. induction i. simpl. repeat rewrite FunValue.
      rewrite I2. lra. apply H4; lia. simpl. rewrite IHi.
      repeat rewrite FunValue. rewrite I2. lra. apply H4; lia. lia. }
    cut ((n <= n)%nat); intros. apply H9 in H10. clear H9.
    unfold IntegralSum. rewrite H10. clear H10. apply Lemma9_4_1; auto. lia.
Qed.


Property Property9_4_2a : ∀ f g a b J G, Def_Integral f a b J
  -> Def_Integral g a b G -> Def_Integral (f \+ g) a b (J + G).
Proof.
  intros. assert (a < b). { destruct H as [_[]]; auto. }
  destruct H as [H[H2[]]]. destruct H0 as [H0[_[]]].
  assert (I3 : Function (f \+ g)). { apply Corollary_plus_fun_a. }
  assert(I2 : \[a, b\] ⊂ dom[f \+ g]).
  { rewrite Corollary_plus_fun_c. red. intros. apply Classifier1; split; auto. }
  repeat split; auto. intros. assert(ε/2 > 0). lra. apply H6 in H8 as H9.
  apply H4 in H8 as H10. clear H6 H4. destruct H9 as [δ1[]], H10 as [δ2[]].
  apply (Examp1 δ1 δ2) in H4 as H11; auto. destruct H11 as [δ[H11[]]].
  exists δ. split; auto. intros. apply H6 in H15 as H17; auto; [ |lra].
  clear H6. apply H10 in H15 as H18; auto; [ |lra]. clear H10.
  assert(∀ x, x ∈ (\[a, b\]) -> (f \+ g)[x] = f[x] + g[x]).
  { intros. rewrite Corollary_plus_fun_b; auto. }
  assert(∀ i, (i <= n)%nat -> ξ[i] ∈ \[a, b\]).
  { intros. apply (Seg_subInterval _ _ _ _ i) in H14; auto. apply H14.
    assert(i < S n)%nat. lia. apply H15 in H19. apply Classifier1; lra. }
  assert(∀ i, (i <= n)%nat
    -> Σ \{\ λ i s, s = (f \+ g) [ξ[i]] * (T[S i] - T[i])\}\ i
    = Σ \{\ λ i s, s = f[ξ[i]] * (T[S i] - T[i]) \}\ i
    + Σ \{\ λ i s, s = g[ξ[i]] * (T[S i] - T[i]) \}\ i).
  { intros. induction i. simpl. repeat rewrite FunValue. rewrite H6. lra.
    apply H10; lia. simpl. rewrite IHi. repeat rewrite FunValue. rewrite H6. 
    lra. apply H10; lia. lia. }
  unfold IntegralSum in *. rewrite H19. apply Abs_R in H17.
  apply Abs_R in H18. apply Abs_R. lra. lia.
Qed.

Property Property9_4_2b : ∀ f g a b J G, Def_Integral f a b J
  -> Def_Integral g a b G -> Def_Integral (f \- g) a b (J - G).
Proof.
  intros. assert (a < b). { destruct H as [_[]]; auto. }
  destruct H as [H[H2[]]]. destruct H0 as [H0[_[]]].
  assert (I3 : Function (f \- g)). { apply Corollary_sub_fun_a. }
  assert(I2 : \[a, b\] ⊂ dom[f \- g]).
  { rewrite Corollary_sub_fun_c. red. intros. apply Classifier1; split; auto. }
  repeat split; auto. intros. assert(ε/2 > 0). lra. apply H6 in H8 as H9.
  apply H4 in H8 as H10. clear H6 H4. destruct H9 as [δ1[]], H10 as [δ2[]].
  apply (Examp1 δ1 δ2) in H4 as H11; auto. destruct H11 as [δ[H11[]]].
  exists δ. split; auto. intros. apply H6 in H15 as H17; auto; [ |lra].
  clear H6. apply H10 in H15 as H18; auto; [ |lra]. clear H10.
  assert(∀ x, x ∈ (\[a, b\]) -> (f \- g)[x] = f[x] - g[x]).
  { intros. apply f_x_T; auto. apply Classifier2. repeat split; auto. }
  assert(∀ i, (i <= n)%nat -> ξ[i] ∈ \[a, b\]).
  { intros. apply (Seg_subInterval _ _ _ _ i) in H14; auto. apply H14.
    assert(i < S n)%nat. lia. apply H15 in H19. apply Classifier1; lra. }
  assert(∀ i, (i <= n)%nat
    -> Σ \{\ λ i s, s = (f \- g)[ξ[i]] * (T[S i] - T[i])\}\ i
    = Σ \{\ λ i s, s = f[ξ[i]] * (T[S i] - T[i]) \}\ i
    - Σ \{\ λ i s, s = g[ξ[i]] * (T[S i] - T[i]) \}\ i).
  { intros. induction i. simpl. repeat rewrite FunValue. rewrite H6. lra.
    apply H10; lia. simpl. rewrite IHi. repeat rewrite FunValue. rewrite H6. 
    lra. apply H10; lia. lia. }
  unfold IntegralSum in *. rewrite H19. apply Abs_R in H17.
  apply Abs_R in H18. apply Abs_R. lra. lia.
Qed.

(* 有界函数取绝对值后存在非负上确界 *)
Lemma Lemma9_4_3a : ∀ f D, DBoundedFun f D -> NotEmpty D
  -> ∃ y, sup \{ λ u, ∃ x, x ∈ D /\ u = ∣(f[x])∣ \} y /\ 0 <= y.
Proof.
  intros. destruct H as [H[H1[M]]].
  assert (∃ y, sup \{ λ u, ∃ x, x ∈ D /\ u = ∣(f[x])∣ \} y) as [y].
  { apply Sup_principle. destruct H0. exists ∣(f[x])∣. apply Classifier1; eauto.
    exists M. red; intros. apply Classifier1 in H3 as [x0[]]. rewrite H4; auto. }
  exists y. split; auto. destruct H0. assert (∣(f[x])∣ <= y).
  { destruct H3. apply H3. apply Classifier1; eauto. }
  assert (∣(f[x])∣ >= 0). apply Abs_Rge0. lra.
Qed.

(* 函数取绝对值后上确界为0, 则函数值恒为0 *)
Lemma Lemma9_4_3b : ∀ f D, sup \{ λ u, ∃ x, x ∈ D /\ u = ∣(f[x])∣ \} 0
  -> (∀ (x : R), x ∈ D -> f[x] = 0).
Proof.
  intros. assert (∣(f[x])∣ <= 0). { destruct H. apply H. apply Classifier1; eauto. }
  apply Abs_le_R in H1. lra.
Qed.

(* 振幅是函数两点差值的绝对值的上确界 *)
Lemma Lemma9_4_3c : ∀ f D, DBoundedFun f D -> NotEmpty D
  -> sup \{ λ u, ∃ x1 x2, x1 ∈ D /\ x2 ∈ D /\ u = ∣(f[x1] - f[x2])∣ \} (amp f D).
Proof.
  intros. assert (D ⊂ dom[f]). { destruct H as [_[]]; auto. }
  pose proof H. apply sup_inf_Coro_2 in H2; auto.
  pose proof H. apply sup_Coro_1 in H3 as []; auto.
  pose proof H. apply inf_Coro_1 in H5 as []; auto.
  assert (∀ x, x ∈ D -> f[x] ∈ ran[f|[D]]).
  { intros. apply Classifier1. exists x. apply Classifier1; split. apply x_fx_T; auto.
    destruct H; auto. apply Classifier2; split; auto. apply Classifier1; auto. }
  split. red; intros. apply Classifier1 in H8 as [x1[x2[H8[]]]].
  destruct (Rle_or_lt f[x2] f[x1]). rewrite H10,Abs_ge; [ |lra].
  apply H7,H3 in H8. apply H7,H5 in H9. unfold amp. lra.
  rewrite H10,Abs_lt; [ |lra]. rewrite Ropp_minus_distr.
  apply H7,H3 in H9. apply H7,H5 in H8. unfold amp. lra.
  intros. unfold amp in H8. assert ((inf_fD f D) + a < (sup_fD f D)). lra.
  apply H4 in H9 as [y1[]]. assert (y1 - a > (inf_fD f D)). lra.
  apply H6 in H11 as [y2[]]. assert (y1 - y2 > a). lra.
  apply Classifier1 in H9 as [x1], H11 as [x2].
  apply Classifier1 in H9 as [], H11 as [].
  applyClassifier2 H14. applyClassifier2 H15.
  destruct H14 as [H14 _], H15 as [H15 _].
  apply f_x_T in H9,H11; destruct H; auto. rewrite <-H9,<-H11 in H13.
  destruct (Rlt_or_le f[x1] f[x2]). exists (f[x2] - f[x1]). split; [ |lra].
  apply Classifier1. exists x1,x2. rewrite Abs_lt; try lra. split; auto.
  split; auto. lra. exists (f[x1] - f[x2]). split; auto. apply Classifier1.
  exists x1,x2. rewrite Abs_ge; auto. lra.
Qed.

(* 集合上确界之间的一些关联 *)
Lemma Lemma9_4_3d : ∀ A B am bm, sup A am -> sup B bm
  -> (∀ a, a ∈ A -> ∃ b, b ∈ B /\ a <= b) -> am <= bm.
Proof.
  intros. destruct (Rle_or_lt am bm); auto. destruct H,H0.
  apply H3 in H2 as [a[]]. apply H1 in H2 as [b[]]. apply H0 in H2. exfalso. lra.
Qed.

Lemma Lemma9_4_3e : ∀ A B C bm cm, NotEmpty A -> sup B bm -> sup C cm
  -> (∀ a, a ∈ A -> ∃ b c, b ∈ B /\ c ∈ C /\ a = b + c)
  -> ∃ am, sup A am /\ am <= bm + cm.
Proof.
  intros. assert (∃ am, sup A am) as [am].
  { apply Sup_principle; auto. destruct H0,H1. exists (bm + cm).
    red; intros. apply H2 in H5 as [b[c[H5[]]]]. rewrite H7.
    apply H0 in H5. apply H1 in H6. lra. }
  exists am. split; auto. destruct (Rle_or_lt am (bm + cm)); auto.
  destruct H0,H1,H3. apply H7 in H4 as [a[]]. apply H2 in H4 as [b[c[H4[]]]].
  rewrite H10 in H8. apply H0 in H4. apply H1 in H9.
  assert (b + c <= bm + cm). lra. exfalso. lra.
Qed.

Lemma Lemma9_4_3f : ∀ A B C bm cm, NotEmpty A -> sup B bm -> sup C cm
  -> (∀ b, b ∈ B -> 0 <= b) -> (∀ c, c ∈ C -> 0 <= c)
  -> (∀ a, a ∈ A -> ∃ b c, b ∈ B /\ c ∈ C /\ a = b * c)
  -> ∃ am, sup A am /\ am <= bm * cm.
Proof.
  intros. assert (∃ am, sup A am) as [am].
  { apply Sup_principle; auto. destruct H0,H1. exists (bm * cm).
    red; intros. apply H4 in H7 as [b[c[H7[]]]]. rewrite H9.
    pose proof (H2 b H7). pose proof (H3 c H8).
    apply H0 in H7. apply H1 in H8. apply Rmult_le_compat; auto. }
  exists am. split; auto. destruct (Rle_or_lt am (bm * cm)); auto.
  destruct H0,H1,H5. apply H9 in H6 as [a[]]. apply H4 in H6 as [b[c[H6[]]]].
  rewrite H12 in H10. pose proof (H2 b H6). pose proof (H3 c H11).
  apply H0 in H6. apply H1 in H11.
  assert (b * c <= bm * cm). { apply Rmult_le_compat; auto. } exfalso. lra.
Qed.

(* 分割增加p个分点后, 振幅乘小区间之和不增大 *)
Lemma Lemma9_4_3g : ∀ f T T' a b n p, DBoundedFun f (\[a, b\])
  -> Sum_Seg T T' a b (S n) p
  -> (Σ \{\ λ u v, v = (amp f (\[T'[u], T'[S u]\]))
    * (T'[S u] - T'[u]) \}\ (n + p)%nat)
    <= Σ \{\ λ u v, v = (amp f (\[T[u], T[S u]\])) * (T[S u] - T[u]) \}\ n.
Proof.
  intros. pose proof H0 as [H1[]].
  rewrite <-(Corollary_amp f T a b),<-(Corollary_amp f T' a b); auto.
  assert ((Up_sum f T' (n + p)) <= (Up_sum f T n)).
  { pose proof H0. apply (Property9_6_2a f) in H4 as []; auto. }
  assert ((Low_sum f T n) <= (Low_sum f T' (n + p))).
  { pose proof H0. apply (Property9_6_2b f) in H5 as []; auto. } lra.
Qed.

(* 求和分配律 *)
Lemma Lemma9_4_3h : ∀ n A C B D,
  Σ \{\ λ u v, v = A * (B u) + C * (D u) \}\ n
  = A * (Σ \{\ λ u v, v = B u \}\ n) + C * (Σ \{\ λ u v, v = D u \}\ n).
Proof.
  intros. induction n. simpl. repeat rewrite FunValue. lra.
  simpl. rewrite IHn. repeat rewrite FunValue. lra.
Qed.

Property Property9_4_3 : ∀ f g a b, (∃ J, Def_Integral f a b J)
  -> (∃ J, Def_Integral g a b J) -> (∃ J, Def_Integral (f \* g) a b J).
Proof.
  intros. assert (a < b). { destruct H as [J[_[]]]; auto. }
  assert (DBoundedFun f (\[a, b\]) /\ DBoundedFun g (\[a, b\])) as [].
  { destruct H as [J1], H0 as [J2]. split; eapply Theorem9_2; eauto.
    destruct H; auto. destruct H0; auto. }
  assert (DBoundedFun (f \* g) (\[a, b\])).
  { destruct H2 as [H2[H4[]]], H3 as [H3[H6[]]].
    split. apply Corollary_mult_fun_a. rewrite Corollary_mult_fun_c. split.
    red; intros. apply Classifier1; auto. exists (x * x0). intros.
    rewrite Corollary_mult_fun_b,Abs_mult; auto.
    assert (0 <= ∣(f[x1])∣ /\ 0 <= ∣(g[x1])∣) as [].
    { split; apply Rge_le,Abs_Rge0. } apply Rmult_le_compat; auto. }
  assert (NotEmpty (\[a, b\])). { exists ((a+b)/2). apply Classifier1; lra. }
  pose proof H2. pose proof H3. apply Lemma9_4_3a in H6 as [A[]], H7 as [B[]];
  auto. destruct H8. destruct H9.
  - apply Theorem9_3b; auto. split; auto. intros.
    set (ε1 := δ/(2*B)). set (ε2 := δ/(2*A)).
    assert (ε1 > 0 /\ ε2 > 0) as [].
    { split; apply Rlt_gt,Rdiv_lt_0_compat; auto; lra. }
    pose proof H. pose proof H0.
    apply Theorem9_3b in H13 as [_], H14 as [_]; auto.
    pose proof (H13 ε1 H11) as [T1[n1[]]]. pose proof (H14 ε2 H12) as [T2[n2[]]].
    destruct (Lemma9_6_3b T1 T2 a b (S n1) (S n2) H15 H17)
    as [n[H19[H20[H21[H22[]]]]]]. destruct n. exfalso. lia.
    exists (Merge_seg T1 T2),n. split; auto. set (T := Merge_seg T1 T2).
    assert (Σ \{\ λ u v, v = (amp (f \* g) (\[T[u], T[S u]\]))
        * (T[S u] - T[u]) \}\ n
      <= Σ \{\ λ u v, v = B * ((amp f (\[T[u], T[S u]\])) * (T[S u] - T[u]))
        + A * ((amp g (\[T[u], T[S u]\])) * (T[S u] - T[u])) \}\ n).
    { apply Rge_le,Σ_Fact3. intros. repeat rewrite FunValue.
      assert (\[T[i], T[S i]\] ⊂ \[a, b\]).
      { red; intros. pose proof H22. destruct H27 as [H27[H28[H29[H30[]]]]].
        rewrite <-H31,<-H32. apply Classifier1 in H26 as []. apply Classifier1.
        assert (T[0%nat] <= T[i] /\ T[S i] <= T[S n]) as [].
        { split; apply (Seg_Increase_a T a b (S n)); auto; lia. }
        unfold T in *. lra. }
      assert (DBoundedFun (f \* g) (\[T[i], T[S i]\])
        /\ DBoundedFun f (\[T[i], T[S i]\]) /\ DBoundedFun g (\[T[i], T[S i]\])).
      { destruct H2 as [H2[H27[M1]]], H3 as [H3[H29[M2]]], H4 as [H4[H31[M]]].
        split; [ |split]; split; auto; split; eauto; red; auto. }
      destruct H27 as [H27[]]. assert (NotEmpty (\[T[i], T[S i]\])).
      { assert (T[i] < T[S i]).
        { apply (Seg_StrictlyIncrease_a T a b (S n)); auto. lia. }
        exists ((T[i] + T[S i])/2). apply Classifier1; lra. }
      pose proof H28. pose proof H29.
      pose proof H28 as H28a. pose proof H29 as H29a.
      apply Lemma9_4_3a in H31 as [y1[]], H32 as [y2[]]; auto.
      apply Lemma9_4_3c in H27,H28,H29; auto.
      set (A1 := \{ λ u, ∃ x, x ∈ \[T[i], T[S i]\] /\ u = ∣(g[x])∣ \}).
      set (A2 := \{ λ u, ∃ x1 x2, x1 ∈ \[T[i], T[S i]\] /\ x2 ∈ \[T[i], T[S i]\]
        /\ u = ∣(f[x1] - f[x2])∣ \}).
      set (A3 := \{ λ u, ∃ x, x ∈ \[T[i], T[S i]\] /\ u = ∣(f[x])∣ \}).
      set (A4 := \{ λ u, ∃ x1 x2, x1 ∈ \[T[i], T[S i]\] /\ x2 ∈ \[T[i], T[S i]\]
        /\ u = ∣(g[x1] - g[x2])∣ \}).
      set (A5 := \{ λ u, ∃ x1 x2, x1 ∈ \[T[i], T[S i]\] /\ x2 ∈ \[T[i], T[S i]\]
        /\ u = ∣(g[x1])∣ * ∣(f[x1] - f[x2])∣ \}).
      set (A6 := \{ λ u, ∃ x1 x2, x1 ∈ \[T[i], T[S i]\] /\ x2 ∈ \[T[i], T[S i]\]
        /\ u = ∣(f[x2])∣ * ∣(g[x1] - g[x2])∣ \}).
      set (A7 := \{ λ u, ∃ x1 x2, x1 ∈ \[T[i], T[S i]\] /\ x2 ∈ \[T[i], T[S i]\]
        /\ u = ∣(g[x1])∣ * ∣(f[x1] - f[x2])∣
          + ∣(f[x2])∣ * ∣(g[x1] - g[x2])∣ \}).
      assert (NotEmpty A5 /\ NotEmpty A6 /\ NotEmpty A7) as [H35[]].
      { destruct H30. split. exists (∣(g[x])∣ * ∣(f[x] - f[x])∣).
        apply Classifier1; eauto. split. exists (∣(f[x])∣ * ∣(g[x] - g[x])∣).
        apply Classifier1; eauto. exists (∣(g[x])∣ * ∣(f[x] - f[x])∣
        + ∣(f[x])∣ * ∣(g[x] - g[x])∣). apply Classifier1; eauto. }
      assert (∀ a, a ∈ A5 -> ∃ a1 a2, a1 ∈ A1 /\ a2 ∈ A2 /\ a = a1 * a2).
      { intros. apply Classifier1 in H38 as [x1[x2[H38[]]]]. exists (∣(g[x1])∣),
        (∣(f[x1] - f[x2])∣). repeat split; auto; apply Classifier1; eauto. }
      assert (∀ a, a ∈ A6 -> ∃ a1 a2, a1 ∈ A3 /\ a2 ∈ A4 /\ a = a1 * a2).
      { intros. apply Classifier1 in H39 as [x1[x2[H39[]]]]. exists (∣(f[x2])∣),
        (∣(g[x1] - g[x2])∣). repeat split; auto; apply Classifier1; eauto. }
      assert (∀ a, a ∈ A1 \/ a ∈ A2 \/ a ∈ A3 \/ a ∈ A4 -> 0 <= a).
      { intros. destruct H40 as [H40|[H40|[H40|H40]]]; apply Classifier1 in H40
        as [x1[]]; try destruct H40 as [x2[]]; rewrite H41;
        apply Rge_le,Abs_Rge0. }
      assert ((∀ a, a ∈ A7 -> ∃ a1 a2, a1 ∈ A5 /\ a2 ∈ A6 /\ a = a1 + a2)).
      { intros. apply Classifier1 in H41 as [x1[x2[H41[]]]].
        exists (∣(g[x1])∣ * ∣(f[x1] - f[x2])∣),
        (∣(f[x2])∣ * ∣(g[x1] - g[x2])∣). rewrite H43.
        repeat split; auto; apply Classifier1; eauto. }
      apply (Lemma9_4_3f _ _ _ y2 (amp f (\[T[i], T[S i]\]))) in H38
      as [am5[]]; auto.
      apply (Lemma9_4_3f _ _ _ y1 (amp g (\[T[i], T[S i]\]))) in H39
      as [am6[]]; auto.
      apply (Lemma9_4_3e _ _ _ am5 am6) in H41 as [am7[]]; auto.
      set (A8 := \{ λ u, ∃ x1 x2, x1 ∈ \[T[i], T[S i]\] /\ x2 ∈ \[T[i], T[S i]\]
        /\ u = ∣((f \* g)[x1] - (f \* g)[x2])∣ \}).
      assert (∀ a, a ∈ A8 -> ∃ b, b ∈ A7 /\ a <= b).
      { intros. apply Classifier1 in H45 as [x1[x2[H45[]]]].
        exists (∣(g[x1])∣ * ∣(f[x1] - f[x2])∣
          + ∣(f[x2])∣ * ∣(g[x1] - g[x2])∣). split. apply Classifier1; eauto.
        destruct H2 as [_[]], H3 as [_[]]. rewrite H47,<-Abs_mult,<-Abs_mult,
        Corollary_mult_fun_b,Corollary_mult_fun_b; auto.
        replace (f[x1] * g[x1] - f[x2] * g[x2]) with
        (g[x1] * (f[x1] - f[x2]) + f[x2] * (g[x1] - g[x2])); [ |lra].
        apply Abs_plus_le. }
      assert (∀ a0, a0 ∈ A3 -> ∃ b0, b0 ∈ \{ λ u, ∃ x, (x ∈ \[a, b\])
        /\ u = ∣(f[x])∣ \} /\ a0 <= b0).
      { intros. apply Classifier1 in H46 as [x[]]. exists a0. split; [ |lra].
        apply Classifier1; eauto. }
      assert (∀ a0, a0 ∈ A1 -> ∃ b0, b0 ∈ \{ λ u, ∃ x, (x ∈ \[a, b\])
        /\ u = ∣(g[x])∣ \} /\ a0 <= b0).
      { intros. apply Classifier1 in H47 as [x[]]. exists a0. split; [ |lra].
        apply Classifier1; eauto. }
      apply (Lemma9_4_3d _ _ (amp (f \* g) (\[T[i], T[S i]\])) am7) in H45; auto.
      apply (Lemma9_4_3d _ _ y1 A) in H46; auto.
      apply (Lemma9_4_3d _ _ y2 B) in H47; auto.
      rewrite <-Rmult_assoc,<-Rmult_assoc,<-Rmult_plus_distr_r.
      apply Rle_ge,Rmult_le_compat_r. assert (T[i] <= T[S i]).
      { apply (Seg_Increase_a T a b (S n)); auto. lia. } lra.
      assert ((amp (f \* g) (\[T[i], T[S i]\]) <= y2 * (amp f (\[T[i], T[S i]\]))
        + y1 * (amp g (\[T[i], T[S i]\])))). lra.
      assert (y2 * (amp f (\[T[i], T[S i]\]))
        <= B * (amp f (\[T[i], T[S i]\]))).
      { apply Rmult_le_compat_r; [ |lra]. unfold amp.
        apply sup_inf_Coro_2 in H28a. lra. assert (T[i] < T[S i]).
        { apply (Seg_StrictlyIncrease_a T a b (S n)); auto. lia. }
        exists ((T[i] + T[S i])/2). apply Classifier1. lra. }
      assert (y1 * (amp g (\[T[i], T[S i]\]))
        <= A * (amp g (\[T[i], T[S i]\]))).
      { apply Rmult_le_compat_r; [ |lra]. unfold amp.
        apply sup_inf_Coro_2 in H29a. lra. assert (T[i] < T[S i]).
        { apply (Seg_StrictlyIncrease_a T a b (S n)); auto. lia. }
        exists ((T[i] + T[S i])/2). apply Classifier1. lra. } lra. }
    rewrite Lemma9_4_3h in H25.
    assert (Σ \{\ λ u v, v = (amp f (\[T[u], T[S u]\])) * (T[S u] - T[u]) \}\n
      <= Σ \{\ λ u v, v = (amp f (\[T1[u], T1[S u]\])) * (T1[S u] - T1[u]) \}\ n1).
    { replace n with (n1 + (n - n1))%nat; [ |lia].
      apply (Lemma9_4_3g f T1 T a b); auto. }
    assert (Σ \{\ λ u v, v = (amp g (\[T[u], T[S u]\])) * (T[S u] - T[u]) \}\n
      <= Σ \{\ λ u v, v = (amp g (\[T2[u], T2[S u]\])) * (T2[S u] - T2[u]) \}\ n2).
    { replace n with (n2 + (n - n2))%nat; [ |lia].
      apply (Lemma9_4_3g g T2 T a b); auto. }
    assert (B * (Σ \{\ λ u v, v = (amp f (\[T[u], T[S u]\]))
      * (T[S u] - T[u]) \}\n) < B * ε1). { apply Rmult_lt_compat_l; lra. }
    assert (A * (Σ \{\ λ u v, v = (amp g (\[T[u], T[S u]\]))
      * (T[S u] - T[u]) \}\n) < A * ε2). { apply Rmult_lt_compat_l; lra. }
    replace δ with (B * ε1 + A * ε2). lra. unfold ε1,ε2,Rdiv.
    rewrite Rinv_mult,Rinv_mult,Rmult_comm,(Rmult_comm A),
    Rmult_assoc,Rmult_assoc,Rmult_assoc,Rmult_assoc,(Rmult_comm _ A),
    (Rmult_comm _ B),Rinv_r,Rinv_r; lra.
  - rewrite <-H9 in H7. pose proof (Lemma9_4_3b g (\[a, b\]) H7).
    destruct H2 as [_[]], H3 as [_[]]. exists (0 * (b - a)).
    apply Lemma9_6; auto. apply Corollary_mult_fun_a.
    rewrite Corollary_mult_fun_c. red; intros. apply Classifier1; auto. intros.
    rewrite Corollary_mult_fun_b; auto. rewrite H10; auto. lra.
  - rewrite <-H8 in H6. pose proof (Lemma9_4_3b f (\[a, b\]) H6).
    destruct H2 as [_[]], H3 as [_[]]. exists (0 * (b - a)).
    apply Lemma9_6; auto. apply Corollary_mult_fun_a.
    rewrite Corollary_mult_fun_c. red; intros. apply Classifier1; auto. intros.
    rewrite Corollary_mult_fun_b; auto. rewrite H10; auto. lra.
Qed.

(* 区间上一点要么落在原有分割的分点上, 要么可以增加该点形成一个新的分割 *)
Lemma Lemma9_4_4a : ∀ T a b c n, a < c < b -> Seg T a b (S n)
  -> ∃ T1 k, (T1 = T /\ (0 < k <= n)%nat /\ T1[k] = c)
    \/ (Sum_Seg T T1 a b (S n) 1%nat /\ (0 < k <= (S n))%nat /\ T1[k] = c).
Proof.
  intros. destruct (classic (∃ k, (0 < k <= n)%nat /\ T[k] = c)) as [H1|H1].
  destruct H1 as [k[]]. exists T,k. left; auto.
  assert (∃ k, (0 <= k <= n)%nat /\ T[k] < c < T[S k]) as [k[]].
  { pose proof H0 as [H2[H3[H4[H5[]]]]].
    set (h := \{\ λ u v, (u <= S n)%nat /\ v = T[u] \}\).
    assert (Function1_1 h).
    { split; red; intros. applyClassifier2 H8. applyClassifier2 H9.
      destruct H8 as [], H9 as []. rewrite H10,H11; auto.
      applyClassifier2 H8. applyClassifier2 H9. applyClassifier2 H8.
      applyClassifier2 H9. destruct H8 as [], H9 as []. rewrite H10 in H11.
      destruct (Nat.lt_total y z) as [H12|[]]; auto;
      apply (Seg_StrictlyIncrease_a T a b (S n)) in H12; auto;
      rewrite H11 in H12; exfalso; lra. }
    assert (dom[h] = \{ λ u, (u <= S n)%nat \}).
    { apply AxiomI; split; intros. apply Classifier1 in H9 as [].
      applyClassifier2 H9. destruct H9. apply Classifier1; auto.
      applyClassifier1 H9. apply Classifier1. exists T[z].
      apply Classifier1; eauto. }
    assert (ran[h] = ran[T]).
    { apply AxiomI; split; intros; apply Classifier1 in H10 as [].
      applyClassifier2 H10. destruct H10. rewrite H11. apply Classifier1. exists x.
      apply x_fx_T; auto. rewrite H4. apply Classifier1; auto. apply Classifier1.
      exists x. apply Classifier1. exists x,z. split; auto.
      assert (x ∈ dom[T]). { apply Classifier1; eauto. } rewrite H4 in H11.
      applyClassifier1 H11. split; auto. apply f_x_T in H10; auto. }
    assert (Finite ran[T]). { left. red; eauto. }
    set (A := \{ λ u, ∃ k, (k <= n)%nat /\ T[k] < c /\ u = T[k] \}).
    assert (Finite A).
    { apply (SubSetFinite ran[T] A); auto. red; intros.
      apply Classifier1 in H12 as [k[H12[]]]. rewrite H14. apply Classifier1.
      exists k. apply x_fx_T; auto. rewrite H4. apply Classifier1; lia. }
    assert (NotEmpty A).
    { exists a. apply Classifier1. exists 0%nat. split. lia. rewrite H6. lra. }
    assert (NotEmptyFinite A).
    { destruct H12; auto. destruct H13. rewrite H12 in H13.
      applyClassifier1 H13. elim H13; auto. }
    apply finite_maxR in H14 as [r[]]. apply Classifier1 in H14 as [k[H14[]]].
    exists k. split. lia. split; auto. destruct (Rlt_or_le c T[S k]); auto.
    assert (k = n \/ k < n)%nat as []. lia. rewrite H19,H7. lra.
    assert (T[S k] ∈ A).
    { apply Classifier1. exists (S k). split. lia. split; auto. destruct H18; auto.
      elim H1. exists (S k). split; auto. lia. }
    apply H15 in H20. rewrite H17 in H20. apply (Seg_Increase_b T a b (S n))
    in H20; auto. exfalso. lia. }
  set (T1 := \{\ λ u v, (u <= (S (S n)))%nat
    /\ ((u <= k)%nat -> v = T[u]) /\ (u = S k -> v = c)
    /\ (((S k) < u)%nat -> v = T[(u - 1)%nat]) \}\).
  assert (Function T1).
  { red; intros. applyClassifier2 H4. applyClassifier2 H5.
    destruct H4 as [H4[H6[]]], H5 as [H5[H9[]]].
    assert (x <= k \/ x = S k \/ (S k) < x)%nat as [H12|[]]. lia.
    rewrite H6,H9; auto. rewrite H7,H10; auto. rewrite H8,H11; auto. }
  assert (dom[T1] = \{ λ u, (u <= S (S n))%nat \}).
  { apply AxiomI; split; intros. apply Classifier1 in H5 as [].
    applyClassifier2 H5. destruct H5. apply Classifier1; auto. applyClassifier1 H5.
    apply Classifier1. assert (z <= k \/ z = S k \/ (S k) < z)%nat as [H6|[]];
    [lia|exists T[z]|exists c|exists T[(z-1)%nat]]; apply Classifier2; split; auto;
    split; intros; auto; try (exfalso; lia); split; intros; auto; exfalso; lia. }
  assert (∀ m, (m <= k)%nat -> T1[m] = T[m]).
  { intros. assert (m ∈ dom[T1]). { rewrite H5. apply Classifier1; lia. }
    apply x_fx_T in H7; auto. applyClassifier2 H7. destruct H7 as [H7[H8[]]]; auto. }
  assert (T1[S k] = c).
  { intros. assert ((S k) ∈ dom[T1]). { rewrite H5. apply Classifier1; lia. }
    apply x_fx_T in  H7; auto. applyClassifier2 H7. destruct H7 as [H7[H8[]]]; auto. }
  assert (∀ m, ((S k) < m <= (S (S n)))%nat -> T1[m] = T[(m-1)%nat]).
  { intros. assert (m ∈ dom[T1]). { rewrite H5. apply Classifier1; lia. }
    apply x_fx_T in H9; auto. applyClassifier2 H9.
    destruct H9 as [H9[H10[]]]; auto. apply H12. lia. }
  assert (Seg T1 a b (((S n) + 1)%nat)).
  { replace ((S n) + 1)%nat with (S (S n)); [ |lia].
    split; auto. split. lia. split; auto.
    pose proof H0 as [H10[H11[H12[H13[]]]]]. split. intros.
    assert (k0 <= k \/ k0 = S k \/ (S k) < k0)%nat as [H16|[]]. lia.
    assert (k0 < k \/ k0 = k)%nat as []. lia. rewrite H6,H6; auto.
    apply H13. lia. rewrite H17,H6,H7; auto. lra. rewrite H16,H7,H8; auto.
    simpl. lra. lia. rewrite H8,H8; auto.
    replace ((S k0) - 1)%nat with (S (k0 - 1)%nat). apply H13. lia.
    lia. lia. rewrite H6,H8; simpl; auto. lia. lia. }
  exists T1,(S k). right. split; [ |split]; auto; [ |lia]. split; auto.
  split; auto. red; intros. apply Classifier1 in H10 as []. apply Classifier1.
  assert (x ∈ dom[T]). { apply Classifier1; eauto. }
  pose proof H0 as [H12[H13[H14[H15[]]]]]. rewrite H14 in H11. applyClassifier1 H11.
  assert (x <= k \/ (S k) <= x)%nat as [H18|H18]. lia.
  exists x. apply Classifier2; split. lia. split; intros.
  apply f_x_T in H10; auto. split; intros; exfalso; lia.
  assert ((S k) < (S x) <= S (S n))%nat. lia. pose proof H19. apply H8 in H20.
  simpl in H20. rewrite Nat.sub_0_r in H20. exists (S x). apply Classifier2; split.
  lia. split; [ |split]; intros; try (exfalso; lia). simpl.
  rewrite Nat.sub_0_r. apply f_x_T in H10; auto.
Qed.

(* 两个求和式间的一种大小比较 *)
Lemma Lemma9_4_4b : ∀ f g m n, (n <= m)%nat -> (∀ k, (k <= m)%nat -> 0 <= f[k])
  -> (∃ l, (0 <= l <= (m - n))%nat /\ (∀ k, (k <= n)%nat -> g[k] = f[(k+l)%nat]))
  -> (Σ g n) <= (Σ f m).
Proof.
  intros. destruct H1 as [l[]]. set (f1 := \{\ λ u v, v = f[(u + l)%nat] \}\).
  assert ((Σ f1 (m - l)%nat) <= Σ f m).
  { assert (l <= m)%nat. lia. clear dependent n. generalize dependent l.
    induction m; intros. assert (l = 0)%nat. lia. rewrite H. simpl. unfold f1.
    rewrite FunValue. rewrite H. simpl. lra.
    assert (l <= m \/ l = S m)%nat as []. lia. pose proof H.
    apply IHm in H1; auto. replace ((S m) - l)%nat with (S (m - l)%nat); [ |lia].
    simpl. unfold f1. rewrite FunValue.
    replace ((S (m-l)) + l)%nat with (S m); [ |lia]. lra.
    rewrite <-H in *. replace (l - l)%nat with 0%nat; [ |lia]. simpl.
    unfold f1. rewrite FunValue. simpl. clear dependent f1. clear IHm H H3.
    induction l. simpl. lra. simpl. assert (0 <= (Σ f l)).
    { clear IHl. induction l. simpl. apply H0. lia. simpl.
      assert (0 <= (Σ f l)). { apply IHl. auto. }
      assert (0 <= f[S l]). { apply H0. lia. } lra. } lra. }
  assert ((Σ g n) <= (Σ f1 (m-l)%nat)).
  { assert (∀ k, (k <= n)%nat -> g[k] = f1[k]).
    { intros. unfold f1. rewrite FunValue; auto. }
    assert (n <= (m-l))%nat. lia. remember (m - l)%nat.
    assert (∀ k, (k <= n0)%nat -> 0 <= f1[k]).
    { intros. unfold f1. rewrite FunValue. apply H0. lia. }
    clear Heqn0. clear dependent m. induction n0. assert (n = 0)%nat. lia.
    rewrite H. simpl. rewrite H4. lra. lia. assert (n <= n0 \/ n = S n0)%nat.
    lia. destruct H. simpl. assert ((Σ g n) <= (Σ f1 n0)). { apply IHn0; auto. }
    assert (0 <= f1[S n0]). { apply H6. lia. } lra. rewrite <-H.
    apply Rge_le,Σ_Fact3. intros. rewrite H4; auto. lra. } lra.
Qed.

Property Property9_4_4a : ∀ f a b, a < b -> (∃ J, Def_Integral f a b J)
  <-> (∀ c, a < c < b -> ∃ J1 J2, Def_Integral f a c J1 /\ Def_Integral f c b J2).
Proof.
  split; intros.
  - apply Theorem9_3b in H0 as []; auto.
    assert (∀ δ, δ > 0 -> ∃ T n, Seg T a b (S n)
      /\ Σ \{\ λ u v, v = amp f ((\[T[u], T[S u]\])) * (T[S u] - T[u]) \}\ n < δ
      /\ (∃ k, (0 < k <= n)%nat /\ T[k] = c)).
    { intros. apply H2 in H3 as [T[n[]]]. pose proof H3.
      apply (Lemma9_4_4a T a b c) in H5 as [T1[k[[H5[]]|[H5[]]]]]; auto.
      exists T1,n. rewrite H5. split; auto. split; auto. exists k. rewrite <-H5.
      auto. pose proof H5 as [H8[]]. simpl in H9. exists T1,(n+1)%nat.
      split; auto. split. apply (Lemma9_4_3g f) in H5; auto. lra.
      exists k. split; auto. lia. }
    assert (∃ J, Def_Integral f a c J) as [J1].
    { apply Theorem9_3b. lra. split. destruct H0 as [H0[H4[M]]]. split; auto.
      assert (\[a, c\] ⊂ \[a, b\]).
      { red; intros. applyClassifier1 H6. apply Classifier1; lra. }
      split; eauto. red; auto. intros. apply H3 in H4 as [T[n[H4[H5[k[]]]]]].
      set (T1 := \{\ λ u v, (u <= k)%nat /\ v = T[u] \}\).
      assert (Function T1).
      { red; intros. applyClassifier2 H8. applyClassifier2 H9.
        destruct H8 as [], H9 as []. rewrite H10,H11; auto. }
      assert (dom[T1] = \{ λ u, (u <= (S (k-1)))%nat \}).
      { apply AxiomI; split; intros. apply Classifier1 in H9 as [].
        applyClassifier2 H9. destruct H9. apply Classifier1; lia. applyClassifier1 H9.
        apply Classifier1. exists T[z]. apply Classifier2; split; auto. lia. }
      assert (∀ m, (m <= k)%nat -> T1[m] = T[m]).
      { intros. assert (m ∈ dom[T1]). { rewrite H9. apply Classifier1; lia. }
        apply x_fx_T in H11; auto. applyClassifier2 H11. tauto. }
      exists T1,(k-1)%nat. split. split; auto. split. lia. split; auto.
      destruct H4 as [H4[H11[H12[H13[]]]]]. split. intros. rewrite H10,H10;
      try lia. apply H13. lia. rewrite H10,H10; try lia. split; auto.
      replace (S (k-1)%nat) with k; [ |lia]. auto.
      assert (Σ \{\ λ u v, v = (amp f (\[T1[u], T1[S u]\]))
        * (T1[S u] - T1[u]) \}\ (k-1)%nat
        <= Σ \{\ λ u v, v = (amp f (\[T[u], T[S u]\])) * (T[S u] - T[u]) \}\ n).
      { apply Lemma9_4_4b. lia. intros. rewrite FunValue.
        assert (DBoundedFun f (\[T[k0], T[S k0]\])).
        { destruct H0 as [H0[H12[]]]. split; auto.
          assert (\[T[k0], T[S k0]\] ⊂ \[a, b\]).
          { red; intros. apply Classifier1 in H14 as []. pose proof H4
            as [_[_[_[_[]]]]]. rewrite <-H16,<-H17. apply Classifier1.
            assert (T[0%nat] <= T[k0] /\ T[S k0] <= T[S n]).
            { split; apply (Seg_Increase_a T a b (S n)); auto; lia. } lra. }
          split; eauto. red; auto. }
          assert (T[k0] < T[S k0]). { destruct H4 as [_[_[_[]]]]. apply H4; lia. }
          apply Rmult_le_pos. apply sup_inf_Coro_2 in H12. unfold amp. lra.
        exists ((T[k0] + T[S k0])/2). apply Classifier1. lra. lra. exists 0%nat.
        split. lia. intros. rewrite FunValue,FunValue.
        replace (k0 + 0)%nat with k0; auto. rewrite H10,H10; auto; lia. } lra. }
    assert (∃ J, Def_Integral f c b J) as [J2].
    { apply Theorem9_3b. lra. split. destruct H0 as [H0[H5[M]]]. split; auto.
      assert (\[c, b\] ⊂ \[a, b\]).
      { red; intros. applyClassifier1 H7. apply Classifier1; lra. }
      split; eauto. red; auto. intros. apply H3 in H5 as [T[n[H5[H6[k[]]]]]].
      set (T1 := \{\ λ u v, (u <= (S n) - k)%nat /\ v = T[(u + k)%nat] \}\).
      assert (Function T1).
      { red; intros. applyClassifier2 H9. applyClassifier2 H10.
        destruct H9 as [], H10 as []. rewrite H11,H12; auto. }
      assert (dom[T1] = \{ λ u, (u <= (S (n-k)))%nat \}).
      { apply AxiomI; split; intros. apply Classifier1 in H10 as [].
        apply ->Classifier2 in H10. destruct H10. apply Classifier1. lia.
        applyClassifier1 H10. apply Classifier1. exists T[(z+k)%nat].
        apply Classifier2; split; auto. lia. }
      assert (∀ m, (m <= (S (n-k)))%nat -> T1[m] = T[(m+k)%nat]).
      { intros. assert (m ∈ dom[T1]). { rewrite H10. apply Classifier1; lia. }
        apply x_fx_T in H12; auto. apply ->Classifier2 in H12. destruct H12. auto. }
      exists T1,(n-k)%nat. split. split; auto. split. lia. split; auto.
      destruct H5 as [H5[H12[H13[H14[]]]]]. split. intros. rewrite H11,H11;
      try lia. apply H14. lia. rewrite H11,H11; try lia. split; auto.
      replace ((S (n-k)) + k)%nat with (S n); [ |lia]. auto.
      assert (Σ \{\ λ u v, v = (amp f (\[T1[u], T1[S u]\]))
        * (T1[S u] - T1[u]) \}\ (n-k)%nat
        <= Σ \{\ λ u v, v = (amp f (\[T[u], T[S u]\])) * (T[S u] - T[u]) \}\ n).
      { apply Lemma9_4_4b. lia. intros. rewrite FunValue.
        assert (DBoundedFun f (\[T[k0], T[S k0]\])).
        { destruct H0 as [H0[H13[]]]. split; auto.
          assert (\[T[k0], T[S k0]\] ⊂ \[a, b\]).
          { red; intros. apply Classifier1 in H15 as []. pose proof H5
            as [_[_[_[_[]]]]]. rewrite <-H17,<-H18. apply Classifier1.
            assert (T[0%nat] <= T[k0] /\ T[S k0] <= T[S n]).
            { split; apply (Seg_Increase_a T a b (S n)); auto; lia. } lra. }
          split; eauto. red; auto. }
        assert (T[k0] < T[S k0]). { destruct H5 as [_[_[_[]]]]. apply H5; lia. }
        apply Rmult_le_pos. apply sup_inf_Coro_2 in H13. unfold amp. lra.
        exists ((T[k0] + T[S k0])/2). apply Classifier1. lra. lra. exists k.
        split. lia. intros. rewrite FunValue,FunValue,H11,H11; auto; lia. } lra. }
    eauto.
  - set (c := (a + b)/2). assert (a < c < b). unfold c. lra. apply H0 in H1
    as [J1[J2[]]]. apply (Lemma9_5c f a c b); eauto. unfold c. lra.
Qed.

Property Property9_4_4b : ∀ f a b c J1 J2 J, c ∈ \(a, b\)
  -> Def_Integral f a c J1 -> Def_Integral f c b J2 -> Def_Integral f a b J
  -> J = J1 + J2.
Proof.
  intros. apply NNPP; intro. assert (∣(J - (J1 + J2))∣ > 0).
  { apply Abs_not_eq_0. lra. }
  assert (∀ ε, 0 < ε -> ∣(J - (J1 + J2))∣ < 3*ε).
  { destruct H0 as [H0[H5[]]], H1 as [H1[H8[]]], H2 as [H2[H11[]]].
    intros. pose proof H14. pose proof H14. apply H7 in H14 as [δ1[]].
    apply H10 in H15 as [δ2[]]. apply H13 in H16 as [δ[]].
    destruct (Examp2 δ1 δ2 δ) as [δ3[H20[H21[]]]]; auto.
    destruct (Examp2 δ3 (c-a) (b-c)) as [δ0[H24[H25[]]]]; auto; try lra.
    assert (0 < δ0 <= c - a /\ 0 < δ0 <= b - c) as []. lra.
    apply Seg_Exists in H28 as [T1[n1[]]], H29 as [T2[n2[]]]; auto.
    set (T := \{\ λ u v, (u <= (S (S (n1+n2))))%nat
      /\ ((u <= (S n1))%nat -> v = T1[u])
      /\ (((S n1) < u <= (S (S (n1+n2))))%nat -> v = T2[(u - (S n1))%nat]) \}\).
    assert (Function T).
    { red; intros. applyClassifier2 H32. applyClassifier2 H33.
      destruct H32 as [H32[]], H33 as [H33[]].
      assert (x <= (S n1) \/ (S n1) < x <= (S (S (n1 + n2))))%nat as []. lia.
      rewrite H34,H36; auto. rewrite H35,H37; auto. }
    assert (dom[T] = \{ λ u, (u <= (S (S (n1 + n2))))%nat \}).
    { apply AxiomI; split; intros. apply Classifier1 in H33 as [].
      applyClassifier2 H33. destruct H33 as []. apply Classifier1; auto.
      applyClassifier1 H33.
      assert (z <= (S n1) \/ (S n1) < z <= (S (S (n1 + n2))))%nat as []. lia.
      apply Classifier1. exists T1[z]. apply Classifier2; repeat split; auto.
      intros. exfalso. lia. apply Classifier1. exists T2[(z - (S n1))%nat].
      apply Classifier2; repeat split; auto. intros. exfalso. lia. }
    assert (∀ k, (k <= (S n1))%nat -> T[k] = T1[k]).
    { intros. assert (k ∈ dom[T]). { rewrite H33. apply Classifier1. lia. }
      apply x_fx_T in H35; auto. applyClassifier2 H35.
      destruct H35 as [H35[]]; auto. }
    assert (∀ k, ((S n1) < k <= S (S (n1 + n2)))%nat
      -> T[k] = T2[(k - (S n1))%nat]).
    { intros. assert (k ∈ dom[T]). { rewrite H33. apply Classifier1. lia. }
      apply x_fx_T in H36; auto. applyClassifier2 H36.
      destruct H36 as [H36[H37[]]]; auto. }
    assert (Seg T a b (S (S (n1 + n2)%nat))
      /\ SegMold T (S (S (n1 + n2)%nat)) δ0) as [].
    { pose proof H28 as [_[_[_[H36[]]]]]. pose proof H29 as [_[_[_[H39[]]]]].
      split. split; auto. split. lia. split; auto. split. intros.
      assert (k < (S n1) \/ k = (S n1) \/ (S n1) < k < S (S (n1 + n2)))%nat
      as [H43|[]]. lia. rewrite H34,H34; try lia; auto. rewrite H43,H34,H35;
      try lia. rewrite H38,<-H40. replace (S (S n1) - (S n1))%nat with 1%nat.
      apply H39. lia. lia. rewrite H35,H35; try lia.
      replace ((S k) - (S n1))%nat with (S (k - (S n1)))%nat; [ |lia].
      apply H29. lia. rewrite H34,H35; try lia. split; auto.
      replace (S (S (n1 + n2)) - (S n1))%nat with (S n2); auto. lia.
      assert (δ0 ∈ \{ λ u, SegMold T1 (S n1) u \}
        /\ δ0 ∈ \{ λ u, SegMold T2 (S n2) u \}) as [].
      { apply SegMold_Exists in H28 as [], H29 as [].
        split; [rewrite H30|rewrite H31]; apply Axiomc; [exists x|exists x0];
        apply Classifier1; auto. }
      apply Classifier1 in H42 as [[x1[]]], H43 as [[x2[]]]. split. exists x1.
      split. lia. rewrite H34,H34; auto. lia. intros.
      assert (m < (S n1) \/ m = (S n1) \/ (S n1) < m < S (S (n1 + n2)))%nat
      as [H49|[]]. lia. rewrite H34,H34; try lia. auto. rewrite H49,H35,H34;
      try lia. rewrite H38,<-H40. replace (S (S n1) - (S n1))%nat with 1%nat.
      apply H47. lia. lia. rewrite H35,H35; try lia.
      replace ((S m) - (S n1))%nat with (S (m - (S n1)))%nat; [ |lia].
      apply H47. lia. }
    assert (mold T (S (S (n1 + n2)%nat)) = δ0).
    { assert (δ0 ∈ \{ λ u, SegMold T (S (S (n1 + n2)%nat)) u \}
        /\ (mold T (S (S (n1 + n2)%nat)))
           ∈ \{ λ u, SegMold T (S (S (n1 + n2)%nat)) u \}) as [].
      { split. apply Classifier1; auto. apply Axiomc.
        apply SegMold_Exists in H36 as []. exists x. apply Classifier1; auto. }
      apply SegMold_Unique in H36 as []. rewrite H36 in H38,H39.
      applyClassifier1 H38. applyClassifier1 H39. rewrite H38,H39; auto. }
    set (ξ1 := \{\ λ u v, v = (T1[u] + T1[S u])/2 \}\).
    set (ξ2 := \{\ λ u v, v = (T2[u] + T2[S u])/2 \}\).
    assert (SegPoints T1 ξ1 (S n1)).
    { red; intros. unfold ξ1. rewrite FunValue. assert (T1[k] < T1[S k]).
      { destruct H28 as [_[_[_[]]]]. apply H28; lia. } lra. }
    assert (SegPoints T2 ξ2 (S n2)).
    { red; intros. unfold ξ2. rewrite FunValue. assert (T2[k] < T2[S k]).
      { destruct H29 as [_[_[_[]]]]. apply H29; lia. } lra. }
    set (ξ := \{\ λ u v, v = (T[u] + T[S u])/2 \}\).
    assert (SegPoints T ξ (S (S (n1 + n2)%nat))).
    { red; intros. unfold ξ. rewrite FunValue. assert (T[k] < T[S k]).
      { destruct H36 as [_[_[_[]]]]. apply H36; lia. } lra. }
    assert (∣((IntegralSum f T1 n1 ξ1) - J1)∣ < ε).
    { apply H17; auto. rewrite <-H30. lra. }
    assert (∣((IntegralSum f T2 n2 ξ2) - J2)∣ < ε).
    { apply H18; auto. rewrite <-H31. lra. }
    assert (∣((IntegralSum f T (S (n1 + n2)%nat) ξ) - J)∣ < ε).
    { apply H19; auto. rewrite H38. lra. }
    assert (∣(((IntegralSum f T1 n1 ξ1) - J1) + ((IntegralSum f T2 n2 ξ2) - J2))∣
      <= ∣((IntegralSum f T1 n1 ξ1) - J1)∣ + ∣((IntegralSum f T2 n2 ξ2) - J2)∣).
    { apply Abs_plus_le. }
    replace (((IntegralSum f T1 n1 ξ1) - J1) + ((IntegralSum f T2 n2 ξ2) - J2))
    with (((IntegralSum f T1 n1 ξ1) + (IntegralSum f T2 n2 ξ2)) - (J1 + J2))
    in H45; [ |lra].
    assert ((IntegralSum f T1 n1 ξ1) + (IntegralSum f T2 n2 ξ2)
      = IntegralSum f T (S (n1 + n2)%nat) ξ).
    { assert (∀ h m1 m2, Σ h (S (m1 + m2)%nat)
        = (Σ h m1) + (Σ \{\ λ u v, v = h[(u + (S m1))%nat] \}\ m2)).
      { intros. induction m2. simpl. rewrite FunValue,Nat.add_0_r,Nat.add_0_l;
        auto. simpl. rewrite FunValue. replace (m1 + (S m2))%nat with
        (S (m1 + m2)%nat); [ |lia]. rewrite IHm2.
        replace ((S m2) + (S m1))%nat with (S (S (m1 + m2)%nat)). lra. lia. }
      unfold IntegralSum at 3. rewrite H46.
      assert (IntegralSum f T1 n1 ξ1
        = Σ \{\ λ i s, s = f[ξ[i]] * (T[S i] - T[i]) \}\ n1).
      { apply Σ_Fact5. intros. rewrite FunValue,FunValue,H34,H34; try lia.
        unfold ξ,ξ1. rewrite FunValue,FunValue,H34,H34; auto. lia. }
      assert (IntegralSum f T2 n2 ξ2 = Σ \{\ λ u v, v
        = \{\ λ i s, s = f[ξ[i]] * (T[S i] - T[i]) \}\[(u + (S n1))%nat] \}\ n2).
      { apply Σ_Fact5. intros. rewrite FunValue,FunValue,FunValue. destruct x.
        destruct H28 as [_[_[_[_[]]]]], H29 as [_[_[_[_[]]]]].
        rewrite H35,Nat.add_0_l,H34,H29,H49; try lia.
        replace (S (S n1) - (S n1))%nat with 1%nat; [ |lia].
        unfold ξ,ξ2. rewrite FunValue,FunValue,H34,H35,H29,H49; try lia.
        replace (S (S n1) - (S n1))%nat with 1%nat; [ |lia]. auto.
        rewrite H35,H35; try lia.
        replace (S (S x + S n1) - (S n1))%nat with (S (S x)); [ |lia].
        replace (S x + (S n1) - (S n1))%nat with (S x); [ |lia].
        unfold ξ,ξ2. rewrite FunValue,FunValue,H35,H35; try lia.
        replace (S (S x + S n1) - (S n1))%nat with (S (S x)); [ |lia].
        replace (S x + (S n1) - (S n1))%nat with (S x); [ |lia]. auto. }
      rewrite H47,H48; auto. } rewrite H46 in H45.
    assert (∣((IntegralSum f T (S (n1 + n2)%nat) ξ) - (J1 + J2))∣ < 2*ε). lra.
    assert (∣(((IntegralSum f T (S (n1 + n2))%nat ξ) - (J1 + J2))
      - ((IntegralSum f T (S (n1 + n2))%nat ξ) - J))∣
    <= ∣((IntegralSum f T (S (n1 + n2))%nat ξ) - (J1 + J2))∣
      + ∣((IntegralSum f T (S (n1 + n2))%nat ξ) - J)∣). { apply Abs_minus_le. }
    replace (((IntegralSum f T (S (n1 + n2))%nat ξ) - (J1 + J2))
      - ((IntegralSum f T (S (n1 + n2))%nat ξ) - J)) with (J - (J1 + J2))
    in H48; [ |lra]. lra. }
  assert (0 < ∣(J - (J1 + J2))∣/3). lra. apply H5 in H6. lra.
Qed.


Property Property9_4_5a : ∀ f a b J, Def_Integral f a b J
  -> (∀ x, x ∈ \[a, b\] -> f[x] >= 0) -> J >= 0.
Proof.
  intros. destruct (Rlt_or_le J 0); [ |lra]. assert (0 < -J). lra.
  destruct H as [H[H3[]]]. apply H5 in H2 as [δ[]].
  destruct (Examp1 δ (b-a)) as [δ0[H7[]]]; try lra.
  assert (0 < δ0 <= b-a). lra. apply Seg_Exists in H10 as [T[n[]]]; auto.
  set (ξ := \{\ λ u v, v = (T[u] + T[S u])/2 \}\).
  assert (SegPoints T ξ (S n)).
  { red; intros. unfold ξ. rewrite FunValue.
    assert (T[k] < T[S k]). { destruct H10 as [_[_[_[]]]]; auto. } lra. }
  assert (∣((IntegralSum f T n ξ) - J)∣ < -J).
  { apply H6; auto. rewrite <-H11; auto. }
  assert (0 <= (IntegralSum f T n ξ)).
  { assert (∀ h m, (∀ k, (k <= m)%nat -> 0 <= h[k]) -> 0 <= (Σ h m)).
    { intros. induction m. simpl; auto. simpl. assert (0 <= h[S m]); auto.
      assert (0 <= (Σ h m)). { apply IHm; auto. } lra. }
    apply H14. intros. rewrite FunValue.
    assert (0 < (T[S k] - T[k])).
    { destruct H10 as [_[_[_[]]]]. assert (k < (S n))%nat. lia.
      apply H10 in H17. lra. }
    assert (f[ξ[k]] >= 0).
    { apply H0. assert (T[k] < ξ[k] < T[S k]).
      { unfold ξ. rewrite FunValue. lra. }
      assert (a <= T[k] /\ T[S k] <= b) as [].
      { pose proof H10 as [_[_[_[_[]]]]]. rewrite <-H18,<-H19.
        split; apply (Seg_Increase_a T a b (S n)); auto; lia. }
      apply Classifier1. lra. } apply Rmult_le_pos; lra. }
  rewrite Abs_ge in H13. exfalso. lra. lra.
Qed.

Property Property9_4_5b : ∀ f a b J, Def_Integral f a b J
  -> (∀ x, x ∈ \[a, b\] -> f[x] <= 0) -> J <= 0.
Proof.
  intros. destruct (Rlt_or_le 0 J); [ |lra].
  destruct H as [H[H3[]]]. pose proof H1. apply H4 in H5 as [δ[]].
  destruct (Examp1 δ (b-a)) as [δ0[H7[]]]; try lra.
  assert (0 < δ0 <= b-a). lra. apply Seg_Exists in H10 as [T[n[]]]; auto.
  set (ξ := \{\ λ u v, v = (T[u] + T[S u])/2 \}\).
  assert (SegPoints T ξ (S n)).
  { red; intros. unfold ξ. rewrite FunValue.
    assert (T[k] < T[S k]). { destruct H10 as [_[_[_[]]]]; auto. } lra. }
  assert (∣((IntegralSum f T n ξ) - J)∣ < J).
  { apply H6; auto. rewrite <-H11; auto. }
  assert ((IntegralSum f T n ξ) <= 0).
  { assert (∀ h m, (∀ k, (k <= m)%nat -> h[k] <= 0) -> (Σ h m) <= 0).
    { intros. induction m. simpl; auto. simpl. assert (h[S m] <= 0); auto.
      assert ((Σ h m) <= 0). { apply IHm; auto. } lra. }
    apply H14. intros. rewrite FunValue.
    assert (0 < (T[S k] - T[k])).
    { destruct H10 as [_[_[_[]]]]. assert (k < (S n))%nat. lia.
      apply H10 in H17. lra. }
    assert (f[ξ[k]] <= 0).
    { apply H0. assert (T[k] < ξ[k] < T[S k]).
      { unfold ξ. rewrite FunValue. lra. }
      assert (a <= T[k] /\ T[S k] <= b) as [].
      { pose proof H10 as [_[_[_[_[]]]]]. rewrite <-H18,<-H19.
        split; apply (Seg_Increase_a T a b (S n)); auto; lia. }
      apply Classifier1. lra. } apply Rmult_leq_gre; lra. }
  rewrite Abs_lt in H13. exfalso. lra. lra.
Qed.

(* 性质5的推论 *)
Corollary Corollary9_4_5 : ∀ f g a b J1 J2, Def_Integral f a b J1
  -> Def_Integral g a b J2 -> (∀ x, x ∈ \[a, b\] -> f[x] <= g[x])
  -> J1 <= J2.
Proof.
  intros. assert(J2 - J1 >= 0).
  { apply (Property9_4_5a (g \- f) a b). apply Property9_4_2b; auto. intros.
    destruct H as [_[_[]]], H0 as [_[_[]]]. rewrite Corollary_sub_fun_b; auto.
    apply H1 in H2. lra. } lra.
Qed.


Property Property9_4_6a : ∀ f a b, (∃ J, Def_Integral f a b J)
  -> (∃ J, Def_Integral (\{\ λ u v, u ∈ dom[f] /\ v = ∣(f[u])∣ \}\) a b J).
Proof.
  intros. assert (a < b). { destruct H as [J[_[]]]; auto. }
  apply Theorem9_3b in H as []; auto. apply Theorem9_3b; auto.
  set (fa := \{\ λ u v, u ∈ dom[f] /\ v = ∣(f[u])∣ \}\).
  assert (Function fa).
  { red; intros. applyClassifier2 H2. applyClassifier2 H3. destruct H2,H3.
    rewrite H4,H5; auto. }
  assert (dom[fa] = dom[f]).
  { apply AxiomI; split; intros; apply Classifier1 in H3 as [].
    applyClassifier2 H3. destruct H3 as []; auto. apply Classifier1.
    exists ∣(f[z])∣. apply Classifier2; split; auto. apply Classifier1; eauto. }
  assert (∀ x, x ∈ dom[f] -> fa[x] = ∣(f[x])∣).
  { intros. rewrite <-H3 in H4. apply x_fx_T in H4; auto. applyClassifier2 H4.
    tauto. }
  assert (DBoundedFun fa (\[a, b\])).
  { split; auto. destruct H as [H[H5[M]]]. rewrite H3. split; auto.
    exists M. intros. rewrite H4,Abs_ge; auto. apply Abs_Rge0. } split; auto.
  intros. pose proof (H1 δ H6) as [T[n[]]]. exists T,n. split; auto.
  assert (Σ \{\ λ u v, v = (amp f (\[T[u], T[S u]\])) * (T[S u] - T[u]) \}\ n
    >= Σ \{\ λ u v, v = (amp fa (\[T[u], T[S u]\])) * (T[S u] - T[u]) \}\ n).
  { apply Σ_Fact3. intros. rewrite FunValue,FunValue. pose proof H7 as
    [H10[H11[H12[H13[]]]]]. assert (T[i] < T[S i]). { apply H13. lia. }
    apply Rle_ge,Rmult_le_compat_r. lra.
    assert (\[T[i], T[S i]\] ⊂ \[a, b\]).
    { red; intros. applyClassifier1 H17. assert (a <= T[i] /\ T[S i] <= b).
      { pose proof H7 as [H18[H19[H20[H21[]]]]]. rewrite <-H22,<-H23.
        split; apply (Seg_Increase_a T a b (S n)); auto; lia. }
      apply Classifier1. lra. }
    assert (DBoundedFun f (\[T[i], T[S i]\])
      /\ DBoundedFun fa (\[T[i], T[S i]\])) as [].
    { destruct H as [H[H18[M1]]], H5 as [H5[H20[M2]]].
      repeat split; try red; eauto. }
    assert (NotEmpty (\[T[i], T[S i]\])).
    { exists ((T[i] + T[S i])/2). apply Classifier1. lra. }
    apply Lemma9_4_3c in H18,H19; auto. eapply Lemma9_4_3d; eauto. intros.
    apply Classifier1 in H21 as [x1[x2[H21[]]]]. exists ∣(f[x1] - f[x2])∣. split.
    apply Classifier1; eauto. rewrite H23. destruct H as [_[]]. rewrite H4,H4; auto.
    apply Abs_abs_minus. } lra.
Qed.

Property Property9_4_6b : ∀ f a b J1 J2, Def_Integral f a b J1
  -> Def_Integral (\{\ λ u v, u ∈ dom[f] /\ v = ∣(f[u])∣ \}\) a b J2
  -> ∣J1∣ <= J2.
Proof.
  intros. set (fa := \{\ λ u v, u ∈ dom[f] /\ v = ∣(f[u])∣ \}\).
  assert (Function fa).
  { red; intros. applyClassifier2 H1. applyClassifier2 H2.
    destruct H1,H2. rewrite H3,H4; auto. }
  assert (dom[fa] = dom[f]).
  { apply AxiomI; split; intros; apply Classifier1 in H2 as [].
    applyClassifier2 H2. destruct H2 as []; auto. apply Classifier1.
    exists ∣(f[z])∣. apply Classifier2; split; auto. apply Classifier1; eauto. }
  assert (∀ x, x ∈ dom[f] -> fa[x] = ∣(f[x])∣).
  { intros. rewrite <-H2 in H3. apply x_fx_T in H3; auto. applyClassifier2 H3.
    tauto. }
  assert (∀ x, x ∈ (\[a, b\]) -> f[x] <= fa[x]).
  { intros. rewrite H3. apply Abs_neg_pos. destruct H as [_[_[]]]; auto. }
  assert (Def_Integral (fa \\* (-1)) a b (-J2)).
  { replace (-J2) with (-1 * J2). apply Property9_4_1; auto. lra. }
  assert (∀ x, x ∈ (\[a, b\]) -> (fa \\* (-1))[x] <= f[x]).
  { intros. assert (x ∈ dom[fa \\* (-1)]).
    { rewrite Corollary_mult_fun_d,H2. destruct H as [_[_[]]]; auto. }
    apply x_fx_T in H7; auto. applyClassifier2 H7. destruct H7 as [].
    rewrite H8,H3. replace (∣(f[x])∣ * (-1)) with (-∣(f[x])∣).
    apply Abs_neg_pos. lra. rewrite <-H2; auto. red; intros.
    applyClassifier2 H8. applyClassifier2 H9. destruct H8,H9.
    rewrite H10,H11; auto. }
  apply (Corollary9_4_5 _ _ _ _ J1 J2) in H4; auto.
  apply (Corollary9_4_5 _ _ _ _ (-J2) J1) in H6; auto. apply Abs_le_R; auto.
Qed.

(* 常值函数的积分 *)
Lemma Lemma9_7 : ∀ M a b, a < b
  -> Def_Integral \{\ λ u v, v = M \}\ a b (M * (b-a)).
Proof.
  intros. assert (Function \{\ λ (u : R) v, v = M \}\).
  { red; intros. applyClassifier2 H0. applyClassifier2 H1. rewrite H0,H1; auto. }
  assert(\[a, b\] ⊂ dom[\{\ λ u v, v = M \}\]).
  { red. intros. apply Classifier1. exists M. apply Classifier2; auto. }
  apply Lemma9_6; auto. intros. rewrite FunValue; auto.
Qed.

(* 积分第一中值定理 *)
Theorem Theorem9_7 : ∀ f a b, a < b -> ContinuousClose f a b
  -> (∃ ξ, ξ ∈ \[a, b\] /\ Def_Integral f a b (f[ξ] * (b-a))).
Proof.
  intros. assert (∃ J, Def_Integral f a b J) as [J]. apply Theorem9_4; auto.
  pose proof H0. apply Theorem4_6 in H2 as [[M][m]]; auto.
  set (g1 := \{\ λ (i : R) s, s = M \}\). set (g2 := \{\ λ (i : R) s, s = m \}\).
  pose proof (Lemma9_7 M a b H). pose proof (Lemma9_7 m a b H).
  assert ((m * (b-a)) <= J).
  { apply (Corollary9_4_5 g2 f a b); auto. intros. unfold g2. rewrite FunValue.
    destruct H3 as [_[]]; auto. }
  assert (J <= (M * (b-a))).
  { apply (Corollary9_4_5 f g1 a b); auto. intros. unfold g1. rewrite FunValue.
    destruct H2 as [_[]]; auto. }
  destruct H2 as [H2[H8[x1[]]]], H3 as [H3[H11[x2[]]]].
  destruct H6. destruct H7. assert (m < J/(b-a) < M).
  { split; apply (Rmult_lt_reg_r (b-a)); try lra; unfold Rdiv;
    rewrite Rmult_assoc,(Rmult_comm (/(b-a))),Rinv_r,Rmult_1_r; auto; lra. }
  rewrite <-H10,<-H13 in H14. assert (x1 < x2 \/ x2 < x1) as [].
  destruct (Rtotal_order x1 x2) as [H15|[]]; auto. rewrite H15 in H14.
  exfalso. lra. assert (ContinuousClose f x1 x2).
  { destruct H0 as [H0[]]. apply Classifier1 in H9 as [], H12 as []. split.
    red; intros. apply H0. lra. split. destruct H9. apply Theorem4_1,H0. lra.
    rewrite H9; auto. destruct H19. apply Theorem4_1,H0. lra. rewrite H19; auto. }
  apply (Theorem4_7 f x1 x2 (J/(b-a))) in H16 as [ξ[]]; auto. exists ξ. split.
  apply Classifier1. applyClassifier1 H9. applyClassifier1 H12. lra. unfold Rdiv in H17.
  rewrite H17,Rmult_assoc,(Rmult_comm (/(b-a))),Rinv_r,Rmult_1_r; auto. lra.
  apply Classifier1 in H9 as [], H12 as []. assert (ContinuousClose f x2 x1).
  { destruct H0 as [H0[]]. split. red; intros. apply H0. lra. split.
    destruct H12. apply Theorem4_1,H0. lra. rewrite H12; auto.
    destruct H16. apply Theorem4_1,H0. lra. rewrite H16; auto. }
  apply (Theorem4_7 f x2 x1 (J/(b-a))) in H18 as [ξ[]]; auto. exists ξ. split.
  apply Classifier1. lra. unfold Rdiv in H19.
  rewrite H19,Rmult_assoc,(Rmult_comm (/(b-a))),Rinv_r,Rmult_1_r; auto. lra.
  exists x1. split; auto. rewrite H10,<-H7; auto. exists x2. split; auto.
  rewrite H13,H6; auto.
Qed.


(* 推广的积分第一中值定理 *)
Theorem Theorem9_8a : ∀ f g a b, a < b
  -> ContinuousClose f a b -> ContinuousClose g a b
  -> (∀ x, x ∈ \[a, b\] -> g[x] >= 0)
  -> (∃ G J, Def_Integral g a b G /\ Def_Integral (f \* g) a b J
    /\ (∃ ξ, ξ ∈ \[a, b\] /\ J = f[ξ] * G)).
Proof.
  intros. pose proof H0. apply Theorem4_6 in H3
  as [[M[H3[H4[x1[]]]]][m[H7[H8[x2[]]]]]]; auto.
  assert (∃ J, Def_Integral (f \* g) a b J) as [J].
  { apply Property9_4_3; apply Theorem9_4; auto. }
  assert (∃ G, Def_Integral g a b G) as [G]. { apply Theorem9_4; auto. }
  exists G,J. split; auto. split; auto.
  assert (Def_Integral (g \\* m) a b (m * G)). { apply Property9_4_1; auto. }
  assert (Def_Integral (g \\* M) a b (M * G)). { apply Property9_4_1; auto. }
  assert ((m * G) <= J).
  { eapply Corollary9_4_5; eauto. intros. destruct H12 as [H12[_[H16 _]]].
    rewrite Corollary_mult_fun_b; auto. assert (Function (g \\* m)).
    { red; intros. applyClassifier2 H17. applyClassifier2 H18.
      destruct H17 as [], H18 as []. rewrite H19,H20; auto. }
    assert (x ∈ dom[g \\* m]). { rewrite Corollary_mult_fun_d; auto. }
    apply x_fx_T in H18; auto. applyClassifier2 H18. destruct H18 as []; auto.
    rewrite H19,Rmult_comm. apply Rmult_le_compat_r; auto. apply H2 in H15. lra. }
  assert (J <= (M * G)).
  { eapply Corollary9_4_5; eauto. intros. destruct H12 as [H12[_[H17 _]]].
    rewrite Corollary_mult_fun_b; auto. assert (Function (g \\* M)).
    { red; intros. applyClassifier2 H18. applyClassifier2 H19.
      destruct H18 as [], H19 as []. rewrite H20,H21; auto. }
    assert (x ∈ dom[g \\* M]). { rewrite Corollary_mult_fun_d; auto. }
    apply x_fx_T in H19; auto. applyClassifier2 H19. destruct H19; auto.
    rewrite H20,Rmult_comm. apply Rmult_le_compat_l; auto. apply H2 in H16. lra. }
  assert (G >= 0) as []. { eapply Property9_4_5a; eauto. }
  assert (m <= J/G /\ J/G <= M) as [].
  { split; apply (Rmult_le_reg_r G); auto; unfold Rdiv;
    rewrite Rmult_assoc,(Rmult_comm (/G)),Rinv_r; lra. }
  destruct H18. destruct H19. apply Classifier1 in H5 as [], H9 as [].
  destruct (Rtotal_order x1 x2) as [H22|[H22|H22]].
  assert (ContinuousClose f x1 x2).
  { destruct H0 as [H0[]]. split. red; intros. apply H0. lra. split.
    destruct H5. apply Theorem4_1,H0. lra. rewrite H5; auto. destruct H21.
    apply Theorem4_1,H0. lra. rewrite H21; auto. }
  apply (Theorem4_7 _ _ _ (J/G)) in H23 as [ξ[]]; auto. exists ξ. split.
  apply Classifier1. lra. unfold Rdiv in H24. rewrite H24,Rmult_assoc,
  (Rmult_comm (/G)),Rinv_r. lra. lra. rewrite H6,H10; auto.
  rewrite <-H10 in H18. rewrite <-H6,H22 in H19. exfalso. lra.
  assert (ContinuousClose f x2 x1).
  { destruct H0 as [H0[]]. split. red; intros. apply H0. lra. split.
    destruct H9. apply Theorem4_1,H0. lra. rewrite H9; auto. destruct H20.
    apply Theorem4_1,H0. lra. rewrite H20; auto. }
  apply (Theorem4_7 _ _ _ (J/G)) in H23 as [ξ[]]; auto. exists ξ. split.
  apply Classifier1. lra. unfold Rdiv in H24. rewrite H24,Rmult_assoc,
  (Rmult_comm (/G)),Rinv_r. lra. lra. rewrite H6,H10; auto.
  exists x1. split; auto. unfold Rdiv in H19. rewrite H6,<-H19,Rmult_assoc,
  (Rmult_comm (/G)),Rinv_r. lra. lra. exists x2. split; auto. unfold Rdiv in H18.
  rewrite H10,H18,Rmult_assoc,(Rmult_comm (/G)),Rinv_r. lra. lra.
  rewrite H17 in H15,H16. assert (J = 0). lra. rewrite H17,H18. exists x1.
  split; auto. lra.
Qed.

Theorem Theorem9_8b : ∀ f g a b, a < b
  -> ContinuousClose f a b -> ContinuousClose g a b
  -> (∀ x, x ∈ \[a, b\] -> g[x] <= 0)
  -> (∃ G J, Def_Integral g a b G /\ Def_Integral (f \* g) a b J
    /\ (∃ ξ, ξ ∈ \[a, b\] /\ J = f[ξ] * G)).
Proof.
  intros. pose proof H0. apply Theorem4_6 in H3
  as [[M[H3[H4[x1[]]]]][m[H7[H8[x2[]]]]]]; auto.
  assert (∃ J, Def_Integral (f \* g) a b J) as [J].
  { apply Property9_4_3; apply Theorem9_4; auto. }
  assert (∃ G, Def_Integral g a b G) as [G]. { apply Theorem9_4; auto. }
  exists G,J. split; auto. split; auto.
  assert (Def_Integral (g \\* m) a b (m * G)). { apply Property9_4_1; auto. }
  assert (Def_Integral (g \\* M) a b (M * G)). { apply Property9_4_1; auto. }
  assert (J <= (m * G)).
  { eapply Corollary9_4_5; eauto. intros. destruct H12 as [H12[_[H16 _]]].
    rewrite Corollary_mult_fun_b; auto. assert (Function (g \\* m)).
    { red; intros. applyClassifier2 H17. applyClassifier2 H18.
      destruct H17,H18. rewrite H19,H20; auto. }
    assert (x ∈ dom[g \\* m]). { rewrite Corollary_mult_fun_d; auto. }
    apply x_fx_T in H18; auto. applyClassifier2 H18. destruct H18; auto.
    rewrite H19,Rmult_comm. apply Rmult_le_compat_neg_l; auto. }
  assert ((M * G) <= J).
  { eapply Corollary9_4_5; eauto. intros. destruct H12 as [H12[_[H17 _]]].
    rewrite Corollary_mult_fun_b; auto. assert (Function (g \\* M)).
    { red; intros. applyClassifier2 H18. applyClassifier2 H19.
      destruct H18 as [], H19 as []. rewrite H20,H21; auto. }
    assert (x ∈ dom[g \\* M]). { rewrite Corollary_mult_fun_d; auto. }
    apply x_fx_T in H19; auto. applyClassifier2 H19. destruct H19; auto.
    rewrite H20,(Rmult_comm f[x]). apply Rmult_le_compat_neg_l; auto. }
  assert (G <= 0) as []. { eapply Property9_4_5b; eauto. }
  assert (m <= J/G /\ J/G <= M) as [].
  { pose proof H17. apply Rinv_lt_0_compat in H18. split.
    apply (Rmult_le_compat_neg_l (/G)) in H15; [ |lra].
    rewrite Rmult_comm,Rmult_assoc,Rinv_r,Rmult_1_r,Rmult_comm in H15; auto. lra.
    apply (Rmult_le_compat_neg_l (/G)) in H16; [ |lra].
    rewrite Rmult_comm,(Rmult_comm (/G)),Rmult_assoc,Rinv_r,Rmult_1_r in H16;
    auto. lra. }
  destruct H18. destruct H19. apply Classifier1 in H5 as [], H9 as [].
  destruct (Rtotal_order x1 x2) as [H22|[H22|H22]].
  assert (ContinuousClose f x1 x2).
  { destruct H0 as [H0[]]. split. red; intros. apply H0. lra. split.
    destruct H5. apply Theorem4_1,H0. lra. rewrite H5; auto. destruct H21.
    apply Theorem4_1,H0. lra. rewrite H21; auto. }
  apply (Theorem4_7 _ _ _ (J/G)) in H23 as [ξ[]]; auto. exists ξ. split.
  apply Classifier1. lra. unfold Rdiv in H24. rewrite H24,Rmult_assoc,
  (Rmult_comm (/G)),Rinv_r. lra. lra. rewrite H6,H10; auto.
  rewrite <-H10 in H18. rewrite <-H6,H22 in H19. exfalso. lra.
  assert (ContinuousClose f x2 x1).
  { destruct H0 as [H0[]]. split. red; intros. apply H0. lra. split.
    destruct H9. apply Theorem4_1,H0. lra. rewrite H9; auto. destruct H20.
    apply Theorem4_1,H0. lra. rewrite H20; auto. }
  apply (Theorem4_7 _ _ _ (J/G)) in H23 as [ξ[]]; auto. exists ξ. split.
  apply Classifier1. lra. unfold Rdiv in H24. rewrite H24,Rmult_assoc,
  (Rmult_comm (/G)),Rinv_r. lra. lra. rewrite H6,H10; auto.
  exists x1. split; auto. unfold Rdiv in H19. rewrite H6,<-H19,Rmult_assoc,
  (Rmult_comm (/G)),Rinv_r. lra. lra. exists x2. split; auto. unfold Rdiv in H18.
  rewrite H10,H18,Rmult_assoc,(Rmult_comm (/G)),Rinv_r. lra. lra.
  rewrite H17 in H15,H16. assert (J = 0). lra. rewrite H17,H18. exists x1.
  split; auto. lra.
Qed.





