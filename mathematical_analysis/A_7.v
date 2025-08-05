(******************************************************************************)
(*   This is part of completeness of real numbers, it is distributed under    *)
(*       the terms of the GNU Lesser General Public License version 2.1       *)
(*                   (see file LICENSE for more details)                      *)
(*                                                                            *)
(*                           Copyright 2025-2028                              *)
(*                        Guowei Dou and Wensheng Yu                          *)
(******************************************************************************)

(** A_7 *)
(* completeness of real numbers *)

(* 读入文件 *)
Require Export A_2.


(* 区间列 *)
Definition Interval_Seq f := Function f /\ dom[f] = Full nat
  /\ ran[f] ⊂ \{ λ u, ∃ a b, a < b /\ u = \[a, b\] \}.

Corollary Interval_Seq_Value : ∀ f n, Interval_Seq f
  -> ∃ a b, a < b /\ f[n] = \[a, b\].
Proof.
  intros. destruct H as [H[]].
  assert (n ∈ dom[f]). { rewrite H0. apply Classifier1; auto. }
  apply fx_ran_T,H1,Classifier1 in H2 as [a[b[]]]; eauto.
Qed.

(* 区间列每个区间的左端(即最小值)构成的数列 *)
Definition LeftSeq f := \{\ λ (u : nat) v, v ∈ f[u]
  /\ (∀ r, r ∈ f[u] -> v <= r) \}\.

Corollary LeftSeq_is_Seq : ∀ f, Interval_Seq f -> IsSeq (LeftSeq f).
Proof.
  intros. split. red; intros. applyClassifier2 H0. applyClassifier2 H1.
  destruct H0,H1. apply H2 in H1. apply H3 in H0. lra.
  apply AxiomI; split; intros. apply Classifier1; auto.
  apply Classifier1. destruct H as [H[]]. rewrite <-H1 in H0.
  apply fx_ran_T,H2,Classifier1 in H0 as [a[b[]]]; auto.
  exists a. apply Classifier2. unfold set. rewrite H3. split.
  apply Classifier1. lra. intros. applyClassifier1 H4. lra.
Qed.

(* 左端数列的取值 *)
Corollary LeftSeq_Value : ∀ f a b n, Interval_Seq f -> a < b -> f[n] = \[a, b\]
  -> (LeftSeq f)[n] = a.
Proof.
  intros. pose proof (LeftSeq_is_Seq f H) as [].
  assert (n ∈ dom[LeftSeq f]). { rewrite H3. apply Classifier1; auto. }
  apply x_fx_T in H4; auto. applyClassifier2 H4. destruct H4. unfold set in *.
  rewrite H1 in H4,H5.
  assert ((LeftSeq f)[n] < a \/ (LeftSeq f)[n] = a \/ a < (LeftSeq f)[n]). lra.
  destruct H6 as [H6|[]]; auto. applyClassifier1 H4. exfalso. lra.
  assert (a ∈ \[a, b\]). { apply Classifier1; lra. } apply H5 in H7. exfalso. lra.
Qed.

(* 区间列每个区间的右端(即最大值)构成的数列 *)
Definition RightSeq f := \{\ λ (u : nat) v, v ∈ f[u]
  /\ (∀ r, r ∈ f[u] -> r <= v) \}\.

Corollary RightSeq_is_Seq : ∀ f, Interval_Seq f -> IsSeq (RightSeq f).
Proof.
  intros. split. red; intros. applyClassifier2 H0. applyClassifier2 H1.
  destruct H0,H1. apply H2 in H1. apply H3 in H0. lra.
  apply AxiomI; split; intros. apply Classifier1; auto.
  apply Classifier1. destruct H as [H[]]. rewrite <-H1 in H0.
  apply fx_ran_T,H2,Classifier1 in H0 as [a[b[]]]; auto.
  exists b. apply Classifier2. unfold set. rewrite H3. split.
  apply Classifier1. lra. intros. applyClassifier1 H4. lra.
Qed.

(*右端数列的取值 *)
Corollary RightSeq_Value : ∀ f a b n, Interval_Seq f -> a < b -> f[n] = \[a, b\]
  -> (RightSeq f)[n] = b.
Proof.
  intros. pose proof (RightSeq_is_Seq f H) as [].
  assert (n ∈ dom[RightSeq f]). { rewrite H3. apply Classifier1; auto. }
  apply x_fx_T in H4; auto. applyClassifier2 H4.
  destruct H4. unfold set in *. rewrite H1 in H4,H5.
  assert ((RightSeq f)[n] < b \/ (RightSeq f)[n] = b \/ b < (RightSeq f)[n]). lra.
  destruct H6 as [H6|[]]; auto. assert (b ∈ \[a, b\]). { apply Classifier1; lra. }
  apply H5 in H7. exfalso. lra. applyClassifier1 H4. exfalso. lra.
Qed.

(* 定义 区间套 *)
Definition Interval_Nest f := Interval_Seq f /\ (∀ n, f[S n] ⊂ f[n])
  /\ limit_seq (\{\ λ u v, v = (RightSeq f)[u] - (LeftSeq f)[u] \}\) 0.

(* 区间套每个区间左端构成的数列是单增的, 右端构成的数列是单减的 *)
Corollary Interval_Nest_Coro1 : ∀ f, Interval_Nest f
  -> IncreaseSeq (LeftSeq f) /\ DecreaseSeq (RightSeq f).
Proof.
  intros. destruct H as [H[]]. pose proof (LeftSeq_is_Seq f H).
  pose proof (RightSeq_is_Seq f H). pose proof H as [H4[]].
  split; split; auto; intros.
  - pose proof (Interval_Seq_Value f n H) as [a1[b1[]]].
    rewrite (LeftSeq_Value f a1 b1 n); auto.
    pose proof (Interval_Seq_Value f (S n) H) as [a2[b2[]]].
    rewrite (LeftSeq_Value f a2 b2 (S n)); auto.
    pose proof (H0 n). rewrite H8,H10 in H11.
    assert (a2 ∈ \[a2, b2\]). apply Classifier1; lra.
    apply H11 in H12. applyClassifier1 H12. lra.
  - pose proof (Interval_Seq_Value f n H) as [a1[b1[]]].
    rewrite (RightSeq_Value f a1 b1 n); auto.
    pose proof (Interval_Seq_Value f (S n) H) as [a2[b2[]]].
    rewrite (RightSeq_Value f a2 b2 (S n)); auto.
    pose proof (H0 n). rewrite H8,H10 in H11.
    assert (b2 ∈ \[a2, b2\]). apply Classifier1; lra.
    apply H11 in H12. applyClassifier1 H12. lra.
Qed.

(* 区间套左端数列总小于右端数列 *)
Corollary Interval_Nest_Coro2 : ∀ f m n, Interval_Nest f
  -> (LeftSeq f)[m] < (RightSeq f)[n].
Proof.
  intros. assert (∀ m1 n1, (m1 < n1)%nat -> f[n1] ⊂ f[m1]).
  { intros. induction n1. induction m1. red; auto. exfalso. lia.
    assert (m1 = n1 \/ m1 < n1)%nat as []. lia.
    rewrite H1. destruct H as [H[]]. auto. apply IHn1 in H1.
    assert (f[S n1] ⊂ f[n1]). { destruct H as [H[]]; auto. }
    red; intros; auto. }
  assert (m < n \/ n < m \/ m = n)%nat as [H1|[H1|H1]]. lia.
  - destruct H as [H[]]. pose proof H. pose proof H.
    apply (Interval_Seq_Value f m) in H4 as [a1[b1[]]].
    apply (Interval_Seq_Value f n) in H5 as [a2[b2[]]].
    pose proof H1. apply H0 in H8. rewrite H6,H7 in H8.
    rewrite (LeftSeq_Value f a1 b1),(RightSeq_Value f a2 b2); auto.
    assert (a2 ∈ \[a2, b2\]). { apply Classifier1. lra. }
    apply H8 in H9. applyClassifier1 H9. lra.
  - destruct H as [H[]]. pose proof H. pose proof H.
    apply (Interval_Seq_Value f m) in H4 as [a1[b1[]]].
    apply (Interval_Seq_Value f n) in H5 as [a2[b2[]]].
    pose proof H1. apply H0 in H8. rewrite H6,H7 in H8.
    rewrite (LeftSeq_Value f a1 b1),(RightSeq_Value f a2 b2); auto.
    assert (b1 ∈ \[a1, b1\]). { apply Classifier1. lra. }
    apply H8 in H9. applyClassifier1 H9. lra.
  - rewrite H1. destruct H as [H[]]. pose proof H.
    apply (Interval_Seq_Value f n) in H4 as [a[b[]]].
    rewrite (LeftSeq_Value f a b),(RightSeq_Value f a b); auto.
Qed.


(* 单增有界数列的极限为其值域的上确界 *)
Lemma Lemma7_1a : ∀ f, IncreaseSeq f -> (∃ M, ∀ n, f[n] <= M)
  -> ∃ x, limit_seq f x /\ sup ran[f] x.
Proof.
  intros. destruct H0 as [M]. assert (∀ n, f[0%nat] <= f[n]).
  { intros. induction n. lra. destruct H. pose proof (H1 n). lra. }
  assert (BoundedSeq f).
  { destruct H. split; auto. pose proof (Abs_neg_pos M).
    pose proof (Abs_neg_pos f[0%nat]). destruct (Rle_or_lt ∣M∣ ∣(f[0%nat])∣);
    [exists ∣(f[0%nat])∣|exists ∣M∣]; intros; apply Abs_le_R;
    pose proof (H0 n); pose proof (H1 n); lra. }
  pose proof H2. apply Theorem2_9 in H3 as []; [ |red; auto].
  exists x. split; auto.
  assert (∀ a, a < x -> ∃ x0, (x0 ∈ ran[f]) /\ x0 > a).
  { intros. destruct H3. assert (x - a > 0). lra. apply H5 in H6 as [N].
    assert (S N > N)%nat. lia. apply H6 in H7.
    replace ∣(f[S N] - x)∣ with ∣(x - f[S N])∣ in H7. apply Abs_R in H7 as [].
    assert (f[S N] > a). lra. exists f[S N]. split; auto. apply Classifier1.
    exists (S N). destruct H3. apply x_fx_T; auto. rewrite H10.
    apply Classifier1; auto. replace (f[S N] - x) with (-(x - f[S N])).
    apply Abs_eq_neg. lra. }
  split; auto. red; intros. destruct (Rle_or_lt x0 x); auto. destruct H3.
  assert (x0 - x > 0). lra. apply H7 in H8 as [N].
  assert (∀ n, (n > N)%nat -> f[n] < x0).
  { intros. apply H8 in H9. apply Abs_R in H9 as []. lra. }
  applyClassifier1 H5. destruct H5 as [m]. destruct H3. apply f_x_T in H5; auto.
  rewrite <-H5 in H9. assert (m <= N \/ N < m)%nat as []. lia.
  assert (f[S N] < f[m]). apply H9. lia.
  assert (f[m] <= f[S N]). { apply EqualIncrease in H as []. apply H13. lia. }
  exfalso. lra. assert (f[m] < f[m]). apply H9. lia. exfalso. lra.
Qed.

(* 单减有界数列的极限为其值域的下确界 *)
Lemma Lemma7_1b : ∀ f, DecreaseSeq f -> (∃ M, ∀ n, M <= f[n])
  -> ∃ x, limit_seq f x /\ inf ran[f] x.
Proof.
  intros. destruct H0 as [M]. assert (∀ n, f[n] <= f[0%nat]).
  { intros. induction n. lra. destruct H. pose proof (H1 n). lra. }
  assert (BoundedSeq f).
  { destruct H. split; auto. pose proof (Abs_neg_pos M).
    pose proof (Abs_neg_pos f[0%nat]). destruct (Rle_or_lt ∣M∣ ∣(f[0%nat])∣);
    [exists ∣(f[0%nat])∣|exists ∣M∣]; intros; apply Abs_le_R;
    pose proof (H0 n); pose proof (H1 n); lra. }
  pose proof H2. apply Theorem2_9 in H3 as []; [ |red; auto].
  exists x. split; auto.
  assert (∀ a, a > x -> ∃ x0, (x0 ∈ ran[f]) /\ x0 < a).
  { intros. destruct H3. assert (a - x > 0). lra. apply H5 in H6 as [N].
    assert (S N > N)%nat. lia. apply H6 in H7. apply Abs_R in H7 as [].
    assert (f[S N] < a). lra. exists f[S N]. split; auto. apply Classifier1.
    exists (S N). destruct H3. apply x_fx_T; auto. rewrite H10.
    apply Classifier1; auto. }
  split; auto. red; intros. destruct (Rle_or_lt x x0). lra. destruct H3.
  assert (x - x0 > 0). lra. apply H7 in H8 as [N].
  assert (∀ n, (n > N)%nat -> f[n] > x0).
  { intros. apply H8 in H9. replace ∣(f[n] - x)∣ with ∣(x - f[n])∣ in H9.
    apply Abs_R in H9 as []. lra. replace (f[n] - x) with (-(x - f[n])).
    apply Abs_eq_neg. lra. }
  applyClassifier1 H5. destruct H5 as [m]. destruct H3. apply f_x_T in H5; auto.
  rewrite <-H5 in H9. assert (m <= N \/ N < m)%nat as []. lia.
  assert (f[S N] > f[m]). apply H9. lia.
  assert (f[m] >= f[S N]). { apply EqualDecrease in H as []. apply H13. lia. }
  exfalso. lra. assert (f[m] > f[m]). apply H9. lia. exfalso. lra.
Qed.

(* 区间套定理 *)
(* 存在性 *)
Theorem Theorem7_1a : ∀ f, Interval_Nest f
  -> ∃ ξ, (∀ n, ξ ∈ f[n]) /\ (∀ n, (LeftSeq f)[n] <= ξ <= (RightSeq f)[n]).
Proof.
  intros. pose proof H. apply Interval_Nest_Coro1 in H0 as [].
  assert ((∃ M, ∀ n, (LeftSeq f)[n] <= M) /\ (∃ M, ∀ n, M <= (RightSeq f)[n])).
  { assert ((∃ M, ∀ n, (LeftSeq f)[n] < M) /\ (∃ M, ∀ n, M < (RightSeq f)[n])).
    { split; [exists (RightSeq f)[0%nat]|exists (LeftSeq f)[0%nat]]; intros;
      apply Interval_Nest_Coro2; auto. }
    destruct H2 as [[M1][M2]]. split; [exists M1|exists M2]; intros;
    [pose proof (H2 n)|pose proof (H3 n)]; lra. } destruct H2.
  apply Lemma7_1a in H2 as [x1[]]; auto. apply Lemma7_1b in H3 as [x2[]]; auto.
  assert (x1 = x2).
  { destruct H as [H[]]. assert (limit_seq \{\ λ u v,
      v = (RightSeq f)[u] - (LeftSeq f)[u] \}\ (x2 - x1)).
    apply Corollary2_7b; auto.
    assert (x2 - x1 = 0). { eapply Theorem2_2; eauto. } lra. }
  rewrite H6 in *. exists x2.
  assert (∀ n, (LeftSeq f)[n] <= x2 <= (RightSeq f)[n]).
  { intros. destruct H4 as [H4 _], H5 as [H5 _], H0 as [[]_], H1 as [[]_].
    split; [apply H4|apply Rge_le,H5]; apply Classifier1; exists n; apply x_fx_T;
    auto; [rewrite H7|rewrite H8]; apply Classifier1; auto. }
  split; auto. intros. destruct H. pose proof H.
  apply (Interval_Seq_Value f n) in H9 as [a[b[]]]. rewrite H10.
  pose proof (H7 n). rewrite (LeftSeq_Value f a b) in H11; auto.
  rewrite (RightSeq_Value f a b) in H11; auto. apply Classifier1. lra.
Qed.

(* 唯一性 *)
Theorem Theorem7_1b : ∀ f ξ1 ξ2, Interval_Nest f
  -> ((∀ n, ξ1 ∈ f[n]) /\ (∀ n, ξ2 ∈ f[n]))
    \/ ((∀ n, (LeftSeq f)[n] <= ξ1 <= (RightSeq f)[n])
      /\ (∀ n, (LeftSeq f)[n] <= ξ2 <= (RightSeq f)[n]))
  -> ξ1 = ξ2.
Proof.
  intros. assert ((∀ n, (LeftSeq f)[n] <= ξ1 <= (RightSeq f)[n]) /\
    (∀ n, (LeftSeq f)[n] <= ξ2 <= (RightSeq f)[n])) as [].
  { destruct H0; auto. destruct H0. destruct H. pose proof H.
    split; intros; apply (Interval_Seq_Value f n) in H3; destruct H3 as [a[b[]]];
    [pose proof (H0 n)|pose proof (H1 n)]; rewrite H4 in H5;
    rewrite (LeftSeq_Value f a b),(RightSeq_Value f a b); auto;
    applyClassifier1 H5; lra. }
  set (h := \{\ λ u v, v = (RightSeq f)[u] - (LeftSeq f)[u] \}\).
  assert (limit_seq h 0). { destruct H as [H[]]. auto. }
  assert ((∃ N, ∀ n, (N < n)%nat -> ∣(ξ1 - ξ2)∣ <= h[n])).
  { exists 0%nat. intros. unfold h. rewrite FunValue.
    pose proof (H1 n). pose proof (H2 n).
    assert (-(RightSeq f)[n] <= -ξ2 <= -(LeftSeq f)[n]). lra.
    assert (-(RightSeq f)[n] <= -ξ1 <= -(LeftSeq f)[n]). lra.
    apply Abs_le_R. lra. }
  apply (Corollary2_5a h 0) in H4; auto. apply Abs_le_R in H4. lra.
Qed.

Corollary Corollary7_1 : ∀ f ξ, Interval_Nest f -> (∀ n, ξ ∈ f[n])
  -> (∀ ε, ε > 0 -> (∃ N, (N > 0)%nat /\ (∀ n, (n > N)%nat -> f[n] ⊂ U(ξ; ε)))).
Proof.
  intros. pose proof H. apply Interval_Nest_Coro1 in H2 as [].
  assert ((∃ M, ∀ n, (LeftSeq f)[n] <= M) /\ (∃ M, ∀ n, M <= (RightSeq f)[n])).
  { pose proof H. apply Theorem7_1a in H4 as [M[]].
    split; exists M; intros; apply H5. } destruct H4.
  apply Lemma7_1a in H4 as [x1[]]; auto. apply Lemma7_1b in H5 as [x2[]]; auto.
  assert (x1 = x2).
  { destruct H as [H[]]. assert (limit_seq \{\ λ u v,
      v = (RightSeq f)[u] - (LeftSeq f)[u] \}\ (x2 - x1)).
    apply Corollary2_7b; auto.
    assert (x2 - x1 = 0). { eapply Theorem2_2; eauto. } lra. } subst x1.
  assert (∀ n, x2 ∈ f[n]).
  { intros. destruct H. pose proof H.
    apply (Interval_Seq_Value f n) in H9 as [a[b[]]]. rewrite H10.
    assert ((LeftSeq f)[n] <= x2 /\ (RightSeq f)[n] >= x2).
    { destruct H6,H7. destruct H2 as [[]_], H3 as [[]_].
      split; [apply H6|apply H7]; apply Classifier1; exists n; apply x_fx_T; auto;
      [rewrite H13|rewrite H14]; apply Classifier1; auto. }
    rewrite (LeftSeq_Value f a b),(RightSeq_Value f a b) in H11; auto.
    apply Classifier1; lra. }
  assert (x2 = ξ). { apply (Theorem7_1b f x2 ξ); auto. } subst x2.
  destruct H4,H5. destruct (H9 ε H1) as [N1], (H10 ε H1) as [N2].
  exists ((S N2) + N1)%nat. split. lia. intros. destruct H. pose proof H.
  apply (Interval_Seq_Value f n) in H15 as [a[b[]]]. rewrite H16.
  assert (n > N1 /\ n > N2)%nat as []. lia.
  apply H11 in H17. apply H12 in H18. rewrite (LeftSeq_Value f a b) in H17; auto.
  rewrite (RightSeq_Value f a b) in H18; auto. red; intros. applyClassifier1 H19.
  destruct H19. apply Classifier1,Abs_R. apply Abs_R in H17,H18. lra.
Qed.


(**********    有限集与无限集性质补充    **********)

(* 有限集与有限集等势 *)
Property Finite_equ_Finite : ∀ {X Y : Type} (A : @set X)(B : @set Y) f,
  Function1_1 f -> dom[f] = A -> ran[f] = B -> Finite A -> Finite B.
Proof.
  intros. destruct H2. destruct H2 as [m[g[[][]]]]. set (h := f ◦ g).
  assert (Function1_1 h).
  { split. red; intros. applyClassifier2 H6. applyClassifier2 H7.
    destruct H6 as [x1[]], H7 as [y1[]]. apply f_x_T in H6,H7; auto.
    rewrite <-H6 in H8. rewrite <-H7 in H9. destruct H. apply (H (g[x])); auto.
    red; intros. applyClassifier2 H6. applyClassifier2 H7. applyClassifier2 H6.
    applyClassifier2 H7. destruct H6 as [x1[]], H7 as [y1[]]. destruct H.
    assert ([x, x1] ∈ f﹣¹ /\ [x, y1] ∈ f﹣¹
      /\ [x1, y] ∈ g﹣¹ /\ [y1, z] ∈ g﹣¹) as [H11[H12[]]].
    { split; [ |split; [ |split]]; apply Classifier2; auto. }
    apply f_x_T in H11,H12; auto. rewrite <-H11 in H13. rewrite <-H12 in H14.
    eapply H3; eauto. }
  assert (dom[h] = \{ λ x, (x <= m)%nat \}).
  { apply AxiomI; split; intros. rewrite <-H4. applyClassifier1 H7. destruct H7.
    applyClassifier2 H7. destruct H7 as [x1[]]. apply Classifier1; eauto.
    apply Classifier1. exists f[g[z]]. apply Classifier2. exists g[z].
    rewrite <-H4 in H7. split; apply x_fx_T; auto. destruct H; auto.
    rewrite H0,<-H5. apply Classifier1. exists z. apply x_fx_T; auto. }
  assert (ran[h] = B).
  { apply AxiomI; split; intros. applyClassifier1 H8. destruct H8.
    applyClassifier2 H8. destruct H8 as [x1[]]. rewrite <-H1. apply Classifier1.
    eauto. rewrite <-H1 in H8. applyClassifier1 H8. destruct H8.
    assert (x ∈ dom[f]). { apply Classifier1; eauto. }
    rewrite H0,<-H5 in H9. applyClassifier1 H9. destruct H9. apply Classifier1.
    exists x0. apply Classifier2. eauto. }
  left. exists m,h; auto. apply NNPP; intro.
  assert (B <> Empty Y). { intro. elim H3. right; auto. }
  apply not_empty in H4 as [y0]. rewrite <-H1 in H4. applyClassifier1 H4.
  destruct H4. assert (x ∈ dom[f]). { apply Classifier1; eauto. }
  rewrite H0,H2 in H5. applyClassifier1 H5. auto.
Qed.

(* 无限集与无限集等势 *)
Property Infinite_equ_Infinite : ∀ {X Y : Type} (A : @set X)(B : @set Y) f,
  Function1_1 f -> dom[f] = A -> ran[f] = B -> ~ Finite A -> ~ Finite B.
Proof.
  intros. intro. assert (Function1_1 (f﹣¹)). { apply invFun1_1; auto. }
  assert (dom[f﹣¹] = ran[f]).
  { apply AxiomI; split; intros. applyClassifier1 H5. destruct H5.
    applyClassifier2 H5. apply Classifier1; eauto. applyClassifier1 H5.
    destruct H5. apply Classifier1. exists x. apply Classifier2; auto. }
  assert (ran[f﹣¹] = dom[f]).
  { apply AxiomI; split; intros. applyClassifier1 H6. destruct H6.
    applyClassifier2 H6. apply Classifier1; eauto. applyClassifier1 H6.
    destruct H6. apply Classifier1. exists x. apply Classifier2; auto. }
  apply H2,(Finite_equ_Finite B A (f﹣¹)); auto;
  [rewrite <-H1|rewrite <-H0]; auto.
Qed.

(* 有限集并单点集仍有限 *)
Property Finite_union_Singleton : ∀ {X : Type} (A : @set X)(x : X), Finite A
  -> Finite (A ∪ [x]).
Proof.
  intros. destruct (classic (x ∈ A)).
  - assert (A ∪ [x] = A).
    { apply AxiomI; split; intros. applyClassifier1 H1. destruct H1; auto.
      applyClassifier1 H1. rewrite H1; auto. apply Classifier1; auto. }
    rewrite H1; auto.
  - destruct H. destruct H as [m[f[[][]]]].
    set (g := \{\ λ u v, (u <= S m)%nat /\ ((u <= m)%nat -> v = f[u])
      /\ (u = S m -> v = x) \}\).
    assert (Function1_1 g).
    { split; red; intros. applyClassifier2 H4. applyClassifier2 H5.
      destruct H4 as [H4[]], H5 as [H5[]]. assert (x0 <= m \/ x0 = S m)%nat. lia.
      destruct H10. rewrite H6,H8; auto. rewrite H7,H9; auto.
      applyClassifier2 H4. applyClassifier2 H5. applyClassifier2 H4.
      applyClassifier2 H5. destruct H4 as [H4[]], H5 as [H5[]].
      assert (y <= m \/ y = S m)%nat. lia.
      assert (z <= m \/ z = S m)%nat. lia. destruct H10,H11.
      pose proof (H6 H10). pose proof (H8 H11).
      assert ([y, x0] ∈ f /\ [z, x0] ∈ f) as [].
      { split; [rewrite H12|rewrite H13]; apply x_fx_T; auto; rewrite H2;
        apply Classifier1; auto. }
      assert ([x0, y] ∈ f﹣¹ /\ [x0, z] ∈ f﹣¹) as [].
      { split; apply Classifier2; auto. } apply (H1 x0); auto.
      assert ([y, x0] ∈ f).
      { rewrite H6; auto. apply x_fx_T; auto. rewrite H2. apply Classifier1; auto. }
      rewrite H9 in H12; auto. elim H0. rewrite <-H3. apply Classifier1; eauto.
      assert ([z, x0] ∈ f).
      { rewrite H8; auto. apply x_fx_T; auto. rewrite H2. apply Classifier1; auto. }
      rewrite H7 in H12; auto. elim H0. rewrite <-H3. apply Classifier1; eauto.
      rewrite H10,H11; auto. }
    assert (dom[g] = \{ λ u, (u <= S m)%nat \}).
    { apply AxiomI; split; intros. applyClassifier1 H5. destruct H5.
      applyClassifier2 H5. destruct H5. apply Classifier1; auto.
      apply Classifier1. applyClassifier1 H5.
      assert (z <= m \/ z = S m)%nat as []. lia. exists f[z]. apply Classifier2.
      repeat split; auto. intros. exfalso. lia. exists x. apply Classifier2.
      repeat split; auto. intros. exfalso. lia. }
    assert (ran[g] = A ∪ [x]).
    { apply AxiomI; split; intros. applyClassifier1 H6. destruct H6.
      applyClassifier2 H6. destruct H6 as [H6[]].
      assert (x0 <= m \/ x0 = S m)%nat as []. lia.
      apply Classifier1. left. rewrite <-H3. apply Classifier1. exists x0.
      rewrite H7; auto. apply x_fx_T; auto. rewrite H2. apply Classifier1; auto.
      rewrite <-H8; auto. apply Classifier1; right. apply Classifier1; auto.
      applyClassifier1 H6. destruct H6. rewrite <-H3 in H6. applyClassifier1 H6.
      destruct H6. apply Classifier1. exists x0.
      assert (x0 ∈ dom[f]). { apply Classifier1; eauto. }
      rewrite H2 in H7. applyClassifier1 H7. apply Classifier2.
      repeat split; auto; intros. apply f_x_T in H6; auto. exfalso. lia.
      applyClassifier1 H6. apply Classifier1. exists (S m). apply Classifier2.
      repeat split; auto. intros. exfalso. lia. }
    left. exists (S m),g. auto.
    assert (A ∪ [x] = [x]).
    { apply AxiomI; split; intros. applyClassifier1 H1. destruct H1; auto.
      rewrite H in H1. applyClassifier1 H1. elim H1; auto.
      apply Classifier1; auto. }
    rewrite H1. left. apply SingletonFinite.
Qed.

(* 有限集并有限集仍有限 *)
Property Finite_union_Finite : ∀ {X : Type} (A B : @set X), Finite A
  -> Finite B -> Finite (A ∪ B).
Proof.
  intros. destruct H0.
  - destruct H0 as [m[f[[][]]]]. generalize dependent f. generalize dependent B.
    induction m; intros.
    assert (B = [f[0%nat]]).
    { apply AxiomI; split; intros. rewrite <-H3 in H4. applyClassifier1 H4.
      destruct H4. assert (x ∈ dom[f]). { apply Classifier1; eauto. }
      rewrite H2 in H5. applyClassifier1 H5. apply f_x_T in H4; auto.
      assert (x = 0%nat). lia. rewrite <-H4,H6. apply Classifier1; auto.
      applyClassifier1 H4. rewrite H4,<-H3. apply Classifier1. exists 0%nat.
      apply x_fx_T; auto. rewrite H2. apply Classifier1; auto. }
    rewrite H4. apply Finite_union_Singleton; auto.
    set (g := f — [[(S m), f[(S m)]]]).
    assert (Function g).
    { red; intros. applyClassifier1 H4. applyClassifier1 H5. destruct H4,H5.
      apply (H0 x); auto. }
    assert (Function g﹣¹).
    { red; intros. applyClassifier2 H5. applyClassifier2 H6. applyClassifier1 H5.
      applyClassifier1 H6. destruct H5,H6.
      assert ([x,y] ∈ f﹣¹ /\ [x,z] ∈ f﹣¹). { split; apply Classifier2; auto. }
      destruct H9. apply (H1 x); auto. }
    assert (dom[g] = \{ λ x, (x <= m)%nat \}).
    { apply AxiomI; split; intros. applyClassifier1 H6. destruct H6.
      applyClassifier1 H6. destruct H6. applyClassifier1 H7.
      assert (z ∈ dom[f]). { apply Classifier1; eauto. }
      rewrite H2 in H8. applyClassifier1 H8. apply Classifier1.
      assert (z <> S m).
      { intro. elim H7. apply Classifier1. apply f_x_T in H6; auto.
        rewrite <-H6,H9; auto. } lia.
      applyClassifier1 H6. apply Classifier1. exists f[z]. apply Classifier1.
      split. apply x_fx_T; auto. rewrite H2. apply Classifier1. lia.
      apply Classifier1. intro. applyClassifier1 H7. apply ProdEqual in H7.
      destruct H7. lia. }
    assert (ran[g] = B — [f[S m]]).
    { apply AxiomI; split; intros. applyClassifier1 H7. destruct H7.
      applyClassifier1 H7. destruct H7. apply Classifier1. split. rewrite <-H3.
      apply Classifier1; eauto. apply Classifier1. intro. applyClassifier1 H8.
      applyClassifier1 H9. elim H8.
      assert ([S m, z] ∈ f).
      { rewrite H9. apply x_fx_T; auto. rewrite H2. apply Classifier1; auto. }
      assert ([z, S m] ∈ f﹣¹ /\ [z, x] ∈ f﹣¹) as [].
      { split; apply Classifier2; auto. }
      assert (S m = x). { apply (H1 z); auto. }
      rewrite H9,<-H13. apply Classifier1; auto.
      applyClassifier1 H7. destruct H7. rewrite <-H3 in H7. apply Classifier1.
      applyClassifier1 H7. destruct H7. exists x. apply Classifier1; split; auto.
      apply Classifier1. intro. applyClassifier1 H9. apply ProdEqual in H9 as [].
      rewrite H10 in H8. applyClassifier1 H8. elim H8. apply Classifier1; auto. }
    pose proof H7. apply (IHm _ g) in H8; auto.
    assert ((A ∪ (B — [f[S m]])) ∪ [f[S m]] = A ∪ B).
    { apply AxiomI; split; intros. apply Classifier1. applyClassifier1 H9.
      destruct H9. applyClassifier1 H9. destruct H9; auto. applyClassifier1 H9.
      destruct H9; auto. applyClassifier1 H9. right. rewrite H9,<-H3.
      apply Classifier1. exists (S m). apply x_fx_T; auto. rewrite H2.
      apply Classifier1; auto. apply Classifier1. applyClassifier1 H9.
      destruct H9. left. apply Classifier1; auto.
      destruct (classic (z ∈ [f[S m]])); auto. left. apply Classifier1. right.
      apply Classifier1; split; auto. }
    rewrite <-H9. apply Finite_union_Singleton; auto.
  - assert (A ∪ B = A).
    { apply AxiomI; split; intros. applyClassifier1 H1. destruct H1; auto.
      rewrite H0 in H1. applyClassifier1 H1. elim H1; auto.
      apply Classifier1; auto. }
    rewrite H1; auto.
Qed.

(* 最小数原理 非空自然数集有最小值 *)
Property MinNat : ∀ A, NotEmpty A -> ∃ m, m ∈ A /\ (∀ n, n ∈ A -> (m <= n)%nat).
Proof.
  intros. destruct H as [n]. generalize dependent A. induction n as [ |n H].
  - intros. exists 0%nat. split; auto. intros. lia.
  - intros. destruct (classic (n ∈ A)). apply H in H1; auto.
    assert(n ∈ A ∪ [n]). apply Classifier1; right; apply Classifier1; auto.
    apply H in H2; auto. destruct H2 as [m[]]. destruct(classic (m = n)).
    exists (S n). split; auto. intros.
    assert(n0 ∈ A ∪ [n]). apply Classifier1; left; auto. apply H3 in H6.
    destruct (classic (n0 = n)). subst n0. contradiction. rewrite H4 in H6. lia.
    exists m. applyClassifier1 H2. destruct H2. split; auto. intros. apply H3.
    apply Classifier1; left; auto. applyClassifier1 H2. contradiction.
Qed.

(* 无限自然数集可按大小顺序排成数列 *)
Property inFinite_to_Seq : ∀ A, ~ Finite A -> ∃ f, Function f
  /\ dom[f] = Full nat /\ ran[f] = A /\ StrictlyIncreaseFun_nat f.
Proof.
  intros. assert (NotEmpty A). { apply not_empty. intro. elim H. right; auto. }
  apply MinNat in H0 as [a[]].
  set (fst D := c \{ λ u, u ∈ D /\ (∀ n, n ∈ D -> (u <= n)%nat) \}).
  set (fix B m := match m with |O => A |S k => (B k) — [fst (B k)] end) as B.
  set (h := \{\ λ u v, v = fst (B u) \}\).
  assert (Function h).
  { red; intros. applyClassifier2 H2. applyClassifier2 H3. rewrite H2,H3; auto. }
  assert (dom[h] = Full nat).
  { apply AxiomI; split; intros. apply Classifier1; auto. apply Classifier1.
    exists (fst (B z)). apply Classifier2; auto. }
  assert (∀ D, NotEmpty D -> (fst D) ∈ D /\ (∀ n, n ∈ D -> ((fst D) <= n)%nat)).
  { intros. apply MinNat in H4 as [x[]].
    assert (NotEmpty \{ λ u, u ∈ D /\ (∀ n, n ∈ D -> (u <= n)%nat) \}).
    { exists x. apply Classifier1; auto. }
    apply Axiomc in H6. applyClassifier1 H6. unfold fst; auto. }
  assert (∀ m, (B m) ⊂ A).
  { red; intros. induction m; auto. simpl in H5. applyClassifier1 H5. tauto. }
  assert (∀ m, ~ Finite (B m)).
  { intros. induction m. simpl; auto. simpl. intro.
    assert ((B m) ⊂ ((B m) — [fst (B m)]) ∪ [fst (B m)]).
    { red; intros. destruct (classic (z ∈ [fst (B m)])). apply Classifier1; auto.
      apply Classifier1. left. apply Classifier1; split; auto. }
    apply SubSetFinite in H7; auto. apply Finite_union_Finite; auto.
    left. apply SingletonFinite. }
  assert (∀ m, NotEmpty (B m)).
  { intros. pose proof (H6 m). apply not_empty. intro.
    elim H7. rewrite H8. right; auto. }
  assert (∀ m, B (S m) = A — \{ λ u, (u <= fst (B m))%nat \}).
  { intros. induction m. simpl. assert (NotEmpty A). red; eauto.
    apply H4 in H8 as []. apply AxiomI; split; intros. applyClassifier1 H10.
    destruct H10. apply Classifier1. split; auto. applyClassifier1 H11.
    apply Classifier1. intro. elim H11. applyClassifier1 H12. apply Classifier1.
    apply H9 in H10. lia. applyClassifier1 H10. destruct H10.
    apply Classifier1; split; auto. applyClassifier1 H11. apply Classifier1.
    intro. elim H11. applyClassifier1 H12. apply Classifier1. rewrite H12. lia.
    replace (B (S (S m))) with ((B (S m)) — [fst (B (S m))]); auto.
    pose proof (H7 (S m)). apply H4 in H8 as []. apply AxiomI; split; intros.
    apply ->Classifier1 in H10. destruct H10. pose proof H10. rewrite IHm in H12.
    applyClassifier1 H12. destruct H12. apply Classifier1; split; auto.
    apply Classifier1. intro. apply ->Classifier1 in H14. apply H9 in H10.
    apply ->Classifier1 in H11. elim H11. apply Classifier1. simpl in *. lia.
    apply Classifier1. split. rewrite IHm. apply ->Classifier1 in H10.
    destruct H10. apply Classifier1; split; auto. apply Classifier1. intro.
    applyClassifier1 H12. apply ->Classifier1 in H11. elim H11.
    apply Classifier1. simpl B at 2 in H8. apply ->Classifier1 in H8.
    destruct H8. pose proof (H7 m). apply H4 in H14 as []. apply H15 in H8. lia.
    apply Classifier1. intro. apply ->Classifier1 in H11.
    apply ->Classifier1 in H10. destruct H10. apply ->Classifier1 in H12.
    elim H12. apply Classifier1. rewrite H11. lia. }
  assert (∀ x, x ∈ A -> ∃ m, fst (B m) = x).
  { intros. apply NNPP; intro.
    set (X := \{ λ u, u ∈ A /\ ~ (∃ m, fst (B m) = u) \}).
    assert (NotEmpty X). { exists x. apply Classifier1; auto. }
    apply MinNat in H11 as [x0[]].
    assert (∀ y, (y < x0)%nat -> y ∈ A -> (∃ m, fst (B m) = y)).
    { intros. apply NNPP; intro. assert (y ∈ X). { apply Classifier1; auto. }
      apply H12 in H16. lia. }
    destruct x0. applyClassifier1 H11. destruct H11. elim H14. exists 0%nat.
    simpl. assert (NotEmpty A). red; eauto. apply H4 in H15 as [].
    apply H16 in H11. lia. set (X0 := \{ λ u, u ∈ A /\ (u <= x0)%nat \}).
    assert (Finite X0).
    { assert (X0 ⊂ \{ λ u, (u <= x0)%nat \}).
      { red; intros. applyClassifier1 H14. apply Classifier1. tauto. }
      apply SubSetFinite in H14; auto. left. apply NatFinite. }
    destruct H14. pose proof H14. apply finite_maxN in H15 as [M[]].
    assert (∃ m, fst (B m) = M) as [k].
    { apply NNPP; intro. applyClassifier1 H15. destruct H15.
      assert (M ∈ X). { apply Classifier1; split; auto. }
      apply H12 in H19. lia. }
    pose proof (H8 k). rewrite H17 in H18. pose proof (H7 (S k)).
    apply H4 in H19 as []. pattern (B (S k)) at 2 in H19. rewrite H18 in H19.
    pattern (B (S k)) at 1 in H20. rewrite H18 in H20.
    assert (S x0 ∈ (A — \{ λ u, (u <= M)%nat \})).
    { applyClassifier1 H11. destruct H11. apply Classifier1; split; auto.
      apply Classifier1. intro. applyClassifier1 H22. applyClassifier1 H15.
      destruct H15. lia. }
    assert (∀ n, n ∈ (A — \{ λ u, (u <= M)%nat \}) -> ((S x0) <= n)%nat).
    { intros. applyClassifier1 H22. destruct H22. applyClassifier1 H23.
      assert (n ∉ X0). { intro. elim H23. apply Classifier1. apply H16; auto. }
      apply NNPP; intro. elim H24. apply Classifier1. split; auto. lia. }
    apply H22 in H19. apply H20 in H21. applyClassifier1 H11. destruct H11.
    elim H23. exists (S k). lia.
    assert (∀ n, n ∈ A -> (S x0 <= n)%nat).
    { intros. apply NNPP; intro.
      assert (n ∈ X0). { apply Classifier1. split; auto. lia. }
      rewrite H14 in H17. applyClassifier1 H17; auto. }
    applyClassifier1 H11. destruct H11. elim H16. exists 0%nat. simpl.
    assert (NotEmpty A). { exists x. auto. } apply H4 in H17 as [].
    apply H15 in H17. apply H18 in H11. lia. }
  assert (ran[h] = A).
  { apply AxiomI; split; intros. applyClassifier1 H10. destruct H10.
    apply f_x_T in H10; auto. unfold h in H10. rewrite FunValue in H10.
    apply (H5 x). rewrite <-H10. apply H4; auto. apply H9 in H10 as [].
    rewrite <-H10. apply Classifier1. exists x. apply Classifier2; auto. }
  assert (∀ m, fst (B m) < fst (B (S m)))%nat.
  { intros. pose proof (H7 m). apply H4 in H11 as [].
    assert ((fst (B (S m))) ∈ (B m)).
    { clear H11 H12. assert (B (S m) ⊂ B m).
      { red; intros. simpl in H11. applyClassifier1 H11; tauto. }
      apply H11,H4; auto. } apply H12 in H13.
    assert (fst (B m) <> fst (B (S m))).
    { intro. pose proof (H7 (S m)). apply H4 in H15 as []. rewrite <-H14 in H15.
      rewrite H8 in H15. simpl in H15. applyClassifier1 H15. destruct H15.
      applyClassifier1 H17. elim H17. apply Classifier1; auto. } lia. }
  exists h. split; auto. split; auto. split; [ |split]; auto.
  intros. apply f_x_T in H12,H13; auto. rewrite <-H12,<-H13.
  clear dependent y1. clear dependent y2. induction x2. exfalso. lia.
  assert (x1 < x2 \/ x1 = x2)%nat as [] by lia.
  pose proof (IHx2 H12). unfold h in H13. rewrite FunValue,FunValue in H13.
  unfold h. rewrite FunValue,FunValue; auto. pose proof (H11 x2). lia.
  rewrite H12. unfold h. rewrite FunValue,FunValue; auto.
Qed.


(* 定义 点集S的聚点为ξ *)
Definition Cluster_Point S ξ := ∀ ε, 0 < ε -> ~ Finite (Uº(ξ; ε) ∩ S).

Definition Cluster_Point' S ξ := ∀ ε, 0 < ε -> (Uº(ξ; ε) ∩ S) <> Empty R.

Definition Cluster_Point'' S ξ := ∃ f, IsSeq f /\ ran[f] ⊂ S
  /\ (∀ m n, m <> n -> f[m] <> f[n]) /\ limit_seq f ξ.

Corollary Cluster_Point_Equ1 : ∀ S ξ, Cluster_Point S ξ -> Cluster_Point' S ξ.
Proof.
  red; intros. intro. apply H in H0. elim H0. rewrite H1. right. auto.
Qed.

Corollary Cluster_Point_Equ2 : ∀ S ξ, Cluster_Point' S ξ -> Cluster_Point'' S ξ.
Proof.
  intros. set (fix A n := match n with |O => c \{ λ u, u ∈ (Uº(ξ; 1) ∩ S) \}
    |S m => c \{ λ u, (1/(INR (m+2)%nat) <= ∣(ξ - (A m))∣
      -> u ∈ (Uº(ξ; 1/(INR (m+2)%nat)) ∩ S))
    /\ (∣(ξ - (A m))∣ <= 1/(INR (m+2)%nat)
      -> u ∈ ((Uº(ξ; ∣(ξ - (A m))∣)) ∩ S)) \} end) as A.
  set (h := \{\ λ u v, v = A u \}\).
  assert (IsSeq h).
  { split. red; intros. applyClassifier2 H0. applyClassifier2 H1.
    rewrite H0,H1; auto. apply AxiomI; split; intros. apply Classifier1; auto.
    apply Classifier1. exists (A z). apply Classifier2; auto. }
  assert (∀ n, A n <> ξ /\ A n ∈ S /\ ∣(ξ - (A n))∣ < 1/(INR (n+1)%nat)).
  { intros. induction n. simpl.
    assert ((c \{ λ u, u ∈ Uº(ξ; 1) ∩ S \}) ∈ \{ λ u, u ∈ Uº(ξ; 1) ∩ S \}).
    { apply Axiomc. assert (NotEmpty (Uº(ξ; 1) ∩ S)). { apply not_empty,H. lra. }
      destruct H1. exists x. apply Classifier1; auto. }
    applyClassifier1 H1. applyClassifier1 H1. destruct H1.
    applyClassifier1 H1. split. intro. rewrite H3,Abs_ge in H1; lra.
    split; auto. rewrite Abs_eq_neg in H1. rewrite Ropp_minus_distr in H1. lra.
    destruct IHn as [H1[]].
    assert (A (Datatypes.S n) ∈ \{ λ u, (1/(INR (n+2)%nat) <= ∣(ξ - A n)∣
        -> u ∈ Uº(ξ; (1/(INR (n+2)%nat))) ∩ S)
      /\ (∣(ξ - A n)∣ <= 1/(INR (n+2)%nat)
        -> u ∈ Uº(ξ; (∣(ξ - A n)∣)) ∩ S) \}).
    { apply Axiomc. assert (NotEmpty (Uº(ξ; (1/(INR (n+2)%nat))) ∩ S)
        /\ NotEmpty (Uº(ξ; (∣(ξ - A n)∣)) ∩ S)).
      { split; apply not_empty,H. apply Rdiv_lt_0_compat. lra. apply lt_0_INR.
        lia. apply Abs_not_eq_0. lra. } destruct H4 as [[x1][x2]].
      destruct (Rle_or_lt (1/(INR (n+2)%nat)) (∣(ξ - A n)∣));
      [exists x1|exists x2]; apply Classifier1; split; intros; auto.
      assert (∣(ξ - A n)∣ = 1/(INR (n+2)%nat)). lra. rewrite H8; auto.
      exfalso. lra. } applyClassifier1 H4. destruct H4.
    assert ((1/(INR (n+2)%nat)) <= (∣(ξ - A n)∣)
      \/ (∣(ξ - A n)∣) <= (1/(INR (n+2)%nat))) as []. lra.
    pose proof (H4 H6). applyClassifier1 H7. destruct H7. applyClassifier1 H7.
    destruct H7. split. intro. simpl in H10. rewrite H10 in H7.
    rewrite Abs_ge in H7; lra. split; auto. rewrite Abs_eq_neg,Ropp_minus_distr.
    replace (Datatypes.S n + 1)%nat with (n + 2)%nat. auto. lia.
    pose proof (H5 H6). applyClassifier1 H7. destruct H7. applyClassifier1 H7.
    destruct H7. split. intro. simpl in H10. rewrite H10 in H7.
    rewrite Abs_ge in H7; lra. split; auto. rewrite Abs_eq_neg,Ropp_minus_distr.
    replace (Datatypes.S n + 1)%nat with (n + 2)%nat. simpl. lra. lia. }
  assert (∀ n, ∣(ξ - (A (Datatypes.S n)))∣ < ∣(ξ - (A n))∣).
  { intros. assert (A (Datatypes.S n) ∈ \{ λ u, (1/(INR (n+2)%nat) <= ∣(ξ - A n)∣
        -> u ∈ Uº(ξ; (1/(INR (n+2)%nat))) ∩ S)
      /\ (∣(ξ - A n)∣ <= 1/(INR (n+2)%nat) -> u ∈ Uº(ξ; (∣(ξ - A n)∣)) ∩ S) \}).
    { apply Axiomc. assert (NotEmpty (Uº(ξ; (1/(INR (n+2)%nat))) ∩ S)
        /\ NotEmpty (Uº(ξ; (∣(ξ - A n)∣)) ∩ S)).
      { split; apply not_empty,H. apply Rdiv_lt_0_compat. lra. apply lt_0_INR.
        lia. apply Abs_not_eq_0. destruct (H1 n). lra. } destruct H2 as [[x1][x2]].
      destruct (Rle_or_lt (1/(INR (n+2)%nat)) (∣(ξ - A n)∣));
      [exists x1|exists x2]; apply Classifier1; split; intros; auto.
      assert (∣(ξ - A n)∣ = 1/(INR (n+2)%nat)). lra. rewrite H6; auto.
      exfalso. lra. } applyClassifier1 H2. destruct H2.
    assert ((1/(INR (n+2)%nat)) <= (∣(ξ - A n)∣)
      \/ (∣(ξ - A n)∣) <= (1/(INR (n+2)%nat))) as []. lra.
    pose proof (H2 H4). applyClassifier1 H5. destruct H5. applyClassifier1 H5.
    rewrite Abs_eq_neg,Ropp_minus_distr. simpl (A (Datatypes.S n)). lra.
    pose proof (H3 H4). applyClassifier1 H5. destruct H5. applyClassifier1 H5.
    rewrite Abs_eq_neg,Ropp_minus_distr. simpl (A (Datatypes.S n)). lra. }
  assert (∀ m n, (m < n)%nat -> ∣(ξ - (A n))∣ < ∣(ξ - (A m))∣).
  { intros. generalize dependent m. induction n. intros. exfalso. lia.
    intros. assert (m < n \/ m = n)%nat as []. lia. apply IHn in H4.
    pose proof (H2 n). lra. rewrite H4. apply H2. }
  set (h1 := \{\ λ (u : nat) v, v = ξ \}\).
  set (h2 := \{\ λ u v, v = 1/(INR (u + 1)%nat) \}\).
  set (h3 := \{\ λ u v, v = h1[u] - h2[u] \}\).
  set (h4 := \{\ λ u v, v = h1[u] + h2[u] \}\).
  assert (IsSeq h1 /\ IsSeq h2) as [].
  { split; split; unfold Function; intros;
    try (applyClassifier2 H4; applyClassifier2 H5; rewrite H4,H5; auto);
    apply AxiomI; split; intros; apply Classifier1; auto;
    [exists ξ|exists (1/(INR (z + 1)%nat))]; apply Classifier2; auto. }
  assert (limit_seq h1 ξ).
  { split; auto. intros. exists 0%nat. intros. unfold h1.
    rewrite FunValue,Abs_ge; lra. }
  assert (limit_seq h2 0).
  { split; auto. intros. assert (0 < 1/ε). apply Rdiv_lt_0_compat; lra.
    assert (∃ k, (INR k) * 1 > 1/ε) as [k]. { apply Archimedes; lra. }
    assert (0 < (INR (k + 1)%nat)). { apply lt_0_INR. lia. }
    assert (0 < 1/(INR (k + 1)%nat)). { apply Rdiv_lt_0_compat; lra. }
    exists k. intros. unfold h2. rewrite FunValue,Abs_ge; rewrite Rminus_0_r.
    rewrite Rmult_1_r in H9. assert (0 < (INR k)). lra.
    apply (Rmult_lt_compat_l ε) in H9; auto. unfold Rdiv in H9.
    rewrite <-Rmult_assoc,Rinv_r_simpl_m in H9; [ |lra].
    apply (Rmult_lt_compat_r (/(INR k))) in H9; auto.
    rewrite Rinv_r_simpl_l in H9. assert (1/(INR (n+1)%nat) < 1/(INR k)).
    { unfold Rdiv. rewrite Rmult_1_l,Rmult_1_l. apply Rinv_1_lt_contravar.
      replace 1 with (INR 1%nat); auto. apply le_INR.
      replace 0 with (INR 0%nat) in H13; auto. apply INR_lt in H13. lia.
      apply lt_INR. lia. } lra. lra. apply Rinv_0_lt_compat; auto.
    assert (0 < 1/(INR (n+1)%nat)).
    { apply Rdiv_lt_0_compat. lra. replace 0 with (INR 0%nat); auto.
      apply lt_INR. lia. } lra. }
  assert (limit_seq h3 (ξ - 0) /\ limit_seq h4 (ξ + 0)) as [].
  { split. apply Corollary2_7b; auto. apply Corollary2_7a; auto. }
  rewrite Rminus_0_r in H8. rewrite Rplus_0_r in H9.
  exists h. split; auto. split. red; intros. applyClassifier1 H10. destruct H10.
  applyClassifier2 H10. rewrite H10. apply H1. split. intros. intro.
  unfold h in H11. rewrite FunValue,FunValue in H11. assert (m < n \/ n < m)%nat.
  lia. destruct H12; apply H3 in H12; rewrite H11 in H12; lra.
  apply (Theorem2_6 h3 h4 h); auto. exists 0%nat. intros. unfold h3,h4,h.
  rewrite FunValue,FunValue,FunValue. unfold h1,h2. rewrite FunValue,FunValue.
  destruct (H1 n) as [H11[]]. pose proof H13. rewrite Abs_eq_neg in H14.
  rewrite Ropp_minus_distr in H14. apply Abs_R in H13,H14. lra.
Qed.

Corollary Cluster_Point_Equ3 : ∀ S ξ, Cluster_Point'' S ξ -> Cluster_Point S ξ.
Proof.
  red; intros. destruct H as [f[H[H1[]]]]. intro. destruct H3 as [_].
  pose proof H0. apply H3 in H5 as [N].
  assert (∀ n, (n > N)%nat -> f[n] ∈ (U(ξ; ε) ∩ S)).
  { intros. apply Classifier1. split. apply Classifier1; auto. apply H1. destruct H.
     apply fx_ran_T; auto. rewrite H7. apply Classifier1; auto. }
  assert (~ Finite \{ λ u, (u > N)%nat \}).
  { intros. intro. destruct H7. apply finite_maxN in H7 as [M[]].
    assert ((M + 1)%nat ∈ \{ λ u, (u > N)%nat \}).
    { applyClassifier1 H7. apply Classifier1. lia. } apply H8 in H9. lia.
    assert ((N + 1)%nat ∈ \{ λ u, (u > N)%nat \}). { apply Classifier1. lia. }
    rewrite H7 in H8. applyClassifier1 H8; auto. }
  assert (Function1_1 f).
  { destruct H. split; auto. red; intros. applyClassifier2 H9. applyClassifier2 H10.
    apply NNPP; intro. apply H2 in H11. apply f_x_T in H9,H10; auto. lra. }
  set (g := f|[\{ λ u, (u > N)%nat \}]).
  assert (Function1_1 g). { apply RestrictFun1_1; auto. }
  assert (dom[g] = \{ λ u, (u > N)%nat \}).
  { destruct H8. apply (@RestrictFun nat R f (\{ λ u, (u > N)%nat \})) in H8
    as [H8[]]. unfold g. rewrite H11. destruct H. rewrite H13. apply AxiomI;
    split; intros. applyClassifier1 H14. tauto. apply Classifier1; split; auto.
    apply Classifier1; auto. }
  assert (~ Finite ran[g]).
  { apply (Infinite_equ_Infinite dom[g] _ g); auto. rewrite H10; auto. }
  assert (ran[g] ⊂ (U(ξ; ε) ∩ S)).
  { red; intros. applyClassifier1 H12. destruct H12. applyClassifier1 H12.
    destruct H12. applyClassifier2 H13. destruct H13. applyClassifier1 H13.
    apply f_x_T in H12. rewrite <-H12. apply H6; auto. destruct H; auto. }
  assert (Finite (U(ξ; ε) ∩ S)).
  { destruct (classic (ξ ∈ S)).
    assert (U(ξ; ε) ∩ S = (Uº(ξ; ε) ∩ S) ∪ [ξ]).
    { apply AxiomI; split; intros. applyClassifier1 H14. destruct H14.
      destruct (classic (z = ξ)). apply Classifier1. right.
      apply Classifier1; auto. apply Classifier1; left. apply Classifier1.
      split; auto. apply Classifier1. split. apply Abs_not_eq_0. lra.
      applyClassifier1 H14; auto. applyClassifier1 H14.
      destruct H14. applyClassifier1 H14. destruct H14. apply Classifier1.
      split; auto. applyClassifier1 H14. destruct H14. apply Classifier1; auto.
      applyClassifier1 H14. rewrite H14. apply Classifier1; split; auto.
      apply Classifier1. rewrite Abs_ge; lra. }
    rewrite H14. apply Finite_union_Singleton; auto.
    assert (U(ξ; ε) ∩ S = Uº(ξ; ε) ∩ S).
    { apply AxiomI; split; intros. applyClassifier1 H14. destruct H14.
      apply Classifier1. split; auto. destruct (classic (z = ξ)). elim H13.
      rewrite <-H16; auto. applyClassifier1 H14. apply Classifier1; split; auto.
      apply Abs_not_eq_0. lra.
      applyClassifier1 H14. destruct H14. apply Classifier1; split; auto.
      applyClassifier1 H14. destruct H14. apply Classifier1; auto. }
    rewrite H14; auto. }
  elim H11. apply SubSetFinite in H12; auto.
Qed.

(* 聚点原理 *)
Theorem Theorem7_2 : ∀ S, (∃ M, Upper S M) -> (∃ L, Lower S L) -> ~ Finite S
  -> (∃ ξ, Cluster_Point S ξ).
Proof.
  intros. destruct H as [M], H0 as [L].
  assert (NotEmpty S) as [s]. { apply not_empty. intro. elim H1. right; auto. }
  assert (L < M).
  { pose proof H2. pose proof H2. apply H in H3. apply H0 in H4.
    assert (L <= M). lra. assert (L < M \/ L = M) as []. lra. auto.
    assert (S = [s]).
    { apply AxiomI; split; intros. pose proof H7. apply H in H7. apply H0 in H8.
      apply Classifier1. lra. applyClassifier1 H7. rewrite H7; auto. }
    rewrite H7 in H1. elim H1. left. apply SingletonFinite. }
  assert (S ⊂ \[L, M\]).
  { red; intros. apply Classifier1. pose proof H4.
    apply H in H4. apply H0 in H5; auto. }
  set (le D := c \{ λ u, inf D u \}). set (ri D := c \{ λ u, sup D u \}).
  set (fix A n := match n with |O => \[L, M\]
    |Datatypes.S m
    => c \{ λ u, (~ Finite (\[((le (A m)) + (ri (A m)))/2, (ri (A m))\] ∩ S)
        -> u = \[((le (A m)) + (ri (A m)))/2, (ri (A m))\])
      /\ (Finite (\[((le (A m)) + (ri (A m)))/2, (ri (A m))\] ∩ S)
        -> u = \[(le (A m)), ((le (A m)) + (ri (A m)))/2\]) \} end)
  as A. set (f := \{\ λ u v, v = A u \}\).
  assert (∀ a b, a <= b -> le (\[a, b\]) = a /\ ri (\[a, b\]) = b).
  { intros. assert (a ∈ \{ λ u, inf (\[a, b\]) u \}
      /\ b ∈ \{ λ u, sup (\[a, b\]) u \}) as [].
    { split; apply Classifier1; split; unfold Upper,Lower; intros.
      applyClassifier1 H6. lra. assert (b < b0 \/ b0 <= b) as []. lra.
      exists b. split; auto. apply Classifier1. lra. exists a. split.
      apply Classifier1; lra. lra. applyClassifier1 H6; lra.
      assert (a <= a0 \/ a0 < a) as []. lra. exists b. split; auto.
      apply Classifier1; lra. exists a. split. apply Classifier1. lra. lra. }
    assert ((le (\[a, b\])) ∈ \{ λ u, inf (\[a, b\]) u \}
      /\ (ri (\[a, b\])) ∈ \{ λ u, sup (\[a, b\]) u \}) as [].
    { split; apply Axiomc; unfold NotEmpty; eauto. }
    applyClassifier1 H6. applyClassifier1 H7. applyClassifier1 H8.
    applyClassifier1 H9. destruct H6,H7,H8,H9. split.
    destruct (Rtotal_order a (le (\[a, b\]))).
    assert (a >= le (\[a, b\])). { apply H8. apply Classifier1; lra. }
    exfalso. lra. destruct H14; auto. apply H12 in H14 as [x[]].
    applyClassifier1 H14. exfalso. lra.
    destruct (Rtotal_order b (ri (\[a, b\]))) as [H14|[]]; auto.
    apply H13 in H14 as [x[]]. applyClassifier1 H14. exfalso. lra.
    assert (b <= ri (\[a, b\])). { apply H9. apply Classifier1; lra. }
    exfalso. lra. }
  assert (∀ m, (le (A m)) < (ri (A m))).
  { intros. induction m. simpl. assert (L <= M). lra. apply H5 in H6 as [].
    rewrite H6,H7; auto.
    assert ((A (Datatypes.S m))
       ∈ \{ λ u, (~ Finite (\[(le (A m) + ri (A m))/2, (ri (A m))\] ∩ S)
        -> u = \[(le (A m) + ri (A m))/2, (ri (A m))\])
      /\ (Finite (\[(le (A m) + ri (A m))/2, (ri (A m))\] ∩ S)
        -> u = \[(le (A m)), (le (A m) + ri (A m))/2\]) \}).
    { apply Axiomc. destruct (classic
      (Finite (\[(le (A m) + ri (A m))/2, (ri (A m))\] ∩ S)));
      [exists (\[(le (A m)), (le (A m) + ri (A m))/2\])
      |exists (\[(le (A m) + ri (A m))/2, (ri (A m))\])]; apply Classifier1;
      split; intros; auto; contradiction. }
    apply ->Classifier1 in H6. destruct H6. destruct (classic
    (Finite (\[(le (A m) + ri (A m))/2, (ri (A m))\] ∩ S))).
    apply H7 in H8. rewrite H8.
    assert ((le (A m)) <= (((le (A m)) + (ri (A m)))/2)). lra.
    apply H5 in H9 as []. rewrite H9,H10. lra.
    apply H6 in H8. rewrite H8.
    assert ((((le (A m)) + (ri (A m)))/2) <= (ri (A m))). lra.
    apply H5 in H9 as []. rewrite H9,H10. lra. }
  assert (∀ m, ~ Finite (\[(le (A m) + ri (A m))/2, (ri (A m))\] ∩ S)
    -> (A (Datatypes.S m)) = \[(le (A m) + ri (A m))/2, (ri (A m))\]).
  { intros. assert ((A (Datatypes.S m))
       ∈ \{ λ u, (~ Finite (\[(le (A m) + ri (A m))/2, (ri (A m))\] ∩ S)
        -> u = \[(le (A m) + ri (A m))/2, (ri (A m))\])
      /\ (Finite (\[(le (A m) + ri (A m))/2, (ri (A m))\] ∩ S)
        -> u = \[(le (A m)), (le (A m) + ri (A m))/2\]) \}).
    { apply Axiomc. exists (\[(le (A m) + ri (A m))/2, (ri (A m))\]).
      apply Classifier1. split; intros; auto. contradiction. }
    apply ->Classifier1 in H8. destruct H8. apply H8 in H7. rewrite H7; auto. }
  assert (∀ m, Finite (\[(le (A m) + ri (A m))/2, (ri (A m))\] ∩ S)
    -> (A (Datatypes.S m)) = \[(le (A m)), (le (A m) + ri (A m))/2\]).
  { intros. assert ((A (Datatypes.S m))
       ∈ \{ λ u, (~ Finite (\[(le (A m) + ri (A m))/2, (ri (A m))\] ∩ S)
        -> u = \[(le (A m) + ri (A m))/2, (ri (A m))\])
      /\ (Finite (\[(le (A m) + ri (A m))/2, (ri (A m))\] ∩ S)
        -> u = \[(le (A m)), (le (A m) + ri (A m))/2\]) \}).
    { apply Axiomc. exists (\[(le (A m)), (le (A m) + ri (A m))/2\]).
      apply Classifier1. split; intros; auto. contradiction. }
    apply ->Classifier1 in H9. destruct H9. apply H10 in H8. rewrite H8; auto. }
  assert (Interval_Seq f).
  { split. red; intros. applyClassifier2 H9. applyClassifier2 H10.
    rewrite H9,H10; auto. split. apply AxiomI; split; intros.
    apply Classifier1; auto. apply Classifier1. exists (A z).
    apply Classifier2; auto. red; intros. apply Classifier1.
    applyClassifier1 H9. destruct H9. applyClassifier2 H9. destruct x.
    exists L,M. auto.
    destruct (classic (Finite (\[(le (A x) + ri (A x))/2, (ri (A x))\] ∩ S)));
    [apply H8 in H10|apply H7 in H10]; rewrite H9,H10;
    [exists (le (A x)),((le (A x) + ri (A x))/2)
    |exists ((le (A x) + ri (A x))/2),(ri (A x))]; split; auto;
    pose proof (H6 x); lra. }
  assert (∀ m, A m = \[(le (A m)), (ri (A m))\]).
  { intros. destruct m. simpl. pose proof H3. apply Rlt_le,H5 in H10 as [].
    rewrite H10,H11; auto.
    destruct (classic (Finite (\[(le (A m) + ri (A m))/2, (ri (A m))\] ∩ S))).
    apply H8 in H10. rewrite H10. pose proof (H6 m).
    assert ((le (A m) <= ((le (A m)) + (ri (A m)))/2)). lra.
    apply H5 in H12 as []. rewrite H12,H13; auto.
    apply H7 in H10. rewrite H10. pose proof (H6 m).
    assert ((((le (A m)) + (ri (A m)))/2) <= (ri (A m))). lra.
    apply H5 in H12 as []. rewrite H12,H13; auto. }
  assert (∀ m, f[Datatypes.S m] ⊂ f[m]).
  { red; intros. unfold f in H11. rewrite FunValue in H11. unfold f.
    rewrite FunValue.
    destruct (classic (Finite (\[(le (A m) + ri (A m))/2, (ri (A m))\] ∩ S)));
    [apply H8 in H12|apply H7 in H12]; rewrite H12 in H11; rewrite H10;
    pose proof (H6 m); applyClassifier1 H11; apply Classifier1; lra. }
  assert (∀ m, ~ Finite (f[m] ∩ S)).
  { intros. unfold f. rewrite FunValue. induction m. simpl.
    assert (\[L, M\] ∩ S = S).
    { apply AxiomI; split; intros. applyClassifier1 H12. tauto.
      apply Classifier1; split; auto. } rewrite H12; auto.
    destruct (classic (Finite (\[(le (A m) + ri (A m))/2, (ri (A m))\] ∩ S))).
    - pose proof (H8 m H12). intro.
      assert ((\[(le (A m) + ri (A m))/2, (ri (A m))\] ∩ S)
         ∪ ((A (Datatypes.S m)) ∩ S) = ((A m) ∩ S)).
      { apply AxiomI; split; intros. apply ->Classifier1 in H15. destruct H15.
        applyClassifier1 H15. destruct H15. apply Classifier1; split; auto.
        rewrite H10. pose proof (H6 m). applyClassifier1 H15.
        apply Classifier1. lra. apply ->Classifier1 in H15. destruct H15.
        apply Classifier1; split; auto. rewrite H10. rewrite H13 in H15.
        applyClassifier1 H15. apply Classifier1. pose proof (H6 m). lra.
        applyClassifier1 H15. destruct H15. apply Classifier1.
        rewrite H10 in H15. applyClassifier1 H15.
        assert (z <= (le (A m) + ri (A m))/2 \/ (le (A m) + ri (A m))/2 <= z). lra.
        destruct H17. right. rewrite H13. apply Classifier1; split; auto.
        apply Classifier1. lra. left. apply Classifier1; split; auto.
        apply Classifier1. lra. }
      elim IHm. rewrite <-H15. apply Finite_union_Finite; auto.
    - pose proof (H7 m H12). rewrite H13; auto. }
  assert (∀ m, (RightSeq f)[m] = ri (f[m])).
  { intros. pose proof (H6 m). apply (RightSeq_Value f _ _ m) in H13; auto;
    unfold f; rewrite FunValue; auto. }
  assert (∀ m, (LeftSeq f)[m] = le (f[m])).
  { intros. pose proof (H6 m). apply (LeftSeq_Value f _ _ m) in H14; auto;
    unfold f; rewrite FunValue; auto. }
  set (fix zs m := match m with |O => 1 |S k => 1/2 * (zs k) end) as zs.
  assert (∀ m, (RightSeq f)[m] - (LeftSeq f)[m] = (zs m) * (M - L)).
  { intros. induction m. rewrite H13,H14. unfold f. rewrite FunValue. simpl.
    pose proof H3. apply Rlt_le,H5 in H15 as []. rewrite H15,H16. lra.
    rewrite H13,H14. unfold f. rewrite FunValue. simpl zs.
    rewrite H13,H14 in IHm. unfold f in IHm. rewrite FunValue in IHm.
    pose proof (H6 m). assert (le (A m) < (le (A m) + ri (A m))/2 < ri (A m)).
    lra. destruct H16. apply Rlt_le,H5 in H16 as [], H17 as [].
    destruct (classic (Finite (\[(le (A m) + ri (A m))/2, (ri (A m))\] ∩ S)));
    [apply H8 in H20|apply H7 in H20]; rewrite H20.
    rewrite H16,H18,Rmult_assoc,<-IHm. lra.
    rewrite H17,H19,Rmult_assoc,<-IHm. lra. }
  assert (limit_seq \{\ λ u v, v = (RightSeq f)[u] - (LeftSeq f)[u] \}\ 0).
  { split. split. red; intros. applyClassifier2 H16. applyClassifier2 H17.
    rewrite H16,H17; auto. apply AxiomI; split; intros. apply Classifier1; auto.
    apply Classifier1. exists ((RightSeq f)[z] - (LeftSeq f)[z]).
    apply Classifier2; auto. intros.
    assert ((M - L)/ε > 0). { apply Rdiv_lt_0_compat; lra. }
    pose proof H17. apply (Archimedes 1) in H18 as [k]; [ |lra].
    assert (1/(INR k) < ε/(M - L)).
    { pose proof H18. apply (Rmult_lt_compat_l ε) in H19; auto.
      unfold Rdiv in H19. rewrite <-Rmult_assoc,Rinv_r_simpl_m in H19; [ |lra].
      rewrite Rmult_1_r in H19. apply (Rmult_lt_compat_l (/(INR k))) in H19;
      [ |apply Rinv_0_lt_compat; lra]. rewrite (Rmult_comm _ (ε * (INR k))),
      Rinv_r_simpl_l in H19. apply (Rmult_lt_compat_r (/(M - L))) in H19;
      [ |apply Rinv_0_lt_compat; lra]. rewrite Rinv_r_simpl_l in H19; [ |lra].
      lra. assert (0 < INR k). lra. lra. }
    assert (∀ m, (0 < m)%nat -> zs m < 1/(INR m)).
    { intros. induction m. exfalso. lia. simpl zs. assert (m = 0 \/ 0 < m)%nat.
      lia. destruct H21. rewrite H21. simpl. lra. pose proof H21.
      apply IHm in H22. apply (Rmult_lt_compat_l (1/2)) in H22; [ |lra].
      assert (1/2 * (1/(INR m)) <= 1/(INR (Datatypes.S m))).
      { replace (INR (Datatypes.S m)) with ((INR m) + 1). unfold Rdiv.
        pose proof H21. apply lt_INR in H23. simpl in H23.
        assert (INR 1 <= INR m). { apply le_INR. lia. } simpl in H24.
        rewrite Rmult_1_l,Rmult_1_l,Rmult_1_l,<-Rinv_mult; try lra.
        apply Rinv_le_contravar. lra. lra. destruct m; auto. simpl; lra. } lra. }
    assert (∀ m, zs m > 0). { intros. induction m; simpl; lra. }
    exists k. intros. rewrite FunValue,H15,Rminus_0_r. rewrite Abs_ge.
    assert (0 < n)%nat. lia. pose proof (H20 n H23).
    assert (1/(INR n) < 1/(INR k)).
    { unfold Rdiv. rewrite Rmult_1_l,Rmult_1_l. apply Rinv_lt_contravar.
      apply lt_INR in H23. simpl in H23. apply Rmult_lt_0_compat; lra.
      apply lt_INR; auto. } assert (zs n < ε/(M - L)). lra.
    apply (Rmult_lt_compat_l (M - L)) in H26; [ |lra]. unfold Rdiv in H26.
    rewrite <-Rmult_assoc,Rinv_r_simpl_m in H26; lra. pose proof (H21 n).
    apply Rle_ge,Rmult_le_pos; lra. }
  assert (Interval_Nest f). { split; auto. }
  pose proof H17. apply Theorem7_1a in H18 as [ξ[]]. exists ξ.
  pose proof (Corollary7_1 f ξ H17 H18). red. intros.
  destruct (H20 ε H21) as [N[]]. intro.
  assert (Finite (U(ξ; ε) ∩ S)).
  { destruct (classic (ξ ∈ S)).
    - assert ((Uº(ξ; ε) ∩ S) ∪ [ξ] = (U(ξ; ε) ∩ S)).
      { apply AxiomI; split; intros. applyClassifier1 H26. destruct H26.
        applyClassifier1 H26. destruct H26. apply Classifier1; split; auto.
        applyClassifier1 H26. apply Classifier1. lra. applyClassifier1 H26.
        rewrite H26. apply Classifier1; split; auto. apply Classifier1.
        rewrite Abs_ge; lra. applyClassifier1 H26. destruct H26.
        apply Classifier1. destruct (classic (z = ξ)).
        right. apply Classifier1; auto. left. apply Classifier1; split; auto.
        applyClassifier1 H26. apply Classifier1; split; auto.
        apply Abs_not_eq_0; lra. }
      rewrite <-H26. apply Finite_union_Singleton; auto.
    - assert ((Uº(ξ; ε) ∩ S) = (U(ξ; ε) ∩ S)).
      { apply AxiomI; split; intros. applyClassifier1 H26. destruct H26.
        apply Classifier1. split; auto. applyClassifier1 H26.
        apply Classifier1; lra. applyClassifier1 H26. destruct H26.
        apply Classifier1; split; auto. applyClassifier1 H26.
        apply Classifier1; split; auto. apply Abs_not_eq_0.
        intro. assert (z = ξ). lra. elim H25. rewrite <-H29; auto. }
      rewrite <-H26; auto. }
  elim (H12 (N + 1)%nat). apply (SubSetFinite (U(ξ; ε) ∩ S)); auto.
  assert ((N + 1) > N)%nat. lia. apply H23 in H26. red; intros.
  applyClassifier1 H27. destruct H27. apply Classifier1; split; auto.
Qed.


(* 定义 H为S的一个开覆盖 *)
Definition Open_Cover H S := H ⊂ \{ λ u, ∃ α β, α < β /\ u = \(α, β\) \}
  /\ (∀ s, s ∈ S -> ∃ A, A ∈ H /\ s ∈ A).

(* 定义 H为S的一个无限开覆盖 *)
Definition Infinite_Open_Cover H S := Open_Cover H S /\ ~ Finite H.

(* 有限覆盖定理 *)
Theorem Theorem7_3 : ∀ H a b, a < b -> Open_Cover H (\[a, b\])
  -> ∃ Hf, Hf ⊂ H /\ Finite Hf /\ Open_Cover Hf (\[a, b\]).
Proof.
  intros. apply NNPP; intro.
  set (le D := c \{ λ u, inf D u \}). set (ri D := c \{ λ u, sup D u \}).
  set (fix A n := match n with |O => \[a, b\]
    |S m
    => c \{ λ u, (~ (∃ Hf, Hf ⊂ H /\ Finite Hf
          /\ Open_Cover Hf (\[((le (A m)) + (ri (A m)))/2, (ri (A m))\]))
        -> u = \[((le (A m)) + (ri (A m)))/2, (ri (A m))\])
      /\ ((∃ Hf, Hf ⊂ H /\ Finite Hf
          /\ Open_Cover Hf (\[((le (A m)) + (ri (A m)))/2, (ri (A m))\]))
        -> u = \[(le (A m)), ((le (A m)) + (ri (A m)))/2\]) \} end)
  as A. set (f := \{\ λ u v, v = A u \}\).
  assert (∀ u v, u <= v -> le (\[u, v\]) = u /\ ri (\[u, v\]) = v).
  { intros. assert (u ∈ \{ λ w, inf (\[u, v\]) w \}
      /\ v ∈ \{ λ w, sup (\[u, v\]) w \}) as [].
    { split; apply Classifier1; split; unfold Upper,Lower; intros.
      applyClassifier1 H4. lra. assert (v < b0 \/ b0 <= v) as []. lra.
      exists v. split; auto. apply Classifier1. lra. exists u. split.
      apply Classifier1; lra. lra. applyClassifier1 H4; lra.
      assert (u <= a0 \/ a0 < u) as []. lra. exists v. split; auto.
      apply Classifier1; lra. exists u. split. apply Classifier1. lra. lra. }
    assert ((le (\[u, v\])) ∈ \{ λ w, inf (\[u, v\]) w \}
      /\ (ri (\[u, v\])) ∈ \{ λ w, sup (\[u, v\]) w \}) as [].
    { split; apply Axiomc; unfold NotEmpty; eauto. }
    applyClassifier1 H4. applyClassifier1 H5. applyClassifier1 H6.
    applyClassifier1 H7. destruct H4,H5,H6,H7. split.
    destruct (Rtotal_order u (le (\[u, v\]))).
    assert (u >= le (\[u, v\])). { apply H6. apply Classifier1; lra. }
    exfalso. lra. destruct H12; auto. apply H10 in H12 as [x[]].
    applyClassifier1 H12. exfalso. lra.
    destruct (Rtotal_order v (ri (\[u, v\]))) as [H12|[]]; auto.
    apply H11 in H12 as [x[]]. applyClassifier1 H12. exfalso. lra.
    assert (v <= ri (\[u, v\])). { apply H7. apply Classifier1; lra. }
    exfalso. lra. }
  assert (∀ m, (le (A m)) < (ri (A m))).
  { intros. induction m. simpl. assert (a <= b). lra. apply H3 in H4 as [].
    rewrite H4,H5; auto.
    assert ((A (S m))
       ∈ \{ λ u, (~ (∃ Hf, Hf ⊂ H /\ Finite Hf
          /\ Open_Cover Hf (\[((le (A m)) + (ri (A m)))/2, (ri (A m))\]))
        -> u = \[((le (A m)) + (ri (A m)))/2, (ri (A m))\])
      /\ ((∃ Hf, Hf ⊂ H /\ Finite Hf
          /\ Open_Cover Hf (\[((le (A m)) + (ri (A m)))/2, (ri (A m))\]))
        -> u = \[(le (A m)), ((le (A m)) + (ri (A m)))/2\]) \}).
    { apply Axiomc. destruct (classic (∃ Hf, Hf ⊂ H /\ Finite Hf
        /\ Open_Cover Hf (\[((le (A m)) + (ri (A m)))/2, (ri (A m))\])));
      [exists (\[(le (A m)), (le (A m) + ri (A m))/2\])
      |exists (\[(le (A m) + ri (A m))/2, (ri (A m))\])]; apply Classifier1;
      split; intros; auto; contradiction. }
    apply ->Classifier1 in H4. destruct H4.
    destruct (classic (∃ Hf, Hf ⊂ H /\ Finite Hf
      /\ Open_Cover Hf (\[((le (A m)) + (ri (A m)))/2, (ri (A m))\]))).
    apply H5 in H6. rewrite H6.
    assert ((le (A m)) <= (((le (A m)) + (ri (A m)))/2)). lra.
    apply H3 in H7 as []. rewrite H7,H8. lra.
    apply H4 in H6. rewrite H6.
    assert ((((le (A m)) + (ri (A m)))/2) <= (ri (A m))). lra.
    apply H3 in H7 as []. rewrite H7,H8. lra. }
  assert (∀ m, ~ (∃ Hf, Hf ⊂ H /\ Finite Hf
      /\ Open_Cover Hf (\[((le (A m)) + (ri (A m)))/2, (ri (A m))\]))
    -> (A (S m)) = \[(le (A m) + ri (A m))/2, (ri (A m))\]).
  { intros. assert ((A (S m))
       ∈ \{ λ u, (~ (∃ Hf, Hf ⊂ H /\ Finite Hf
          /\ Open_Cover Hf (\[((le (A m)) + (ri (A m)))/2, (ri (A m))\]))
        -> u = \[((le (A m)) + (ri (A m)))/2, (ri (A m))\])
      /\ ((∃ Hf, Hf ⊂ H /\ Finite Hf
          /\ Open_Cover Hf (\[((le (A m)) + (ri (A m)))/2, (ri (A m))\]))
        -> u = \[(le (A m)), ((le (A m)) + (ri (A m)))/2\]) \}).
    { apply Axiomc. exists (\[(le (A m) + ri (A m))/2, (ri (A m))\]).
      apply Classifier1. split; intros; auto. contradiction. }
    apply ->Classifier1 in H6. destruct H6. apply H6 in H5. rewrite H5; auto. }
  assert (∀ m, (∃ Hf, Hf ⊂ H /\ Finite Hf
      /\ Open_Cover Hf (\[((le (A m)) + (ri (A m)))/2, (ri (A m))\]))
    -> (A (S m)) = \[(le (A m)), (le (A m) + ri (A m))/2\]).
  { intros. assert ((A (S m))
       ∈ \{ λ u, (~ (∃ Hf, Hf ⊂ H /\ Finite Hf
          /\ Open_Cover Hf (\[((le (A m)) + (ri (A m)))/2, (ri (A m))\]))
        -> u = \[((le (A m)) + (ri (A m)))/2, (ri (A m))\])
      /\ ((∃ Hf, Hf ⊂ H /\ Finite Hf
          /\ Open_Cover Hf (\[((le (A m)) + (ri (A m)))/2, (ri (A m))\]))
        -> u = \[(le (A m)), ((le (A m)) + (ri (A m)))/2\]) \}).
    { apply Axiomc. exists (\[(le (A m)), (le (A m) + ri (A m))/2\]).
      apply Classifier1. split; intros; auto. contradiction. }
    apply ->Classifier1 in H7. destruct H7. apply H8 in H6. rewrite H6; auto. }
  assert (Interval_Seq f).
  { split. red; intros. applyClassifier2 H7. applyClassifier2 H8.
    rewrite H7,H8; auto. split. apply AxiomI; split; intros.
    apply Classifier1; auto. apply Classifier1.
    exists (A z). apply Classifier2; auto. red; intros. apply Classifier1.
    applyClassifier1 H7. destruct H7. applyClassifier2 H7. destruct x.
    exists a,b. auto.
    destruct (classic (∃ Hf, Hf ⊂ H /\ Finite Hf
      /\ Open_Cover Hf (\[((le (A x)) + (ri (A x)))/2, (ri (A x))\])));
    [apply H6 in H8|apply H5 in H8]; rewrite H7,H8;
    [exists (le (A x)),((le (A x) + ri (A x))/2)
    |exists ((le (A x) + ri (A x))/2),(ri (A x))]; split; auto;
    pose proof (H4 x); lra. }
  assert (∀ m, A m = \[(le (A m)), (ri (A m))\]).
  { intros. destruct m. simpl. pose proof H0. apply Rlt_le,H3 in H8 as [].
    rewrite H8,H9; auto.
    destruct (classic (∃ Hf, Hf ⊂ H /\ Finite Hf
      /\ Open_Cover Hf (\[((le (A m)) + (ri (A m)))/2, (ri (A m))\]))).
    apply H6 in H8. rewrite H8. pose proof (H4 m).
    assert ((le (A m) <= ((le (A m)) + (ri (A m)))/2)). lra.
    apply H3 in H10 as []. rewrite H10,H11; auto.
    apply H5 in H8. rewrite H8. pose proof (H4 m).
    assert ((((le (A m)) + (ri (A m)))/2) <= (ri (A m))). lra.
    apply H3 in H10 as []. rewrite H10,H11; auto. }
  assert (∀ m, f[S m] ⊂ f[m]).
  { red; intros. unfold f in H9. rewrite FunValue in H9. unfold f.
    rewrite FunValue. destruct (classic (∃ Hf, Hf ⊂ H /\ Finite Hf
      /\ Open_Cover Hf (\[((le (A m)) + (ri (A m)))/2, (ri (A m))\])));
    [apply H6 in H10|apply H5 in H10]; rewrite H10 in H9; rewrite H8;
    pose proof (H4 m); applyClassifier1 H9; apply Classifier1; lra. }
  assert (∀ m, ~ (∃ Hf, Hf ⊂ H /\ Finite Hf /\ Open_Cover Hf f[m])).
  { intros. unfold f. rewrite FunValue. induction m. simpl. auto.
    destruct (classic (∃ Hf, Hf ⊂ H /\ Finite Hf
      /\ Open_Cover Hf (\[((le (A m)) + (ri (A m)))/2, (ri (A m))\]))).
    - pose proof (H6 m H10). intro. rewrite H11 in H12.
      destruct H10 as [Hf1[H10[]]], H12 as [Hf2[H12[]]]. elim IHm.
      pose proof H1 as [H17 _]. exists (Hf1 ∪ Hf2). split. red; intros.
      applyClassifier1 H18. destruct H18; auto. split.
      apply Finite_union_Finite; auto.
      split. red; intros. applyClassifier1 H18. destruct H18; auto. intros.
      destruct H14,H16. rewrite H8 in H18. applyClassifier1 H18.
      assert ((s <= (le (A m) + ri (A m))/2) \/ ((le (A m) + ri (A m))/2 <= s))
      as []. lra.
      assert (s ∈ \[le (A m), (le (A m) + ri (A m))/2\]).
      { apply Classifier1; lra. }
      apply H20 in H22 as [x[]]. exists x. split; auto. apply Classifier1; auto.
      assert (s ∈ \[(le (A m) + ri (A m))/2, ri (A m)\]).
      { apply Classifier1; lra. }
      apply H19 in H22 as [x[]]. exists x. split; auto. apply Classifier1; auto.
    - pose proof (H5 m H10). rewrite H11. auto. }
  assert (∀ m, (RightSeq f)[m] = ri (f[m])).
  { intros. pose proof (H4 m). apply (RightSeq_Value f _ _ m) in H11; auto;
    unfold f; rewrite FunValue; auto. }
  assert (∀ m, (LeftSeq f)[m] = le (f[m])).
  { intros. pose proof (H4 m). apply (LeftSeq_Value f _ _ m) in H12; auto;
    unfold f; rewrite FunValue; auto. }
  set (fix zs m := match m with |O => 1 |S k => 1/2 * (zs k) end) as zs.
  assert (∀ m, (RightSeq f)[m] - (LeftSeq f)[m] = (zs m) * (b - a)).
  { intros. induction m. rewrite H11,H12. unfold f. rewrite FunValue. simpl.
    pose proof H0. apply Rlt_le,H3 in H13 as []. rewrite H13,H14. lra.
    rewrite H11,H12. unfold f. rewrite FunValue. simpl zs.
    rewrite H11,H12 in IHm. unfold f in IHm. rewrite FunValue in IHm.
    pose proof (H4 m). assert (le (A m) < (le (A m) + ri (A m))/2 < ri (A m)). lra.
    destruct H14. apply Rlt_le,H3 in H14 as [], H15 as [].
    destruct (classic (∃ Hf, Hf ⊂ H /\ Finite Hf
      /\ Open_Cover Hf (\[((le (A m)) + (ri (A m)))/2, (ri (A m))\])));
    [apply H6 in H18|apply H5 in H18]; rewrite H18.
    rewrite H14,H16,Rmult_assoc,<-IHm. lra.
    rewrite H15,H17,Rmult_assoc,<-IHm. lra. }
  assert (limit_seq \{\ λ u v, v = (RightSeq f)[u] - (LeftSeq f)[u] \}\ 0).
  { split. split. red; intros. applyClassifier2 H14. applyClassifier2 H15.
    rewrite H14,H15; auto. apply AxiomI; split; intros. apply Classifier1; auto.
    apply Classifier1. exists ((RightSeq f)[z] - (LeftSeq f)[z]).
    apply Classifier2; auto. intros.
    assert ((b - a)/ε > 0). { apply Rdiv_lt_0_compat; lra. }
    pose proof H15. apply (Archimedes 1) in H16 as [k]; [ |lra].
    assert (1/(INR k) < ε/(b - a)).
    { pose proof H16. apply (Rmult_lt_compat_l ε) in H17; auto.
      unfold Rdiv in H17. rewrite <-Rmult_assoc,Rinv_r_simpl_m in H17; [ |lra].
      rewrite Rmult_1_r in H17.
      apply (Rmult_lt_compat_l (/(INR k))) in H17; [ |apply Rinv_0_lt_compat; lra].
      rewrite (Rmult_comm _ (ε * (INR k))),Rinv_r_simpl_l in H17.
      apply (Rmult_lt_compat_r (/(b - a))) in H17; [ |apply Rinv_0_lt_compat; lra].
      rewrite Rinv_r_simpl_l in H17; [ |lra]. lra. assert (0 < INR k). lra. lra. }
    assert (∀ m, (0 < m)%nat -> zs m < 1/(INR m)).
    { intros. induction m. exfalso. lia. simpl zs. assert (m = 0 \/ 0 < m)%nat.
      lia. destruct H19. rewrite H19. simpl. lra. pose proof H19.
      apply IHm in H20. apply (Rmult_lt_compat_l (1/2)) in H20; [ |lra].
      assert (1/2 * (1/(INR m)) <= 1/(INR (S m))).
      { replace (INR (S m)) with ((INR m) + 1). unfold Rdiv.
        pose proof H19. apply lt_INR in H21. simpl in H21.
        assert (INR 1 <= INR m). { apply le_INR. lia. } simpl in H22.
        rewrite Rmult_1_l,Rmult_1_l,Rmult_1_l,<-Rinv_mult; try lra.
        apply Rinv_le_contravar. lra. lra. destruct m; auto. simpl; lra. } lra. }
    assert (∀ m, zs m > 0). { intros. induction m; simpl; lra. }
    exists k. intros. rewrite FunValue,H13,Rminus_0_r. rewrite Abs_ge.
    assert (0 < n)%nat. lia. pose proof (H18 n H21).
    assert (1/(INR n) < 1/(INR k)).
    { unfold Rdiv. rewrite Rmult_1_l,Rmult_1_l. apply Rinv_lt_contravar.
      apply lt_INR in H21. simpl in H21. apply Rmult_lt_0_compat; lra.
      apply lt_INR; auto. } assert (zs n < ε/(b - a)). lra.
    apply (Rmult_lt_compat_l (b - a)) in H24; [ |lra]. unfold Rdiv in H24.
    rewrite <-Rmult_assoc,Rinv_r_simpl_m in H24; lra. pose proof (H19 n).
    apply Rle_ge,Rmult_le_pos; lra. }
  assert (Interval_Nest f). { split; auto. }
  pose proof H15. apply Theorem7_1a in H16 as [ξ[]]. pose proof H1 as [].
  assert (ξ ∈ f[0%nat]); auto. unfold f in H20. rewrite FunValue in H20.
  simpl in H20. pose proof (H19 ξ H20) as [Hf[]]. pose proof H21.
  apply H18 in H23. applyClassifier1 H23. destruct H23 as [α[β[]]].
  rewrite H24 in H22. pose proof H22. applyClassifier1 H25. destruct H25.
  destruct (Examp1 (ξ-α) (β-ξ)) as [ε[H27[]]]; try lra.
  pose proof (Corollary7_1 f ξ H15 H16). pose proof (H30 ε H27) as [N[]].
  assert (N + 1 > N)%nat. lia. pose proof H33. apply H32 in H34.
  assert (f[(N + 1)%nat] ⊂ \(α, β\)).
  { red; intros. apply H34 in H35. applyClassifier1 H35. apply Classifier1.
    apply Abs_R in H35. lra. }
  pose proof (H10 (N + 1)%nat). elim H36. exists [\(α, β\)]. split. red; intros.
  applyClassifier1 H37. rewrite H37,<-H24; auto. split. left.
  apply SingletonFinite. split. red; intros. applyClassifier1 H37.
  apply Classifier1; eauto. intros. exists \(α, β\). split; auto.
  apply Classifier1; auto.
Qed.


(* 定义 数列f的聚点为a *)
Definition Seq_Cluster_Point f a := IsSeq f
  /\ (∀ ε, 0 < ε -> ~ Finite \{ λ u, f[u] ∈ U(a; ε) \}).

(* 数列最大聚点存在性 *)
Theorem Theorem7_4a : ∀ f, BoundedSeq f
  -> (∃ M, Seq_Cluster_Point f M /\ (∀ a, Seq_Cluster_Point f a -> a <= M)).
Proof.
  intros. destruct H as [H[M]].
  assert (-(M + 1) < M + 1).
  { pose proof (H0 0%nat). pose proof (Abs_Rge0 (f[0%nat])). lra. }
  assert (ran[f] ⊂ \[-(M+1), (M+1)\]).
  { red; intros. applyClassifier1 H2. destruct H2. destruct H.
    apply f_x_T in H2; auto. pose proof (H0 x). rewrite H2 in H4.
    apply Abs_le_R in H4. apply Classifier1. lra. }
  set (le D := c \{ λ u, inf D u \}). set (ri D := c \{ λ u, sup D u \}).
  set (fix A n := match n with |O => \[-(M+1), (M+1)\]
    |S m => c \{ λ u,
      (~ Finite \{ λ u, f[u] ∈ (\[((le (A m)) + (ri (A m)))/2, (ri (A m))\]) \}
        -> u = \[((le (A m)) + (ri (A m)))/2, (ri (A m))\])
      /\ (Finite \{ λ u, f[u] ∈ (\[((le (A m)) + (ri (A m)))/2, (ri (A m))\]) \}
        -> u = \[(le (A m)), ((le (A m)) + (ri (A m)))/2\]) \} end)
  as A. set (g := \{\ λ u v, v = A u \}\).
  assert (∀ a b, a <= b -> le (\[a, b\]) = a /\ ri (\[a, b\]) = b).
  { intros. assert (a ∈ \{ λ u, inf (\[a, b\]) u \}
      /\ b ∈ \{ λ u, sup (\[a, b\]) u \}) as [].
    { split; apply Classifier1; split; unfold Upper,Lower; intros.
      applyClassifier1 H4. lra. assert (b < b0 \/ b0 <= b) as []. lra.
      exists b. split; auto. apply Classifier1. lra. exists a. split.
      apply Classifier1; lra. lra. applyClassifier1 H4; lra.
      assert (a <= a0 \/ a0 < a) as []. lra. exists b. split; auto.
      apply Classifier1; lra. exists a. split. apply Classifier1. lra. lra. }
    assert ((le (\[a, b\])) ∈ \{ λ u, inf (\[a, b\]) u \}
      /\ (ri (\[a, b\])) ∈ \{ λ u, sup (\[a, b\]) u \}) as [].
    { split; apply Axiomc; unfold NotEmpty; eauto. }
    applyClassifier1 H4. applyClassifier1 H5. applyClassifier1 H6.
    applyClassifier1 H7. destruct H4,H5,H6,H7. split.
    destruct (Rtotal_order a (le (\[a, b\]))).
    assert (a >= le (\[a, b\])). { apply H6. apply Classifier1; lra. }
    exfalso. lra. destruct H12; auto. apply H10 in H12 as [x[]].
    applyClassifier1 H12. exfalso. lra.
    destruct (Rtotal_order b (ri (\[a, b\]))) as [H12|[]]; auto.
    apply H11 in H12 as [x[]]. applyClassifier1 H12. exfalso. lra.
    assert (b <= ri (\[a, b\])). { apply H7. apply Classifier1; lra. }
    exfalso. lra. }
  assert (∀ m, (le (A m)) < (ri (A m))).
  { intros. induction m. simpl. assert (-(M+1) <= (M+1)). lra.
    apply H3 in H4 as []. rewrite H4,H5; auto.
    assert ((A (S m)) ∈ \{ λ u,
      (~ Finite \{ λ u, f[u] ∈ (\[((le (A m)) + (ri (A m)))/2, (ri (A m))\]) \}
        -> u = \[(le (A m) + ri (A m))/2, (ri (A m))\])
      /\ (Finite \{ λ u, f[u] ∈ (\[((le (A m)) + (ri (A m)))/2, (ri (A m))\]) \}
        -> u = \[(le (A m)), (le (A m) + ri (A m))/2\]) \}).
    { apply Axiomc. destruct (classic
      (Finite \{ λ u, f[u] ∈ (\[((le (A m)) + (ri (A m)))/2, (ri (A m))\]) \}));
      [exists (\[(le (A m)), (le (A m) + ri (A m))/2\])
      |exists (\[(le (A m) + ri (A m))/2, (ri (A m))\])]; apply Classifier1;
      split; intros; auto; contradiction. }
    apply ->Classifier1 in H4. destruct H4. destruct (classic
    (Finite \{ λ u, f[u] ∈ (\[((le (A m)) + (ri (A m)))/2, (ri (A m))\]) \})).
    apply H5 in H6. rewrite H6.
    assert ((le (A m)) <= (((le (A m)) + (ri (A m)))/2)). lra.
    apply H3 in H7 as []. rewrite H7,H8. lra.
    apply H4 in H6. rewrite H6.
    assert ((((le (A m)) + (ri (A m)))/2) <= (ri (A m))). lra.
    apply H3 in H7 as []. rewrite H7,H8. lra. }
  assert (∀ m,
    ~ Finite \{ λ u, f[u] ∈ (\[((le (A m)) + (ri (A m)))/2, (ri (A m))\]) \}
    -> (A (S m)) = \[(le (A m) + ri (A m))/2, (ri (A m))\]).
  { intros. assert ((A (S m)) ∈ \{ λ u,
      (~ Finite \{ λ u, f[u] ∈ (\[((le (A m)) + (ri (A m)))/2, (ri (A m))\]) \}
        -> u = \[(le (A m) + ri (A m))/2, (ri (A m))\])
      /\ (Finite \{ λ u, f[u] ∈ (\[((le (A m)) + (ri (A m)))/2, (ri (A m))\]) \}
        -> u = \[(le (A m)), (le (A m) + ri (A m))/2\]) \}).
    { apply Axiomc. exists (\[(le (A m) + ri (A m))/2, (ri (A m))\]).
      apply Classifier1. split; intros; auto. contradiction. }
    apply ->Classifier1 in H6. destruct H6. apply H6 in H5. rewrite H5; auto. }
  assert (∀ m,
    Finite \{ λ u, f[u] ∈ (\[((le (A m)) + (ri (A m)))/2, (ri (A m))\]) \}
    -> (A (Datatypes.S m)) = \[(le (A m)), (le (A m) + ri (A m))/2\]).
  { intros. assert ((A (S m)) ∈ \{ λ u,
      (~ Finite \{ λ u, f[u] ∈ (\[((le (A m)) + (ri (A m)))/2, (ri (A m))\]) \}
        -> u = \[(le (A m) + ri (A m))/2, (ri (A m))\])
      /\ (Finite \{ λ u, f[u] ∈ (\[((le (A m)) + (ri (A m)))/2, (ri (A m))\]) \}
        -> u = \[(le (A m)), (le (A m) + ri (A m))/2\]) \}).
    { apply Axiomc. exists (\[(le (A m)), (le (A m) + ri (A m))/2\]).
      apply Classifier1. split; intros; auto. contradiction. }
    apply ->Classifier1 in H7. destruct H7. apply H8 in H6. rewrite H6; auto. }
  assert (Interval_Seq g).
  { split. red; intros. applyClassifier2 H7. applyClassifier2 H8.
    rewrite H7,H8; auto. split. apply AxiomI; split; intros.
    apply Classifier1; auto. apply Classifier1.
    exists (A z). apply Classifier2; auto. red; intros. apply Classifier1.
    applyClassifier1 H7. destruct H7. applyClassifier2 H7. destruct x.
    exists (-(M+1)),(M+1). auto. destruct (classic
    (Finite \{ λ u, f[u] ∈ (\[((le (A x)) + (ri (A x)))/2, (ri (A x))\]) \}));
    [apply H6 in H8|apply H5 in H8]; rewrite H7,H8;
    [exists (le (A x)),((le (A x) + ri (A x))/2)
    |exists ((le (A x) + ri (A x))/2),(ri (A x))]; split; auto;
    pose proof (H4 x); lra. }
  assert (∀ m, A m = \[(le (A m)), (ri (A m))\]).
  { intros. destruct m. simpl. pose proof H1. apply Rlt_le,H3 in H8 as [].
    rewrite H8,H9; auto. destruct (classic
    (Finite \{ λ u, f[u] ∈ (\[((le (A m)) + (ri (A m)))/2, (ri (A m))\]) \})).
    apply H6 in H8. rewrite H8. pose proof (H4 m).
    assert ((le (A m) <= ((le (A m)) + (ri (A m)))/2)). lra.
    apply H3 in H10 as []. rewrite H10,H11; auto.
    apply H5 in H8. rewrite H8. pose proof (H4 m).
    assert ((((le (A m)) + (ri (A m)))/2) <= (ri (A m))). lra.
    apply H3 in H10 as []. rewrite H10,H11; auto. }
  assert (∀ m, g[S m] ⊂ g[m]).
  { red; intros. unfold g in H9. rewrite FunValue in H9. unfold g.
    rewrite FunValue. destruct (classic
    (Finite \{ λ u, f[u] ∈ (\[((le (A m)) + (ri (A m)))/2, (ri (A m))\]) \}));
    [apply H6 in H10|apply H5 in H10]; rewrite H10 in H9; rewrite H8;
    pose proof (H4 m); applyClassifier1 H9; apply Classifier1; lra. }
  assert (∀ m, ~ Finite \{ λ u, f[u] ∈ g[m] \}
    /\ Finite \{ λ u, (ri (A m)) < f[u] \}).
  { intros. unfold g. rewrite FunValue. induction m. simpl.
    assert (\{ λ u, f[u] ∈ \[-(M+1), (M+1)\] \} = dom[f]).
    { destruct H. apply AxiomI; split; intros. rewrite H10.
      apply Classifier1; auto. apply Classifier1,H2,Classifier1. exists z.
      apply x_fx_T; auto. }
    assert (\{ λ u, (ri (\[-(M+1), (M+1)\])) < f[u] \} = Empty nat).
    { apply AxiomI; split; intros. applyClassifier1 H11. pose proof H1.
      apply Rlt_le,H3 in H12 as []. rewrite H13 in H11.
      assert (z ∈ dom[f]). { destruct H. rewrite H14. apply Classifier1; auto. }
      apply x_fx_T in H14. assert (f[z] ∈ ran[f]). { apply Classifier1; eauto. }
      apply H2 in H15. applyClassifier1 H15. exfalso. lra. destruct H; auto.
      applyClassifier1 H11. elim H11; auto. }
    rewrite H10,H11. split. intro. destruct H. rewrite H13 in H12.
    destruct H12. apply finite_maxN in H12 as [x[]].
    assert (S x ∈ Full nat). { apply Classifier1; auto. } apply H14 in H15. lia.
    assert (0%nat ∈ Empty nat). { rewrite <-H12. apply Classifier1; auto. }
    applyClassifier1 H14. auto. right; auto. destruct (classic
    (Finite \{ λ u, f[u] ∈ (\[((le (A m)) + (ri (A m)))/2, (ri (A m))\]) \})).
    - pose proof (H6 m H10). destruct IHm. split. intro. elim H12.
      assert (\{ λ u, f[u] ∈ (A m) \}
         ⊂ \{ λ u, f[u] ∈ \[(le (A m) + ri (A m))/2, ri (A m)\] \}
         ∪ \{ λ u, f[u] ∈ A (S m) \}).
      { red; intros. applyClassifier1 H15. rewrite H8 in H15. applyClassifier1 H15.
        destruct H15. pose proof (H4 m). apply Classifier1. rewrite H11.
        assert (f[z] <= (le (A m) + ri (A m))/2
          \/ (le (A m) + ri (A m))/2 <= f[z]) as [] by lra; [right|left];
        apply Classifier1; apply Classifier1; lra. }
      apply SubSetFinite in H15; auto. apply Finite_union_Finite; auto.
      assert (\{ λ u, (ri (A (S m))) < f[u] \}
         ⊂ \{ λ u, (ri (A m)) < f[u] \}
         ∪ \{ λ u, f[u] ∈ \[(le (A m) + ri (A m))/2, ri (A m)\] \}).
      { red; intros. rewrite H11 in H14. applyClassifier1 H14. pose proof (H4 m).
        assert (le (A m) <= (le (A m) + ri (A m))/2). lra. apply H3 in H16 as [].
        rewrite H17 in H14. apply Classifier1.
        assert (f[z] <= ri (A m) \/ ri (A m) < f[z]) as [] by lra; [right|left];
        apply Classifier1; [apply Classifier1| ]; auto. lra. }
      apply SubSetFinite in H14; auto. apply Finite_union_Finite; auto.
    - pose proof (H5 m H10). destruct IHm. split. intro. rewrite H11 in H14; auto.
      assert (\{ λ u, ri (A (S m)) < f[u] \} ⊂ \{ λ u, ri (A m) < f[u] \}).
      { red; intros. rewrite H11 in H14. applyClassifier1 H14.
        assert ((le (A m) + ri (A m))/2 <= ri (A m)). { pose proof (H4 m). lra. }
        apply H3 in H15 as []. rewrite H16 in H14. apply Classifier1; auto. }
      apply SubSetFinite in H14; auto. }
  assert (∀ m, (RightSeq g)[m] = ri (g[m])).
  { intros. pose proof (H4 m). apply (RightSeq_Value g _ _ m) in H11; auto;
    unfold g; rewrite FunValue; auto. }
  assert (∀ m, (LeftSeq g)[m] = le (g[m])).
  { intros. pose proof (H4 m). apply (LeftSeq_Value g _ _ m) in H12; auto;
    unfold g; rewrite FunValue; auto. }
  set (fix zs m := match m with |O => 1 |S k => 1/2 * (zs k) end) as zs.
  assert (∀ m, (RightSeq g)[m] - (LeftSeq g)[m] = (zs m) * (2*(M+1))).
  { intros. induction m. rewrite H11,H12. unfold g. rewrite FunValue. simpl.
    pose proof H1. apply Rlt_le,H3 in H13 as []. rewrite H13,H14. lra.
    rewrite H11,H12. unfold g. rewrite FunValue. simpl zs.
    rewrite H11,H12 in IHm. unfold g in IHm. rewrite FunValue in IHm.
    pose proof (H4 m). assert (le (A m) < (le (A m) + ri (A m))/2 < ri (A m)). lra.
    destruct H14. apply Rlt_le,H3 in H14 as [], H15 as []. destruct (classic
    (Finite \{ λ u, f[u] ∈ (\[((le (A m)) + (ri (A m)))/2, (ri (A m))\]) \}));
    [apply H6 in H18|apply H5 in H18]; rewrite H18.
    rewrite H14,H16,Rmult_assoc,<-IHm. lra.
    rewrite H15,H17,Rmult_assoc,<-IHm. lra. }
  assert (limit_seq \{\ λ u v, v = (RightSeq g)[u] - (LeftSeq g)[u] \}\ 0).
  { split. split. red; intros. applyClassifier2 H14. applyClassifier2 H15.
    rewrite H14,H15; auto. apply AxiomI; split; intros. apply Classifier1; auto.
    apply Classifier1. exists ((RightSeq g)[z] - (LeftSeq g)[z]).
    apply Classifier2; auto. intros.
    assert ((2*(M+1))/ε > 0). { apply Rdiv_lt_0_compat; lra. }
    pose proof H15. apply (Archimedes 1) in H16 as [k]; [ |lra].
    assert (1/(INR k) < ε/(2*(M+1))).
    { pose proof H16. apply (Rmult_lt_compat_l ε) in H17; auto.
      unfold Rdiv in H17. rewrite <-Rmult_assoc,Rinv_r_simpl_m in H17; [ |lra].
      rewrite Rmult_1_r in H17.
      apply (Rmult_lt_compat_l (/(INR k))) in H17;
      [ |apply Rinv_0_lt_compat; lra].
      rewrite (Rmult_comm _ (ε * (INR k))),Rinv_r_simpl_l in H17.
      apply (Rmult_lt_compat_r (/(2*(M+1)))) in H17;
      [ |apply Rinv_0_lt_compat; lra].
      rewrite Rinv_r_simpl_l in H17; [ |lra]. lra. assert (0 < INR k). lra. lra. }
    assert (∀ m, (0 < m)%nat -> zs m < 1/(INR m)).
    { intros. induction m. exfalso. lia. simpl zs. assert (m = 0 \/ 0 < m)%nat.
      lia. destruct H19. rewrite H19. simpl. lra. pose proof H19.
      apply IHm in H20. apply (Rmult_lt_compat_l (1/2)) in H20; [ |lra].
      assert (1/2 * (1/(INR m)) <= 1/(INR (S m))).
      { replace (INR (S m)) with ((INR m) + 1). unfold Rdiv.
        pose proof H19. apply lt_INR in H21. simpl in H21.
        assert (INR 1 <= INR m). { apply le_INR. lia. } simpl in H22.
        rewrite Rmult_1_l,Rmult_1_l,Rmult_1_l,<-Rinv_mult; try lra.
        apply Rinv_le_contravar. lra. lra. destruct m; auto. simpl; lra. } lra. }
    assert (∀ m, zs m > 0). { intros. induction m; simpl; lra. }
    exists k. intros. rewrite FunValue,H13,Rminus_0_r. rewrite Abs_ge.
    assert (0 < n)%nat. lia. pose proof (H18 n H21).
    assert (1/(INR n) < 1/(INR k)).
    { unfold Rdiv. rewrite Rmult_1_l,Rmult_1_l. apply Rinv_lt_contravar.
      apply lt_INR in H21. simpl in H21. apply Rmult_lt_0_compat; lra.
      apply lt_INR; auto. } assert (zs n < ε/(2*(M+1))). lra.
    apply (Rmult_lt_compat_l (2*(M+1))) in H24; [ |lra]. unfold Rdiv in H24.
    rewrite <-Rmult_assoc,Rinv_r_simpl_m in H24; lra. pose proof (H19 n).
    apply Rle_ge,Rmult_le_pos; lra. }
  assert (Interval_Nest g). { split; auto. }
  pose proof H15. apply Theorem7_1a in H16 as [ξ[]]. exists ξ.
  pose proof (Corollary7_1 g ξ H15 H16). split.
  - split; auto. intros. destruct (H18 ε H19) as [N[]]. intro.
    destruct (H10 (S N)). elim H23.
    assert (\{ λ u, f[u] ∈ g[S N] \} ⊂ \{ λ u, f[u] ∈ U(ξ; ε) \}).
    { red; intros. applyClassifier1 H25. apply Classifier1.
      apply H21 in H25; auto. }
    apply SubSetFinite in H25; auto.
  - intros ξ1 H19. assert (ξ1 <= ξ \/ ξ < ξ1) as [] by lra; auto. destruct H19.
    assert ((ξ1 - ξ)/2 > 0). lra. pose proof H22. apply H21 in H23.
    pose proof H22. apply H18 in H24 as [N[]]. destruct (H10 (S N)). elim H23.
    assert (\{ λ u, f[u] ∈ U(ξ1; ((ξ1 - ξ)/2)) \}
       ⊂ \{ λ u, (ri (A (S N))) < f[u] \}).
    { assert ((S N) > N)%nat. lia. apply H25 in H28. unfold g in H28.
      rewrite FunValue in H28. red; intros. applyClassifier1 H29.
      apply Classifier1. applyClassifier1 H29. apply Abs_R in H29.
      rewrite H8 in H28.
      assert ((ri (A (S N))) ∈ \[le (A (S N)), ri (A (S N))\]).
      { apply Classifier1. pose proof (H4 (S N)). lra. }
      apply H28 in H30. apply ->Classifier1 in H30. apply Abs_R in H30. lra. }
    apply SubSetFinite in H28; auto.
Qed.

(* 数列最小聚点存在性 *)
Theorem Theorem7_4b : ∀ f, BoundedSeq f
  -> (∃ m, Seq_Cluster_Point f m /\ (∀ a, Seq_Cluster_Point f a -> m <= a)).
Proof.
  intros. destruct H as [H[M]].
  assert (-(M + 1) < M + 1).
  { pose proof (H0 0%nat). pose proof (Abs_Rge0 (f[0%nat])). lra. }
  assert (ran[f] ⊂ \[-(M+1), (M+1)\]).
  { red; intros. applyClassifier1 H2. destruct H2. destruct H.
    apply f_x_T in H2; auto. pose proof (H0 x). rewrite H2 in H4.
    apply Abs_le_R in H4. apply Classifier1. lra. }
  set (le D := c \{ λ u, inf D u \}). set (ri D := c \{ λ u, sup D u \}).
  set (fix A n := match n with |O => \[-(M+1), (M+1)\]
    |S m => c \{ λ u,
      (~ Finite \{ λ u, f[u] ∈ (\[(le (A m)), ((le (A m)) + (ri (A m)))/2\]) \}
        -> u = \[(le (A m)), ((le (A m)) + (ri (A m)))/2\])
      /\ (Finite \{ λ u, f[u] ∈ (\[(le (A m)), ((le (A m)) + (ri (A m)))/2\]) \}
        -> u = \[((le (A m)) + (ri (A m)))/2, (ri (A m))\]) \} end)
  as A. set (g := \{\ λ u v, v = A u \}\).
  assert (∀ a b, a <= b -> le (\[a, b\]) = a /\ ri (\[a, b\]) = b).
  { intros. assert (a ∈ \{ λ u, inf (\[a, b\]) u \}
      /\ b ∈ \{ λ u, sup (\[a, b\]) u \}) as [].
    { split; apply Classifier1; split; unfold Upper,Lower; intros.
      applyClassifier1 H4. lra. assert (b < b0 \/ b0 <= b) as []. lra.
      exists b. split; auto. apply Classifier1. lra. exists a. split.
      apply Classifier1; lra. lra. applyClassifier1 H4; lra.
      assert (a <= a0 \/ a0 < a) as []. lra. exists b. split; auto.
      apply Classifier1; lra. exists a. split. apply Classifier1. lra. lra. }
    assert ((le (\[a, b\])) ∈ \{ λ u, inf (\[a, b\]) u \}
      /\ (ri (\[a, b\])) ∈ \{ λ u, sup (\[a, b\]) u \}) as [].
    { split; apply Axiomc; unfold NotEmpty; eauto. }
    applyClassifier1 H4. applyClassifier1 H5. applyClassifier1 H6.
    applyClassifier1 H7. destruct H4,H5,H6,H7. split.
    destruct (Rtotal_order a (le (\[a, b\]))).
    assert (a >= le (\[a, b\])). { apply H6. apply Classifier1; lra. }
    exfalso. lra.
    destruct H12; auto. apply H10 in H12 as [x[]]. applyClassifier1 H12.
    exfalso. lra. destruct (Rtotal_order b (ri (\[a, b\]))) as [H12|[]]; auto.
    apply H11 in H12 as [x[]]. applyClassifier1 H12. exfalso. lra.
    assert (b <= ri (\[a, b\])). { apply H7. apply Classifier1; lra. }
    exfalso. lra. }
  assert (∀ m, (le (A m)) < (ri (A m))).
  { intros. induction m. simpl. assert (-(M+1) <= (M+1)). lra.
    apply H3 in H4 as []. rewrite H4,H5; auto.
    assert ((A (S m)) ∈ \{ λ u,
      (~ Finite \{ λ u, f[u] ∈ (\[(le (A m)), ((le (A m)) + (ri (A m)))/2\]) \}
        -> u = \[(le (A m)), (le (A m) + ri (A m))/2\])
      /\ (Finite \{ λ u, f[u] ∈ (\[(le (A m)), ((le (A m)) + (ri (A m)))/2\]) \}
        -> u = \[(le (A m) + ri (A m))/2, (ri (A m))\]) \}).
    { apply Axiomc. destruct (classic
      (Finite \{ λ u, f[u] ∈ (\[(le (A m)), ((le (A m)) + (ri (A m)))/2\]) \}));
      [exists (\[(le (A m) + ri (A m))/2, (ri (A m))\])
      |exists (\[(le (A m)), (le (A m) + ri (A m))/2\])]; apply Classifier1;
      split; intros; auto; contradiction. }
    apply ->Classifier1 in H4. destruct H4. destruct (classic
    (Finite \{ λ u, f[u] ∈ (\[(le (A m)), ((le (A m)) + (ri (A m)))/2\]) \})).
    apply H5 in H6. rewrite H6.
    assert ((((le (A m)) + (ri (A m)))/2) <= (ri (A m))). lra.
    apply H3 in H7 as []. rewrite H7,H8. lra.
    apply H4 in H6. rewrite H6.
    assert ((le (A m)) <= (((le (A m)) + (ri (A m)))/2)). lra.
    apply H3 in H7 as []. rewrite H7,H8. lra. }
  assert (∀ m,
    ~ Finite \{ λ u, f[u] ∈ (\[(le (A m)), ((le (A m)) + (ri (A m)))/2\]) \}
    -> (A (S m)) = \[(le (A m)), (le (A m) + ri (A m))/2\]).
  { intros. assert ((A (S m)) ∈ \{ λ u,
      (~ Finite \{ λ u, f[u] ∈ (\[(le (A m)), ((le (A m)) + (ri (A m)))/2\]) \}
        -> u = \[(le (A m)), (le (A m) + ri (A m))/2\])
      /\ (Finite \{ λ u, f[u] ∈ (\[(le (A m)), ((le (A m)) + (ri (A m)))/2\]) \}
        -> u = \[(le (A m) + ri (A m))/2, (ri (A m))\]) \}).
    { apply Axiomc. exists (\[(le (A m)), (le (A m) + ri (A m))/2\]).
      apply Classifier1. split; intros; auto. contradiction. }
    apply ->Classifier1 in H6. destruct H6. apply H6 in H5. rewrite H5; auto. }
  assert (∀ m,
    Finite \{ λ u, f[u] ∈ (\[(le (A m)), ((le (A m)) + (ri (A m)))/2\]) \}
    -> (A (Datatypes.S m)) = \[(le (A m) + ri (A m))/2, (ri (A m))\]).
  { intros. assert ((A (S m)) ∈ \{ λ u,
      (~ Finite \{ λ u, f[u] ∈ (\[(le (A m)), ((le (A m)) + (ri (A m)))/2\]) \}
        -> u = \[(le (A m)), (le (A m) + ri (A m))/2\])
      /\ (Finite \{ λ u, f[u] ∈ (\[(le (A m)), ((le (A m)) + (ri (A m)))/2\]) \}
        -> u = \[(le (A m) + ri (A m))/2, (ri (A m))\]) \}).
    { apply Axiomc. exists (\[(le (A m) + ri (A m))/2, (ri (A m))\]).
      apply Classifier1. split; intros; auto. contradiction. }
    apply ->Classifier1 in H7. destruct H7. apply H8 in H6. rewrite H6; auto. }
  assert (Interval_Seq g).
  { split. red; intros. applyClassifier2 H7. applyClassifier2 H8.
    rewrite H7,H8; auto. split. apply AxiomI; split; intros.
    apply Classifier1; auto. apply Classifier1.
    exists (A z). apply Classifier2; auto. red; intros. apply Classifier1.
    applyClassifier1 H7. destruct H7. applyClassifier2 H7. destruct x.
    exists (-(M+1)),(M+1). auto. destruct (classic
    (Finite \{ λ u, f[u] ∈ (\[(le (A x)), ((le (A x)) + (ri (A x)))/2\]) \}));
    [apply H6 in H8|apply H5 in H8]; rewrite H7,H8;
    [exists ((le (A x) + ri (A x))/2),(ri (A x))
    |exists (le (A x)),((le (A x) + ri (A x))/2)]; split; auto;
    pose proof (H4 x); lra. }
  assert (∀ m, A m = \[(le (A m)), (ri (A m))\]).
  { intros. destruct m. simpl. pose proof H1. apply Rlt_le,H3 in H8 as [].
    rewrite H8,H9; auto. destruct (classic
    (Finite \{ λ u, f[u] ∈ (\[(le (A m)), ((le (A m)) + (ri (A m)))/2\]) \})).
    apply H6 in H8. rewrite H8. pose proof (H4 m).
    assert ((((le (A m)) + (ri (A m)))/2) <= (ri (A m))). lra.
    apply H3 in H10 as []. rewrite H10,H11; auto.
    apply H5 in H8. rewrite H8. pose proof (H4 m).
    assert ((le (A m)) <= (((le (A m)) + (ri (A m)))/2)). lra.
    apply H3 in H10 as []. rewrite H10,H11; auto. }
  assert (∀ m, g[S m] ⊂ g[m]).
  { red; intros. unfold g in H9. rewrite FunValue in H9. unfold g.
    rewrite FunValue. destruct (classic
    (Finite \{ λ u, f[u] ∈ (\[(le (A m)), ((le (A m)) + (ri (A m)))/2\]) \}));
    [apply H6 in H10|apply H5 in H10]; rewrite H10 in H9; rewrite H8;
    pose proof (H4 m); applyClassifier1 H9; apply Classifier1; lra. }
  assert (∀ m, ~ Finite \{ λ u, f[u] ∈ g[m] \}
    /\ Finite \{ λ u, f[u] < (le (A m)) \}).
  { intros. unfold g. rewrite FunValue. induction m. simpl.
    assert (\{ λ u, f[u] ∈ \[-(M+1), (M+1)\] \} = dom[f]).
    { destruct H. apply AxiomI; split; intros. rewrite H10.
      apply Classifier1; auto. apply Classifier1,H2,Classifier1.
      exists z. apply x_fx_T; auto. }
    assert (\{ λ u, f[u] < (le (\[-(M+1), (M+1)\])) \} = Empty nat).
    { apply AxiomI; split; intros. applyClassifier1 H11. pose proof H1.
      apply Rlt_le,H3 in H12 as []. rewrite H12 in H11.
      assert (z ∈ dom[f]). { destruct H. rewrite H14. apply Classifier1; auto. }
      apply x_fx_T in H14. assert (f[z] ∈ ran[f]). { apply Classifier1; eauto. }
      apply H2 in H15. applyClassifier1 H15. exfalso. lra. destruct H; auto.
      applyClassifier1 H11. elim H11; auto. }
    rewrite H10,H11. split. intro. destruct H. rewrite H13 in H12.
    destruct H12. apply finite_maxN in H12 as [x[]].
    assert (S x ∈ Full nat). { apply Classifier1; auto. } apply H14 in H15. lia.
    assert (0%nat ∈ Empty nat). { rewrite <-H12. apply Classifier1; auto. }
    applyClassifier1 H14. auto. right; auto. destruct (classic
    (Finite \{ λ u, f[u] ∈ (\[(le (A m)), ((le (A m)) + (ri (A m)))/2\]) \})).
    - pose proof (H6 m H10). destruct IHm. split. intro. elim H12.
      assert (\{ λ u, f[u] ∈ (A m) \}
         ⊂ \{ λ u, f[u] ∈ \[(le (A m)), (le (A m) + ri (A m))/2\] \}
         ∪ \{ λ u, f[u] ∈ A (S m) \}).
      { red; intros. applyClassifier1 H15.
        rewrite H8 in H15. applyClassifier1 H15.
        destruct H15. pose proof (H4 m). apply Classifier1. rewrite H11.
        assert (f[z] <= (le (A m) + ri (A m))/2
          \/ (le (A m) + ri (A m))/2 <= f[z]) as [] by lra; [left|right];
        apply Classifier1; apply Classifier1; lra. }
      apply SubSetFinite in H15; auto. apply Finite_union_Finite; auto.
      assert (\{ λ u, f[u] < (le (A (S m))) \}
         ⊂ \{ λ u, f[u] < (le (A m)) \}
         ∪ \{ λ u, f[u] ∈ \[(le (A m)), (le (A m) + ri (A m))/2\] \}).
      { red; intros. rewrite H11 in H14. applyClassifier1 H14. pose proof (H4 m).
        assert ((le (A m) + ri (A m))/2 <= (ri (A m))). lra.
        apply H3 in H16 as []. rewrite H16 in H14. apply Classifier1.
        assert (f[z] < le (A m) \/ le (A m) <= f[z]) as [] by lra; [left|right];
        apply Classifier1; [ |apply Classifier1]; auto. lra. }
      apply SubSetFinite in H14; auto. apply Finite_union_Finite; auto.
    - pose proof (H5 m H10). destruct IHm. split. intro. rewrite H11 in H14; auto.
      assert (\{ λ u, f[u] < (le (A (S m))) \} ⊂ \{ λ u, f[u] < (le (A m)) \}).
      { red; intros. rewrite H11 in H14. applyClassifier1 H14.
        assert ((le (A m)) <= (le (A m) + ri (A m))/2). { pose proof (H4 m). lra. }
        apply H3 in H15 as []. rewrite H15 in H14. apply Classifier1; auto. }
      apply SubSetFinite in H14; auto. }
  assert (∀ m, (RightSeq g)[m] = ri (g[m])).
  { intros. pose proof (H4 m). apply (RightSeq_Value g _ _ m) in H11; auto;
    unfold g; rewrite FunValue; auto. }
  assert (∀ m, (LeftSeq g)[m] = le (g[m])).
  { intros. pose proof (H4 m). apply (LeftSeq_Value g _ _ m) in H12; auto;
    unfold g; rewrite FunValue; auto. }
  set (fix zs m := match m with |O => 1 |S k => 1/2 * (zs k) end) as zs.
  assert (∀ m, (RightSeq g)[m] - (LeftSeq g)[m] = (zs m) * (2*(M+1))).
  { intros. induction m. rewrite H11,H12. unfold g. rewrite FunValue. simpl.
    pose proof H1. apply Rlt_le,H3 in H13 as []. rewrite H13,H14. lra.
    rewrite H11,H12. unfold g. rewrite FunValue. simpl zs.
    rewrite H11,H12 in IHm. unfold g in IHm. rewrite FunValue in IHm.
    pose proof (H4 m). assert (le (A m) < (le (A m) + ri (A m))/2 < ri (A m)). lra.
    destruct H14. apply Rlt_le,H3 in H14 as [], H15 as []. destruct (classic
    (Finite \{ λ u, f[u] ∈ (\[(le (A m)), ((le (A m)) + (ri (A m)))/2\]) \}));
    [apply H6 in H18|apply H5 in H18]; rewrite H18.
    rewrite H17,H15,Rmult_assoc,<-IHm. lra.
    rewrite H16,H14,Rmult_assoc,<-IHm. lra. }
  assert (limit_seq \{\ λ u v, v = (RightSeq g)[u] - (LeftSeq g)[u] \}\ 0).
  { split. split. red; intros. applyClassifier2 H14. applyClassifier2 H15.
    rewrite H14,H15; auto. apply AxiomI; split; intros. apply Classifier1; auto.
    apply Classifier1. exists ((RightSeq g)[z] - (LeftSeq g)[z]).
    apply Classifier2; auto. intros.
    assert ((2*(M+1))/ε > 0). { apply Rdiv_lt_0_compat; lra. }
    pose proof H15. apply (Archimedes 1) in H16 as [k]; [ |lra].
    assert (1/(INR k) < ε/(2*(M+1))).
    { pose proof H16. apply (Rmult_lt_compat_l ε) in H17; auto.
      unfold Rdiv in H17. rewrite <-Rmult_assoc,Rinv_r_simpl_m in H17; [ |lra].
      rewrite Rmult_1_r in H17.
      apply (Rmult_lt_compat_l (/(INR k))) in H17;
      [ |apply Rinv_0_lt_compat; lra].
      rewrite (Rmult_comm _ (ε * (INR k))),Rinv_r_simpl_l in H17.
      apply (Rmult_lt_compat_r (/(2*(M+1)))) in H17;
      [ |apply Rinv_0_lt_compat; lra].
      rewrite Rinv_r_simpl_l in H17; [ |lra]. lra. assert (0 < INR k). lra. lra. }
    assert (∀ m, (0 < m)%nat -> zs m < 1/(INR m)).
    { intros. induction m. exfalso. lia. simpl zs. assert (m = 0 \/ 0 < m)%nat.
      lia. destruct H19. rewrite H19. simpl. lra. pose proof H19.
      apply IHm in H20. apply (Rmult_lt_compat_l (1/2)) in H20; [ |lra].
      assert (1/2 * (1/(INR m)) <= 1/(INR (S m))).
      { replace (INR (S m)) with ((INR m) + 1). unfold Rdiv.
        pose proof H19. apply lt_INR in H21. simpl in H21.
        assert (INR 1 <= INR m). { apply le_INR. lia. } simpl in H22.
        rewrite Rmult_1_l,Rmult_1_l,Rmult_1_l,<-Rinv_mult; try lra.
        apply Rinv_le_contravar. lra. lra. destruct m; auto. simpl; lra. } lra. }
    assert (∀ m, zs m > 0). { intros. induction m; simpl; lra. }
    exists k. intros. rewrite FunValue,H13,Rminus_0_r. rewrite Abs_ge.
    assert (0 < n)%nat. lia. pose proof (H18 n H21).
    assert (1/(INR n) < 1/(INR k)).
    { unfold Rdiv. rewrite Rmult_1_l,Rmult_1_l. apply Rinv_lt_contravar.
      apply lt_INR in H21. simpl in H21. apply Rmult_lt_0_compat; lra.
      apply lt_INR; auto. } assert (zs n < ε/(2*(M+1))). lra.
    apply (Rmult_lt_compat_l (2*(M+1))) in H24; [ |lra]. unfold Rdiv in H24.
    rewrite <-Rmult_assoc,Rinv_r_simpl_m in H24; lra. pose proof (H19 n).
    apply Rle_ge,Rmult_le_pos; lra. }
  assert (Interval_Nest g). { split; auto. }
  pose proof H15. apply Theorem7_1a in H16 as [ξ[]]. exists ξ.
  pose proof (Corollary7_1 g ξ H15 H16). split.
  - split; auto. intros. destruct (H18 ε H19) as [N[]]. intro.
    destruct (H10 (S N)). elim H23.
    assert (\{ λ u, f[u] ∈ g[S N] \} ⊂ \{ λ u, f[u] ∈ U(ξ; ε) \}).
    { red; intros. applyClassifier1 H25. apply Classifier1.
    apply H21 in H25; auto. }
    apply SubSetFinite in H25; auto.
  - intros ξ1 H19. assert (ξ1 < ξ \/ ξ <= ξ1) as [] by lra; auto. destruct H19.
    assert ((ξ - ξ1)/2 > 0). lra. pose proof H22. apply H21 in H23.
    pose proof H22. apply H18 in H24 as [N[]]. destruct (H10 (S N)). elim H23.
    assert (\{ λ u, f[u] ∈ U(ξ1; ((ξ - ξ1)/2)) \}
       ⊂ \{ λ u, f[u] < (le (A (S N))) \}).
    { assert ((S N) > N)%nat. lia. apply H25 in H28. unfold g in H28.
      rewrite FunValue in H28. red; intros. applyClassifier1 H29.
      apply Classifier1. applyClassifier1 H29. apply Abs_R in H29.
      rewrite H8 in H28.
      assert ((le (A (S N))) ∈ \[le (A (S N)), ri (A (S N))\]).
      { apply Classifier1. pose proof (H4 (S N)). lra. }
      apply H28 in H30. apply ->Classifier1 in H30. apply Abs_R in H30. lra. }
    apply SubSetFinite in H28; auto.
Qed.


(* 数列上极限 *)
Definition uplimit_seq f M := Seq_Cluster_Point f M
  /\ (∀ a, Seq_Cluster_Point f a -> a <= M).

(* 数列下极限 *)
Definition lowlimit_seq f m := Seq_Cluster_Point f m
  /\ (∀ a, Seq_Cluster_Point f a -> m <= a).

Theorem Theorem7_5 : ∀ f M m, lowlimit_seq f m -> uplimit_seq f M -> m <= M.
Proof. intros. destruct H,H0. apply H2 in H; auto. Qed.


(* 引理 子列的聚点也是原数列的聚点 *)
Lemma Lemma7_6 : ∀ f g ξ, SubSeq f g -> Seq_Cluster_Point g ξ
  -> Seq_Cluster_Point f ξ.
Proof.
  intros. destruct H as [H[H1[h[H2[]]]]]. destruct H0 as [_]. split; auto.
  assert (Function1_1 h).
  { destruct H2. split; auto. red; intros.
    applyClassifier2 H6. applyClassifier2 H7.
    assert (y = z \/ y < z \/ z < y)%nat. lia. destruct H8; auto.
    destruct H8; [apply (H5 y x z x) in H8|apply (H5 z x y x) in H8]; auto;
    exfalso; lia. }
  intros. pose proof H6. apply H0 in H7. pose proof H5 as [H8 _].
  pose proof (@RestrictFun1_1 nat nat h (\{ λ u, g[u] ∈ U(ξ; ε) \}) H5).
  destruct (@RestrictFun nat nat h ((\{ λ u, g[u] ∈ U(ξ; ε) \})) H8)
  as [H10[]].
  assert (ran[h|[\{ λ u, g[u] ∈ U(ξ; ε) \}]] ⊂ \{ λ u, f[u] ∈ U(ξ; ε) \}).
  { red; intros. applyClassifier1 H13. destruct H13. applyClassifier1 H13.
    destruct H13. applyClassifier2 H14. destruct H14.
    apply f_x_T in H13; auto. rewrite <-H13. applyClassifier1 H14.
    apply Classifier1. rewrite H4 in H14; auto. }
  assert (~ Finite ran[h|[\{ λ u, g[u] ∈ U(ξ; ε) \}]]).
  { apply (Infinite_equ_Infinite (dom[h|[\{ λ u, g[u] ∈ U(ξ; ε) \}]]) _
    (h|[\{ λ u, g[u] ∈ U(ξ; ε) \}])); auto.
    assert (\{ λ u, g[u] ∈ U(ξ; ε) \} ∩ dom[h] = \{ λ u, g[u] ∈ U(ξ; ε) \}).
    { rewrite H3. apply AxiomI; split; intros. applyClassifier1 H14. tauto.
      apply Classifier1; split; auto. apply Classifier1; auto. }
    rewrite H11,H14; auto. }
  intro. apply SubSetFinite in H13; auto.
Qed.

Theorem Theorem7_6 : ∀ f a, limit_seq f a
  <-> (BoundedSeq f /\ lowlimit_seq f a /\ uplimit_seq f a).
Proof.
  split; intros.
  - split. split; auto. destruct H; auto. apply Lemma2_3. red; eauto.
    apply EqualLimit in H as [].
    assert (∀ ε, 0 < ε -> ~ Finite \{ λ u, f[u] ∈ U(a; ε) \}).
    { intros. intro. pose proof H1. apply H0 in H3.
      assert (\{ λ u, f[u] ∈ U(a; ε) \} ∪ \{ λ u, f[u] ∉ U(a; ε) \} = Full nat).
      { apply AxiomI; split; intros. apply Classifier1; auto. apply Classifier1.
        destruct (classic (f[z] ∈ U(a; ε))); [left|right];
        apply Classifier1; auto. }
      assert (Finite (Full nat)).
      { rewrite <-H4. apply Finite_union_Finite; auto. }
      destruct H5. apply finite_maxN in H5 as [x[]].
      assert (S x ∈ Full nat). { apply Classifier1; auto. } apply H6 in H7. lia.
      assert (0%nat ∈ Full nat). { apply Classifier1; auto. } rewrite H5 in H6.
      applyClassifier1 H6. auto. }
    split; split; [split| |split| ]; auto; intros; destruct H2.
    + assert (a <= a0 \/ a0 < a) as [] by lra; auto.
      assert ((a-a0)/2 > 0). lra. pose proof H5. pose proof H5.
      apply H0 in H6. apply H3 in H7.
      assert (\{ λ u, f[u] ∈ U(a0; ((a-a0)/2)) \}
         ⊂ \{ λ u, f[u] ∉ U(a; ((a-a0)/2)) \}).
      { red; intros. applyClassifier1 H8. apply Classifier1. intro.
        applyClassifier1 H8. applyClassifier1 H9. apply Abs_R in H8,H9. lra. }
      elim H7. apply SubSetFinite in H8; auto.
    + assert (a0 <= a \/ a < a0) as [] by lra; auto.
      assert ((a0-a)/2 > 0). lra. pose proof H5. pose proof H5.
      apply H0 in H6. apply H3 in H7.
      assert (\{ λ u, f[u] ∈ U(a0; ((a0-a)/2)) \}
         ⊂ \{ λ u, f[u] ∉ U(a; ((a0-a)/2)) \}).
      { red; intros. applyClassifier1 H8. apply Classifier1. intro.
        applyClassifier1 H8. applyClassifier1 H9. apply Abs_R in H8,H9. lra. }
      elim H7. apply SubSetFinite in H8; auto.
  - destruct H as [[H[M]][[[]][[]]]]. apply EqualLimit. split; auto. intros.
    apply NNPP; intro. pose proof H8 as H8a.
    apply inFinite_to_Seq in H8 as [h[H8[H9[]]]].
    set (g := \{\ λ u v, v = f[h[u]] \}\). assert (IsSeq g).
    { split. red; intros. applyClassifier2 H12. applyClassifier2 H13.
      rewrite H12,H13; auto. apply AxiomI; split; intros. apply Classifier1; auto.
      apply Classifier1. exists (f[h[z]]). apply Classifier2; auto. }
    assert (BoundedSeq g).
    { split; auto. exists M. intros. unfold g. rewrite FunValue; auto. }
    pose proof H13. apply Theorem7_4a in H14 as [x[]].
    assert (Seq_Cluster_Point f x).
    { apply (Lemma7_6 f) in H14; auto. split; auto. split; auto.
      exists h. split; auto. split; auto. intros. unfold g.
      rewrite FunValue; auto. }
    assert (x = a). { pose proof H16. apply H3 in H16. apply H6 in H17. lra. }
    subst x. destruct H14. pose proof H7. apply H17 in H18.
    assert (\{ λ u, g[u] ∈ U(a; ε) \} = Empty nat).
    { apply AxiomI; split; intros. applyClassifier1 H19.
      unfold g in H19. rewrite FunValue in H19.
      assert (z ∈ dom[h]). { rewrite H9. apply Classifier1; auto. }
      apply x_fx_T in H20; auto.
      assert (h[z] ∈ ran[h]). { apply Classifier1; eauto. }
      rewrite H10 in H21. applyClassifier1 H21. elim H21; auto.
      applyClassifier1 H19. elim H19; auto. }
    rewrite H19 in H18. elim H18. right. auto.
Qed.

Theorem Theorem7_7a : ∀ f M, BoundedSeq f -> uplimit_seq f M
  <-> (∀ ε, ε > 0 -> (∃ N, (N > 0)%nat /\ (∀ n, (n > N)%nat -> f[n] < M + ε))
    /\ (∃ fs, SubSeq f fs /\ (∀ n, fs[n] > M - ε))).
Proof.
  split; intros.
  - destruct H0 as [[]]. pose proof H1. apply H2 in H4. pose proof H4.
    apply inFinite_to_Seq in H5 as [h[H5[H6[]]]].
    set (g := \{\ λ u v, v = f[h[u]] \}\).
    assert (SubSeq f g).
    { split; auto. split. split. red; intros. applyClassifier2 H9.
      applyClassifier2 H10. rewrite H9,H10; auto. apply AxiomI; split; intros.
      apply Classifier1; auto. apply Classifier1. exists f[h[z]].
      apply Classifier2; auto. exists h. split; auto. split; auto. intros.
      unfold g. rewrite FunValue; auto. }
    assert (Finite \{ λ u, (M + ε) <= f[u] \}).
    { apply NNPP; intro. pose proof H10.
      apply inFinite_to_Seq in H11 as [φ[H11[H12[]]]].
      set (g1 := \{\ λ u v, v = f[φ[u]] \}\).
      assert (IsSeq g1).
      { split. red; intros. applyClassifier2 H15. applyClassifier2 H16.
        rewrite H15,H16; auto. apply AxiomI; split; intros.
        apply Classifier1; auto. apply Classifier1.
        exists f[φ[z]]. apply Classifier2; auto. }
      assert (BoundedSeq g1).
      { split; auto. destruct H as [H[]]. exists x. intros.
        unfold g1. rewrite FunValue; auto. }
      apply Theorem7_4a in H16 as [x[H16 _]].
      assert (Seq_Cluster_Point f x).
      { apply (Lemma7_6 f) in H16; auto. split; auto. split; auto.
        exists φ. split; auto. split; auto. intros. unfold g1.
        rewrite FunValue; auto. }
      apply H3 in H17. destruct H16. pose proof H1. apply H18 in H19.
      assert (NotEmpty \{ λ u, g1[u] ∈ U(x; ε) \}) as [].
      { apply not_empty. intro. elim H19. right; auto. }
      applyClassifier1 H20. applyClassifier1 H20. apply Abs_R in H20.
      unfold g1 in H20. rewrite FunValue in H20.
      assert (φ[x0] ∈ ran[φ]).
      { apply Classifier1. exists x0. apply x_fx_T; auto.
        rewrite H12. apply Classifier1; auto. }
      rewrite H13 in H21. applyClassifier1 H21. lra. }
    split. destruct H10. apply finite_maxN in H10 as [x[]]. exists (S x).
    split. lia. intros. assert (f[n] < M + ε \/ M + ε <= f[n]) as [] by lra; auto.
    assert (n ∈ \{ λ u, M + ε <= f[u] \}). { apply Classifier1; auto. }
    apply H11 in H14. exfalso. lia. exists (1%nat). split. lia. intros.
    assert (f[n] < M + ε \/ M + ε <= f[n]) as [] by lra; auto.
    assert (n ∈ \{ λ u, M + ε <= f[u] \}). { apply Classifier1; auto. }
    rewrite H10 in H13. applyClassifier1 H13. elim H13; auto.
    exists g. split; auto. intros. unfold g. rewrite FunValue.
    assert (h[n] ∈ ran[h]).
    { apply Classifier1. exists n. apply x_fx_T; auto.
      rewrite H6. apply Classifier1; auto. }
    rewrite H7 in H11. applyClassifier1 H11. applyClassifier1 H11.
    apply Abs_R in H11. lra.
  - destruct H. split; [split; auto| ]; intros. pose proof H2.
    apply H0 in H3 as [[N[]][h[]]]. destruct H5 as [_[H5[φ[H7[]]]]].
    assert (Function1_1 φ).
    { destruct H7. split; auto. red; intros. applyClassifier2 H11.
      applyClassifier2 H12. assert (y = z \/ y < z \/ z < y)%nat. lia.
      destruct H13; auto.
      destruct H13; [apply (H10 y x z x) in H13|apply (H10 z x y x) in H13];
      auto; exfalso; lia. }
    assert (~ Finite ran[φ]).
    { apply (Infinite_equ_Infinite dom[φ] ran[φ] φ); auto. intro.
      rewrite H8 in H11. destruct H11. apply finite_maxN in H11 as [x[]].
      assert (S x ∈ Full nat). { apply Classifier1; auto. }
      apply H12 in H13. lia.
      assert (0%nat ∈ Full nat). { apply Classifier1; auto. }
      rewrite H11 in H12. applyClassifier1 H12; auto. }
    assert (~ Finite (ran[φ] ∩ \{ λ u, (u > N)%nat \})).
    { intro. assert (ran[φ] ⊂  (ran[φ] ∩ \{ λ u, (u > N)%nat \})
         ∪ \{ λ u, (u <= S N)%nat \}).
      { red; intros. apply Classifier1. destruct (classic (z > N)%nat);
        [left; apply Classifier1; split; auto|right]; apply Classifier1; lia. }
      apply SubSetFinite in H13; auto. apply Finite_union_Finite; auto.
      left. apply NatFinite. }
    assert ((ran[φ] ∩ \{ λ u, (u > N)%nat \}) ⊂ \{ λ u, f[u] ∈ U(M; ε) \}).
    { red; intros. applyClassifier1 H13. destruct H13. applyClassifier1 H14.
      apply Classifier1. applyClassifier1 H13. destruct H13. destruct H7.
      apply f_x_T in H13; auto. apply Classifier1. apply Abs_R.
      apply H4 in H14. split. rewrite <-H13,<-H9. pose proof (H6 x). lra. lra. }
    intro. apply SubSetFinite in H13; auto.
    assert (a <= M \/ M < a) as [] by lra; auto.
    set (ε := (a - M)/2). assert (0 < ε). unfold ε. lra.
    pose proof H4. apply H0 in H5 as [[N[]]_]. destruct H2.
    pose proof H4. apply H7 in H8.
    assert (\{ λ u, f[u] ∈ U(a; ε) \} ⊂ \{ λ u, (u <= N)%nat \}).
    { red; intros. applyClassifier1 H9. apply Classifier1.
      assert (z <= N \/ N < z)%nat as [] by lia; auto.
      apply H6 in H10. applyClassifier1 H9. apply Abs_R in H9.
      unfold ε in H9,H10. exfalso. lra. }
    apply SubSetFinite in H9. elim H8; auto. left. apply NatFinite.
Qed.

Theorem Theorem7_7b : ∀ f m, BoundedSeq f -> lowlimit_seq f m
  <-> (∀ ε, ε > 0 -> (∃ N, (N > 0)%nat /\ (∀ n, (n > N)%nat -> f[n] > m - ε))
    /\ (∃ fs, SubSeq f fs /\ (∀ n, fs[n] < m + ε))).
Proof.
  split; intros.
  - destruct H0 as [[]]. pose proof H1. apply H2 in H4. pose proof H4.
    apply inFinite_to_Seq in H5 as [h[H5[H6[]]]].
    set (g := \{\ λ u v, v = f[h[u]] \}\).
    assert (SubSeq f g).
    { split; auto. split. split. red; intros. applyClassifier2 H9.
      applyClassifier2 H10. rewrite H9,H10; auto. apply AxiomI; split; intros.
      apply Classifier1; auto. apply Classifier1. exists f[h[z]].
      apply Classifier2; auto. exists h. split; auto. split; auto.
      intros. unfold g. rewrite FunValue; auto. }
    assert (Finite \{ λ u, f[u] <= (m - ε) \}).
    { apply NNPP; intro. pose proof H10.
      apply inFinite_to_Seq in H11 as [φ[H11[H12[]]]].
      set (g1 := \{\ λ u v, v = f[φ[u]] \}\).
      assert (IsSeq g1).
      { split. red; intros. applyClassifier2 H15. applyClassifier2 H16.
        rewrite H15,H16; auto. apply AxiomI; split; intros.
        apply Classifier1; auto. apply Classifier1. exists f[φ[z]].
        apply Classifier2; auto. }
      assert (BoundedSeq g1).
      { split; auto. destruct H as [H[]]. exists x. intros.
        unfold g1. rewrite FunValue; auto. }
      apply Theorem7_4a in H16 as [x[H16 _]].
      assert (Seq_Cluster_Point f x).
      { apply (Lemma7_6 f) in H16; auto. split; auto. split; auto.
        exists φ. split; auto. split; auto. intros. unfold g1.
        rewrite FunValue; auto. }
      apply H3 in H17. destruct H16. pose proof H1. apply H18 in H19.
      assert (NotEmpty \{ λ u, g1[u] ∈ U(x; ε) \}) as [].
      { apply not_empty. intro. elim H19. right; auto. }
      applyClassifier1 H20. applyClassifier1 H20. apply Abs_R in H20.
      unfold g1 in H20. rewrite FunValue in H20.
      assert (φ[x0] ∈ ran[φ]).
      { apply Classifier1. exists x0. apply x_fx_T; auto.
        rewrite H12. apply Classifier1; auto. }
      rewrite H13 in H21. applyClassifier1 H21. lra. }
    split. destruct H10. apply finite_maxN in H10 as [x[]]. exists (S x).
    split. lia. intros. assert (f[n] > m - ε \/ f[n] <= m - ε) as [] by lra; auto.
    assert (n ∈ \{ λ u, f[u] <= m - ε \}). { apply Classifier1; auto. }
    apply H11 in H14. exfalso. lia. exists (1%nat). split. lia. intros.
    assert (f[n] > m - ε \/ f[n] <= m - ε) as [] by lra; auto.
    assert (n ∈ \{ λ u, f[u] <= m - ε \}). { apply Classifier1; auto. }
    rewrite H10 in H13. applyClassifier1 H13. elim H13; auto.
    exists g. split; auto. intros. unfold g. rewrite FunValue.
    assert (h[n] ∈ ran[h]).
    { apply Classifier1. exists n. apply x_fx_T; auto.
      rewrite H6. apply Classifier1; auto. }
    rewrite H7 in H11. applyClassifier1 H11. applyClassifier1 H11.
    apply Abs_R in H11. lra.
  - destruct H. split; [split; auto| ]; intros. pose proof H2.
    apply H0 in H3 as [[N[]][h[]]]. destruct H5 as [_[H5[φ[H7[]]]]].
    assert (Function1_1 φ).
    { destruct H7. split; auto. red; intros. applyClassifier2 H11.
      applyClassifier2 H12. assert (y = z \/ y < z \/ z < y)%nat. lia.
      destruct H13; auto.
      destruct H13; [apply (H10 y x z x) in H13|apply (H10 z x y x) in H13];
      auto; exfalso; lia. }
    assert (~ Finite ran[φ]).
    { apply (Infinite_equ_Infinite dom[φ] ran[φ] φ); auto. intro.
      rewrite H8 in H11. destruct H11. apply finite_maxN in H11 as [x[]].
      assert (S x ∈ Full nat). { apply Classifier1; auto. } apply H12 in H13. lia.
      assert (0%nat ∈ Full nat). { apply Classifier1; auto. }
      rewrite H11 in H12. applyClassifier1 H12; auto. }
    assert (~ Finite (ran[φ] ∩ \{ λ u, (u > N)%nat \})).
    { intro. assert (ran[φ] ⊂  (ran[φ] ∩ \{ λ u, (u > N)%nat \})
         ∪ \{ λ u, (u <= S N)%nat \}).
      { red; intros. apply Classifier1. destruct (classic (z > N)%nat);
        [left; apply Classifier1; split; auto|right]; apply Classifier1; lia. }
      apply SubSetFinite in H13; auto. apply Finite_union_Finite; auto.
      left. apply NatFinite. }
    assert ((ran[φ] ∩ \{ λ u, (u > N)%nat \}) ⊂ \{ λ u, f[u] ∈ U(m; ε) \}).
    { red; intros. applyClassifier1 H13. destruct H13. applyClassifier1 H14.
      apply Classifier1. applyClassifier1 H13. destruct H13. destruct H7.
      apply f_x_T in H13; auto. apply Classifier1. apply Abs_R.
      apply H4 in H14. split. lra. rewrite <-H13,<-H9. pose proof (H6 x). lra. }
    intro. apply SubSetFinite in H13; auto.
    assert (m <= a \/ a < m) as [] by lra; auto.
    set (ε := (m - a)/2). assert (0 < ε). unfold ε. lra.
    pose proof H4. apply H0 in H5 as [[N[]]_]. destruct H2.
    pose proof H4. apply H7 in H8.
    assert (\{ λ u, f[u] ∈ U(a; ε) \} ⊂ \{ λ u, (u <= N)%nat \}).
    { red; intros. applyClassifier1 H9. apply Classifier1.
      assert (z <= N \/ N < z)%nat as [] by lia; auto.
      apply H6 in H10. applyClassifier1 H9. apply Abs_R in H9.
      unfold ε in H9,H10. exfalso. lra. }
    apply SubSetFinite in H9. elim H8; auto. left. apply NatFinite.
Qed.

Theorem Theorem7_7'a : ∀ f M, BoundedSeq f -> uplimit_seq f M
  <-> ((∀ α, α > M -> Finite \{ λ u, f[u] > α \})
    /\ (∀ β, β < M -> ~ Finite \{ λ u, f[u] > β \})).
Proof.
  split; intros.
  - destruct (Theorem7_7a f M H) as [H1 _]. pose proof (H1 H0). clear H1.
    split; intros. assert (α - M > 0) by lra. pose proof H3.
    apply H2 in H4 as [[N[]]_].
    assert (\{ λ u, f[u] > α \} ⊂ \{ λ u, (u <= N)%nat \}).
    { red; intros. applyClassifier1 H6. apply Classifier1.
      assert (N < z \/ z <= N)%nat as [] by lia; auto.
      apply H5 in H7. exfalso. lra. }
    apply SubSetFinite in H6; auto. left. apply NatFinite.
    assert (M - β > 0) by lra. pose proof H3.
    apply H2 in H4 as [_[g[[H4[H5[h[H6[]]]]]]]].
    assert (ran[h] ⊂ \{ λ u, f[u] > β \}).
    { red; intros. applyClassifier1 H10. destruct H10. destruct H6.
      apply f_x_T in H10; auto. apply Classifier1. pose proof (H9 x).
      rewrite H8,H10 in H12. lra. }
    assert (~ Finite ran[h]).
    { apply (Infinite_equ_Infinite dom[h] ran[h] h); auto.
      destruct H6. split; auto. red; intros.
      applyClassifier2 H12. applyClassifier2 H13.
      assert (y = z \/ y < z \/ z < y)%nat. lia. destruct H14; auto.
      destruct H14; [apply (H11 y x z x) in H14|apply (H11 z x y x) in H14];
      auto; exfalso; lia. intro. rewrite H7 in H11. destruct H11.
      apply finite_maxN in H11 as [x[]].
      assert (S x ∈ Full nat). { apply Classifier1; auto. }
      apply H12 in H13. lia.
      assert (0%nat ∈ Full nat). { apply Classifier1; auto. }
      rewrite H11 in H12. applyClassifier1 H12; auto. }
    intro. apply SubSetFinite in H10; auto.
  - destruct H,H0. split; [split; auto| ]; intros.
    assert (M - ε < M < M + ε) as [] by lra. pose proof H4. pose proof H5.
    apply H2 in H6. apply H0 in H7.
    assert (~ Finite (\{ λ u, f[u] > M - ε \} — \{ λ u, f[u] >= M + ε \})).
    { intro. assert (\{ λ u, f[u] > M - ε \} ⊂ (\{ λ u, f[u] > M - ε \}
        — \{ λ u, f[u] >= M + ε \}) ∪ \{ λ u, f[u] >= M + ε \}).
      { red; intros. apply Classifier1.
        destruct (classic (z ∈ (\{ λ u, f[u] >= M + ε \}))); [right|left]; auto;
        apply Classifier1; split; auto. }
      apply SubSetFinite in H9; auto. apply Finite_union_Finite; auto.
      assert (\{ λ u, f[u] >= M + ε \} ⊂ \{ λ u, f[u] > M + ε/2 \}).
      { red; intros. applyClassifier1 H10. apply Classifier1. lra. }
      apply SubSetFinite in H10; auto. apply H0. lra. }
    assert ((\{ λ u, f[u] > M - ε \} — \{ λ u, f[u] >= M + ε \})
       ⊂ \{ λ u, f[u] ∈ U(M; ε) \}).
    { red; intros. applyClassifier1 H9. destruct H9. applyClassifier1 H10.
      apply Classifier1. applyClassifier1 H9. apply Classifier1.
      apply Abs_R. split. lra.
      assert (f[z] < M + ε \/ f[z] >= M + ε) as [] by lra. lra.
      elim H10. apply Classifier1; auto. }
    intro. apply SubSetFinite in H9; auto.
    destruct H3. assert (a <= M \/ M < a) as [] by lra; auto.
    assert ((a - M)/2 > 0) by lra. pose proof H6. apply H4 in H7.
    assert (M + (a-M)/2 > M) by lra. apply H0 in H8. elim H7.
    assert (\{ λ u, f[u] ∈ U(a; ((a-M)/2)) \} ⊂ \{ λ u, f[u] > M + (a-M)/2 \}).
    { red; intros. applyClassifier1 H9. apply Classifier1. applyClassifier1 H9.
      apply Abs_R in H9. lra. }
    apply SubSetFinite in H9; auto.
Qed.

Theorem Theorem7_7'b : ∀ f m, BoundedSeq f -> lowlimit_seq f m
  <-> ((∀ β, β < m -> Finite \{ λ u, f[u] < β \})
    /\ (∀ α, α > m -> ~ Finite \{ λ u, f[u] < α \})).
Proof.
  split; intros.
  - destruct (Theorem7_7b f m H) as [H1 _]. pose proof (H1 H0). clear H1.
    split; intros. assert (m - β > 0) by lra. pose proof H3.
    apply H2 in H4 as [[N[]]_].
    assert (\{ λ u, f[u] < β \} ⊂ \{ λ u, (u <= N)%nat \}).
    { red; intros. applyClassifier1 H6. apply Classifier1.
      assert (N < z \/ z <= N)%nat as [] by lia; auto.
      apply H5 in H7. exfalso. lra. }
    apply SubSetFinite in H6; auto. left. apply NatFinite.
    assert (α - m > 0) by lra. pose proof H3.
    apply H2 in H4 as [_[g[[H4[H5[h[H6[]]]]]]]].
    assert (ran[h] ⊂ \{ λ u, f[u] < α \}).
    { red; intros. applyClassifier1 H10. destruct H10. destruct H6.
      apply f_x_T in H10; auto. apply Classifier1. pose proof (H9 x).
      rewrite H8,H10 in H12. lra. }
    assert (~ Finite ran[h]).
    { apply (Infinite_equ_Infinite dom[h] ran[h] h); auto.
      destruct H6. split; auto. red; intros. applyClassifier2 H12.
      applyClassifier2 H13.
      assert (y = z \/ y < z \/ z < y)%nat. lia. destruct H14; auto.
      destruct H14; [apply (H11 y x z x) in H14|apply (H11 z x y x) in H14];
      auto; exfalso; lia. intro. rewrite H7 in H11. destruct H11.
      apply finite_maxN in H11 as [x[]].
      assert (S x ∈ Full nat). { apply Classifier1; auto. }
      apply H12 in H13. lia.
      assert (0%nat ∈ Full nat). { apply Classifier1; auto. }
      rewrite H11 in H12. applyClassifier1 H12; auto. }
    intro. apply SubSetFinite in H10; auto.
  - destruct H,H0. split; [split; auto| ]; intros.
    assert (m - ε < m < m + ε) as [] by lra. pose proof H4. pose proof H5.
    apply H2 in H7. apply H0 in H6.
    assert (~ Finite (\{ λ u, f[u] < m + ε \} — \{ λ u, f[u] <= m - ε \})).
    { intro. assert (\{ λ u, f[u] < m + ε \} ⊂ (\{ λ u, f[u] < m + ε \}
        — \{ λ u, f[u] <= m - ε \}) ∪ \{ λ u, f[u] <= m - ε \}).
      { red; intros. apply Classifier1.
        destruct (classic (z ∈ (\{ λ u, f[u] <= m - ε \}))); [right|left]; auto;
        apply Classifier1; split; auto. }
      apply SubSetFinite in H9; auto. apply Finite_union_Finite; auto.
      assert (\{ λ u, f[u] <= m - ε \} ⊂ \{ λ u, f[u] < m - ε/2 \}).
      { red; intros. applyClassifier1 H10. apply Classifier1. lra. }
      apply SubSetFinite in H10; auto. apply H0. lra. }
    assert ((\{ λ u, f[u] < m + ε \} — \{ λ u, f[u] <= m - ε \})
       ⊂ \{ λ u, f[u] ∈ U(m; ε) \}).
    { red; intros. applyClassifier1 H9. destruct H9. applyClassifier1 H10.
      apply Classifier1. applyClassifier1 H9. apply Classifier1. apply Abs_R.
      split. assert (f[z] <= m - ε \/ f[z] > m - ε) as [] by lra. elim H10.
      apply Classifier1; auto. lra. lra. }
    intro. apply SubSetFinite in H9; auto.
    destruct H3. assert (m <= a \/ a < m) as [] by lra; auto.
    assert ((m - a)/2 > 0) by lra. pose proof H6. apply H4 in H7.
    assert (m - ((m-a)/2) < m) by lra. apply H0 in H8. elim H7.
    assert (\{ λ u, f[u] ∈ U(a; ((m-a)/2)) \} ⊂ \{ λ u, f[u] < m - (m-a)/2 \}).
    { red; intros. applyClassifier1 H9. apply Classifier1. applyClassifier1 H9.
      apply Abs_R in H9. lra. }
    apply SubSetFinite in H9; auto.
Qed.

(* 无限集 ∩ 大于N的所有自然数集 还是 无限集 *)
Lemma Lemma7_8 : ∀ A N, ~ Finite A -> ~ Finite (A ∩ \{ λ u, (N < u)%nat \}).
Proof.
  intros. intro. destruct H0.
  - apply finite_maxN in H0 as [x[]].
    assert (A ⊂ \{ λ u, (u <= x)%nat \}).
    { red; intros. apply Classifier1.
      assert (z <= x \/ x < z)%nat as [] by lia; auto.
      assert (z ∈ (A ∩ \{ λ u, (N < u)%nat \})).
      { applyClassifier1 H0. destruct H0. apply Classifier1. split; auto.
        apply Classifier1. applyClassifier1 H4. lia. }
      apply H1 in H4. exfalso. lia. }
    apply SubSetFinite in H2; auto. left. apply NatFinite.
  - assert (A ⊂ \{ λ u, (u <= N)%nat \}).
    { red; intros. apply Classifier1.
      assert (z <= N \/ N < z)%nat as [] by lia; auto.
      assert (z ∈ Empty nat).
      { rewrite <-H0. apply Classifier1; split; auto. }
      applyClassifier1 H3. elim H3; auto. }
    apply SubSetFinite in H1; auto. left. apply NatFinite.
Qed.

Theorem Theorem7_8a : ∀ f g Mf Mg, BoundedSeq f -> BoundedSeq g
  -> (∃ N0, (N0 > 0)%nat /\ (∀ n, (n > N0)%nat -> f[n] < g[n]))
  -> uplimit_seq f Mf -> uplimit_seq g Mg -> Mf <= Mg.
Proof.
  intros. destruct H1 as [N[]]. assert (Mf <= Mg \/ Mg < Mf) as [] by lra; auto.
  destruct (Theorem7_7'a f Mf H) as [H6 _], (Theorem7_7'a g Mg H0) as [H7 _].
  destruct (H6 H2), (H7 H3). clear H6 H7. set (ε := (Mf + Mg)/2).
  assert (Mg < ε < Mf) as [] by (unfold ε; lra).
  assert (~ Finite (\{ λ u, f[u] > ε \} ∩ \{ λ u, (u > N)%nat \})).
  { apply Lemma7_8; auto. }
  apply H10 in H6. elim H12.
  assert ((\{ λ u, f[u] > ε \} ∩ \{ λ u, (u > N)%nat \}) ⊂ \{ λ u, g[u] > ε \}).
  { red; intros. applyClassifier1 H13. destruct H13. applyClassifier1 H13.
    applyClassifier1 H14. apply Classifier1. apply H4 in H14. lra. }
  apply SubSetFinite in H13; auto.
Qed.

Theorem Theorem7_8b : ∀ f g mf mg, BoundedSeq f -> BoundedSeq g
  -> (∃ N0, (N0 > 0)%nat /\ (∀ n, (n > N0)%nat -> f[n] <= g[n]))
  -> lowlimit_seq f mf -> lowlimit_seq g mg -> mf <= mg.
Proof.
  intros. destruct H1 as [N[]]. assert (mf <= mg \/ mg < mf) as [] by lra; auto.
  destruct (Theorem7_7'b f mf H) as [H6 _], (Theorem7_7'b g mg H0) as [H7 _].
  destruct (H6 H2), (H7 H3). clear H6 H7. set (ε := (mf + mg)/2).
  assert (mg < ε < mf) as [] by (unfold ε; lra).
  assert (~ Finite (\{ λ u, g[u] < ε \} ∩ \{ λ u, (u > N)%nat \})).
  { apply Lemma7_8; auto. }
  apply H8 in H7. elim H12.
  assert ((\{ λ u, g[u] < ε \} ∩ \{ λ u, (u > N)%nat \}) ⊂ \{ λ u, f[u] < ε \}).
  { red; intros. applyClassifier1 H13. destruct H13. applyClassifier1 H13.
    applyClassifier1 H14. apply Classifier1. apply H4 in H14. lra. }
  apply SubSetFinite in H13; auto.
Qed.

Theorem Theorem7_8c : ∀ f α β Mf mf, BoundedSeq f
  -> (∃ N0, (N0 > 0)%nat /\ (∀ n, (n > N0)%nat -> α <= f[n] < β))
  -> uplimit_seq f Mf -> lowlimit_seq f mf
  -> α <= mf /\ mf <= Mf /\ Mf <= β.
Proof.
  intros. destruct H0 as [N[]].
  destruct (Theorem7_7'a f Mf), (Theorem7_7'b f mf); auto.
  apply H4 in H1 as []. apply H6 in H2 as []. clear H4 H5 H6 H7.
  assert (~ mf < α).
  { intro. apply H9 in H4. elim H4.
    assert (\{ λ u, f[u] < α \} ⊂ \{ λ u, (u <= N)%nat \}).
    { red; intros. applyClassifier1 H5. apply Classifier1.
      assert (z <= N \/ N < z)%nat as [] by lia; auto.
      apply H3 in H6. exfalso. lra. }
    apply SubSetFinite in H5; auto. left. apply NatFinite. }
  assert (~ β < Mf).
  { intro. apply H8 in H5. elim H5.
    assert (\{ λ u, f[u] > β \} ⊂ \{ λ u, (u <= N)%nat \}).
    { red; intros. applyClassifier1 H6. apply Classifier1.
      assert (z <= N \/ N < z)%nat as [] by lia; auto.
      apply H3 in H7. exfalso. lra. }
    apply SubSetFinite in H6; auto. left. apply NatFinite. }
  split. lra. split. apply (Theorem7_5 f). apply Theorem7_7'b; auto.
  apply Theorem7_7'a; auto. lra.
Qed.

Theorem Theorem7_9a : ∀ f Mf, BoundedSeq f -> uplimit_seq f Mf
  <-> limit_seq (\{\ λ u v, sup \{ λ w, ∃ m, (u <= m)%nat /\ w = f[m] \} v \}\) Mf.
Proof.
  intros.
  set (h := \{\ λ u v, sup \{ λ w, ∃ m, (u <= m)%nat /\ w = f[m] \} v \}\).
  assert (IsSeq h).
  { split. red; intros. applyClassifier2 H0. applyClassifier2 H1.
    destruct H0,H1. assert (y = z \/ y < z \/ z < y) by lra.
    destruct H4; auto. destruct H4. apply H3 in H4 as [x0[]].
    apply H0 in H4. exfalso. lra. apply H2 in H4 as [x0[]]. apply H1 in H4.
    exfalso. lra. apply AxiomI; split; intros. apply Classifier1; auto.
    apply Classifier1. assert (NotEmpty \{ λ w, ∃ m, (z <= m)%nat /\ w = f[m] \}).
    { exists f[z]. apply Classifier1. exists z. auto. }
    assert (∃ M, Upper \{ λ w, ∃ m, (z <= m)%nat /\ w = f[m] \} M).
    { destruct H as [H[M]]. exists M. red; intros. applyClassifier1 H3.
      destruct H3 as [k[]]. rewrite H4. pose proof (H2 k).
      apply Abs_le_R in H5. lra. }
    apply Sup_inf_principle in H1 as []. apply H1 in H2 as []. exists x.
    apply Classifier2; auto. }
  assert (∀ m, sup \{ λ w,∃ k, (m <= k)%nat /\ w = f[k] \} h[m]).
  { intros. assert ([m,h[m]] ∈ h).
    { destruct H0. apply x_fx_T; auto. rewrite H1. apply Classifier1; auto. }
    applyClassifier2 H1; auto. }
  assert (DecreaseSeq h).
  { split; auto. intros. destruct (H1 (S n)).
    assert (h[n] >= h[S n] \/ h[n] < h[S n]) as [] by lra; auto.
    pose proof H4. apply H3 in H5 as [x[]]. applyClassifier1 H5.
    destruct H5 as [k[]]. destruct (H1 n).
    assert (f[k] ∈ \{ λ u, ∃ w, (n <= w)%nat /\ u = f[w] \}).
    { apply Classifier1. exists k. split; auto. lia. }
    apply H8 in H10. rewrite H7 in H6. exfalso. lra. }
  assert (∀ n, f[n] <= h[n]).
  { intros. destruct (H1 n). apply H3. apply Classifier1. exists n. split; auto. }
  assert (BoundedSeq h).
  { split; auto. destruct H as [H[M]]. exists M. intros. apply Abs_le_R.
    destruct (H1 n). split. pose proof (H4 n). apply Abs_le_R in H7.
    pose proof (H3 n). lra.
    assert (h[n] <= M \/ M < h[n]) as [] by lra; auto. pose proof H7.
    apply H6 in H8 as [x[]]. applyClassifier1 H8. destruct H8 as [k[]].
    rewrite H10 in H9. pose proof (H4 k). apply Abs_le_R in H11. exfalso. lra. }
  assert (∀ r, ~ Finite \{ λ u, h[u] > r \} -> ~ Finite \{ λ u, f[u] > r \}).
  { intros. intro. pose proof H6 as [].
    - apply finite_maxN in H7 as [N[]].
      assert (∀ m, (m > N)%nat -> f[m] <= r).
      { intros. assert (f[m] <= r \/ r < f[m]) as [] by lra; auto.
        assert (m ∈ \{ λ u, f[u] > r \}). { apply Classifier1; auto. }
        apply H8 in H11. exfalso. lia. }
      assert (∀ m, (m > N)%nat -> h[m] <= r).
      { intros. destruct (H1 m).
        assert (h[m] <= r \/ r < h[m]) as [] by lra; auto.
        pose proof H13. apply H12 in H14 as [y[]]. applyClassifier1 H14.
        destruct H14 as [k[]]. subst y. assert (k > N)%nat by lia.
        apply H9 in H16. exfalso. lra. }
      assert (\{ λ u, h[u] > r \} ⊂ \{ λ u, (u <= N)%nat \}).
      { red; intros. applyClassifier1 H11. apply Classifier1.
        assert (z <= N \/ N < z)%nat as [] by lia; auto.
        apply H10 in H12. exfalso. lra. }
      apply SubSetFinite in H11; auto. left. apply NatFinite.
    - assert (∀ m, f[m] <= r).
      { intros. assert (f[m] <= r \/ r < f[m]) as [] by lra; auto.
        assert (m ∈ Empty nat). { rewrite <-H7. apply Classifier1; auto. }
        applyClassifier1 H9. elim H9; auto. }
      assert (∀ m, h[m] <= r).
      { intros. assert (h[m] <= r \/ r < h[m]) as [] by lra; auto.
        destruct (H1 m). pose proof H9. apply H11 in H12 as [y[]].
        applyClassifier1 H12. destruct H12 as [k[]]. subst y.
        pose proof (H8 k). exfalso. lra. }
      elim H5. right. apply AxiomI; split; intros. applyClassifier1 H10.
      pose proof (H9 z). exfalso. lra. applyClassifier1 H10. elim H10; auto. }
  assert (Convergence h) as [hl]. { apply Theorem2_9; auto. red; auto. }
  split; intros.
  - pose proof H6. apply EqualLimit in H8 as [].
    assert (Mf = hl \/ Mf < hl \/ hl < Mf) by lra.
    destruct H10. rewrite H10; auto. destruct (Theorem7_7'a f Mf H).
    destruct (H11 H7). clear H11 H12. destruct H10.
    + set (ε := (hl - Mf)/2). assert (ε > 0) by (unfold ε; lra).
      assert (~ Finite \{ λ u, h[u] > Mf + ε \}).
      { assert (\{ λ u, h[u] ∈ U(hl; ε) \} ⊂ \{ λ u, h[u] > Mf + ε \}).
        { red; intros. applyClassifier1 H12.
          apply Classifier1. applyClassifier1 H12.
          apply Abs_R in H12. unfold ε in H12. unfold ε. lra. }
        intro. apply SubSetFinite in H12; auto. apply H9 in H11.
        assert (\{ λ u, h[u] ∈ U(hl; ε) \} ∪ \{ λ u, h[u] ∉ U(hl; ε) \}
          = Full nat).
        { apply AxiomI; split; intros. apply Classifier1; auto.
          apply Classifier1. destruct (classic (h[z] ∈ U(hl; ε)));
          [left|right]; apply Classifier1; auto. }
        assert (Finite (Full nat)) as [].
        { rewrite <-H16. apply Finite_union_Finite; auto. }
        apply finite_maxN in H17 as [N[]].
        assert (S N ∈ Full nat) by (apply Classifier1; auto).
        apply H18 in H19. lia.
        assert (0%nat ∈ Full nat) by (apply Classifier1; auto).
        rewrite H17 in H18. applyClassifier1 H18; auto. }
      apply H5 in H12. elim H12. apply H13. lra.
    + set (ε := (Mf - hl)/2). assert (ε > 0) by (unfold ε; lra).
      pose proof H11. apply H9 in H12.
      assert (hl + ε < Mf) by (unfold ε; lra). apply H14 in H15.
      assert (\{ λ u, h[u] > hl + ε \} ⊂ \{ λ u, h[u] ∉ U(hl; ε) \}).
      { red; intros. applyClassifier1 H16. apply Classifier1.
        intro. applyClassifier1 H17. apply Abs_R in H17. lra. }
      apply SubSetFinite in H16; auto. elim H15.
      assert (\{ λ u, f[u] > hl + ε \} ⊂ \{ λ u, h[u] > hl + ε \}).
      { red; intros. applyClassifier1 H17. apply Classifier1.
        pose proof (H3 z). lra. }
      apply SubSetFinite in H17; auto.
  - apply Theorem7_7'a; auto. pose proof H7. apply EqualLimit in H8 as [].
    split; intros.
    + assert (α - Mf > 0) by lra. apply H9 in H11.
      assert (\{ λ u, h[u] > α \} ⊂ \{ λ u, h[u] ∉ U(Mf; (α - Mf)) \}).
      { red; intros. applyClassifier1 H12. apply Classifier1. intro.
        applyClassifier1 H13. apply Abs_R in H13. lra. }
      apply SubSetFinite in H12; auto.
      assert (\{ λ u, f[u] > α \} ⊂ \{ λ u, h[u] > α \}).
      { red; intros. applyClassifier1 H13. apply Classifier1.
        pose proof (H3 z). lra. }
      apply SubSetFinite in H13; auto.
    + apply H5. assert (\{ λ u, h[u] ∈ U(Mf; (Mf - β)) \} ⊂ \{ λ u, h[u] > β \}).
      { red; intros. applyClassifier1 H11. apply Classifier1. applyClassifier1 H11.
        apply Abs_R in H11. lra. }
      assert (~ Finite (\{ λ u, h[u] ∈ U(Mf; (Mf - β)) \})).
      { intro. assert (Mf - β > 0). lra. apply H9 in H13.
        assert (\{ λ u, h[u] ∈ U(Mf; (Mf - β)) \}
            ∪ \{ λ u, h[u] ∉ U(Mf; (Mf - β)) \} = Full nat).
        { apply AxiomI; split; intros. apply Classifier1; auto.
          apply Classifier1. destruct (classic (h[z] ∈ U(Mf; (Mf - β))));
          [left|right]; apply Classifier1; auto. }
        assert (Finite (Full nat)) as [].
        { rewrite <-H14. apply Finite_union_Finite; auto. }
        apply finite_maxN in H15 as [N[]].
        assert (S N ∈ Full nat) by (apply Classifier1; auto).
        apply H16 in H17. lia.
        assert (0%nat ∈ Full nat) by (apply Classifier1; auto).
        rewrite H15 in H16. applyClassifier1 H16; auto. }
      intro. apply SubSetFinite in H11; auto.
Qed.

Theorem Theorem7_9b : ∀ f mf, BoundedSeq f -> lowlimit_seq f mf
  <-> limit_seq (\{\ λ u v, inf \{ λ w, ∃ m, (u <= m)%nat /\ w = f[m] \} v \}\) mf.
Proof.
  intros.
  set (h := \{\ λ u v, inf \{ λ w, ∃ m, (u <= m)%nat /\ w = f[m] \} v \}\).
  assert (IsSeq h).
  { split. red; intros. applyClassifier2 H0. applyClassifier2 H1.
    destruct H0,H1. assert (y = z \/ z < y \/ y < z) by lra.
    destruct H4; auto. destruct H4. apply H3 in H4 as [x0[]].
    apply H0 in H4. exfalso. lra. apply H2 in H4 as [x0[]]. apply H1 in H4.
    exfalso. lra. apply AxiomI; split; intros. apply Classifier1; auto.
    apply Classifier1. assert (NotEmpty \{ λ w, ∃ m, (z <= m)%nat /\ w = f[m] \}).
    { exists f[z]. apply Classifier1. exists z. auto. }
    assert (∃ M, Lower \{ λ w, ∃ m, (z <= m)%nat /\ w = f[m] \} M).
    { destruct H as [H[M]]. exists (-M). red; intros. applyClassifier1 H3.
      destruct H3 as [k[]]. rewrite H4. pose proof (H2 k).
      apply Abs_le_R in H5. lra. }
    apply Sup_inf_principle in H1 as []. apply H3 in H2 as []. exists x.
    apply Classifier2; auto. }
  assert (∀ m, inf \{ λ w,∃ k, (m <= k)%nat /\ w = f[k] \} h[m]).
  { intros. assert ([m,h[m]] ∈ h).
    { destruct H0. apply x_fx_T; auto. rewrite H1. apply Classifier1; auto. }
    applyClassifier2 H1; auto. }
  assert (IncreaseSeq h).
  { split; auto. intros. destruct (H1 (S n)).
    assert (h[n] <= h[S n] \/ h[n] > h[S n]) as [] by lra; auto.
    pose proof H4. apply H3 in H5 as [x[]]. applyClassifier1 H5.
    destruct H5 as [k[]]. destruct (H1 n).
    assert (f[k] ∈ \{ λ u, ∃ w, (n <= w)%nat /\ u = f[w] \}).
    { apply Classifier1. exists k. split; auto. lia. }
    apply H8 in H10. rewrite H7 in H6. exfalso. lra. }
  assert (∀ n, f[n] >= h[n]).
  { intros. destruct (H1 n). apply H3. apply Classifier1.
    exists n. split; auto. }
  assert (BoundedSeq h).
  { split; auto. destruct H as [H[M]]. exists M. intros. apply Abs_le_R.
    destruct (H1 n). split.
    assert (-M <= h[n] \/ h[n] < -M) as [] by lra; auto. pose proof H7.
    apply H6 in H8 as [x[]]. applyClassifier1 H8. destruct H8 as [k[]].
    rewrite H10 in H9. pose proof (H4 k). apply Abs_le_R in H11. exfalso. lra.
    pose proof (H4 n). apply Abs_le_R in H7. pose proof (H3 n). lra. }
  assert (∀ r, ~ Finite \{ λ u, h[u] < r \} -> ~ Finite \{ λ u, f[u] < r \}).
  { intros. intro. pose proof H6 as [].
    - apply finite_maxN in H7 as [N[]].
      assert (∀ m, (m > N)%nat -> f[m] >= r).
      { intros. assert (f[m] >= r \/ r > f[m]) as [] by lra; auto.
        assert (m ∈ \{ λ u, f[u] < r \}). { apply Classifier1; auto. }
        apply H8 in H11. exfalso. lia. }
      assert (∀ m, (m > N)%nat -> h[m] >= r).
      { intros. destruct (H1 m).
        assert (h[m] >= r \/ r > h[m]) as [] by lra; auto.
        pose proof H13. apply H12 in H14 as [y[]]. applyClassifier1 H14.
        destruct H14 as [k[]]. subst y. assert (k > N)%nat by lia.
        apply H9 in H16. exfalso. lra. }
      assert (\{ λ u, h[u] < r \} ⊂ \{ λ u, (u <= N)%nat \}).
      { red; intros. applyClassifier1 H11. apply Classifier1.
        assert (z <= N \/ N < z)%nat as [] by lia; auto.
        apply H10 in H12. exfalso. lra. }
      apply SubSetFinite in H11; auto. left. apply NatFinite.
    - assert (∀ m, f[m] >= r).
      { intros. assert (f[m] >= r \/ r > f[m]) as [] by lra; auto.
        assert (m ∈ Empty nat). { rewrite <-H7. apply Classifier1; auto. }
        applyClassifier1 H9. elim H9; auto. }
      assert (∀ m, h[m] >= r).
      { intros. assert (h[m] >= r \/ r > h[m]) as [] by lra; auto.
        destruct (H1 m). pose proof H9. apply H11 in H12 as [y[]].
        applyClassifier1 H12. destruct H12 as [k[]]. subst y.
        pose proof (H8 k). exfalso. lra. }
      elim H5. right. apply AxiomI; split; intros. applyClassifier1 H10.
      pose proof (H9 z). exfalso. lra. applyClassifier1 H10. elim H10; auto. }
  assert (Convergence h) as [hl]. { apply Theorem2_9; auto. red; auto. }
  split; intros.
  - pose proof H6. apply EqualLimit in H8 as [].
    assert (mf = hl \/ hl < mf \/ mf < hl) by lra.
    destruct H10. rewrite H10; auto. destruct (Theorem7_7'b f mf H).
    destruct (H11 H7). clear H11 H12. destruct H10.
    + set (ε := (mf - hl)/2). assert (ε > 0) by (unfold ε; lra).
      assert (~ Finite \{ λ u, h[u] < hl + ε \}).
      { assert (\{ λ u, h[u] ∈ U(hl; ε) \} ⊂ \{ λ u, h[u] < hl + ε \}).
        { red; intros. applyClassifier1 H12.
          apply Classifier1. applyClassifier1 H12.
          apply Abs_R in H12. unfold ε in H12. unfold ε. lra. }
        intro. apply SubSetFinite in H12; auto. apply H9 in H11.
        assert (\{ λ u, h[u] ∈ U(hl; ε) \} ∪ \{ λ u, h[u] ∉ U(hl; ε) \}
          = Full nat).
        { apply AxiomI; split; intros. apply Classifier1; auto.
          apply Classifier1. destruct (classic (h[z] ∈ U(hl; ε)));
          [left|right]; apply Classifier1; auto. }
        assert (Finite (Full nat)) as [].
        { rewrite <-H16. apply Finite_union_Finite; auto. }
        apply finite_maxN in H17 as [N[]].
        assert (S N ∈ Full nat) by (apply Classifier1; auto).
        apply H18 in H19. lia.
        assert (0%nat ∈ Full nat) by (apply Classifier1; auto).
        rewrite H17 in H18. applyClassifier1 H18; auto. }
      apply H5 in H12. elim H12. apply H13. unfold ε. lra.
    + set (ε := (hl - mf)/2). assert (ε > 0) by (unfold ε; lra).
      pose proof H11. apply H9 in H12.
      assert (mf < hl - ε) by (unfold ε; lra). apply H14 in H15.
      assert (\{ λ u, h[u] < hl - ε \} ⊂ \{ λ u, h[u] ∉ U(hl; ε) \}).
      { red; intros. applyClassifier1 H16. apply Classifier1.
        intro. applyClassifier1 H17. apply Abs_R in H17. lra. }
      apply SubSetFinite in H16; auto. elim H15.
      assert (\{ λ u, f[u] < hl - ε \} ⊂ \{ λ u, h[u] < hl - ε \}).
      { red; intros. applyClassifier1 H17. apply Classifier1.
        pose proof (H3 z). lra. }
      apply SubSetFinite in H17; auto.
  - apply Theorem7_7'b; auto. pose proof H7. apply EqualLimit in H8 as [].
    split; intros.
    + assert (mf - β > 0) by lra. apply H9 in H11.
      assert (\{ λ u, h[u] < β \} ⊂ \{ λ u, h[u] ∉ U(mf; (mf - β)) \}).
      { red; intros. applyClassifier1 H12. apply Classifier1. intro.
        applyClassifier1 H13. apply Abs_R in H13. lra. }
      apply SubSetFinite in H12; auto.
      assert (\{ λ u, f[u] < β \} ⊂ \{ λ u, h[u] < β \}).
      { red; intros. applyClassifier1 H13. apply Classifier1.
        pose proof (H3 z). lra. }
      apply SubSetFinite in H13; auto.
    + apply H5. assert (\{ λ u, h[u] ∈ U(mf; (α - mf)) \} ⊂ \{ λ u, h[u] < α \}).
      { red; intros. applyClassifier1 H11. apply Classifier1. applyClassifier1 H11.
        apply Abs_R in H11. lra. }
      assert (~ Finite (\{ λ u, h[u] ∈ U(mf; (α - mf)) \})).
      { intro. assert (α - mf > 0). lra. apply H9 in H13.
        assert (\{ λ u, h[u] ∈ U(mf; (α - mf)) \}
            ∪ \{ λ u, h[u] ∉ U(mf; (α - mf)) \} = Full nat).
        { apply AxiomI; split; intros. apply Classifier1; auto.
          apply Classifier1. destruct (classic (h[z] ∈ U(mf; (α - mf))));
          [left|right]; apply Classifier1; auto. }
        assert (Finite (Full nat)) as [].
        { rewrite <-H14. apply Finite_union_Finite; auto. }
        apply finite_maxN in H15 as [N[]].
        assert (S N ∈ Full nat) by (apply Classifier1; auto).
        apply H16 in H17. lia.
        assert (0%nat ∈ Full nat) by (apply Classifier1; auto).
        rewrite H15 in H16. applyClassifier1 H16; auto. }
      intro. apply SubSetFinite in H11; auto.
Qed.


