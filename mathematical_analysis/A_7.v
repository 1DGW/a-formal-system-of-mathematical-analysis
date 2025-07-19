(** A_7 *)
(* 实数的完备性 *)

(* 读入文件 *)
Require Export A_2.


(* 区间列 *)
Definition Interval_Seq f := Function f /\ dom[f] = Full nat
  /\ ran[f] ⊂ \{ λ u, ∃ a b, a < b /\ u = \[a, b\] \}.

(* 用于值域包含于实数集合的函数的取值 *)
(* Notation "f [ x ]" := (f[x|(\[0,0\])%R]) (at level 5). *)

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
Corollary LeftSeq_Value : ∀ f a b n, Interval_Seq f -> a <= b -> f[n] = \[a, b\]
  -> (LeftSeq f)[n] = a.
Proof.
  intros. pose proof (LeftSeq_is_Seq f H) as [].
  assert (n ∈ dom[LeftSeq f]). { rewrite H3. apply Classifier1; auto. }
  apply x_fx_T in H4; auto. applyClassifier2 H4.
  destruct H4. unfold set in *. rewrite H1 in H4,H5.
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
  exists b. apply Classifier2. unfold set in *. rewrite H3. split.
  apply Classifier1. lra. intros. applyClassifier1 H4. lra.
Qed.

(*右端数列的取值 *)
Corollary RightSeq_Value : ∀ f a b n, Interval_Seq f -> a <= b -> f[n] = \[a, b\]
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
Corollary Interval_Nest_Coro f : Interval_Nest f
  -> IncreaseSeq (LeftSeq f) /\ DecreaseSeq (RightSeq f).
Proof.
  intros. destruct H as [H[]]. pose proof (LeftSeq_is_Seq f H).
  pose proof (RightSeq_is_Seq f H). pose proof H as [H4[]].
  split; split; auto; intros.
  - pose proof (Interval_Seq_Value f n H) as [a1[b1[]]].
    rewrite (LeftSeq_Value f a1 b1 n); auto; [ |lra].
    pose proof (Interval_Seq_Value f (S n) H) as [a2[b2[]]].
    rewrite (LeftSeq_Value f a2 b2 (S n)); auto; [ |lra].
    pose proof (H0 n). rewrite H8,H10 in H11.
    assert (a2 ∈ \[a2, b2\]). apply Classifier1; lra.
    apply H11 in H12. applyClassifier1 H12. lra.
  - pose proof (Interval_Seq_Value f n H) as [a1[b1[]]].
    rewrite (RightSeq_Value f a1 b1 n); auto; [ |lra].
    pose proof (Interval_Seq_Value f (S n) H) as [a2[b2[]]].
    rewrite (RightSeq_Value f a2 b2 (S n)); auto; [ |lra].
    pose proof (H0 n). rewrite H8,H10 in H11.
    assert (b2 ∈ \[a2, b2\]). apply Classifier1; lra.
    apply H11 in H12. applyClassifier1 H12. lra.
Qed.

(* 区间套定理 *)
(* 存在性 *)
Theorem Theorem7_1a : ∀ f, Interval_Nest f
  -> ∃ ξ, (∀ n, ξ ∈ f[n]) /\ (∀ n, (LeftSeq f)[n] <= ξ <= (RightSeq f)[n]).
Proof.
  intros. 
Admitted.

(* 唯一性 *)
Theorem Theorem7_1b : ∀ f ξ1 ξ2, Interval_Nest f
  -> ((∀ n, ξ1 ∈ f[n]) -> (∀ n, ξ2 ∈ f[n]))
    \/ ((∀ n, (LeftSeq f)[n] <= ξ1 <= (RightSeq f)[n])
      -> (∀ n, (LeftSeq f)[n] <= ξ2 <= (RightSeq f)[n]))
  -> ξ1 = ξ2.
Admitted.

Corollary Corollary7_1 : ∀ f ξ, Interval_Nest f -> (∀ n, ξ ∈ f[n])
  -> (∀ ε, ε > 0 -> (∃ N, (N > 0)%nat /\ (∀ n, (n > N)%nat -> f[n] ⊂ U(ξ; ε)))).
Admitted.

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
  { apply AxiomI; split; intros. applyClassifier1 H8. destruct H8. applyClassifier2 H8.
    destruct H8 as [x1[]]. rewrite <-H1. apply Classifier1. eauto. rewrite <-H1 in H8.
    applyClassifier1 H8. destruct H8. assert (x ∈ dom[f]). { apply Classifier1; eauto. }
    rewrite H0,<-H5 in H9. applyClassifier1 H9. destruct H9. apply Classifier1.
    exists x0. apply Classifier2. eauto. }
  left. exists m,h; auto. apply NNPP; intro.
  assert (B <> Empty Y). { intro. elim H3. right; auto. }
  apply not_empty in H4 as [y0]. rewrite <-H1 in H4. applyClassifier1 H4.
  destruct H4. assert (x ∈ dom[f]). { apply Classifier1; eauto. }
  rewrite H0,H2 in H5. applyClassifier1 H5. auto.
Qed.

(* 有限集与有限集等势 *)
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
      applyClassifier2 H4. applyClassifier2 H5. applyClassifier2 H4. applyClassifier2 H5.
      destruct H4 as [H4[]], H5 as [H5[]]. assert (y <= m \/ y = S m)%nat. lia.
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
    { apply AxiomI; split; intros. applyClassifier1 H5. destruct H5. applyClassifier2 H5.
      destruct H5. apply Classifier1; auto. apply Classifier1. applyClassifier1 H5.
      assert (z <= m \/ z = S m)%nat as []. lia. exists f[z]. apply Classifier2.
      repeat split; auto. intros. exfalso. lia. exists x. apply Classifier2.
      repeat split; auto. intros. exfalso. lia. }
    assert (ran[g] = A ∪ [x]).
    { apply AxiomI; split; intros. applyClassifier1 H6. destruct H6. applyClassifier2 H6.
      destruct H6 as [H6[]]. assert (x0 <= m \/ x0 = S m)%nat as []. lia.
      apply Classifier1. left. rewrite <-H3. apply Classifier1. exists x0.
      rewrite H7; auto. apply x_fx_T; auto. rewrite H2. apply Classifier1; auto.
      rewrite <-H8; auto. apply Classifier1; right. apply Classifier1; auto.
      applyClassifier1 H6. destruct H6. rewrite <-H3 in H6. applyClassifier1 H6.
      destruct H6. apply Classifier1. exists x0.
      assert (x0 ∈ dom[f]). { apply Classifier1; eauto. }
      rewrite H2 in H7. applyClassifier1 H7. apply Classifier2. repeat split; auto;
      intros. apply f_x_T in H6; auto. exfalso. lia. applyClassifier1 H6.
      apply Classifier1. exists (S m). apply Classifier2. repeat split; auto.
      intros. exfalso. lia. }
    left. exists (S m),g. auto.
    assert (A ∪ [x] = [x]).
    { apply AxiomI; split; intros. applyClassifier1 H1. destruct H1; auto.
      rewrite H in H1. applyClassifier1 H1. elim H1; auto. apply Classifier1; auto. }
    rewrite H1. left. apply SingletonFinite.
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
Admitted.

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
  { destruct H8. apply (RestrictFun f (\{ λ u, (u > N)%nat \})) in H8
    as [H8[]]. unfold g. rewrite H11. destruct H. rewrite H13. apply AxiomI;
    split; intros. applyClassifier1 H14. tauto. apply Classifier1; split; auto.
    apply Classifier1; auto. }
  assert (~ Finite ran[g]).
  { apply (Infinite_equ_Infinite dom[g] _ g); auto. rewrite H10; auto. }
  assert (ran[g] ⊂ (U(ξ; ε) ∩ S)).
  { red; intros. applyClassifier1 H12. destruct H12. applyClassifier1 H12. destruct H12.
    applyClassifier2 H13. destruct H13. applyClassifier1 H13. apply f_x_T in H12.
    rewrite <-H12. apply H6; auto. destruct H; auto. }
  assert (Finite (U(ξ; ε) ∩ S)).
  { destruct (classic (ξ ∈ S)).
    assert (U(ξ; ε) ∩ S = (Uº(ξ; ε) ∩ S) ∪ [ξ]).
    { apply AxiomI; split; intros. applyClassifier1 H14. destruct H14.
      destruct (classic (z = ξ)). apply Classifier1. right. apply Classifier1; auto.
      apply Classifier1; left. apply Classifier1. split; auto. apply Classifier1.
      split. apply Abs_not_eq_0. lra. applyClassifier1 H14; auto. applyClassifier1 H14.
      destruct H14. applyClassifier1 H14. destruct H14. apply Classifier1. split; auto.
      applyClassifier1 H14. destruct H14. apply Classifier1; auto. applyClassifier1 H14.
      rewrite H14. apply Classifier1; split; auto. apply Classifier1.
      rewrite Abs_ge; lra. }
    rewrite H14. apply Finite_union_Singleton; auto.
    assert (U(ξ; ε) ∩ S = Uº(ξ; ε) ∩ S).
    { apply AxiomI; split; intros. applyClassifier1 H14. destruct H14. apply Classifier1.
      split; auto. destruct (classic (z = ξ)). elim H13. rewrite <-H16; auto.
      applyClassifier1 H14. apply Classifier1; split; auto. apply Abs_not_eq_0. lra.
      applyClassifier1 H14. destruct H14. apply Classifier1; split; auto.
      applyClassifier1 H14. destruct H14. apply Classifier1; auto. }
    rewrite H14; auto. }
  elim H11. apply SubSetFinite in H12; auto.
Qed.

(* 聚点原理 *)
Theorem Theorem7_2 : ∀ S, (∃ M, Upper S M) -> (∃ L, Lower S L)
  -> ~ Finite S -> (∃ ξ, Cluster_Point S ξ).
Admitted.


(* 定义 H为S的一个开覆盖 *)
Definition Open_Cover H S := H ⊂ \{ λ u, ∃ α β, α < β /\ u = \(α, β\) \}
  /\ (∀ s, s ∈ S -> ∃ A, A ∈ H /\ s ∈ A).

(* 定义 H为S的一个无限开覆盖 *)
Definition Infinite_Open_Cover H S := Open_Cover H S /\ ~ Finite H.

(* 有限覆盖定理 *)
Theorem Theorem7_3 : ∀ H S, Open_Cover H S
  -> ∃ Hf, Hf ⊂ H /\ Finite Hf /\ Open_Cover Hf S.
Admitted.


(* 定义 数列f的聚点为a *)
Definition Seq_Cluster_Point f a := IsSeq f
  /\ (∀ ε, 0 < ε -> ~ Finite \{ λ u, f[u] ∈ Uº(a; ε) \}).

(* 数列最大聚点存在性 *)
Theorem Theorem7_4a : ∀ f, BoundedSeq f
  -> (∃ M, Seq_Cluster_Point f M /\ (∀ a, Seq_Cluster_Point f a -> a <= M)).
Admitted.

(* 数列最小聚点存在性 *)
Theorem Theorem7_4b : ∀ f, BoundedSeq f
  -> (∃ m, Seq_Cluster_Point f m /\ (∀ a, Seq_Cluster_Point f a -> m <= a)).
Admitted.


(* 数列上极限 *)
Definition uplimit_seq f M := Seq_Cluster_Point f M
  /\ (∀ a, Seq_Cluster_Point f a -> a <= M).

(* 数列下极限 *)
Definition lowlimit_seq f m := Seq_Cluster_Point f m
  /\ (∀ a, Seq_Cluster_Point f a -> m <= a).

Theorem Theorem7_5 : ∀ f M m, lowlimit_seq f m -> uplimit_seq f M -> m <= M.
Admitted.

Theorem Theorem7_6 : ∀ f a, limit_seq f a
  <-> (lowlimit_seq f a /\ uplimit_seq f a).
Admitted.

Theorem Theorem7_7a : ∀ f M, BoundedSeq f -> uplimit_seq f M
  <-> (∀ ε, ε > 0 -> (∃ N, (N > 0)%nat /\ (∀ n, (n > N)%nat -> f[n] < M + ε))
    /\ (∃ fs, SubSeq f fs /\ (∀ n, fs[n] > M - ε))).
Admitted.

Theorem Theorem7_7b : ∀ f m, BoundedSeq f -> lowlimit_seq f m
  <-> (∀ ε, ε > 0 -> (∃ N, (N > 0)%nat /\ (∀ n, (n > N)%nat -> f[n] > m - ε))
    /\ (∃ fs, SubSeq f fs /\ (∀ n, fs[n] < m + ε))).
Admitted.

Theorem Theorem7_7'a : ∀ f M, BoundedSeq f -> uplimit_seq f M
  <-> ((∀ α, α > M -> Finite \{ λ u, f[u] > α \})
    /\ (∀ β, β < M -> ~ Finite \{ λ u, f[u] > β \})).
Admitted.

Theorem Theorem7_7'b : ∀ f m, BoundedSeq f -> lowlimit_seq f m
  <-> ((∀ β, β < m -> Finite \{ λ u, f[u] < β \})
    /\ (∀ α, α > m -> ~ Finite \{ λ u, f[u] < α \})).
Admitted.

Theorem Theorem7_8a : ∀ f g Mf Mg, BoundedSeq f -> BoundedSeq g
  -> (∃ N0, (N0 > 0)%nat /\ (∀ n, (n > N0)%nat -> f[n] < g[n]))
  -> uplimit_seq f Mf -> uplimit_seq g Mg -> Mf <= Mg.
Admitted.

Theorem Theorem7_8b : ∀ f g mf mg, BoundedSeq f -> BoundedSeq g
  -> (∃ N0, (N0 > 0)%nat /\ (∀ n, (n > N0)%nat -> f[n] <= g[n]))
  -> lowlimit_seq f mf -> lowlimit_seq g mg -> mf <= mg.
Admitted.

Theorem Theorem7_8c : ∀ f α β Mf mf, BoundedSeq f
  -> (∃ N0, (N0 > 0)%nat /\ (∀ n, (n > N0)%nat -> α <= f[n] < β))
  -> uplimit_seq f Mf -> lowlimit_seq f mf
  -> α <= mf /\ mf <= Mf /\ Mf <= β.
Admitted.

Theorem Theorem7_9a : ∀ f Mf, BoundedSeq f -> uplimit_seq f Mf
  <-> limit_seq (\{\ λ u v, sup \{ λ w, ∃ m, (u <= m)%nat /\ w = f[m] \} v \}\) Mf.
Admitted.

Theorem Theorem7_9b : ∀ f mf, BoundedSeq f -> lowlimit_seq f mf
  <-> limit_seq (\{\ λ u v, inf \{ λ w, ∃ m, (u <= m)%nat /\ w = f[m] \} v \}\) mf.
Admitted.









