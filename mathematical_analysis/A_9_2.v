(** A_9_2 *)
(* 牛顿-莱布尼茨公式 *)

Require Export A_9_1.

(* 关于该定理, F和f的条件均可减弱
   (f只需在[a,b]上可积而不必连续, F只需在(a,b)上是f的原函数而在[a,b]上连续即可)
   以下直接给出条件减弱以后的陈述 *)

(* 牛顿-莱布尼兹公式 *)
Theorem Theorem9_1 : ∀ f F a b, (∃ J, Def_Integral f a b J)
  -> Primitive_Open f F a b -> ContinuousClose F a b
  -> Def_Integral f a b (F[b] - F[a]).
Proof.
  intros. destruct H as [J].
  assert (∀ ε, 0 < ε -> ∣((F[b] - F[a]) - J)∣ < ε).
  { intros. destruct H as [H[H3[]]]. pose proof H2. apply H5 in H6 as [δ[]].
    destruct (Examp1 δ (b-a)) as [δ0[H8[]]]; auto. lra.
    assert (0 < δ0 <= b - a). lra. apply Seg_Exists in H11 as [T[n[]]]; auto.
    set (ξ := \{\ λ u v, v = c \{ λ i, T[u] < i < T[S u] /\ Derivative F i f[i]
      /\ f[i] = (F[T[S u]] - F[T[u]])/(T[S u] - T[u]) \} \}\).
    assert (∀ k, (k <= n)%nat -> T[k] < ξ[k] < T[S k] /\ Derivative F ξ[k] f[ξ[k]]
      /\ f[ξ[k]] = (F[T[S k]] - F[T[k]])/(T[S k] - T[k])).
    { intros. assert (ξ[k] ∈ \{ λ i, T[k] < i < T[S k] /\ Derivative F i f[i]
        /\ f[i] = (F[T[S k]] - F[T[k]])/(T[S k] - T[k]) \}).
      { unfold ξ. rewrite FunValue. apply Axiomc.
        assert (T[k] < T[S k]). { destruct H11 as [_[_[_[]]]]. apply H11. lia. }
        assert (a <= T[k] /\ T[S k] <= b) as [].
        { pose proof H11 as [_[_[_[_[]]]]]. rewrite <-H15,<-H16.
          split; apply (Seg_Increase_a T a b (S n)); auto; lia. }
        assert (ContinuousClose F T[k] T[S k]).
        { destruct H1 as [H1[]]. split. red; intros. apply H1. lra. split.
          destruct H15. apply Theorem4_1. apply H1. lra. rewrite <-H15; auto.
          destruct H16. apply Theorem4_1. apply H1. lra. rewrite H16; auto. }
        assert (∀ x, T[k] < x < T[S k] -> Derivable F x).
        { intros. destruct H0 as [_[_[_[_[]]]]]. exists f[x]. apply H19.
          apply Classifier1. lra. } pose proof H17.
        apply Theorem6_2 in H19 as [x[]]; auto. destruct H0 as [_[_[_[_[]]]]].
        assert (x ∈ \(a, b\)). { apply Classifier1. lra. } apply H21 in H22.
        exists x. apply Classifier1. split; auto. split; auto.
        eapply DerivativeUnique; eauto. } apply Classifier1 in H14 as []; auto. }
    assert (SegPoints T ξ (S n)).
    { red; intros. assert (k <= n)%nat. lia. apply H13 in H15 as []. lra. }
    pose proof H11. apply (H7 T ξ) in H15; auto; [ |rewrite <-H12; auto].
    assert (Σ \{\ λ u v, v = F[T[S u]] - F[T[u]] \}\ n = F[b] - F[a]).
    { assert (∀ h1 (h2 : (@set (@prod nat R))) m,
        Σ \{\ λ u v, v = h1[h2[S u]] - h1[h2[u]] \}\ m = h1[h2[S m]] - h1[h2[0%nat]]).
      { intros. induction m. simpl. rewrite FunValue; auto. simpl.
        rewrite IHm,FunValue; lra. }
      rewrite H16. destruct H11 as [_[_[_[_[]]]]]. rewrite H11,H17; auto. }
    assert (F[b] - F[a] = IntegralSum f T n ξ).
    { rewrite <-H16. apply Σ_Fact5. intros. rewrite FunValue,FunValue.
      assert (x <= n)%nat. lia. apply H13 in H18 as [H18[]]. rewrite H20,
      Rmult_comm. unfold Rdiv. rewrite <-Rmult_assoc,Rinv_r_simpl_m; auto. lra. }
    rewrite H17; auto. }
  pose proof (Abs_Rge0 (F[b] - F[a] - J)) as []. apply Rgt_lt,H2 in H3.
  exfalso. lra. apply Abs_eq_0 in H3. replace (F[b] - F[a]) with J; auto. lra.
Qed.











