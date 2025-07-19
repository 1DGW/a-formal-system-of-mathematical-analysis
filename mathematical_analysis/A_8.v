(** A_8 *)
(* 不定积分 *)

(* 读入文件 *)
Require Export A_6.


(* 定义：开区间上的原函数 *)
Definition Primitive_Open f F a b := Function f /\ Function F
  /\ a < b /\ \(a, b\) ⊂ dom[f] /\ \(a, b\) ⊂ dom[F]
  /\ (∀ x, x ∈ \(a, b\) -> Derivative F x f[x]).

(* 定义：闭区间上的原函数 *)
Definition Primitive_Close f F a b := Function f /\ Function F
  /\ a < b /\ \[a, b\] ⊂ dom[f] /\ \[a, b\] ⊂ dom[F]
  /\ (∀ x, x ∈ \(a, b\) -> Derivative F x f[x])
  /\ Derivative_pos F a f[a] /\ Derivative_neg F b f[b].

(* 定理8.1 原函存在定理 书本161，要到第九章5节才能得到证明 *)

(* 定理8.2  *)
Theorem Theorem8_2a : ∀ f F a b, Primitive_Open f F a b
  -> ∀ C, Primitive_Open f (F \+ \{\ λ x y, y = C \}\) a b.
Proof.
  intros. assert(H': ∀ z, \{\ λ (x y : R), y = C \}\[z] = C).
  { intros. rewrite FunValue; auto. }
  destruct H as [H[H1[H2[H3[H4 H5]]]]]. unfold Primitive_Open in *.
  split; auto. split. apply Corollary_plus_fun_a. split; auto. split; auto.
  split. red; intros. apply Classifier1. exists (F[z]+C). apply Classifier2; auto.
  split; auto. split. apply Classifier1. exists C. apply Classifier2; auto.
  rewrite FunValue; auto. intros.
  assert(Derivative (F \+ (\{\ λ x y, y = C \}\)) x f[x]).
  { replace f[x] with (f[x] + \{\ λ x y, y = C \}\’[x]).
    apply H5 in H0 as H0'. pose proof H0'.
    apply Corollary_DerivativeValue_a in H6. rewrite <-H6.
    apply Theorem5_4a; red. eauto. exists 0. apply EleFun_Fact14.
    assert (Derivative (\{\ λ x y, y = C \}\) x 0) by (apply EleFun_Fact14).
    apply Corollary_DerivativeValue_a in H6. rewrite H6. lra. } auto.
Qed.

Theorem Theorem8_2b: ∀ f a b, a < b
  -> (∀ F G, Primitive_Open f F a b /\ Primitive_Open f G a b
    -> (∃ C, ∀ x, x ∈ \(a, b\) -> F[x] - G[x] = C)).
Proof.
  intros. destruct H0. red in H0, H1.
  destruct H0 as [_[H0[_[H7 H8]]]]. destruct H1 as [_[H6[_[H9 H10]]]].
  assert(∀ x, x ∈ \(a, b\) -> Derivative \{\ λ x0 y, y = F[x0] - G[x0] \}\ x 0).
  { intros. assert (Derivative (F \- G) x 0).
    { pose proof H1. apply H8 in H1. apply H10 in H2.
      pose proof H1. pose proof H2. apply Corollary_DerivativeValue_a in H3,H4.
      replace 0 with (F’[x] - G’[x]); [ |lra]. apply Theorem5_4b; red; eauto. }
    assert (\{\ λ x0 y, y = F[x0] - G[x0] \}\|[dom[F] ∩ dom[G]] = F \- G).
    { apply AxiomI; split; intros; destruct z. applyClassifier1 H3. destruct H3.
      applyClassifier2 H3. apply Classifier2. applyClassifier2 H4. destruct H4.
      applyClassifier1 H4. destruct H4. auto. applyClassifier2 H3.
      destruct H3 as [H3[]]. apply Classifier1. split. apply Classifier2; auto.
      apply Classifier2. split; apply Classifier1; auto. } rewrite <-H3 in H2.
    apply Lemma6_10s in H2; auto. red; intros. applyClassifier2 H4.
    applyClassifier2 H5. subst; auto. }
  assert(∃ x1, x1 ∈ \(a, b\)). { exists ((a+b)/2). apply Classifier1; lra. }
  destruct H2 as [x1]. exists (F[x1] - G[x1]).
  intros. destruct(classic (x = x1)). rewrite H4; auto.
  assert(∃ h, h = \{\ λ x0 y, y = F[x0] - G[x0] \}\). eauto.
  destruct H5 as [h]. assert(∀ x, x ∈ \(a, b\) -> Continuous h x).
  { intros. rewrite H5. apply Theorem5_1. red. exists 0; auto. }
  apply H11 in H2 as H2'; apply Theorem4_1 in H2'.
  apply H11 in H3 as H3'; apply Theorem4_1 in H3'.
  applyClassifier1 H2. applyClassifier1 H3. assert(∀ x, h[x] = F[x] - G[x]).
  { intros. rewrite H5. rewrite FunValue; auto. } apply Rdichotomy in H4.
  destruct H4.
  - assert(ContinuousClose h x x1).
    { red; split. red. intros. apply H11. apply Classifier1. lra. split; tauto. }
    assert(∀ x0, x < x0 < x1 -> Derivable h x0).
    { intros. rewrite H5. red. exists 0. apply H1; apply Classifier1; lra. }
    apply (Theorem6_2 h x x1) in H13; auto. destruct H13 as [ξ[H13 H15]].
    cut(ξ ∈ \(a, b\)). intros. apply H1 in H16. rewrite <- H5 in H16.
    apply (DerivativeUnique _ _ ((h[x1] - h[x])/(x1 - x)) 0) in H15; auto.
    apply Rmult_integral in H15 as []. rewrite <-H12,<-H12. lra.
    assert (x1 - x <> 0) by lra. apply Rinv_neq_0_compat in H17.
    elim H17; auto. apply Classifier1. lra.
  - assert(ContinuousClose h x1 x).
    { red; split. red. intros. apply H11. apply Classifier1. lra. split; tauto. }
    assert(∀ x0, x1 < x0 < x -> Derivable h x0).
    { intros. rewrite H5. red. exists 0. apply H1; apply Classifier1; lra. }
    apply (Theorem6_2 h x1 x) in H13; auto. destruct H13 as [ξ[H13 H15]].
    cut(ξ ∈ \(a, b\)). intros. apply H1 in H16. rewrite <- H5 in H16.
    apply (DerivativeUnique _ _ ((h[x] - h[x1])/(x - x1)) 0) in H15; auto.
    apply Rmult_integral in H15 as []. rewrite <-H12,<-H12. lra.
    assert (x - x1 <> 0) by lra. apply Rinv_neq_0_compat in H17.
    elim H17; auto. apply Classifier1. lra.
Qed.


(* 定义：f在开区间上的不定积分 *)
Definition Indef_Integral_Open f a b := \{ λ F, Primitive_Open f F a b \}.

(* 定义：f在闭区间上的不定积分 *)
Definition Indef_Integral_Close f a b := \{ λ F, Primitive_Close f F a b \}.

Notation "∫( f ; a ; b )" := (Indef_Integral_Open f a b).
Notation "∫[ f ; a ; b ]" := (Indef_Integral_Open f a b).

Theorem Theorem8_3 : ∀ f g F G a b k1 k2,
  Primitive_Open f F a b -> Primitive_Open g G a b
  -> Primitive_Open ((f \\* k1) \+ (g \\* k2)) ((F \\* k1) \+ (G \\* k2)) a b.
Proof.
  intros. destruct H as [H[H1[H2[H3 H4]]]], H0 as [H0[H5[H6[H7 H8]]]].
  assert(I1 : Function (F \\* k1 \+ G \\* k2)).
  { apply Corollary_plus_fun_a. }
  assert(I2 : Function (f \\* k1 \+ g \\* k2)).
  { apply Corollary_plus_fun_a. }
  assert(I3 : \(a, b\) ⊂ dom[f \\* k1 \+ g \\* k2]).
  { rewrite Corollary_plus_fun_c,Corollary_mult_fun_d,Corollary_mult_fun_d.
    red; intros. apply Classifier1; auto. }
  assert(I4 : \(a, b\) ⊂ dom[F \\* k1 \+ G \\* k2]).
  { rewrite Corollary_plus_fun_c,Corollary_mult_fun_d,Corollary_mult_fun_d.
    red; intros. destruct H4,H8. apply Classifier1; auto. }
  split; auto. split; auto. split; auto. split; auto. split; auto. intros.
  assert (Derivative (F \\* k1) x (k1 * F’[x])).
  { apply Corollary5_5. apply H4 in H9. red; eauto. }
  assert (Derivative (G \\* k2) x (k2 * G’[x])).
  { apply Corollary5_5. apply H8 in H9. red; eauto. }
  assert (Derivative (F \\* k1 \+ G \\* k2) x ((F \\* k1)’[x] + (G \\* k2)’[x])).
  { apply Theorem5_4a; auto; red; eauto. }
  apply Corollary_DerivativeValue_a in H12 as H12'.
  apply Corollary_DerivativeValue_a in H10. rewrite H10 in H12'.
  apply Corollary_DerivativeValue_a in H11. rewrite H11 in H12'.
  pose proof H9. pose proof H9. apply H4 in H13. apply H8 in H14.
  apply Corollary_DerivativeValue_a in H13,H14. rewrite H13,H14 in H12'.
  rewrite Corollary_plus_fun_b; try rewrite Corollary_mult_fun_d; auto.
  replace ((f \\* k1) [x]) with (k1 * f[x]).
  replace ((g \\* k2) [x]) with (k2 * g[x]). rewrite <-H12'.
  pose proof H12. apply Corollary_DerivativeValue_a in H15. rewrite H15; auto.
  symmetry. apply f_x_T; auto. red; intros. applyClassifier2 H15. applyClassifier2 H16.
  lra. apply Classifier2; split; auto. lra. symmetry. apply f_x_T; auto. red; intros.
  applyClassifier2 H15. applyClassifier2 H16. lra. apply Classifier2; split; auto. lra.
Qed.


(* 第1换元积分法  *)
Theorem Theorem8_4 : ∀ f ψ F a b c d, a < b -> c < d
  -> Function f -> Function ψ -> \(a, b\) ⊂ dom[f] -> \(c, d\) ⊂ dom[ψ]
  -> (∀ t, t ∈ \(c, d\) -> Derivable ψ t /\ ψ[t] ∈ \(a, b\))
  -> Primitive_Open f F a b
  -> (∀ C, Primitive_Open (\{\ λ t y, t ∈ \(c, d\) /\ y = f[ψ[t]] * ψ’[t] \}\)
    ((F ◦ ψ) \+ \{\ λ u v, v = C \}\) c d).
Proof.
  assert (∀ f ψ F a b c d, a < b -> c < d -> Function ψ -> \(c, d\) ⊂ dom[ψ]
    -> (∀ t, t ∈ \(c, d\) -> Derivable ψ t /\ ψ[t] ∈ \(a, b\))
    -> Primitive_Open f F a b -> Primitive_Open
      \{\ λ t y, t ∈ \(c, d\) /\ y = f[ψ[t]] * ψ’[t] \}\ (F ◦ ψ) c d).
  { intros. red. destruct H4 as [H9[H7[H8[H10 H6]]]]. destruct H6.
    assert(H11 : ∀ z, z ∈ \(c, d\) -> (F ◦ ψ)[z] = F[ψ[z]]).
    { intros. apply f_x_T. apply Comp_Fun_P1; auto. apply Classifier2. exists ψ[z].
      split. apply x_fx_T; auto. apply x_fx_T; auto. apply H3 in H6 as []; auto. }
    assert (Function \{\ λ t y, t ∈ \(c, d\) /\ y = f[ψ[t]] * ψ’[t] \}\).
    { red; intros. applyClassifier2 H6. applyClassifier2 H12. lra. }
    split; auto. split. apply Comp_Fun_P1; auto.
    assert(dom[\{\ λ t y, t ∈ \(c, d\) /\ y = f[ψ[t]] * ψ’[t] \}\] = \(c, d\)).
    { apply AxiomI; split; intros. applyClassifier1 H12. destruct H12 as [y].
      applyClassifier2 H12. tauto. apply Classifier1. exists(f[ψ[z]] * ψ’[z]).
      apply Classifier2; auto. }
    split; auto. split. red; intros. rewrite H12; auto. split. red; intros.
    apply Classifier1. exists (F[ψ[z]]). apply Classifier2. exists (ψ[z]). split.
    apply x_fx_T; auto. assert(ψ[z] ∈ dom[F]) by (apply H3 in H13 as []; auto).
    apply x_fx_T; auto. intros. assert(∃ u, u = ψ[x]). { exists ψ[x]; auto. } 
    destruct H14 as [u]. assert(Derivative (F ◦ ψ) x (F’[u] * ψ’[x])).
    { apply Theorem5_8; auto. apply H3; auto. red. exists f[u].
      apply H5. rewrite H14; apply H3; auto. }
    apply Corollary_DerivativeValue_a in H15 as H16. rewrite <-H12 in H13.
    apply x_fx_T in H13; auto. applyClassifier2 H13. destruct H13; auto.
    rewrite H17. cut (F’[u] = f[ψ[x]]). intros. rewrite <-H18; auto. rewrite H14.
    apply H3 in H13 as []. apply H5,Corollary_DerivativeValue_a in H18; auto. }
  intros. apply (H f ψ F a b c d) in H5; auto. apply Theorem8_2a; auto.
Qed.


(* 函数在区间上导数处处为0，则这个函数是一个常值函数 *)
Lemma Lemma8_5a : ∀ f a b, a < b -> (∀ t, t ∈ \(a, b\) -> Derivative f t 0)
  -> (∃ C, ∀x, x ∈ \(a, b\) -> f[x] = C).
Proof.
  intros. assert(∃ t1, t1 ∈ \(a, b\)).
  { exists (a + (b-a)/2). apply Classifier1. lra. }
  destruct H1. exists f[x]. intros. destruct (classic (x = x0)). rewrite H3; auto.
  assert(∀ x1 x2, x1 ∈ \(a, b\) -> x2 ∈ \(a, b\) -> x1 < x2
    -> ContinuousClose f x1 x2).
  { intros. split. intros. red; intros. apply Theorem5_1. exists 0; apply H0.
    applyClassifier1 H4. applyClassifier1 H5. apply Classifier1; lra.
    assert(Continuous f x1). { apply Theorem5_1. exists 0; apply H0; auto. }
    assert(Continuous f x2). { apply Theorem5_1. exists 0; apply H0; auto. }
    apply Theorem4_1 in H7,H8. split; tauto. } apply Rdichotomy in H3 as [].
  - apply H4 in H3 as H3'; auto. apply Theorem6_2 in H3'; auto.
    destruct H3' as [ξ[]]. assert(ξ ∈ \(a, b\)). applyClassifier1 H1.
    applyClassifier1 H2. apply Classifier1. lra. apply H0 in H7.
    apply (DerivativeUnique _ _ 0) in H6; auto. unfold Rdiv in H6.
    symmetry in H6. apply Rmult_integral in H6 as []. lra.
    assert(x0 - x <> 0). lra. apply Rinv_neq_0_compat in H6; lra. intros.
    exists 0. applyClassifier1 H1. applyClassifier1 H2. apply H0; apply Classifier1; lra.
  - apply H4 in H3 as H3'; auto. apply Theorem6_2 in H3'; auto.
    destruct H3' as [ξ[]]. assert(ξ ∈ \(a, b\)). applyClassifier1 H1.
    applyClassifier1 H2. apply Classifier1. lra. apply H0 in H7.
    apply (DerivativeUnique _ _ 0) in H6; auto. unfold Rdiv in H6.
    symmetry in H6. apply Rmult_integral in H6 as []. lra.
    assert(x0 - x <> 0). lra. apply Rinv_neq_0_compat in H6; lra. intros.
    exists 0. applyClassifier1 H1. applyClassifier1 H2. apply H0; apply Classifier1; lra.
Qed.

(* 两个函数在区间里差值为固定的常数，一个函数可导，则这两个函数的导数也相等 *)
Lemma Lemma8_5b : ∀ f G F a b C, a < b
  -> (∀ x, x ∈ \(a, b\) -> G[x] = F[x] - C)
  -> Function G -> \(a, b\) ⊂ dom[F] -> \(a, b\) ⊂ dom[G]
  -> (∀ x, x ∈ \(a, b\) -> Derivative F x (F’[x]) /\ F’[x] = f[x])
  -> (∀ x, x ∈ \(a, b\) -> Derivative G x (G’[x]) /\ G’[x] = f[x]).
Proof.
  intros. apply H0 in H5 as H0'. apply H4 in H5 as H1'.
  destruct H1'. destruct H6 as [L1[[δ'[L2 L3]] L4]].
  assert (∃ δ0, δ0 > 0 /\ U(x; δ0) ⊂ U(x; δ') /\ U(x; δ0) ⊂ \(a, b\))
    as [δ0[K0[K1 K2]]].
  { applyClassifier1 H5. destruct H5. destruct (Rlt_or_le (b-x) (x-a)).
    destruct (Examp1 (b-x) δ') as [δ0[H9[]]]; try lra. exists δ0.
    split; auto. split; red; intros; applyClassifier1 H12; apply Classifier1. lra.
    apply Abs_R in H12 as []. lra. destruct (Examp1 (x-a) δ') as [δ0[H9[]]];
    try lra. exists δ0. split; auto. split; red; intros; applyClassifier1 H12;
    apply Classifier1. lra. apply Abs_R in H12 as []. lra. }
  assert(Derivative G x f[x]).
  { red. split; auto. split. exists δ0. split; auto. red; auto.
    destruct L4 as [L4[δ[L5 [L6 L7]]]]. split. red; intros.
    applyClassifier2 H6. applyClassifier2 H8; lra. exists δ; split; auto.
    split. red; intros. apply Classifier1. exists ((G[z] - G[x])/(z - x)).
    apply Classifier2; auto. intros. apply L7 in H6. clear L7.
    destruct H6 as [δ1[]]. apply (Examp3 δ δ0 δ1) in K0 as L7; auto.
    destruct L7 as [δ2[L8[L9 L10]]]. exists δ2. split. lra. intros.
    assert(x0 ∈ \(a, b\)). { apply K2. apply Classifier1. lra. }
    rewrite FunValue. assert (0 < ∣(x0-x)∣ < δ1). lra.
    apply H8 in H11 as H8'. rewrite FunValue in H8'. rewrite H0'.
    rewrite (H0 x0); auto. rewrite <-H7.
    replace (F[x0] - C - (F[x] - C)) with (F[x0] - F[x]); auto. lra. lra. }
  apply Corollary_DerivativeValue_a in H6 as H6'. split; auto.
  rewrite <-H6' in H6; auto.
Qed.



 (* 第二换元积分法 *)
Theorem Theorem8_5 : ∀ f ψ G a b c d, a < b -> c < d
  -> Function f -> Function ψ -> \(a, b\) ⊂ dom[f] -> \(c, d\) ⊂ dom[ψ]
  -> (∀ t, t ∈ \(c, d\) -> Derivable ψ t)
  -> \{ λ u, ∃ x, x ∈ \(c, d\) /\ u = ψ[x] \} = \(a, b\)
  -> (∃ t, Inverse_Function (ψ|[\(c, d\)]) t)
  -> NotEmpty (Indef_Integral_Open f a b)
  -> Primitive_Open \{\λ t y, y = f[ψ[t]] * ψ’[t] \}\ G c d
  -> (∀ C, Primitive_Open f ((G ◦ (ψ|[\(c, d\)])﹣¹) \+ \{\ λ x y, y = C \}\) a b).
Proof.
  intros. destruct H8 as [F]. applyClassifier1 H8.
  assert(∀ t u, t ∈ \(c, d\) -> ψ[t] = u -> Derivative (F ◦ ψ) t (F’[u] * ψ’[t])).
  { intros. assert (ψ[t] ∈ \(a, b\)). { rewrite <-H6. apply Classifier1; eauto. }
    apply Theorem5_8; auto. destruct H8 as [_[_[_[]]]]. apply H13 in H12.
    rewrite <-H11. red; eauto. }
  assert(∀ t, t ∈ \(c, d\) -> Derivative G t (f[ψ[t]] * ψ’[t])).
  { intros. destruct H9 as [I1[I2[I3[I4 I5]]]]. apply I5 in H11.
    rewrite FunValue in H11; auto. }
  assert(∀ t, t ∈ \(c, d\) -> Derivative ((F ◦ ψ) \- G) t ((F ◦ ψ)’[t] - G’[t])
    /\ (F ◦ ψ)’[t] - G’[t] = 0).
  { intros. assert (Derivative (F ◦ ψ) t (F’[ψ[t]] * ψ’[t])). { apply H10; auto. }
    apply H11 in H12 as H13'. split. apply Theorem5_4b; red; eauto.
    apply Corollary_DerivativeValue_a in H13,H13'. rewrite H13,H13'.
    destruct H8 as [L1[L2[L3[L4 L5]]]]. assert (ψ[t] ∈ \(a, b\)).
    { rewrite <-H6. apply Classifier1; eauto. }
    apply L5,Corollary_DerivativeValue_a in H8. rewrite H8. lra. }
  assert(∃ C, ∀ x, x ∈ \(c, d\) -> ((F ◦ ψ) \- G)[x] = C) as [C1].
  { apply Lemma8_5a; auto. intros. apply H12 in H13 as []. rewrite <-H14; auto. }
  assert(∀ x, x ∈ \(c, d\) -> F[ψ[x]] - G[x] = C1).
  { intros. destruct H8 as [L1[L2[L3[L4 L5]]]].
    assert (ψ[x] ∈ dom[F]). { apply L5. rewrite <-H6. apply Classifier1; eauto. }
    rewrite <-(H13 x); auto. rewrite Corollary_sub_fun_b,(Comp_Fun_P3 F ψ); auto;
    try rewrite (Comp_Fun_P2 F ψ); auto; [ | |destruct H9 as [_[_[_[_[]]]]]]; auto;
    apply Classifier1; split; auto; apply Classifier1; auto. } destruct H7 as [h[]].
  assert(∀x, x ∈ \(a, b\) -> G[(ψ|[\(c, d\)])﹣¹[x]] = F[x] - C1).
  { intros. pose proof (Inverse_P1 (ψ|[\(c, d\)])) as [].
    pose proof (RestrictFun ψ \(c, d\) H2). destruct H19 as [H19[]].
    assert (Function h). { rewrite H15. destruct H7; auto. }
    assert(\(a, b\) ⊂ dom[h]).
    { rewrite H15,H17. rewrite <-H6. red; intros. applyClassifier1 H23.
      destruct H23 as [x0[]]. rewrite H24,<-H21; [apply fx_ran_T; auto| ];
      rewrite H20; apply Classifier1; auto. }
    pose proof H16. apply H23 in H16. applyClassifier1 H16. destruct H16.
    pose proof H16. apply f_x_T in H25; auto. rewrite H15 in H25. rewrite H25.
    assert ((ψ|[\(c, d\)])[x0] = x).
    { rewrite <-H25,Inverse_P3; auto. split; auto. rewrite H17.
      apply Classifier1. exists x0. rewrite <-H25. rewrite <-H25,H15 in H16.
      applyClassifier2 H16; auto. } rewrite <-H25.
    assert(x0 ∈ \(c, d\)).
    { apply H23,fx_ran_T in H24; auto. rewrite H15,H18,H20,H25 in H24.
      applyClassifier1 H24; tauto. }
    pose proof H27. apply H14 in H27. rewrite H25,<-H26,H21. lra.
    rewrite H20. apply Classifier1; auto. }
  assert(Primitive_Open f (G ◦ (ψ|[\(c, d\)])﹣¹) a b).
  { red. split; auto. split. destruct H7. apply Comp_Fun_P1; auto.
    destruct H9 as [_[]]; auto. split; auto.
    pose proof (Inverse_P1 (ψ|[\(c, d\)])) as [].
    pose proof (RestrictFun ψ \(c, d\) H2). destruct H19 as [H19[]].
    destruct H9 as [H9[H22[H23[]]]]. destruct H7.
    assert (\(a, b\) ⊂ dom[G ◦ (ψ|[\(c, d\)])﹣¹]).
    { red; intros. rewrite Comp_Fun_P2; auto. apply Classifier1. split.
      apply Classifier1. rewrite <-H6 in H27. applyClassifier1 H27. destruct H27 as [x[]].
      assert (x ∈ dom[ψ|[\(c, d\)]]). { rewrite H20. apply Classifier1; split; auto. }
      rewrite <-H21 in H28; auto. rewrite H28,Inverse_P2; auto. destruct H25;
      auto. split; [split| ]; auto. rewrite <-H6 in H27. applyClassifier1 H27.
      destruct H27 as [x[]]. assert (x ∈ dom[ψ|[\(c, d\)]]).
      { rewrite H20. apply Classifier1; split; auto. }
      rewrite H28,<-H21,H17; auto. apply Classifier1. exists x. apply x_fx_T; auto. }
    assert ((∀ x, x ∈ \(a, b\) -> (G ◦ (ψ|[\(c, d\)])﹣¹)[x] = F[x] - C1)).
    { intros. rewrite <-H16; auto. rewrite Comp_Fun_P3; auto. }
    split; auto. split; auto. intros.
    pose proof (Lemma8_5b f (G ◦ (ψ|[\(c, d \)])﹣¹) F a b C1 H H28).
    assert (Derivative (G ◦ (ψ|[\(c, d\)])﹣¹) x ((G ◦ (ψ|[\(c, d\)])﹣¹)’[x])
      /\ (G ◦ (ψ|[\(c, d\)])﹣¹)’[x] = f[x]) as [].
    { apply H30; auto. apply Comp_Fun_P1; auto. destruct H8 as [_[_[_[_[]]]]];
      auto. intros. destruct H8 as [_[_[_[_[]]]]]. apply H32 in H31.
      apply Corollary_DerivativeValue_a in H31 as H33. rewrite H33; auto. }
    rewrite <-H32; auto. }
  apply Theorem8_2a; auto.
Qed.


(* 分部积分法 *)
Theorem Theorem8_6 : ∀ u v G a b, a < b
  -> \(a, b\) ⊂ dom[u] -> \(a, b\) ⊂ dom[v]
  -> (∀ t, t ∈ \(a, b\) -> Derivable u t /\ Derivable v t)
  -> Primitive_Open \{\ λ x y, y = u’[x] * v[x] \}\ G a b
  -> Primitive_Open \{\ λ t y, y = u[t] * v’[t] \}\ ((u \* v) \- G) a b.
Proof.
  intros. split. red; intros. applyClassifier2 H4. applyClassifier2 H5. subst; auto.
  split. apply Corollary_sub_fun_a. split; auto. split. red; intros.
  apply Classifier1. exists (u[z] * v’[z]). apply Classifier2; auto. split. red; intros.
  rewrite Corollary_sub_fun_c,Corollary_mult_fun_c. destruct H3 as [_[_[_[_[]]]]].
  apply Classifier1; split; [apply Classifier1| ]; auto. intros.
  destruct H3 as [_[_[_[H3[]]]]]. rewrite FunValue.
  assert (Derivative (u \* v) x (u’[x] * v[x] + v’[x] * u[x])).
  { apply H2 in H4 as []. apply Theorem5_5b; red; eauto. }
  assert (Derivative ((u \* v) \- G) x ((u \* v)’[x] - G’[x])).
  { pose proof H3. apply H6 in H4. apply Theorem5_4b; red; eauto. }
  apply H6 in H4. rewrite FunValue in H4.
  apply Corollary_DerivativeValue_a in H4,H7.
  replace (u[x] * v’[x]) with ((u \* v)’[x] - G’[x]); auto. lra.
Qed.


