(** A_9_6 *)
(* 可积性理论补叙 *)

Require Export A_9_1.


(*************  首先补充一些后续证明需要用的关于函数和集合的事实或性质  ****************)

(* 非空自然数集有最小值 *)
Property Minimum_Principle : ∀ A, NotEmpty A -> A ⊂ \{ λ u, ∃ n, u = INR n \}
  -> ∃ m, m ∈ A /\ Lower A m.
Proof.
  intros. destruct H. apply H0 in H as H'.
  applyClassifier1 H'. destruct H' as [n]. generalize dependent H1.
  generalize dependent A. generalize dependent x. induction n as [|n H1]. intros.
  - exists x. split; auto. red. intros. subst x. apply H0 in H2. applyClassifier1 H2.
    destruct H2. subst x0. apply Rle_ge. apply le_INR. lia.
  - intros. destruct(classic (INR n ∈ A)). 
    + apply H1 in H3; auto.
    + assert(INR n ∈ A ∪ [INR n]). apply Classifier1; right; apply Classifier1; auto.
      apply H1 in H4; auto. destruct H4 as [m[]]. destruct(classic (m = INR n)).
      exists x. split; auto. unfold Lower in *. intros.
      assert(x0 ∈ A ∪ [INR n]). apply Classifier1; left; auto. apply H5 in H8.
      destruct(classic (x0 = INR n)). subst x0. contradiction.
      subst m x. apply H0 in H7. applyClassifier1 H7.
      destruct H7. subst x0. apply Rle_ge. apply le_INR.
      assert(INR n < INR x). lra.  apply INR_lt in H2. lia.
      exists m. applyClassifier1 H4. destruct H4. split; auto. 
      unfold Lower in *. intros. apply H5. apply Classifier1; left; auto.
      applyClassifier1 H4. lra. red. intros. apply Classifier1.
      applyClassifier1 H5. destruct H5. apply H0 in H5. applyClassifier1 H5; auto.
      exists n. applyClassifier1 H5; auto.
Qed.

(* 鸽笼原理 *)
Property drawerPrinciple : ∀ n D, D ⊂ \{ λ u, (u < n)%nat \}
  -> D <> \{ λ u, (u < n)%nat \}
  -> ~ (∃f,Function1_1 f /\ dom[f] = \{λ u, (u < n)%nat \} /\ ran[f] = D).
Proof.
  intros. generalize dependent D. induction n.
  - intros. assert(\{ λ u,(u < 0)%nat \} = Empty nat).
    { apply AxiomI. split;intros. applyClassifier1 H1. lia.
      applyClassifier1 H1. lia. }
    rewrite H1 in H0. apply not_empty in H0. red in H0,H. destruct H0.
    apply H in H0. applyClassifier1 H0; lia.
  - intros. intro. destruct H1 as [f[H1[]]].
    assert(\{ λ u, (u < S n)%nat \} = \{ λ u,(u < n)%nat \} ∪ [n]).
    { apply AxiomI. split; intros; apply Classifier1; applyClassifier1 H4.
      destruct (classic (z = n)) as [Hc|Hc]. right; apply Classifier1; lia.
      left; apply Classifier1; lia. destruct H4; applyClassifier1 H4; lia. }
    rewrite H4 in H. destruct(classic (n ∈ D)) as [Hc|Hc].
    + assert(J1 : ∃ k, k ∈ dom[f] /\ f[k] = n). 
     { cut(n ∈ ran[ f]); intros. applyClassifier1 H5. destruct H5. exists x.
       split. apply Classifier1; exists n; auto. destruct H1; apply f_x_T; auto.
       rewrite H3; auto. } destruct J1 as [k[]]. 
      set(g := \{\λ i v, i = k /\ (i < n)%nat /\ v = f[n] \/ 
      i <> k /\ (i < n)%nat /\ v = f[i] \}\).
      assert(J3 : (D — [n]) ⊂ \{ λ u, (u < n)%nat \}).
      { red; intros. applyClassifier1 H7; destruct H7.
        apply H in H7. applyClassifier1 H7; destruct H7; auto. 
        applyClassifier1 H7. applyClassifier1 H8. elim H8; apply Classifier1; auto. }
      assert(J4 : (D — [n]) <> \{λ u,(u < n)%nat \}).
      { intro. assert ((D — [n]) ∪ [n] = \{ λ u,(u < n)%nat \} ∪ [n]).
        { apply AxiomI. split; intros; apply Classifier1; applyClassifier1 H8.
          destruct H8. rewrite H7 in H8. left; auto. right; auto.
          destruct H8; rewrite H7. left; auto. right; auto.  }
        assert((D — [n]) ∪ [n] = D).
        { apply AxiomI. split; intros. applyClassifier1 H9. destruct H9.
          applyClassifier1 H9. tauto. applyClassifier1 H9. subst z; auto.
          apply Classifier1. destruct (classic (z = n)). right.
          apply Classifier1; auto. left. apply Classifier1. split; auto. }
         rewrite H9 in H8. rewrite <-H4 in H8. contradiction. }
      apply IHn in J3 as J3'; auto. elim J3'. exists g. destruct H1.
      assert(J2: Function g). 
      { red. intros. applyClassifier2 H9. applyClassifier2 H8.
        destruct H9 as [[H9 H9']|[H9[]]],H8 as [[I2 I2']|[I2[]]]; lia. }
      assert(J5: ∀ x z, x = f[n] -> x = f[z] -> (z < n)%nat -> z = n).
      { intros. unfold Function in H7. apply (H7 x _ _); apply Classifier2.
      rewrite H9. apply x_fx_T; auto. rewrite H2; apply Classifier1; lia. 
      rewrite H8. apply x_fx_T; auto. rewrite H2; apply Classifier1; lia. }
      assert(J6: dom[g] = \{ λ u, (u < n)%nat \}).
      { apply AxiomI. split; intros. apply Classifier1. applyClassifier1 H8.
        destruct H8. applyClassifier2 H8; destruct H8; lia.  
        apply Classifier1. applyClassifier1 H8. destruct(classic (z = k)).
        exists(f[n]). apply Classifier2. left. lia. exists (f[z]).
        apply Classifier2. right. lia. }
      repeat split; auto.
      * red. intros. repeat applyClassifier2 H9. repeat applyClassifier2 H8. 
        destruct H9 as [[H9[]]|[H9[]]],H8 as [[I2 []]|[I2[]]]. lia.
        apply (J5 x y) in H11; auto. lia. apply (J5 x z) in H12; auto. lia. 
        red in H7. apply (H7 x _ _); apply Classifier2; [rewrite H12|rewrite H11];
        apply x_fx_T; auto; rewrite H2; apply Classifier1; lia. 
      * apply AxiomI. split; intros. applyClassifier1 H8; destruct H8.
        applyClassifier2 H8; destruct H8 as [[H8[]]|[H8[]]].
        apply Classifier1. split. rewrite H10. rewrite <- H3. apply fx_ran_T; auto.
        rewrite H2; apply Classifier1; lia. apply Classifier1.
        subst k. intro. applyClassifier1 H8. subst z. red in H1.
        assert(x=n). apply (J5 n x); auto. lia. 
        apply Classifier1. split. rewrite <- H3. apply Classifier1. exists x.
        rewrite H10; apply x_fx_T; auto. rewrite H2; apply Classifier1; lia.
        apply Classifier1. intro. applyClassifier1 H11. rewrite H11 in H10.
        assert(k = x). apply (H7 n _ _); auto;[rewrite <- H6|rewrite H10];
        apply Classifier2; apply x_fx_T; auto; rewrite H2; apply Classifier1; lia. lia.
        apply Classifier1. applyClassifier1 H8. destruct H8. rewrite <- H3 in H8.
        applyClassifier1 H8. destruct H8. assert(x ∈ dom[f]). 
        apply Classifier1; exists z; auto. rewrite H2 in H10. applyClassifier1 H10. 
        destruct (classic (n = k)). destruct (classic (x = n)).
        subst k x. applyClassifier1 H9. elim H9. apply Classifier1. 
        assert(z = f[n]). symmetry; apply f_x_T; auto. 
        apply (H1 n); auto. rewrite <- H6 in H8. rewrite H11 in H8.
        rewrite <- H6; auto. assert(x ∈ dom[g]). rewrite J6. apply Classifier1; lia.
        exists x. apply Classifier2. right. repeat split;[lia|lia|].
        symmetry; apply f_x_T; auto. destruct(classic (x = n)). 
        assert(k < n)%nat. rewrite H2 in H5. applyClassifier1 H5. lia.
        exists k. apply Classifier2. left. repeat split;[lia|]. symmetry.
        subst x. apply f_x_T; auto. exists x. apply Classifier2. right.
        repeat split;[|lia|]. destruct(classic (x = k)); auto. subst x.
        apply f_x_T in H8; auto. applyClassifier1 H9. elim H9. apply Classifier1.
        lia. apply f_x_T in H8; auto.
    + destruct H1 as [H1 I2].
      assert(J0: D ⊂ \{ λ u,(u < n)%nat \}).
      { red; intros. apply H in H5 as H5'. applyClassifier1 H5'. destruct H5'; auto.
        applyClassifier1 H6. rewrite <- H6 in Hc. contradiction. }
      assert(J1: D — ([f[n]]) ⊂ \{ λ u,(u < n)%nat \}).
      { red. intros. apply Classifier1. applyClassifier1 H5. destruct H5.
       red in H.  apply J0 in H5 as H5'. applyClassifier1 H5'; auto. }
      assert(J2: D — ([f[n]]) <> \{ λ u, (u < n)%nat \}).
      { intro. assert(f[n] ∈ D). { rewrite <- H3. apply fx_ran_T; auto.
        rewrite H2; apply Classifier1; lia. }
      apply J0 in H6. rewrite <- H5 in H6. applyClassifier1 H6; destruct H6.
      applyClassifier1 H7. elim H7; apply Classifier1; auto. }
      apply IHn in J1; auto. elim J1.
      exists (f|[\{λ u,(u < n)%nat \}]).
      assert(J3: Function1_1 (f | [\{λ u,(u < n)%nat \}])).
      apply RestrictFun1_1; split; auto. split; auto. split.
      * apply AxiomI. split; intros. apply Classifier1. applyClassifier1 H5.
        destruct H5 as [y]. applyClassifier1 H5. destruct H5.
        applyClassifier2 H6. destruct H6. applyClassifier1 H6. lia.
        apply Classifier1. exists f[z]. apply Classifier1. applyClassifier1 H5.
        split. apply x_fx_T; auto. rewrite H2. apply Classifier1; lia.
        apply Classifier2. split; apply Classifier1; lia.
      * destruct J3. apply AxiomI. split; intros. applyClassifier1 H7.
        destruct H7. applyClassifier1 H7; destruct H7. applyClassifier2 H8.
        rewrite <-H3. apply Classifier1. split. apply f_x_T in H7 as H8'; auto.
        rewrite <-H8'. apply fx_ran_T; auto. destruct H8; applyClassifier1 H8.
        rewrite H2; apply Classifier1; lia. apply Classifier1. intro. applyClassifier1 H9.
        subst z. assert([n, f[n]] ∈ f). apply x_fx_T; auto.
        rewrite H2; apply Classifier1; lia. assert(x = n).
        apply (I2 f[n] _ _); apply Classifier2; auto. destruct H8.
        applyClassifier1 H8; lia. apply Classifier1.
        applyClassifier1 H7; destruct H7. applyClassifier1 H8.
        rewrite <-H3 in H7. applyClassifier1 H7; destruct H7. exists x.
        apply Classifier1. split; auto. apply Classifier2.
        destruct(classic (x = n)). subst x. elim H8. apply Classifier1. symmetry.
        apply f_x_T; auto. split;[ |apply Classifier1; auto].
        assert(x ∈ dom[f]). apply Classifier1; exists z; auto.
        apply Classifier1. rewrite H2 in H10; applyClassifier1 H10; lia.
Qed.

(* 实数中的最大值 *)
Definition maxR A r := r ∈ A /\ (∀ x, x ∈ A -> x <= r).

(* 非空有限的实数集有最大值 *)
Fact finite_maxR : ∀ A, NotEmptyFinite A -> (∃ r, maxR A r).
Proof.
  intros A H1. unfold NotEmptyFinite in H1. destruct H1 as [n H1].
  generalize dependent H1. generalize dependent A. induction n as [|n H1].
  - intros A H1. destruct H1 as [f [H1 [H2 H3]]].
    assert (H4 : \{ λ x : nat, (x <= 0)%nat \} = [0%nat]).
    { apply AxiomI. intro z; split; intro I1.
      - apply <- Classifier1. apply -> Classifier1 in I1. simpl in I1. lia.
      - apply -> Classifier1 in I1; simpl in I1. rewrite I1. apply <- Classifier1.
        apply le_n. }
    rewrite H4 in H2. assert (H5 : A = [f[0%nat]]).
    { apply AxiomI. intro z; split; intro J1.
      - apply <- Classifier1. rewrite <- H3 in J1.
        apply -> Classifier1 in J1; simpl in J1. destruct J1 as [x J1].
        assert (J2 : x ∈ dom[f]).
        { apply <- Classifier1. exists z. auto. }
        rewrite H2 in J2. apply -> Classifier1 in J2; simpl in J2.
        rewrite J2 in J1. destruct H1 as [H1 J3]. apply f_x_T in J1; auto.
      - apply -> Classifier1 in J1; simpl in J1. rewrite <- H3.
        apply <- Classifier1. exists 0%nat. assert (J2 : 0%nat ∈ dom[f]).
        { rewrite H2. apply <- Classifier1. auto. }
        apply -> Classifier1 in J2; simpl in J2. destruct J2 as [y J2].
        destruct H1 as [H1 J3]. apply f_x_T in J2 as J4; auto.
        rewrite J1. rewrite J4. auto. }
    exists f[0%nat]. unfold max. split.
    + rewrite H5. apply <- Classifier1. auto.
    + intros x. intro J1. rewrite H5 in J1.
      apply -> Classifier1 in J1; simpl in J1. rewrite <- J1. right. auto.
  - intros A H2. destruct H2 as [f [H2 [H3 H4]]].
    assert (H5 : ∃ B, B = \{ λ (x : nat), (x <= n)%nat \}).
    { exists \{ λ (x : nat), (x <= n)%nat \}. auto. }
    destruct H5 as [B H5]. apply RestrictFun1_1 with (x := B) in H2 as H6.
    destruct H2 as [H2 H7]. pose proof (RestrictFun f B).
    apply H in H2 as H8. clear H. destruct H8 as [H8 [H9 H10]].
    assert (H11 : ∃n : R, maxR ran[f|[B]] n).
    { apply H1. exists (f|[B]). split; [auto | split]; auto. rewrite H9.
      rewrite H5. rewrite H3. apply AxiomI. intro z; split; intro J1.
      - apply -> Classifier1 in J1; simpl in J1. apply J1.
      - apply <- Classifier1. split; auto. apply -> Classifier1 in J1; simpl in J1.
        apply <- Classifier1. apply le_S. auto. }
    assert (H12 : ran[f|[B]] ∪ [f[S n]] = A).
    { apply AxiomI. intro z; split; intro J1.
      - apply -> Classifier1 in J1; simpl in J1. destruct J1 as [J1 | J1].
        + rewrite <- H4. apply -> Classifier1 in J1; simpl in J1.
          destruct J1 as [x J1]. apply -> Classifier1 in J1; simpl in J1.
          destruct J1 as [J1 J2]. apply <- Classifier1. exists x. auto.
        + rewrite <- H4. apply -> Classifier1 in J1; simpl in J1.
          rewrite J1. apply fx_ran_T; auto. rewrite H3. apply <- Classifier1.
          apply le_n.
      - rewrite <- H4 in J1. apply -> Classifier1 in J1; simpl in J1.
        destruct J1 as [x J1]. assert (J2 : x ∈ dom[f]).
        { apply <- Classifier1. exists z. auto. }
        rewrite H3 in J2. apply -> Classifier1 in J2; simpl in J2.
        apply Nat.le_succ_r in J2 as J3. apply <- Classifier1.
        destruct J3 as [J3 | J3].
        + left. apply <- Classifier1. exists x. apply <- Classifier1. split; auto.
          apply <- Classifier2. split.
          * rewrite H5. apply <- Classifier1. auto.
          * apply <- Classifier1. auto.
        + right. apply <- Classifier1. symmetry. apply f_x_T; auto. rewrite <- J3.
          auto. }
    destruct H11 as [r1 H11].
    destruct (total_order_T r1 (f[S n])) as [[H13 | H13] | H13].
    + exists (f[S n]). unfold maxR. split.
      * rewrite <- H12. apply <- Classifier1. right. apply <- Classifier1; auto.
      * intros x J1. rewrite <- H12 in J1. apply -> Classifier1 in J1; simpl in J1.
        destruct J1 as [J1 | J1].
        -- apply H11 in J1. left. destruct J1 as [J1 | J1].
          ++ apply Rlt_trans with (r2 := r1); auto.
          ++ rewrite J1; auto.
        -- apply -> Classifier1 in J1; simpl in J1. rewrite <- J1. right;auto.
    + exists r1. unfold maxR. split.
      * rewrite <- H12. apply <- Classifier1. left. apply H11.
      * intros x J1. rewrite <- H12 in J1. apply -> Classifier1 in J1; simpl in J1.
        destruct J1 as [J1 | J1].
        -- apply H11. auto.
        -- apply -> Classifier1 in J1; simpl in J1. rewrite J1.
          rewrite <- H13. right; auto.
    + exists r1. unfold maxR. split.
      * rewrite <- H12. apply <- Classifier1. left. apply H11.
      * intros x J1. rewrite <- H12 in J1. apply -> Classifier1 in J1; simpl in J1.
        destruct J1 as [J1 | J1].
        -- apply H11. auto.
        -- apply -> Classifier1 in J1; simpl in J1. rewrite J1.
          left; auto.
Qed.

(* 有限集不与其真子集等势 *)
Fact Fact9_6a : ∀ {X} (A B : @set X) (f : @set (@prod X X)),
  Finite A -> B ⊂ A -> Function1_1 f -> dom[f] = A -> ran[f] = B -> B = A.
Proof.
  intros. assert (Finite B). { apply SubSetFinite in H0; auto. }
  destruct H. destruct H as [N[g[H[]]]].
  assert (Function1_1 ((g﹣¹) ◦ f ◦ g)).
  { apply Comp_Fun_P4. split; auto.
    apply Comp_Fun_P4. split; auto. apply invFun1_1; auto. }
  assert (dom[(g﹣¹) ◦ f ◦ g] = dom[g]).
  { destruct H,H1. rewrite Comp_Fun_P2; auto.
    apply AxiomI; split; intros. applyClassifier1 H10. destruct H10; auto.
    assert (g[z] ∈ dom[f]).
    { rewrite H2,<-H6. apply Classifier1. exists z. apply x_fx_T; auto. }
    apply Classifier1; split; auto. apply Classifier1.
    apply fx_ran_T in H10; auto. rewrite Comp_Fun_P2; auto. apply Classifier1.
    split; auto. apply Classifier1. destruct (Inverse_P1 g). rewrite H12,H6.
    apply H0. rewrite <-H3. apply Classifier1. exists g[z]. apply x_fx_T; auto.
    apply Comp_Fun_P1; auto. }
  assert (ran[(g﹣¹ ◦ f) ◦ g] = ran[g﹣¹|[B]]).
  { apply AxiomI; split; intros. applyClassifier1 H9. destruct H9.
    applyClassifier2 H9. destruct H9 as [y[]]. applyClassifier2 H10.
    destruct H10 as [y1[]]. applyClassifier2 H11. apply Classifier1. exists y1.
    apply Classifier1. split. apply Classifier2; auto. apply Classifier2. split.
    rewrite <-H3. apply Classifier1. eauto. apply Classifier1; auto.
    applyClassifier1 H9. destruct H9. applyClassifier1 H9. destruct H9.
    applyClassifier2 H10. destruct H10. applyClassifier2 H9. apply Classifier1.
    exists g﹣¹[f﹣¹[x]]. apply Classifier2. exists f﹣¹[x]. split.
    assert ([f﹣¹[x], g﹣¹[f﹣¹[x]]] ∈ g﹣¹).
    { apply x_fx_T. destruct H; auto. destruct (Inverse_P1 g).
      rewrite H12,H6,<-H2. destruct (Inverse_P1 f). rewrite <-H15.
      apply Classifier1. exists x. apply x_fx_T. destruct H1; auto.
      rewrite H14,H3; auto. }
    applyClassifier2 H12; auto. apply Classifier2. exists x. split.
    assert ([x, (f﹣¹)[x]] ∈ f﹣¹).
    { apply x_fx_T. destruct H1; auto. destruct (Inverse_P1 f).
      rewrite H12,H3; auto. }
    applyClassifier2 H12; auto. apply Classifier2; auto. }
  assert (ran[g﹣¹|[B]] ⊂ dom[g]).
  { red; intros. applyClassifier1 H10. destruct H10. applyClassifier1 H10.
    destruct H10. applyClassifier2 H10. apply Classifier1; eauto. }
  apply NNPP; intro. assert (NotEmpty (A — B)) as [x].
  { apply NNPP; intro. elim H11. apply AxiomI; split; intros; auto.
    apply NNPP; intro. apply H12. exists z. apply Classifier1; split; auto. }
  applyClassifier1 H12. destruct H12.
  assert ((g﹣¹)[x] ∈ dom[g] /\ (g﹣¹)[x] ∉ ran[g﹣¹|[B]]) as [].
  { split. apply Classifier1. exists x.
    assert ([x, (g﹣¹)[x]] ∈ (g﹣¹)).
    { apply x_fx_T. destruct H; auto. destruct (Inverse_P1 g).
      rewrite H14,H6; auto. }
    applyClassifier2 H14; auto. intro. destruct H. applyClassifier1 H14. destruct H14.
    pose proof H14. applyClassifier1 H16. destruct H16.
    assert ([x, g﹣¹[x]] ∈ g﹣¹).
    { apply x_fx_T; auto. destruct (Inverse_P1 g). rewrite H18,H6; auto. }
    applyClassifier2 H16. applyClassifier2 H18. assert (x = x0).
    { apply (H (g﹣¹[x])); auto. }
    assert (x ∈ dom[g﹣¹|[B]]). { rewrite H19. apply Classifier1; eauto. }
    pose proof (RestrictFun g﹣¹ B). apply H21 in H15 as [H15[]].
    rewrite H22 in H20. applyClassifier1 H20. destruct H20. applyClassifier1 H13; auto. }
  assert (ran[g﹣¹|[B]] <> dom[g]). { intro. rewrite <-H16 in H14; auto. }
  assert (\{ λ x, (x <= N)%nat \} = \{ λ x,(x < S N)%nat \}).
  { apply AxiomI; split; intros; applyClassifier1 H17; apply Classifier1; lia. }
  rewrite H17 in *. rewrite H5 in *. elim (drawerPrinciple (S N) ran[g﹣¹|[B]]);
  eauto. apply AxiomI; split; intros; auto. rewrite H in H5. applyClassifier1 H5.
  elim H5; auto.
Qed.

(* 两个一一函数, 定义域相差一个值, 则值域也相差一个值 *)
Fact Fact9_6b : ∀ {X : Type} (f g : @set (@prod nat X)) (n : nat),
  Function1_1 f -> Function1_1 g -> dom[f] = \{ λ u, (u < n)%nat \}
  -> ran[f] ⊂ ran[g] -> dom[g] = \{ λ u, (u < S n)%nat \}
  -> ∃ a, (ran[g] — ran[f]) = [a].
Proof.
  intros. destruct H. destruct H0.
  assert(ran[f] <> ran[g]).
  { destruct(classic (ran[f] = ran[g])) as [Hc|Hc]; auto.
    pose proof (Inverse_P1 f) as [].
    assert((∃f,Function1_1 f /\ dom[f] = \{λ u, (u < S n)%nat \} 
      /\ ran[f] = \{ λ u,(u < n)%nat \})).
    { exists(f ﹣¹ ◦ g). assert(J0: Function1_1 (f ﹣¹ ◦ g)). 
      { apply Comp_Fun_P4. repeat split; auto. 
        red. intros. repeat applyClassifier2 H8. repeat applyClassifier2 H9.
        apply (H x); auto. }
      assert(J1: dom[ f ﹣¹ ◦ g] = \{ λ u,(u < S n)%nat \}).
      { rewrite (Comp_Fun_P2 (f﹣¹) g); auto. rewrite <- H3. rewrite H6.
        apply AxiomI. split; intros. applyClassifier1 H8. destruct H8. auto.
        apply Classifier1. split; auto. apply Classifier1. rewrite Hc.
        apply Classifier1. exists z. apply x_fx_T; auto. }
      split; auto. split; auto. apply AxiomI. split; intros. applyClassifier1 H8.
      destruct H8. applyClassifier2 H8. destruct H8 as [y[]]. applyClassifier2 H9.
      rewrite <- H1. apply Classifier1. exists y; auto.
      rewrite <- H1 in H8. applyClassifier1 H8. destruct H8.
      apply Classifier1. assert(x ∈ ran[g]). rewrite <-Hc. apply Classifier1.
      exists z; auto. applyClassifier1 H9. destruct H9. exists x0. 
      apply Classifier2. exists x. split; auto. apply Classifier2; auto. }
     assert(J3: dom[ f] ⊂  \{ λ u,(u < S n)%nat \}).
     { rewrite H1. red; intros. applyClassifier1 H9; apply Classifier1; lia. }
     apply (drawerPrinciple (S n) dom[f]) in J3. rewrite H1 in J3.
     contradiction. intro. rewrite H1 in H9.
     assert(n ∈ \{ λ u,(u < S n)%nat\}). apply Classifier1; lia.
     rewrite <- H9 in H10. applyClassifier1 H10. lia. }
     assert(J4: ∃a : X, a ∈ ran[g] /\ a ∉ ran[f]).
     { apply NNPP. intro. assert(∀a, a ∈ ran[ g] -> a ∈ ran[ f]).
       { intros. red in H7. apply NNPP. intro. apply H7. exists a.
         split; try tauto.  }  assert(ran[g] = ran[f]).
       { apply AxiomI. split; intros. apply H8; auto. apply H2; auto. }
       rewrite H9 in H6. contradiction. } destruct J4 as [x[]]. 
     assert([x] ⊂ ran[g] — ran[f]).
     { red; intros. applyClassifier1 H9. subst.
       apply Classifier1; split; [|apply Classifier1]; auto. }
     assert(J5: (ran[g] — ran[f]) ⊂ [x]).
     { red. intros. apply Classifier1. destruct(classic (z = x)); auto.
       applyClassifier1 H10; destruct H10. assert(ran[f] ∪ [z] ⊂ ran[g]).
       { red; intros. applyClassifier1 H13. destruct H13. apply H2; auto.
         applyClassifier1 H13; subst; tauto. }
     assert(ran[f] ∪ [z] <> ran[g]).
     { intro. rewrite <-H14 in H7. applyClassifier1 H7. destruct H7.
       contradiction. applyClassifier1 H7. auto. }
     set(f1 := f∪[[n,z]]). applyClassifier1 H11.
     assert(J6: ∀x0 y, [x0, y] ∈ f -> x0 ∈ dom[ f]).
     { intros. apply Classifier1. exists y; auto. }
     assert(J4 : Function1_1 f1 /\ dom[f1] = \{λ u,(u < S n)%nat\} 
       /\ ran[f1] = ran[ f]∪[z]).
     { assert(J5 : n ∉ dom[ f]). intro.
       rewrite H1 in H15; applyClassifier1 H15; lia.
       assert(J7: ∀x0 y, [x0, y] ∈ f -> y ∈ ran[ f]).
       { intros. apply Classifier1. exists x0; auto. }
       repeat split.
       - red. intros. applyClassifier1 H15. applyClassifier1 H16. destruct H15,H16.
         apply (H x0); auto. applyClassifier1 H16. apply J6 in H15.
         apply ProdEqual in H16 as []. subst x0. contradiction. 
         applyClassifier1 H15. apply J6 in H16.
         apply ProdEqual in H15 as []. subst x0. contradiction. 
         applyClassifier1 H16. applyClassifier1 H15.
         apply ProdEqual in H16 as [], H15 as[]; subst; auto. 
       - red; intros. applyClassifier2 H15. applyClassifier2 H16.
         applyClassifier1 H15. applyClassifier1 H16. destruct H15,H16.
         apply (H4 x0); apply Classifier2; auto. applyClassifier1 H16.
         apply ProdEqual in H16 as []. subst x0. apply J7 in H15. contradiction. 
         applyClassifier1 H15. apply J7 in H16. apply ProdEqual in H15 as [].
         subst x0. contradiction. applyClassifier1 H16. applyClassifier1 H15.
         apply ProdEqual in H16 as [], H15 as[]; subst; auto.
       - apply AxiomI. split; intros. applyClassifier1 H15. destruct H15.
         apply Classifier1. applyClassifier1 H15. destruct H15. apply J6 in H15.
         rewrite H1 in H15; applyClassifier1 H15; lia. applyClassifier1 H15.
         apply ProdEqual in H15 as []. lia. apply Classifier1.
         applyClassifier1 H15. destruct(classic (z0 = n)). exists z.
         apply Classifier1. right. apply Classifier1. subst; auto. exists f[z0].
         apply Classifier1. left. apply x_fx_T; auto.
         rewrite H1; apply Classifier1; lia.
       - apply AxiomI. split; intros. apply Classifier1.
         applyClassifier1 H15; destruct H15. applyClassifier1 H15; destruct H15.
         left; apply (J7 x0); auto. applyClassifier1 H15.
         apply ProdEqual in H15 as []. right; apply Classifier1; auto.
         apply Classifier1. applyClassifier1 H15; destruct H15.
         applyClassifier1 H15; destruct H15. exists x0. apply Classifier1.
         left; auto. exists n. applyClassifier1 H15. apply Classifier1.
         right; apply Classifier1; subst; auto. }
     destruct J4 as [[][]].
     assert((∃f',Function1_1 f' /\ dom[f'] = ran[g] 
       /\ ran[f'] = ran[f] ∪ [z])) as [f'[H19[]]].
     { exists(f1 ◦ g﹣¹). assert(J0 : Function1_1 (f1 ◦ g﹣¹)). 
       { apply Comp_Fun_P4. repeat split; auto. red. intros.
         repeat applyClassifier2 H19. repeat applyClassifier2 H20.
         apply (H0 x0); auto. }
       pose proof (Inverse_P1 g) as [].
       assert(J1: dom[f1 ◦ g﹣¹] = ran[g]).
       { rewrite (Comp_Fun_P2 f1 (g﹣¹)); auto. rewrite H19. rewrite H17,<-H3.
         apply AxiomI. split; intros. applyClassifier1 H21. destruct H21. auto.
         apply Classifier1. split; auto. apply Classifier1. apply Classifier1.
         exists z0. applyClassifier1 H21. destruct H21.
         assert((g﹣¹)[z0] = x0). apply f_x_T; auto. apply Classifier2; auto.
         subst; auto. }
       split; auto. split; auto. apply AxiomI.
       split; intros; applyClassifier1 H21; destruct H21.
       applyClassifier2 H21. destruct H21 as [y[]]. applyClassifier2 H21.
       applyClassifier1 H22. destruct H22; apply Classifier1.
       left; apply Classifier1; exists y; auto. applyClassifier1 H22.
       right; apply ProdEqual in H22 as []. apply Classifier1; auto.
       apply Classifier1. applyClassifier1 H21. destruct H21.
       assert(x0 ∈ dom[g]). apply (J6 x0 z0) in H21 as H22. rewrite H1 in H22.
       rewrite H3; applyClassifier1 H22; apply Classifier1; lia. exists g[x0].
       apply Classifier2. exists x0. split; auto. apply Classifier2.
       apply x_fx_T; auto. apply Classifier1. left; auto. applyClassifier1 H21.
       assert(n ∈ dom[g]). rewrite H3; apply Classifier1; lia.
       apply Classifier1. exists g[n]. apply Classifier2. exists n. split; auto.
       apply Classifier2. apply x_fx_T; auto. apply Classifier1. right; auto.
       apply Classifier1. subst; auto. }
     apply (Fact9_6a _ _ f') in H13; auto. elim H14; auto. left. exists n,g.
     repeat split; auto. rewrite H3. apply AxiomI; split; intros;
     applyClassifier1 H22; apply Classifier1; lia. }
   exists x. apply AxiomI; split; auto.
Qed.

(* 函数限制在 {x < n} 上还是函数(相当于差掉一个值 f — [Sn, f[Sn]]) *)
Fact Fact9_6c : ∀ {X : Type} (f : @set (@prod nat X)) n B,
  Function1_1 f -> dom[f] = \{ λ x, (x < S n)%nat \}
  -> f[n] ∈ ran[f] -> ran[f] = B
  -> Function1_1 (f|[\{λ x, (x < n)%nat\}])
    /\ dom[f|[\{ λ x, (x < n)%nat \}]] = \{ λ x0, (x0 < n)%nat \}
    /\ ran[f|[\{ λ x, (x < n)%nat \}]] = B — [f[n]].
Proof.
  intros. destruct H. assert(J3 : Function1_1 (f | [\{λ u,(u < n)%nat \}])).
  { apply RestrictFun1_1; split; auto. } split; auto. split. 
  * apply AxiomI. split; intros. apply Classifier1. applyClassifier1 H4.
    destruct H4 as [y]. applyClassifier1 H4; destruct H4.
    applyClassifier2 H5. destruct H5. applyClassifier1 H5. lia.
    apply Classifier1. exists f[z]. apply Classifier1. applyClassifier1 H4. split.
    apply x_fx_T; auto. rewrite H0. apply Classifier1; lia.
    apply Classifier2. split; apply Classifier1; auto.
  * destruct J3. apply AxiomI. split; intros. repeat (applyClassifier1 H6;
    destruct H6). applyClassifier2 H7.
    rewrite <-H2. apply Classifier1. split. apply f_x_T in H6 as H8'; auto.
    rewrite <-H8'. apply Classifier1. exists x. subst z; auto.
    apply Classifier1. intro. applyClassifier1 H8. subst z.
    assert([n, f[n]] ∈ f). apply x_fx_T; auto.
    rewrite H0; apply Classifier1; lia.
    assert(x = n). apply (H3 f[n] _ _); apply Classifier2; auto.
    destruct H7. applyClassifier1 H7; lia. apply Classifier1.
    applyClassifier1 H6; destruct H6. applyClassifier1 H7. rewrite <-H2 in H6.
    applyClassifier1 H6; destruct H6. exists x. apply Classifier1. split; auto.
    apply Classifier2. destruct (classic (x = n)). subst x. elim H7.
    apply Classifier1. symmetry. apply f_x_T; auto.
    split;[|apply Classifier1; auto]. assert(x ∈ dom[f]).
    apply Classifier1; exists z; auto. apply Classifier1.
    rewrite H0 in H9; applyClassifier1 H9; lia.
Qed.

(* 函数并一个值还是函数 *)
Fact Fact9_6d : ∀ {X :Type} (f : @set (@prod nat X)) x n B,
  Function1_1 f -> dom[f] = \{ λ x ,(x <= n)%nat \} -> x ∉ ran[f] -> ran[f] = B
  -> Function1_1 (f ∪ [[S n,x]])
    /\ dom[f ∪ [[S n, x]]] = \{ λ x0,(x0 <= S n)%nat \}
    /\ ran[f ∪ [[S n, x]]] = B ∪ [x].
Proof.
  intros. destruct H. 
  assert(J1: ∀x0 y, [x0, y] ∈ f -> y ∈ ran[ f]).
  { intros. apply Classifier1. exists x0; auto. }
  assert(J2: ∀x0 y, [x0, y] ∈ f -> x0 ∈ dom[ f]).
  { intros. apply Classifier1. exists y; auto. }
  assert(J3: S n ∉ dom[ f]). intro. rewrite H0 in H4; applyClassifier1 H4; lia.
  repeat split.
  - red. intros. applyClassifier1 H4. applyClassifier1 H5. destruct H5,H4.
    apply (H x0); auto. applyClassifier1 H4. apply J2 in H5. 
    apply ProdEqual in H4 as []. subst x0. contradiction. 
    applyClassifier1 H5. apply J2 in H4. 
    apply ProdEqual in H5 as []. subst x0. contradiction. 
    applyClassifier1 H5. applyClassifier1 H4. 
    apply ProdEqual in H5 as [], H4 as[]; subst; auto. 
  - red; intros. applyClassifier2 H5. applyClassifier2 H4. applyClassifier1 H5.
    applyClassifier1 H4. destruct H5,H4. apply (H3 x0); apply Classifier2; auto.
    applyClassifier1 H4. apply ProdEqual in H4 as []. subst x0. apply J1 in H5.
    contradiction. applyClassifier1 H5. apply J1 in H4. 
    apply ProdEqual in H5 as []. subst x0. contradiction. 
    applyClassifier1 H5. applyClassifier1 H4. 
    apply ProdEqual in H5 as [], H4 as[]; subst; auto.    
  - apply AxiomI. split; intros. applyClassifier1 H4. destruct H4.
    apply Classifier1. applyClassifier1 H4. destruct H4. apply J2 in H4. 
    rewrite H0 in H4; applyClassifier1 H4; lia. applyClassifier1 H4.
    apply ProdEqual in H4 as []. lia. apply Classifier1. applyClassifier1 H4.
    destruct(classic (z = S n)). exists x. apply Classifier1. right.
    apply Classifier1. subst; auto. exists f[z]. apply Classifier1. left.
    apply x_fx_T; auto. rewrite H0; apply Classifier1; lia.
  - apply AxiomI. rewrite <- H2. split; intros. apply Classifier1.
    applyClassifier1 H4; destruct H4. applyClassifier1 H4; destruct H4.
    left; apply (J1 x0); auto. applyClassifier1 H4. apply ProdEqual in H4 as [].
    right; apply Classifier1; auto.
    apply Classifier1. applyClassifier1 H4; destruct H4. applyClassifier1 H4; 
    destruct H4. exists x0. apply Classifier1. left; auto. exists (S n). 
    applyClassifier1 H4. apply Classifier1. right. apply Classifier1. subst; auto.
Qed.

(* 有限集并有限集还是有限集 *)
Fact Fact9_6e: ∀ {X : Type} (A B : @set X), Finite A -> Finite B
  -> Finite (A ∪ B).
Proof.
  intros. unfold Finite in *.
  assert(J0 : ∀ (A B : @set X), B = Empty X -> A ∪ B = A).
  { intros. rewrite H1. apply AxiomI; split; intros. 
    applyClassifier1 H2; destruct H2; auto. applyClassifier1 H2; contradiction.
    apply Classifier1. left; auto. }
  destruct H, H0. destruct H as [n[f[H[]]]].
  assert (I1 : ∀ n, \{ λ x,(x <= n)%nat\} = \{ λ x, (x < S n)%nat \}).
  { intros. apply AxiomI; split; intros; applyClassifier1 H3; apply Classifier1;
    lia. }
  - generalize dependent f. generalize dependent A.
    induction n. left. red. destruct H0 as [n1[g[H0[]]]]. destruct H, H0.
    assert(∃ x : X, A = [x]).
    { exists f[0%nat]. apply AxiomI. split; intros. apply Classifier1.
      rewrite <- H2 in H7. applyClassifier1 H7. destruct H7.
      assert(x ∈ dom[f]). apply Classifier1. exists z; auto. rewrite H1 in H8.
      applyClassifier1 H8. assert (x = 0)%nat. lia. subst x. symmetry.
      apply f_x_T; auto. applyClassifier1 H7. rewrite <-H2. apply Classifier1.
      exists 0%nat. rewrite H7. apply x_fx_T; auto.
      rewrite H1; apply Classifier1; lia. }
    destruct H7. destruct(classic (x ∈ B)) as [Hc|Hc].
    + exists n1, g. repeat split; auto. rewrite H4, H7. apply AxiomI.
      split; intros. apply Classifier1. right; auto. applyClassifier1 H8. 
      destruct H8; auto. applyClassifier1 H8; subst; auto.
    + exists (S n1), (g ∪ [[(S n1), x]]).
      apply (Fact9_6d g x n1 B) in H3; auto. 
      destruct H3 as [[H3 H3'][]]. repeat split; auto. rewrite H7. rewrite H9.
      apply AxiomI; split; intros; applyClassifier1 H10; destruct H10;
      apply Classifier1; auto. red; auto. rewrite H4. intro. contradiction.
    + intros. destruct H. assert(S n ∈ dom[f]). rewrite H1; apply Classifier1; lia.
      assert(f[S n] ∈ ran[f]). apply Classifier1. exists (S n). apply x_fx_T; auto.
      assert(J1: Function1_1 (f|[[S n]])).
      { apply RestrictFun1_1; split; auto. }
      rewrite (I1 (S n)) in H1.
      apply (Fact9_6c f (S n) A) in H1; auto;[|split;auto].
      destruct H1 as [H1[]]. apply (IHn (A — [f[S n]])) in H1; auto.
      assert(J2: (A — [f[S n]] ∪ B) ∪ [f[S n]] = A ∪ B).
      { apply AxiomI; split; intros; applyClassifier1 H8; apply Classifier1;
        destruct H8. repeat (applyClassifier1 H8; destruct H8);[left|right]; auto.
        applyClassifier1 H8. subst; auto. destruct(classic (z = f[S n])).
        right. apply Classifier1; auto. repeat (left; apply Classifier1).
        split; auto. left; apply Classifier1; right; auto. }
      destruct H1. destruct(classic (f[S n] ∈ B)) as [Hc|Hc].
      * assert((A — [f[S n]] ∪ B) = (A ∪ B)).
        { apply AxiomI. split; intros; applyClassifier1 H8; apply Classifier1;
          destruct H8. applyClassifier1 H8. left; tauto. right; auto.
          destruct(classic (z = f[S n])). subst. right; auto. left.
          apply Classifier1. split; auto. apply Classifier1. right; auto. }
        rewrite <-H8. left; auto.
      * left. destruct H1 as [k[h[H1[]]]]. red.
        exists (S k), (h ∪ [[(S k), f[S n]]]). rewrite <-J2.
        apply (Fact9_6d h (f[S n]) k (A — [f[S n]] ∪ B)); auto.
        intro. rewrite H9 in H10. repeat (applyClassifier1 H10; destruct H10).
        applyClassifier1 H11. apply H11; apply Classifier1; auto. auto.
      *  assert((A ∪ B) = [f[S n]]).
        { rewrite <- J2. rewrite H1. apply AxiomI. split; intros;
          applyClassifier1 H8; destruct H8; auto. applyClassifier1 H8. contradiction.
          apply Classifier1. right; apply Classifier1; auto. }
        rewrite H8. left. apply SingletonFinite.
      * rewrite (I1 n); auto. 
    - left. rewrite (J0 A B); auto. 
    - left. apply (J0 B A) in H; auto. assert(B ∪ A = A ∪ B).
      apply AxiomI; split; intros; apply Classifier1; applyClassifier1 H1; tauto.
      rewrite <- H1, H; auto.
    - right. apply (J0 A) in H0. rewrite H0; auto.
Qed.

(* 定义: 严格单增数列 *)
Definition StrictlyIncreaseFun_Seq f := Function f
  /\ (∀ x1 x2: nat, x1 ∈ dom[f] -> x2 ∈ dom[f] -> (x1 < x2)%nat -> f[x1] < f[x2]).

(* 非空有限集上可构造严格递增函数 *)
Fact Fact9_6f : ∀ A, NotEmptyFinite A
  -> (∃ n T, (0 < n)%nat /\ StrictlyIncreaseFun_Seq T
    /\ dom[T] = \{λ u, (u < n)%nat \} /\ ran[T] = A ).
Proof.
  intros. pose proof H as J1. destruct H as [n[f[]]].
  generalize dependent A. generalize dependent f. induction n.
  - intros. destruct H0, H. exists 1%nat,f. repeat split; auto. intros.
    rewrite H0 in H3. rewrite H0 in H4. applyClassifier1 H3. applyClassifier1 H4. lia.
    apply AxiomI. split; intros; [rewrite H0 in H3 | rewrite H0];
    apply Classifier1; applyClassifier1 H3; lia.
  - intros. apply finite_maxR in J1. destruct J1 as [y].
    assert(∃x, x ∈ dom[f] /\ f[x] = y). { destruct H1 as [].
    destruct H0 as []. rewrite <- H3 in H1. applyClassifier1 H1.
    destruct H1 as [x]. exists x. split. apply Classifier1. exists y; auto.
    destruct H; apply f_x_T; auto. }
    destruct H2 as [x[H2 H2']].
    set(f1 := \{\ λ i v,(i < x)%nat /\ v = f[i]
      \/ (x <= i <= n)%nat /\ v = f[S i] \}\). 
    assert (Function1_1 f1 /\ dom[f1] = \{ λ x, (x <= n)%nat\}
      /\ ran[ f1] = A — [y]).
    { destruct H0 as [H0 H0']. rewrite H0 in H2. applyClassifier1 H2.
      destruct H. red in H, H3.
      assert(H5: ∀i, (i < x)%nat \/ (x <= i <= S n)%nat -> i ∈ dom[f]).
      { intros. destruct H4 as [H6|H6]; rewrite H0; apply Classifier1; lia. }
      assert(H7: ∀i k,(i <= S n)%nat -> (k <= S n)%nat -> (∃x0,x0 = f[i] 
       /\ x0 = f[k]) -> i = k). { intros. destruct H7 as [x1[H9 H9']].
        apply (H3 x1); auto; apply Classifier2;[rewrite H9|rewrite H9']; 
        apply x_fx_T; auto; rewrite H0; apply Classifier1; lia. } repeat split.
      - unfold Function. intros. applyClassifier2 H4. applyClassifier2 H6.
        destruct H6 as [[H6 H6']|[H6 H6']], H4 as [[H4 H4']|[H4 H4']]
        ;[lra|lia|lia|lra].
      - unfold Function. intros.  
        repeat applyClassifier2 H6. repeat applyClassifier2 H4. 
        destruct H6 as [[H6 H6']|[H6 H6']], H4 as [[H4 H4']|[H4 H4']].
        apply H7;[lia|lia|exists x0;split;auto]. 
        assert(S y0 = z). apply H7;[lia|lia|exists x0;split;auto]. lia.
        assert(S z = y0). apply H7;[lia|lia|exists x0;split;auto]. lia.
        assert(S y0 = S z). apply H7;[lia|lia|exists x0;split;auto]. lia.
      - apply AxiomI. split; intros. apply Classifier1. applyClassifier1 H4.
        destruct H4 as [y0]. applyClassifier2 H4. lia. apply Classifier1. 
        applyClassifier1 H4. destruct(classic (z < x)%nat). exists f[z].
        apply Classifier2. left. split; auto. exists f[S z].
        apply Classifier2. right. split; auto; lia.
      - apply AxiomI. split; intros. apply Classifier1.
        applyClassifier1 H4. destruct H4 as [x0]. applyClassifier2 H4.
        destruct H4 as [[]|[]]. split. rewrite <- H0'. apply Classifier1. 
        exists x0. rewrite H6. apply x_fx_T; auto. apply Classifier1. intro.
        applyClassifier1 H8. assert(x0 = x).
        apply H7;[lia|lia|exists z; split; auto]. lra. lia.
        split. rewrite <- H0'. apply Classifier1. exists (S x0). rewrite H6.
        apply x_fx_T; auto. rewrite H0. apply Classifier1. lia. apply Classifier1.
        intro. applyClassifier1 H8.
        assert(S x0 = x). apply H7;[lia|lia|exists z; split; auto]. lra. lia.
        apply Classifier1. applyClassifier1 H4. destruct H4. rewrite <-H0' in H4.
        applyClassifier1 H4. destruct H4 as [x0]. destruct (classic (x0 <= x)%nat).
        exists x0. apply Classifier2. left. split. assert (x0 < x \/ x0 = x)%nat.
        lia. destruct H9; auto. assert(f[x0] = z). apply f_x_T; auto.
        applyClassifier1 H6. elim H6. apply Classifier1. rewrite <-H2',<-H9.
        symmetry. apply f_x_T; auto. symmetry. apply f_x_T; auto.
        exists (pred x0). apply Classifier2. right. assert(x0 ∈ dom[f]).
        apply Classifier1. exists z; auto. rewrite H0 in H9.
        applyClassifier1 H9. split. lia. replace (S (pred x0)) with x0.
        symmetry; apply f_x_T; auto. lia. }
    assert(NotEmptyFinite (A — [y])).
    { red. exists n,f1. split; tauto. } destruct H3.
    apply (IHn f1 H3 (A — [y]) H5) in H4 as J3.
    destruct J3 as [n1[T[H6a[H6[H6']]]]]. exists (S n1).
    exists \{\ λ u v, (u < n1)%nat /\ v = T[u] \/ u = n1 /\ v = y \}\.
    assert(J2: Function \{\ λ u v, (u < n1)%nat /\ v = T[u] \/ u = n1 
      /\ v = y \}\). { red. intros. applyClassifier2 H8. applyClassifier2 H9.
    destruct H8 as [[H8 ]|[H8 ]], H9 as [[H9 ]|[H9 ]];[lra|lia|lia|lra]. }
    clear H3 H5 f1. destruct H6 as [H6 J3]. repeat split; auto.
    + assert(J4: ∀x1, (x1 < n1)%nat -> \{\λ u v,(u < n1)%nat /\ v = T[u] 
      \/ u = n1 /\ v = y \}\[x1] = T[x1]).
      { intros. apply f_x_T; auto. apply Classifier2; left; auto. }
      assert(J5: ∀x1, (x1 = n1)%nat -> \{\λ u v,(u < n1)%nat /\ v = T[u] 
      \/ u = n1 /\ v = y \}\[x1] = y).
      { intros. apply f_x_T; auto. apply Classifier2; right; auto.  }
      assert(J6: ∀x1, (x1 < n1)%nat -> x1 ∈ dom[T]). { intros.  
      rewrite H6'; apply Classifier1; lia. }
      assert(J7: ∀x1, (x1 < n1)%nat -> T[x1] < y).
      { intros. apply J6 in H3. assert(T[x1] ∈ ran[ T]). apply fx_ran_T; auto.
        rewrite H7 in H5. applyClassifier1 H5. destruct H1. destruct H5.
        apply H8 in H5. applyClassifier1 H9. destruct H5; auto.
        elim H9; apply Classifier1; auto. } 
      intros. applyClassifier1 H3. applyClassifier1 H5.
      destruct H3 as [y1],H5 as [y2].
      applyClassifier2 H3. applyClassifier2 H5. 
      destruct H3 as [[H3 H3']|[H3 H3']], H5 as [[H5 H5']|[H5 H5']].
      repeat rewrite J4; auto. rewrite J4; auto. rewrite J5; auto. lia. lia.
    + apply AxiomI. split; intros. apply Classifier1.
      applyClassifier1 H3. destruct H3 as [y0]. applyClassifier2 H3. 
      destruct H3 as [[H9 _]|[H9_]]; lia. apply Classifier1. applyClassifier1 H3.
      destruct (classic (z = n1)). exists y. apply Classifier2. right.
      split; auto. exists T[z]. apply Classifier2. left. split; auto. lia.
    + apply AxiomI. split; intros. applyClassifier1 H3. destruct H3 as [x0 H9].
      applyClassifier2 H9. destruct H9 as [[H9 H9']|[H9 H9']].
      assert(x0 ∈ dom[T]). rewrite H6'; apply Classifier1; auto.  
      assert(T[x0] ∈ ran[T]).  apply fx_ran_T; auto.
      rewrite H7 in H5. applyClassifier1 H5. rewrite H9'; tauto.
      destruct H1. rewrite H9'; auto. apply Classifier1.
      destruct (classic (z = y)). exists n1. apply Classifier2. right; auto.
      assert (z ∈ ran[T]). rewrite H7. apply Classifier1. split; auto.
      applyClassifier1 H8. destruct H8 as [x0]. exists x0. apply Classifier2. left. 
      assert(x0 ∈ dom[T]). apply Classifier1. exists z; auto.
      rewrite H6' in H9. applyClassifier1 H9. split; auto. symmetry.
      apply f_x_T; auto.
Qed.

(* 两个一一函数, 值域的包含关系与定义域一致 *)
Fact Fact9_6g : ∀ {X : Type} (f g : @set (@prod nat X)) n m,
  Function1_1 f -> Function1_1 g -> dom[f] = \{ λ u, (u <= n)%nat \}
  -> dom[g] = \{ λ u, (u <= m)%nat \} -> ran[f] ⊂ ran[g] -> (n <= m)%nat.
Proof.
  intros. destruct H0, H. destruct(classic (n <= m)%nat) as [Hc|Hc]; auto.
  assert(Function1_1 (g﹣¹)).
  { split; auto. red. intros. repeat applyClassifier2 H6.
    repeat applyClassifier2 H7. apply (H0 x); auto. }
  assert(Function1_1 ((g ﹣¹)|[ran[f]])). apply RestrictFun1_1; auto.
  assert(Function1_1 (((g ﹣¹)|[ran[f]])◦ f)).
  { apply Comp_Fun_P4; split; auto. split; auto. } clear H6. destruct H7.
  pose proof (RestrictFun (g﹣¹) ran[f]). apply H9 in H4 as H9'.
  clear H9. destruct H9' as [_[]]. set(h:= (g ﹣¹ |[ran[f]] ◦ f)).
  assert(dom[h] = \{λ u,(u <= n)%nat\}).
  { apply AxiomI; split; intros. 
    - applyClassifier1 H11. destruct H11. applyClassifier2 H11.
      destruct H11 as [y[]]. rewrite <- H1. apply Classifier1. exists y; auto.
    - apply Classifier1. rewrite <- H1 in H11. applyClassifier1 H11.
      destruct H11 as [y]. exists (g﹣¹|[ran[f]])[y]. apply Classifier2.
      exists y. split; auto. apply x_fx_T; auto.
      cut(ran[f] ∩ ran[g] = ran[f]); intros. pose proof (Inverse_P1 g).
      destruct H13. rewrite H9, H13, H12. apply Classifier1; exists z; auto.
      apply AxiomI. split; intros. applyClassifier1 H12. tauto. apply Classifier1.
      split; auto. }
  assert(ran[h] ⊂ \{λ u,(u <= m)%nat\}).
  { red. intros. rewrite <- H2. applyClassifier1 H12. destruct H12.
    applyClassifier2 H12. destruct H12 as [y[]]. applyClassifier1 H13.
    destruct H13. applyClassifier2 H13. apply Classifier1. exists y; auto. }
  assert(ran[ h] ⊂ \{ λ u,(u < S n)%nat \}).
  { red. intros. apply H12 in H13. applyClassifier1 H13. apply Classifier1. lia. }
  assert(ran[ h] <> \{ λ u,(u < S n)%nat \}).
  { intro. cut(n ∈ \{ λ u,(u < S n)%nat \}); intros. rewrite <- H14 in H15.
    apply H12 in H15. applyClassifier1 H15. lia. apply Classifier1; lia. }
  apply (drawerPrinciple (S n)) in H13; auto. elim H13.
  exists h; split; auto. split; auto. rewrite H11. 
  apply AxiomI; split; intros; apply Classifier1; applyClassifier1 H15; lia. 
Qed.

Fact Fact9_6h : ∀ (T : Seq) n m z, Function1_1 T
  -> dom[T] = \{ λ u, (u <= n)%nat \} -> [m,z] ∈ T -> (n > 0)%nat
  -> ∃ T', T' = \{\ λ u v, ((u < m)%nat /\ v = T[u])
                         \/ ((m <= u < n)%nat /\ v = T[S u]) \}\
    /\ Function1_1 T' /\ dom[T'] = \{ λ u, (u <= n - 1)%nat \}
    /\ ran[T'] = ran[T] — [z].
Proof.
  intros. exists \{\λ u v,(u < m)%nat /\ v = T[u] \/ (m <= u < n)%nat /\ 
   v = T[S u]\}\. destruct H. split; auto.
   assert(I1: m ∈ dom[T]). apply Classifier1; exists z; auto.
   rewrite H0 in I1. applyClassifier1 I1.
   assert(I2 : Function \{\ λ u v, ((u < m)%nat /\ v = T[u])
     \/ ((m <= u < n)%nat /\ v = T[S u]) \}\).
   { red; intros. repeat applyClassifier2 H4; repeat applyClassifier2 H5;
     destruct H4 as [[]|[]], H5 as [[]|[]];[lra|lia|lia|lra]. }
   assert(I3 : ∀ x y z, x = T[y] -> x = T[z]
     -> (y <= n)%nat -> (z <= n)%nat -> y=z).
   { intros. apply (H3 x); [rewrite H4|rewrite H5]; apply Classifier2;
     apply x_fx_T; auto; rewrite H0; apply Classifier1; lia. }
   repeat split; auto. 
   - red; intros. repeat applyClassifier2 H4; repeat applyClassifier2 H5;
     destruct H4 as [[]|[]], H5 as [[]|[]].
     apply (I3 x); auto; lia. apply (I3 x y (S z0) H6) in H7; auto; lia.
     apply (I3 x (S y) z0 H6) in H7; auto; lia. 
     apply (I3 x (S y) (S z0) H6) in H7; auto; lia. 
   - apply AxiomI; split; intros; apply Classifier1; applyClassifier1 H4.
     + destruct H4. applyClassifier2 H4; destruct H4; lia.
     + destruct(classic (z0 < m)%nat);[exists T[z0]|exists T[S z0]];
       apply Classifier2; [left|right]; auto. split; [lia|auto].
   - apply AxiomI; split; intros; applyClassifier1 H4; apply Classifier1;
     destruct H4.
     + applyClassifier2 H4. split. apply Classifier1.
       destruct H4 as [[]|[]]; [exists x|exists (S x)]; subst z0; apply x_fx_T;
       auto; rewrite H0; apply Classifier1; lia. apply f_x_T in H1; auto.
       destruct H4 as [[]|[]]; apply Classifier1; intro; applyClassifier1 H6; subst z.
       apply (I3 z0 x m) in H5; auto; lia. apply (I3 z0 (S x) m) in H5; auto; lia.
     + applyClassifier1 H4. destruct H4. destruct (classic (x < m)%nat);
       [exists x|exists (pred x)]; apply Classifier2. left; split; auto. symmetry.
       apply f_x_T; auto. applyClassifier1 H5. assert(x <> m).
       { intro. apply H5. apply Classifier1. subst x. apply (H m); auto. }
       assert(x ∈ dom[T]). apply Classifier1; exists z0; auto. rewrite H0 in H8.
       applyClassifier1 H8. right. split. lia. replace (S (Init.Nat.pred x)) with x.
       apply f_x_T in H4; auto. lia.
Qed.

(* 两个1-1函数, 元素个数分别为n m, 则值域的并的元素个数小于等于S (n + m) *)
Fact Fact9_6i : ∀ (T1 T2 T : Seq) n m k, Function1_1 T1 -> Function1_1 T2
  -> Function1_1 T -> dom[T1] = \{ λ u, (u <= n)%nat \}
  -> dom[T2] = \{ λ u, (u <= m)%nat \} -> dom[T] = \{ λ u, (u <= k)%nat \}
  -> ran[T] = ran[T1] ∪ ran[T2] -> (k <= S (n + m))%nat.
Proof.
  intros. generalize dependent T2. generalize dependent T.
  generalize dependent k. induction m; intros.
  - assert(0%nat ∈ dom[T2]). rewrite H3; apply Classifier1; lia.
    applyClassifier1 H6. destruct H6 as [a].
    assert(ran[T2] = [a]). { apply AxiomI; split; intros; apply Classifier1;
    applyClassifier1 H7. destruct H7. cut(x ∈ dom[T2]); intros. rewrite H3 in H8.
    applyClassifier1 H8. assert (H8' : (x = 0)%nat). lia. subst x. destruct H0.
    apply (H0 0%nat); auto. apply Classifier1; exists z; auto. subst z.
    exists 0%nat; auto. }
    destruct(classic (a ∈ ran[T1])) as [Hc|Hc].
    + assert(ran[T1] ∪ ran[T2] = ran[T1]).
      { rewrite H7. apply AxiomI; split; intros. applyClassifier1 H8.
        destruct H8; auto. applyClassifier1 H8; subst a; auto.
        apply Classifier1; left; auto. } rewrite H8 in H5.
      apply (Fact9_6g T T1 k n H1 H) in H4; auto. lia.
      red. intros. rewrite <- H5; auto.
    + apply (Fact9_6d T1 a n ran[T1]) in H; auto. destruct H as [H[]].
      apply (Fact9_6g T (T1 ∪ [[S n, a]]) k (S n) H1) in H4; auto. lia.
      rewrite H9. red. intros. rewrite <- H7, <- H5; auto. 
  - destruct(classic (k = 0%nat)). lia.
    destruct(classic (ran[T2] ⊂ ran[T1])) as [Hc|Hc].
    + assert(ran[T1] ∪ ran[T2] = ran[T1]).
      { apply AxiomI; split; intros. applyClassifier1 H7; destruct H7; auto.
        apply Classifier1. left; auto. } rewrite H7 in H5.
      apply (Fact9_6g T T1 k n H1 H) in H4; auto. lia.
      red. intros. rewrite <-H5; auto. 
    + assert(∃ a, a ∈ ran[T2] /\ ~ (a ∈ ran[T1])).
      { apply NNPP. intro. elim Hc. red. intros. red in H6. apply NNPP. intro.
        apply H7. exists z. split; try tauto. } destruct H7 as [a[]].
      applyClassifier1 H7. destruct H7 as [x].
    apply (Fact9_6h T2 (S m) x a) in H0 as H0'; auto; [ |lia].
    destruct H0' as [T2'[L1[L2 [L3 L4]]]]. replace (S m -1)%nat with m in L3;
    [ |lia]. assert(a ∈ ran[T]). 
    { rewrite H5. apply Classifier1; right. apply Classifier1. exists x; auto. }
    applyClassifier1 H9. destruct H9 as [x']. assert(x' ∈ dom[T]).
    apply Classifier1; exists a; auto. apply (Fact9_6h T k x' a) in H1 as H1';
    auto; [ |lia]. destruct H1' as [T'[I1[I2[I3 I4]]]].
    apply (IHm (k-1)%nat T' I2 I3 T2') in L3; auto. lia.
    rewrite I4. rewrite L4. apply AxiomI; split; intros; apply Classifier1.
    applyClassifier1 H11.
    * destruct H11. rewrite H5 in H11. applyClassifier1 H11. destruct H11.
      left; auto. right. apply Classifier1. split; auto.
    * applyClassifier1 H11. rewrite H5. split. apply Classifier1. destruct H11.
      left; auto. applyClassifier1 H11. right; tauto. destruct H11. apply Classifier1.
      intro. applyClassifier1 H12. subst z; auto. applyClassifier1 H11; tauto.
Qed.

(******************************************************************************)



(* 函数在D上的上下确界 *)
(* 用c选择可以使上和与下和的定义简便 *)
Definition sup_fD f (D : @set R) := c (\{ λ u, sup (ran[f|[D]]) u \}).

(* f在D上的上确界就是限制在D上值域的上确界 *)
Corollary sup_Coro_1 : ∀ f D, DBoundedFun f D -> NotEmpty D
  -> sup (ran[f|[D]]) (sup_fD f D).
Proof.
  intros. destruct H as [H[H1[]]].
  - assert (NotEmpty (ran[f|[D]])).
    { destruct H0. exists f[x0]. apply Classifier1. exists x0.
      apply Classifier1; split. apply x_fx_T; auto.
      apply Classifier2; split; auto. apply Classifier1; auto. }
    apply Sup_principle in H3 as [].
    assert (NotEmpty \{ λ u, sup (ran[f|[D]]) u \}).
    { exists x0. apply Classifier1; auto. }
    apply Axiomc in H4. applyClassifier1 H4; auto.
    exists x. unfold Upper; intros. applyClassifier1 H4. destruct H4.
    applyClassifier1 H4. destruct H4. apply f_x_T in H4; auto. rewrite <-H4.
    applyClassifier2 H5. destruct H5. apply H2 in H5.
    destruct (Abs_neg_pos f[x1]). lra.
Qed.

(* 子集的上确界小于等于父集的上确界 *)
Corollary sup_Coro_2 : ∀ f D1 D2, NotEmpty D1 -> D1 ⊂ D2 -> DBoundedFun f D2
  -> (sup_fD f D1) <= (sup_fD f D2).
Proof.
  intros. assert (NotEmpty D2). { destruct H. exists x; auto. }
  assert (DBoundedFun f D1).
  { destruct H1 as [H1[H3[]]]. split; auto. split; eauto. red; auto. }
  destruct (sup_Coro_1 f D1 H3 H). destruct (sup_Coro_1 f D2 H1 H2).
  destruct (Rle_or_lt (sup_fD f D1) (sup_fD f D2)); auto.
  apply H5 in H8 as [x[]]. assert (x ∈ ran[f|[D2]]).
  { apply Classifier1 in H8 as []. apply Classifier1 in H8 as [].
    apply Classifier1. exists x0. apply Classifier1; split; auto.
    applyClassifier2 H10. destruct H10 as []. apply Classifier2; split; auto. }
  apply H6 in H10. exfalso. lra.
Qed.

Definition inf_fD f (D : @set R) := c (\{ λ u, inf (ran[f|[D]]) u \}).

(* f在D上的下确界就是限制在D上值域的下确界 *)
Corollary inf_Coro_1 : ∀ f D, DBoundedFun f D -> NotEmpty D
  -> inf (ran[f|[D]]) (inf_fD f D).
Proof.
  intros. destruct H as [H[H1[]]].
  - assert (NotEmpty (ran[f|[D]])).
    { destruct H0. exists f[x0]. apply Classifier1. exists x0.
      apply Classifier1; split. apply x_fx_T; auto.
      apply Classifier2; split; auto. apply Classifier1; auto. }
    apply Sup_inf_principle in H3 as [_].
    assert (∃ L, Lower ran[f|[D]] L).
    { exists (-x). unfold Lower; intros. applyClassifier1 H4. destruct H4.
    applyClassifier1 H4. destruct H4. apply f_x_T in H4; auto. rewrite <-H4.
    applyClassifier2 H5. destruct H5. apply H2 in H5.
    destruct (Abs_neg_pos f[x1]). lra. }
    assert (NotEmpty \{ λ u, inf (ran[f|[D]]) u \}).
    { apply H3 in H4 as []. exists x0. apply Classifier1; auto. }
    apply Axiomc in H5. applyClassifier1 H5; auto.
Qed.

(* 父集的下确界小于等于子集的下确界 *)
Corollary inf_Coro_2 : ∀ f D1 D2, NotEmpty D1 -> D1 ⊂ D2 -> DBoundedFun f D2
  -> (inf_fD f D2) <= (inf_fD f D1).
Proof.
  intros. assert (NotEmpty D2). { destruct H. exists x; auto. }
  assert (DBoundedFun f D1).
  { destruct H1 as [H1[H3[]]]. split; auto. split; eauto. red; auto. }
  destruct (inf_Coro_1 f D1 H3 H). destruct (inf_Coro_1 f D2 H1 H2).
  destruct (Rle_or_lt (inf_fD f D2) (inf_fD f D1)); auto.
  apply Rlt_gt,H5 in H8 as [x[]]. assert (x ∈ ran[f|[D2]]).
  { apply Classifier1 in H8 as []. apply Classifier1 in H8 as [].
    apply Classifier1. exists x0. apply Classifier1; split; auto.
    applyClassifier2 H10. destruct H10 as []. apply Classifier2; split; auto. }
  apply H6 in H10. exfalso. lra.
Qed.

(* f在D上取值介于上下确界之间 *)
Corollary sup_inf_Coro_1 : ∀ f D x, DBoundedFun f D -> NotEmpty D
  -> x ∈ D -> (inf_fD f D) <= f[x] <= (sup_fD f D).
Proof.
  intros. pose proof H. pose proof H.
  apply sup_Coro_1 in H2; auto. apply inf_Coro_1 in H3; auto.
  destruct H2 as [H2 _], H3 as [H3 _]. destruct H as [H[]].
  assert (f[x] ∈ ran[f|[D]]).
  { apply Classifier1. exists x. apply Classifier1; split. apply x_fx_T; auto.
    apply Classifier2; split; auto. apply Classifier1; auto. }
  split; [apply Rge_le,H3|apply H2]; auto.
Qed.

(* 下确界 小于等于 上确界 *)
Corollary sup_inf_Coro_2 : ∀ f D, DBoundedFun f D -> NotEmpty D
  -> (inf_fD f D) <= (sup_fD f D).
Proof.
  intros. pose proof H0. destruct H0. apply (sup_inf_Coro_1 f D x) in H1; auto. lra.
Qed.

(* 若上下确界相等, f为常量函数 *)
Corollary sup_inf_Coro_3 : ∀ f D, DBoundedFun f D -> (inf_fD f D) = (sup_fD f D)
  -> (∀ x, x ∈ D -> f[x] = (inf_fD f D)).
Proof.
  intros. destruct H as [H[H2[M]]]. assert (NotEmpty D). red; eauto.
  apply (sup_inf_Coro_1 f D) in H1; auto. rewrite H0 in H1. rewrite H0. lra.
  split; eauto.
Qed.


(* f关于分割T的上和 *)
Definition Up_sum f (T : Seq)(n : nat) :=
  (Σ \{\ λ i s, s = (sup_fD f (\[T[i], T[S i]\])) * (T[S i]- T[i]) \}\ n).

(* f关于分割T的下和 *)
Definition Low_sum f (T : Seq)(n : nat) :=
  (Σ \{\ λ i s, s = (inf_fD f (\[T[i], T[S i]\])) * (T[S i]- T[i]) \}\ n).

(* 下和小于等于上和 *)
Corollary Up_Low_sum_Coro_1 : ∀ f T a b n, DBoundedFun f (\[a, b\])
  -> Seg T a b (S n) -> (Low_sum f T n) <= (Up_sum f T n).
Proof.
  intros. unfold Low_sum, Up_sum. apply Rge_le. apply Σ_Fact3. intros.
  repeat rewrite FunValue. apply Rmult_ge_compat_r. left.
  apply Rgt_minus; apply (Seg_StrictlyIncrease_a T a b  (S n) H0 i (S i)); lia.
  assert(DBoundedFun f (\[T[i], T[S i]\])). 
  { apply (Seg_DBounded _ _ a b n); auto. }
  assert(∃x, x ∈ (\[T[i], T[S i]\])). { exists T[i]. apply Classifier1.
  split. lra. left. apply (Seg_StrictlyIncrease_a T a b  (S n) H0 i (S i)); lia. }
  destruct H3. apply (sup_inf_Coro_1 f (\[T[i], T[S i]\]) x) in H2; auto.
  lra. red; exists x ; auto.  
Qed.

(* 上和是全体积分和的上界 *) 
Corollary Up_Low_sum_Coro_2: ∀ f T ξ a b n, Seg T a b (S n) -> SegPoints T ξ (S n) 
  -> DBoundedFun f (\[a,b\])
  -> (Up_sum f T n) >= (IntegralSum f T n ξ).
Proof.
  intros. unfold Up_sum. pose proof H as J1. 
  destruct H as [H[H2[H3[]]]]. 
  assert (L3 : ∀ i, (i <= n)%nat -> f[ξ[i]] <= (sup_fD f (\[T[i], T[S i]\]))).
  { intros. assert (NotEmpty (\[T[i], T[S i]\])).
    { exists T[i]. apply Classifier1. split. lra. left. apply H4. lia. }
    apply (sup_inf_Coro_1 f _ (ξ[i])) in H7 as []; auto. 
    apply (Seg_DBounded _ T a b n); auto. red in H0. apply Classifier1.
    cut((i < S n)%nat); intros. apply H0 in H8. lra. lia. }
  apply Σ_Fact3. intros. repeat rewrite FunValue. assert((T [S i] > T [i])).
  apply H4; lia. apply Rmult_ge_compat_r. lra. apply L3 in H6; lra.
Qed.

(* 下和是全体积分和的下界 *) 
Corollary Up_Low_sum_Coro_3 : ∀ f T ξ a b n, Seg T a b (S n) -> SegPoints T ξ (S n) 
  -> DBoundedFun f (\[a,b\])
  -> (Low_sum f T n) <= (IntegralSum f T n ξ).
Proof.
  intros. unfold Low_sum. pose proof H as J1. 
  destruct H as [H[H2[H3[]]]]. 
  assert (L3 : ∀ i, (i <= n)%nat -> f[ξ[i]] >= (inf_fD f (\[T[i], T[S i]\]))).
  { intros. assert (NotEmpty (\[T[i], T[S i]\])).
    { exists T[i]. apply Classifier1. split. lra. left. apply H4. lia. }
    apply (sup_inf_Coro_1 f _ (ξ[i])) in H7 as []. lra. 
    apply (Seg_DBounded _ T a b n); auto. red in H0. apply Classifier1.
    cut((i < S n)%nat); intros. apply H0 in H8. lra. lia. }
  apply Rge_le. apply Σ_Fact3. intros. 
  repeat rewrite FunValue. assert((T [S i] > T [i])).
  apply H4; lia. apply Rmult_ge_compat_r. lra. apply L3 in H6; lra.
Qed.

Lemma Lemma9_6_1a : ∀ n A B C, Σ \{\ λ i m, m = (A i) - B * (C i) \}\ n
  = Σ \{\ λ i m, m = (A i) \}\ n - B * Σ \{\ λ i m, m = (C i) \}\ n.
Proof.
  intros. induction n. simpl.
  - repeat rewrite FunValue. auto.
  - simpl. rewrite IHn.
  assert (\{\ λ i m, m = (A i) - B * (C i) \}\[S n]
    = \{\ λ i m, m = (A i) \}\[S n] - B * \{\ λ i m, m = (C i) \}\[S n]).
  { repeat rewrite FunValue. auto. }
  rewrite H. lra.
Qed.

Lemma Lemma9_6_1b : ∀ n A B C, Σ \{\ λ i m, m = (A i) + B * (C i) \}\ n
  = Σ \{\ λ i m, m = (A i) \}\ n + B * Σ \{\ λ i m, m = (C i) \}\ n.
Proof.
  intros. induction n. simpl.
  - repeat rewrite FunValue. auto.
  - simpl. rewrite IHn.
  assert (\{\ λ i m, m = (A i) + B * (C i) \}\[S n]
    = \{\ λ i m, m = (A i) \}\[S n] + B * \{\ λ i m, m = (C i) \}\[S n]).
  { repeat rewrite FunValue. auto. }
  rewrite H. lra.
Qed.

Lemma Lemma9_6_1c : ∀ T n a b, Seg T a b (S n) ->
 Σ \{\ λ i m, m = T [S i] - T [i] \}\ n = b - a .
Proof.
  intros. red in H. destruct H as [H[H1[H2[H3 [H4 H4']]]]].
  assert  ( ∀ u k, u[S k] - u[O] =
    Σ \{\ λ i v, v = u[S i] - u[i] \}\ k). 
  { intros u m. induction m as [|m IHm].
    - simpl. rewrite FunValue. reflexivity.
    - simpl. rewrite FunValue. rewrite <- IHm. field. }
   generalize (H0 T n); intros H5.
   rewrite H4', H4 in H5. auto.
Qed.

(* 性质1 上和是全体积分和的上确界 *)
Property Property9_6_1a : ∀ f T a b n, Seg T a b (S n)
  -> DBoundedFun f (\[a, b\]) -> sup (\{ λ u, ∃ ξ, SegPoints T ξ (S n)
    /\ u = IntegralSum f T n ξ \}) (Up_sum f T n).
Proof.
  intros. red. split. 
  - red. intros. applyClassifier1 H1. destruct H1 as [ξ[]].  
    rewrite H2. apply Rge_le. apply (Up_Low_sum_Coro_2 f T _ a b _); auto.  
  - intros s H2.
    assert(∀ i, (i < S n)%nat 
      -> sup (ran[f|[(\[T[i], T[S i]\])]]) (sup_fD f (\[T[i], T[S i]\]))).
    { intros. apply sup_Coro_1. apply (Seg_DBounded f T a b n); auto. lia.
      exists T[i]. apply Classifier1. split. lra. left.
      apply (Seg_StrictlyIncrease_a _ a b (S n)); auto; lia. }
    assert (J2: ∃ε : R, ε = Up_sum f T n - s /\ ε > 0). 
    { exists (Up_sum f T n - s). split; lra. } 
    destruct J2 as [ε[J2 H3]]. 
    assert (∀ i, (i < S n)%nat 
    -> ∃x ,f[x] > sup_fD f (\[T[i], T[S i]\]) - ε / (b -a) 
    /\ x ∈ (\[T[i], T[S i]\])).
    { intros. apply H1 in H4.  destruct H4 as []. 
      assert(ε / (b - a) > 0). { apply Rdiv_lt_0_compat; auto.
      apply Seg_a_less_b in H; lra. }
      assert (sup_fD f (\[T[i], T [S i]\])- ε / (b - a) 
      < sup_fD f (\[T [i], T[S i] \])). lra. apply H5 in H7 as [x0[]].
      applyClassifier1 H7. destruct H7 as [x]. applyClassifier1 H7. destruct H7.
      exists x. assert(f[x] = x0). destruct H0 as []. apply f_x_T; auto.
      split. lra. applyClassifier1 H9. destruct H9 as [x1[y[H9[H11 _]]]]. 
      apply ProdEqual in H9 as []. subst x1. auto. }
   set (ξ := \{\ λ i v,(i <= n)%nat /\ v = c ((\[T[i], T[S i]\]) ∩
   \{ λ u, f[u] > (sup_fD f (\[T[i], T[S i]\]) - ε/(b - a)) \}) \}\).
   assert(Function ξ). { red. intros. applyClassifier2 H6.
   applyClassifier2 H5. destruct H6 as [], H5 as []. lra. }
   assert(∀k, (k < S n)%nat -> ξ [k] = c(\[T[k], T[S k]\]
     ∩ \{ λ u, f[u] > sup_fD f (\[T[k], T[S k]\]) - ε / (b - a) \})).
   { intros. apply f_x_T; auto. apply Classifier2. split; auto. lia.   }
   assert(∀k, (k < S n)%nat -> NotEmpty (\[ T[k], T [S k] \]
     ∩ \{ λ u,f [u] > sup_fD f (\[T[k], T[S k]\]) - ε / (b - a) \})).
   { intros. apply H4 in H7 as [x[]]. exists x. apply Classifier1. split; auto. }
   exists (Σ \{\ λ i m, m =f [ξ[i]] * (T [S i] - T [i])\}\ n).
   split. apply Classifier1. exists ξ. split. red. intros.
   apply H7 in H8 as H8'. apply H6 in H8 as H6'. apply Axiomc in H8'.
   rewrite <- H6' in H8'. applyClassifier1 H8'. destruct H8'.
   applyClassifier1 H9. lra. auto.
   assert (∀ i,(i < S n)%nat -> f[ξ[i]] > sup_fD f (\[T[i], T[S i]\]) - ε/(b-a)). 
   { intros. apply H7 in H8 as H7'. apply H6 in H8 as H6'. apply Axiomc in H7'.
   rewrite <-H6' in H7'. applyClassifier1 H7'. destruct H7'.
   applyClassifier1 H10; auto. } clear H4 H6.
   assert  (∀ i, (i < S n)%nat -> f[ξ[i]] * (T[S i] - T[i]) > 
   (sup_fD f (\[T[i], T[S i]\]) - ε / (b - a)) * (T[S i] - T[i])).
   { intros. apply H8 in H4 as H9'. apply Rmult_gt_compat_r; auto.
   apply Rgt_minus. apply (Seg_StrictlyIncrease_a _ a b (S n)); auto. lia. }
   assert(Σ \{\ λ i m, m = f[ξ[i]] * (T[S i] - T[i])\}\ n > Σ \{\ λ i m, 
   m = (sup_fD f (\[T[i], T[S i]\]) - ε / (b - a)) * (T[S i] - T[i])\}\ n ).
   { apply Σ_Fact4. intros. repeat rewrite FunValue. apply H4; lia. } 
   assert  (Σ \{\ λ i m,  m = (sup_fD f (\[T[i], T[S i]\]) - ε / (b - a)) 
   * (T[S i] - T[i])\}\ n = Σ \{\ λ i m,  m = (sup_fD f (\[T[i], T[S i]\]))
   *(T[S i] - T[i])\}\ n - (ε / (b - a)) * Σ\{\ λ i m, m = (T[S i] - T[i])\}\ n).
   { assert(\{\ λ i m, m = (sup_fD f (\[T[i], T[S i]\]) - ε / (b - a)) * 
      (T[S i] - T[i]) \}\ = \{\ λ i m, m = (sup_fD f (\[T[i], T[S i]\])) 
      * (T[S i] - T[i]) - ε / (b - a) * (T[S i] - T[i]) \}\ ).
     { apply AxiomI. split; intros;
       applyClassifier1 H9; destruct H9 as [x[y[H16 H17]]];
       apply Classifier1; exists x, y; split; auto; rewrite H17; lra. }  
   rewrite H9. rewrite Lemma9_6_1a. auto. }
   assert  (Σ \{\ λ i m, m = T [S i] - T [i] \}\ n = b - a).
   { apply Lemma9_6_1c. auto. }
   rewrite H10 in H9. clear H10. 
   assert(ε / (b - a) * (b - a) = ε).
   { unfold Rdiv. rewrite Rmult_assoc. rewrite (Rinv_l (b - a)). lra. 
     apply Seg_a_less_b in H. lra. }
   rewrite H10 in H9. assert(s = Up_sum f T n- ε). lra.
   unfold Up_sum in H11. rewrite <- H11 in H9. lra. 
Qed.

(* 下和是全体积分和的下确界 *)
Property Property9_6_1b : ∀ f T a b n, Seg T a b (S n)
  -> DBoundedFun f (\[a, b\]) -> inf (\{ λ u, ∃ ξ, SegPoints T ξ (S n)
    /\ u = IntegralSum f T n ξ \}) (Low_sum f T n).
Proof.
  intros. red. split. 
  - red. intros. applyClassifier1 H1. destruct H1 as [ξ[]].  
    rewrite H2. apply Rle_ge. apply (Up_Low_sum_Coro_3 _ _ _ a b _); auto.  
  - intros s H2.
    assert(∀ i, (i < S n)%nat 
      -> inf (ran[f|[(\[T[i], T[S i]\])]]) (inf_fD f (\[T[i], T[S i]\]))).
    { intros. apply inf_Coro_1. apply (Seg_DBounded f T a b n); auto. lia.
      exists T[i]. apply Classifier1. split. lra. left.
      apply (Seg_StrictlyIncrease_a _ a b (S n)); auto; lia. }
    assert (J2: ∃ε : R, ε = s - Low_sum f T n /\ ε > 0). 
    { exists (s - Low_sum f T n). split; lra. } 
    destruct J2 as [ε[J2 H3]]. 
    assert (∀ i, (i < S n)%nat 
    -> ∃x ,f[x] < inf_fD f (\[T[i], T[S i]\]) + ε / (b -a) 
    /\ x ∈ (\[T[i], T[S i]\])).
    { intros. apply H1 in H4.  destruct H4 as []. 
      assert(ε / (b - a) > 0). { apply Rdiv_lt_0_compat; auto.
      apply Seg_a_less_b in H; lra. }
      assert(inf_fD f (\[T[i], T [S i]\])+ ε / (b - a) 
      > inf_fD f (\[T [i], T[S i] \])). lra. apply H5 in H7 as [x0[]].
      applyClassifier1 H7. destruct H7 as [x]. applyClassifier1 H7. destruct H7.
      exists x. assert(f[x] = x0). destruct H0 as []. apply f_x_T; auto.
      split. lra. applyClassifier1 H9. destruct H9 as [x1[y[H9[H11 _]]]]. 
      apply ProdEqual in H9 as []. subst x1. auto. }
   set (ξ := \{\ λ i v,(i <= n)%nat /\ v = c ((\[T[i], T[S i]\]) ∩
   \{ λ u, f[u] < (inf_fD f (\[T[i], T[S i]\]) + ε/(b - a)) \}) \}\).
   assert(Function ξ). { red. intros. applyClassifier2 H6.
   applyClassifier2 H5. destruct H6 as [], H5 as []. lra. }
   assert(∀k, (k < S n)%nat -> ξ [k] = c (\[ T[k], T [S k] \]
     ∩ \{ λ u,f [u] < inf_fD f (\[T[k], T[S k]\]) + ε / (b - a) \})).
   { intros. apply f_x_T; auto. apply Classifier2. split; auto. lia.   }
   assert(∀k, (k < S n)%nat -> NotEmpty (\[ T[k], T [S k] \]
     ∩ \{ λ u,f [u] < inf_fD f (\[T[k], T[S k]\]) + ε / (b - a) \})).
   { intros. apply H4 in H7 as [x[]]. exists x. apply Classifier1. split; auto. }
   exists (Σ \{\ λ i m, m =f [ξ[i]] * (T [S i] - T [i])\}\ n).
   split. apply Classifier1. exists ξ. split. red. intros.
   apply H7 in H8 as H8'. apply H6 in H8 as H6'. 
   apply Axiomc in H8'. rewrite <- H6' in H8'. applyClassifier1 H8'.
   destruct H8'. applyClassifier1 H9. lra. auto.  
   assert (∀ i,(i < S n)%nat -> f[ξ[i]] < inf_fD f (\[T[i], T[S i]\]) + ε/(b-a)). 
   { intros. apply H7 in H8 as H7'. apply H6 in H8 as H6'. apply Axiomc in H7'.
   rewrite <- H6' in H7'. applyClassifier1 H7'. destruct H7'. 
   applyClassifier1 H10; auto. } clear H4 H6.
   assert  (∀i : nat,(i < S n)%nat ->  f [ξ[i]] * (T[S i] - T[i]) <
   (inf_fD f (\[T[i], T[S i]\]) + ε / (b - a)) * (T[S i] - T[i])).
   { intros. apply H8 in H4 as H9'. apply Rmult_gt_compat_r; auto.
   apply Rgt_minus. apply (Seg_StrictlyIncrease_a _ a b (S n)); auto. lia. }
   assert(Σ \{\ λ i m, m = f[ξ[i]] * (T[S i] - T[i])\}\ n < Σ \{\ λ i m, 
   m = (inf_fD f (\[T[i], T[S i]\]) + ε / (b - a)) * (T[S i] - T[i])\}\ n ).
   { apply Σ_Fact4. intros. repeat rewrite FunValue. apply H4; lia. } 
   assert  (Σ \{\ λ i m,  m = (inf_fD f (\[T[i], T[S i]\]) + ε / (b - a)) 
   * (T[S i] - T[i])\}\ n = Σ \{\ λ i m,  m = (inf_fD f (\[T[i], T[S i]\]))
   *(T[S i] - T[i])\}\ n + (ε / (b - a)) * Σ\{\ λ i m, m = (T[S i] - T[i])\}\ n).
   { assert(\{\ λ i m, m = (inf_fD f (\[T[i], T[S i]\]) + ε / (b - a)) * 
      (T[S i] - T[i]) \}\ = \{\ λ i m, m = (inf_fD f (\[T[i], T[S i]\])) 
      * (T[S i] - T[i]) + ε / (b - a) * (T[S i] - T[i]) \}\ ).
     { apply AxiomI. split; intros;
       applyClassifier1 H9; destruct H9 as [x[y[H16 H17]]];
       apply Classifier1; exists x, y; split; auto; rewrite H17; lra. }  
   rewrite H9. rewrite Lemma9_6_1b. auto. }
   assert  (Σ \{\ λ i m, m = T [S i] - T [i] \}\ n = b - a).
   { apply Lemma9_6_1c. auto. }
   rewrite H10 in H9. clear H10. 
   assert(ε / (b - a) * (b - a) = ε).
   { unfold Rdiv. rewrite Rmult_assoc. rewrite (Rinv_l (b - a)). lra. 
     apply Seg_a_less_b in H. lra. }
   rewrite H10 in H9. assert(s = Low_sum f T n + ε). lra.
   unfold Low_sum in H11. rewrite <- H11 in H9. lra.
Qed.

(* T'是T增加p个分割点后的分割, 就是说T'和T都是[a,b]上分割,
   T分割n份, T'分割n+p份, T的值域包含于T'  *)
Definition Sum_Seg (T T':Seq) (a b :R) (n p : nat) := Seg T a b n
  /\ Seg T' a b (n + p)%nat /\ ran[T] ⊂ ran[T'].

(* 性质二引理1: T'是T增加一个点的分割, T'与T存在如下关系 *)
Lemma Lemma9_6_2a : ∀ T T' a b n, Sum_Seg T T' a b n 1
  -> (∃ N, (0 < N <= n)%nat /\ (∀ u, (0 <= u < N)%nat -> T'[u] = T[u])
    /\ T'[N] = c (ran[T'] — ran[T])
    /\ (∀ u, (N < u <= S n)%nat -> T'[u] = T[(u - 1)%nat])).
Proof.
  intros. destruct H as [H[]]. assert (Function1_1 T /\ Function1_1 T')
  as [J1 J2]. { split; apply Seg_is_Function1_1; eauto. }
  pose proof H as H'. pose proof H0 as H0'.
  destruct H as [H[H2[H3[H4[]]]]], H0 as [H0[H7[H8[H9[]]]]].
  assert (n + 1 = S n)%nat. lia. rewrite H12 in *. clear H12.
  pose proof H1. apply Fact9_6b with (n := S n) in H12 as [y]; auto;
  [ |rewrite H3|rewrite H8]; try (apply AxiomI; split; intros;
  applyClassifier1 H13; apply Classifier1; lia).
  assert (y ∈ ran[T'] /\ y ∉ ran[T]) as [].
  { assert (y ∈ [y]). apply Classifier1; auto. rewrite <-H12 in H13.
    applyClassifier1 H13. destruct H13. applyClassifier1 H14; auto. }
  pose proof H13. applyClassifier1 H15. destruct H15 as [N].
  assert (N ∈ dom[T']). { apply Classifier1; eauto. }
  rewrite H8 in H16. applyClassifier1 H16.
  assert (∀ u, (0 <= u < N)%nat -> T'[u] = T[u]).
  { intros. induction u. rewrite H5,H10; auto. assert (0 <= u < N)%nat. lia.
    apply IHu in H18. destruct (Req_appart_dec T'[S u] T[S u]) as [H19 | []]; auto.
    - assert (T'[S u] ∈ ran[T'] — ran[T]).
      { apply Classifier1; split. apply Classifier1. exists (S u). apply x_fx_T; auto.
        rewrite H8. apply Classifier1. lia. apply Classifier1. intro. applyClassifier1 H20.
        destruct H20. assert (x ∈ dom[T]). { apply Classifier1; eauto. }
        apply f_x_T in H20; auto. rewrite H3 in H21. applyClassifier1 H21.
        assert (u < x)%nat.
        { assert (T'[u] < T'[S u]). { apply H9; lia. }
          rewrite H18,<-H20 in H22.
          apply (Seg_StrictlyIncrease_b T a b n) in H22; eauto. lia. }
        assert (x <= u)%nat.
        { rewrite <-H20 in H19. apply (Seg_StrictlyIncrease_b T a b n) in H19;
          eauto; lia. } lia. }
      rewrite H12 in H20. applyClassifier1 H20. apply f_x_T in H15; auto.
      rewrite <-H15 in H20. destruct H17.
      apply (Seg_StrictlyIncrease_a T' a b (S n)) in H21; try lia.
      rewrite H20 in H21. apply Rlt_irrefl in H21. destruct H21. repeat split; auto.
    - assert (T[S u] ∉ ran[T']).
      { intro. applyClassifier1 H20. destruct H20.
        assert (x ∈ dom[T']). { apply Classifier1; eauto. } rewrite H8 in H21.
        applyClassifier1 H21. apply f_x_T in H20; auto. assert (x <= u)%nat.
        { rewrite <-H20 in H19.
          apply (Seg_StrictlyIncrease_b T' a b (S n)) in H19; eauto; lia. }
        assert (T[u] < T[S u]). { apply H4. lia. } rewrite <-H18,<-H20 in H23.
        apply (Seg_StrictlyIncrease_b T' a b (S n)) in H23; eauto; lia. }
      elim H20. apply H1. apply fx_ran_T; auto. rewrite H3. apply Classifier1. lia. }
  assert (0 < N)%nat as J3.
  { apply Nat.neq_0_lt_0. intro. rewrite H18 in H15. apply f_x_T in H15; auto.
    elim H14. rewrite <-H15. replace T'[0%nat] with T'[0%nat]; auto.
    rewrite H10,<-H5. apply fx_ran_T; auto. rewrite H3. apply Classifier1. lia. }
  assert (∀ u, (N < u <= S n)%nat -> T'[u] = T[(u - 1)%nat]).
  { intros. induction u. destruct H18. apply Nat.nlt_0_r in H18. elim H18.
    assert ((0 <= N - 1 < N)%nat) as J4. lia.
    destruct (classic (u = N)) as [Hc|Hc].
    rewrite Hc in *. simpl. rewrite Nat.sub_0_r.
    destruct (Rtotal_order T'[S N] T[N]) as [H19 | []]; auto.
    assert (T[(N - 1)%nat] < T'[S N]).
    { rewrite <-H17; auto. apply (Seg_StrictlyIncrease_a T' a b (S n)); auto; lia. }
    assert (T'[S N] ∈ (ran[T'] — ran[T])).
    { apply Classifier1. split. apply Classifier1. exists (S N). apply x_fx_T; auto.
      rewrite H8. apply Classifier1; lia. apply Classifier1. intro. applyClassifier1 H21.
      destruct H21. assert (x ∈ dom[T]). { apply Classifier1; eauto. }
      apply f_x_T in H21; auto. rewrite <-H21 in H19,H20.
      apply (Seg_StrictlyIncrease_b T a b n) in H19,H20; eauto; try lia.
      rewrite H3 in H22. applyClassifier1 H22; auto. }
    rewrite H12 in H21. applyClassifier1 H21. rewrite <-H21 in H15.
    apply f_x_T,(Seg_Injective T' a b (S n)) in H15; eauto; try lia.
    assert (T[(N - 1)%nat] < T[N]).
    { apply (Seg_StrictlyIncrease_a T a b n); auto; lia. }
    rewrite <-H17 in H20; auto. assert (T[N] ∈ ran[T]).
    { apply Classifier1. exists N. apply x_fx_T; auto.
      rewrite H3. apply Classifier1; lia. }
    apply H1 in H21. applyClassifier1 H21. destruct H21. 
    assert (x ∈ dom[T']). { apply Classifier1; eauto. } rewrite H8 in H22.
    applyClassifier1 H22. apply f_x_T in H21; auto. rewrite <-H21 in H19,H20.
    apply (Seg_StrictlyIncrease_b T' a b (S n)) in H19,H20; eauto; try lia.
    assert (x = N). lia. apply f_x_T in H15; auto. elim H14.
    rewrite <-H15,<-H23,H21. apply Classifier1. exists N. apply x_fx_T; auto.
    rewrite H3. apply Classifier1; lia. assert (N < u <= S n)%nat. lia.
    pose proof H19. apply IHu in H20. simpl. rewrite Nat.sub_0_r.
    destruct (Rtotal_order T'[S u] T[u]) as [H21 | []]; auto.
    - assert (T[(u - 1)%nat] < T'[S u]). { rewrite <-H20. apply H9. lia. }
      assert (T'[S u] ∈ (ran[T'] — ran[T])).
      { apply Classifier1; split. apply fx_ran_T; auto. rewrite H8.
        apply Classifier1; lia. apply Classifier1. intro. applyClassifier1 H23.
        destruct H23. assert (x ∈ dom[T]). { apply Classifier1; eauto. }
        rewrite H3 in H24. applyClassifier1 H24. apply f_x_T in H23; auto.
        rewrite <-H23 in H21,H22.
        apply (Seg_StrictlyIncrease_b T a b n) in H21,H22; eauto; lia. }
      rewrite H12 in H23. applyClassifier1 H23. apply f_x_T in H15; auto.
      rewrite <-H15 in H23. apply (Seg_Injective T' a b (S n)) in H23; auto.
      exfalso. lia. lia.
    - assert (T[u] > T'[u]).
      { rewrite H20. apply (Seg_StrictlyIncrease_a T a b n); auto; lia. }
      assert (T[u] ∈ ran[T]).
      { apply fx_ran_T; auto. rewrite H3. apply Classifier1; lia. }
      apply H1 in H23. applyClassifier1 H23. destruct H23.
      assert (x ∈ dom[T']). { apply Classifier1; eauto. }
      rewrite H8 in H24. applyClassifier1 H24. apply f_x_T in H23; auto.
      rewrite <-H23 in H21,H22.
      apply (Seg_StrictlyIncrease_b T' a b (S n)) in H21,H22; eauto; lia. }
  exists N. repeat split; auto. assert (N <= n \/ N = S n)%nat. lia.
  destruct H19; auto. rewrite H19 in *. elim H14. apply f_x_T in H15; auto.
  rewrite <-H15. replace T'[S n] with T'[S n]; auto. rewrite H11,<-H6.
  apply fx_ran_T; auto. rewrite H3. apply Classifier1; lia. rewrite H12.
  rewrite ChooseSingleton. apply f_x_T in H15; auto.
Qed.

(* 性质二引理2 对分割T增加一个分割点得到T' 上和不等式 *)
Lemma Lemma9_6_2b : ∀ f T T' a b n, DBoundedFun f (\[a, b\])
  -> Sum_Seg T T' a b (S n) 1 -> ((Up_sum f T n) - ((sup_fD f (\[a, b\]))
    - (inf_fD f (\[a, b\]))) * (mold T (S n))) <= (Up_sum f T' (S n))
    <= (Up_sum f T n).
Proof.
  assert ((∀ T n, Σ T (S n) = Σ T n + T[S n])
    /\ (∀ T n, Σ T (S (S n)) = Σ T n + T[S n] + T[S (S n)])) as [J1 J2].
  { split; intros; simpl; auto. }
  assert ((∀ T T' n, (∀ m, (0 <= m <= n)%nat -> T[m] = T'[m])
    -> Σ T n = Σ T' n)) as J3.
  { intros. induction n. simpl. rewrite H; auto; lia.
    assert (∀ m, (0 <= m <= n)%nat -> T[m] = T'[m]). { intros. apply H. lia. }
    simpl. rewrite H, IHn; auto. lia. }
  assert (∀ T T' n N, (0 <= N <= n)%nat -> (∀ u, (0 <= u < N)%nat
    -> T'[u] = T[u]) -> (∀ u, ((S N) < u <= (S n))%nat -> T'[u] = T[(u - 1)%nat])
    -> Σ T n - Σ T' (S n) = T[N] - (T'[N] + T'[S N])) as G1.
  { intros. induction n. assert (N = 0%nat). lia. rewrite H2. simpl; auto.
    destruct (classic (N = S n)). rewrite H2, J1, J2. rewrite H2 in H0.
    assert (Σ T n = Σ T' n). { apply J3. intros. symmetry. apply H0. lia. }
    lra. assert (0 <= N <= n)%nat. lia. apply IHn in H3. rewrite J1, J1, <-H3.
    assert (T[S n] = T'[S (S n)]). { rewrite H1; auto. lia. } lra.
    intros. apply H1. lia. }
  intros f T T' a b n I H. assert (NotEmpty (\[a, b\])) as I0.
  { assert (a < b).
    { destruct H. pose proof H. destruct H as [_[_[_[_[]]]]]. rewrite <-H, <-H2.
      apply (Seg_StrictlyIncrease_a T a b (S n)); auto; lia. }
    exists ((a + b)/2). apply Classifier1; lra. }
  assert ((∀ n, \{\ λ i s, s = (sup_fD f (\[T[i], T[S i]\]))
    * (T[S i] - T[i]) \}\[n] = (sup_fD f (\[T[n], T[S n]\]))
    * (T[S n] - T[n])) /\ (∀ n, \{\ λ i s, s = (sup_fD f (\[T'[i], T'[S i]\]))
    * (T'[S i] - T'[i]) \}\[n] = (sup_fD f (\[T'[n], T'[S n]\]))
    * (T'[S n] - T'[n]))) as [J4 J5].
  { split; intros; apply f_x_T; try (apply Classifier2; auto); red; intros;
    applyClassifier2 H0; applyClassifier2 H1; rewrite H0,H1; auto. }
  pose proof H. apply Lemma9_6_2a in H0 as [N[H0[H1[]]]].
  assert ((Up_sum f T n) - (Up_sum f T' (S n))
    = (sup_fD f (\[T[(N - 1)%nat], T[N]\])) * (T[N] - T[(N - 1)%nat])
    - ((sup_fD f (\[T'[(N - 1)%nat], T'[N]\])) * (T'[N] - T'[(N - 1)%nat])
      + (sup_fD f (\[T'[N], T'[S N]\])) * (T'[S N] - T'[N]))).
  { unfold Up_sum. rewrite (G1 _ _ n (N - 1)%nat). rewrite J4, J5, J5.
    replace (S (N - 1)%nat) with N; auto. lia. lia. intros.
    rewrite J4, J5, H1, H1; auto. lia. lia. intros. rewrite J4, J5, H3, H3.
    replace (S u - 1)%nat with (S (u - 1))%nat; auto. lia. lia. lia. }
  assert (T'[(N - 1)%nat] < T'[N] < T'[S N]).
  { destruct H as [_[]]. replace (S n + 1)%nat with (S (S n)) in H; [ |lia].
    split; apply (Seg_StrictlyIncrease_a T' a b (S (S n))); auto; lia. }
  assert (a <= T'[(N - 1)%nat] /\ T'[S N] <= b) as [H5a H5b].
  { destruct H as [_[]]. pose proof H. destruct H7 as [_[_[_[_[]]]]].
    rewrite <-H7, <-H8. simpl. simpl in H.
    split; apply (Seg_Increase_a T' a b (S (n + 1)%nat)); eauto; lia. }
  rewrite H1, (H3 (S N)) in H5; try lia. rewrite H1 in H5a; [ |lia].
  rewrite H3 in H5b; [ |lia]. simpl in H5, H5b. rewrite Nat.sub_0_r in H5, H5b.
  assert ((T[N] - T[(N - 1)%nat]) = (T[N] - T'[N]) + (T'[N] - T[(N - 1)%nat])). lra.
  rewrite H6 in H4. rewrite (H1 (N - 1)%nat), (H3 (S N)) in H4; try lia.
  simpl in H4. rewrite Nat.sub_0_r in H4.
  assert ((Up_sum f T n) - (Up_sum f T' (S n))
  = ((sup_fD f (\[T[(N - 1)%nat], T[N]\])) - (sup_fD f (\[T[(N - 1)%nat], T'[N]\])))
  * (T'[N] - T[(N - 1)%nat]) + ((sup_fD f (\[T[(N - 1)%nat], T[N]\]))
  - (sup_fD f (\[T'[N], T[N]\]))) * (T[N] - T'[N])). lra.
  assert (∀ f D1 D, NotEmpty D1 -> NotEmpty D -> D1 ⊂ D
    -> DBoundedFun f D -> (sup_fD f D1) <= (sup_fD f D)).
  { intros. pose proof H11. apply sup_Coro_1 in H12 as []; auto.
    assert (DBoundedFun f0 D1).
    { destruct H11 as [H11[H14[]]]. repeat split; auto. red; intros; auto.
      exists x. intros; auto. }
    pose proof H14. apply sup_Coro_1 in H15 as []; auto.
    assert (ran[f0|[D1]] ⊂ ran[f0|[D]]).
    { red; intros. applyClassifier1 H17. destruct H17. applyClassifier1 H17. destruct H17.
      apply Classifier1. exists x. apply Classifier1. split; auto. applyClassifier2 H18.
      destruct H18. apply Classifier2. split; auto. }
    destruct (Rle_or_lt (sup_fD f0 D1) (sup_fD f0 D)); auto. pose proof H18.
    apply H16 in H19 as [x[]]. apply H17, H12 in H19. exfalso. lra. }
  assert (∀ f D1 D, D1 ⊂ D -> DBoundedFun f D -> DBoundedFun f D1).
  { intros. destruct H10 as [H10[]]. repeat split; auto. red; intros; auto.
    destruct H12. exists x. intros; auto. }
  assert ((sup_fD f (\[T[(N - 1)%nat], T'[N]\]))
    <= (sup_fD f (\[T[(N - 1)%nat], T[N]\]))).
  { apply H8. exists ((T[(N - 1)%nat] + T'[N])/2). apply Classifier1; lra.
    exists ((T[(N - 1)%nat] + T[N])/2). apply Classifier1; lra. red; intros.
    applyClassifier1 H10. apply Classifier1; lra. apply (H9 f _ (\[a, b\])); auto.
    red; intros. applyClassifier1 H10. destruct H10. apply Classifier1. lra. }
  assert ((sup_fD f (\[T'[N], T[N]\]))
    <= (sup_fD f (\[T[(N - 1)%nat], T[N]\]))).
  { apply H8. exists ((T'[N] + T[N])/2). apply Classifier1; lra.
    exists ((T[(N - 1)%nat] + T[N])/2). apply Classifier1; lra. red; intros.
    applyClassifier1 H11. apply Classifier1. lra. apply (H9 f _ (\[a, b\])); auto.
    red; intros. applyClassifier1 H11. apply Classifier1; lra. }
  assert (0 <= (Up_sum f T n - (Up_sum f T' (S n)))).
  { rewrite H7. apply Rplus_le_le_0_compat; apply Rmult_le_pos; lra. }
  assert ((sup_fD f (\[T[(N - 1)%nat], T[N]\])) <= (sup_fD f (\[a, b\]))).
  { apply H8; auto. exists ((T[(N - 1)%nat] + T[N])/2). apply Classifier1; lra.
    red; intros. applyClassifier1 H13. apply Classifier1; lra. }
  assert (∀ f D1 D, NotEmpty D1 -> NotEmpty D -> D1 ⊂ D
    -> DBoundedFun f D -> inf_fD f D <= sup_fD f D1).
  { intros. pose proof H17. apply (H9 _ D1) in H18; auto. pose proof H18 as H18a.
    apply sup_Coro_1 in H18 as []; auto. apply inf_Coro_1 in H17 as []; auto.
    assert (ran[f0|[D1]] ⊂ ran[f0|[D]]).
    { red; intros. applyClassifier1 H21. destruct H21. applyClassifier1 H21.
      destruct H21. apply Classifier1. exists x. apply Classifier1; split; auto.
      applyClassifier2 H22. destruct H22. apply Classifier2; auto. }
    assert (Lower ran[f0|[D1]] (inf_fD f0 D)). { red; intros. apply H17; auto. }
    destruct H14. destruct H18a as [H23[]].
    pose proof (RestrictFun f0 D1). apply H26 in H23 as [H23[]].
    assert (x ∈ dom[f0|[D1]]). { rewrite H27. apply Classifier1; auto. }
    apply fx_ran_T in H29; auto. pose proof H29.
    apply H18 in H29. apply H22 in H30. lra. }
  assert ((inf_fD f (\[a, b\])) <= (sup_fD f (\[T[(N - 1)%nat], T'[N]\]))
    /\ (inf_fD f (\[a, b\])) <= (sup_fD f (\[T'[N], T[N]\]))) as [].
  { split; apply H14; auto; try (red; intros; applyClassifier1 H15; apply Classifier1;
    lra). exists ((T[(N - 1)%nat] + T'[N])/2). apply Classifier1; lra.
    exists ((T'[N] + T[N])/2). apply Classifier1; lra. }
  assert ((Up_sum f T n) - (Up_sum f T' (S n))
    <= ((sup_fD f (\[a, b\])) - (inf_fD f (\[a, b\]))) * (T'[N] - T[(N - 1)%nat])
    + ((sup_fD f (\[a, b\])) - (inf_fD f (\[a, b\]))) * (T[N] - T'[N])).
  { rewrite H7. apply Rplus_le_compat; apply Rmult_le_compat_r; lra. }
  assert (((sup_fD f (\[a, b\])) - (inf_fD f (\[a, b\]))) * (T'[N] - T[(N - 1)%nat])
    + ((sup_fD f (\[a, b\])) - (inf_fD f (\[a, b\]))) * (T[N] - T'[N])
    = ((sup_fD f (\[a, b\])) - (inf_fD f (\[a, b\]))) * (T[N] - T[(N - 1)%nat])).
  { rewrite <-Rmult_plus_distr_l. lra. } rewrite H18 in H17.
  assert ((inf_fD f (\[a, b\])) <= (sup_fD f (\[a, b\]))).
  { pose proof I. pose proof I. apply inf_Coro_1 in H19 as [H19 _]; auto.
    apply sup_Coro_1 in H20 as [H20 _]; auto. pose proof I.
    destruct H21 as [H21[]]. pose proof (RestrictFun f (\[a, b\])).
    apply H24 in H21 as [H21[]]. destruct I0. assert (x ∈ dom[f|[\[a, b\]]]).
    { rewrite H25. apply Classifier1; auto. }
    apply fx_ran_T in H28; auto. pose proof H28.
    apply H19 in H28. apply H20 in H29. lra. }
  assert ((T[S (N - 1)%nat] - T[(N - 1)%nat]) <= (mold T (S n))).
  { apply (SegMold_Max T a b). lia. destruct H; auto. }
  replace (S (N - 1)%nat) with N in H20; [ |lia].
  assert (((sup_fD f (\[a, b\])) - (inf_fD f (\[a, b\]))) * (T[N] - T[(N - 1)%nat])
    <= ((sup_fD f (\[a, b\])) - (inf_fD f (\[a, b\]))) * (mold T (S n))).
  { apply Rmult_le_compat_l; lra. } lra.
Qed.

(* 性质二引理3 对分割T增加一个分割点得到T' 下和不等式 *)
Lemma Lemma9_6_2c : ∀ f T T' a b n, DBoundedFun f (\[a, b\])
  -> Sum_Seg T T' a b (S n) 1 -> (Low_sum f T n) <= (Low_sum f T' (S n))
  <= ((Low_sum f T n) + ((sup_fD f (\[a, b\])) - (inf_fD f (\[a, b\])))
    * (mold T (S n))).
Proof.
  assert ((∀ T n, Σ T (S n) = Σ T n + T[S n])
    /\ (∀ T n, Σ T (S (S n)) = Σ T n + T[S n] + T[S (S n)])) as [J1 J2].
  { split; intros; simpl; auto. }
  assert ((∀ T T' n, (∀ m, (0 <= m <= n)%nat -> T[m] = T'[m])
    -> Σ T n = Σ T' n)) as J3.
  { intros. induction n. simpl. rewrite H; auto; lia.
    assert (∀ m, (0 <= m <= n)%nat -> T[m] = T'[m]). { intros. apply H. lia. }
    simpl. rewrite H, IHn; auto. lia. }
  assert (∀ T T' n N, (0 <= N <= n)%nat -> (∀ u, (0 <= u < N)%nat
    -> T'[u] = T[u]) -> (∀ u, ((S N) < u <= (S n))%nat -> T'[u] = T[(u - 1)%nat])
    -> Σ T n - Σ T' (S n) = T[N] - (T'[N] + T'[S N])) as G1.
  { intros. induction n. assert (N = 0%nat). lia. rewrite H2. simpl; auto.
    destruct (classic (N = S n)). rewrite H2, J1, J2. rewrite H2 in H0.
    assert (Σ T n = Σ T' n). { apply J3. intros. symmetry. apply H0. lia. }
    lra. assert (0 <= N <= n)%nat. lia. apply IHn in H3. rewrite J1, J1, <-H3.
    assert (T[S n] = T'[S (S n)]). { rewrite H1; auto. lia. } lra.
    intros. apply H1. lia. }
  intros f T T' a b n I H. assert (NotEmpty (\[a, b\])) as I0.
  { assert (a < b).
    { destruct H. pose proof H. destruct H as [_[_[_[_[]]]]]. rewrite <-H, <-H2.
      apply (Seg_StrictlyIncrease_a T a b (S n)); auto; lia. }
    exists ((a + b)/2). apply Classifier1; lra. }
  assert ((∀ n, \{\ λ i s, s = (inf_fD f (\[T[i], T[S i]\]))
    * (T[S i] - T[i]) \}\[n] = (inf_fD f (\[T[n], T[S n]\]))
    * (T[S n] - T[n])) /\ (∀ n, \{\ λ i s, s = (inf_fD f (\[T'[i], T'[S i]\]))
    * (T'[S i] - T'[i]) \}\[n] = (inf_fD f (\[T'[n], T'[S n]\]))
    * (T'[S n] - T'[n]))) as [J4 J5].
  { split; intros; apply f_x_T; try (apply Classifier2; auto); red; intros;
    applyClassifier2 H0; applyClassifier2 H1; rewrite H0,H1; auto. }
  pose proof H. apply Lemma9_6_2a in H0 as [N[H0[H1[]]]].
  assert ((Low_sum f T n) - (Low_sum f T' (S n))
    = (inf_fD f (\[T[(N - 1)%nat], T[N]\])) * (T[N] - T[(N - 1)%nat])
    - ((inf_fD f (\[T'[(N - 1)%nat], T'[N]\])) * (T'[N] - T'[(N - 1)%nat])
      + (inf_fD f (\[T'[N], T'[S N]\])) * (T'[S N] - T'[N]))).
  { unfold Low_sum. rewrite (G1 _ _ n (N - 1)%nat). rewrite J4, J5, J5.
    replace (S (N - 1)%nat) with N; auto. lia. lia. intros.
    rewrite J4, J5, H1, H1; auto. lia. lia. intros. rewrite J4, J5, H3, H3.
    replace (S u - 1)%nat with (S (u - 1))%nat; auto. lia. lia. lia. }
  assert (T'[(N - 1)%nat] < T'[N] < T'[S N]).
  { destruct H as [_[]]. replace (S n + 1)%nat with (S (S n)) in H; [ |lia].
    split; apply (Seg_StrictlyIncrease_a T' a b (S (S n))); auto; lia. }
  assert (a <= T'[(N - 1)%nat] /\ T'[S N] <= b) as [H5a H5b].
  { destruct H as [_[]]. pose proof H. destruct H7 as [_[_[_[_[]]]]].
    rewrite <-H7, <-H8. simpl. simpl in H.
    split; apply (Seg_Increase_a T' a b (S (n + 1)%nat)); eauto; lia. }
  rewrite H1, (H3 (S N)) in H5; try lia. rewrite H1 in H5a; [ |lia].
  rewrite H3 in H5b; [ |lia]. simpl in H5, H5b. rewrite Nat.sub_0_r in H5, H5b.
  assert ((T[N] - T[(N - 1)%nat]) = (T[N] - T'[N]) + (T'[N] - T[(N - 1)%nat])). lra.
  rewrite H6 in H4. rewrite (H1 (N - 1)%nat), (H3 (S N)) in H4; try lia.
  simpl in H4. rewrite Nat.sub_0_r in H4.
  assert ((Low_sum f T n) - (Low_sum f T' (S n))
  = ((inf_fD f (\[T[(N - 1)%nat], T[N]\])) - (inf_fD f (\[T[(N - 1)%nat], T'[N]\])))
  * (T'[N] - T[(N - 1)%nat]) + ((inf_fD f (\[T[(N - 1)%nat], T[N]\]))
  - (inf_fD f (\[T'[N], T[N]\]))) * (T[N] - T'[N])). lra.
  assert (∀ f D1 D, NotEmpty D1 -> NotEmpty D -> D1 ⊂ D
    -> DBoundedFun f D -> (inf_fD f D) <= (inf_fD f D1)).
  { intros. pose proof H11. apply inf_Coro_1 in H12 as []; auto.
    assert (DBoundedFun f0 D1).
    { destruct H11 as [H11[H14[]]]. repeat split; auto. red; intros; auto.
      exists x. intros; auto. }
    pose proof H14. apply inf_Coro_1 in H15 as []; auto.
    assert (ran[f0|[D1]] ⊂ ran[f0|[D]]).
    { red; intros. applyClassifier1 H17. destruct H17. applyClassifier1 H17. destruct H17.
      apply Classifier1. exists x. apply Classifier1. split; auto. applyClassifier2 H18.
      destruct H18. apply Classifier2. split; auto. }
    destruct (Rle_or_lt (inf_fD f0 D) (inf_fD f0 D1)); auto. pose proof H18.
    apply H16 in H19 as [x[]]. apply H17, H12 in H19. exfalso. lra. }
  assert (∀ f D1 D, D1 ⊂ D -> DBoundedFun f D -> DBoundedFun f D1).
  { intros. destruct H10 as [H10[]]. repeat split; auto. red; intros; auto.
    destruct H12. exists x. intros; auto. }
  assert ((inf_fD f (\[T[(N - 1)%nat], T[N]\]))
    <= (inf_fD f (\[T[(N - 1)%nat], T'[N]\]))).
  { apply H8. exists ((T[(N - 1)%nat] + T'[N])/2). apply Classifier1; lra.
    exists ((T[(N - 1)%nat] + T[N])/2). apply Classifier1; lra. red; intros.
    applyClassifier1 H10. apply Classifier1; lra. apply (H9 f _ (\[a, b\])); auto.
    red; intros. applyClassifier1 H10. destruct H10. apply Classifier1. lra. }
  assert ((inf_fD f (\[T[(N - 1)%nat], T[N]\]))
    <= (inf_fD f (\[T'[N], T[N]\]))).
  { apply H8. exists ((T'[N] + T[N])/2). apply Classifier1; lra.
    exists ((T[(N - 1)%nat] + T[N])/2). apply Classifier1; lra. red; intros.
    applyClassifier1 H11. apply Classifier1. lra. apply (H9 f _ (\[a, b\])); auto.
    red; intros. applyClassifier1 H11. apply Classifier1; lra. }
  assert ((Low_sum f T n - (Low_sum f T' (S n))) <= 0).
  { rewrite H7. assert (0 <= ((inf_fD f (\[T[(N - 1)%nat], T'[N]\]))
      - (inf_fD f (\[T[(N - 1)%nat], T[N]\]))) * (T' [N] - T [(N - 1)%nat])
      + ((inf_fD f (\[T'[N], T[N]\])) - (inf_fD f (\[T[(N - 1)%nat], T[N]\])))
      * (T[N] - T'[N])).
    { apply Rplus_le_le_0_compat; apply Rmult_le_pos; lra. } lra. }
  assert ((inf_fD f (\[a, b\])) <= (inf_fD f (\[T[(N - 1)%nat], T[N]\]))).
  { apply H8; auto. exists ((T[(N - 1)%nat] + T[N])/2). apply Classifier1; lra.
    red; intros. applyClassifier1 H13. apply Classifier1; lra. }
  assert (∀ f D1 D, NotEmpty D1 -> NotEmpty D -> D1 ⊂ D
    -> DBoundedFun f D -> inf_fD f D1 <= sup_fD f D).
  { intros. pose proof H17. apply (H9 _ D1) in H18; auto. pose proof H18 as H18a.
    apply sup_Coro_1 in H17 as []; auto. apply inf_Coro_1 in H18 as []; auto.
    assert (ran[f0|[D1]] ⊂ ran[f0|[D]]).
    { red; intros. applyClassifier1 H21. destruct H21. applyClassifier1 H21.
      destruct H21. apply Classifier1. exists x. apply Classifier1; split; auto.
      applyClassifier2 H22. destruct H22. apply Classifier2; auto. }
    assert (Upper ran[f0|[D1]] (sup_fD f0 D)). { red; intros. apply H17; auto. }
    destruct H14. destruct H18a as [H23[]].
    pose proof (RestrictFun f0 D1). apply H26 in H23 as [H23[]].
    assert (x ∈ dom[f0|[D1]]). { rewrite H27. apply Classifier1; auto. }
    apply fx_ran_T in H29; auto. pose proof H29.
    apply H18 in H29. apply H22 in H30. lra. }
  assert ((inf_fD f (\[T[(N - 1)%nat], T'[N]\])) <= (sup_fD f (\[a, b\]))
    /\ (inf_fD f (\[T'[N], T[N]\])) <= (sup_fD f (\[a, b\]))) as [].
  { split; apply H14; auto; try (red; intros; applyClassifier1 H15; apply Classifier1;
    lra). exists ((T[(N - 1)%nat] + T'[N])/2). apply Classifier1; lra.
    exists ((T'[N] + T[N])/2). apply Classifier1; lra. }
  assert (((inf_fD f (\[a, b\])) - (sup_fD f (\[a, b\]))) * (T'[N] - T[(N - 1)%nat])
    + ((inf_fD f (\[a, b\])) - (sup_fD f (\[a, b\]))) * (T[N] - T'[N])
    <= (Low_sum f T n) - (Low_sum f T' (S n))).
  { rewrite H7. apply Rplus_le_compat; apply Rmult_le_compat_r; lra. }
  assert (((inf_fD f (\[a, b\])) - (sup_fD f (\[a, b\]))) * (T'[N] - T[(N - 1)%nat])
    + ((inf_fD f (\[a, b\])) - (sup_fD f (\[a, b\]))) * (T[N] - T'[N])
    = ((inf_fD f (\[a, b\])) - (sup_fD f (\[a, b\]))) * (T[N] - T[(N - 1)%nat])).
  { rewrite <-Rmult_plus_distr_l. lra. } rewrite H18 in H17.
  assert ((inf_fD f (\[a, b\])) <= (sup_fD f (\[a, b\]))).
  { pose proof I. pose proof I. apply inf_Coro_1 in H19 as [H19 _]; auto.
    apply sup_Coro_1 in H20 as [H20 _]; auto. pose proof I. destruct H21
    as [H21[]]. pose proof (RestrictFun f (\[a, b\])).
    apply H24 in H21 as [H21[]]. destruct I0. assert (x ∈ dom[f|[\[a, b\]]]).
    { rewrite H25. apply Classifier1; auto. }
    apply fx_ran_T in H28; auto. pose proof H28.
    apply H19 in H28. apply H20 in H29. lra. }
  assert ((T[S (N - 1)%nat] - T[(N - 1)%nat]) <= (mold T (S n))).
  { apply (SegMold_Max T a b). lia. destruct H; auto. }
  replace (S (N - 1)%nat) with N in H20; [ |lia].
  assert (((inf_fD f (\[a, b\])) - (sup_fD f (\[a, b\]))) * (mold T (S n))
    <= ((inf_fD f (\[a, b\])) - (sup_fD f (\[a, b\]))) * (T[N] - T[(N - 1)%nat])).
  { apply Rmult_le_compat_neg_l; auto. lra. } lra.
Qed.

(* 性质二引理4 对分割T增加(S p)个分点后, 可以构造出增加p个分点的分割 *)
Lemma Lemma9_6_2d : ∀ T T' a b n p, Sum_Seg T T' a b (S n) (S p)
  -> ∃ T0, Sum_Seg T T0 a b (S n) p /\ Sum_Seg T0 T' a b ((S n) + p)%nat 1.
Proof.
  intros. assert (Function1_1 T /\ Function1_1 T') as [].
  { destruct H as [H[]]. split; apply Seg_is_Function1_1; eauto. }
  destruct H as [[H[H2[H3[H4[]]]]][[H7[H8[H9[H10[]]]]]]].
  assert (NotEmpty (ran[T'] — ran[T])) as [d].
  { apply NNPP; intro. assert (ran[T] = ran[T']).
    { apply AxiomI; split; intros; auto. apply NNPP; intro. apply H14.
      exists z. apply Classifier1; split; auto. }
    assert (Function1_1 ((T﹣¹) ◦ T')).
    { apply Comp_Fun_P4; split; auto. apply invFun1_1; auto. }
    assert (dom[((T﹣¹) ◦ T')] = dom[T']).
    { apply AxiomI; split; intros. applyClassifier1 H17. destruct H17.
      applyClassifier2 H17. destruct H17. destruct H17. apply Classifier1; eauto.
      applyClassifier1 H17. destruct H17. apply Classifier1. exists ((T﹣¹)[x]).
      apply Classifier2. exists x. split; auto. apply x_fx_T. destruct H0; auto.
      destruct (Inverse_P1 T). rewrite H18, H15. apply Classifier1; eauto. }
    assert (ran[((T﹣¹) ◦ T')] = dom[T]).
    { apply AxiomI; split; intros. applyClassifier1 H18. destruct H18.
      applyClassifier2 H18. destruct H18 as [y[]]. destruct (Inverse_P1 T).
      rewrite <-H21. apply Classifier1; eauto. apply Classifier1. applyClassifier1 H18.
      destruct H18. exists (T'﹣¹[x]). apply Classifier2. exists x. split.
      assert ([x, (T'﹣¹)[x]] ∈ (T'﹣¹)).
      { apply x_fx_T. destruct H1; auto. destruct (Inverse_P1 T').
        rewrite H19, <-H15. apply Classifier1; eauto. } applyClassifier2 H19; auto.
      apply Classifier2; auto. }
    assert (dom[T] ⊂ dom[T']).
    { red; intros. rewrite H3 in H19. rewrite H9.
      applyClassifier1 H19. apply Classifier1; lia. }
    assert (dom[T'] = \{ λ u, (u < S n + S p + 1)%nat \}).
    { rewrite H9. apply AxiomI; split; intros; applyClassifier1 H20;
      apply Classifier1; lia. } rewrite H20 in H19.
    apply drawerPrinciple in H19. elim H19. rewrite <-H20. eauto. rewrite H3.
    intro. assert ((S n + S p)%nat ∈ \{ λ u, (u < S n + S p + 1)%nat \}).
    { apply Classifier1; lia. } rewrite <-H21 in H22. applyClassifier1 H22. lia. }
  applyClassifier1 H14. destruct H14. applyClassifier1 H15. pose proof H14.
  applyClassifier1 H16. destruct H16 as [N]. assert (N ∈ dom[T']).
  { apply Classifier1; eauto. } pose proof H17. rewrite H9 in H18.
  applyClassifier1 H18. set (T0 := \{\ λ u v, ((0 <= u < N)%nat /\ v = T'[u])
    \/ ((N <= u <= (S n + S p - 1))%nat /\ v = T'[S u]) \}\).
  assert (Function T0).
  { red; intros. applyClassifier2 H19. applyClassifier2 H20.
    destruct H19 as [[]|[]], H20 as [[]|[]]; try (rewrite H21,H22; auto);
    try (exfalso; lia). }
  assert (dom[T0] = \{ λ u, (u <= S n + S p - 1)%nat \}).
  { apply AxiomI; split; intros. applyClassifier1 H20. destruct H20.
    applyClassifier2 H20. destruct H20 as [[]|[]]; apply Classifier1; lia.
    applyClassifier1 H20. apply Classifier1. destruct (classic (0 <= z < N)%nat).
    exists T'[z]. apply Classifier2; auto. assert ((N <= z <= S n + S p - 1)%nat).
    lia. exists T'[S z]. apply Classifier2; auto. }
  assert ((∀ k, (0 <= k < N)%nat -> T0[k] = T'[k])
    /\ (∀ k, (N <= k <= S n + S p - 1)%nat -> T0[k] = T'[S k])) as [].
  { split; intros; apply f_x_T; auto; apply Classifier2; auto. }
  assert (Seg T0 a b (S n + S p - 1)%nat).
  { repeat split; auto. lia. intros. destruct (classic (0 <= k < N)%nat) as [Hc|Hc].
    rewrite H21; auto. destruct (classic (S k < N)%nat). rewrite H21; [ |lia].
    apply H10. lia. assert (N <= S k <= S n + S p - 1)%nat. lia.
    rewrite H22; auto. apply (Seg_StrictlyIncrease_a T' a b (S n + S p)%nat); auto.
    repeat split; auto. lia. lia. rewrite H22, H22; try lia. apply H10; lia.
    rewrite H21; auto. split. lia. apply NNPP; intro. assert (N = 0)%nat. lia.
    rewrite H24 in H16. apply f_x_T in H16; auto. elim H15.
    rewrite <-H16. replace (T'[0%nat]) with T'[0%nat]; auto. rewrite H11,<-H5.
    apply fx_ran_T; auto. rewrite H3. apply Classifier1. lia. rewrite H22. simpl.
    rewrite Nat.sub_0_r. simpl in H12; auto. split; auto. apply NNPP; intro.
    assert (N = S n + S p)%nat. lia. rewrite H24 in H16.
    apply f_x_T in H16; auto. elim H15. rewrite <-H16.
    replace (T'[(S n + S p)%nat]) with T'[(S n + S p)%nat]; auto.
    rewrite H12, <-H6. apply fx_ran_T; auto. rewrite H3. apply Classifier1; auto. }
  assert (ran[T0] = ran[T'] — [d]).
  { apply AxiomI; split; intros. applyClassifier1 H24. destruct H24. applyClassifier2 H24.
    destruct H24 as [[]|[]]. apply Classifier1; split. rewrite H25. apply fx_ran_T; auto.
    rewrite H9. apply Classifier1; lia. apply Classifier1. intro. applyClassifier1 H26.
    rewrite <-H26, H25 in H16. apply f_x_T in H16; auto.
    apply (Seg_Injective T' a b (S n + S p)%nat) in H16; auto. rewrite H16 in H24.
    lia. repeat split; auto. lia. apply Classifier1; split. rewrite H25.
    apply fx_ran_T; auto. rewrite H9. apply Classifier1; lia. apply Classifier1. intro.
    applyClassifier1 H26. rewrite <-H26, H25 in H16. apply f_x_T in H16; auto.
    apply (Seg_Injective T' a b (S n + S p)%nat) in H16; auto. rewrite H16 in H24.
    lia. repeat split; auto. lia. applyClassifier1 H24. destruct H24.
    applyClassifier1 H24. destruct H24. assert (x ∈ dom[T']). { apply Classifier1; eauto. }
    rewrite H9 in H26. applyClassifier1 H26. apply f_x_T in H24; auto.
    destruct (classic (0 <= x < N)%nat).
    rewrite <-H24,<-H21; auto. apply fx_ran_T; auto. rewrite H20.
    apply Classifier1; lia. assert (x <> N).
    { intro. rewrite <-H28 in H16. apply f_x_T in H16; auto.
      applyClassifier1 H25. elim H25. rewrite <-H16,<-H24. apply Classifier1; auto. }
    assert (N <= x - 1 <= S n + S p - 1)%nat. lia. rewrite <-H24.
    replace x with (S (x - 1)%nat). rewrite <-H22; auto. apply fx_ran_T; auto.
    rewrite H20. apply Classifier1; lia. lia. }
  assert (ran[T] ⊂ ran[T0]).
  { rewrite H24. red; intros. apply Classifier1; split; auto. apply Classifier1.
    intro. applyClassifier1 H26. rewrite H26 in H25; auto. }
  assert (ran[T0] ⊂ ran[T']). { rewrite H24. red; intros. applyClassifier1 H26; tauto. }
  exists T0. replace (S n + S p - 1)%nat with (S n + p)%nat in H23; [ |lia].
  split. split; auto. repeat split; auto. split; auto. split; auto.
  replace (S n + p + 1)%nat with (S n + S p)%nat; [ |lia]. repeat split; auto.
Qed.

(* 性质二引理5 两个分割T T'分割相同段数, 如果二者值域存在包含关系, 则两个分割相同 *)
Lemma Lemma9_6_2e : ∀ T T' a b n, Seg T a b n -> Seg T' a b n
  -> ran[T] ⊂ ran[T'] -> T = T'.
Proof.
  intros. pose proof H. pose proof H0.
  destruct H2 as [H2[H4[H5[H6[]]]]], H3 as [H9[H10[H11[H12[]]]]].
  assert (Function1_1 T /\ Function1_1 T') as [].
  { split; apply Seg_is_Function1_1; eauto. }
  assert (Function1_1 (T ◦ (T'﹣¹))).
  { apply Comp_Fun_P4; auto. split; auto. apply invFun1_1; auto. }
  assert (dom[T ◦ (T'﹣¹)] = ran[T']).
  { apply AxiomI; split; intros. applyClassifier1 H17. destruct H17.
    applyClassifier2 H17. destruct H17 as [y[]]. applyClassifier2 H17.
    apply Classifier1; eauto. applyClassifier1 H17. destruct H17. apply Classifier1.
    exists T[x]. apply Classifier2. exists x. split. apply Classifier2; auto.
    apply x_fx_T; auto. rewrite H5, <-H11. apply Classifier1; eauto. }
  assert (ran[T ◦ (T'﹣¹)] = ran[T]).
  { apply AxiomI; split; intros. applyClassifier1 H18. destruct H18.
    applyClassifier2 H18. destruct H18 as [y[]]. apply Classifier1; eauto.
    applyClassifier1 H18. destruct H18. apply  Classifier1. exists T'[x].
    apply Classifier2. exists x. split; auto. apply Classifier2.
    apply x_fx_T; auto. rewrite H11, <-H5. apply Classifier1; eauto. }
  assert (Finite ran[T']). { left. exists n, T'; auto. }
  assert (ran[T] = ran[T']). { apply Fact9_6a with (f := T ◦ T'﹣¹); auto. }
  assert (∀ k, (k <= n)%nat -> T[k] = T'[k]).
  { intros. induction k. rewrite H7, H3; auto.
    assert (T[k] = T'[k]). { apply IHk; lia. }
    assert ((S k) ∈ dom[T]). { rewrite H5. apply Classifier1; auto. }
    pose proof H23. rewrite H5, <-H11 in H24.
    destruct (Rtotal_order T[S k] T'[S k]) as [H25 | []]; auto.
    - apply fx_ran_T in H23; auto. rewrite H20 in H23.
      applyClassifier1 H23. destruct H23.
      assert (x ∈ dom[T']). { apply Classifier1; eauto. }
      rewrite H11 in H26. applyClassifier1 H26. apply f_x_T in H23; auto.
      assert (T'[k] < T[S k]). { rewrite <-H22; auto. }
      replace T[S k] with T[S k] in H23; auto. rewrite <-H23 in H25, H27.
      apply (Seg_StrictlyIncrease_b _ a b n) in H25, H27; eauto. exfalso. lia. lia.
    - apply fx_ran_T in H24; auto. rewrite <-H20 in H24.
      applyClassifier1 H24. destruct H24.
      assert (x ∈ dom[T]). { apply Classifier1; eauto. }
      rewrite H5 in H26. applyClassifier1 H26. apply f_x_T in H24; auto.
      assert (T[k] < T'[S k]). { rewrite H22; auto. }
      rewrite <-H24 in H25, H27. apply (Seg_StrictlyIncrease_b _ a b n)
      in H25,H27; eauto. exfalso. lia. lia. }
  apply AxiomI; split; intros; destruct z.
  assert (x ∈ dom[T]). { apply Classifier1; eauto. }
  apply f_x_T in H22; auto. rewrite <-H22. rewrite H21. apply x_fx_T; auto.
  rewrite H11, <-H5; auto. rewrite H5 in H23. applyClassifier1 H23; auto.
  assert (x ∈ dom[T']). { apply Classifier1; eauto. }
  apply f_x_T in H22; auto. rewrite <-H22. rewrite <-H21. apply x_fx_T; auto.
  rewrite H5, <-H11; auto. rewrite H11 in H23. applyClassifier1 H23; auto.
Qed.

(* 性质二引理6 分割T增加p个分点得到T', 则||T'|| <= ||T|| *)
Lemma Lemma9_6_2f : ∀ T T' a b n p, Sum_Seg T T' a b (S n) p
  -> (mold T' ((S n) + p)%nat) <= (mold T (S n)).
Proof.
  intros. generalize dependent T. generalize dependent T'.
  generalize dependent a. generalize dependent b. generalize dependent n.
  induction p; intros.
  - destruct H as [H[]]. rewrite Nat.add_0_r in *.
    apply (Lemma9_6_2e T T' a b (S n)) in H1; auto. rewrite H1. lra.
  - apply Lemma9_6_2d in H as [T0[]]. apply IHp in H. pose proof H0.
    apply Lemma9_6_2a in H0 as [N[H0[H2[]]]]. destruct H1 as [H1[]].
    assert ((mold T' (S n + S p)) ∈ \{ λ x, SegMold T' (S n + S p) x \}).
    { apply Axiomc. apply SegMold_Exists in H5 as [].
      exists x. apply Classifier1. replace (S n + S p)%nat with (S n + p + 1)%nat.
      auto. lia. } applyClassifier1 H7. destruct H7 as [[x[]]].
    assert (T0[(N - 1)%nat] <= T'[N] <= T0[N]).
    { rewrite <-H2; [ |lia]. replace T0[N] with T0[((S N) - 1)%nat].
      rewrite <-H4; [ |lia]. destruct H5 as [_[_[_[]]]].
      split; left. replace T'[N] with T'[S (N - 1)%nat]. apply H5; lia.
      replace (S (N - 1)%nat) with N; auto. lia. apply H5; auto. lia.
      replace ((S N) - 1)%nat with N; auto. lia. }
    destruct (classic (0 <= x < N)%nat) as [Hc|Hc].
    + destruct (classic (S x = N)).
      * rewrite H11, (H2 x) in H8; [ |lia]. assert (T'[N] - T0[x] <= T0[N] - T0[x]).
        lra. assert (T0[N] - T0[x] <= (mold T0 (S n + p))).
        { rewrite <-H11. apply (SegMold_Max T0 a b); auto. lia. }
        simpl. rewrite <-H8. lra.
      * assert ((S x) < N)%nat. lia. rewrite H2, H2 in H8; try lia.
        simpl. rewrite <-H8. assert (T0[S x] - T0[x] <= (mold T0 (S n + p))).
        { apply (SegMold_Max T0 a b); auto. lia. } lra.
    + assert (N <= x < S n + S p)%nat. lia. rewrite H4 in H8; [ |lia].
      simpl in H8. rewrite Nat.sub_0_r in H8. destruct (classic (x = N)).
      * rewrite H12 in H8. simpl. assert (T0[N] - T'[N] <= T0[N] - T0[(N - 1)%nat]).
        lra. assert (T0[S (N - 1)%nat] - T0[(N - 1)%nat] <= mold T0 (S n + p)%nat).
        { apply (SegMold_Max T0 a b); auto. lia. }
        replace (S (N - 1)%nat) with N in H14. rewrite <-H8. lra. lia.
      * simpl. rewrite <-H8, H4; [ |lia]. replace T0[x] with T0[S (x - 1)%nat].
        assert (T0[S (x - 1)%nat] - T0[(x - 1)%nat] <= mold T0 (S n + p)%nat).
        { apply (SegMold_Max T0 a b); auto. lia. } lra.
        replace (S (x - 1)%nat) with x. auto. lia.
Qed.

(* 性质二 对分割T增加p个分割点得到T' 上和不等式 *)
Property Property9_6_2a : ∀ f T T' a b n p, DBoundedFun f (\[a, b\])
  -> Sum_Seg T T' a b (S n) p -> ((Up_sum f T n) - ((sup_fD f (\[a, b\]))
    - (inf_fD f (\[a, b\]))) * (INR p) * (mold T (S n)))
    <= (Up_sum f T' (n + p)%nat) <= (Up_sum f T n).
Proof.
  intros. generalize dependent T. generalize dependent T'. generalize dependent a.
  generalize dependent b. generalize dependent n. induction p; intros.
  - destruct H0 as [H0[]]. rewrite Nat.add_0_r in *. simpl.
    rewrite Rmult_0_r, Rmult_0_l, Rminus_0_r.
    assert (T = T'). { apply (Lemma9_6_2e T T' a b (S n)); auto. }
    rewrite H3. lra.
  - pose proof H0. apply Lemma9_6_2d in H1 as [T0[]]. pose proof H1.
    pose proof H2. apply IHp in H3; auto. simpl in H4.
    apply (Lemma9_6_2b f) in H4; auto.
    assert (0 <= (Up_sum f T n) - (Up_sum f T0 (n + p)%nat) <=
      (sup_fD f (\[a, b\]) - inf_fD f (\[a, b\])) * (INR p) * (mold T (S n))). lra.
    assert (0 <= (Up_sum f T0 (n + p)%nat) - (Up_sum f T' (S (n + p)%nat)) <=
      (sup_fD f (\[a, b\]) - inf_fD f (\[a, b\])) * (mold T0 (S (n + p)%nat))). lra.
    assert ((mold T0 (S (n + p)%nat)) <= (mold T (S n))).
    { apply (Lemma9_6_2f T T0 a b); auto. }
    assert (0 < (mold T0 (S (n + p)%nat))).
    { destruct H1 as [H1[]]. pose proof H8.
      apply SegMold_Max with (k := 0%nat) in H10; [ |lia].
      destruct H8 as [_[_[_[]]]]. assert (0 < S n + p)%nat. lia.
      apply H8 in H12. replace (S (n + p)%nat) with (S n + p)%nat. lra. lia. }
    assert (0 <= (sup_fD f (\[a, b\]) - inf_fD f (\[a, b\]))).
    { assert (0 <= (sup_fD f (\[a, b\]) - inf_fD f (\[a, b\]))
        * (mold T0 (S (n + p)%nat))). lra. replace 0 with
      (0 * (mold T0 (S (n + p)%nat))) in H9; [ |lra].
      apply Rmult_le_reg_r in H9; auto. }
    assert (0 <= (Up_sum f T0 (n + p)%nat) - (Up_sum f T' (S (n + p)%nat))
      <= (sup_fD f (\[a, b\]) - inf_fD f (\[a, b\])) * (mold T (S n))).
    { destruct H6. split; auto. apply (Rle_trans _ ((sup_fD f (\[a, b\])
      - inf_fD f (\[a, b\])) * (mold T0 (S (n + p)%nat)))); auto.
      apply Rmult_le_compat_l; auto. }
    assert (0 + 0 <= (Up_sum f T n - Up_sum f T0 (n + p)%nat)
      + (Up_sum f T0 (n + p)%nat - Up_sum f T' (S (n + p)%nat))
      <= (sup_fD f (\[a, b\]) - inf_fD f (\[a, b\])) * (INR p) * (mold T (S n))
      + (sup_fD f (\[a, b\]) - inf_fD f (\[a, b\])) * (mold T (S n))). lra.
    assert ((Up_sum f T n - Up_sum f T0 (n + p)%nat)
      + (Up_sum f T0 (n + p)%nat - Up_sum f T' (S (n + p)%nat))
      = Up_sum f T n - Up_sum f T' (S (n + p)%nat)). lra.
    assert ((sup_fD f (\[a, b\]) - inf_fD f (\[a, b\])) * (INR p) * (mold T (S n))
      + (sup_fD f (\[a, b\]) - inf_fD f (\[a, b\])) * (mold T (S n))
      = (sup_fD f (\[a, b\]) - inf_fD f (\[a, b\])) * (INR (S p)) * (mold T (S n))).
    { replace (INR (S p)) with ((INR p) + 1). lra. simpl. destruct p; auto.
      simpl. lra. } rewrite H12, H13, Rplus_0_r in H11.
    replace (S (n + p)%nat) with (n + S p)%nat in H11. lra. lia.
Qed.

(* 性质二 对分割T增加p个分割点得到T' 下和不等式 *)
Property Property9_6_2b : ∀ f T T' a b n p, DBoundedFun f (\[a, b\])
  -> Sum_Seg T T' a b (S n) p -> (Low_sum f T n) <= (Low_sum f T' (n + p)%nat)
    <= ((Low_sum f T n) + ((sup_fD f (\[a, b\])) - (inf_fD f (\[a, b\])))
      * (INR p) * (mold T (S n))).
Proof.
  intros. generalize dependent T. generalize dependent T'. generalize dependent a.
  generalize dependent b. generalize dependent n. induction p; intros.
  - destruct H0 as [H0[]]. rewrite Nat.add_0_r in *. simpl.
    rewrite Rmult_0_r, Rmult_0_l, Rplus_0_r.
    assert (T = T'). { apply (Lemma9_6_2e T T' a b (S n)); auto. }
    rewrite H3. lra.
  - pose proof H0. apply Lemma9_6_2d in H1 as [T0[]]. pose proof H1.
    pose proof H2. apply IHp in H3; auto. simpl in H4.
    apply (Lemma9_6_2c f) in H4; auto.
    assert (0 <= (Low_sum f T0 (n + p)%nat) - (Low_sum f T n) <=
      (sup_fD f (\[a, b\]) - inf_fD f (\[a, b\])) * (INR p) * (mold T (S n))). lra.
    assert (0 <= (Low_sum f T' (S (n + p)%nat)) - (Low_sum f T0 (n + p)%nat)  <=
      (sup_fD f (\[a, b\]) - inf_fD f (\[a, b\])) * (mold T0 (S (n + p)%nat))). lra.
    assert ((mold T0 (S (n + p)%nat)) <= (mold T (S n))).
    { apply (Lemma9_6_2f T T0 a b); auto. }
    assert (0 < (mold T0 (S (n + p)%nat))).
    { destruct H1 as [H1[]]. pose proof H8.
      apply SegMold_Max with (k := 0%nat) in H10; [ |lia].
      destruct H8 as [_[_[_[]]]]. assert (0 < S n + p)%nat. lia.
      apply H8 in H12. replace (S (n + p)%nat) with (S n + p)%nat. lra. lia. }
    assert (0 <= (sup_fD f (\[a, b\]) - inf_fD f (\[a, b\]))).
    { assert (0 <= (sup_fD f (\[a, b\]) - inf_fD f (\[a, b\]))
        * (mold T0 (S (n + p)%nat))). lra. replace 0 with
      (0 * (mold T0 (S (n + p)%nat))) in H9; [ |lra].
      apply Rmult_le_reg_r in H9; auto. }
    assert (0 <= (Low_sum f T' (S (n + p)%nat)) - (Low_sum f T0 (n + p)%nat)
      <= (sup_fD f (\[a, b\]) - inf_fD f (\[a, b\])) * (mold T (S n))).
    { destruct H6. split; auto. apply (Rle_trans _ ((sup_fD f (\[a, b\])
      - inf_fD f (\[a, b\])) * (mold T0 (S (n + p)%nat)))); auto.
      apply Rmult_le_compat_l; auto. }
    assert (0 + 0 <= (Low_sum f T0 (n + p)%nat - Low_sum f T n)
      + (Low_sum f T' (S (n + p)%nat) - Low_sum f T0 (n + p)%nat)
      <= (sup_fD f (\[a, b\]) - inf_fD f (\[a, b\])) * (INR p) * (mold T (S n))
      + (sup_fD f (\[a, b\]) - inf_fD f (\[a, b\])) * (mold T (S n))). lra.
    assert ((Low_sum f T0 (n + p)%nat - Low_sum f T n)
      + (Low_sum f T' (S (n + p)%nat) - Low_sum f T0 (n + p)%nat)
      = Low_sum f T' (S (n + p)%nat) - Low_sum f T n). lra.
    assert ((sup_fD f (\[a, b\]) - inf_fD f (\[a, b\])) * (INR p) * (mold T (S n))
      + (sup_fD f (\[a, b\]) - inf_fD f (\[a, b\])) * (mold T (S n))
      = (sup_fD f (\[a, b\]) - inf_fD f (\[a, b\])) * (INR (S p)) * (mold T (S n))).
    { replace (INR (S p)) with ((INR p) + 1). lra. simpl. destruct p; auto.
      simpl. lra. } rewrite H12, H13, Rplus_0_r in H11.
    replace (S (n + p)%nat) with (n + S p)%nat in H11. lra. lia.
Qed.

(* 定义 分割的合并 *)
Definition Merge_seg (T T1 : @set (@prod nat R)) :=
  c \{ λ f, StrictlyIncreaseFun_Seq f /\ (∃ n, dom[f] = \{ λ u, (u <= n)%nat \})
    /\ ran[f] = ran[T] ∪ ran[T1] \}.

(* 性质三引理1 分割的合并还是分割 *)
Lemma Lemma9_6_3a : ∀ T1 T2 a b n m, Seg T1 a b n -> Seg T2 a b m
  -> (∃ k, (n <= k)%nat /\ (m <= k)%nat /\ (k <= S (n + m))%nat
    /\ Seg (Merge_seg T1 T2) a b k) /\ ran[T1] ⊂ ran[Merge_seg T1 T2]
    /\ ran[T2] ⊂ ran[Merge_seg T1 T2].
Proof.
  intros. pose proof H. pose proof H0.
  destruct H1 as [H1[H3[H4[H5[]]]]], H2 as [H2[H8[H9[H10[]]]]].
  assert (Function1_1 T1 /\ Function1_1 T2) as [].
  { split; apply Seg_is_Function1_1; eauto. }
  assert (Finite ran[T1] /\ Finite ran[T2]) as [].
  { split; left; [exists n,T1|exists m,T2]; auto. }
  assert (Finite (ran[T1] ∪ ran[T2])). { apply Fact9_6e; auto. }
  assert (NotEmptyFinite (ran[T1] ∪ ran[T2])).
  { destruct H17; auto. assert (a ∈ Empty R).
    { rewrite <-H17. apply Classifier1. left. rewrite <-H6.
      apply fx_ran_T; auto. rewrite H4. apply Classifier1; lia. }
    applyClassifier1 H18. elim H18; auto. }
  apply Fact9_6f in H18 as [k[T0[H18[H19[]]]]].
  assert (dom[T0] = \{ λ u,(u <= (k - 1))%nat \}).
  { rewrite H20. apply AxiomI; split; intros;
    applyClassifier1 H22; apply Classifier1; lia. }
  assert ((Merge_seg T1 T2) ∈ \{ λ f, StrictlyIncreaseFun_Seq f
    /\ (∃ n, dom[f] = \{ λ u, (u <= n)%nat \}) /\ ran[f] = ran[T1] ∪ ran[T2] \}).
  { apply Axiomc. exists T0. apply Classifier1. destruct H19. repeat split; eauto. }
  applyClassifier1 H23. destruct H23 as [H23[[v]]].
  clear dependent k. clear dependent T0.
  assert (ran[T1] ⊂ ran[Merge_seg T1 T2] /\ ran[T2] ⊂ ran[Merge_seg T1 T2])
  as []. { split; rewrite H25; red; intros; apply Classifier1; auto. }
  assert (Function1_1 (Merge_seg T1 T2)).
  { destruct H23. split; auto. red; intros. applyClassifier2 H22. applyClassifier2 H23.
    assert (y ∈ dom[Merge_seg T1 T2] /\ z ∈ dom[Merge_seg T1 T2]) as [].
    { split; apply Classifier1; eauto. }
    apply f_x_T in H22, H23; auto.
    destruct (Nat.lt_total y z) as [H28 | []]; auto. apply H21 in H28; auto.
    rewrite H22, H23 in H28. exfalso. lra. apply H21 in H28; auto.
    rewrite H22, H23 in H28. exfalso. lra. }
  apply (Fact9_6g _ _ n v) in H18; auto. apply (Fact9_6g _ _ m v) in H19;
  auto. repeat split. exists v. repeat split; auto.
  apply (Fact9_6i T1 T2 (Merge_seg T1 T2)); auto. destruct H20; auto. lia.
  intros. destruct H23. apply H23; try (rewrite H24; apply Classifier1; lia). lia.
  - assert (a ∈ ran[Merge_seg T1 T2]).
    { rewrite <-H6, H25. apply Classifier1. left. apply fx_ran_T; auto.
      rewrite H4. apply Classifier1; lia. }
    assert ((Merge_seg T1 T2)[0%nat] <= a).
    { applyClassifier1 H21; destruct H21.
      assert (x ∈ dom[Merge_seg T1 T2]). { apply Classifier1; eauto. }
      destruct H23. apply f_x_T in H21; auto. rewrite <-H21.
      destruct (classic (x = 0%nat)). rewrite H27. right. auto.
      left. apply H26; auto. rewrite H24. apply Classifier1; lia. lia. }
    assert ((Merge_seg T1 T2)[0%nat] ∈ ran[Merge_seg T1 T2]).
    { destruct H23. apply fx_ran_T; auto. rewrite H24. apply Classifier1; lia. }
    assert (a <= (Merge_seg T1 T2)[0%nat]).
    { rewrite H25 in H26. applyClassifier1 H26; destruct H26; applyClassifier1 H26;
      destruct H26. assert (x ∈ dom[T1]). { apply Classifier1; eauto. }
      apply f_x_T in H26; auto. rewrite <-H26, <-H6.
      apply (Seg_Increase_a T1 a b n); eauto; try lia. rewrite H4 in H27.
      applyClassifier1 H27; lia. assert (x ∈ dom[T2]). { apply Classifier1; eauto. }
      apply f_x_T in H26; auto. rewrite <-H26, <-H11.
      apply (Seg_Increase_a T2 a b m); eauto; try lia. rewrite H9 in H27.
      applyClassifier1 H27; lia. } lra.
  - assert (b ∈ ran[Merge_seg T1 T2]).
    { rewrite <-H7, H25. apply Classifier1. left. apply fx_ran_T; auto.
      rewrite H4. apply Classifier1; lia. }
    assert (b <= (Merge_seg T1 T2)[v]).
    { applyClassifier1 H21; destruct H21.
      assert (x ∈ dom[Merge_seg T1 T2]). { apply Classifier1; eauto. }
      rewrite H24 in H22. applyClassifier1 H22. destruct H23.
      apply f_x_T in H21; auto. rewrite <-H21.
      destruct (classic (x = v%nat)). rewrite H27. right. auto.
      left. apply H26; auto. rewrite H24. apply Classifier1; lia.
      rewrite H24. apply Classifier1; auto. lia. }
    assert ((Merge_seg T1 T2)[v] ∈ ran[Merge_seg T1 T2]).
    { destruct H23. apply fx_ran_T; auto. rewrite H24. apply Classifier1; lia. }
    assert ((Merge_seg T1 T2)[v] <= b).
    { rewrite H25 in H26. applyClassifier1 H26; destruct H26; applyClassifier1 H26;
      destruct H26. assert (x ∈ dom[T1]). { apply Classifier1; eauto. }
      apply f_x_T in H26; auto. rewrite <-H26, <-H7.
      apply (Seg_Increase_a T1 a b n); eauto; try lia; rewrite H4 in H27;
      applyClassifier1 H27; lia. assert (x ∈ dom[T2]). { apply Classifier1; eauto. }
      apply f_x_T in H26; auto. rewrite <-H26, <-H12.
      apply (Seg_Increase_a T2 a b m); eauto; try lia; rewrite H9 in H27;
      applyClassifier1 H27; lia. } lra.
  - rewrite H25. red; intros. apply Classifier1; auto.
  - rewrite H25. red; intros. apply Classifier1; auto.
Qed.

(* 性质三引理2 分割的合并可由原分割增加分点而得到 *)
Lemma Lemma9_6_3b : ∀ T1 T2 a b n m, Seg T1 a b n -> Seg T2 a b m
  -> (∃ k, (n <= k)%nat /\ (m <= k)%nat /\ (k <= S (n + m))%nat
    /\ Seg (Merge_seg T1 T2) a b k
    /\ Sum_Seg T1 (Merge_seg T1 T2) a b n (k - n)%nat
    /\ Sum_Seg T2 (Merge_seg T1 T2) a b m (k - m)%nat).
Proof.
  intros. pose proof H0. apply (Lemma9_6_3a T1 T2 a b n m) in H1; auto.
  destruct H1 as [[k[H1[H2[]]]][]]. exists k. split; [ |split; [ |split]]; auto.
  split; auto. split; split; auto; split; auto.
  replace (n + (k - n))%nat with k; auto. lia.
  replace (m + (k - m))%nat with k; auto. lia.
Qed.

(* 性质三 *)
Property Property9_6_3 : ∀ f T1 T2 a b n m, DBoundedFun f (\[a, b\])
  -> Seg T1 a b (S n) -> Seg T2 a b (S m)
  -> ∃ k, Seg (Merge_seg T1 T2) a b (S k)
    /\ (Up_sum f (Merge_seg T1 T2) k) <= (Up_sum f T1 n)
    /\ (Up_sum f (Merge_seg T1 T2) k) <= (Up_sum f T2 m)
    /\ (Low_sum f T1 n) <= (Low_sum f (Merge_seg T1 T2) k)
    /\ (Low_sum f T2 m) <= (Low_sum f (Merge_seg T1 T2) k).
Proof.
  intros. pose proof H0. apply (Lemma9_6_3b T1 T2 a b (S n) (S m)) in H2
  as [k[H2[H3[_[H4[]]]]]]; auto. pose proof H5. pose proof H6.
  apply (Property9_6_2a f) in H5, H6; auto. apply (Property9_6_2b f) in H7, H8;
  auto. assert (n + (k - S n) = k - 1)%nat. lia.
  assert (m + (k - S m) = k - 1)%nat. lia. rewrite H9, H10 in *.
  exists (k - 1)%nat. replace (S (k - 1)%nat) with k; [ |lia]. split; auto. lra.
Qed.

(* 性质四 任何分割的下和总小于等于任何另一个分割的上和 *)
Property Property9_6_4 : ∀ f T1 T2 a b n m, DBoundedFun f (\[a, b\])
  -> Seg T1 a b (S n) -> Seg T2 a b (S m) -> (Low_sum f T1 n) <= (Up_sum f T2 m).
Proof.
  intros. pose proof H0. apply (Property9_6_3 f T1 T2 a b n m) in H2
  as [k[H2[H3[H4[]]]]]; auto. apply (Up_Low_sum_Coro_1 f) in H2; auto. lra.
Qed.

(* 定义 f在区间[a, b]上的全体上和集 *)
Definition ST f a b := \{ λ u, ∃ n T, Seg T a b (S n) /\ u = Up_sum f T n \}.

(* 定义 f在区间[a, b]上的全体下和集 *)
Definition sT f a b := \{ λ u, ∃ n T, Seg T a b (S n) /\ u = Low_sum f T n \}.

(* 上和集 下和集 都非空 *)
Corollary ST_sT_NotEmpty : ∀ f a b, a < b -> NotEmpty (ST f a b)
  /\ NotEmpty (sT f a b).
Proof.
  intros. set (T := \{\ λ u v, (u <= 1)%nat
    /\ ((u = 0%nat /\ v = a) \/ (u = 1%nat /\ v = b)) \}\).
  assert (Function T).
  { red; intros. applyClassifier2 H0. applyClassifier2 H1.
    destruct H0 as [H0[[]|[]]], H1 as [H1[[]|[]]]; try (rewrite H3, H5; auto);
    rewrite H2 in H4; exfalso; lia. }
  assert (dom[T] = \{ λ u, (u <= 1)%nat \}).
  { apply AxiomI; split; intros. applyClassifier1 H1. destruct H1.
    applyClassifier2 H1. apply Classifier1. destruct H1 as [_[[]|[]]]; rewrite H1; lia.
    applyClassifier1 H1. apply Classifier1. destruct (classic (z = 0%nat)). exists a.
    rewrite H2. apply Classifier2; auto. assert (z = 1%nat). lia. exists b.
    rewrite H3. apply Classifier2; auto. }
  assert (T[0%nat] = a).
  { assert ([0%nat, a] ∈ T). { apply Classifier2; auto. }
    apply f_x_T in H2; auto. }
  assert (T[1%nat] = b).
  { assert ([1%nat, b] ∈ T). { apply Classifier2; auto. }
    apply f_x_T in H3; auto. }
  assert (Seg T a b 1).
  { repeat split; auto. intros. assert (k = 0%nat). lia.
    rewrite H5, H2, H3; auto. }
  split; [exists (Up_sum f T 0%nat) | exists (Low_sum f T 0%nat)];
  apply Classifier1; eauto.
Qed.

(* 上和集存在下确界 *)
Corollary ST_inf : ∀ f a b, a < b -> DBoundedFun f (\[a, b\])
  -> ∃ s, inf (ST f a b) s.
Proof.
  intros. assert (NotEmpty (ST f a b)). apply ST_sT_NotEmpty; auto.
  pose proof H1. destruct H1 as [s]. apply Sup_inf_principle in H2 as [_].
  apply H2. applyClassifier1 H1. destruct H1 as [n[T1[]]]. exists (Low_sum f T1 n).
  red; intros. applyClassifier1 H4. destruct H4 as [m[T0[]]]. rewrite H5.
  assert ((Low_sum f T1 n) <= (Up_sum f T0 m)).
  { apply (Property9_6_4 f _ _ a b); auto. } lra.
Qed.

(* 下和集存在上确界 *)
Corollary sT_sup : ∀ f a b, a < b -> DBoundedFun f (\[a, b\])
  -> ∃ s, sup (sT f a b) s.
Proof.
  intros. assert (NotEmpty (sT f a b)). apply ST_sT_NotEmpty; auto.
  pose proof H1. destruct H1 as [s]. apply Sup_inf_principle in H2 as [H2 _].
  apply H2. applyClassifier1 H1. destruct H1 as [n[T1[]]]. exists (Up_sum f T1 n).
  red; intros. applyClassifier1 H4. destruct H4 as [m[T0[]]]. rewrite H5.
  apply (Property9_6_4 f _ _ a b); auto.
Qed.

(* 定义 f在[a, b]的上积分 *)
Definition Up_Integral f a b := c \{ λ u, inf (ST f a b) u \}.

(* 定义 f在[a, b]的下积分 *)
Definition Low_Integral f a b := c \{ λ u, sup (sT f a b) u \}.

(* 上积分是上和集的下确界 *)
Corollary Up_Integral_Corollary : ∀ f a b, a < b
  -> DBoundedFun f (\[a, b\]) -> inf (ST f a b) (Up_Integral f a b).
Proof.
  intros. assert ((Up_Integral f a b) ∈ \{ λ u, inf (ST f a b) u \}).
  { apply Axiomc. apply ST_inf in H0 as []; auto. exists x. apply Classifier1; auto. }
  applyClassifier1 H1; auto.
Qed.

(* 下积分是下和集的上确界 *)
Corollary Low_Integral_Corollary : ∀ f a b, a < b
  -> DBoundedFun f (\[a, b\]) -> sup (sT f a b) (Low_Integral f a b).
Proof.
  intros. assert ((Low_Integral f a b) ∈ \{ λ u, sup (sT f a b) u \}).
  { apply Axiomc. apply sT_sup in H0 as []; auto. exists x. apply Classifier1; auto. }
  applyClassifier1 H1; auto.
Qed.

(* 性质5a 下积分小于等于上积分 *)
Property Property9_6_5a : ∀ f a b, a < b -> DBoundedFun f (\[a, b\])
  -> (Low_Integral f a b) <= (Up_Integral f a b).
Proof.
  intros. pose proof H0. apply Low_Integral_Corollary in H1 as []; auto.
  destruct (Rle_or_lt (Low_Integral f a b) (Up_Integral f a b)); auto.
  apply H2 in H3 as [x[]]. pose proof H0. apply Up_Integral_Corollary in H5
  as []; auto. apply H6 in H4 as [y[]]. applyClassifier1 H3. destruct H3 as [n[T1[]]].
  applyClassifier1 H4. destruct H4 as [m[T2[]]]. rewrite H8, H9 in H7.
  apply (Property9_6_4 f T1 T2 a b n m) in H0; auto. exfalso. lra.
Qed.

(* 性质5b 函数的下确界乘区间宽度 小于等于 下积分 *)
Property Property9_6_5b : ∀ f a b, a < b -> DBoundedFun f (\[a, b\])
  -> (inf_fD f (\[a, b\])) * (b - a) <= (Low_Integral f a b).
Proof.
  intros. pose proof H0. apply Low_Integral_Corollary in H1 as [H1 _]; auto.
  pose proof H. apply (ST_sT_NotEmpty f) in H2 as [_ []].
  pose proof H2. applyClassifier1 H3. destruct H3 as [n[T[]]].
  assert (∀ m, (m <= n)%nat -> (inf_fD f (\[a, b\]))
    <= (inf_fD f (\[T[m], T[S m]\]))).
  { intros. pose proof H3. destruct H6 as [H6[H7[H8[H9[]]]]].
    assert (\[T[m], T[S m]\] ⊂ \[a, b\]).
    { red; intros. applyClassifier1 H12. destruct H12. apply Classifier1.
      assert (a <= T[m] /\ T[S m] <= b) as [].
      { split; [rewrite <-H10 | rewrite <-H11];
        apply (Seg_Increase_a T a b (S n)); eauto; lia. } lra. }
    assert (NotEmpty (\[T[m], T[S m]\]) /\ NotEmpty (\[a, b\])) as [].
    { assert ((T[m] + T[S m])/2 ∈ (\[T[m], T[S m]\])).
      { assert (m < S n)%nat. lia. apply H9 in H13. apply Classifier1; split; lra. }
      split; red; eauto. }
    assert (DBoundedFun f (\[T[m], T[S m]\])).
    { destruct H0 as [H0[H15[]]]. repeat split; auto. red; intros; auto.
      exists x0. intros. apply H16; auto. }
    apply (inf_Coro_1 f) in H13 as [], H14 as []; auto.
    destruct (Rle_or_lt (inf_fD f (\[a, b\])) (inf_fD f (\[T[m], T[S m]\]))).
    auto. apply H16 in H18 as [x0[]].
    assert (x0 ∈ ran[f|[\[a, b\]]]).
    { applyClassifier1 H18. destruct H18. applyClassifier1 H18. destruct H18.
      apply Classifier1. exists x1. apply Classifier1; split; auto.
      applyClassifier2 H20. destruct H20. apply Classifier2; split; auto. }
    apply H14 in H20. exfalso. lra. }
  assert ((inf_fD f (\[a, b\])) * (b - a)
    = Σ \{\ λ u v, v = (inf_fD f (\[a, b\])) * (T[S u] - T[u]) \}\ n).
  { assert (∀ u k, (inf_fD f (\[a, b\])) * (u[S k] - u[0%nat])
      = Σ \{\ λ i v, v = (inf_fD f (\[a, b\])) * (u[S i] - u[i]) \}\ k).
    { intros u m. induction m; simpl; rewrite FunValue; auto.
      rewrite <-IHm. lra. } pose proof (H6 T n).
    destruct H3 as [_[_[_[_[]]]]]. rewrite <-H7, H3, H8; auto. }
  rewrite H4 in H2. apply H1 in H2.
  assert ((Low_sum f T n) >= (inf_fD f (\[a, b\])) * (b - a)).
  { rewrite H6. apply Σ_Fact3. intros.
    assert (\{\ λ i0 s, s = (inf_fD f (\[T[i0], T[S i0]\]))
      * (T[S i0] - T[i0]) \}\[i] = (inf_fD f (\[T[i], T[S i]\]))
      * (T[S i] - T[i]) /\ \{\ λ u v, v = (inf_fD f (\[a, b\]))
      * (T[S u] - T[u]) \}\[i] = (inf_fD f (\[a, b\])) * (T[S i] - T[i])) as [].
    { split; apply f_x_T; try apply Classifier2; auto; red; intros;
      applyClassifier2 H8; applyClassifier2 H9; subst; auto. }
    rewrite H8, H9. apply Rmult_ge_compat_r. left.
    destruct H3 as [_[_[_[]]]]. assert (i < S n)%nat. lia. apply H3 in H11.
    lra. apply H5 in H7. lra. } lra.
Qed.

(* 性质5c 函数的上确界乘区间宽度 大于等于 上积分 *)
Property Property9_6_5c : ∀ f a b, a < b -> DBoundedFun f (\[a, b\])
  -> (sup_fD f (\[a, b\])) * (b - a) >= (Up_Integral f a b).
Proof.
  intros. pose proof H0. apply Up_Integral_Corollary in H1 as [H1 _]; auto.
  pose proof H. apply (ST_sT_NotEmpty f) in H2 as [[] _].
  pose proof H2. applyClassifier1 H3. destruct H3 as [n[T[]]].
  assert (∀ m, (m <= n)%nat -> (sup_fD f (\[T[m], T[S m]\]))
    <= (sup_fD f (\[a, b\]))).
  { intros. pose proof H3. destruct H6 as [H6[H7[H8[H9[]]]]].
    assert (\[T[m], T[S m]\] ⊂ \[a, b\]).
    { red; intros. applyClassifier1 H12. destruct H12. apply Classifier1.
      assert (a <= T[m] /\ T[S m] <= b) as [].
      { split; [rewrite <-H10 | rewrite <-H11];
        apply (Seg_Increase_a T a b (S n)); eauto; lia. } lra. }
    assert (NotEmpty (\[T[m], T[S m]\]) /\ NotEmpty (\[a, b\])) as [].
    { assert ((T[m] + T[S m])/2 ∈ (\[T[m], T[S m]\])).
      { assert (m < S n)%nat. lia. apply H9 in H13. apply Classifier1; split; lra. }
      split; red; eauto. }
    assert (DBoundedFun f (\[T[m], T[S m]\])).
    { destruct H0 as [H0[H15[]]]. repeat split; auto. red; intros; auto.
      exists x0. intros. apply H16; auto. }
    apply (sup_Coro_1 f) in H13 as [], H14 as []; auto.
    destruct (Rle_or_lt (sup_fD f (\[T[m], T[S m]\])) (sup_fD f (\[a, b\]))).
    auto. apply H16 in H18 as [x0[]].
    assert (x0 ∈ ran[f|[\[a, b\]]]).
    { applyClassifier1 H18. destruct H18. applyClassifier1 H18. destruct H18.
      apply Classifier1. exists x1. apply Classifier1; split; auto.
      applyClassifier2 H20. destruct H20. apply Classifier2; split; auto. }
    apply H14 in H20. exfalso. lra. }
  assert ((sup_fD f (\[a, b\])) * (b - a)
    = Σ \{\ λ u v, v = (sup_fD f (\[a, b\])) * (T[S u] - T[u]) \}\ n).
  { assert (∀ u k, (sup_fD f (\[a, b\])) * (u[S k] - u[0%nat])
      = Σ \{\ λ i v, v = (sup_fD f (\[a, b\])) * (u[S i] - u[i]) \}\ k).
    { intros u m. induction m; simpl; rewrite FunValue; auto.
      rewrite <-IHm. lra. } pose proof (H6 T n).
    destruct H3 as [_[_[_[_[]]]]]. rewrite <-H7, H3, H8; auto. }
  rewrite H4 in H2. apply H1 in H2.
  assert ((sup_fD f (\[a, b\])) * (b - a) >= (Up_sum f T n)).
  { rewrite H6. apply Σ_Fact3. intros.
    assert (\{\ λ i0 s, s = (sup_fD f (\[T[i0], T[S i0]\]))
      * (T[S i0] - T[i0]) \}\[i] = (sup_fD f (\[T[i], T[S i]\]))
      * (T[S i] - T[i]) /\ \{\ λ u v, v = (sup_fD f (\[a, b\]))
      * (T[S u] - T[u]) \}\[i] = (sup_fD f (\[a, b\])) * (T[S i] - T[i])) as [].
    { split; apply f_x_T; try apply Classifier2; auto; red; intros;
      applyClassifier2 H8; applyClassifier2 H9; subst; auto. }
    rewrite H8, H9. apply Rmult_ge_compat_r. left.
    destruct H3 as [_[_[_[]]]]. assert (i < S n)%nat. lia. apply H3 in H11.
    lra. apply H5 in H7. lra. } lra.
Qed.

(* 性质六·达布定理 引理1 任意两个分割, 它们的上合之间的不等式关系 *)
Lemma Lemma9_6_6a : ∀ f T T' a b n m, DBoundedFun f (\[a, b\])
  -> Seg T a b (S n) -> Seg T' a b (S m) -> (Up_sum f T n) <= (Up_sum f T' m)
  + (sup_fD f (\[a, b\]) - inf_fD f (\[a, b\])) * (INR (S (S m))) * (mold T (S n)).
Proof.
  intros. pose proof H1. apply (Lemma9_6_3b T T' a b (S n) (S m)) in H2
  as [k[H2[H3[H4[H5[]]]]]]; auto. apply (Property9_6_2a f) in H6, H7; auto.
  assert (n + (k - S n) = k - 1 /\ m + (k - S m) = k - 1)%nat as []. split; lia.
  rewrite H8 in H6. rewrite H9 in H7.
  assert ((Up_sum f T n) <= (Up_sum f T' m) + (sup_fD f (\[a, b\])
    - inf_fD f (\[a, b\])) * (INR (k - S n)%nat) * (mold T (S n))). lra.
  assert ((INR (k - (S n))%nat) <= INR (S (S m))). { apply le_INR. lia. }
  assert (a < b).
  { pose proof H0. destruct H12 as [_[_[_[_[]]]]]. rewrite <-H12, <-H13.
    apply (Seg_StrictlyIncrease_a T a b (S n)); auto; lia. }
  assert (NotEmpty (\[a, b\])). { exists ((a + b)/2). apply Classifier1; lra. }
  pose proof H13. destruct H13. apply (sup_inf_Coro_1 f _ x) in H13; auto.
  assert (0 <= (sup_fD f (\[a, b\])) - (inf_fD f (\[a, b\]))). lra.
  assert (0 < (mold T (S n))).
  { pose proof H0. apply SegMold_Max with (k := 0%nat) in H16.
    destruct H0 as [_[_[_[]]]]. assert (T[0%nat] < T[1%nat]).
    apply H0; lia. lra. lia. }
  assert ((sup_fD f (\[a, b\]) - inf_fD f (\[a, b\])) * (INR (k - S n)%nat)
    * (mold T (S n)) <= (sup_fD f (\[a, b\]) - inf_fD f (\[a, b\]))
    * (INR (S (S m))) * (mold T (S n))).
  { apply Rmult_le_compat_r, Rmult_le_compat_l; auto. lra. } lra.
Qed.

(* 性质六·达布定理 引理2 任意两个分割, 它们的下合之间的不等式关系 *)
Lemma Lemma9_6_6b : ∀ f T T' a b n m, DBoundedFun f (\[a, b\])
  -> Seg T a b (S n) -> Seg T' a b (S m) -> (Low_sum f T' m)
    - (sup_fD f (\[a, b\]) - inf_fD f (\[a, b\])) * (INR (S (S m)))
    * (mold T (S n)) <= (Low_sum f T n).
Proof.
  intros. pose proof H1. apply (Lemma9_6_3b T T' a b (S n) (S m)) in H2
  as [k[H2[H3[H4[H5[]]]]]]; auto. apply (Property9_6_2b f) in H6, H7; auto.
  assert (n + (k - S n) = k - 1 /\ m + (k - S m) = k - 1)%nat as []. split; lia.
  rewrite H8 in H6. rewrite H9 in H7.
  assert ((Low_sum f T' m) - (sup_fD f (\[a, b\])
    - inf_fD f (\[a, b\])) * (INR (k - S n)%nat) * (mold T (S n))
    <= (Low_sum f T n)). lra.
  assert ((INR (k - (S n))%nat) <= INR (S (S m))). { apply le_INR. lia. }
  assert (a < b).
  { pose proof H0. destruct H12 as [_[_[_[_[]]]]]. rewrite <-H12, <-H13.
    apply (Seg_StrictlyIncrease_a T a b (S n)); auto; lia. }
  assert (NotEmpty (\[a, b\])). { exists ((a + b)/2). apply Classifier1; lra. }
  pose proof H13. destruct H13. apply (sup_inf_Coro_1 f _ x) in H13; auto.
  assert (0 <= (sup_fD f (\[a, b\])) - (inf_fD f (\[a, b\]))). lra.
  assert (0 < (mold T (S n))).
  { pose proof H0. apply SegMold_Max with (k := 0%nat) in H16.
    destruct H0 as [_[_[_[]]]]. assert (T[0%nat] < T[1%nat]).
    apply H0; lia. lra. lia. }
  assert ((sup_fD f (\[a, b\]) - inf_fD f (\[a, b\])) * (INR (k - S n)%nat)
    * (mold T (S n)) <= (sup_fD f (\[a, b\]) - inf_fD f (\[a, b\]))
    * (INR (S (S m))) * (mold T (S n))).
  { apply Rmult_le_compat_r, Rmult_le_compat_l; auto. lra. } lra.
Qed.

(* 定义 模 到 分割上和 的函数 *)
Definition ST_Fun f a b := \{\ λ u v, 0 < u <= b - a
  /\ v = c \{ λ w, ∃ T n, Seg T a b (S n) /\ u = mold T (S n)
    /\ w = Up_sum f T n \} \}\.

Corollary ST_Fun_is_Function : ∀ f a b, a < b -> Function (ST_Fun f a b)
  /\ dom[ST_Fun f a b] = \{ λ u, 0 < u <= b - a \}.
Proof.
  intros. split; try (apply AxiomI; split; intros).
  - red; intros. applyClassifier2 H0. applyClassifier2 H1. destruct H0, H1.
    rewrite H2, H3; auto.
  - applyClassifier1 H0. destruct H0. applyClassifier2 H0. apply Classifier1. tauto.
  - applyClassifier1 H0. apply Classifier1. exists (c \{ λ w, ∃ T n, Seg T a b (S n)
      /\ z = mold T (S n) /\ w = Up_sum f T n \}). apply Classifier2; auto.
Qed.

Corollary ST_Fun_Value : ∀ f a b x, a < b -> 0 < x <= (b - a)
  -> ∃ T n, Seg T a b (S n) /\ x = mold T (S n)
    /\ (ST_Fun f a b)[x] = Up_sum f T n.
Proof.
  intros. pose proof H. apply (ST_Fun_is_Function f) in H1 as [].
  assert (x ∈ dom[ST_Fun f a b]). { rewrite H2. apply Classifier1; auto. }
  apply x_fx_T in H3; auto. applyClassifier2 H3. destruct H3.
  assert (NotEmpty (\{ λ w, ∃ T n, Seg T a b (S n) /\ x = mold T (S n)
    /\ w = Up_sum f T n \})).
  { apply (Seg_Exists a b x) in H as [T[n[]]]; auto. exists (Up_sum f T n).
    apply Classifier1; eauto. }
  apply Axiomc in H5. rewrite <-H4 in H5. applyClassifier1 H5; auto.
Qed.

(* 定义 模 到 分割下和 的函数 *)
Definition sT_Fun f a b := \{\ λ u v, 0 < u <= b - a
  /\ v = c \{ λ w, ∃ T n, Seg T a b (S n) /\ u = mold T (S n)
    /\ w = Low_sum f T n \} \}\.

Corollary sT_Fun_is_Function : ∀ f a b, a < b -> Function (sT_Fun f a b)
  /\ dom[sT_Fun f a b] = \{ λ u, 0 < u <= b - a \}.
Proof.
  intros. split; try (apply AxiomI; split; intros).
  - red; intros. applyClassifier2 H0. applyClassifier2 H1. destruct H0, H1.
    rewrite H2, H3; auto.
  - applyClassifier1 H0. destruct H0. applyClassifier2 H0. apply Classifier1. tauto.
  - applyClassifier1 H0. apply Classifier1. exists (c \{ λ w, ∃ T n, Seg T a b (S n)
      /\ z = mold T (S n) /\ w = Low_sum f T n \}). apply Classifier2; auto.
Qed.

Corollary sT_Fun_Value : ∀ f a b x, a < b -> 0 < x <= (b - a)
  -> ∃ T n, Seg T a b (S n) /\ x = mold T (S n)
    /\ (sT_Fun f a b)[x] = Low_sum f T n.
Proof.
  intros. pose proof H. apply (sT_Fun_is_Function f) in H1 as [].
  assert (x ∈ dom[sT_Fun f a b]). { rewrite H2. apply Classifier1; auto. }
  apply x_fx_T in H3; auto. applyClassifier2 H3. destruct H3.
  assert (NotEmpty (\{ λ w, ∃ T n, Seg T a b (S n) /\ x = mold T (S n)
    /\ w = Low_sum f T n \})).
  { apply (Seg_Exists a b x) in H as [T[n[]]]; auto. exists (Low_sum f T n).
    apply Classifier1; eauto. }
  apply Axiomc in H5. rewrite <-H4 in H5. applyClassifier1 H5; auto.
Qed.


(* 性质六·达布定理 引理3 函数下确界小于上确界时 上积分是模趋于0时上和的极限 *)
Lemma Lemma9_6_6c : ∀ f a b, a < b -> DBoundedFun f (\[a, b\])
  -> inf_fD f (\[a, b\]) < sup_fD f (\[a, b\])
  -> limit_pos (ST_Fun f a b) 0 (Up_Integral f a b).
Proof.
  intros. split. apply ST_Fun_is_Function; auto. exists (b - a). split. lra.
  split. red; intros. pose proof H. apply (ST_Fun_is_Function f) in H3 as [].
  rewrite H4. applyClassifier1 H2. apply Classifier1; lra. intros.
  apply (Up_Integral_Corollary f a b H) in H0 as H3.
  destruct H3. assert (Up_Integral f a b + ε / 2 > Up_Integral f a b). lra.
  apply H4 in H5. destruct H5 as [x[]]. applyClassifier1 H5. 
  destruct H5 as [n[T'[]]].
  assert(∀ T m, Seg T a b (S m) -> Up_sum f T m <= Up_sum f T' n + 
  (sup_fD f (\[a, b\]) - inf_fD f (\[a, b\])) * (INR (S (S n))) * 
  (mold T (S m))).
  { intros. apply (Lemma9_6_6a f _ _ _ _ m n); auto. }
  assert(I1 : ∃ t,
    t = ε/(2 * (sup_fD f (\[a, b\]) - inf_fD f (\[a, b\])) * INR(S (S n)))).
  { exists (ε/(2*(sup_fD f (\[a, b\]) - inf_fD f (\[a, b\]))* 
    INR(S (S n)))); auto. }
  destruct I1 as [t I1]. assert(t > 0).
  { rewrite I1. unfold Rdiv. apply Rmult_gt_0_compat. lra. apply Rlt_gt.
    apply Rinv_0_lt_compat. apply Rmult_gt_0_compat. lra. apply lt_0_INR. lia. }
  apply (Examp1 t (b-a)) in H9 as H10;[|lra]. destruct H10 as [δ[H10[]]].
  exists δ. split. lra. intros. 
  apply (ST_Fun_Value f a b x0) in H as H';[|lra]. 
  destruct H' as [T[m[H14[]]]]. rewrite H16.
  apply (H8 T m) in H14 as H14'.
  assert(((sup_fD f (\[a, b\]) - inf_fD f (\[a, b\])) * INR (S (S n)) * mold T (S m))
  < (ε / 2)). { assert( x0 < t). lra.  
    assert(I2: (sup_fD f (\[a, b\]) - inf_fD f (\[a, b\])) * INR (S (S n)) > 0).
    { apply Rmult_gt_0_compat. lra. apply lt_0_INR. lia. }
    apply (Rmult_lt_compat_l ((sup_fD f (\[a, b\]) - inf_fD f (\[a, b\])) 
    * INR (S (S n))) _ _) in H17; auto.
    replace ((sup_fD f (\[a, b\]) - inf_fD f (\[a, b\])) * INR (S (S n))* t)
    with (ε / 2) in H17. subst x0. lra. 
    unfold Rdiv in I1. rewrite I1.  rewrite <- Rmult_assoc.
    rewrite (Rmult_assoc 2 (sup_fD f (\[a, b\]) - inf_fD f (\[a, b\])) _).
    rewrite Rinv_mult,(Rmult_assoc _ ε),<-(Rmult_assoc ε),<-(Rmult_assoc _ (ε * /2)).
    rewrite Rinv_r_simpl_m; auto. lra. }
    apply <- Abs_R. subst x. split;[|lra].
    assert(Up_sum f T m >= Up_Integral f a b).
    apply H3. apply Classifier1. exists m, T. split;auto. lra.
Qed.

(* 性质六·达布定理 引理4 函数下确界等于上确界时(常值函数) 上积分是模趋于0时上和的极限 *)
Lemma Lemma9_6_6d : ∀ f a b, a < b -> DBoundedFun f (\[a, b\])
  -> inf_fD f (\[a, b\]) = sup_fD f (\[a, b\])
  -> limit_pos (ST_Fun f a b) 0 (Up_Integral f a b).
Proof.
  intros. pose proof (Property9_6_5a f a b H H0).
  pose proof (Property9_6_5b f a b H H0).
  pose proof (Property9_6_5c f a b H H0).
  pose proof (sup_inf_Coro_3 f (\[a, b\]) H0 H1).
  pose proof H. apply (ST_Fun_is_Function f) in H6 as [].
  split; auto. exists (b - a). split. lra. split. red; intros.
  applyClassifier1 H8. rewrite H7. apply Classifier1. lra. intros. exists ((b - a)/2).
  split. lra. intros. assert (0 < x <= b - a). lra.
  apply (ST_Fun_Value f) in H10 as [T[n[H10[]]]]; auto. rewrite H12.
  assert (Up_sum f T n = inf_fD f (\[a, b\]) * (b - a)).
  { assert (Σ \{\ λ i s, s = sup_fD f (\[T[i], T[S i]\]) * (T[S i] - T[i]) \}\ n
      = Σ \{\ λ i s, s = (inf_fD f (\[a, b\])) * (T[S i] - T[i]) \}\ n).
    { apply Σ_Fact5. intros. rewrite FunValue,FunValue.
      assert (T[x0] < T[S x0]). { destruct H10. apply H14. lia. }
      pose proof (Seg_Increase_a T a b (S n) H10).
      assert (\[T[x0], T[S x0]\] ⊂ \[a, b\]).
      { red; intros. destruct H10 as [_[_[_[_[]]]]]. applyClassifier1 H16.
        apply Classifier1. destruct H16. rewrite <-H10,<-H17.
        assert (T[0%nat] <= T[x0] /\ T[S x0] <= T[S n]) as [].
        { split; apply H15; lia. } lra. }
      assert (DBoundedFun f (\[T[x0], T[S x0]\])).
      { destruct H0 as [H0[H17[]]]. split; auto. split; eauto. red; auto. }
      assert ((T[x0] + T[S x0])/2 ∈ (\[T[x0], T[S x0]\])). { apply Classifier1. lra. }
      assert (NotEmpty (\[T[x0], T[S x0]\])). red; eauto.
      apply (sup_Coro_1 f) in H19 as []; auto. red in H19.
      assert (sup_fD f (\[a, b\]) <= sup_fD f (\[T[x0], T[S x0]\])).
      { apply H19. rewrite <-H1,<-(H5 ((T[x0] + T[S x0])/2)); auto.
        apply Classifier1. exists ((T[x0] + T[S x0])/2). apply Classifier1. split.
        destruct H0 as [H0[]]. apply x_fx_T; auto. apply Classifier2.
        split; auto. apply Classifier1; auto. }
      destruct H21. apply H20 in H21 as [y[]].
      pose proof H0. apply sup_Coro_1 in H23 as [H23 _].
      assert (y ∈ ran[f|[\[a, b\]]]).
      { applyClassifier1 H21. destruct H21. applyClassifier1 H21. destruct H21.
        apply Classifier1. exists x1. apply Classifier1; split; auto.
        apply Classifier2. applyClassifier2 H24. destruct H24. auto. }
      apply H23 in H24. exfalso. lra. exists ((a + b)/2). apply Classifier1; lra.
      rewrite H1,H21; auto. }
    assert (∀ A B n, Σ \{\ λ i s, s = A * (B i) \}\ n
      = A * Σ \{\ λ i s, s = (B i) \}\ n).
    { intros. induction n0. simpl. rewrite FunValue. rewrite FunValue. auto.
      simpl. rewrite IHn0,FunValue,FunValue. simpl. lra. }
    unfold Up_sum. rewrite H13,H14,(Lemma9_6_1c T n a b); auto. }
  assert (inf_fD f (\[a, b\]) * (b - a) = Up_Integral f a b).
  { rewrite H1 in H3. rewrite H1. lra. }
  rewrite H13,H14,Rminus_diag,Abs_ge; lra.
Qed.

(* 性质六·达布定理 引理5 函数下确界小于上确界时 下积分是模趋于0时下和的极限 *)
Lemma Lemma9_6_6e : ∀ f a b, a < b -> DBoundedFun f (\[a, b\])
  -> inf_fD f (\[a, b\]) < sup_fD f (\[a, b\])
  -> limit_pos (sT_Fun f a b) 0 (Low_Integral f a b).
Proof.
  intros. split. apply sT_Fun_is_Function; auto. exists (b - a). split. lra.
  split. red; intros. pose proof H. apply (sT_Fun_is_Function f) in H3 as [].
  rewrite H4. applyClassifier1 H2. apply Classifier1; lra. intros.
  apply (Low_Integral_Corollary f a b H) in H0 as H3; auto. 
  destruct H3. assert(Low_Integral f a b - ε / 2 < Low_Integral f a b). lra.
  apply H4 in H5. destruct H5 as [x[]]. applyClassifier1 H5. destruct H5 as [n[T'[]]].
  assert(∀T m, Seg T a b (S m) -> Low_sum f T' n - (sup_fD f (\[a, b\]) 
  - inf_fD f (\[a, b\])) * (INR (S (S n))) * (mold T (S m)) <= Low_sum f T m).
  { intros. apply (Lemma9_6_6b f _ _ _ _ m n); auto. }
  assert(I1:∃t, t = ε/(2*(sup_fD f (\[a, b\]) - inf_fD f (\[a, b\]))*INR(S (S n)))).
  { exists (ε/(2*(sup_fD f (\[a, b\]) - inf_fD f (\[a, b\]))*INR(S (S n)))); auto. }
  destruct I1 as [t I1]. assert(t > 0).
  { rewrite I1. unfold Rdiv. apply Rmult_gt_0_compat. lra. apply Rlt_gt.
    apply Rinv_0_lt_compat. apply Rmult_gt_0_compat. lra. apply lt_0_INR. lia. }
  apply (Examp1 t (b-a)) in H9 as H10;[|lra]. destruct H10 as [δ[H10[]]].
  exists δ. split. lra. intros. 
  apply (sT_Fun_Value f a b x0) in H as H';[|lra]. 
  destruct H' as [T[m[H14[]]]]. rewrite H16.
  apply (H8 T m) in H14 as H14'. 
  assert(((sup_fD f (\[a, b\]) - inf_fD f (\[a, b\])) * INR (S (S n)) * mold T (S m))
  < (ε / 2)). { assert( x0 < t). lra.  
    assert(I2: (sup_fD f (\[a, b\]) - inf_fD f (\[a, b\])) * INR (S (S n)) > 0).
    { apply Rmult_gt_0_compat. lra. apply lt_0_INR. lia. }
    apply (Rmult_lt_compat_l ((sup_fD f (\[a, b\]) - inf_fD f (\[a, b\])) 
    * INR (S (S n))) _ _) in H17; auto.
    replace ((sup_fD f (\[a, b\]) - inf_fD f (\[a, b\])) * INR (S (S n))* t)
    with (ε / 2) in H17. subst x0. lra. 
    unfold Rdiv in I1. rewrite I1.  rewrite <- Rmult_assoc.
    rewrite (Rmult_assoc 2 (sup_fD f (\[a, b\]) - inf_fD f (\[a, b\])) _).
    rewrite Rinv_mult,(Rmult_assoc _ ε),<-(Rmult_assoc ε),<-(Rmult_assoc _ (ε * /2)).
    rewrite Rinv_r_simpl_m; auto. lra. }
    apply <- Abs_R. subst x. split;[lra|]. 
    assert(Low_sum f T m <= Low_Integral f a b).
    apply H3. apply Classifier1. exists m, T. split;auto. lra.
Qed.

(* 性质六·达布定理 引理6 函数下确界等于上确界时(常值函数) 下积分是模趋于0时下和的极限 *)
Lemma Lemma9_6_6f : ∀ f a b, a < b -> DBoundedFun f (\[a, b\])
  -> inf_fD f (\[a, b\]) = sup_fD f (\[a, b\])
  -> limit_pos (sT_Fun f a b) 0 (Low_Integral f a b).
Proof.
  intros. pose proof (Property9_6_5a f a b H H0).
  pose proof (Property9_6_5b f a b H H0).
  pose proof (Property9_6_5c f a b H H0).
  pose proof (sup_inf_Coro_3 f (\[a, b\]) H0 H1).
  pose proof H. apply (sT_Fun_is_Function f) in H6 as [].
  split; auto. exists (b - a). split. lra. split. red; intros.
  applyClassifier1 H8. rewrite H7. apply Classifier1. lra. intros. exists ((b - a)/2).
  split. lra. intros. assert (0 < x <= b - a). lra.
  apply (sT_Fun_Value f) in H10 as [T[n[H10[]]]]; auto. rewrite H12.
  assert (Low_sum f T n = sup_fD f (\[a, b\]) * (b - a)).
  { assert (Σ \{\ λ i s, s = inf_fD f (\[T[i], T[S i]\]) * (T[S i] - T[i]) \}\ n
      = Σ \{\ λ i s, s = (sup_fD f (\[a, b\])) * (T[S i] - T[i]) \}\ n).
    { apply Σ_Fact5. intros. rewrite FunValue,FunValue.
      assert (T[x0] < T[S x0]). { destruct H10. apply H14. lia. }
      pose proof (Seg_Increase_a T a b (S n) H10).
      assert (\[T[x0], T[S x0]\] ⊂ \[a, b\]).
      { red; intros. destruct H10 as [_[_[_[_[]]]]]. applyClassifier1 H16.
        apply Classifier1. destruct H16. rewrite <-H10,<-H17.
        assert (T[0%nat] <= T[x0] /\ T[S x0] <= T[S n]) as [].
        { split; apply H15; lia. } lra. }
      assert (DBoundedFun f (\[T[x0], T[S x0]\])).
      { destruct H0 as [H0[H17[]]]. split; auto. split; eauto. red; auto. }
      assert ((T[x0] + T[S x0])/2 ∈ (\[T[x0], T[S x0]\])). { apply Classifier1. lra. }
      assert (NotEmpty (\[T[x0], T[S x0]\])). red; eauto.
      apply (inf_Coro_1 f) in H19 as []; auto. red in H19.
      assert (inf_fD f (\[a, b\]) >= inf_fD f (\[T[x0], T[S x0]\])).
      { apply H19. rewrite <-(H5 ((T[x0] + T[S x0])/2)); auto.
        apply Classifier1. exists ((T[x0] + T[S x0])/2). apply Classifier1. split.
        destruct H0 as [H0[]]. apply x_fx_T; auto. apply Classifier2.
        split; auto. apply Classifier1; auto. }
      destruct H21. apply H20 in H21 as [y[]].
      pose proof H0. apply inf_Coro_1 in H23 as [H23 _].
      assert (y ∈ ran[f|[\[a, b\]]]).
      { applyClassifier1 H21. destruct H21. applyClassifier1 H21. destruct H21.
        apply Classifier1. exists x1. apply Classifier1; split; auto.
        apply Classifier2. applyClassifier2 H24. destruct H24. auto. }
      apply H23 in H24. exfalso. lra. exists ((a + b)/2). apply Classifier1; lra.
      rewrite <-H1,H21; auto. }
    assert (∀ A B n, Σ \{\ λ i s, s = A * (B i) \}\ n
      = A * Σ \{\ λ i s, s = (B i) \}\ n).
    { intros. induction n0. simpl. rewrite FunValue. rewrite FunValue. auto.
      simpl. rewrite IHn0,FunValue,FunValue. simpl. lra. }
    unfold Low_sum. rewrite H13,H14,(Lemma9_6_1c T n a b); auto. }
  assert (sup_fD f (\[a, b\]) * (b - a) = Low_Integral f a b).
  { rewrite <-H1 in H4. rewrite <-H1. lra. }
  rewrite H13,H14,Rminus_diag,Abs_ge; lra.
Qed.

(* 性质六·达布定理 上积分是模趋于0时上和的极限 *)
Property Property9_6_6a : ∀ f a b, a < b -> DBoundedFun f (\[a, b\])
  -> limit_pos (ST_Fun f a b) 0 (Up_Integral f a b).
Proof.
  intros. pose proof H0. apply sup_inf_Coro_2 in H1 as [].
  apply Lemma9_6_6c; auto. apply Lemma9_6_6d; auto.
  exists ((a + b)/2). apply Classifier1. lra.
Qed.

(* 性质六·达布定理 下积分是模趋于0时下和的极限 *)
Property Property9_6_6b : ∀ f a b, a < b -> DBoundedFun f (\[a, b\])
  -> limit_pos (sT_Fun f a b) 0 (Low_Integral f a b).
Proof.
  intros. pose proof H0. apply sup_inf_Coro_2 in H1 as [].
  apply Lemma9_6_6e; auto. apply Lemma9_6_6f; auto.
  exists ((a + b)/2). apply Classifier1. lra.
Qed.

(* 可积第一充要条件 引理1 若定积分J存在, 则上和与下和在分割的模趋于0时极限均为J *)
Lemma Lemma9_14a :∀ f a b J, a < b
  -> DBoundedFun f (\[a, b\]) -> Def_Integral f a b J
  -> limit_pos (ST_Fun f a b) 0 J /\ limit_pos (sT_Fun f a b) 0 J.
Proof.
  intros. pose proof H1. destruct H2 as [H2[_[]]]. split.
  - split. apply ST_Fun_is_Function; auto. exists (b - a). split. lra.
    split. red; intros. pose proof H. apply (ST_Fun_is_Function f) in H6 as []. 
    rewrite H7. applyClassifier1 H5. apply Classifier1; lra. intros.
    assert(I1: ε/2 > 0). lra. apply H4 in I1 as H6. destruct H6 as [δ[]].
    pose proof H6. apply (Examp1 δ (b-a)) in H8 as [δ'[H8[]]];[|lra].
    exists δ'. split; [lra|]. intros. pose proof H.
    apply (ST_Fun_Value f a b x) in H12; [|lra]. destruct H12 as [T[n[H13[]]]].
    rewrite H14. clear H4.
    apply (Property9_6_1a f T a b n) in H13 as H15; auto. destruct H15. 
    assert(I2 : Up_sum f T n - ε / 2 < Up_sum f T n). lra. apply H15 in I2.
    destruct I2 as [x0[]]. pose proof (H4 x0).  apply H18 in H16 as I2. 
    applyClassifier1 H16. destruct H16 as [ξ[]]. apply (H7 _ ξ ) in H13 as H20; 
    auto;[|lra]. clear H4 H15 H18. apply Abs_R in H20.
    unfold IntegralSum in H19. unfold IntegralSum in H20.
    rewrite <- H19 in H20. apply Abs_R; split; lra.
  - split. apply sT_Fun_is_Function; auto. exists (b - a). split. lra.
    split. red; intros. pose proof H. apply (sT_Fun_is_Function f) in H6 as []. 
    rewrite H7. applyClassifier1 H5. apply Classifier1; lra. intros.
    assert(I1: ε/2 > 0). lra. apply H4 in I1 as H6. destruct H6 as [δ[]].
    pose proof H6. apply (Examp1 δ (b-a)) in H8 as [δ'[H8[]]];[|lra].
    exists δ'. split; [lra|]. intros. pose proof H.
    apply (sT_Fun_Value f a b x) in H12; [|lra]. destruct H12 as [T[n[H12[]]]].
    rewrite H14. clear H4.
    apply (Property9_6_1b f T a b n) in H12 as H15;  auto. destruct H15. 
    assert(I2 : Low_sum f T n + ε/2 > Low_sum f T n). lra.
    apply H15 in I2. destruct I2 as [x0[]]. pose proof (H4 x0).
    apply H18 in H16 as I2. clear H4 H18 H15.
    applyClassifier1 H16. destruct H16 as [ξ[]]. apply (H7 _ ξ ) in H12 as H19; 
    auto;[|lra]. apply Abs_R in H19. unfold IntegralSum in H15.
    unfold IntegralSum in H19. rewrite <- H15 in H19. apply Abs_R; split; lra.
Qed.

(* 可积的第一充要条件  引理2  函数下确界小于上确界时 的 充要条件 *)
Lemma Lemma9_14b :∀ f a b, a < b -> DBoundedFun f (\[a, b\])
  -> inf_fD f (\[a, b\]) < sup_fD f (\[a, b\])
  -> (∃ J, Def_Integral f a b J) <-> (Low_Integral f a b) = (Up_Integral f a b).
Proof.
  intros f a b H H0 H'. split; intros.
  - destruct H1 as [J]. pose proof H1.
    apply (Lemma9_14a ) in H2 as [L1 L2]; auto.
    destruct H1 as [H1[_[]]].
    apply Property9_6_6b in H0 as H0'; auto. 
    apply Property9_6_6a in H0 as H0''; auto.
    apply (Theorem3_2b (ST_Fun f a b) 0 J (Up_Integral f a b)) in H0''; auto.
    apply (Theorem3_2b (sT_Fun f a b) 0 J (Low_Integral f a b)) in H0'; auto. lra.
  - assert(I3: ∃J, J = Low_Integral f a b). exists (Low_Integral f a b); auto.
    destruct I3 as [J]. exists J. pose proof H0. destruct H3 as [H3[]].
    repeat (split; auto). intros.
    apply (Up_Integral_Corollary f a b H) in H0 as I3; auto.
    apply (Low_Integral_Corollary f a b H) in H0 as I2; auto.
    destruct I3. assert(Up_Integral f a b + ε / 2 > Up_Integral f a b). lra.
    apply H8 in H9. destruct H9 as [x[]]. applyClassifier1 H9.
    destruct H9 as [n[T'[]]]. destruct I2.
    assert(Low_Integral f a b - ε / 2 < Low_Integral f a b). lra.
    apply H13 in H14. destruct H14 as [y[]]. applyClassifier1 H14. 
    destruct H14 as [n'[T''[]]].
    assert(∀T m, Seg T a b (S m) -> Up_sum f T m <= Up_sum f T' n + 
    (sup_fD f (\[a, b\]) - inf_fD f (\[a, b\])) * (INR (S (S n))) * (mold T (S m))).
    { intros. apply (Lemma9_6_6a f _ _ _ _ m n); auto. }
    assert(∀T m, Seg T a b (S m) -> Low_sum f T'' n' - (sup_fD f (\[a, b\]) 
    - inf_fD f (\[a, b\])) * (INR (S (S n'))) * (mold T (S m)) <= Low_sum f T m).
    { intros. apply (Lemma9_6_6b f _ _ _ _ m n'); auto. }
    assert(I4: ∃t,
      t = ε/(2*(sup_fD f (\[a, b\]) - inf_fD f (\[a, b\]))*INR(S (S n)))).
    { exists (ε/(2*(sup_fD f (\[a, b\]) - inf_fD f (\[a, b\]))*INR(S (S n)))); auto. }
    destruct I4 as [t I4]. assert(t > 0).
    { rewrite I4. unfold Rdiv. apply Rmult_gt_0_compat. lra. apply Rlt_gt.
      apply Rinv_0_lt_compat. apply Rmult_gt_0_compat. lra. apply lt_0_INR. lia. }
    assert(I5:∃t, t = ε/(2*(sup_fD f (\[a, b\]) - inf_fD f (\[a, b\]))*INR(S(S n')))).
    { exists (ε/(2*(sup_fD f (\[a, b\]) - inf_fD f (\[a, b\]))*INR(S(S n')))); auto. }
    destruct I5 as [t' I5]. assert(t' > 0).
    { rewrite I5. unfold Rdiv. apply Rmult_gt_0_compat. lra. apply Rlt_gt.
      apply Rinv_0_lt_compat. apply Rmult_gt_0_compat. lra. apply lt_0_INR. lia. }
    apply (Examp1 t t') in H20 as H21;[|lra]. destruct H21 as [δ[H21[]]].
    exists δ. split; auto. intros. 
    apply H17 in H24 as I1. apply H18 in H24 as I2. clear H17 H18.
    assert(mold T (S n0) < t). lra.  
    assert(mold T (S n0) < t'). lra.
    assert((sup_fD f (\[a, b\]) - inf_fD f (\[a, b\])) * INR (S (S n)) > 0).
    { apply Rmult_gt_0_compat. lra. apply lt_0_INR. lia. }
    assert((sup_fD f (\[a, b\]) - inf_fD f (\[a, b\])) * INR (S (S n')) > 0).
    { apply Rmult_gt_0_compat. lra. apply lt_0_INR. lia. }
    apply (Rmult_lt_compat_l ((sup_fD f (\[a, b\]) - inf_fD f (\[a, b\])) 
    * INR (S (S n))) _ _) in H17; auto.
    apply (Rmult_lt_compat_l ((sup_fD f (\[a, b\]) - inf_fD f (\[a, b\])) 
    * INR (S (S n'))) _ _) in H18; auto.
    rewrite I4 in H17. rewrite (Rmult_assoc 2 _ _) in H17.
    unfold Rdiv in H17. rewrite Rinv_mult in H17.
    rewrite (Rmult_comm (/2)),<-(Rmult_assoc ε),<-Rmult_assoc,<-Rmult_assoc,
    Rinv_r_simpl_m in H17; [ |lra].
    rewrite I5 in H18. rewrite (Rmult_assoc 2 _ _) in H18.
    unfold Rdiv in H18. rewrite Rinv_mult in H18.
    rewrite (Rmult_comm (/2)),<-(Rmult_assoc ε),<-Rmult_assoc,<-Rmult_assoc,
    Rinv_r_simpl_m in H18; [ |lra].
    assert(Up_sum f T n0 < Up_Integral f a b + ε). lra.
    assert(Low_sum f T n0 > Low_Integral f a b - ε). lra. 
    apply Abs_R. apply (Up_Low_sum_Coro_2 f T _ a b) in H25 as I6; auto.
    apply (Up_Low_sum_Coro_3 f T _ a b) in H25 as I7; auto.
    unfold IntegralSum in *. lra.
Qed.

(* 可积的第一充要条件  引理3  函数下确界等于上确界时(常值函数) 的 充要条件 *)
Lemma Lemma9_14c :∀ f a b, a < b -> DBoundedFun f (\[a, b\])
  -> inf_fD f (\[a, b\]) = sup_fD f (\[a, b\])
  -> (∃ J, Def_Integral f a b J) <-> (Low_Integral f a b) = (Up_Integral f a b).
Proof.
  split; intros.
  - destruct H2 as [J]. pose proof H2. apply (Lemma9_14a ) in H3 as []; auto.
    destruct H2 as [H2[_[]]]. apply Property9_6_6b in H0 as H7; auto.
    apply Property9_6_6a in H0 as H8; auto.
    apply (Theorem3_2b (ST_Fun f a b) 0 J (Up_Integral f a b)) in H8; auto.
    apply (Theorem3_2b (sT_Fun f a b) 0 J (Low_Integral f a b)) in H7; auto. lra.
  - destruct (Up_Integral_Corollary f a b H H0).
    destruct (Low_Integral_Corollary f a b H H0).
    exists (Low_Integral f a b). pose proof H0 as [H7[H8 _]].
    split; auto. split; auto. split; auto. intros.
    assert ((Low_Integral f a b) - ε < (Low_Integral f a b)
      < (Low_Integral f a b) + ε) as []. lra. rewrite H2 in H11.
    apply H6 in H10 as [y1[]]. apply H4 in H11 as [y2[]].
    applyClassifier1 H10. destruct H10 as [n1[T1[]]]. rewrite H14 in *.
    applyClassifier1 H11. destruct H11 as [n2[T2[]]]. rewrite H15 in *.
    exists 1. split. lra. intros.
    pose proof (Lemma9_6_6a f T T2 a b n n2 H0 H16 H11).
    pose proof (Lemma9_6_6b f T T1 a b n n1 H0 H16 H10).
    rewrite H1,Rminus_diag,Rmult_0_l,Rmult_0_l,Rplus_0_r in H19.
    rewrite H1,Rminus_diag,Rmult_0_l,Rmult_0_l,Rminus_0_r in H20.
    destruct (Property9_6_1a f T a b n H16 H0) as [H21 _].
    destruct (Property9_6_1b f T a b n H16 H0) as [H22 _].
    assert ((IntegralSum f T n ξ)
       ∈ \{ λ u,∃ ξ, SegPoints T ξ (S n) /\ u = IntegralSum f T n ξ \}).
    { apply Classifier1; eauto. }
    pose proof H23. apply H21 in H23. apply H22 in H24.
    apply Abs_R. lra.
Qed.

(* 可积的第一充要条件 *)
Theorem Theorem9_14 : ∀ f a b, a < b -> DBoundedFun f (\[a, b\])
  -> (∃ J, Def_Integral f a b J) <-> (Low_Integral f a b) = (Up_Integral f a b).
Proof.
  intros. pose proof H0. apply sup_inf_Coro_2 in H1 as [].
  apply Lemma9_14b; auto. apply Lemma9_14c; auto.
  exists ((a + b)/2). apply Classifier1. lra.
Qed.

(* 可积的第二充要条件 *)
Theorem Theorem9_15 : ∀ f a b, a < b -> DBoundedFun f (\[a, b\])
  -> (∃ J, Def_Integral f a b J)
    <-> (∀ δ, δ > 0 -> ∃ T n, Seg T a b (S n)
      /\ (Up_sum f T n) - (Low_sum f T n) < δ).
Proof.
  split; intros.
  - pose proof (Property9_6_6a f a b H H0).
    pose proof (Property9_6_6b f a b H H0).
    pose proof (ST_Fun_is_Function f a b H) as [].
    pose proof (sT_Fun_is_Function f a b H) as [].
    pose proof H1. apply Theorem9_14 in H9; auto.
    assert (limit_pos ((ST_Fun f a b) \- (sT_Fun f a b)) 0
      ((Up_Integral f a b) - (Low_Integral f a b))). { apply Lemma6_10e; auto. }
    rewrite H9,Rminus_diag in H10. destruct H10 as [H10[δ1[H11[]]]].
    pose proof (H13 δ H2) as [δ0[]]. rewrite Rplus_0_l in H15.
    assert (0 < δ0/2 < δ0). lra.
    assert (0 < δ0/2 <= b - a).
    { rewrite Corollary_sub_fun_c,H6,H8 in H12.
      assert (δ0/2 ∈ U+º(0; δ1)). { apply Classifier1; split; lra. }
      apply H12 in H17. applyClassifier1 H17. destruct H17. applyClassifier1 H17; auto. }
    pose proof (H15 (δ0/2) H16). rewrite Rminus_0_r,Corollary_sub_fun_b in H18;
    [ |rewrite H6|rewrite H8]; try (apply Classifier1; lra).
    pose proof (ST_Fun_Value f a b (δ0/2) H H17) as [T1[m1[H19[]]]].
    pose proof (sT_Fun_Value f a b (δ0/2) H H17) as [T2[m2[H22[]]]].
    pose proof (Property9_6_3 f T1 T2 a b m1 m2 H0 H19 H22) as [k[H25[H26[H27[]]]]].
    exists (Merge_seg T1 T2),k. split; auto. rewrite H21,H24 in H18.
    pose proof (Property9_6_4 f T2 T1 a b m2 m1 H0 H22 H19).
    rewrite Abs_ge in H18; lra.
  - apply Theorem9_14; auto.
    assert (∀ δ, δ > 0 -> 0 <= (Up_Integral f a b) - (Low_Integral f a b) < δ).
    { intros. apply H1 in H2 as [T[n[]]].
      pose proof (Up_Integral_Corollary f a b H H0) as [H4 _].
      assert ((Up_sum f T n) >= (Up_Integral f a b)). { apply H4,Classifier1; eauto. }
      pose proof (Low_Integral_Corollary f a b H H0) as [H6 _].
      assert ((Low_sum f T n) <= (Low_Integral f a b)). { apply H6,Classifier1; eauto. }
      pose proof (Property9_6_5a f a b H H0). lra. }
    destruct (Rtotal_order 0 ((Up_Integral f a b) - (Low_Integral f a b)))
    as [H3|[]]. apply H2 in H3. exfalso. lra. lra. pose proof Rlt_0_1.
    apply H2 in H4. exfalso. lra.
Qed.

Section theorem9_16.

(* 振幅大于ε的小区间的总长 *)
Let f1a ε f T := \{\ λ u v,
  ((sup_fD f (\[T[u], T[S u]\])) - (inf_fD f (\[T[u], T[S u]\])) >= ε
    -> v = T[S u] - T[u])
  /\ ((sup_fD f (\[T[u], T[S u]\])) - (inf_fD f (\[T[u], T[S u]\])) < ε
    -> v = 0) \}\.

Fact f1a_Fact1 : ∀ f T ε n,
  (sup_fD f (\[T[n], T[S n]\])) - (inf_fD f (\[T[n], T[S n]\])) >= ε
  -> (f1a ε f T)[n] = T[S n] - T[n].
Proof.
  intros. assert (n ∈ dom[(f1a ε f T)]).
  { apply Classifier1. exists (T[S n] - T[n]). apply Classifier2; split; auto.
    intros. exfalso. lra. }
  apply x_fx_T in H0. applyClassifier2 H0. destruct H0; auto.
  red; intros. applyClassifier2 H1. applyClassifier2 H2. destruct H1,H2.
  destruct (Rge_lt ((sup_fD f (\[T[x], T[S x]\])) 
    - (inf_fD f (\[T[x], T[S x]\]))) ε).
  rewrite H1,H2; auto. rewrite H3,H4; auto.
Qed.

Fact f1a_Fact2 : ∀ f T ε n,
  (sup_fD f (\[T[n], T[S n]\])) - (inf_fD f (\[T[n], T[S n]\])) < ε
  -> (f1a ε f T)[n] = 0.
Proof.
  intros. assert (n ∈ dom[(f1a ε f T)]).
  { apply Classifier1. exists 0. apply Classifier2; split; auto.
    intros. exfalso. lra. }
  apply x_fx_T in H0. applyClassifier2 H0. destruct H0; auto.
  red; intros. applyClassifier2 H1. applyClassifier2 H2. destruct H1,H2.
  destruct (Rge_lt ((sup_fD f (\[T[x], T[S x]\])) 
    - (inf_fD f (\[T[x], T[S x]\]))) ε).
  rewrite H1,H2; auto. rewrite H3,H4; auto.
Qed.

Let sum1 ε f T n := Σ (f1a ε f T) n.

Let f1b ε f T := \{\ λ u v,
  ((sup_fD f (\[T[u], T[S u]\])) - (inf_fD f (\[T[u], T[S u]\])) >= ε
    -> v = ε * (T[S u] - T[u]))
  /\ ((sup_fD f (\[T[u], T[S u]\])) - (inf_fD f (\[T[u], T[S u]\])) < ε
    -> v = 0) \}\.

Fact f1b_Fact1 : ∀ f T ε n,
  (sup_fD f (\[T[n], T[S n]\])) - (inf_fD f (\[T[n], T[S n]\])) >= ε
  -> (f1b ε f T)[n] = ε * (T[S n] - T[n]).
Proof.
  intros. assert (n ∈ dom[(f1b ε f T)]).
  { apply Classifier1. exists (ε * (T[S n] - T[n])). apply Classifier2; split; auto.
    intros. exfalso. lra. }
  apply x_fx_T in H0. applyClassifier2 H0. destruct H0; auto.
  red; intros. applyClassifier2 H1. applyClassifier2 H2. destruct H1,H2.
  destruct (Rge_lt ((sup_fD f (\[T[x], T[S x]\]))
    - (inf_fD f (\[T[x], T[S x]\]))) ε).
  rewrite H1,H2; auto. rewrite H3,H4; auto.
Qed.

Fact f1b_Fact2 : ∀ f T ε n,
  (sup_fD f (\[T[n], T[S n]\])) - (inf_fD f (\[T[n], T[S n]\])) < ε
  -> (f1b ε f T)[n] = 0.
Proof.
  intros. assert (n ∈ dom[(f1b ε f T)]).
  { apply Classifier1. exists 0. apply Classifier2; split; auto.
    intros. exfalso. lra. }
  apply x_fx_T in H0. applyClassifier2 H0. destruct H0; auto.
  red; intros. applyClassifier2 H1. applyClassifier2 H2. destruct H1,H2.
  destruct (Rge_lt ((sup_fD f (\[T[x], T[S x]\])) 
    - (inf_fD f (\[T[x], T[S x]\]))) ε).
  rewrite H1,H2; auto. rewrite H3,H4; auto.
Qed.

Fact sum1_Fact : ∀ f T n ε, ε * (sum1 ε f T n) = Σ (f1b ε f T) n.
Proof.
  intros. induction n. unfold sum1. simpl.
  destruct (Rge_lt ((sup_fD f (\[T[0%nat], T[S 0]\]))
    - (inf_fD f (\[T[0%nat], T[S 0]\]))) ε).
  rewrite f1a_Fact1,f1b_Fact1; auto. rewrite f1a_Fact2,f1b_Fact2; auto.
  rewrite Rmult_0_r; auto. unfold sum1. simpl. rewrite Rmult_plus_distr_l.
  unfold sum1 in IHn. rewrite IHn.
  destruct (Rge_lt ((sup_fD f (\[T[S n], T[S (S n)]\]))
    - (inf_fD f (\[T[S n], T[S (S n)]\]))) ε).
  rewrite f1a_Fact1,f1b_Fact1; auto. rewrite f1a_Fact2,f1b_Fact2; auto.
  rewrite Rmult_0_r; auto.
Qed.

(* 振幅大于ε的小区间的 振幅乘小区间长度 的总和 *)
Let f2 ε f T := \{\ λ u v,
  ((sup_fD f (\[T[u], T[S u]\])) - (inf_fD f (\[T[u], T[S u]\])) >= ε
    -> v = (((sup_fD f (\[T[u], T[S u]\])) - (inf_fD f (\[T[u], T[S u]\])))
           * (T[S u] - T[u])))
  /\ ((sup_fD f (\[T[u], T[S u]\])) - (inf_fD f (\[T[u], T[S u]\])) < ε
    -> v = 0) \}\.

Fact f2_Fact1 : ∀ f T ε n,
  (sup_fD f (\[T[n], T[S n]\])) - (inf_fD f (\[T[n], T[S n]\])) >= ε
  -> (f2 ε f T)[n]
    = ((sup_fD f (\[T[n], T[S n]\])) - (inf_fD f (\[T[n], T[S n]\])))
      * (T[S n] - T[n]).
Proof.
  intros. assert (n ∈ dom[(f2 ε f T)]).
  { apply Classifier1.
    exists (((sup_fD f (\[T[n], T[S n]\])) - (inf_fD f (\[T[n], T[S n]\])))
    * (T[S n] - T[n])). apply Classifier2; split; auto. intros. exfalso. lra. }
  apply x_fx_T in H0. applyClassifier2 H0. destruct H0; auto.
  red; intros. applyClassifier2 H1. applyClassifier2 H2. destruct H1,H2.
  destruct (Rge_lt ((sup_fD f (\[T[x], T[S x]\])) 
    - (inf_fD f (\[T[x], T[S x]\]))) ε).
  rewrite H1,H2; auto. rewrite H3,H4; auto.
Qed.

Fact f2_Fact2 : ∀ f T ε n,
  (sup_fD f (\[T[n], T[S n]\])) - (inf_fD f (\[T[n], T[S n]\])) < ε
  -> (f2 ε f T)[n] = 0.
Proof.
  intros. assert (n ∈ dom[(f2 ε f T)]).
  { apply Classifier1. exists 0. apply Classifier2; split; auto.
    intros. exfalso. lra. }
  apply x_fx_T in H0. applyClassifier2 H0. destruct H0; auto.
  red; intros. applyClassifier2 H1. applyClassifier2 H2. destruct H1,H2.
  destruct (Rge_lt ((sup_fD f (\[T[x], T[S x]\])) 
    - (inf_fD f (\[T[x], T[S x]\]))) ε).
  rewrite H1,H2; auto. rewrite H3,H4; auto.
Qed.

Let sum2 ε f T n := Σ (f2 ε f T) n.

Fact sum1_leq_sum2 : ∀ f T a b n ε, Seg T a b (S n)
  -> ε * (sum1 ε f T n) <= (sum2 ε f T n).
Proof.
  intros. rewrite sum1_Fact. apply Rge_le,Σ_Fact3. intros.
  destruct (Rge_lt ((sup_fD f (\[T[i], T[S i]\]))
    - (inf_fD f (\[T[i], T[S i]\]))) ε).
  rewrite f1b_Fact1,f2_Fact1; auto. apply Rmult_ge_compat_r; auto.
  destruct H as [H[H2[H3[]]]]. assert (i < S n)%nat. lia.
  apply H4 in H6. lra. rewrite f1b_Fact2,f2_Fact2; auto. lra.
Qed.

Fact sum2_leq_sum1 : ∀ f T a b n ε, Seg T a b (S n)
  -> DBoundedFun f (\[a, b\]) -> (sum2 ε f T n)
    <= ((sup_fD f (\[a, b\])) - (inf_fD f (\[a, b\]))) * (sum1 ε f T n).
Proof.
  intros.
  assert ((sup_fD f (\[a, b\]) - inf_fD f (\[a, b\])) * (sum1 ε f T n)
    = Σ \{\ λ u v, v = (sup_fD f (\[a, b\]) - inf_fD f (\[a, b\]))
      * (f1a ε f T)[u] \}\ n).
  { clear H H0. induction n. unfold sum1. simpl. rewrite FunValue; auto.
    replace (sum1 ε f T (S n)) with ((sum1 ε f T n) + (f1a ε f T)[S n]); auto.
    simpl. rewrite FunValue,Rmult_plus_distr_l,IHn; auto. }
  rewrite H1. apply Rge_le,Σ_Fact3. intros. rewrite FunValue.
  destruct (Rge_lt ((sup_fD f (\[T[i], T[S i]\]))
    - (inf_fD f (\[T[i], T[S i]\]))) ε).
  rewrite f2_Fact1,f1a_Fact1; auto. apply Rmult_ge_compat_r.
  destruct H as [H[H4[H5[H6[]]]]].
  assert (i < S n)%nat. lia. apply H6 in H9. lra.
  assert (\[T[i], T[S i]\] ⊂ \[a, b\] /\ NotEmpty (\[T[i], T[S i]\])) as [].
  { pose proof H. destruct H4 as [H4[H5[H6[H7[]]]]]. rewrite <-H8,<-H9.
    assert (T[0%nat] <= T[i] /\ T[i] <= T[S i] /\ T[S i] <= T[S n]) as [H10[]].
    { repeat split; apply (Seg_Increase_a T a b (S n)); auto; lia. }
    split. red; intros. applyClassifier1 H13. apply Classifier1. lra.
    exists ((T[i] + T[S i])/2). apply Classifier1; lra. }
  assert ((sup_fD f (\[T[i], T[S i]\])) <= (sup_fD f (\[a, b\]))
    /\ (inf_fD f (\[a, b\]) <= (inf_fD f (\[T[i], T[S i]\])))) as [].
  { split; [apply sup_Coro_2|apply inf_Coro_2]; auto. } lra.
  rewrite f1a_Fact2,f2_Fact2; auto. lra.
Qed.

(* 所有 振幅乘小区间长度 的总和 *)
Let f3 f T := \{\ λ u v,
  v = ((sup_fD f (\[T[u], T[S u]\])) - (inf_fD f (\[T[u], T[S u]\])))
      * (T[S u] - T[u]) \}\.

Let sum3 f T n := Σ (f3 f T) n.

Fact sum2_leq_sum3 : ∀ f T a b n ε, DBoundedFun f (\[a, b\]) -> Seg T a b (S n)
  -> (sum2 ε f T n) <= (sum3 f T n).
Proof.
  intros. apply Rge_le,Σ_Fact3. intros. unfold f3. rewrite FunValue.
  destruct (Rge_lt ((sup_fD f (\[T[i], T[S i]\]))
    - (inf_fD f (\[T[i], T[S i]\]))) ε).
  rewrite f2_Fact1; auto. lra. rewrite f2_Fact2; auto. apply Rmult_gre_gr.
  split. assert (DBoundedFun f (\[T[i], T[S i]\])). destruct H as [H[H3[]]].
  split; auto. assert ((\[T[i], T[S i]\]) ⊂ (\[a, b\])).
  { red; intros. pose proof H0. destruct H6 as [H6[H7[H8[H9[]]]]].
    applyClassifier1 H5. destruct H5. apply Classifier1. rewrite <-H10,<-H11.
    assert (T[0%nat] <= T[i] /\ T[S i] <= T[S n]) as [].
    { split; apply (Seg_Increase_a T a b (S n)); auto; lia. } lra. }
  split. red; intros; auto. exists x. intros. apply H4; auto.
  apply sup_inf_Coro_2 in H3. lra. assert (T[i] < T[S i]).
  { apply (Seg_StrictlyIncrease_a T a b (S n)); auto. lia. }
  exists ((T[i] + T[S i])/2). apply Classifier1. lra.
  destruct H0 as [H0[H3[H4[]]]].
  assert (i < S n)%nat. lia. apply H5 in H7; lra.
Qed.

Fact sum3_Fact : ∀ f T a b n, DBoundedFun f (\[a, b\]) -> Seg T a b (S n)
  -> (sum3 f T n) = (Up_sum f T n) - (Low_sum f T n).
Proof.
  intros. generalize dependent T. generalize dependent a.
  generalize dependent b. induction n; intros.
  unfold sum3,Up_sum,Low_sum. simpl. unfold f3.
  rewrite FunValue,FunValue,FunValue. lra. unfold sum3,Up_sum,Low_sum.
  simpl. pattern f3 at 2. unfold f3 at 2. rewrite FunValue,FunValue,FunValue.
  set (T1 := T — [[S (S n), T[S (S n)]]]).
  assert (Function T1).
  { destruct H0 as [H0[H1[H2[H3[]]]]]. red; intros.
    applyClassifier1 H6. applyClassifier1 H7. destruct H6,H7. apply (H0 x); auto. }
  assert (dom[T1] = \{ λ u, (u <= S n)%nat \}).
  { apply AxiomI; split; intros. applyClassifier1 H2. destruct H2.
    applyClassifier1 H2. destruct H2. assert (z ∈ dom[T]). { apply Classifier1; eauto. }
    destruct H0 as [H0[H5[H6[]]]]. rewrite H6 in H4. applyClassifier1 H4.
    assert (z <> S (S n)).
    { intro. applyClassifier1 H3. elim H3. apply Classifier1.
      apply f_x_T in H2; auto. rewrite <-H9,H2; auto. }
    apply Classifier1. lia. destruct H0 as [H0[H3[H4[]]]].
    assert (z ∈ dom[T]). { rewrite H4. applyClassifier1 H2. apply Classifier1. lia. }
    applyClassifier1 H7. destruct H7. apply Classifier1. exists x. apply Classifier1.
    split; auto. apply Classifier1. intro. applyClassifier1 H8.
    apply ProdEqual in H8 as []. rewrite H8 in H2. applyClassifier1 H2. lia. }
  assert (∀ i, (i <= S n)%nat -> T1[i] = T[i]).
  { intros. destruct H0 as [H0[H4[H5[H6[]]]]].
    assert (i ∈ dom[T] /\ i ∈ dom[T1]) as [].
    { rewrite H5,H2. split; apply Classifier1; lia. }
    apply x_fx_T in H9,H10; auto. applyClassifier1 H10. destruct H10.
    apply (H0 i); auto. }
  assert (Seg T1 a (T[S n]) (S n)).
  { destruct H0 as [H0[H4[H5[H6[]]]]]. split; auto. split. lia.
    split; auto. rewrite H3,H3; try lia. split; auto. intros.
    rewrite H3,H3; auto. lia. }
  assert (DBoundedFun f (\[a, T[S n]\])).
  { destruct H as [H[H5[]]]. split; auto.
    assert (\[a, T[S n]\] ⊂ \[a, b\]).
    { red; intros. applyClassifier1 H7. apply Classifier1.
      assert (T[S n] <= b).
      { destruct H0 as [H0[H8[H9[H10[]]]]]. rewrite <-H12; auto.
        assert (S n < S (S n))%nat. lia. apply H10 in H13. lra. } lra. }
    split. red; intros; auto. exists x. intros; auto. }
  pose proof (IHn T[S n] a H5 T1 H4).
  assert (Σ (f3 f T) n = sum3 f T1 n).
  { unfold sum3. apply Σ_Fact5. intros. unfold f3.
    rewrite FunValue,FunValue,H3,H3; auto. lia. }
  assert (Σ \{\ λ i s, s = (sup_fD f (\[T[i], T[S i] \])) * (T[S i] - T[i]) \}\ n
    = Up_sum f T1 n).
  { unfold Up_sum. apply Σ_Fact5. intros.
    rewrite FunValue,FunValue,H3,H3; auto. lia. }
  assert (Σ \{\ λ i s, s = (inf_fD f (\[T[i], T[S i] \])) * (T[S i] - T[i]) \}\ n
    = Low_sum f T1 n).
  { unfold Up_sum. apply Σ_Fact5. intros.
    rewrite FunValue,FunValue,H3,H3; auto. lia. }
  rewrite H7,H8,H9. lra.
Qed.

(* 振幅小于ε的小区间的总长 *)
Let f4 ε f T := \{\ λ u v,
  ((sup_fD f (\[T[u], T[S u]\])) - (inf_fD f (\[T[u], T[S u]\])) >= ε
    -> v = 0)
  /\ ((sup_fD f (\[T[u], T[S u]\])) - (inf_fD f (\[T[u], T[S u]\])) < ε
    -> v = T[S u] - T[u]) \}\.

Fact f4_Fact1 : ∀ f T ε n,
  (sup_fD f (\[T[n], T[S n]\])) - (inf_fD f (\[T[n], T[S n]\])) >= ε
  -> (f4 ε f T)[n] = 0.
Proof.
  intros. assert (n ∈ dom[(f4 ε f T)]).
  { apply Classifier1. exists 0. apply Classifier2; split; auto.
    intros. exfalso. lra. }
  apply x_fx_T in H0. applyClassifier2 H0. destruct H0; auto.
  red; intros. applyClassifier2 H1. applyClassifier2 H2. destruct H1,H2.
  destruct (Rge_lt ((sup_fD f (\[T[x], T[S x]\])) 
    - (inf_fD f (\[T[x], T[S x]\]))) ε).
  rewrite H1,H2; auto. rewrite H3,H4; auto.
Qed.

Fact f4_Fact2 : ∀ f T ε n,
  (sup_fD f (\[T[n], T[S n]\])) - (inf_fD f (\[T[n], T[S n]\])) < ε
  -> (f4 ε f T)[n] = T[S n] - T[n].
Proof.
  intros. assert (n ∈ dom[(f4 ε f T)]).
  { apply Classifier1. exists (T[S n] - T[n]). apply Classifier2; split; auto.
    intros. exfalso. lra. }
  apply x_fx_T in H0. applyClassifier2 H0. destruct H0; auto.
  red; intros. applyClassifier2 H1. applyClassifier2 H2. destruct H1,H2.
  destruct (Rge_lt ((sup_fD f (\[T[x], T[S x]\])) 
    - (inf_fD f (\[T[x], T[S x]\]))) ε).
  rewrite H1,H2; auto. rewrite H3,H4; auto.
Qed.

Let sum4 ε f T n := Σ (f4 ε f T) n.

Fact sum4_Fact ε f T a b n : Seg T a b (S n) -> (sum4 ε f T n) <= b - a.
Proof.
  intros. assert (b - a = Σ \{\ λ u v, v = (T[S u] - T[u]) \}\ n).
  { rewrite (Lemma9_6_1c T n a b); auto. }
  rewrite H0. apply Rge_le,Σ_Fact3. intros. rewrite FunValue.
  destruct (Rge_lt ((sup_fD f (\[T[i], T[S i]\]))
    - (inf_fD f (\[T[i], T[S i]\]))) ε).
  rewrite f4_Fact1; auto. assert (T[i] <= T[S i]).
  { apply (Seg_Increase_a T a b (S n)); auto; lia. } lra.
  rewrite f4_Fact2; auto. lra.
Qed.

(* 振幅小于ε的小区间的 振幅乘小区间长度 的总和 *)
Let f5 ε f T := \{\ λ u v,
  ((sup_fD f (\[T[u], T[S u]\])) - (inf_fD f (\[T[u], T[S u]\])) >= ε
    -> v = 0)
  /\ ((sup_fD f (\[T[u], T[S u]\])) - (inf_fD f (\[T[u], T[S u]\])) < ε
    -> v = (((sup_fD f (\[T[u], T[S u]\])) - (inf_fD f (\[T[u], T[S u]\])))
           * (T[S u] - T[u]))) \}\.

Fact f5_Fact1 : ∀ f T ε n,
  (sup_fD f (\[T[n], T[S n]\])) - (inf_fD f (\[T[n], T[S n]\])) >= ε
  -> (f5 ε f T)[n] = 0.
Proof.
  intros. assert (n ∈ dom[(f5 ε f T)]).
  { apply Classifier1. exists 0. apply Classifier2; split; auto. intros. exfalso. lra. }
  apply x_fx_T in H0. applyClassifier2 H0. destruct H0; auto.
  red; intros. applyClassifier2 H1. applyClassifier2 H2. destruct H1,H2.
  destruct (Rge_lt ((sup_fD f (\[T[x], T[S x]\])) 
    - (inf_fD f (\[T[x], T[S x]\]))) ε).
  rewrite H1,H2; auto. rewrite H3,H4; auto.
Qed.

Fact f5_Fact2 : ∀ f T ε n,
  (sup_fD f (\[T[n], T[S n]\])) - (inf_fD f (\[T[n], T[S n]\])) < ε
  -> (f5 ε f T)[n]
     = ((sup_fD f (\[T[n], T[S n]\])) - (inf_fD f (\[T[n], T[S n]\])))
     * (T[S n] - T[n]).
Proof.
  intros. assert (n ∈ dom[(f5 ε f T)]).
  { apply Classifier1.
    exists (((sup_fD f (\[T[n], T[S n]\])) - (inf_fD f (\[T[n], T[S n]\])))
      * (T[S n] - T[n])). apply Classifier2; split; auto. intros. exfalso. lra. }
  apply x_fx_T in H0. applyClassifier2 H0. destruct H0; auto.
  red; intros. applyClassifier2 H1. applyClassifier2 H2. destruct H1,H2.
  destruct (Rge_lt ((sup_fD f (\[T[x], T[S x]\])) 
    - (inf_fD f (\[T[x], T[S x]\]))) ε).
  rewrite H1,H2; auto. rewrite H3,H4; auto.
Qed.

Let sum5 ε f T n := Σ (f5 ε f T) n.

Fact sum3_eq_sum2_plus_sum5 : ∀ ε f T n, (sum3 f T n)
  = (sum2 ε f T n) + (sum5 ε f T n).
Proof.
  intros. generalize dependent T. generalize dependent ε. induction n; intros.
  unfold sum3,sum2,sum5; simpl. unfold f3. rewrite FunValue.
  destruct (Rge_lt ((sup_fD f (\[T[0%nat], T[S 0]\]))
    - (inf_fD f (\[T[0%nat], T[S 0]\]))) ε).
  rewrite f2_Fact1,f5_Fact1; auto. lra. rewrite f2_Fact2,f5_Fact2; auto. lra.
  replace (sum3 f T (S n)) with ((sum3 f T n) + (f3 f T)[S n]); auto.
  replace (sum2 ε f T (S n)) with ((sum2 ε f T n) + (f2 ε f T)[S n]); auto.
  replace (sum5 ε f T (S n)) with ((sum5 ε f T n) + (f5 ε f T)[S n]); auto.
  unfold f3. rewrite FunValue.
  destruct (Rge_lt ((sup_fD f (\[T[S n], T[S (S n)]\]))
    - (inf_fD f (\[T[S n], T[S (S n)]\]))) ε).
  rewrite f2_Fact1,f5_Fact1,(IHn ε); auto. lra.
  rewrite f2_Fact2,f5_Fact2,(IHn ε); auto. lra.
Qed.

Fact sum5_leq_sum4 : ∀ ε f T a b n, Seg T a b (S n)
  -> (sum5 ε f T n) <= ε * (sum4 ε f T n).
Proof.
  intros. assert (ε * (sum4 ε f T n) = Σ \{\ λ u v, v = ε * (f4 ε f T)[u] \}\ n).
  { clear H. induction n. unfold sum4; simpl. rewrite FunValue. auto.
    replace (sum4 ε f T (S n)) with ((sum4 ε f T n) + (f4 ε f T)[S n]); auto.
    simpl. rewrite FunValue,Rmult_plus_distr_l,IHn; auto. }
  rewrite H0. apply Rge_le,Σ_Fact3. intros. rewrite FunValue.
  destruct (Rge_lt ((sup_fD f (\[T[i], T[S i]\]))
    - (inf_fD f (\[T[i], T[S i]\]))) ε).
  rewrite f4_Fact1,f5_Fact1; auto. lra. rewrite f4_Fact2,f5_Fact2; auto.
  apply Rmult_ge_compat_r. assert (T[i] <= T[S i]).
  { apply (Seg_Increase_a T a b (S n)); auto; lia. } lra. lra.
Qed.

(* 可积的第三充要条件 *)
Theorem Theorem9_16 : ∀ f a b, a < b -> DBoundedFun f (\[a, b\])
  -> (∃ J, Def_Integral f a b J)
    <-> (∀ ε η, ε > 0 -> η > 0 -> ∃ T n, Seg T a b (S n)
      /\ (sum1 ε f T n) < η).
Proof.
  intros. split; intros.
  - assert (ε * η > 0). { apply Rmult_gt_0_compat; auto. }
    pose proof H4. apply (Theorem9_15 f a b H H0) in H5 as [T[n[]]]; auto.
    pose proof (sum1_leq_sum2 f T a b n ε H5).
    pose proof (sum2_leq_sum3 f T a b n ε H0 H5). exists T,n. split; auto.
    assert (ε * (sum1 ε f T n) < ε * η).
    { rewrite (sum3_Fact f T a b n) in H8; auto. lra. }
    apply Rmult_gt_reg_l in H9; auto.
  - pose proof H0. apply sup_inf_Coro_2 in H2 as [].
    + apply Theorem9_15; auto. intros.
      set (ε := δ/(2*(b-a))).
      set (η := δ/(2 * ((sup_fD f (\[a, b\])) - (inf_fD f (\[a, b\]))))).
      assert (ε > 0 /\ η > 0) as [].
      { split; apply Rlt_gt,Rdiv_lt_0_compat; lra. }
      pose proof (H1 ε η H4 H5) as [T[n[]]]. exists T,n. split; auto.
      rewrite <-(sum3_Fact f T a b),(sum3_eq_sum2_plus_sum5 ε); auto.
      pose proof (sum2_leq_sum1 f T a b n ε H6 H0).
      pose proof (sum5_leq_sum4 ε f T a b n H6).
      pose proof (sum4_Fact ε f T a b n H6).
      apply (Rmult_le_compat_l ε) in H10; [ |lra].
      assert ((sum5 ε f T n) <= ε * (b - a)). lra.
      apply (Rmult_lt_compat_l ((sup_fD f (\[a, b\])) - (inf_fD f (\[a, b\]))))
      in H7; [ |lra].
      assert ((sum2 ε f T n)
        < ((sup_fD f (\[a, b\])) - (inf_fD f (\[a, b\]))) * η). lra.
      pattern ε at 2 in H11. unfold ε in H11 at 2. unfold Rdiv in H11.
      rewrite Rmult_assoc,Rinv_mult,Rmult_assoc,Rinv_l,Rmult_1_r in H11;
      try lra. unfold η in H12. unfold Rdiv in H12.
      rewrite Rmult_comm,Rmult_assoc,Rinv_mult,Rmult_assoc,
      Rinv_l,Rmult_1_r in H12; lra.
    + pose proof (sup_inf_Coro_3 f (\[a, b\]) H0 H2).
      exists ((b - a) * (inf_fD f (\[a, b\]))). destruct H0 as [H0[H4[y]]].
      split; auto. split; auto. split; auto. intros. exists 1. split. lra.
      intros. rewrite <-(Lemma9_6_1c T n a b); auto.
      assert ((Σ \{\ λ i m, m = T[S i] - T[i] \}\ n) * (inf_fD f (\[a, b\]))
        = Σ \{\ λ i m, m = (inf_fD f (\[a, b\])) * (T[S i] - T[i]) \}\ n).
      { clear H3 H6 H7 H8 H9. induction n. simpl. rewrite FunValue,FunValue.
        lra. simpl. rewrite FunValue,FunValue,Rmult_plus_distr_r,IHn. lra. }
      assert (IntegralSum f T n ξ
        = (Σ \{\ λ i m, m = T[S i] - T[i] \}\ n) * (inf_fD f (\[a, b\]))).
      { rewrite H10. apply Σ_Fact5. intros. rewrite FunValue,FunValue,H3; auto.
        pose proof H7. destruct H12 as [H12[H13[H14[H15[]]]]].
        rewrite <-H16,<-H17. apply Classifier1. pose proof H11. apply H8 in H18.
        assert (0 <= x /\ S x <= S n)%nat as []. lia.
        apply (Seg_Increase_a T a b (S n)) in H19,H20; auto; try lia. lra. }
      rewrite H11,Rminus_diag,Abs_ge; auto. lra.
    + exists ((a + b)/2). apply Classifier1. lra.
Qed.

End theorem9_16.



