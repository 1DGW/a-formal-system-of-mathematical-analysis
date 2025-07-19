(** A_01 *)
(* 逻辑与集合论基础 *)

(**************  基本逻辑(增加排中律, 古典逻辑)  **************)

(* 引入记号 *)
Notation "∀ x .. y , P" := (forall x, .. (forall y , P) ..)
  (at level 200, x binder, y binder, right associativity).

Notation "∃ x .. y , P" := (exists x, .. (exists y , P) ..)
  (at level 200, x binder, y binder, right associativity).

Notation "'λ' x .. y , t " := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity).

(* 排中律 *)
Axiom classic : ∀ P, P \/ ~P.

Theorem NNPP : ∀ P, ~~P <-> P.
Proof.
  split; intros; destruct (classic P); tauto.
Qed.

Theorem not_and_or : ∀ P Q,
  (~(P /\ Q) <-> (~P) \/ (~Q)) /\ (~(P \/ Q) <-> (~P) /\ (~Q)).
Proof.
  intros; destruct (classic P); tauto.
Qed.

Theorem not_all_ex_not : ∀ U (P : U -> Prop), ~ (∀ n, P n) -> (∃ n, ~ P n).
Proof.
  intros. apply NNPP; intro. elim H. intros. apply NNPP; intro. elim H0; eauto.
Qed.

Theorem not_ex_all_not : ∀ U (P : U -> Prop), ~ (∃ n, P n) -> (∀ n, ~ P n).
Proof.
  intros. intro. elim H; eauto.
Qed.

Theorem imply_to_or : ∀ P Q, (P -> Q) -> (~ P) \/ Q.
Proof. intros. destruct (classic (P)); auto. Qed.

Theorem imply_to_and : ∀ P Q, ~ (P -> Q) -> P /\ ~ Q.
Proof.
  intros. destruct (classic P). split; auto. elim H. intros. elim H0; auto.
Qed.


(********************  基于简单类型的集合初等概念  *********************)

(* 定义：集合 *)
Definition set {U : Type} := U -> Prop.

Definition ClassifierI {U : Type} (P : U -> Prop) := P.

Notation "\{ P \}" := (ClassifierI P) (at level 0).

(* 定义：属于 *)
Definition In {U : Type} (x : U) (A : set) := A x.
Notation "x ∈ A" :=(In x A) (at level 80).

Definition NotIn {U : Type} (x : U) (A : set) := ~ (x ∈ A).
Notation "x ∉ A" := (NotIn x A)(at level 80).

Fact Classifier1 : ∀ (A : Type) (b : A) (P : A -> Prop),
  b ∈ \{ P \} <-> P b.
Proof. split; intros; auto. Qed.

Ltac applyClassifier1 H := match type of H with
  | _ ∈ \{ _ \} => apply ->Classifier1 in H; simpl in H
  | _ ∈ _ => repeat red in H
  | _ => idtac
  end.


(* 公理I：外延公理 *)
Axiom AxiomI : ∀ {A :Type} (x y : set), x = y
  <-> (∀ z : A, z ∈ x <-> z ∈ y).

(* 定义：空集 *)
Definition Empty (A : Type) := \{ λ (x : A), x <> x \}.

(* 定义: 非空集 *)
Definition NotEmpty {A : Type} (S : set) := ∃ (x : A), x ∈ S.

(* 非空集性质 *)
Property not_empty : ∀ {X : Type} (A : set), A <> Empty X <-> NotEmpty A.
Proof.
  intros X A. unfold NotEmpty. split; intro H0.
  - apply NNPP; intro. apply H0. apply AxiomI; split; intros.
    + elim H; eauto.
    + exfalso. applyClassifier1 H1. apply H1; auto.
  - intro H1. destruct H0 as [x H2]. rewrite H1 in H2. applyClassifier1 H2.
    contradiction.
Qed.

(* 定义：全集 *)
Definition Full (A : Type) := \{ λ x : A, x = x \}.

(* 定义：单点集 *)
Definition Singleton {A: Type} (x : A) := \{ λ z, z = x \}.
Notation "[ x ]" := (Singleton x)(at level 0).

(* 定义：子集 *)
Definition Contain {A : Type} (x y : (@set A)) := ∀ z, z ∈ x -> z ∈ y.
Notation "x ⊂ y" := (Contain x y) (at level 70).

(* 定义：集合的运算 *)
Definition Union {A : Type} (x y : (@set A)) :=
  \{ λ z : A, z ∈ x \/ z ∈ y  \} .
Notation "x ∪ y" := (Union x y)(at level 65, right associativity).

Definition Intersection {A : Type} (x y : (@set A)) :=
  \{ λ z : A, z ∈ x /\ z ∈ y \}.
Notation "x ∩ y" := (Intersection x y)(at level 65, right associativity).

Definition Complement {A : Type} (x : (@set A)) := \{ λ y : A, y ∉ x \}.
Notation "¬ x" := (Complement x) (at level 5, right associativity).

Definition Difference {A : Type} (x y : (@set A)) := x ∩ (¬ y).
Notation "x — y" := (Difference x y)(at level 5).

(* 定义：有序偶 *)
Inductive prod {X Y : Type} : Type := | pair (x : X) (y : Y).
Notation "[ x , y ]" := (pair x y)(at level 0).

Definition fst {X Y : Type} (p : (@prod X Y)) := match p with [x , y] => x end.

Definition snd {X Y : Type} (p : (@prod X Y)) := match p with [x , y] => y end.

Property ProdEqual : ∀ {X Y : Type} (x u : X) (y v : Y), [x , y] = [u, v] 
  -> x = u /\ y = v.
Proof.
  intros X Y x u y v H0. assert (H1 : fst [x, y] = x). auto.
  assert (H2 : snd [x, y] = y). auto. assert (H3 : fst [u, v] = u). auto.
  assert (H4 : snd [u, v] = v). auto. split.
  - rewrite H0 in H1. rewrite H1 in H3. auto .
  - rewrite H0 in H2. rewrite H2 in H4. auto.
Qed.

(* 引入符号((x, y) : ...) *)
Definition ClassifierII {X Y : Type} (P : X -> Y -> Prop) :=
  \{ λ u , ∃ x y, u = [x , y] /\ P x y \}.
Notation "\{\ P \}\ " := (ClassifierII P) (at level 0).

Fact Classifier2 : ∀ (X Y : Type) (x : X) (y : Y) (P : X -> Y -> Prop),
  [x, y] ∈ \{\ P \}\ <-> P x y.
Proof.
  intros X Y x y P. split;intros.
  - applyClassifier1 H. destruct H as [u [v [H H0]]].
    apply ProdEqual in H. destruct H. rewrite H,H1. auto.
  - apply Classifier1. exists x, y. split;auto.
Qed.

(* Ltac applyClassifier2 H := apply ->Classifier2 in H; simpl in H. *)

Ltac applyClassifier2 H := apply ->Classifier2 in H; simpl in H.

Definition Cartesian {X Y : Type} (x : (@set X)) (y : (@set Y)) :=
  \{\ λ u v, u ∈ x /\ v ∈ y \}\.
Notation "x × y" := (Cartesian x y)(at level 2, right associativity).


Parameter c : ∀ {U : Type}, @set U -> U.
Axiom Axiomc : ∀ {U : Type} (x : @set U), NotEmpty x -> (c x) ∈ x.

Fact ChooseSingleton : ∀ {U : Type} (x : U), c [x] = x.
Proof.
  intros U x. assert (H0 : c [x] ∈ [x]); auto.
  { apply Axiomc. exists x. apply Classifier1; auto. }
Qed.


(****************** 函数概念 *****************)

(* 定义：函数  *)
Definition Function {A B : Type} (f : (@set (@prod A B)))
  := ∀ x y z, [x, y] ∈ f -> [x, z] ∈ f -> y = z.

(* 定义：定义域 *)
Definition Domain {X Y : Type} (f : (@set (@prod X Y))) :=
  \{ λ x, ∃ y, [x, y] ∈ f \}.
Notation "dom[ f ]" := (Domain f) (at level 5).

(* 定义：值域 *)
Definition Range {X Y : Type} (f : (@set (@prod X Y))) :=
  \{ λ y, ∃ x, [x, y] ∈ f \}.
Notation "ran[ f ]" := (Range f) (at level 5).

(* 定义：值 *)
Definition Value {X Y : Type} (f : (@set (@prod X Y))) (x : X) :=
  c \{ λ y, [x, y] ∈ f \}.
Notation "f [ x ]" := (Value f x) (at level 5).

Property f_x_T : ∀ {X Y : Type} (f : @set (@prod X Y)) (x : X)(y : Y),
  Function f -> [x, y] ∈ f -> f[x] = y.
Proof.
  intros X Y f x y H1 H2. unfold Value.
  assert (H3 : \{ λ y0 : Y, [x, y0] ∈ f \} = [y]). 
  { apply AxiomI. intro z. split; intro H3.
    + apply -> Classifier1 in H3. simpl in H3. apply Classifier1.
      apply H1 with (x := x); auto.
    + apply Classifier1. apply -> Classifier1 in H3. simpl in H3. rewrite H3. auto. }
  rewrite H3. apply ChooseSingleton.
Qed.

Property x_fx_T : ∀ {X Y : Type} (f : (@set (@prod X Y))) (x : X),
  Function f -> x ∈ dom[f] -> [x, f[x]] ∈ f.
Proof.
  intros X Y f x H0 H1. apply -> Classifier1 in H1; simpl in H1. 
  destruct H1 as [y H1]. apply f_x_T in H1 as H2; auto.
  rewrite H2; auto.
Qed.

Property fx_ran_T : ∀ {X Y : Type} (f : (@set (@prod X Y))) (x : X),
  Function f -> x ∈ dom[f] -> f[x] ∈ ran[f].
Proof.
  intros. applyClassifier1 H0. destruct H0 as [y H0].
  eapply f_x_T in H0 as H2; eauto. rewrite H2. apply <- Classifier1. eauto.
Qed.

Property FunValue : ∀ {X Y : Type} (f : X -> Y) (x : X),
  \{\ λ x y, y = f x \}\[x] = f x.
Proof.
  intros X Y f x. assert (Function \{\ λ x y, y = f x \}\).
  { red; intros. applyClassifier2 H. applyClassifier2 H0. subst; auto. }
  apply f_x_T; auto. apply Classifier2; auto.
Qed.

(* 定义：复合 *)
Definition Composition {X Y Z : Type} (f : (@set (@prod Y Z))) (g : (@set (@prod X Y)))
  := \{\ λ x y, (∃ z, [x, z] ∈ g /\ [z, y] ∈ f) \}\.
Notation "f ◦ g" := (Composition f g) (at level 50, no associativity).

(* 定义：逆 *)
Definition Inverse {X Y : Type} (f : (@set (@prod X Y))) :=
  \{\ λ x y, [y, x] ∈ f \}\.
Notation "f ﹣¹" := (Inverse f) (at level 5).

(* 定义:1_1函数 *)
Definition Function1_1 {X Y : Type} (f : (@set (@prod X Y))) :=
  Function f /\ Function (f﹣¹).

(* 反函数的定义 *)
Definition Inverse_Function {X Y : Type} (f : (@set (@prod X Y))) g :=
  Function1_1 f /\ g = f﹣¹.

Property Inverse_P1 : ∀ {X Y : Type} (f : @set (@prod X Y)), dom[f﹣¹] = ran[f]
  /\ ran[f﹣¹] = dom[f].
Proof.
   intros. split.
   - apply AxiomI. split; intros. 
      + apply Classifier1. applyClassifier1 H. destruct H as [y].
        applyClassifier2 H. exists y; auto.
      + apply Classifier1. applyClassifier1 H. destruct H as [y].
        exists y.  apply Classifier2. auto.
   - apply AxiomI. split; intros. 
      + apply Classifier1. applyClassifier1 H. destruct H as [y].
        applyClassifier2 H. exists y; auto.
      + apply Classifier1. applyClassifier1 H. destruct H as [y].
        exists y.  apply Classifier2. auto.
Qed.

Property Inverse_P2 : ∀ {X Y : Type} (f : @set (@prod X Y)) g x,
  Inverse_Function f g -> x ∈ dom[f] -> g[f[x]] = x.
Proof.
  intros. red in H. destruct H as [[H H'] H'']. rewrite H''.
  apply f_x_T; auto. apply Classifier2. apply x_fx_T; auto.
Qed.

Property Inverse_P3 : ∀ {X Y : Type} (f : @set (@prod X Y)) g y,
  Inverse_Function f g -> y ∈ dom[g] -> f[g[y]] = y.
Proof. 
  intros. pose proof H as H'. red in H. destruct H as [[H H''] H''']. 
  rewrite H'''. rewrite H''' in H0. apply f_x_T; auto. 
  assert((f﹣¹)[y] ∈ ran[f﹣¹]). { apply fx_ran_T; auto.  }
  assert (∃ x, x = (f﹣¹)[y]). { exists (f﹣¹)[y]. auto. }
  destruct H2 as [x H2]. rewrite <-H2. rewrite <-H2 in H1.
  pose proof Inverse_P1 f. destruct H3. rewrite H4 in H1.
  pose proof H' as I1. apply (Inverse_P2 f g x) in H'; auto. red in H,H''.
  assert ([f[x], x] ∈ f﹣¹). { apply Classifier2. apply x_fx_T; auto. }
  assert ([y, x] ∈ f﹣¹).
  { red in I1. destruct I1. rewrite <-H7. red in H6. destruct H6 as [H6 H6'].
    rewrite <-H7 in H6'. rewrite H2. rewrite <-H7. rewrite <-H7 in H0.
    apply x_fx_T; auto. }
  applyClassifier2 H5. applyClassifier2 H6. apply (H x f[x] y) in H5; auto.
Qed.

(* 定义:限制 *)
Definition Restriction {X Y : Type} (f : (@set (@prod X Y))) (D : (@set X)) :=
  f ∩ (D × (Full Y)).
Notation "f | [ D ]" := (Restriction f D)(at level 30).

(* 函数的限制还是函数 *)
Property RF_F : ∀ {X Y : Type} (f : (@set (@prod X Y))) (D : (@set X)),
  Function f -> (Function (f|[D])).
Proof.
  intros. unfold Function. intros. applyClassifier1 H0. destruct H0. 
  applyClassifier1 H1. destruct H1. unfold Function in H. apply (H x); auto.
Qed.

(* 函数限制后与原函数的关系 *)
Property RestrictFun : ∀ {X Y : Type} (f : (@set (@prod X Y))) (D : (@set X)),
  Function f -> (Function (f|[D]) /\ dom[f|[D]] = (D ∩ (dom[f]))
  /\ (∀ x, x ∈ dom[f|[D]] -> (f|[D])[x] = f[x])).
Proof.
  intros. split; [apply RF_F; auto|split]; intros.
  - apply AxiomI. split; intro H1.
    + applyClassifier1 H1. destruct H1 as [v H2]. red in H2. applyClassifier1 H2. 
      destruct H2 as [H3 H4]. apply Classifier1. split.
      * applyClassifier2 H4. destruct H4; auto.
      * apply Classifier1. exists v; auto.
    + applyClassifier1 H1. destruct H1 as [H2 H3]. applyClassifier1 H3. 
      destruct H3 as [v H4]. apply Classifier1. exists v. apply Classifier1. 
      split; auto. apply Classifier2. split; auto. apply Classifier1. auto.
  - applyClassifier1 H0. destruct H0. pose proof H0. apply f_x_T in H0.
    + rewrite H0. applyClassifier1 H1. destruct H1. apply f_x_T in H1; auto.
    + apply RF_F; auto.
Qed.

(* 1-1函数的限制还是1-1函数 *)
Property RestrictFun1_1 : ∀ {X Y : Type} (f : (@set (@prod X Y)))
  (x : (@set X)), Function1_1 f -> Function1_1 (f|[x]).
Proof.
  intros. destruct H. split.
  - red; intros. applyClassifier1 H1. applyClassifier1 H2.
    destruct H1 as [], H2 as []. red in H. apply (H x0 _ _); auto.
  - red; intros. applyClassifier2 H1. applyClassifier2 H2.
    applyClassifier1 H1. applyClassifier1 H2. destruct H1 as [], H2 as [].
    red in H0. apply (H0 x0 _ _); apply Classifier2; auto.
Qed.

(* 1-1函数的逆还是1-1函数 *)
Property invFun1_1 : ∀ {X Y : Type}(f : (@set (@prod X Y))),
  Function1_1 f -> Function1_1 (f﹣¹).
Proof.
  intros. destruct H. split; auto. red; intros. apply ->Classifier2 in H1. simpl in H1.
  applyClassifier2 H2. applyClassifier2 H1. applyClassifier2 H2. apply (H x); auto.
Qed.

(* 函数复合的性质 *)
(* 函数复合后还是函数 *)
Property Comp_Fun_P1 : ∀ {X Y Z : Type}(f : @set (@prod X Y))(g : @set (@prod Z X)),
  Function f -> Function g -> Function (f ◦ g).
Proof.
  intros. unfold Function; intros. applyClassifier2 H1. applyClassifier2 H2.
  destruct H1 as [x0[]], H2 as [x1[]]. apply f_x_T in H1; auto.
  apply f_x_T in H2; auto. apply f_x_T in H3; auto. apply f_x_T in H4; auto.
  rewrite <-H3,<-H4,<-H1,<-H2; auto.
Qed.

(* 函数复合后的定义域 *)
Property Comp_Fun_P2 : ∀ {X Y Z : Type}(f : @set (@prod X Y))(g : @set (@prod Z X)),
  Function f -> Function g -> dom[f ◦ g] = \{ λ x, g[x] ∈ dom[f] \} ∩ dom[g].
Proof.
  intros. apply AxiomI; split; intros.
  - applyClassifier1 H1. destruct H1. applyClassifier2 H1. destruct H1 as [x0[]].
    apply Classifier1; split; apply Classifier1; eauto. pose proof H1.
    apply f_x_T in H3; auto. rewrite H3. apply Classifier1; eauto.
  - applyClassifier1 H1. destruct H1. applyClassifier1 H1. apply x_fx_T in H1; auto.
    apply x_fx_T in H2; auto. apply Classifier1. exists f[g[z]].
    apply Classifier2; eauto.
Qed.

(* 函数复合后的取值 *)
Property Comp_Fun_P3 : ∀ {X Y Z : Type}(f : @set (@prod X Y))(g : @set (@prod Z X)),
  Function f -> Function g -> (∀ x, x ∈ dom[f ◦ g] -> (f ◦ g)[x] = f[g[x]]).
Proof.
  intros. pose proof H1. rewrite Comp_Fun_P2 in H1; auto.
  applyClassifier1 H1. destruct H1. applyClassifier1 H1. pose proof H.
  apply (Comp_Fun_P1 f g) in H4; auto. apply x_fx_T in H1; auto.
  apply x_fx_T in H2; auto. apply x_fx_T in H3; auto.
  assert ([x, f[g[x]]] ∈ f ◦ g). { apply Classifier2; eauto. }
  apply (H4 x); auto.
Qed.

(* 1-1函数复合以后还是1-1函数 *)
Property Comp_Fun_P4 : ∀ {X Y Z : Type}(f : @set (@prod X Y))(g : @set (@prod Z X)),
  Function1_1 f /\ Function1_1 g -> Function1_1 (f ◦ g).
Proof.
  intros. destruct H as [[H1 H][H2 H3]]. split.
  - red; intros. applyClassifier2 H0. applyClassifier2 H4.
    destruct H0 as [x0[]], H4 as [x1[]].
    apply f_x_T in H5, H6; apply f_x_T in H0, H4; subst; auto.
  - red; intros. repeat applyClassifier2 H0. repeat applyClassifier2 H4.
    destruct H0 as [x0[]], H4 as [x1[]].
    assert(x0=x1). { red in H. apply (H x _ _); apply Classifier2; auto. }
    rewrite H7 in H0. red in H3. apply(H3 x1 _ _);  apply Classifier2; auto.
Qed.


(*********************** 自然数、有限集与无限集 ***********************)

(* 读取自然数线性运算策略lia *)
Require Export Coq.micromega.Lia.

Corollary AxiomP1 :  0 ∈ Full nat.
Proof. apply Classifier1; auto. Qed.

Corollary AxiomP2 : ∀ m n p, S m = n -> S m = p -> n = p.
Proof. intros. rewrite <- H; auto. Qed.

Corollary AxiomP3 : ∀ m , ~ (S m = 0).
Proof. intros m H1. inversion H1. Qed.

Corollary AxiomP4 : ∀ m n, ~ (m = n) -> ~ (S m = S n).
Proof. intros. intro H1. elim H. inversion H1. auto. Qed.

Corollary AxiomP5 : ∀ M, 0 ∈ M -> (∀ n, n ∈ M -> (S n) ∈ M) -> ∀ m, m ∈ M.
Proof. intros. induction m; auto. Qed.

(* 定义: 非空有限集 *)
Definition NotEmptyFinite {X} (A : set) := ∃ n (f : @set (@prod nat X)),
  Function1_1 f /\ dom[f] = \{ λ x, x <= n \} /\ ran[f] = A.

(* 定义: 有限集 *)
Definition Finite {X} A := NotEmptyFinite A \/ A = (Empty X).

(*----------以下为有限集的一些结论------------*)
(* 单点集为非空有限集 *)
Fact SingletonFinite : ∀ X (x : X), NotEmptyFinite ([x]).
Proof.
  intros. exists 0%nat, \{\ λ u v, (u = 0)%nat /\ v = x \}\. split.
  - split; unfold Function; intros; applyClassifier2 H; applyClassifier2 H0;
    [ |applyClassifier2 H; applyClassifier2 H0]; destruct H, H0.
    rewrite H1,H2; auto. rewrite H,H0; auto.
  - split; apply AxiomI; split; intros; applyClassifier1 H;
    try (destruct H; applyClassifier2 H; destruct H; apply Classifier1);
    try rewrite H; auto; apply Classifier1; [exists x|exists 0%nat];
    apply Classifier2; auto. applyClassifier1 H. split; auto. lia.
Qed.

(* 小于等于某个数的自然数集为非空有限集 *)
Fact NatFinite : ∀ n : nat, NotEmptyFinite \{ λ u, (u <= n)%nat \}.
Proof.
  intros n. unfold NotEmptyFinite.
  exists n, \{\ λ u v, v = u /\ (u <= n)%nat \}\. split; [ |split].
  - split.
    + unfold Function. intros x y z H0 H1. applyClassifier2 H0.
      applyClassifier2 H1. destruct H1 as [H1 H2]. rewrite H1. apply H0.
    + unfold Function. intros x y z H0 H1. applyClassifier2 H0. 
      applyClassifier2 H1. applyClassifier2 H0. applyClassifier2 H1. 
      destruct H0 as [H0 H2]. rewrite <- H0. apply H1.
  - apply AxiomI; intro z; split; intro H0.
    + applyClassifier1 H0. destruct H0 as [y H0]. applyClassifier2 H0.
      apply <- Classifier1. apply H0.
    + apply <- Classifier1. exists z. apply <- Classifier2. applyClassifier1 H0. split; auto.
  - apply AxiomI; intro z; split; intro H0.
    + applyClassifier1 H0. destruct H0 as [x H0]. applyClassifier2 H0.
      apply <- Classifier1. destruct H0 as [H0 H1]. rewrite H0; auto.
    + apply <- Classifier1. exists z. apply <- Classifier2. applyClassifier1 H0. split; auto.
Qed.

(* 有限集的子集为有限集 *)
Fact SubSetFinite : ∀ {X} (A B : @set X), Finite A -> B ⊂ A -> Finite B.
Proof.
 intros X A B H0 H1. unfold Finite in *. destruct H0 as [H0 | H0].
 - destruct classic with (P := B = Empty X) as [H2 | H2]; [right | ]; auto. 
   apply not_empty in H2. left. unfold NotEmptyFinite in H0. 
   destruct H0 as [n H0]. generalize dependent H0. generalize dependent A. 
   generalize dependent B. induction n as [|n H0].
   + intros B H2 A H0 H1. destruct H1 as [f [H1 [H3 H4]]].
     pose proof H2 as H2'. destruct H2' as [b].
     assert (H5 : A = [f[0%nat]]).
     { apply AxiomI. intro z; split; intro J1.
       - rewrite <- H4 in J1. applyClassifier1 J1. destruct J1 as [x J1]. 
         assert (J2 : x ∈ dom[f]). { apply <- Classifier1. exists z. auto. }
         rewrite H3 in J2. applyClassifier1 J2. apply PeanoNat.Nat.le_0_r in J2.
         apply <- Classifier1. rewrite <-J2. symmetry. apply f_x_T; auto. apply H1.
       - applyClassifier1 J1. rewrite <- H4. apply <- Classifier1. exists 0%nat.
         assert (J2 : 0%nat ∈ dom[f]). { rewrite H3. apply <- Classifier1. auto. }
         applyClassifier1 J2. destruct J2 as [y J2].
         apply f_x_T in J2 as J3; try apply H1. rewrite J1. rewrite J3. auto. }
     assert (H6 : B = [f[0%nat]]).
     { apply AxiomI. intro z; split; intro H6.
       - rewrite <- H5. auto.
       - unfold NotEmpty in H2. destruct H2 as [x H2]. assert (J1 : x ∈ A).
         auto. rewrite H5 in J1. applyClassifier1 H6. applyClassifier1 J1. 
         rewrite H6. rewrite <- J1. auto. }
     rewrite H6. apply SingletonFinite.
   + intros B H2 A H1 H3. destruct H3 as [f [H3 [H4 H5]]].
     assert (H6 : ∃ C, C = \{ λ x, (x <= n)%nat \}).
     { exists \{ λ x, (x <= n)%nat \}; auto. }
     destruct H6 as [C H6]. assert (H7 : Function1_1 f). auto.
     destruct H7 as [H7 H8]. pose proof H2 as H2'. destruct H2' as [b].
     assert (H9 : ran[f|[C]] ∪ [f[S n]] = A).
     { apply AxiomI. intro z; split; intro J1.
       - applyClassifier1 J1. destruct J1 as [J1 | J1].
         + rewrite <- H5. applyClassifier1 J1. destruct J1 as [x J1]. applyClassifier1 J1. 
           destruct J1 as [J1 J2]. apply <- Classifier1. exists x. auto.
         + rewrite <- H5. applyClassifier1 J1. rewrite J1. 
           apply fx_ran_T; auto. rewrite H4. apply <- Classifier1. apply le_n.
       - rewrite <- H5 in J1. applyClassifier1 J1. destruct J1 as [x J1]. 
         assert (J2 : x ∈ dom[f]). { apply <- Classifier1. exists z. auto. }
         rewrite H4 in J2. applyClassifier1 J2. 
         apply PeanoNat.Nat.le_succ_r in J2 as J3.
         apply <- Classifier1. destruct J3 as [J3 | J3].
         + left. apply <- Classifier1. exists x. apply <- Classifier1. split; auto.
           apply <- Classifier2. split.
           * rewrite H6. apply <- Classifier1. auto.
           * apply <- Classifier1. auto.
         + right. apply <- Classifier1. symmetry. apply f_x_T; auto.
           rewrite <- J3. auto. }
     apply (@ RestrictFun nat X f C) in H7 as H10.
     destruct H10 as [H10 [H11 H12]].
     assert (H13 : dom[f|[C]] = C).
     { rewrite H11. apply AxiomI. intro z; split; intro J1.
       - apply -> Classifier1 in J1. apply J1.
       - apply <- Classifier1. split; auto. rewrite H4. apply <- Classifier1.
         rewrite H6 in J1. apply -> Classifier1 in J1; simpl in J1.
         apply le_S. auto. }
     assert (H14 : (B — ([f[S n]])) ⊂ (A — ([f[S n]]))).
     { intros z J1. apply -> Classifier1 in J1; simpl in J1. 
       destruct J1 as [J1 J2]. apply -> Classifier1 in J2; simpl in J2.
       apply <- Classifier1. split; auto. }
     assert (H20 : ran[f|[C]] = A — [f [S n]]).
     { apply AxiomI. intro z; split; intro K1.
       - apply <- Classifier1. split.
         + rewrite <- H9. apply <- Classifier1. left; auto.
         + apply <- Classifier1. intro K2. apply -> Classifier1 in K1; simpl in K1. 
           destruct K1 as [x K1]. apply -> Classifier1 in K2; simpl in K2. 
           assert (K3 : x ∈ (C ∩ dom[f])).
           { rewrite <- H11. apply <- Classifier1. exists z. auto. }
           apply -> Classifier1 in K3; simpl in K3. destruct K3 as [K3 K4]. 
           rewrite H6 in K3. apply -> Classifier1 in K3; simpl in K3.
           apply -> Classifier1 in K1; simpl in K1. assert (K5 : [S n, z] ∈ f).
           { assert (L1 : S n ∈ dom[f]). { rewrite H4. apply <- Classifier1. auto. }
             apply -> Classifier1 in L1; simpl in L1. destruct L1 as [y L1].
             apply f_x_T in L1 as L2; auto. rewrite K2. rewrite L2. auto. }
           destruct K1 as [K1 K6]. assert (K7 : x = S n).
           { apply H8 with (x := z); apply <- Classifier2; auto. }
           rewrite K7 in K3. assert (K8 : (n < S n)%nat).
           { apply PeanoNat.Nat.lt_succ_diag_r. }
           apply PeanoNat.Nat.nle_succ_diag_l in K3. auto.
       - apply -> Classifier1 in K1; simpl in K1. destruct K1 as [K1 K2]. 
         rewrite <- H9 in K1. apply -> Classifier1 in K2; simpl in K2.
         apply -> Classifier1 in K1; simpl in K1.
         destruct K1 as [K1 | K1]; auto. exfalso. auto. }
     destruct classic with (P := f[S n] ∈ B) as [H15 | H15].
     * destruct classic with (P := (B — ([f[S n]])) = Empty X) as [J1 | J1].
       -- assert (J2 : B = [f[S n]]). 
          { apply AxiomI. intro z; split; intro K1.
            - apply <- Classifier1. apply NNPP. intro K2. 
              assert (K3 : z ∈ (Empty X)).
              { rewrite <- J1. apply <- Classifier1. split; auto. }
              apply -> Classifier1 in K3; simpl in K3. auto.
            - apply -> Classifier1 in K1; simpl in K1. rewrite K1. auto. }
          rewrite J2. apply SingletonFinite.
       -- assert (J2 : NotEmptyFinite (B — [f[S n]])).
          { apply H0 with (A := (A — [f[S n]])); auto.
            - apply not_empty. auto.
            - exists (f|[C]). split; [ | split]; auto.
              + apply RestrictFun1_1; eauto.
              + rewrite H13. auto. }
          unfold NotEmptyFinite in J2. destruct J2 as [n0 [f0 [J3 [J4 J5]]]].
          unfold NotEmptyFinite. exists (S n0), (f0 ∪ [[(S n0), f[S n]]]).
          split; [idtac | split].
          ++ split.
             ** unfold Function. intros x y z K1 K2.
                apply -> Classifier1 in K1; simpl in K1.
                apply -> Classifier1 in K2; simpl in K2.
                destruct K1 as [K1 | K1].
              --- destruct K2 as [K2 | K2].
               +++ destruct J3 as [J3 J6]. apply J3 with (x := x); auto.
               +++ exfalso. apply -> Classifier1 in K2; simpl in K2.
                   apply ProdEqual in K2. destruct K2 as [K2 K3].
                   assert (K4 : x ∈ dom[f0]).
                   { apply <- Classifier1. exists y; auto. }
                   rewrite J4 in K4. apply -> Classifier1 in K4; simpl in K4.
                   rewrite K2 in K4. assert (K5 : (n0 < S n0)%nat).
                   { apply PeanoNat.Nat.lt_succ_diag_r. }
                   apply PeanoNat.Nat.nle_succ_diag_l in K4. auto.
              --- destruct K2 as [K2 | K2].
               +++ exfalso. apply -> Classifier1 in K1; simpl in K1.
                   apply ProdEqual in K1. destruct K1 as [K1 K3].
                   assert (K4 : x ∈ dom[f0]).
                   { apply <- Classifier1. exists z; auto. }
                   rewrite J4 in K4. apply -> Classifier1 in K4; simpl in K4.
                   rewrite K1 in K4. assert (K5 : (n0 < S n0)%nat).
                   { apply PeanoNat.Nat.lt_succ_diag_r. }
                   apply PeanoNat.Nat.nle_succ_diag_l in K4. auto.
               +++ apply -> Classifier1 in K1; simpl in K1.
                   apply -> Classifier1 in K2; simpl in K2.
                   apply ProdEqual in K1. apply ProdEqual in K2.
                   destruct K2 as [K2 K3]. rewrite K3. apply K1.
             ** unfold Function. intros x y z K1 K2.
                apply -> Classifier2 in K1; simpl in K1.
                apply -> Classifier2 in K2; simpl in K2.
                apply -> Classifier1 in K1; simpl in K1.
                apply -> Classifier1 in K2; simpl in K2.
                destruct K1 as [K1 | K1].
              --- destruct K2 as [K2 | K2].
               +++ apply J3 with (x := x); apply <- Classifier2; auto.
               +++ exfalso. apply -> Classifier1 in K2; simpl in K2.
                   apply ProdEqual in K2. destruct K2 as [K2 K3].
                   assert (K4 : x ∈ ran[f0]).
                   { apply <- Classifier1. exists y. auto. }
                   rewrite J5 in K4. apply -> Classifier1 in K4; simpl in K4.
                   destruct K4 as [K4 K5]. apply -> Classifier1 in K5; simpl in K5.
                   apply K5. apply <- Classifier1. auto.
              --- destruct K2 as [K2 | K2].
               +++ exfalso. apply -> Classifier1 in K1; simpl in K1.
                   apply ProdEqual in K1. destruct K1 as [K1 K3].
                   assert (K4 : x ∈ ran[f0]).
                   { apply <- Classifier1. exists z. auto. }
                   rewrite J5 in K4. apply -> Classifier1 in K4; simpl in K4.
                   destruct K4 as [K4 K5]. apply -> Classifier1 in K5; simpl in K5.
                   apply K5. apply <- Classifier1. auto.
               +++ apply -> Classifier1 in K1; simpl in K1.
                   apply -> Classifier1 in K2; simpl in K2.
                   apply ProdEqual in K1. apply ProdEqual in K2.
                   destruct K2 as [K2 K3]. rewrite K2. apply K1.
          ++ apply AxiomI. intro z; split; intro K1.
             ** apply -> Classifier1 in K1; simpl in K1. destruct K1 as [y K1].
                apply -> Classifier1 in K1; simpl in K1. destruct K1 as [K1 | K1].
              --- assert (K2 : z ∈ dom[f0]).
                  { apply <- Classifier1. exists y. auto. }
                  rewrite J4 in K2. apply -> Classifier1 in K2; simpl in K2.
                  apply <- Classifier1. apply le_S. auto.
              --- apply -> Classifier1 in K1; simpl in K1.
                  apply ProdEqual in K1. destruct K1 as [K1 K2].
                  apply <- Classifier1. rewrite K1. auto.
            ** apply -> Classifier1 in K1; simpl in K1.
               apply PeanoNat.Nat.le_succ_r in K1 as K2.
               apply <- Classifier1. destruct K2 as [K2 | K2].
              --- assert (K3 : z ∈ dom[f0]).
                  { rewrite J4. apply <- Classifier1. auto. }
                  apply -> Classifier1 in K3; simpl in K3.
                  destruct K3 as [y K3]. exists y. apply <- Classifier1. left; auto.
              --- exists (f[S n]). apply <- Classifier1. right.
                 apply <- Classifier1. rewrite K2. auto.
          ++ apply AxiomI. intro z; split; intro K1.
             ** apply -> Classifier1 in K1; simpl in K1. destruct K1 as [x K1].
                apply -> Classifier1 in K1; simpl in K1. destruct K1 as [K1 | K1].
              --- assert (K2 : z ∈ ran[f0]).
                  { apply <- Classifier1. exists x. auto. } rewrite J5 in K2.
                  apply -> Classifier1 in K2; simpl in K2. apply K2.
              --- apply -> Classifier1 in K1; simpl in K1. apply ProdEqual in K1. 
                  destruct K1 as [K1 K2]. rewrite K2. auto.
             ** apply <- Classifier1.
                destruct classic with (P := z = f[S n]) as [K2 | K2].
              --- exists (S n0). apply <- Classifier1. right. apply <- Classifier1.
                  rewrite K2. auto.
              --- assert (K3 : z ∈ ran[f0]).
                  { rewrite J5. apply <- Classifier1. split; auto. }
                  apply -> Classifier1 in K3; simpl in K3. destruct K3 as [x K3].
                  exists x. apply <- Classifier1. left. auto.
     * assert (H16 : B ⊂ (A — ([f[S n]]))).
       { assert (I1 : (B — ([f[S n]])) = B).
         { apply AxiomI. intro z; split; intro I1.
           - apply -> Classifier1 in I1; simpl in I1. apply I1.
           - apply <- Classifier1. split; auto. apply <- Classifier1. intro I2.
             apply -> Classifier1 in I2; simpl in I2. rewrite <- I2 in H15. auto. }
         rewrite <- I1. auto. }
       apply H0 with (A := (A — [f[S n]])); auto. exists (f|[C]).
       split; [ | split]; auto.
       -- apply RestrictFun1_1; eauto.
       -- rewrite H13. auto.
 - right. apply AxiomI. intro z; split; intro H2.
   + rewrite <- H0. auto.
   + exfalso. apply -> Classifier1 in H2; simpl in H2. auto.
Qed.


(* 最大值 *)
(* 自然数中的最大值 *)
Definition maxN (A : set) (n : nat) := n ∈ A /\ (∀ x, x ∈ A -> x <= n)%nat.

(* 非空有限的自然数集有最大值 *)
Fact finite_maxN : ∀ (A : set), NotEmptyFinite A -> (∃ n : nat, maxN A n).
Proof.
  intros A H1. unfold NotEmptyFinite in H1. destruct H1 as [n H1].
  generalize dependent H1. generalize dependent A. induction n as [|n H1].
  - intros A H1. destruct H1 as [f [H1 [H2 H3]]].
    assert (H4 : \{ λ x : nat, (x <= 0)%nat \} = [0%nat]).
    { apply AxiomI. intro z; split; intro I1.
      - apply <- Classifier1. apply -> Classifier1 in I1. simpl in I1. symmetry. lia.
      - apply -> Classifier1 in I1; simpl in I1. rewrite I1. apply <- Classifier1.
        apply le_n. }
    rewrite H4 in H2. assert (H5 : A = [f[0%nat]]).
    { apply AxiomI. intro z; split; intro J1.
      - apply <- Classifier1. rewrite <- H3 in J1.
        apply -> Classifier1 in J1; simpl in J1. destruct J1 as [x J1].
        assert (J2 : x ∈ dom[f]). { apply <- Classifier1. exists z. auto. }
        rewrite H2 in J2. apply -> Classifier1 in J2; simpl in J2.
        rewrite J2 in J1. destruct H1 as [H1 J3]. pose proof J1.
        apply f_x_T in J1; auto.
      - apply -> Classifier1 in J1; simpl in J1. rewrite <- H3.
        apply <- Classifier1. exists 0%nat. assert (J2 : 0%nat ∈ dom[f]).
        { rewrite H2. apply <- Classifier1. auto. }
        apply -> Classifier1 in J2; simpl in J2. destruct J2 as [y J2].
        destruct H1 as [H1 J3]. eapply f_x_T in J2 as J4; auto.
        rewrite J1. rewrite J4. auto. }
    exists f[0%nat]. unfold maxN. split.
    + rewrite H5. apply <- Classifier1. auto.
    + intros x. intro J1. rewrite H5 in J1.
      apply -> Classifier1 in J1; simpl in J1. rewrite <- J1. apply le_n.
  - intros A H2. destruct H2 as [f [H2 [H3 H4]]].
    assert (H5 : ∃ B, B = \{ λ x, (x <= n)%nat \}).
    { exists \{ λ x, (x <= n)%nat \}. auto. }
    destruct H5 as [B H5]. apply (@ RestrictFun1_1 nat nat f B) in H2 as H6.
    destruct H2 as [H2 H7]. apply (@ RestrictFun nat nat f B) in H2 as H8.
    destruct H8 as [H8 [H9 H10]].
    assert (H11 : ∃n : nat, maxN ran[f|[B]] n).
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
        + rewrite <- H4. apply -> Classifier1 in J1; simpl in J1. rewrite J1. 
          apply fx_ran_T; auto. rewrite H3. apply <- Classifier1. apply le_n.
      - rewrite <- H4 in J1. apply -> Classifier1 in J1; simpl in J1.
        destruct J1 as [x J1]. assert (J2 : x ∈ dom[f]).
        { apply <- Classifier1. exists z. auto. }
        rewrite H3 in J2. apply -> Classifier1 in J2; simpl in J2.
        apply PeanoNat.Nat.le_succ_r in J2 as J3. apply <- Classifier1.
        destruct J3 as [J3 | J3].
        + left. apply <- Classifier1. exists x. apply <- Classifier1. split; auto.
          apply <- Classifier2. split.
          * rewrite H5. apply <- Classifier1. auto.
          * apply <- Classifier1. auto.
        + right. apply <- Classifier1. symmetry. apply f_x_T; auto.
          rewrite <- J3. auto. }
    destruct H11 as [n1 H11].
    destruct (Compare_dec.le_gt_dec n1 (f[S n])) as [H13 | H13].
    + exists (f[S n]). unfold maxN. split.
      * rewrite <- H12. apply <- Classifier1. right. apply <- Classifier1; auto.
      * intros x J1. rewrite <- H12 in J1. apply -> Classifier1 in J1; simpl in J1.
        destruct J1 as [J1 | J1].
        -- apply H11 in J1. apply PeanoNat.Nat.le_trans with (m := n1); auto.
        -- apply -> Classifier1 in J1; simpl in J1. rewrite <- J1. apply le_n.
    + exists n1. unfold maxN. split.
      * rewrite <- H12. apply <- Classifier1. left. apply H11.
      * intros x J1. rewrite <- H12 in J1. apply -> Classifier1 in J1; simpl in J1.
        destruct J1 as [J1 | J1].
        -- apply H11. auto.
        -- apply -> Classifier1 in J1; simpl in J1. rewrite J1.
           apply PeanoNat.Nat.lt_le_incl. auto.
Qed.









