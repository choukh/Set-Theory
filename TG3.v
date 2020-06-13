(*** Formal Construction of a Set Theory in Coq ***)
(** based on the thesis by Jonas Kaiser, November 23, 2012 **)
(** Coq coding by choukh, April 2020 **)

Require Export ZFC.TG2.
Require Import Setoid.

(*** TG集合论扩展3：选择公理，正则公理，笛卡尔积，函数(Aczel编码) ***)

(** 希尔伯特ε算子等效于选择公理 **)

(* 选择函数 *)
Definition cho : set → set := λ s, ε (inhabits ∅) (λ x, x ∈ s).

(* “答案确实是在题目选项里选的” *)
Lemma chosen_contained : ∀ s, ⦿s → cho s ∈ s.
Proof. intros s. exact (ε_spec (inhabits ∅) (λ x, x ∈ s)). Qed.

(* “答案集包含在问题集的并集里” *)
Theorem chosen_included : ∀ S, (∀s ∈ S, ⦿s) → {cho | s ∊ S} ⊆ ⋃S.
Proof.
  unfold Sub. unfoldq. intros.
  apply ReplE in H0. unfoldq.
  destruct H0 as [s [H1 H2]].
  specialize H with s.
  eapply UnionI. apply H1.
  apply H in H1. subst.
  apply chosen_contained. apply H1.
Qed.

(* “单选题” *)
Theorem one_chosen : ∀ S, (∀s ∈ S, ⦿s) →
  (∀ s t ∈ S, s ≠ t → s ∩ t = ∅) →
  ∀s ∈ S, ∃ x, s ∩ {cho | s ∊ S} = ⎨x⎬.
Proof.
  unfoldq. intros S Hi Hdj s Hs.
  exists (cho s).
  apply sub_asym.
  - unfold Sub. introq. apply BInterE in H as [Hx1 Hx2].
    cut (x = cho s).
    + intros. subst. apply SingI.
    + apply ReplE in Hx2.
      destruct Hx2 as [t [Ht Hteq]].
      destruct (classic (s = t)).
      * subst. reflexivity.
      * pose proof (Hdj s Hs t Ht H).
        pose proof ((EmptyE H0) x).
        exfalso. apply H1. apply BInterI. apply Hx1.
        pose proof (chosen_contained t (Hi t Ht)).
        rewrite Hteq in H2. apply H2.
  - apply in_impl_sing_sub. apply BInterI.
    + apply chosen_contained. apply Hi. apply Hs.
    + apply ReplI. apply Hs.
Qed.

(** 更多经典逻辑引理 **)

Lemma double_negation : ∀ P : Prop, ¬¬P ↔ P.
Proof.
  split; intros.
  - destruct (classic P) as [HP | HF]; firstorder.
  - destruct (classic (¬P)) as [HF | HFF]; firstorder.
Qed.

Lemma classic_neg_all_1 : ∀ P : set → Prop, ¬ (∀ X, ¬ P X) ↔ (∃ X, P X).
Proof.
  split; intros.
  - destruct (classic (∃ X, P X)); firstorder.
  - firstorder.
Qed.

Lemma classic_neg_all_2 : ∀ P : set → Prop, ¬ (∀ X, P X) ↔ (∃ X, ¬ P X).
Proof.
  intros. pose proof (classic_neg_all_1 (λ x, ¬ P x)).
  simpl in H. rewrite <- H. clear H.
  split; intros.
  - intros H1. apply H. intros. specialize H1 with X.
    rewrite double_negation in H1. apply H1.
  - firstorder.
Qed.

(** ∈归纳原理等效于正则公理模式 **)
Theorem reg_schema : ∀ P,
  (∃ X, P X) → ∃ X, P X ∧ ¬∃x ∈ X, P x.
Proof.
  intros P. pose proof (ε_ind (λ x, ¬ P x)). simpl in H.
  remember (∀ X, (∀x ∈ X, ¬ P x) → ¬ P X) as A.
  remember (∀ X, ¬ P X) as B.
  assert (∀ P Q: Prop, (P → Q) → (¬ Q → ¬ P)) by auto.
  pose proof (H0 A B H). subst. clear H H0.
  rewrite classic_neg_all_1 in H1.
  rewrite classic_neg_all_2 in H1.
  intros. apply H1 in H. destruct H as [X H].
  exists X. clear H1.
  assert (∀ A B : Prop, ¬ (A → ¬ B) ↔ ¬¬B ∧ ¬¬A) by firstorder.
  rewrite H0 in H. clear H0.
  repeat rewrite double_negation in H. firstorder.
Qed.

(* 由正则公理模式导出原始正则公理：
  所有非空集合X中至少有一个成员x，它与X的交集为空集。*)
Theorem regularity : ∀ X, ⦿ X → ∃x ∈ X, x ∩ X = ∅.
Proof.
  introq.
  pose proof (reg_schema (λ x, x ∈ X)).
  simpl in H0. apply H0 in H.
  destruct H as [x [H1 H2]].
  exists x. split. apply H1.
  apply EmptyI. intros y H3.
  apply H2. apply BInterE in H3. unfoldq.
  exists y. apply H3.
Qed.

(* 不存在以自身为元素的集合 *)
Theorem not_self_contained : ¬ ∃ x, x ∈ x.
Proof.
  intros H.
  pose proof (reg_schema (λ x, x ∈ x)).
  simpl in H0. apply H0 in H.
  destruct H as [x [H1 H2]].
  apply H2. unfoldq. exists x; auto.
Qed.

(** 笛卡儿积 **)
Definition CProd : set → set → set := λ A B,
  ⋃ {λ a, {λ b, <a, b> | x∊B} | x∊A}.
Notation "A × B" := (CProd A B) (at level 40).

Lemma CProdI : ∀ A B, ∀a ∈ A, ∀b ∈ B, <a, b> ∈ A × B.
Proof.
  introq. eapply UnionI.
  - apply ReplI. apply H.
  - apply ReplI. apply H0.
Qed.

Lemma CProdE1 : ∀ p A B, p ∈ A × B → π1 p ∈ A ∧ π2 p ∈ B.
Proof.
  intros. apply UnionAx in H. destruct H as [x [H1 H2]].
  apply ReplE in H1. destruct H1 as [a [H3 H4]].
  subst x. apply ReplE in H2. destruct H2 as [b [H1 H2]].
  symmetry in H2. split.
  - rewrite H2. rewrite π1_correct. apply H3.
  - rewrite H2. rewrite π2_correct. apply H1.
Qed.

Lemma CProdE2 : ∀ p A B, p ∈ A × B → is_pair p.
Proof.
  intros. apply UnionAx in H. destruct H as [x [H1 H2]].
  apply ReplE in H1. destruct H1 as [a [H3 H4]].
  subst x. apply ReplE in H2. destruct H2 as [b [H1 H2]].
  exists a, b. auto.
Qed.

Lemma CProd_correct : ∀ p A B, p ∈ A × B ↔ ∃a ∈ A, ∃b ∈ B, p = <a, b>.
Proof.
  unfoldq. split; intros.
  - apply CProdE1 in H as H0. destruct H0 as [H1 H2].
    apply CProdE2 in H. destruct H as [a [b H]].
    rewrite H in *. rewrite π1_correct in H1.
    rewrite π2_correct in H2. firstorder.
  - destruct H as [a [H1 H2]]. destruct H2 as [b [H2 H3]].
    subst. apply CProdI. apply H1. apply H2.
Qed.

Example cprod_0_x : ∀ B, ∅ × B = ∅.
Proof. unfold CProd. intros. rewrite funion_0. reflexivity. Qed.

Example cprod_x_0 : ∀ A, A × ∅ = ∅.
Proof.
  intros. apply sub_0_iff_0. unfold CProd, Sub. introq.
  apply CProdE1 in H. destruct H as [_ H]. exfalso0.
Qed.

Lemma GUCProd : ∀ N, ∀X ∈ 𝒰(N), ∀Y ∈ 𝒰(N), X × Y ∈ 𝒰(N).
Proof.
  introq. apply GUFUnion. apply H.
  introq. apply GURepl. apply H0.
  introq. apply GUOPair.
  - eapply GUTrans. apply H1. apply H.
  - eapply GUTrans. apply H2. apply H0.
Qed.

(** 函数（Aczel编码） **)

(* 函数应用 *)
(* ap f x := {y | <x, y> ∈ f} *)
Definition apₐ : set → set → set := λ f x,
  let P := {p ∊ f | λ p, is_pair p ∧ π1 p = x} in {π2 | p ∊ P}.
Notation "f [ x ]ₐ" := (apₐ f x) (at level 60).

(* 函数本身 *)
(* Lambda X F := {<x, y> | x ∈ X ∧ y ∈ F x} *)
Definition Lambdaₐ : set → (set → set) → set := λ X F,
  ⋃{λ x, {λ y, <x, y> | y ∊ F x} | x ∊ X}.
Notation "'Λₐ' X , F" := (Lambdaₐ X F) (at level 200).

(* 函数类型 *)
(* Π X Y := {Lambda X F | ∀x ∈ X, F x ∈ Y x}
          = {f ∈ 𝒫(X × ⋃⋃{Y|x ∊ X}) | ∀x ∈ X, F x ∈ Y x} *)
Definition Πₐ : set → (set → set) → set := λ X Y, 
  {f ∊ 𝒫(X × ⋃⋃{Y|x ∊ X}) | λ f, ∀x ∈ X, f[x]ₐ ∈ Y x}.

(* 非依赖类型 *)
Definition Arrowₐ : set → set → set := λ X Y, Πₐ X (λ _, Y).
Notation "X ⟶ₐ Y" := (Arrowₐ X Y) (at level 190).

(* 常函数正好表达为笛卡尔积 *)
Fact Λₐ_const_is_cprod : ∀ A B, A × B = Λₐ A, (λ _, B).
Proof. reflexivity. Qed.

(* 函数的成员都是这样的有序对，它的左投影是定义域的成员，右投影是值域的成员的成员 *)
Lemma Λₐ_contain_pair : ∀ X F,
  ∀p ∈ (Λₐ X, F), ∃x ∈ X, ∃y ∈ F x, p = <x, y>.
Proof.
  unfoldq. unfold Lambdaₐ. intros X F p H.
  apply FUnionE in H. destruct H as [x [H1 H2]].
  apply ReplE in H2. destruct H2 as [y [H2 H3]].
  symmetry in H3. firstorder.
Qed.

Lemma apₐ_contain_pair : ∀ f x y, y ∈ f[x]ₐ ↔ <x, y> ∈ f.
Proof.
  split; intros.
  - apply ReplE in H. destruct H as [p [H1 H2]].
    apply SepE in H1. destruct H1 as [H3 [H4 H5]].
    apply op_η in H4. rewrite H4 in H3. subst. apply H3.
  - unfold apₐ. apply ReplAx. unfoldq.
    exists <x, y>. split.
    + apply SepI. apply H. split.
      * exists x, y. reflexivity.
      * apply π1_correct.
    + apply π2_correct.
Qed.

(* β规约 *)
Theorem β_reductionₐ : ∀ X F, ∀x ∈ X, (Λₐ X, F)[x]ₐ = F x.
Proof.
  introq. apply ExtAx. split; intros.
  - apply apₐ_contain_pair in H0.
    apply Λₐ_contain_pair in H0.
    destruct H0 as [a [H1 [b [H2 H3]]]].
    apply op_correct in H3. destruct H3 as [H3 H4].
    subst. apply H2.
  - apply apₐ_contain_pair. eapply UnionI.
    + apply ReplI. apply H.
    + apply ReplI. apply H0.
Qed.

Lemma β_out_0ₐ : ∀ X F x, x ∉ X → (Λₐ X, F)[x]ₐ = ∅.
Proof.
  intros. apply EmptyI. intros y H0. apply H.
  apply apₐ_contain_pair in H0.
  apply Λₐ_contain_pair in H0. destruct H0 as [a [H1 [b [H2 H3]]]].
  apply op_correct in H3 as [Hx Hy]. subst a. apply H1.
Qed.

Lemma apₐ_0_0 : ∀ a, ∅[a]ₐ = ∅.
Proof.
  unfold apₐ. introq. rewrite sep_0.
  rewrite repl_0. reflexivity.
Qed.

(* 函数是函数类型的成员 *)
Theorem Λₐ_in_Πₐ : ∀ X Y F, (∀x ∈ X, F x ∈ Y x) → (Λₐ X, F) ∈ (Πₐ X Y).
Proof.
  intros. apply SepI.
  - apply PowerAx. unfold Sub. unfoldq.
    intros p H0. apply Λₐ_contain_pair in H0.
    destruct H0 as [x [H1 [y [H2 H3]]]].
    subst. apply CProdI. apply H1.
    eapply UnionI; [|apply H2].
    eapply FUnionI. apply H1. apply H. apply H1.
  - introq. rewrite β_reductionₐ; auto.
Qed.

(* 函数类型的成员都是良定义的函数 *)
Theorem Πₐ_only_Λₐ : ∀ X Y, ∀x ∈ X, ∀f ∈ Πₐ X Y, f[x]ₐ ∈ Y x.
Proof.
  unfoldq. intros X Y x Hx f Hf. apply SepE2 in Hf.
  apply Hf. apply Hx.
Qed.

Corollary Πₐ_non_dependent : ∀ X Y, ∀x ∈ X, ∀f ∈ (X ⟶ₐ Y), f[x]ₐ ∈ Y.
Proof. intros. exact (Πₐ_only_Λₐ X (λ _, Y)). Qed.

Example arrowₐ_correct : ∀ A B f a, f ∈ (A ⟶ₐ B) → a ∈ A → f[a]ₐ ∈ B.
Proof. intros. exact (Πₐ_only_Λₐ A (λ _, B) a H0 f H). Qed.

(* 集合2在函数类型建构下封闭 *)
Theorem Πₐ_close_2 : ∀ X Y, (∀ x ∈ X, Y x ∈ 2) → Πₐ X Y ∈ 2.
Proof.
  introq. apply funion_2 in H.
  apply in_2_impl_union_0 in H.
  unfold Πₐ. remember (λ f, ∀x ∈ X, f [x]ₐ ∈ Y x) as P.
  rewrite H. rewrite cprod_x_0.
  rewrite power_0_1. rewrite <- power_1_2.
  apply sep_power.
Qed.

Lemma Λₐ_sub : ∀ X f1 f2, (∀ y ∈ X, f1 y = f2 y) → (Λₐ X, f1) ⊆ (Λₐ X, f2).
Proof.
  unfold Lambdaₐ, Sub. introq.
  apply FUnionE in H0. destruct H0 as [y [H1 H2]].
  eapply FUnionI. apply H1. apply H in H1.
  rewrite H1 in H2. apply H2.
Qed.

(* Λ算符的外延性 *)
Lemma Λₐ_ext : ∀ X f1 f2, (∀ y ∈ X, f1 y = f2 y) → (Λₐ X, f1) = (Λₐ X, f2).
Proof.
  introq. apply sub_asym.
  - apply Λₐ_sub. unfoldq. apply H.
  - apply Λₐ_sub. introq. apply H in H0. auto.
Qed.

Lemma Λₐ_β : ∀ X F, (Λₐ X, F) = Λₐ X, (λ x, (Λₐ X, F)[x]ₐ).
Proof. intros. apply Λₐ_ext. introq. rewrite β_reductionₐ; auto. Qed.

Lemma Πₐ_sub : ∀ X Y1 Y2, (∀x ∈ X, Y1 x = Y2 x) → Πₐ X Y1 ⊆ Πₐ X Y2.
Proof.
  unfold Sub. introq. 
  apply SepE in H0. destruct H0 as [H1 H2].
  apply PowerAx in H1. apply SepI.
  - apply PowerAx. unfold Sub in *.
    introq. apply H1 in H0.
    apply CProd_correct in H0.
    destruct H0 as [a [H3 [b [H4 H5]]]].
    subst x0. apply CProdI. apply H3.
    apply UnionAx in H4. destruct H4 as [c [H4 H5]].
    apply FUnionE in H4. destruct H4 as [d [H6 H7]].
    apply UnionAx. unfoldq. exists c. split; [|apply H5].
    eapply FUnionI. apply H6.
    apply H in H6. rewrite H6 in H7. apply H7.
  - introq. apply H2 in H0 as H3. apply H in H0.
    rewrite H0 in H3. apply H3.
Qed.

(* Π算符的外延性 *)
Lemma Πₐ_ext : ∀ X Y1 Y2, (∀x ∈ X, Y1 x = Y2 x) → Πₐ X Y1 = Πₐ X Y2.
Proof.
  introq. apply sub_asym.
  - apply Πₐ_sub. unfoldq. apply H.
  - apply Πₐ_sub. introq. apply H in H0. auto.
Qed.

Lemma fₐ_sub : ∀ X F f g, f ∈ Πₐ X F → (∀x ∈ X, f[x]ₐ ⊆ g[x]ₐ) → f ⊆ g.
Proof.
  unfold Sub. unfoldq. intros X F f g Hf Hsub p Hp.
  apply SepE in Hf. destruct Hf as [Hf _].
  apply PowerAx in Hf. unfold Sub in Hf.
  apply Hf in Hp as Hp'. clear Hf.
  apply CProd_correct in Hp'. destruct Hp' as [x [H1 [y [_ H2]]]].
  subst. apply apₐ_contain_pair in Hp. apply (Hsub x H1) in Hp.
  apply apₐ_contain_pair in Hp. apply Hp.
Qed.

(* 函数的外延性 *)
Theorem fₐ_ext : ∀ X F f g, f ∈ Πₐ X F → g ∈ Πₐ X F →
  (∀x ∈ X, f[x]ₐ = g[x]ₐ) → f = g.
Proof.
  introq. apply sub_asym.
  - eapply fₐ_sub. apply H. unfold Sub. introq.
    apply H1 in H2. rewrite H2 in H3. apply H3. 
  - eapply fₐ_sub. apply H0. unfold Sub. introq.
    apply H1 in H2. rewrite H2. apply H3. 
Qed.

Lemma fₐ_η : ∀ A B f, f ∈ Πₐ A B → f = Λₐ A, (λ x, f[x]ₐ).
Proof.
  intros. eapply fₐ_ext.
  - apply H.
  - apply Λₐ_in_Πₐ. introq.
    apply (Πₐ_only_Λₐ A B x H0) in H. apply H.
  - introq. rewrite β_reductionₐ; auto.
Qed.

Close Scope one_two_scope.
