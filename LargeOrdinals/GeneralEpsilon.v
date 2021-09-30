(** Coq coding by choukh, Sep 2021 **)

Require Import ZFC.LargeOrdinals.SidedTetration.
Export OrdinalClass 𝐎𝐍Separation VeblenFixedPoint.

Local Hint Resolve enum_operative
  ordAdd_ran ordMul_ran ordExp_ran ordTetL_ran : core.

(* 乘方不动点 *)
Section OrdExpFixedPoint.
Variable ξ : set.
Variable ξ_is_ord : ξ ⋵ 𝐎𝐍.
Variable ξ_neq_0 : ξ ≠ 0.
Variable ξ_neq_1 : ξ ≠ 1.
Local Hint Resolve ξ_is_ord : core.
Local Hint Resolve ξ_neq_0 : core.
Local Hint Resolve ξ_neq_1 : core.

(* ε₀定义为有限层塔序列的上界 *)
Definition ε₀ := sup {ξ ^^ᴸ n | n ∊ ω}.

(* ε₀是ω层塔 *)
Remark ε₀_normal_form : ε₀ = ξ ^^ᴸ ω.
Proof. symmetry. apply ordTetL_limit; nauto. Qed.

(* ε₀是序数 *)
Lemma ε₀_is_ord : ε₀ ⋵ 𝐎𝐍.
Proof. rewrite ε₀_normal_form; auto. Qed.
Local Hint Resolve ε₀_is_ord : core.

(* ε₀是极限序数 *)
Lemma ε₀_is_limord : ε₀ ⋵ 𝐎𝐍ˡⁱᵐ.
Proof with neauto.
  rewrite ε₀_normal_form... split... ext.
  - rewrite ordTetL_limit in *...
    apply FUnionE in H as [n [Hn H]].
    apply UnionAx. exists (ξ ^^ᴸ n). split...
    eapply FUnionI. apply ω_inductive. apply Hn.
    apply ordTetL_n_ascending...
  - apply UnionAx in H as [y [Hy H]]. eapply ord_trans...
Qed.
Local Hint Resolve ε₀_is_limord : core.

(* ε₀里有0层塔 *)
Fact ε₀_has_tower_0 : ξ ∈ ε₀.
Proof with nauto.
  apply (FUnionI _ _ 1)...
  rewrite ordTetL_1_r... rewrite <- (ordExp_1_r) at 1...
  apply ordExp_preserve_lt...
Qed.

(* ε₀里有任意有限层塔 *)
Lemma ε₀_has_tower_n : ∀n ∈ ω, ξ ^^ᴸ n ∈ ε₀.
Proof with nauto.
  intros n Hn. apply (FUnionI _ _ n⁺)...
  apply ω_inductive... apply ordTetL_n_ascending...
Qed.

(* ε₀里有任意有限层塔里的元素 *)
Lemma ε₀_has_those_of_tower_n : ∀n ∈ ω, ∀α ∈ ξ ^^ᴸ n, α ∈ ε₀.
Proof with eauto.
  intros n Hn α Hα. eapply ord_trans...
  apply ε₀_has_tower_n...
Qed.
Local Notation ε₀I := ε₀_has_those_of_tower_n.

(* ε₀的任意元素都在某有限层塔里 *)
Lemma ε₀_has_only_those_of_tower_n : ∀α ∈ ε₀, ∃n ∈ ω, α ∈ ξ ^^ᴸ n.
Proof. intros α Hα. apply FUnionE in Hα; auto. Qed.
Local Notation ε₀E := ε₀_has_only_those_of_tower_n.

(* ε₀里有且只有那些有限层塔里的元素 *)
Fact ε₀_iff_of_tower_n : ∀α ⋵ 𝐎𝐍, α ∈ ε₀ ↔ ∃n ∈ ω, α ∈ ξ ^^ᴸ n.
Proof. split. apply ε₀E. intros [n [Hn Hα]]. apply (ε₀I n); auto. Qed.

(* ε₀不等于0 *)
Lemma ε₀_neq_0 : ε₀ ≠ 0.
Proof.
  rewrite ε₀_normal_form. intros H.
  apply ordTetL_eq_0 in H; nauto.
Qed.
Local Hint Resolve ε₀_neq_0 : core.

(* ε₀对ω指数运算封闭 *)
Lemma ε₀_closed_under_ω_exp : ∀α ∈ ε₀, ξ ^ α ∈ ε₀.
Proof with nauto.
  intros α Hα.
  assert (Hoα: α ⋵ 𝐎𝐍). apply (ord_is_ords ε₀)...
  apply ε₀E in Hα as [n [Hn Hα]].
  apply (ε₀I n⁺). apply ω_inductive...
  rewrite ordTetL_suc... apply ordExp_preserve_lt...
Qed.

(* ε数 *)
Definition ε_number := λ ε, ε ⋵ 𝐎𝐍 ∧ ξ ^ ε = ε.

(* ε₀是ε数 *)
Lemma ε₀_is_ε_number : ε₀ ⋵ ε_number.
Proof with neauto.
  split... ext.
  - rewrite ordExp_limit in H...
    apply FUnionE in H as [α [Hα Hx]]. eapply ord_trans...
    apply ε₀_closed_under_ω_exp...
  - rewrite ordExp_limit... eapply FUnionI...
    apply ε₀E in H as [n [Hn Hx]].
    eapply ordExp_enlarge_l_strictly...
Qed.

(* ε数不等于0 *)
Lemma ε_number_neq_0 : ∀ε ⋵ ε_number, ε ≠ 0.
Proof with eauto.
  intros ε [Hε Heq]. intros H.
  subst. rewrite ordExp_0_r in Heq...
Qed.

(* ε数不等于1 *)
Lemma ε_number_neq_1 : ∀ε ⋵ ε_number, ε ≠ 1.
Proof with neauto.
  intros ε [Hε Heq]. intros H.
  subst. rewrite ordExp_1_r in Heq...
Qed.

(* 任意ε数都有任意有限层塔 *)
Lemma ε_number_has_tower_n : ∀n ∈ ω, ∀ε ⋵ ε_number, ξ ^^ᴸ n ∈ ε.
Proof with neauto.
  intros n Hn. ω_induction n; intros ε [Hε Heq].
  - rewrite <- zero, ordTetL_0, <- Heq...
    apply ordExp_enlarge_r...
    apply ord_neq_0_1_gt_1...
    apply ε_number_neq_0. split...
    apply ε_number_neq_1. split...
  - rewrite ordTetL_suc, <- Heq...
    apply ordExp_preserve_lt... apply IH. split...
Qed.

(* ε₀是最小的ε数 *)
Lemma ε₀_is_the_least_ε_number : ∀α ⋵ ε_number, ε₀ ⋸ α.
Proof with eauto.
  intros ε [Hε Heq]. apply ord_le_iff_sub...
  intros x Hx. apply ε₀E in Hx as [n [Hn Hx]].
  eapply ord_trans... apply ε_number_has_tower_n... split...
Qed.

(* ε运算 *)
Definition ε := Enumerate ε_number.

(* ε数是序数子类 *)
Lemma ε_number_sub_𝐎𝐍 : ε_number ⫃ 𝐎𝐍.
Proof. intros α []; auto. Qed.
Local Hint Resolve ε_number_sub_𝐎𝐍 : core.

(* ε数无界 *)
Lemma ε_number_unbounded : unbounded ε_number.
Proof. apply fixed_point_class_unbounded, ordExp_normal; nauto. Qed.
Local Hint Resolve ε_number_unbounded : core.

(* ε运算的非构造式定义 *)
Lemma ε_spec : ∀α ⋵ 𝐎𝐍, ∀β ⋵ ε_number, β ∉ {ε x | x ∊ α} → ε α ⋸ β.
Proof. intros α Hα β Hβ. apply enum_spec; auto. Qed.

(* ε运算是对ε数的枚举 *)
Lemma ε_is_ε_number : ε :ᶜ 𝐎𝐍 ⇒ ε_number.
Proof. apply enum_into_class; auto. Qed.
Local Hint Resolve ε_is_ε_number : core.

(* ε运算是序数运算 *)
Lemma ε_operative : ε :ᶜ 𝐎𝐍 ⇒ 𝐎𝐍.
Proof. intros. apply enum_operative; auto. Qed.
Local Hint Resolve ε_operative : core.

(* ε运算在0处的值 *)
Theorem ε_0 : ε 0 = ε₀.
Proof with auto.
  ord_ext...
  - apply ε_spec... apply ε₀_is_ε_number.
    intros H. apply ReplAx in H as [x [Hx _]]. exfalso0.
  - apply ε₀_is_the_least_ε_number...
Qed.

(* ε运算单调 *)
Theorem ε_monotone : monotone ε.
Proof. apply enum_monotone; auto. Qed.

(* ε运算具有单射性 *)
Theorem ε_injective : class_injective ε 𝐎𝐍.
Proof. apply enum_injective; auto. Qed.

(* ε数都被ε运算枚举 *)
Theorem ε_surjective : class_surjective ε 𝐎𝐍 ε_number.
Proof. apply enum_surjective; auto. Qed.

(* ε运算等价于ε数 *)
Theorem ε_iff_ε_number :
  ∀ ξ, ξ ⋵ ε_number ↔ ∃ α, α ⋵ 𝐎𝐍 ∧ ε α = ξ.
Proof. apply enum_iff_class; auto. Qed.

(* ε是规范运算 *)
Theorem ε_normal : normal ε.
Proof. apply fixedPoint_normal, ordExp_normal; nauto. Qed.

(* ε在极限处连续 *)
Theorem ε_limit : continuous ε.
Proof. apply ε_normal. Qed.

(* ε数对取序列上界封闭 *)
Theorem ε_closed : closed ε_number.
Proof with auto.
  eapply normal_operation_range_closed...
  apply enum_onto_class... apply ε_normal.
Qed.

(* ε运算的值满足ε不动点性质 *)
Lemma epsilon : ∀α ⋵ 𝐎𝐍, ξ ^ ε α = ε α.
Proof. apply fixedPoint, ordExp_normal; nauto. Qed.

(* ε数大于ξ *)
Lemma ε_has_ξ : ∀α ⋵ 𝐎𝐍, ξ ∈ ε α.
Proof with auto.
  ord_induction. intros α Hα IH.
  ord_destruct α.
  - subst. rewrite ε_0. apply ε₀_has_tower_0.
  - destruct Hsuc as [β [Hβ H]]. subst.
    eapply (ord_trans _ _ _ (ε β))... apply ε_normal...
  - apply EmptyNE in H0 as [β Hβ].
    eapply (ord_trans _ _ _ (ε β))... apply ε_normal...
  Unshelve. 1-2:auto.
Qed.

(* ε数不小于ω *)
Lemma ε_ge_ω : ∀α ⋵ 𝐎𝐍, ω ⋸ ε α.
Proof with nauto.
  ord_induction. intros α Hα IH.
  ord_destruct α.
  - subst. rewrite ε_0. rewrite ε₀_normal_form.
    destruct (classic (ξ ∈ ω)).
    + rewrite ordTetL_n_ω...
    + apply ord_le_iff_not_gt in H... left.
      rewrite ordTetL_limit... apply (FUnionI _ _ 1)...
      rewrite ordTetL_1_r... eapply ord_trans_le_lt. auto.
      apply H. apply ordExp_enlarge_r...
  - destruct Hsuc as [β [Hβ H]]. subst.
    eapply (ord_trans_le _ (ε β))... left. apply ε_normal...
  - apply EmptyNE in H0 as [β Hβ].
    eapply (ord_trans_le _ (ε β))... left. apply ε_normal...
Qed.

(** 高阶运算的不动点同时也是低阶运算的不动点 **)

(* ε数也是ω乘法的不动点 *)
Fact epsilon_mul : ∀α ⋵ 𝐎𝐍, ξ ⋅ ε α = ε α.
Proof with neauto.
  intros α Hα. rewrite <- epsilon at 1...
  rewrite <- (ordExp_1_r ξ) at 1...
  rewrite ordExp_add, ordAdd_1_absorption...
  apply epsilon... eapply ord_trans_le. auto. apply (ε_ge_ω 0)...
  destruct (classic (α = 0)). subst...
  left. apply ε_normal...
Qed.

(* ε数也是ω加法的不动点 *)
Fact epsilon_add : ∀α ⋵ 𝐎𝐍, ξ + ε α = ε α.
Proof with neauto.
  intros α Hα. rewrite <- epsilon_mul at 1...
  rewrite <- (ordMul_1_r ξ) at 1...
  rewrite <- ordMul_distr, ordAdd_1_absorption...
  apply epsilon_mul... eapply ord_trans_le. auto. apply (ε_ge_ω 0)...
  destruct (classic (α = 0)). subst...
  left. apply ε_normal...
Qed.

(* ε数大于自然数 *)
Lemma ε_has_n : ∀α ⋵ 𝐎𝐍, ∀n ∈ ω, n ∈ ε α.
Proof.
  intros α Hα n Hn.
  eapply ord_trans_lt_le; eauto. now apply ε_ge_ω.
Qed.
Local Hint Resolve ε_has_n : core.

(* ε数不等于0 *)
Lemma ε_neq_0 : ∀α ⋵ 𝐎𝐍, ε α ≠ 0.
Proof.
  intros α Hα. eapply EmptyNI. exists 0.
  eapply ord_trans_lt_le. auto.
  apply embed_ran. now apply ε_ge_ω.
Qed.
Local Hint Resolve ε_neq_0 : core.

(* ε数是极限序数 *)
Lemma ε_is_limord : ε :ᶜ 𝐎𝐍 ⇒ 𝐎𝐍ˡⁱᵐ.
Proof with neauto.
  intros α Hα. apply fixed_point_is_limord...
  apply ordExp_normal... intros β Hβ Heq.
  replace (FixedPoint (OrdExp ξ)) with ε in Heq...
  pose proof (epsilon β⁺ (ord_suc_is_ord β Hβ)).
  rewrite Heq, ordExp_suc, epsilon in H...
  eapply (ord_irrefl (ε β ⋅ ξ))...
  rewrite H at 1. rewrite <- ordAdd_1_r...
  eapply ord_trans_lt_le. auto.
  apply ordAdd_preserve_lt; revgoals.
  apply ε_has_n... 1-3:nauto. rewrite <- ordMul_2_r...
  apply ordMul_preserve_le_r... apply ord_suc_correct...
Qed.
Local Hint Resolve ε_is_limord : core.

(** ε指数塔 **)

(* ε塔是序数 *)
Lemma ε_tower_ran : ∀ α β ⋵ 𝐎𝐍, ε α ^^ᴸ β ⋵ 𝐎𝐍.
Proof. auto. Qed.
Local Hint Resolve ε_tower_ran : core.

(* 有限层ε塔不小于ω *)
Lemma ε_tower_n_ge_ω : ∀α ⋵ 𝐎𝐍, ∀n ∈ ω, ω ⋸ ε α ^^ᴸ n.
Proof with nauto.
  intros α Hα n Hn. ω_induction n.
  - rewrite ordTetL_0... apply ε_ge_ω...
  - eapply ord_trans_le. auto. apply IH. left.
    apply ordTetL_n_ascending...
Qed.
Local Hint Resolve ε_tower_n_ge_ω : core.

(* 有限层ε塔大于自然数 *)
Lemma ε_tower_n_has_n : ∀α ⋵ 𝐎𝐍, ∀ m n ∈ ω, m ∈ ε α ^^ᴸ n.
Proof. intros α Hα m Hm n Hn. eapply ord_trans_lt_le; eauto. Qed.
Local Hint Resolve ε_tower_n_has_n : core.

(* εtω定义为有限层ε塔上界 *)
Definition εtω := λ α, sup {ε α ^^ᴸ n | n ∊ ω}.

(* εtω是ω层ε塔 *)
Remark εtω_normal_form : ∀α ⋵ 𝐎𝐍, εtω α = ε α ^^ᴸ ω.
Proof. intros α Hα. symmetry. apply ordTetL_limit; nauto. Qed.

(* 有限层ε塔上界是极限序数 *)
Lemma εtω_is_limord : εtω :ᶜ 𝐎𝐍 ⇒ 𝐎𝐍ˡⁱᵐ.
Proof with auto.
  intros α Hα. apply union_of_limords_is_limord.
  intros x Hx. apply ReplAx in Hx as [n [Hn Hx]]. subst.
  apply ordTetL_is_limord_l...
Qed.
Local Hint Resolve εtω_is_limord : core.

(* 有限层ε塔上界是序数 *)
Corollary εtω_ran : εtω :ᶜ 𝐎𝐍 ⇒ 𝐎𝐍.
Proof. apply εtω_is_limord. Qed.
Local Hint Resolve εtω_ran : core.

(* 有限层ε塔上界不等于0 *)
Lemma εtω_neq_0 : ∀α ⋵ 𝐎𝐍, εtω α ≠ 0.
Proof with nauto.
  intros α Hα. eapply EmptyNI. exists 0.
  apply (FUnionI _ _ 0)...
Qed.
Local Hint Resolve εtω_neq_0 : core.

(* ε幂相乘的吸收律 *)
Lemma ε_pow_mul_absorption :
  ∀ α β ⋵ 𝐎𝐍, ∀n ∈ ω, ω ⋸ β → ε α ^ n ⋅ ε α ^ β = ε α ^ β.
Proof with auto.
  intros α Hα β Hβ n Hn Hωβ.
  rewrite <- epsilon, ordExp_mul, ordExp_mul, ordExp_add...
  f_equal. rewrite <- ordMul_distr... f_equal.
  apply ordAdd_n_absorption...
Qed.

(* 有限层ε塔上界是ε数 *)
Theorem εtω_is_ε_number : ∀α ⋵ 𝐎𝐍, εtω α ⋵ ε_number.
Proof with neauto.
  intros α Hα. split... ext.
  - rewrite ordExp_limit in H...
    apply FUnionE in H as [β [Hβ Hx]].
    apply FUnionE in Hβ as [n [Hn Hβ]].
    apply (FUnionI _ _ n⁺)... apply ω_inductive...
    rewrite ordTetL_suc... eapply ord_trans... auto.
    assert (Hoβ: β ⋵ 𝐎𝐍). eapply ord_is_ords; revgoals...
    eapply ord_trans_le_lt. auto.
    apply ordExp_preserve_le_l; revgoals.
    left. apply ε_has_ξ. apply Hα. 1-3:auto.
    apply ordExp_preserve_lt...
  - apply FUnionE in H as [n [Hn Hx]].
    rewrite ordExp_limit... eapply FUnionI.
    eapply FUnionI. apply ω_inductive, Hn. apply ordTetL_n_ascending...
    generalize dependent Hx. generalize dependent x.
    apply ord_le_iff_sub...
    ω_induction n.
    + rewrite ordTetL_0 in *... rewrite epsilon...
    + rewrite ordTetL_suc in *...
      rewrite <- (epsilon α) at 1 5... rewrite ordExp_mul...
      apply ordExp_preserve_le_r...
      rewrite <- (epsilon α) at 3 7... rewrite ordExp_mul...
      eapply ordMul_preserve_le_r in IH.
      4: apply (ε_is_limord α)... 2-3:auto.
      rewrite <- (epsilon α) in IH at 3 7...
      rewrite ordExp_add in IH...
      ω_destruct m.
      * rewrite ordTetL_0 in *...
        eapply ord_trans_le. auto. apply IH.
        apply ordExp_preserve_le_r... left.
        rewrite <- ordMul_2_r... apply ordMul_preserve_lt...
      * cut (ε α + ε α ^^ᴸ m⁺ = ε α ⋅ ε α ^^ᴸ m⁺). congruence.
        rewrite ordTetL_suc...
        rewrite <- (ordAdd_1_absorption (ε α ^^ᴸ m)) at 1...
        rewrite <- ordExp_add, ordExp_1_r...
        rewrite <- (ordMul_1_r (ε α)) at 1...
        rewrite <- ordMul_distr, ordAdd_1_absorption...
        eapply ord_trans_le. auto. apply (ε_ge_ω α)...
        left. apply ordExp_enlarge_r...
Qed.

(* ε数的后继不是ε数 *)
Lemma suc_ε_is_not_ε_number : ∀α ⋵ 𝐎𝐍, ¬ (ε α)⁺ ⋵ ε_number.
Proof with nauto.
  intros α Hα [Hε H].
  rewrite ordExp_suc, epsilon, <- ordAdd_1_r in H...
  eapply ord_not_lt_self. 3: symmetry in H; apply H. 1-2: nauto.
  eapply ord_trans_lt_le. auto. apply ordAdd_preserve_lt; revgoals.
  apply ε_has_n. apply Hα. 1-4: nauto. rewrite <- ordMul_2_r...
  apply ordMul_preserve_le_r... apply ord_suc_correct...
Qed.

(* ε数的后继小于后继ε数 *)
Lemma suc_ε_lt_ε_suc : ∀α ⋵ 𝐎𝐍, (ε α)⁺ ∈ ε α⁺.
Proof with eauto.
  intros α Hα. contra.
  apply ord_le_iff_not_gt in H as []...
  - apply ord_le_iff_lt_suc, ord_le_iff_not_gt in H...
    apply H, ε_normal...
  - eapply suc_ε_is_not_ε_number...
    rewrite <- H. apply ε_is_ε_number...
Qed.

(* ε数的两倍小于后继ε数 *)
Lemma ε_double_lt_ε_suc : ∀α ⋵ 𝐎𝐍, ε α + ε α ∈ ε α⁺.
Proof with neauto.
  intros α Hα.
  rewrite <- epsilon, <- (epsilon α⁺), <- ordMul_2_r...
  eapply ord_trans_le_lt. auto.
  eapply (ordMul_preserve_le_r _ _ ξ)... apply ord_suc_correct...
  rewrite <- (ordExp_1_r ξ) at 2...
  rewrite ordExp_add, ordAdd_1_r...
  apply ordExp_preserve_lt, suc_ε_lt_ε_suc...
  Unshelve. nauto.
Qed.

(* ε数的平方小于后继ε数 *)
Lemma ε_square_lt_ε_suc : ∀α ⋵ 𝐎𝐍, ε α ⋅ ε α ∈ ε α⁺.
Proof with neauto.
  intros α Hα.
  rewrite <- epsilon, ordExp_add, <- (epsilon α⁺)...
  apply ordExp_preserve_lt, ε_double_lt_ε_suc...
Qed.

(* ε运算在后继序数处的值 *)
Theorem ε_suc : ∀α ⋵ 𝐎𝐍, ε α⁺ = ε α ^^ᴸ ω.
Proof with neauto.
  intros α Hα. rewrite <- εtω_normal_form... ord_ext...
  - apply ε_spec... apply εtω_is_ε_number...
    intros H. apply ReplAx in H as [x [Hx H]].
    assert (Hox: x ⋵ 𝐎𝐍). apply (ord_is_ords α⁺)...
    cut (ε x ∈ εtω α). intros C. eapply ord_not_lt_self; revgoals...
    apply (FUnionI _ _ 1)... rewrite (pred 1), ordTetL_suc, ordTetL_0...
    eapply ord_trans_le_lt. auto. 2: apply ordExp_enlarge_r...
    apply ord_le_iff_lt_suc in Hx as []...
    left. apply ε_normal... right. congruence.
  - apply ord_le_iff_sub... intros x Hx.
    apply FUnionE in Hx as [n [Hn Hx]].
    eapply ord_trans... clear Hx.
    ω_destruct n. {
      rewrite ordTetL_0... apply ε_normal...
    }
    rewrite ordTetL_suc... rewrite <- epsilon at 1...
    rewrite <- (epsilon α⁺), ordExp_mul...
    apply ordExp_preserve_lt...
    ω_destruct n. {
      rewrite ordTetL_0... apply ε_square_lt_ε_suc...
    }
    rewrite ordTetL_suc... rewrite <- epsilon at 1 2...
    rewrite <- (epsilon α⁺), ordExp_mul, ordExp_add...
    apply ordExp_preserve_lt... apply ordAdd_ran, ordMul_ran...
    ω_induction n.
    + rewrite ordTetL_0... rewrite <- (ordMul_1_r (ε α)) at 1...
      rewrite <- ordMul_distr, ordAdd_1_absorption...
      apply ε_square_lt_ε_suc... apply ε_ge_ω...
    + rewrite ordTetL_suc...
      rewrite <- (ordMul_1_r (ε α)) at 1...
      rewrite <- ordMul_distr, ordAdd_1_absorption...
      rewrite <- epsilon at 1 2...
      rewrite <- (epsilon α⁺), ordExp_mul, ordExp_add...
      apply ordExp_preserve_lt... apply ordAdd_ran...
      eapply ord_trans_le. auto. apply (ε_ge_ω α)...
      left. apply ordExp_enlarge_r...
Qed.

End OrdExpFixedPoint.
