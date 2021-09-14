(** Coq coding by choukh, Sep 2021 **)

Require ZFC.Lib.OrdinalCountability.
Require Import ZFC.Elements.EST8_8.
Export OrdinalClass 𝐎𝐍Separation VeblenFixedPoint.

Local Hint Resolve
  ordAdd_ran ordMul_ran ordExp_ran ordTetL_ran : core.

(** ω指数塔 **)

(* 0层塔 *)
Lemma ω_tower_0 : ω ^^ᴸ 0 = ω.
Proof. apply ordTetL_0; auto. Qed.

(* 后继层塔 *)
Lemma ω_tower_suc : ∀α ⋵ 𝐎𝐍, ω ^^ᴸ α⁺ = ω ^ (ω ^^ᴸ α).
Proof. apply ordTetL_suc; auto. Qed.

(* 1层塔 *)
Fact ω_tower_1 : ω ^^ᴸ 1 = ω ^ ω.
Proof. rewrite pred, ω_tower_suc, ω_tower_0; auto. Qed.

(* 极限层塔 *)
Lemma ω_tower_limit : continuous (OrdTetL ω).
Proof. apply ordTetL_limit; auto. Qed.

(* ω塔是序数 *)
Lemma ω_tower_ran : ∀α ⋵ 𝐎𝐍, ω ^^ᴸ α ⋵ 𝐎𝐍.
Proof. apply ordTetL_ran; auto. Qed.
Local Hint Resolve ω_tower_ran : core.

(* 有限层塔递增 *)
Lemma ω_tower_n_ascending : ∀n ∈ ω, ω ^^ᴸ n ∈ ω ^^ᴸ n⁺.
Proof with nauto.
  intros n Hn. ω_induction n.
  - rewrite ω_tower_suc, <- zero, ω_tower_0...
    apply ordExp_enlarge_r...
  - rewrite ω_tower_suc, ω_tower_suc...
    apply ordExp_preserve_lt...
Qed.

(* 有限层塔单调 *)
Lemma ω_tower_n_monotone : ∀n ∈ ω, ∀m ∈ n, ω ^^ᴸ m ∈ ω ^^ᴸ n.
Proof with eauto.
  intros n Hn. ω_induction n; intros k Hlt.
  - exfalso0.
  - assert (Hk: k ∈ ω). eapply ω_trans... apply ω_inductive...
    apply le_iff_lt_suc in Hlt as []...
    + eapply ord_trans. auto. apply IH...
      apply ω_tower_n_ascending...
    + subst. apply ω_tower_n_ascending...
Qed.

(* 有限层塔大于等于ω *)
Lemma ω_tower_n_ge_ω : ∀n ∈ ω, ω ⋸ ω ^^ᴸ n.
Proof with auto.
  intros n Hn. ω_destruct n.
  - right. rewrite ordTetL_0...
  - left. rewrite <- ordTetL_0 at 1...
    apply ω_tower_n_monotone... apply suc_has_0...
Qed.

(* 有限层塔不等于任意自然数 *)
Lemma ω_tower_n_neq_nat : ∀ m n ∈ ω, ω ^^ᴸ m ≠ n.
Proof with neauto.
  intros m Hm n Hn Heq.
  apply (ord_irrefl ω)... eapply ord_trans_le_lt. auto.
  apply (ω_tower_n_ge_ω m)... rewrite Heq...
Qed.

(* 有限层塔单射 *)
Lemma ω_tower_n_injective : ∀ m n ∈ ω, ω ^^ᴸ m = ω ^^ᴸ n → m = n.
Proof with neauto.
  intros n Hn. ω_induction n; intros k Hk H.
  - ω_destruct k...
    rewrite ordTetL_0, ordTetL_suc in H...
    rewrite <- ordExp_1_r in H at 1...
    apply ordExp_cancel in H...
    exfalso. apply (ω_tower_n_neq_nat k Hp 1)...
  - ω_destruct k.
    + rewrite ordTetL_suc, ordTetL_0 in H...
      rewrite <- ordExp_1_r in H...
      apply ordExp_cancel in H...
      exfalso. apply (ω_tower_n_neq_nat m Hm 1)...
    + rewrite ordTetL_suc, ordTetL_suc in H...
      apply ordExp_cancel in H...
      apply IH in H... subst...
Qed.

(* ε₀定义为有限层塔序列的上界 *)
Definition ε₀ := sup {ω ^^ᴸ n | n ∊ ω}.

(* ε₀是ω层塔 *)
Remark ε₀_normal_form : ε₀ = ω ^^ᴸ ω.
Proof. symmetry. apply ω_tower_limit; nauto. Qed.

(* ε₀是序数 *)
Lemma ε₀_is_ord : ε₀ ⋵ 𝐎𝐍.
Proof. rewrite ε₀_normal_form; auto. Qed.
Local Hint Resolve ε₀_is_ord : core.

(* ε₀是极限序数 *)
Lemma ε₀_is_limord : ε₀ ⋵ 𝐎𝐍ˡⁱᵐ.
Proof.
  rewrite ε₀_normal_form.
  apply ordTetL_is_limord_l; nauto.
Qed.
Local Hint Resolve ε₀_is_limord : core.

(* ε₀里有0层塔 *)
Fact ε₀_has_tower_0 : ω ∈ ε₀.
Proof with nauto.
  apply (FUnionI _ _ 1)...
  rewrite ω_tower_1. rewrite <- (ordExp_1_r) at 1...
  apply ordExp_preserve_lt...
Qed.

(* ε₀里有任意有限层塔 *)
Lemma ε₀_has_tower_n : ∀n ∈ ω, ω ^^ᴸ n ∈ ε₀.
Proof with nauto.
  intros n Hn. eapply (FUnionI _ _ n⁺)...
  apply ω_inductive... apply ω_tower_n_ascending...
Qed.

(* ε₀里有任意有限层塔里的元素 *)
Lemma ε₀_has_those_of_tower_n : ∀n ∈ ω, ∀α ∈ ω ^^ᴸ n, α ∈ ε₀.
Proof with eauto.
  intros n Hn α Hα. eapply ord_trans...
  apply ε₀_has_tower_n...
Qed.
Local Notation ε₀I := ε₀_has_those_of_tower_n.

(* ε₀的任意元素都在某有限层塔里 *)
Lemma ε₀_has_only_those_of_tower_n : ∀α ∈ ε₀, ∃n ∈ ω, α ∈ ω ^^ᴸ n.
Proof. intros α Hα. apply FUnionE in Hα; auto. Qed.
Local Notation ε₀E := ε₀_has_only_those_of_tower_n.

(* ε₀里有且只有那些有限层塔里的元素 *)
Fact ε₀_iff_of_tower_n : ∀α ⋵ 𝐎𝐍, α ∈ ε₀ ↔ ∃n ∈ ω, α ∈ ω ^^ᴸ n.
Proof. split. apply ε₀E. intros [n [Hn Hα]]. apply (ε₀I n); auto. Qed.

(* ε₀不等于0 *)
Lemma ε₀_neq_0 : ε₀ ≠ 0.
Proof.
  rewrite ε₀_normal_form. intros H.
  apply ordTetL_eq_0 in H; nauto.
Qed.
Local Hint Resolve ε₀_neq_0 : core.

(* ε₀对ω指数运算封闭 *)
Lemma ε₀_closed_under_ω_exp : ∀α ∈ ε₀, ω ^ α ∈ ε₀.
Proof with nauto.
  intros α Hα.
  assert (Hoα: α ⋵ 𝐎𝐍). apply (ord_is_ords ε₀)...
  apply ε₀E in Hα as [n [Hn Hα]].
  apply (ε₀I n⁺). apply ω_inductive...
  rewrite ω_tower_suc... apply ordExp_preserve_lt...
Qed.

(* ε数 *)
Definition ε_number := λ ε, ε ⋵ 𝐎𝐍 ∧ ω ^ ε = ε.

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
  assert (1 ∈ ω)... rewrite Heq in H.
  eapply nat_irrefl...
Qed.

(* 任意ε数都有任意有限层塔 *)
Lemma ε_number_has_tower_n : ∀n ∈ ω, ∀ε ⋵ ε_number, ω ^^ᴸ n ∈ ε.
Proof with neauto.
  intros n Hn. ω_induction n; intros ε [Hε Heq].
  - rewrite <- zero, ω_tower_0, <- Heq.
    apply ordExp_enlarge_r...
    apply ord_neq_0_1_gt_1...
    apply ε_number_neq_0. split...
    apply ε_number_neq_1. split...
  - rewrite ω_tower_suc, <- Heq...
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

(* ex8_28 ε数无界 *)
Lemma ε_number_unbounded : unbounded ε_number.
Proof. apply fixed_point_class_unbounded, ordExp_normal; nauto. Qed.
Local Hint Resolve ε_number_unbounded : core.

(* ε运算的非构造式定义 *)
Lemma ε_spec : ∀α ⋵ 𝐎𝐍, ∀ξ ⋵ ε_number, ξ ∉ {ε x | x ∊ α} → ε α ⋸ ξ.
Proof. intros α Hα ξ Hξ. apply enum_spec; auto. Qed.

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

(* ex8_29 ε数对取序列上界封闭 *)
Theorem ε_closed : closed ε_number.
Proof with auto.
  eapply normal_operation_range_closed...
  apply enum_onto_class... apply ε_normal.
Qed.

(* ε运算的值满足ε不动点性质 *)
Lemma epsilon : ∀α ⋵ 𝐎𝐍, ω ^ ε α = ε α.
Proof. apply fixedPoint, ordExp_normal; nauto. Qed.

(* ε数大于ω *)
Lemma ε_has_ω : ∀α ⋵ 𝐎𝐍, ω ∈ ε α.
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

(** 高阶运算的不动点同时也是低阶运算的不动点 **)

(* ε数也是ω乘法的不动点 *)
Fact epsilon_mul : ∀α ⋵ 𝐎𝐍, ω ⋅ ε α = ε α.
Proof with nauto.
  intros α Hα. rewrite <- epsilon at 1...
  rewrite <- (ordExp_1_r ω) at 1...
  rewrite ordExp_add, ordAdd_1_absorption...
  apply epsilon... left. apply ε_has_ω...
Qed.

(* ε数也是ω加法的不动点 *)
Fact epsilon_add : ∀α ⋵ 𝐎𝐍, ω + ε α = ε α.
Proof with nauto.
  intros α Hα. rewrite <- epsilon_mul at 1...
  rewrite <- (ordMul_1_r ω) at 1...
  rewrite <- ordMul_distr, ordAdd_1_absorption...
  apply epsilon_mul... left. apply ε_has_ω...
Qed.

(* ε数大于自然数 *)
Lemma ε_has_n : ∀α ⋵ 𝐎𝐍, ∀n ∈ ω, n ∈ ε α.
Proof.
  intros α Hα n Hn.
  eapply ord_trans; eauto. now apply ε_has_ω.
Qed.
Local Hint Resolve ε_has_n : core.

(* ε数不等于0 *)
Lemma ε_neq_0 : ∀α ⋵ 𝐎𝐍, ε α ≠ 0.
Proof.
  intros α Hα. eapply EmptyNI. exists ω. now apply ε_has_ω.
Qed.
Local Hint Resolve ε_neq_0 : core.

(* ε数是极限序数 *)
Lemma ε_is_limord : ε :ᶜ 𝐎𝐍 ⇒ 𝐎𝐍ˡⁱᵐ.
Proof with neauto.
  intros α Hα. apply fixed_point_is_limord...
  apply ordExp_normal... intros β Hβ Heq.
  replace (FixedPoint (OrdExp ω)) with ε in Heq...
  pose proof (epsilon β⁺ (ord_suc_is_ord β Hβ)).
  rewrite Heq, ordExp_suc, epsilon in H...
  eapply (ord_irrefl (ε β ⋅ ω))...
  rewrite H at 1. rewrite <- ordAdd_1_r...
  eapply ord_trans. auto. apply ordAdd_preserve_lt; revgoals.
  apply ε_has_n... 1-3:nauto. rewrite <- ordMul_2_r...
  apply ordMul_preserve_lt...
Qed.
Local Hint Resolve ε_is_limord : core.

(** ε指数塔 **)

(* 0层ε塔 *)
Lemma ε_tower_0 : ∀α ⋵ 𝐎𝐍, ε α ^^ᴸ 0 = ε α.
Proof. intros α Hα. apply ordTetL_0; auto. Qed.

(* 后继层ε塔 *)
Lemma ε_tower_suc : ∀ α β ⋵ 𝐎𝐍, ε α ^^ᴸ β⁺ = ε α ^ (ε α ^^ᴸ β).
Proof. intros α Hα. apply ordTetL_suc; auto. Qed.

(* 极限层ε塔 *)
Lemma ε_tower_limit : ∀α ⋵ 𝐎𝐍, continuous (OrdTetL (ε α)).
Proof. intros α Hα. apply ordTetL_limit; auto. Qed.

(* ε塔是序数 *)
Lemma ε_tower_ran : ∀ α β ⋵ 𝐎𝐍, ε α ^^ᴸ β ⋵ 𝐎𝐍.
Proof. auto. Qed.
Local Hint Resolve ε_tower_ran : core.

(* 有限层ε塔递增 *)
Lemma ε_tower_n_ascending : ∀α ⋵ 𝐎𝐍, ∀n ∈ ω, ε α ^^ᴸ n ∈ ε α ^^ᴸ n⁺.
Proof with neauto.
  intros α Hα n Hn. ω_induction n.
  - rewrite ε_tower_suc, <- zero, ε_tower_0... apply ordExp_enlarge_r...
  - rewrite ε_tower_suc, ε_tower_suc... apply ordExp_preserve_lt...
Qed.

(* 有限层ε塔单调 *)
Lemma ε_tower_n_monotone : ∀α ⋵ 𝐎𝐍, ∀n ∈ ω, ∀m ∈ n, ε α ^^ᴸ m ∈ ε α ^^ᴸ n.
Proof with neauto.
  intros α Hα n Hn. ω_induction n; intros k Hlt.
  - exfalso0.
  - assert (Hk: k ∈ ω). eapply ω_trans... apply ω_inductive...
    apply ord_le_iff_lt_suc in Hlt as []...
    + eapply ord_trans. auto. apply IH...
    apply ε_tower_n_ascending...
    + subst. apply ε_tower_n_ascending...
Qed.

(* 有限层ε塔大于ω *)
Lemma ε_tower_n_has_ω : ∀α ⋵ 𝐎𝐍, ∀n ∈ ω, ω ∈ ε α ^^ᴸ n.
Proof with auto.
  intros α Hα n Hn. ω_induction n.
  - rewrite ε_tower_0... apply ε_has_ω...
  - eapply ord_trans. auto. apply IH. apply ε_tower_n_ascending...
Qed.
Local Hint Resolve ε_tower_n_has_ω : core.

(* 有限层ε塔大于自然数 *)
Lemma ε_tower_n_has_n : ∀α ⋵ 𝐎𝐍, ∀ m n ∈ ω, m ∈ ε α ^^ᴸ n.
Proof. intros α Hα m Hm n Hn. eapply ord_trans; eauto. Qed.
Local Hint Resolve ε_tower_n_has_n : core.

(* 有限层ε塔单射 *)
Lemma ε_tower_n_injective : ∀α ⋵ 𝐎𝐍, ∀ m n ∈ ω, ε α ^^ᴸ m = ε α ^^ᴸ n → m = n.
Proof with neauto.
  intros α Hα n Hn. ω_induction n; intros k Hk H.
  - ω_destruct k...
    rewrite ε_tower_0, ε_tower_suc in H...
    rewrite <- ordExp_1_r in H at 1...
    apply ordExp_cancel in H...
    exfalso. apply (ord_irrefl 1)... rewrite H at 2...
  - ω_destruct k.
    + rewrite ε_tower_suc, ε_tower_0 in H...
      rewrite <- ordExp_1_r in H...
      apply ordExp_cancel in H...
      exfalso. apply (ord_irrefl 1)... rewrite <- H at 2...
    + rewrite ε_tower_suc, ε_tower_suc in H...
      apply ordExp_cancel in H...
      apply IH in H... subst...
Qed.

(* εtω定义为有限层ε塔上界 *)
Definition εtω := λ α, sup {ε α ^^ᴸ n | n ∊ ω}.

(* εtω是ω层ε塔 *)
Remark εtω_normal_form : ∀α ⋵ 𝐎𝐍, εtω α = ε α ^^ᴸ ω.
Proof. intros α Hα. symmetry. apply ε_tower_limit; nauto. Qed.

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
Proof.
  intros α Hα. eapply EmptyNI. exists ω.
  apply (FUnionI _ _ 0); nauto.
Qed.
Local Hint Resolve εtω_neq_0 : core.

(* 有限层ε塔上界是ε数 *)
Theorem εtω_is_ε_number : ∀α ⋵ 𝐎𝐍, εtω α ⋵ ε_number.
Proof with neauto.
  intros α Hα. split... ext.
  - rewrite ordExp_limit in H...
    apply FUnionE in H as [β [Hβ Hx]].
    apply FUnionE in Hβ as [n [Hn Hβ]].
    apply (FUnionI _ _ n⁺)... apply ω_inductive...
    rewrite ε_tower_suc... eapply ord_trans... auto.
    assert (Hoβ: β ⋵ 𝐎𝐍). eapply ord_is_ords; revgoals...
    eapply ord_trans_le_lt. auto.
    apply ordExp_preserve_le_l; revgoals.
    left. apply ε_has_ω. apply Hα. 1-3:auto.
    apply ordExp_preserve_lt...
  - apply FUnionE in H as [n [Hn Hx]].
    rewrite ordExp_limit... eapply FUnionI.
    eapply FUnionI. apply ω_inductive, Hn. apply ε_tower_n_ascending...
    generalize dependent Hx. generalize dependent x.
    apply ord_le_iff_sub...
    ω_induction n.
    + rewrite ε_tower_0 in *... rewrite epsilon...
    + rewrite ε_tower_suc in *...
      rewrite <- (epsilon α) at 1 5... rewrite ordExp_mul...
      apply ordExp_preserve_le_r...
      rewrite <- (epsilon α) at 3 7... rewrite ordExp_mul...
      eapply ordMul_preserve_le_r in IH.
      4: apply (ε_is_limord α)... 2-3:auto.
      rewrite <- (epsilon α) in IH at 3 7...
      rewrite ordExp_add in IH...
      ω_destruct m.
      * rewrite ε_tower_0 in *...
        eapply ord_trans_le. auto. apply IH.
        apply ordExp_preserve_le_r... left.
        rewrite <- ordMul_2_r... apply ordMul_preserve_lt...
      * cut (ε α + ε α ^^ᴸ m⁺ = ε α ⋅ ε α ^^ᴸ m⁺). congruence.
        rewrite ε_tower_suc...
        rewrite <- (ordAdd_1_absorption (ε α ^^ᴸ m)) at 1...
        rewrite <- ordExp_add, ordExp_1_r...
        rewrite <- (ordMul_1_r (ε α)) at 1...
        rewrite <- ordMul_distr, ordAdd_1_absorption...
        eapply ord_trans_le. auto. left. apply (ε_has_ω α)...
        left. apply ordExp_enlarge_r...
Qed.

(* ε数的后继不是ε数 *)
Lemma suc_ε_is_not_ε_number : ∀α ⋵ 𝐎𝐍, ¬ (ε α)⁺ ⋵ ε_number.
Proof with nauto.
  intros α Hα [Hε H].
  rewrite ordExp_suc, epsilon, <- ordAdd_1_r in H...
  eapply ord_not_lt_self. 3: symmetry in H; apply H. 1-2: nauto.
  eapply ord_trans. auto. apply ordAdd_preserve_lt; revgoals.
  apply ε_has_n. apply Hα. 1-4: nauto.
  rewrite <- ordMul_2_r... apply ordMul_preserve_lt...
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
  rewrite <- epsilon, <- (epsilon α⁺)...
  eapply ord_trans. auto.
  apply ordAdd_preserve_lt; revgoals.
  apply ordExp_preserve_lt; revgoals. apply suc_has_n. 1-7: nauto.
  rewrite ordAdd_ω_pow_absorption...
  apply ordExp_preserve_lt, suc_ε_lt_ε_suc...
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
    apply (FUnionI _ _ 1)... rewrite (pred 1), ε_tower_suc, ε_tower_0...
    eapply ord_trans_le_lt. auto. 2: apply ordExp_enlarge_r...
    apply ord_le_iff_lt_suc in Hx as []...
    left. apply ε_normal... right. congruence.
  - apply ord_le_iff_sub... intros x Hx.
    apply FUnionE in Hx as [n [Hn Hx]].
    eapply ord_trans... clear Hx.
    ω_destruct n. {
      rewrite ε_tower_0... apply ε_normal...
    }
    rewrite ε_tower_suc... rewrite <- epsilon at 1...
    rewrite <- (epsilon α⁺), ordExp_mul...
    apply ordExp_preserve_lt...
    ω_destruct n. {
      rewrite ε_tower_0... apply ε_square_lt_ε_suc...
    }
    rewrite ε_tower_suc... rewrite <- epsilon at 1 2...
    rewrite <- (epsilon α⁺), ordExp_mul, ordExp_add...
    apply ordExp_preserve_lt... apply ordAdd_ran, ordMul_ran...
    ω_induction n.
    + rewrite ε_tower_0, <- epsilon, ordExp_add, <- (epsilon α⁺)...
      rewrite ordAdd_ω_pow_absorption...
      apply ordExp_preserve_lt, ε_double_lt_ε_suc...
      apply ordAdd_enlarge_r...
    + rewrite ε_tower_suc... rewrite <- epsilon at 1 2 3...
      rewrite <- (epsilon α⁺), ordExp_mul, ordExp_add...
      rewrite ordAdd_ω_pow_absorption.
      2: apply ordAdd_ran, ordMul_ran...
      * apply ordExp_preserve_lt... apply ordAdd_ran, ordMul_ran...
      * apply ordAdd_enlarge_r, ord_gt_0_neq_0...
        eapply ord_trans. auto. apply ε_has_n... apply ordMul_enlarge_r...
Qed.

Module Countability.
Import Choice OrdinalCountability.
Open Scope OrdArith_scope.

(* 有限层塔是可数无穷 *)
Lemma ω_tower_n_cntinf : AC_II → ∀n ∈ ω, |ω ^^ᴸ n| = ℵ₀.
Proof with nauto.
  intros AC2 n Hn. ω_induction n. rewrite ordTetL_0...
  rewrite ordTetL_suc, ordExp_limit...
  2: apply ordTetL_is_limord_l...
  2: apply ω_tower_n_neq_nat...
  apply (add_one_member_to_funion 0). rewrite ordExp_0_r...
  apply countableI1, nat_finite...
  apply countable_union_of_cntinf...
  - exists ω. apply ReplAx.
    exists 1. split. 2: rewrite ordExp_1_r...
    apply SepI. 2: apply SingNI...
    eapply ord_trans_lt_le. auto.
    apply embed_ran. apply ω_tower_n_ge_ω...
  - apply countableI2, eqnum_repl.
    + apply CardAx1. apply remove_one_member_from_cntinf, IH.
    + intros x1 H1 x2 H2 H. apply SepE1 in H1, H2.
      apply ordExp_cancel in H... 1-2: apply (ord_is_ords (ω ^^ᴸ m))...
  - intros A H. apply ReplAx in H as [α [Hα H]]. subst.
    apply SepE in Hα as [Hα Hne]. apply SingNE in Hne.
    assert (Hoα: α ⋵ 𝐎𝐍). apply (ord_is_ords (ω ^^ᴸ m))...
    apply ord_pow_cntinf... eapply dominate_rewrite_r.
    apply CardAx1. apply IH.
    apply dominate_sub. apply ord_lt_iff_psub...
Qed.

(* ε₀是可数无穷 *)
Theorem ε₀_cntinf : AC_II → |ε₀| = ℵ₀.
Proof with nauto.
  intros AC2. apply countable_union_of_cntinf...
  - exists ω. apply ReplAx. exists 0. split... rewrite ordTetL_0...
  - apply countableI2, eqnum_repl. reflexivity.
    apply ω_tower_n_injective.
  - intros A H. apply ReplAx in H as [n [Hn H]]. subst.
    apply ω_tower_n_cntinf...
Qed.

(* 有限层可数ε塔是可数无穷 *)
Lemma ε_tower_n_cntinf : AC_II → ∀α ⋵ 𝐎𝐍, |ε α| = ℵ₀ → ∀n ∈ ω, |ε α ^^ᴸ n| = ℵ₀.
Proof with neauto.
  intros AC2 α Hα Hcinf n Hn.
  ω_induction n.
  - rewrite ε_tower_0...
  - rewrite ε_tower_suc, ordExp_limit...
    2: apply ordTetL_is_limord_l...
    2: apply ord_gt_0_neq_0...
    apply (add_one_member_to_funion 0). rewrite ordExp_0_r...
    apply countableI1, nat_finite...
    apply countable_union_of_cntinf...
    + exists (ε α). apply ReplAx. exists 1. split...
      apply SepI... apply SingNI... apply ordExp_1_r...
    + apply countableI2, eqnum_repl.
      apply CardAx1, remove_one_member_from_cntinf...
      intros x1 H1 x2 H2 H. apply SepE1 in H1, H2.
      apply ordExp_cancel in H...
      1-2: eapply ord_is_ords; revgoals...
    + intros A H. apply ReplAx in H as [β [Hβ H]]. subst.
      apply SepE in Hβ as [Hβ Hne]. apply SingNE in Hne.
      assert (Hoβ: β ⋵ 𝐎𝐍). eapply ord_is_ords; revgoals...
      apply ord_pow_cntinf... eapply dominate_rewrite_r.
      apply CardAx1, IH. apply dominate_sub. apply ord_lt_iff_psub...
Qed.

(* 可数下标的ε数是可数无穷 *)
Theorem ε_number_cntinf : AC_II → ∀α ⋵ 𝐎𝐍, countable α → |ε α| = ℵ₀.
Proof with neauto.
  intros AC2. ord_induction. intros α Hα IH Hcnt.
  ord_destruct α.
  - subst. rewrite ε_0. apply ε₀_cntinf...
  - destruct Hsuc as [β [Hβ H]]. subst.
    rewrite ε_suc, <- εtω_normal_form...
    apply countable_union_of_cntinf...
    + exists (ε β ^^ᴸ 0). eapply ReplI...
    + apply countableI2, eqnum_repl. reflexivity.
      apply ε_tower_n_injective...
    + intros A HA. apply ReplAx in HA as [n [Hn H]]. subst.
      apply ε_tower_n_cntinf... apply IH, ord_cnt_if_suc_cnt...
  - rewrite ε_limit... apply countable_union_of_cntinf...
    + apply EmptyNE in H0 as [β Hβ]. exists (ε β). eapply ReplI...
    + apply countableI2, eqnum_repl.
      * apply countable_limit_ordinal_cntinf...
      * intros x1 H1 x2 H2. apply ε_injective.
        1-2: eapply ord_is_ords; revgoals...
    + intros A HA. apply ReplAx in HA as [β [Hβ H]]. subst.
      apply IH... eapply dominate_rewrite_r.
      apply countable_limit_ordinal_cntinf...
      apply dominate_sub. apply ord_le_iff_sub... eapply ord_is_ords...
Qed.

End Countability.
