(** Coq coding by choukh, Sep 2021 **)

Require Import ZFC.Elements.EST8_7.
Export OrdinalClass 𝐎𝐍Separation VeblenFixedPoint.

Local Hint Resolve enum_operative ordAdd_ran ordMul_ran ordExp_ran : core.

(* 加法不动点 *)
Section OrdAddFixedPoint.
Variable ξ : set.
Variable ξ_is_ord : ξ ⋵ 𝐎𝐍.
Local Hint Resolve ξ_is_ord : core.

Definition σ₀ := sup {ξ ⋅ n | n ∊ ω}.

Remark σ₀_normal_form : σ₀ = ξ ⋅ ω.
Proof. symmetry. apply ordMul_limit; nauto. Qed.

Lemma σ₀_is_ord : σ₀ ⋵ 𝐎𝐍.
Proof. rewrite σ₀_normal_form; auto. Qed.
Local Hint Resolve σ₀_is_ord : core.

Lemma σ₀_is_limord : σ₀ ⋵ 𝐎𝐍ˡⁱᵐ.
Proof with nauto.
  rewrite σ₀_normal_form.
  destruct (classic (ξ = 0)).
  - subst. rewrite ordMul_0_l... apply empty_is_limord.
  - apply ord_prd_is_limord_r...
Qed.
Local Hint Resolve σ₀_is_limord : core.

Lemma σ₀_has_mul_n : ξ ≠ 0 → ∀n ∈ ω, ξ ⋅ n ∈ σ₀.
Proof with nauto.
  intros Hξ0 n Hn. eapply (FUnionI _ _ n⁺)...
  apply ω_inductive... apply ordMul_normal...
Qed.

Lemma σ₀_has_those_of_mul_n : ξ ≠ 0 → ∀n ∈ ω, ∀α ∈ ξ ⋅ n, α ∈ σ₀.
Proof with eauto.
  intros Hξ0 n Hn α Hα. eapply ord_trans...
  apply σ₀_has_mul_n...
Qed.
Local Notation σ₀I := σ₀_has_those_of_mul_n.

Lemma σ₀_has_only_those_of_mul_n : ∀α ∈ σ₀, ∃n ∈ ω, α ∈ ξ ⋅ n.
Proof. intros α Hα. apply FUnionE in Hα; auto. Qed.
Local Notation σ₀E := σ₀_has_only_those_of_mul_n.

Fact σ₀_iff_of_mul_n : ξ ≠ 0 → ∀α ⋵ 𝐎𝐍, α ∈ σ₀ ↔ ∃n ∈ ω, α ∈ ξ ⋅ n.
Proof. split. apply σ₀E. intros [n [Hn Hα]]. apply (σ₀I H n); auto. Qed.

Lemma σ₀_neq_0 : ξ ≠ 0 → σ₀ ≠ 0.
Proof.
  intros Hξ0 H. rewrite σ₀_normal_form in H.
  apply ord_prd_eq_0 in H as []; nauto.
Qed.
Local Hint Resolve σ₀_neq_0 : core.

Lemma σ₀_closed_under_add : ξ ≠ 0 → ∀α ∈ σ₀, ξ + α ∈ σ₀.
Proof with neauto.
  intros Hξ0 α Hα.
  assert (Hoα: α ⋵ 𝐎𝐍). apply (ord_is_ords σ₀)...
  apply σ₀E in Hα as [n [Hn Hα]].
  apply (σ₀I Hξ0 n⁺). apply ω_inductive...
  eapply ord_trans_lt_le. auto.
  apply ordAdd_preserve_lt; revgoals...
  rewrite ordMul_suc... right. apply ordAdd_arbitrary_assoc...
Qed.

Definition σ := FixedPoint (OrdAdd ξ).
Definition σ_number := fixed_point (OrdAdd ξ).

Lemma σ₀_is_σ_number : σ₀ ⋵ σ_number.
Proof with neauto.
  split...
  destruct (classic (ξ = 0)) as [|H0]. rewrite H, ordAdd_0_l...
  ext.
  - rewrite ordAdd_limit in H...
    apply FUnionE in H as [α [Hα Hx]]. eapply ord_trans...
    apply σ₀_closed_under_add...
  - rewrite ordAdd_limit... eapply FUnionI...
    apply σ₀E in H as [n [Hn Hx]].
    eapply ordAdd_left_enlarge...
Qed.

Lemma σ_number_has_mul_n : ξ ≠ 0 → ∀n ∈ ω, ∀σ ⋵ σ_number, ξ ⋅ n ∈ σ.
Proof with neauto.
  intros Hξ0 n Hn. ω_induction n; intros σ [Hσ Heq].
  - rewrite ordMul_0_r, <- Heq...
    apply ord_neq_0_gt_0...
    intros H. apply ord_sum_eq_0 in H as []...
  - rewrite ordMul_suc, <- Heq, <- ordAdd_arbitrary_assoc...
    apply ordAdd_preserve_lt... apply IH. split...
Qed.

Lemma σ₀_is_the_least_σ_number : ∀α ⋵ σ_number, σ₀ ⋸ α.
Proof with eauto.
  intros σ [Hσ Heq]. apply ord_le_iff_sub...
  intros x Hx. apply σ₀E in Hx as [n [Hn Hx]].
  destruct (classic (ξ = 0)).
  - subst. rewrite ordMul_0_l in Hx... exfalso0.
  - eapply ord_trans... apply σ_number_has_mul_n... split...
Qed.

Lemma σ_number_sub_𝐎𝐍 : σ_number ⫃ 𝐎𝐍.
Proof. intros α []; auto. Qed.
Local Hint Resolve σ_number_sub_𝐎𝐍 : core.

Lemma σ_number_unbounded : unbounded σ_number.
Proof. apply fixed_point_class_unbounded, ordAdd_normal; nauto. Qed.
Local Hint Resolve σ_number_unbounded : core.

Lemma σ_spec : ∀α ⋵ 𝐎𝐍, ∀β ⋵ σ_number, β ∉ {σ x | x ∊ α} → σ α ⋸ β.
Proof. intros α Hα β Hβ. apply enum_spec; auto. Qed.

Lemma σ_is_σ_number : σ :ᶜ 𝐎𝐍 ⇒ σ_number.
Proof. apply enum_into_class; auto. Qed.
Local Hint Resolve σ_is_σ_number : core.

Lemma σ_operative : σ :ᶜ 𝐎𝐍 ⇒ 𝐎𝐍.
Proof. intros. apply enum_operative; auto. Qed.
Local Hint Resolve σ_operative : core.

Theorem σ_0 : σ 0 = σ₀.
Proof with auto.
  ord_ext...
  - apply σ_spec... apply σ₀_is_σ_number.
    intros H. apply ReplAx in H as [x [Hx _]]. exfalso0.
  - apply σ₀_is_the_least_σ_number...
Qed.

Theorem σ_monotone : monotone σ.
Proof. apply enum_monotone; auto. Qed.

Theorem σ_injective : class_injective σ 𝐎𝐍.
Proof. apply enum_injective; auto. Qed.

Theorem σ_surjective : class_surjective σ 𝐎𝐍 σ_number.
Proof. apply enum_surjective; auto. Qed.

Theorem σ_iff_σ_number :
  ∀ ξ, ξ ⋵ σ_number ↔ ∃ α, α ⋵ 𝐎𝐍 ∧ σ α = ξ.
Proof. apply enum_iff_class; auto. Qed.

Theorem σ_normal : normal σ.
Proof. apply fixedPoint_normal, ordAdd_normal; nauto. Qed.

Theorem σ_limit : continuous σ.
Proof. apply σ_normal. Qed.

Theorem σ_closed : closed σ_number.
Proof with auto.
  eapply normal_operation_range_closed...
  apply enum_onto_class... apply σ_normal.
Qed.

Lemma sigma : ∀α ⋵ 𝐎𝐍, ξ + σ α = σ α.
Proof. apply fixedPoint, ordAdd_normal; nauto. Qed.

Theorem σ_suc : ∀α ⋵ 𝐎𝐍, σ α⁺ = (σ α)⁺.
Proof with neauto.
  intros α Hα. ord_ext...
  - apply σ_spec...
    + split... rewrite <- ordAdd_1_r, <- ordAdd_assoc, sigma...
    + intros H. apply ReplAx in H as [x [Hx H]].
      assert (Hox: x ⋵ 𝐎𝐍). apply (ord_is_ords α⁺)...
      apply ord_le_iff_lt_suc in Hx as []...
      * apply σ_normal in H0... rewrite H in H0.
        apply ord_le_iff_not_gt in H0...
      * subst. apply (ord_irrefl (σ α))... rewrite H at 2...
  - apply ord_le_iff_sub... intros x Hx.
    assert (Hox: x ⋵ 𝐎𝐍). apply (ord_is_ords (σ α)⁺)...
    apply ord_le_iff_lt_suc in Hx as []...
    + eapply ord_trans... apply σ_normal...
    + subst. apply σ_normal...
Qed.

Theorem σ_normal_form : ∀α ⋵ 𝐎𝐍, σ α = ξ ⋅ ω + α.
Proof with eauto.
  ord_induction. intros α Hα IH.
  ord_destruct α.
  - subst. rewrite σ_0, σ₀_normal_form, ordAdd_0_r...
  - destruct Hsuc as [β [Hβ H]]. subst.
    rewrite σ_suc, ordAdd_suc... f_equal...
  - rewrite σ_limit, ordAdd_limit... ext.
    + apply FUnionE in H as [β [Hβ H]].
      eapply FUnionI... rewrite <- IH...
    + apply FUnionE in H as [β [Hβ H]].
      eapply FUnionI... rewrite IH...
Qed.

End OrdAddFixedPoint.

(* 乘法不动点 *)
Section OrdMulFixedPoint.
Variable ξ : set.
Variable ξ_is_ord : ξ ⋵ 𝐎𝐍.
Variable ξ_neq_0 : ξ ≠ 0.
Local Hint Resolve ξ_is_ord : core.
Local Hint Resolve ξ_neq_0 : core.

Definition μ₀ := 0.
Definition μ₁ := sup {ξ ^ n | n ∊ ω}.

Remark μ₁_normal_form : μ₁ = ξ ^ ω.
Proof. symmetry. apply ordExp_limit; nauto. Qed.

Lemma μ₁_is_ord : μ₁ ⋵ 𝐎𝐍.
Proof. rewrite μ₁_normal_form; auto. Qed.
Local Hint Resolve μ₁_is_ord : core.

Lemma μ₁_is_limord : ξ ≠ 1 → μ₁ ⋵ 𝐎𝐍ˡⁱᵐ.
Proof with nauto.
  intros Hξ1. rewrite μ₁_normal_form.
  apply ord_pow_is_limord_r...
Qed.
Local Hint Resolve μ₁_is_limord : core.

Lemma μ₁_has_exp_n : ξ ≠ 1 → ∀n ∈ ω, ξ ^ n ∈ μ₁.
Proof with nauto.
  intros Hξ1 n Hn. eapply (FUnionI _ _ n⁺)...
  apply ω_inductive... apply ordExp_normal...
Qed.

Lemma μ₁_has_those_of_exp_n : ξ ≠ 1 → ∀n ∈ ω, ∀α ∈ ξ ^ n, α ∈ μ₁.
Proof with eauto.
  intros Hξ1 n Hn α Hα. eapply ord_trans...
  apply μ₁_has_exp_n...
Qed.
Local Notation μ₁I := μ₁_has_those_of_exp_n.

Lemma μ₁_has_only_those_of_exp_n : ∀α ∈ μ₁, ∃n ∈ ω, α ∈ ξ ^ n.
Proof. intros α Hα. apply FUnionE in Hα; auto. Qed.
Local Notation μ₁E := μ₁_has_only_those_of_exp_n.

Fact μ₁_iff_of_exp_n : ξ ≠ 1 → ∀α ⋵ 𝐎𝐍, α ∈ μ₁ ↔ ∃n ∈ ω, α ∈ ξ ^ n.
Proof. split. apply μ₁E. intros [n [Hn Hα]]. apply (μ₁I H n); auto. Qed.

Lemma μ₁_neq_0 : μ₁ ≠ 0.
Proof.
  intros H. rewrite μ₁_normal_form in H.
  apply ord_pow_eq_0 in H; nauto.
Qed.
Local Hint Resolve μ₁_neq_0 : core.

Lemma μ₁_closed_under_mul : ξ ≠ 1 → ∀α ∈ μ₁, ξ ⋅ α ∈ μ₁.
Proof with neauto.
  intros Hξ1 α Hα.
  assert (Hoα: α ⋵ 𝐎𝐍). apply (ord_is_ords μ₁)...
  apply μ₁E in Hα as [n [Hn Hα]].
  apply (μ₁I Hξ1 n⁺). apply ω_inductive...
  eapply ord_trans_lt_le. auto.
  apply ordMul_preserve_lt; revgoals...
  rewrite ordExp_suc... right. apply ordMul_arbitrary_assoc...
Qed.

Definition μ := FixedPoint (OrdMul ξ).
Definition μ_number := fixed_point (OrdMul ξ).

Lemma μ₁_is_μ_number : μ₁ ⋵ μ_number.
Proof with neauto.
  split...
  destruct (classic (ξ = 1)) as [|H1]. rewrite H, ordMul_1_l...
  ext.
  - rewrite ordMul_limit in H...
    apply FUnionE in H as [α [Hα Hx]]. eapply ord_trans...
    apply μ₁_closed_under_mul...
  - destruct (classic (x = 0)).
    + subst. apply ord_neq_0_gt_0...
      intros H0. apply ord_prd_eq_0 in H0 as []...
    + rewrite ordMul_limit... eapply FUnionI...
      apply μ₁E in H as [n [Hn Hx]].
      eapply ordMul_left_enlarge...
Qed.

Lemma μ_number_has_exp_n : ξ ≠ 1 →
  ∀n ∈ ω, ∀μ ⋵ μ_number, μ ≠ μ₀ → ξ ^ n ∈ μ.
Proof with neauto.
  intros Hξ1 n Hn. ω_induction n; intros μ [Hμ Heq] Hμ0.
  - rewrite ordExp_0_r, <- Heq...
    apply ord_neq_0_1_gt_1...
    + intros H. apply ord_prd_eq_0 in H as []...
    + intros H1. assert (Hμ1: μ = 1). congruence.
      rewrite Hμ1 in Heq. rewrite ordMul_1_r in Heq...
  - rewrite ordExp_suc, <- Heq, <- ordMul_arbitrary_assoc...
    apply ordMul_preserve_lt... apply IH... split...
Qed.

Lemma μ₁_is_the_least_nonzero_μ_number : ∀α ⋵ μ_number, α ≠ μ₀ → μ₁ ⋸ α.
Proof with eauto.
  intros μ [Hμ Heq] Hμ0. apply ord_le_iff_sub...
  intros x Hx. apply μ₁E in Hx as [n [Hn Hx]].
  destruct (classic (ξ = 1)).
  - subst. rewrite ordExp_1_l in Hx...
    rewrite one in Hx. apply SingE in Hx. subst...
  - eapply ord_trans... apply μ_number_has_exp_n... split...
Qed.

Lemma μ_number_sub_𝐎𝐍 : μ_number ⫃ 𝐎𝐍.
Proof. intros α []; auto. Qed.
Local Hint Resolve μ_number_sub_𝐎𝐍 : core.

Lemma μ_number_unbounded : unbounded μ_number.
Proof. apply fixed_point_class_unbounded, ordMul_normal; nauto. Qed.
Local Hint Resolve μ_number_unbounded : core.

Lemma μ_spec : ∀α ⋵ 𝐎𝐍, ∀β ⋵ μ_number, β ∉ {μ x | x ∊ α} → μ α ⋸ β.
Proof. intros α Hα β Hβ. apply enum_spec; auto. Qed.

Lemma μ_is_μ_number : μ :ᶜ 𝐎𝐍 ⇒ μ_number.
Proof. apply enum_into_class; auto. Qed.
Local Hint Resolve μ_is_μ_number : core.

Lemma μ_operative : μ :ᶜ 𝐎𝐍 ⇒ 𝐎𝐍.
Proof. intros. apply enum_operative; auto. Qed.
Local Hint Resolve μ_operative : core.

Theorem μ_0 : μ 0 = μ₀.
Proof with auto.
  ord_ext...
  - apply μ_spec... split... rewrite ordMul_0_r...
    intros H. apply ReplAx in H as [x [Hx _]]. exfalso0.
  - apply ord_le_iff_not_gt... intros H. exfalso0.
Qed.

Theorem μ_injective : class_injective μ 𝐎𝐍.
Proof. apply enum_injective; auto. Qed.

Theorem μ_1 : μ 1 = μ₁.
Proof with nauto.
  ord_ext...
  - apply μ_spec... apply μ₁_is_μ_number.
    intros H. apply ReplAx in H as [x [Hx H]].
    rewrite one in Hx. apply SingE in Hx. subst.
    rewrite <- zero, μ_0 in H...
  - apply μ₁_is_the_least_nonzero_μ_number...
    intros H. rewrite <- μ_0 in H.
    apply μ_injective in H...
Qed.

Theorem μ_monotone : monotone μ.
Proof. apply enum_monotone; auto. Qed.

Theorem μ_surjective : class_surjective μ 𝐎𝐍 μ_number.
Proof. apply enum_surjective; auto. Qed.

Theorem μ_iff_μ_number :
  ∀ ξ, ξ ⋵ μ_number ↔ ∃ α, α ⋵ 𝐎𝐍 ∧ μ α = ξ.
Proof. apply enum_iff_class; auto. Qed.

Theorem μ_normal : normal μ.
Proof. apply fixedPoint_normal, ordMul_normal; nauto. Qed.

Theorem μ_limit : continuous μ.
Proof. apply μ_normal. Qed.

Theorem μ_closed : closed μ_number.
Proof with auto.
  eapply normal_operation_range_closed...
  apply enum_onto_class... apply μ_normal.
Qed.

Lemma mu : ∀α ⋵ 𝐎𝐍, ξ ⋅ μ α = μ α.
Proof. apply fixedPoint, ordMul_normal; nauto. Qed.

Lemma μ_is_limord : ξ ≠ 1 → μ :ᶜ 𝐎𝐍 ⇒ 𝐎𝐍ˡⁱᵐ.
Proof with neauto.
  intros Hξ1 α Hα. apply fixed_point_is_limord...
  apply ordMul_normal... intros β Hβ Heq.
  replace (FixedPoint (OrdMul ξ)) with μ in Heq...
  pose proof (mu β⁺ (ord_suc_is_ord β Hβ)).
  rewrite Heq, ordMul_suc, mu, <- ordAdd_1_r in H...
  apply ordAdd_cancel in H...
Qed.
Local Hint Resolve μ_is_limord : core.

Lemma μ_neq_0 : ∀α ⋵ 𝐎𝐍, α ≠ 0 → μ α ≠ 0 .
Proof with nauto.
  intros α Hα Hα0. apply EmptyNI.
  destruct (classic (α = 1)).
  - subst. rewrite μ_1. exists 0.
    apply (FUnionI _ _ 0)... rewrite ordExp_0_r...
  - exists (μ 1). apply μ_normal...
Qed.
Local Hint Resolve μ_neq_0 : core.

Lemma mu_add : ξ ≠ 1 → ∀α ⋵ 𝐎𝐍, α ≠ 0 → ξ + μ α = μ α.
Proof with nauto.
  intros Hξ1 α Hα Hα0. rewrite <- mu...
  rewrite <- (ordMul_1_r ξ) at 1...
  rewrite <- ordMul_distr... f_equal.
  apply ordAdd_1_absorption... apply limord_ge_ω...
Qed.

Theorem μ_suc_trivial : ξ = 1 → ∀α ⋵ 𝐎𝐍, μ α⁺ = (μ α)⁺.
Proof with neauto.
  intros Hξ1 α Hα. ord_ext...
  - apply μ_spec...
    + split... rewrite Hξ1, ordMul_1_l...
    + intros H. apply ReplAx in H as [x [Hx H]].
      assert (Hox: x ⋵ 𝐎𝐍). apply (ord_is_ords α⁺)...
      apply ord_le_iff_lt_suc in Hx as []...
      * apply μ_normal in H0... rewrite H in H0.
        apply ord_le_iff_not_gt in H0...
      * subst. apply (ord_irrefl (μ α))... rewrite H at 2...
  - apply ord_le_iff_sub... intros x Hx.
    assert (Hox: x ⋵ 𝐎𝐍). apply (ord_is_ords (μ α)⁺)...
    apply ord_le_iff_lt_suc in Hx as []...
    + eapply ord_trans... apply μ_normal...
    + subst. apply μ_normal...
Qed.

Theorem μ_suc : ξ ≠ 1 → ∀α ⋵ 𝐎𝐍, α ≠ 0 → μ α⁺ = μ α + μ 1.
Proof with neauto.
  intros Hξ1 α Hα Hα0.
  ord_ext...
  - apply μ_spec...
    + split... rewrite ordMul_distr, mu, mu...
    + intros H. apply ReplAx in H as [x [Hx H]].
      assert (Hox: x ⋵ 𝐎𝐍). apply (ord_is_ords α⁺)...
      apply ord_le_iff_lt_suc in Hx as []...
      * apply μ_normal in H0... rewrite H in H0.
        apply ord_le_iff_not_gt in H0...
        left. apply ordAdd_enlarge...
      * subst. apply (ord_irrefl (μ α))... rewrite H at 2...
        apply ordAdd_enlarge...
  - apply ord_le_iff_sub... intros x Hx.
    rewrite ordAdd_limit, μ_1 in Hx...
    apply FUnionE in Hx as [β [Hβ Hx]].
    apply FUnionE in Hβ as [n [Hn Hβ]].
    eapply ord_trans... eapply ord_trans. auto.
    apply ordAdd_preserve_lt; revgoals...
    eapply (ord_is_ords (ξ ^ n))... clear Hβ Hx x.
    ω_induction n.
    + rewrite ordExp_0_r, ordAdd_1_r...
      apply sucord_in_limord... apply μ_normal...
    + rewrite ordExp_suc, <- mu, <- (mu α⁺)...
      rewrite <- ordMul_arbitrary_assoc, <- ordMul_distr...
      apply ordMul_preserve_lt...
Qed.

Theorem μ_normal_form_trivial : ξ = 1 → ∀α ⋵ 𝐎𝐍, μ α = α.
Proof with eauto.
  intros Hξ1. ord_induction. intros α Hα IH.
  ord_destruct α.
  - subst. rewrite μ_0...
  - destruct Hsuc as [β [Hβ H]]. subst.
    rewrite μ_suc_trivial... f_equal...
  - rewrite μ_limit... ext.
    + apply FUnionE in H as [β [Hβ H]].
      eapply ord_trans... rewrite IH...
    + eapply FUnionI. apply sucord_in_limord...
      rewrite IH... apply sucord_in_limord...
Qed.

Theorem μ_normal_form : ξ ≠ 1 → ∀α ⋵ 𝐎𝐍, α ≠ 0 → μ α = ξ ^ ω ⋅ α.
Proof with eauto.
  intros Hξ1. ord_induction. intros α Hα IH Hα0.
  ord_destruct α.
  - subst. rewrite μ_0, ordMul_0_r...
  - destruct Hsuc as [β [Hβ H]]. subst.
    destruct (classic (β = 0)).
    + subst. replace 0⁺ with (Embed 1)...
      rewrite μ_1, ordMul_1_r, μ₁_normal_form...
    + rewrite μ_suc, ordMul_suc, μ_1, μ₁_normal_form, IH...
  - rewrite μ_limit, ordMul_limit... ext.
    + apply FUnionE in H as [β [Hβ H]].
      destruct (classic (β = 0)).
      * subst. rewrite μ_0 in H. exfalso0.
      * eapply FUnionI... rewrite <- IH...
    + apply FUnionE in H as [β [Hβ H]].
      destruct (classic (β = 0)).
      * subst. rewrite ordMul_0_r in H... exfalso0.
      * eapply FUnionI... rewrite IH...
Qed.

End OrdMulFixedPoint.
