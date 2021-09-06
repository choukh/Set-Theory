(** Coq coding by choukh, Sep 2021 **)

Require Import ZFC.Elements.EST8_7.
Export OrdinalClass 𝐎𝐍Separation VeblenFixedPoint.

Local Hint Resolve enum_operative ordAdd_ran ordMul_ran : core.

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
