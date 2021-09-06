(** Adapted from "Elements of Set Theory" Chapter 8 **)
(** Coq coding by choukh, Aug 2021 **)

Require Export ZFC.Elements.EST8_2.
Import OrdinalClass 𝐎𝐍Operation.

(*** EST第八章7：序数算术（递归定义） ***)

Declare Scope OrdArith_scope.
Delimit Scope OrdArith_scope with oa.
Open Scope OrdArith_scope.

(* 序数加法 *)
Definition OrdAdd := λ α, Operation α Suc.
Notation "α + β" := (OrdAdd α β) : OrdArith_scope.

Theorem ordAdd_0_r : ∀α ⋵ 𝐎𝐍, α + 0 = α.
Proof. intros α H. apply operation_0. Qed.

Theorem ordAdd_suc : ∀ α β ⋵ 𝐎𝐍, α + β⁺ = (α + β)⁺.
Proof. intros α H. apply operation_suc. Qed.

Theorem ordAdd_limit : ∀α ⋵ 𝐎𝐍, continuous (OrdAdd α).
Proof. intros α H 𝜆. apply operation_limit. Qed.

Corollary ordAdd_1_r : ∀α ⋵ 𝐎𝐍, α + 1 = α⁺.
Proof.
  intros α H.
  rewrite pred, ordAdd_suc, ordAdd_0_r; auto.
Qed.

Theorem ordAdd_ran : ∀ α β ⋵ 𝐎𝐍, α + β ⋵ 𝐎𝐍.
Proof. intros α Hα β Hβ. apply operation_operative; auto. Qed.
Local Hint Resolve ordAdd_ran : core.
Local Hint Resolve add_ran : core.

(* 有限序数加法等效于自然数加法 *)
Theorem fin_ordAdd_eq_add : ∀ m n ∈ ω, m + n = (m + n)%ω.
Proof with nauto.
  intros m Hm n Hn. generalize dependent m.
  ω_induction n; intros k Hk.
  - rewrite ordAdd_0_r, add_0_r...
  - rewrite ordAdd_suc, IH, suc, suc, add_assoc...
Qed.

(* 有限序数的和是自然数 *)
Corollary fin_ordAdd_ran : ∀ m n ∈ ω, m + n ∈ ω.
Proof with auto.
  intros m Hm n Hn. rewrite fin_ordAdd_eq_add...
Qed.

Example ordAdd_1_1 : 1 + 1 = 2.
Proof. rewrite pred, ordAdd_suc, ordAdd_0_r; auto. Qed.

Example ordAdd_1_ω : 1 + ω = ω.
Proof with neauto.
  rewrite ordAdd_limit... ext α Hα.
  - apply FUnionE in Hα as [β [Hβ Hα]].
    eapply ω_trans... apply fin_ordAdd_ran...
  - eapply FUnionI... rewrite fin_ordAdd_eq_add, add_comm, <- suc...
Qed.

Example ordAdd_ω_1 : ω + 1 = ω⁺.
Proof. rewrite pred, ordAdd_suc, ordAdd_0_r; auto. Qed.

(* 序数乘法 *)
Definition OrdMul := λ α, Operation 0 (λ ξ, ξ + α).
Notation "α ⋅ β" := (OrdMul α β) : OrdArith_scope.

Theorem ordMul_0_r : ∀α ⋵ 𝐎𝐍, α ⋅ 0 = 0.
Proof. intros α H. apply operation_0. Qed.

Theorem ordMul_suc : ∀ α β ⋵ 𝐎𝐍, α ⋅ β⁺ = (α ⋅ β) + α.
Proof. intros α H. apply operation_suc. Qed.

Theorem ordMul_limit : ∀α ⋵ 𝐎𝐍, continuous (OrdMul α).
Proof. intros α H 𝜆. apply operation_limit. Qed.

Theorem ordMul_ran : ∀ α β ⋵ 𝐎𝐍, α ⋅ β ⋵ 𝐎𝐍.
Proof with auto.
  intros α Hα β Hβ.
  apply operation_operative...
Qed.
Local Hint Resolve ordMul_ran : core.
Local Hint Resolve mul_ran : core.

(* 有限序数乘法等效于自然数乘法 *)
Theorem fin_ordMul_eq_mul : ∀ m n ∈ ω, m ⋅ n = (m ⋅ n)%ω.
Proof with nauto.
  intros m Hm n Hn. generalize dependent m.
  ω_induction n; intros k Hk.
  - rewrite ordMul_0_r, mul_0_r...
  - rewrite ordMul_suc, IH, mul_suc, fin_ordAdd_eq_add, add_comm...
Qed.

(* 有限序数的积是自然数 *)
Corollary fin_ordMul_ran : ∀ m n ∈ ω, m ⋅ n ∈ ω.
Proof with auto.
  intros m Hm n Hn. rewrite fin_ordMul_eq_mul...
Qed.

(* 序数乘方 *)
Definition OrdExp : set → set → set := λ α,
  match (ixm (α = 0)) with
  | inl _ => λ ξ, match (ixm (ξ = 0)) with
    | inl _ => 1
    | inr _ => 0
    end
  | inr _ => Operation 1 (λ ξ, ξ ⋅ α)
  end.
Notation "α ^ β" := (OrdExp α β) : OrdArith_scope.

Theorem ordExp_0_r : ∀α ⋵ 𝐎𝐍, α ^ 0 = 1.
Proof with auto.
  intros α H. unfold OrdExp.
  destruct (ixm (α = 0)).
  - destruct (ixm (Embed 0 = 0))... exfalso...
  - rewrite operation_0...
Qed.

Theorem ordExp_suc : ∀ α β ⋵ 𝐎𝐍, α ^ β⁺ = (α ^ β) ⋅ α.
Proof with neauto.
  intros α Hα β Hβ. unfold OrdExp.
  destruct (ixm (α = 0)).
  - destruct (ixm (β⁺ = 0)).
    + exfalso. eapply suc_neq_0...
    + destruct (ixm (β = 0)); subst; rewrite ordMul_0_r...
  - apply operation_suc...
Qed.

Theorem ordExp_limit : ∀α ⋵ 𝐎𝐍, α ≠ 0 → continuous (OrdExp α).
Proof with nauto.
  intros α Hα Hα0 𝜆 H𝜆 H𝜆0. unfold OrdExp.
  destruct (ixm (α = 0)). exfalso...
  apply operation_limit...
Qed.

Theorem ordExp_ran : ∀ α β ⋵ 𝐎𝐍, α ^ β ⋵ 𝐎𝐍.
Proof with nauto.
  intros α Hα β Hβ. unfold OrdExp.
  destruct (ixm (α = 0)).
  - destruct (ixm (β = 0))...
  - apply operation_operative...
Qed.
Local Hint Resolve ordExp_ran : core.
Local Hint Resolve exp_ran : core.

(* 有限序数乘方等效于自然数乘方 *)
Theorem fin_ordExp_eq_exp : ∀ m n ∈ ω, m ^ n = (m ^ n)%ω.
Proof with nauto.
  intros m Hm n Hn. generalize dependent m.
  ω_induction n; intros k Hk.
  - rewrite ordExp_0_r, exp_0_r...
  - rewrite ordExp_suc, IH, exp_suc, fin_ordMul_eq_mul, mul_comm...
Qed.

(* 有限序数的幂是自然数 *)
Corollary fin_ordExp_ran : ∀ m n ∈ ω, m ^ n ∈ ω.
Proof with auto.
  intros m Hm n Hn. rewrite fin_ordExp_eq_exp...
Qed.

Example ordExp_2_ω : 2 ^ ω = ω.
Proof with neauto.
  rewrite ordExp_limit; nauto; [|apply suc_neq_0].
  ext α Hα.
  - apply FUnionE in Hα as [β [Hβ Hα]].
    eapply ω_trans... apply fin_ordExp_ran...
  - eapply FUnionI... rewrite fin_ordExp_eq_exp...
    apply exp_enlarge_lt... apply BUnionI2...
Qed.

(** 序数算术定律 **)

Theorem ordAdd_0_l : ∀α ⋵ 𝐎𝐍, 0 + α = α.
Proof with eauto.
  ord_induction. intros α Hα IH.
  ord_destruct α.
  - subst. apply ordAdd_0_r...
  - destruct Hsuc as [β [Hβ Heq]]. subst.
    rewrite ordAdd_suc, IH...
  - rewrite ordAdd_limit... ext ξ Hξ.
    + apply FUnionE in Hξ as [β [Hβ Hξ]].
      rewrite IH in Hξ... eapply ord_trans...
    + eapply sucord_in_limord in Hlim...
      eapply FUnionI... rewrite IH...
Qed.

Theorem ordAdd_1_l : ∀α ∈ ω, 1 + α = α⁺.
Proof.
  intros α Hα. rewrite fin_ordAdd_eq_add, add_1_l; nauto.
Qed.

Theorem ordMul_0_l : ∀α ⋵ 𝐎𝐍, 0 ⋅ α = 0.
Proof with nauto.
  ord_induction. intros α Hα IH.
  ord_destruct α.
  - subst. rewrite ordMul_0_r...
  - destruct Hsuc as [β [Hβ Heq]]. subst.
    rewrite ordMul_suc, ordAdd_0_r, IH...
  - rewrite ordMul_limit... ext ξ Hξ.
    + apply FUnionE in Hξ as [β [Hβ Hξ]].
      rewrite IH in Hξ...
    + exfalso0.
Qed.

Theorem ordMul_1_r : ∀α ⋵ 𝐎𝐍, α ⋅ 1 = α.
Proof.
  intros α H.
  rewrite pred, ordMul_suc, ordMul_0_r, ordAdd_0_l; auto.
Qed.

Theorem ordMul_1_l : ∀α ⋵ 𝐎𝐍, 1 ⋅ α = α.
Proof with neauto.
  ord_induction. intros α Hα IH.
  ord_destruct α.
  - subst. apply ordMul_0_r...
  - destruct Hsuc as [β [Hβ Heq]]. subst.
    rewrite ordMul_suc, IH, ordAdd_1_r...
  - rewrite ordMul_limit... ext ξ Hξ.
    + apply FUnionE in Hξ as [β [Hβ Hξ]].
      rewrite IH in Hξ... eapply ord_trans...
    + eapply sucord_in_limord in Hlim...
      eapply FUnionI... rewrite IH...
Qed.

Theorem ordMul_2_r : ∀α ⋵ 𝐎𝐍, α ⋅ 2 = α + α.
Proof. intros α H. rewrite pred, ordMul_suc, ordMul_1_r; nauto. Qed.

Theorem ordExp_0_l : ∀α ⋵ 𝐎𝐍, α ≠ 0 → 0 ^ α = 0.
Proof with nauto.
  ord_induction. intros α Hα IH H0.
  ord_destruct α.
  - subst. exfalso...
  - destruct Hsuc as [β [Hβ Heq]]. subst.
    rewrite ordExp_suc, ordMul_0_r...
  - unfold OrdExp. destruct (ixm (Embed 0 = 0))...
    + destruct (ixm (α = 0))... exfalso...
    + exfalso...
Qed.

Theorem ordExp_1_r : ∀α ⋵ 𝐎𝐍, α ^ 1 = α.
Proof.
  intros α H.
  rewrite pred, ordExp_suc, ordExp_0_r, ordMul_1_l; auto.
Qed.

Theorem ordExp_1_l : ∀α ⋵ 𝐎𝐍, 1 ^ α = 1.
Proof with neauto.
  ord_induction. intros α Hα IH.
  ord_destruct α.
  - subst. rewrite ordExp_0_r...
  - destruct Hsuc as [β [Hβ Heq]]. subst.
    rewrite ordExp_suc, ordMul_1_r, IH...
  - rewrite ordExp_limit... ext ξ Hξ.
    + apply FUnionE in Hξ as [β [Hβ Hξ]].
      rewrite IH in Hξ...
    + rewrite one in Hξ. apply SingE in Hξ. subst.
      eapply FUnionI. apply ord_neq_0_gt_0...
      rewrite ordExp_0_r, pred...
Qed.

Theorem ordExp_2_r : ∀α ⋵ 𝐎𝐍, α ^ 2 = α ⋅ α.
Proof. intros α H. rewrite pred, ordExp_suc, ordExp_1_r; nauto. Qed.

Lemma ord_sum_eq_0 : ∀ α β ⋵ 𝐎𝐍, α + β = 0 → α = 0 ∧ β = 0.
Proof with eauto.
  intros α Hα β Hβ H0.
  ord_destruct α; ord_destruct β; subst...
  - destruct Hsuc as [γ [Hγ Heq]]. subst.
    rewrite ordAdd_suc in H0... exfalso. eapply suc_neq_0...
  - exfalso. rewrite ordAdd_limit in H0...
    apply union_eq_empty in H0 as [].
    + apply repl_eq_empty in H...
    + apply EmptyNE in H2 as [x Hx].
      assert (Hox: x ⋵ 𝐎𝐍). eapply ord_is_ords...
      apply sucord_in_limord in Hx...
      eapply repl_eq_1 in Hx...
      rewrite ordAdd_suc in Hx... eapply suc_neq_0...
  - destruct Hsuc as [γ [Hγ Heq]]. subst.
    rewrite ordAdd_0_r in H0...
  - destruct Hsuc0 as [γ [Hγ Heq]]. subst.
    rewrite ordAdd_suc in H0... exfalso. eapply suc_neq_0...
  - exfalso. rewrite ordAdd_limit in H0...
    apply union_eq_empty in H0 as [].
    + apply repl_eq_empty in H...
    + apply EmptyNE in H1 as [x Hx].
      assert (Hox: x ⋵ 𝐎𝐍). eapply ord_is_ords...
      apply sucord_in_limord in Hx...
      eapply repl_eq_1 in Hx...
      rewrite ordAdd_suc in Hx... eapply suc_neq_0...
  - rewrite ordAdd_0_r in H0...
  - destruct Hsuc as [γ [Hγ Heq]]. subst.
    rewrite ordAdd_suc in H0... exfalso. eapply suc_neq_0...
  - exfalso. rewrite ordAdd_limit in H0...
    apply union_eq_empty in H0 as [].
    + apply repl_eq_empty in H...
    + apply EmptyNE in H2 as [x Hx].
      assert (Hox: x ⋵ 𝐎𝐍). eapply ord_is_ords...
      apply sucord_in_limord in Hx...
      eapply repl_eq_1 in Hx...
      rewrite ordAdd_suc in Hx... eapply suc_neq_0...
Qed.

Lemma ord_prd_eq_0 : ∀ α β ⋵ 𝐎𝐍, α ⋅ β = 0 → α = 0 ∨ β = 0.
Proof with eauto.
  intros α Hα β Hβ. generalize dependent β.
  ord_induction. intros β Hβ IH H0.
  ord_destruct β. subst...
  - destruct Hsuc as [γ [Hγ Heq]]. subst.
    rewrite ordMul_suc in H0...
    apply ord_sum_eq_0 in H0 as []...
  - rewrite ordMul_limit in H0...
    apply union_eq_empty in H0 as [].
    + apply repl_eq_empty in H...
    + apply EmptyNE in H1 as [x Hx].
      assert (Hox: x ⋵ 𝐎𝐍). eapply ord_is_ords...
      apply sucord_in_limord in Hx...
      eapply repl_eq_1 in Hx as H0...
      apply IH in H0 as []...
      exfalso. eapply suc_neq_0...
Qed.

Lemma ord_pow_eq_0 : ∀ α β ⋵ 𝐎𝐍, α ^ β = 0 → α = 0.
Proof with eauto.
  intros α Hα β Hβ. generalize dependent β.
  ord_induction. intros β Hβ IH H0.
  ord_destruct β.
  - subst. rewrite ordExp_0_r in H0...
    exfalso. eapply suc_neq_0...
  - destruct Hsuc as [γ [Hγ Heq]]. subst.
    rewrite ordExp_suc in H0...
    apply ord_prd_eq_0 in H0 as []...
  - unfold OrdExp in H0.
    destruct (ixm (α = 0))...
    rewrite operation_limit in H0...
    apply union_eq_empty in H0 as [].
    + apply repl_eq_empty in H. exfalso...
    + apply EmptyNE in H1 as [γ Hγ].
      assert (Hoγ: γ ⋵ 𝐎𝐍). eapply ord_is_ords...
      apply sucord_in_limord in Hγ...
      eapply repl_eq_1 in Hγ as H0...
      rewrite <- H. symmetry. apply repl_ext.
      intros δ Hδ. unfold OrdExp.
      destruct (ixm (α = 0))... exfalso...
Qed.

Import OrdinalClass.
Local Hint Resolve operation_operative : core.

Theorem ordAdd_normal : ∀α ⋵ 𝐎𝐍, normal (OrdAdd α).
Proof with auto.
  intros α Hα. apply operation_normal...
  intros β Hβ. fold (OrdAdd α β⁺). rewrite ordAdd_suc...
Qed.

Theorem ordMul_normal : ∀α ⋵ 𝐎𝐍, α ≠ 0 → normal (OrdMul α).
Proof with auto.
  intros α Hα Hlt. apply operation_normal...
  intros β Hβ. fold (OrdMul α β). fold (OrdMul α β⁺).
  rewrite ordMul_suc... rewrite <- ordAdd_0_r at 1...
  apply ordAdd_normal... apply ord_neq_0_gt_0...
Qed.

Theorem ordExp_normal : ∀α ⋵ 𝐎𝐍, 1 ∈ α → normal (OrdExp α).
Proof with neauto.
  intros α Hα Hlt. unfold OrdExp.
  destruct (ixm (α = 0)). subst. exfalso0.
  apply operation_normal... intros β Hβ.
  rewrite operation_suc... rewrite <- ordMul_1_r at 1...
  apply ordMul_normal... intros H.
  apply n. eapply ord_pow_eq_0... unfold OrdExp.
  destruct (ixm (α = 0))... exfalso...
Qed.

Fact ord_sum_is_limord : ∀α ⋵ 𝐎𝐍, ∀𝜆 ⋵ 𝐎𝐍ˡⁱᵐ, 𝜆 ≠ 0 → α + 𝜆 ⋵ 𝐎𝐍ˡⁱᵐ.
Proof with auto.
  intros α Hα 𝜆 H𝜆 Hne.
  apply normal_operation_limit_is_limit...
  apply ordAdd_normal...
Qed.

Fact ord_prd_is_limord_r : ∀α ⋵ 𝐎𝐍, ∀𝜆 ⋵ 𝐎𝐍ˡⁱᵐ, α ≠ 0 → 𝜆 ≠ 0 → α ⋅ 𝜆 ⋵ 𝐎𝐍ˡⁱᵐ.
Proof with auto.
  intros α Hα 𝜆 H𝜆 H1 H2.
  apply normal_operation_limit_is_limit...
  apply ordMul_normal...
Qed.

Fact ord_prd_is_limord_l : ∀α ⋵ 𝐎𝐍, ∀𝜆 ⋵ 𝐎𝐍ˡⁱᵐ, α ≠ 0 → 𝜆 ≠ 0 → 𝜆 ⋅ α ⋵ 𝐎𝐍ˡⁱᵐ.
Proof with auto.
  intros α Hα 𝜆 H𝜆 H1 H2.
  assert (Ho𝜆: 𝜆 ⋵ 𝐎𝐍). apply H𝜆.
  ord_destruct α.
  - subst. exfalso...
  - destruct Hsuc as [β [Hβ Heq]]. subst.
    rewrite ordMul_suc... apply ord_sum_is_limord...
  - apply ord_prd_is_limord_r...
Qed.

Fact ord_pow_is_limord_r : ∀α ⋵ 𝐎𝐍, ∀𝜆 ⋵ 𝐎𝐍ˡⁱᵐ, 1 ∈ α → 𝜆 ≠ 0 → α ^ 𝜆 ⋵ 𝐎𝐍ˡⁱᵐ.
Proof with auto.
  intros α Hα 𝜆 H𝜆 H1 H2.
  apply normal_operation_limit_is_limit...
  apply ordExp_normal...
Qed.

Fact ord_pow_is_limord_l : ∀α ⋵ 𝐎𝐍, ∀𝜆 ⋵ 𝐎𝐍ˡⁱᵐ, 1 ∈ α → 𝜆 ≠ 0 → 𝜆 ^ α ⋵ 𝐎𝐍ˡⁱᵐ.
Proof with nauto.
  intros α Hα 𝜆 H𝜆 H1 H2.
  assert (Ho𝜆: 𝜆 ⋵ 𝐎𝐍). apply H𝜆.
  ord_destruct α.
  - subst. exfalso0.
  - destruct Hsuc as [β [Hβ Heq]]. subst.
    rewrite ordExp_suc... apply ord_prd_is_limord_r...
    intros H. apply ord_pow_eq_0 in H...
  - apply ord_pow_is_limord_r...
    apply gt_1_iff_neq_0_1... split... intros H.
    apply (limord_iff_not_sucord 𝜆)... exists 0...
Qed.

(** 不等式 **)
(** Addition, multiplication and exponentiation is
  strictly increasing and continuous in the right argument,
  but the analogous relation does not hold for the left argument. **)

Corollary ordAdd_preserve_lt : ∀ α β γ ⋵ 𝐎𝐍,
  β ∈ γ ↔ α + β ∈ α + γ.
Proof with eauto.
  intros α Hα β Hβ γ Hγ. split; intros H.
  apply ordAdd_normal...
  destruct (classic (β = γ)).
  - subst. exfalso. eapply ord_irrefl; revgoals...
  - apply ord_connected in H0 as []...
    apply (proj1 (ordAdd_normal α Hα)) in H0...
    exfalso. eapply ord_not_lt_gt; revgoals...
Qed.

Corollary ordMul_preserve_lt : ∀ α β γ ⋵ 𝐎𝐍, α ≠ 0 →
  β ∈ γ ↔ α ⋅ β ∈ α ⋅ γ.
Proof with eauto.
  intros α Hα β Hβ γ Hγ H0. split; intros H.
  apply ordMul_normal...
  destruct (classic (β = γ)).
  - subst. exfalso. eapply ord_irrefl; revgoals...
  - apply ord_connected in H1 as []...
    apply (proj1 (ordMul_normal α Hα H0)) in H1...
    exfalso. eapply ord_not_lt_gt; revgoals...
Qed.

Corollary ordExp_preserve_lt : ∀ α β γ ⋵ 𝐎𝐍, 1 ∈ α → 
  β ∈ γ ↔ α ^ β ∈ α ^ γ.
Proof with eauto.
  intros α Hα β Hβ γ Hγ H1. split; intros H.
  apply ordExp_normal...
  destruct (classic (β = γ)).
  - subst. exfalso. eapply ord_irrefl; revgoals...
  - apply ord_connected in H0 as []...
    apply (proj1 (ordExp_normal α Hα H1)) in H0...
    exfalso. eapply ord_not_lt_gt; revgoals...
Qed.

Corollary ordAdd_cancel : ∀ α β γ ⋵ 𝐎𝐍, α + β = α + γ → β = γ.
Proof with eauto.
  intros α Hα β Hβ γ Hγ Heq.
  contra. apply ord_connected in H as [Hlt|Hlt]...
  - assert (α + β ∈ α + γ). apply ordAdd_normal...
    rewrite Heq in H. eapply ord_irrefl; revgoals...
  - assert (α + γ ∈ α + β). apply ordAdd_normal...
    rewrite Heq in H. eapply ord_irrefl; revgoals...
Qed.

Corollary ordMul_cancel : ∀ α β γ ⋵ 𝐎𝐍, α ≠ 0 → α ⋅ β = α ⋅ γ → β = γ.
Proof with eauto.
  intros α Hα β Hβ γ Hγ H0 Heq.
  contra. apply ord_connected in H as [Hlt|Hlt]...
  - assert (α ⋅ β ∈ α ⋅ γ). apply ordMul_normal...
    rewrite Heq in H. eapply ord_irrefl; revgoals...
  - assert (α ⋅ γ ∈ α ⋅ β). apply ordMul_normal...
    rewrite Heq in H. eapply ord_irrefl; revgoals...
Qed.

Corollary ordExp_cancel : ∀ α β γ ⋵ 𝐎𝐍, 1 ∈ α → α ^ β = α ^ γ → β = γ.
Proof with eauto.
  intros α Hα β Hβ γ Hγ H1 Heq.
  contra. apply ord_connected in H as [Hlt|Hlt]...
  - assert (α ^ β ∈ α ^ γ). apply ordExp_normal...
    rewrite Heq in H. eapply ord_irrefl; revgoals...
  - assert (α ^ γ ∈ α ^ β). apply ordExp_normal...
    rewrite Heq in H. eapply ord_irrefl; revgoals...
Qed.

(** Addition, multiplication and exponentiation is
  non-strictly increasing in the both left and right argument. **)

Theorem ordAdd_preserve_le_l : ∀ α β γ ⋵ 𝐎𝐍,
  α ⋸ β → α + γ ⋸ β + γ.
Proof with eauto.
  intros α Hα β Hβ γ Hγ Hle.
  generalize dependent γ.
  ord_induction; intros γ Hγ IH.
  ord_destruct γ.
  - subst. rewrite ordAdd_0_r, ordAdd_0_r...
  - destruct Hsuc as [δ [Hδ Heq]]. subst.
    rewrite ordAdd_suc, ordAdd_suc...
    rewrite <- ord_suc_preserve_le...
  - apply ord_le_iff_sub...
    rewrite ordAdd_limit, ordAdd_limit...
    intros x Hx. apply FUnionE in Hx as [δ [Hδ Hx]].
    assert (Hoδ: δ ⋵ 𝐎𝐍). eapply ord_is_ords...
    eapply FUnionI... apply IH in Hδ as []...
    eapply ord_trans... congruence.
Qed.

Fact ordAdd_preserve_le_r : ∀ α β γ ⋵ 𝐎𝐍,
  α ⋸ β → γ + α ⋸ γ + β.
Proof.
  intros α Hα β Hβ γ Hγ [].
  left. apply ordAdd_preserve_lt; auto.
  right. congruence.
Qed.

Theorem ordMul_preserve_le_l : ∀ α β γ ⋵ 𝐎𝐍,
  α ⋸ β → α ⋅ γ ⋸ β ⋅ γ.
Proof with eauto.
  intros α Hα β Hβ γ Hγ Hle.
  generalize dependent γ.
  ord_induction; intros γ Hγ IH.
  ord_destruct γ.
  - subst. rewrite ordMul_0_r, ordMul_0_r...
  - destruct Hsuc as [δ [Hδ Heq]]. subst.
    rewrite ordMul_suc, ordMul_suc...
    eapply ord_trans_le. auto.
    + apply ordAdd_preserve_le_l; revgoals.
      apply IH... auto. auto. auto.
    + destruct Hle.
      * left. apply ordAdd_normal...
      * right. congruence.
  - apply ord_le_iff_sub...
    rewrite ordMul_limit, ordMul_limit...
    intros x Hx. apply FUnionE in Hx as [δ [Hδ Hx]].
    assert (Hoδ: δ ⋵ 𝐎𝐍). eapply ord_is_ords...
    eapply FUnionI... apply IH in Hδ as []...
    eapply ord_trans... congruence.
Qed.

Fact ordMul_preserve_le_r : ∀ α β γ ⋵ 𝐎𝐍,
  α ⋸ β → γ ⋅ α ⋸ γ ⋅ β.
Proof with auto.
  intros α Hα β Hβ γ Hγ Hle.
  destruct (classic (γ = 0)). {
    subst. rewrite ordMul_0_l, ordMul_0_l...
  }
  destruct Hle.
  left. apply ordMul_preserve_lt...
  right. congruence.
Qed.

Theorem ordExp_preserve_le_l : ∀ α β γ ⋵ 𝐎𝐍,
  α ⋸ β → α ^ γ ⋸ β ^ γ.
Proof with eauto.
  intros α Hα β Hβ γ Hγ Hle.
  generalize dependent γ.
  ord_induction; intros γ Hγ IH.
  ord_destruct γ.
  - subst. rewrite ordExp_0_r, ordExp_0_r...
  - destruct Hsuc as [δ [Hδ Heq]]. subst.
    destruct (classic (α = 0)). {
      subst. rewrite ordExp_0_l...
      apply ord_le_iff_not_gt... intros H. exfalso0.
    }
    rewrite ordExp_suc, ordExp_suc...
    eapply ord_trans_le. auto.
    + apply ordMul_preserve_le_l; revgoals.
      apply IH... 1-3:auto.
    + destruct Hle.
      * left. apply ordMul_normal... intros H1.
        apply ord_pow_eq_0 in H1... subst. exfalso0.
      * right. congruence.
  - destruct (classic (α = 0)) as [|Hα0]. {
      subst. rewrite ordExp_0_l...
      apply ord_le_iff_not_gt... intros H. exfalso0.
    }
    destruct (classic (β = 0)) as [|Hβ0]. {
      subst. destruct Hle. exfalso0.
      subst. rewrite ordExp_0_l...
    }
    apply ord_le_iff_sub...
    rewrite ordExp_limit, ordExp_limit...
    intros x Hx. apply FUnionE in Hx as [δ [Hδ Hx]].
    assert (Hoδ: δ ⋵ 𝐎𝐍). eapply ord_is_ords...
    eapply FUnionI... apply IH in Hδ as []...
    eapply ord_trans... congruence.
Qed.

Fact ordExp_preserve_le_r : ∀ α β γ ⋵ 𝐎𝐍, 1 ∈ γ →
  α ⋸ β → γ ^ α ⋸ γ ^ β.
Proof.
  intros α Hα β Hβ γ Hγ H0 [].
  left. apply ordExp_preserve_lt; auto.
  right. congruence.
Qed.

Example ω_lt_ω_exp_ω : ω ∈ ω ^ ω.
Proof with nauto.
  eapply (ord_trans _ _ _ (ω ^ 2)); revgoals.
  apply ordExp_preserve_lt...
  rewrite pred, ordExp_suc, ordExp_1_r...
  eapply (ord_trans _ _ _ (ω ⋅ 2)); revgoals.
  apply ordMul_preserve_lt...
  rewrite pred, ordMul_suc, ordMul_1_r...
  eapply (ord_trans _ _ _ (ω + 1)); revgoals.
  apply ordAdd_preserve_lt...
  rewrite ordAdd_1_r...
  Unshelve. 1-3:auto.
Qed.

Lemma ordAdd_enlarge : ∀ α β ⋵ 𝐎𝐍, β ≠ 0 → α ∈ α + β.
Proof with auto.
  intros α Hα β Hβ H0. rewrite <- ordAdd_0_r at 1...
  apply ordAdd_preserve_lt... apply ord_neq_0_gt_0...
Qed.

Lemma ordAdd_enlarge_lt : ∀ α β γ ⋵ 𝐎𝐍, α ∈ β → α ∈ β + γ.
Proof with eauto.
  intros α Hα β Hβ γ Hγ Hle.
  destruct (classic (γ = 0)). subst. rewrite ordAdd_0_r...
  rewrite <- (ordAdd_0_r β) in Hle...
  eapply (ord_trans (β + γ))...
  apply ordAdd_preserve_lt... apply ord_neq_0_gt_0...
Qed.

Lemma ordAdd_enlarge_le : ∀ α β γ ⋵ 𝐎𝐍, α ⋸ β → α ⋸ β + γ.
Proof with eauto.
  intros α Hα β Hβ γ Hγ Hle.
  rewrite <- (ordAdd_0_r β) in Hle...
  eapply ord_trans_le. auto. apply Hle.
  apply ordAdd_preserve_le_r...
  apply ord_le_iff_not_gt... intros H. exfalso0.
Qed.

Lemma ordMul_enlarge : ∀ α β ⋵ 𝐎𝐍, α ≠ 0 → 1 ∈ β → α ∈ α ⋅ β.
Proof with nauto.
  intros α Hα β Hβ Hα0 Hβ1. rewrite <- ordMul_1_r at 1...
  apply ordMul_preserve_lt...
Qed.

Lemma ordMul_enlarge_lt : ∀ α β γ ⋵ 𝐎𝐍, γ ≠ 0 → α ∈ β → α ∈ β ⋅ γ.
Proof with neauto.
  intros α Hα β Hβ γ Hγ H0 Hle.
  destruct (classic (β = 0)). subst. exfalso0.
  destruct (classic (γ = 1)). subst. rewrite ordMul_1_r...
  rewrite <- (ordMul_1_r β) in Hle...
  eapply (ord_trans (β ⋅ γ))...
  apply ordMul_preserve_lt...
  apply gt_1_iff_neq_0_1...
Qed.

Lemma ordMul_enlarge_le : ∀ α β γ ⋵ 𝐎𝐍, γ ≠ 0 → α ⋸ β → α ⋸ β ⋅ γ.
Proof with neauto.
  intros α Hα β Hβ γ Hγ H0 Hle.
  destruct (classic (β = 0)). subst. rewrite ordMul_0_l...
  rewrite <- (ordMul_1_r β) in Hle...
  eapply ord_trans_le. auto. apply Hle.
  apply ordMul_preserve_le_r...
  apply ord_le_iff_not_gt... intros H1.
  rewrite one in H1. apply SingE in H1...
Qed.

Lemma ordExp_enlarge : ∀ α β ⋵ 𝐎𝐍, 1 ∈ α → 1 ∈ β → α ∈ α ^ β.
Proof with nauto.
  intros α Hα β Hβ Hα1 Hβ1. rewrite <- ordExp_1_r at 1...
  apply ordExp_preserve_lt...
Qed.

Lemma ordExp_enlarge_lt : ∀ α β γ ⋵ 𝐎𝐍, γ ≠ 0 → α ∈ β → α ∈ β ^ γ.
Proof with neauto.
  intros α Hα β Hβ γ Hγ H0 Hle.
  destruct (classic (β = 0)). subst. exfalso0.
  destruct (classic (β = 1)). {
    subst. rewrite one in Hle. apply SingE in Hle.
    subst. apply ord_neq_0_gt_0...
    intros Hpow. apply ord_pow_eq_0 in Hpow...
  }
  destruct (classic (γ = 1)). subst. rewrite ordExp_1_r...
  rewrite <- (ordExp_1_r β) in Hle...
  eapply (ord_trans (β ^ γ))...
  apply ordExp_preserve_lt...
  1-2: apply gt_1_iff_neq_0_1...
Qed.

Lemma ordExp_enlarge_le : ∀ α β γ ⋵ 𝐎𝐍, γ ≠ 0 → α ⋸ β → α ⋸ β ^ γ.
Proof with neauto.
  intros α Hα β Hβ γ Hγ H0 Hle.
  destruct (classic (β = 0)). subst. rewrite ordExp_0_l...
  destruct (classic (β = 1)). subst. rewrite ordExp_1_l...
  rewrite <- (ordExp_1_r β) in Hle...
  eapply ord_trans_le. auto. apply Hle.
  apply ordExp_preserve_le_r...
  apply gt_1_iff_neq_0_1...
  apply ord_le_iff_not_gt... intros Hγ1.
  rewrite one in Hγ1. apply SingE in Hγ1...
Qed.

(** 减法，除法，对数 **)

Theorem ord_subtraction : ∀ α β ⋵ 𝐎𝐍, α ⋸ β → ∃!δ ⋵ 𝐎𝐍, α + δ = β.
Proof with eauto.
  intros α Hα β Hβ [Hlt|Heq]; revgoals. {
    exists 0. split. rewrite ordAdd_0_r...
    intros x [Hx H]. subst. rewrite <- ordAdd_0_r in H...
    apply ordAdd_cancel in H...
  }
  pose proof (normal_operation_domain_has_maximum (OrdAdd α)) as [δ [Hoδ [Hδ Hmax]]]...
  apply ordAdd_normal... rewrite ordAdd_0_r...
  assert (Hrp: ∀ x ∈ RangeAmong (OrdAdd α) β⁺, ∃!y ⋵ 𝐎𝐍, α + y = x). {
    intros x Hx. apply SepE in Hx as [Hx [y [Hy Heq]]].
    exists y. split... intros y' [Hy' H']. subst.
    apply ordAdd_cancel in H'...
  }
  apply ϕ_ReplAx in Hδ as [σ [Hσ [_ Heq]]]...
  subst. apply SepE1 in Hσ as Hle.
  apply ord_le_iff_lt_suc in Hle...
  exists δ. split.
  - split... destruct Hle... exfalso.
    apply (ord_irrefl δ⁺)... apply ord_le_iff_lt_suc...
    apply Hmax. apply ϕ_ReplAx... exists (α + δ⁺). split...
    apply SepI. rewrite ordAdd_suc...
    rewrite <- ord_suc_preserve_lt... exists δ⁺...
  - intros δ' [Hδ' Heq].
    ord_ext...
    + apply ord_le_iff_lt_suc...
      apply (ordAdd_preserve_lt α)...
      eapply ord_trans_le_lt. auto. apply Hle.
      rewrite <- Heq, ordAdd_suc...
    + apply Hmax. apply ϕ_ReplAx... exists (α + δ'). split...
      apply SepI. apply ord_le_iff_lt_suc... exists δ'...
Qed.

Theorem ord_division : ∀ α δ ⋵ 𝐎𝐍, δ ≠ 0 →
  ∃! β γ ⋵ 𝐎𝐍, α = δ ⋅ β + γ ∧ γ ∈ δ.
Proof with eauto.
  intros α Hα δ Hδ Hδ0.
  destruct (classic (α = 0)) as [|Hα0]. {
    subst. exists 0. split.
    - split... exists 0. split.
      + split... rewrite ordMul_0_r, ordAdd_0_r...
        split... apply ord_neq_0_gt_0...
      + intros γ [Hγ [H _]]. rewrite ordMul_0_r, ordAdd_0_l in H...
    - intros β [Hβ [γ [[Hγ [Heq _]] _]]]. symmetry in Heq.
      apply ord_sum_eq_0 in Heq as []...
      apply ord_prd_eq_0 in H as []... exfalso...
  }
  pose proof (normal_operation_domain_has_maximum (OrdMul δ)) as [β [Hoβ [Hβ Hmax]]].
  auto. apply ordMul_normal... apply Hα.
  rewrite ordMul_0_r... apply ord_neq_0_gt_0...
  assert (Hrp: ∀x ∈ RangeAmong (OrdMul δ) α⁺, ∃!y ⋵ 𝐎𝐍, δ ⋅ y = x). {
    intros x Hx. apply SepE in Hx as [Hx [y [Hy Heq]]].
    exists y. split... intros y' [Hy' H']. subst.
    apply ordMul_cancel in H'...
  }
  apply ϕ_ReplAx in Hβ as [σ [Hσ [_ Heq]]]...
  subst. apply SepE1 in Hσ as Hle.
  apply ord_le_iff_lt_suc in Hle...
  exists β. split.
  - split... apply ord_subtraction in Hle as [γ [[Hγ Heq] Hu]]...
    exists γ. repeat split; [..|intros γ' [Hγ' [Heq' _]]; apply Hu]...
    contra as C. apply ord_le_iff_not_gt in C...
    apply (ord_irrefl β⁺)... apply ord_le_iff_lt_suc...
    apply Hmax. apply ϕ_ReplAx... exists (δ ⋅ β⁺). split...
    apply SepI. apply ord_le_iff_lt_suc...
    rewrite ordMul_suc... rewrite <- Heq.
    apply ordAdd_preserve_le_r... exists β⁺...
  - intros β' [Hβ' [γ' [[Hγ' [Heq Hlt]] _]]].
    ord_ext...
    + apply ord_le_iff_lt_suc...
      apply (ordMul_preserve_lt δ)...
      eapply ord_trans_le_lt. auto. apply Hle.
      rewrite Heq, ordMul_suc...
      apply ordAdd_preserve_lt...
    + apply Hmax. apply ϕ_ReplAx... exists (δ ⋅ β'). split...
      apply SepI. apply ord_le_iff_lt_suc...
      rewrite Heq. apply ordAdd_enlarge_le... exists β'...
Qed.

Theorem ord_logarithm : ∀ α β ⋵ 𝐎𝐍, α ≠ 0 → 1 ∈ β →
  ∃! γ δ ρ ⋵ 𝐎𝐍, α = β ^ γ ⋅ δ + ρ ∧ δ ≠ 0 ∧ δ ∈ β ∧ ρ ∈ β ^ γ.
Proof with neauto.
  intros α Hα β Hβ Hα0 Hβ1.
  destruct (classic (α = 1)) as [|Hα1]. {
    subst. exists 0. split.
    - split... exists 1. split.
      + split... exists 0. split.
        * split... rewrite ordExp_0_r, ordMul_1_r, ordAdd_0_r...
          repeat split... apply suc_has_0...
        * intros ρ [Hρ [H _]]. rewrite ordExp_0_r, ordMul_1_r in H...
          rewrite <- (ordAdd_0_r 1) in H at 1...
          apply ordAdd_cancel in H...
      + intros δ [Hδ [ρ [[Hρ [H [_ [_ Hlt]]]] _]]].
        rewrite ordExp_0_r in H, Hlt...
        rewrite one in Hlt. apply SingE in Hlt. subst.
        rewrite ordMul_1_l, ordAdd_0_r in H...
    - intros γ [Hγ [δ [[Hδ [ρ [[Hρ [Heq [Hδ0 _]]] _]]] _]]].
      symmetry. contra. apply ord_neq_0_gt_0 in H...
      apply (ordExp_preserve_lt β) in H...
      rewrite ordExp_0_r, Heq in H...
      eapply (ordMul_enlarge_lt _ _ _ _ δ) in H...
      eapply (ordAdd_enlarge_lt _ _ _ _ ρ) in H...
      eapply ord_irrefl; revgoals...
  }
  pose proof (normal_operation_domain_has_maximum (OrdExp β)) as [γ [Hoγ [Hγ Hmax]]].
  auto. apply ordExp_normal... apply Hα.
  rewrite ordExp_0_r... apply gt_1_iff_neq_0_1...
  assert (Hrp: ∀x ∈ RangeAmong (OrdExp β) α⁺, ∃!y ⋵ 𝐎𝐍, β ^ y = x). {
    intros x Hx. apply SepE in Hx as [Hx [y [Hy Heq]]].
    exists y. split... intros y' [Hy' H']. subst.
    apply ordExp_cancel in H'...
  }
  apply ϕ_ReplAx in Hγ as [σ [Hσ [_ Heq]]]...
  subst. apply SepE1 in Hσ as Hle.
  apply ord_le_iff_lt_suc in Hle...
  exists γ. split.
  - split... pose proof (ord_division α Hα (β ^ γ)) as [δ [[Hδ [ρ [[Hρ [H1 H2]] Hu1]]] Hu2]]...
    intros H0. apply ord_pow_eq_0 in H0... subst. exfalso0.
    exists δ. split.
    + split... exists ρ. split; revgoals. {
        intros ρ' [Hρ' [H1' [_ [_ H2']]]]. apply Hu1...
      }
      repeat split...
      * intros H0. rewrite H0, ordMul_0_r, ordAdd_0_l in H1...
        rewrite <- H1 in H2. apply ord_le_iff_not_gt in H2...
      * contra as C. apply ord_le_iff_not_gt in C...
        apply (ord_irrefl γ⁺)... apply ord_le_iff_lt_suc...
        apply Hmax. apply ϕ_ReplAx... exists (β ^ γ⁺). split...
        apply SepI. apply ord_le_iff_lt_suc...
        rewrite ordExp_suc... rewrite H1.
        eapply ord_trans_le. auto.
        apply ordMul_preserve_le_r; revgoals...
        apply ordAdd_enlarge_le... exists γ⁺...
    + intros δ' [Hδ' [ρ' [[Hρ' [H1' [Hlt1 [Hlt2 H2']]]] Hu]]].
      apply Hu2. split... exists ρ'. split...
      intros ρ'' [Hρ'' [H1'' H2'']]. apply Hu...
  - intros γ' [Hγ' [δ' [[Hδ' [ρ' [[Hρ' [H1 [H2 [H3 H4]]]] _]]] _]]].
    ord_ext...
    + apply ord_le_iff_lt_suc...
      apply (ordExp_preserve_lt β)...
      eapply ord_trans_le_lt. auto.
      apply Hle. rewrite H1, ordExp_suc...
      eapply ord_trans_lt_le. auto.
      apply ordAdd_preserve_lt; revgoals...
      rewrite <- ordMul_suc...
      apply ordMul_preserve_le_r...
      apply ord_suc_correct...
    + apply Hmax. apply ϕ_ReplAx... exists (β ^ γ'). split...
      apply SepI. apply ord_le_iff_lt_suc...
      rewrite H1. apply ordAdd_enlarge_le...
      apply ordMul_enlarge_le... exists γ'...
  Unshelve. 1-4:auto.
Qed.

(** 结合律与分配律 **)

Theorem ordAdd_assoc : ∀ α β γ ⋵ 𝐎𝐍, α + β + γ = α + (β + γ).
Proof with eauto.
  intros α Hα β Hβ γ Hγ.
  generalize dependent β.
  generalize dependent α.
  generalize dependent γ.
  ord_induction; intros γ Hγ IH α Hα β Hβ.
  ord_destruct γ.
  - subst. rewrite ordAdd_0_r, ordAdd_0_r...
  - destruct Hsuc as [δ [Hδ Heq]]. subst.
    repeat rewrite ordAdd_suc... rewrite IH...
  - ext ξ Hξ.
    + rewrite ordAdd_limit in Hξ...
      apply FUnionE in Hξ as [δ [Hδ Hξ]].
      rewrite IH in Hξ... eapply ord_trans...
      apply ordAdd_normal, ordAdd_normal...
    + rewrite ordAdd_limit in Hξ...
      2: apply ord_sum_is_limord...
      2: intros H; apply ord_sum_eq_0 in H as []...
      apply FUnionE in Hξ as [δ [Hδ Hξ]].
      rewrite ordAdd_limit in Hδ...
      apply FUnionE in Hδ as [ε [Hε Hδ]].
      assert (Hoε: ε ⋵ 𝐎𝐍). eapply ord_is_ords; revgoals...
      assert (Hoδ: δ ⋵ 𝐎𝐍). eapply ord_is_ords; revgoals...
      apply (ordAdd_preserve_lt α) in Hδ...
      rewrite <- IH in Hδ...
      eapply ord_trans, ord_trans...
      apply ordAdd_preserve_lt...
Qed.

Corollary ordAdd_arbitrary_assoc : ∀α ⋵ 𝐎𝐍, ∀n ∈ ω, α + α ⋅ n = α ⋅ n + α.
Proof with auto.
  intros α Hα n Hn. ω_induction n.
  - rewrite ordMul_0_r, ordAdd_0_r, ordAdd_0_l...
  - rewrite ordMul_suc... rewrite <- IH at 2... rewrite ordAdd_assoc...
Qed.

Corollary ordAdd_left_enlarge : ∀α ⋵ 𝐎𝐍, ∀n ∈ ω, ∀β ∈ α ⋅ n, β ∈ α + β.
Proof with neauto; try congruence.
  intros α Hα n Hn. ω_induction n; intros x Hx.
  - rewrite <- zero, ordMul_0_r in Hx... exfalso0.
  - destruct (classic (x ∈ α ⋅ m)). apply IH...
    assert (Hox: x ⋵ 𝐎𝐍). apply (ord_is_ords (α ⋅ m⁺))...
    rewrite ordMul_suc, <- ordAdd_arbitrary_assoc in Hx...
    apply ord_le_iff_not_gt in H as []...
    apply (ordAdd_preserve_lt α) in H... eapply ord_trans...
Qed.

Theorem ordMul_distr : ∀ α β γ ⋵ 𝐎𝐍, α ⋅ (β + γ) = α ⋅ β + α ⋅ γ.
Proof with eauto.
  intros α Hα β Hβ γ Hγ.
  generalize dependent β.
  generalize dependent α.
  generalize dependent γ.
  ord_induction; intros γ Hγ IH α Hα β Hβ.
  ord_destruct γ.
  - subst. rewrite ordAdd_0_r, ordMul_0_r, ordAdd_0_r...
  - destruct Hsuc as [δ [Hδ Heq]]. subst.
    rewrite ordMul_suc, ordAdd_suc, ordMul_suc, IH, ordAdd_assoc...
  - destruct (classic (α = 0)) as [|Hα0]. {
      subst. repeat rewrite ordMul_0_l... rewrite ordAdd_0_r...
    }
    ext ξ Hξ.
    + rewrite ordMul_limit in Hξ...
      2: apply ord_sum_is_limord...
      2: intros H; apply ord_sum_eq_0 in H as []...
      apply FUnionE in Hξ as [δ [Hδ Hξ]].
      assert (Hoδ: δ ⋵ 𝐎𝐍). apply (ord_is_ords (β + γ))...
      rewrite ordAdd_limit in Hδ...
      apply FUnionE in Hδ as [ε [Hε Hδ]].
      assert (Hoε: ε ⋵ 𝐎𝐍). apply (ord_is_ords γ)...
      eapply (ordMul_preserve_lt α) in Hδ...
      rewrite IH in Hδ... eapply ord_trans, ord_trans...
      apply ordAdd_normal, ordMul_normal...
    + rewrite ordAdd_limit in Hξ...
      2: apply ord_prd_is_limord_r...
      2: intros H; apply ord_prd_eq_0 in H as []...
      apply FUnionE in Hξ as [δ [Hδ Hξ]].
      rewrite ordMul_limit in Hδ...
      apply FUnionE in Hδ as [ε [Hε Hδ]].
      assert (Hoε: ε ⋵ 𝐎𝐍). eapply ord_is_ords; revgoals...
      assert (Hoδ: δ ⋵ 𝐎𝐍). eapply ord_is_ords; revgoals...
      apply (ordAdd_preserve_lt (α ⋅ β)) in Hδ...
      rewrite <- IH in Hδ...
      eapply ord_trans, ord_trans...
      apply ordMul_preserve_lt, ordAdd_preserve_lt...
Qed.

Theorem ordMul_assoc : ∀ α β γ ⋵ 𝐎𝐍, α ⋅ β ⋅ γ = α ⋅ (β ⋅ γ).
Proof with eauto.
  intros α Hα β Hβ γ Hγ.
  generalize dependent β.
  generalize dependent α.
  generalize dependent γ.
  ord_induction; intros γ Hγ IH α Hα β Hβ.
  ord_destruct γ.
  - subst. repeat rewrite ordMul_0_r...
  - destruct Hsuc as [δ [Hδ Heq]]. subst.
    repeat rewrite ordMul_suc... repeat rewrite IH...
    rewrite ordMul_distr...
  - destruct (classic (α = 0)) as [|Hα0]. {
      subst. repeat rewrite ordMul_0_l...
    }
    destruct (classic (β = 0)) as [|Hβ0]. {
      subst. rewrite ordMul_0_l, ordMul_0_r, ordMul_0_l...
    }
    ext ξ Hξ.
    + rewrite ordMul_limit in Hξ...
      apply FUnionE in Hξ as [δ [Hδ Hξ]].
      rewrite IH in Hξ... eapply ord_trans...
      apply ordMul_normal, ordMul_normal...
    + rewrite ordMul_limit in Hξ...
      2: apply ord_prd_is_limord_r...
      2: intros H; apply ord_prd_eq_0 in H as []...
      apply FUnionE in Hξ as [δ [Hδ Hξ]].
      rewrite ordMul_limit in Hδ...
      apply FUnionE in Hδ as [ε [Hε Hδ]].
      assert (Hoε: ε ⋵ 𝐎𝐍). eapply ord_is_ords; revgoals...
      assert (Hoδ: δ ⋵ 𝐎𝐍). eapply ord_is_ords; revgoals...
      apply (ordMul_preserve_lt α) in Hδ...
      rewrite <- IH in Hδ...
      eapply ord_trans, ord_trans...
      apply ordMul_preserve_lt...
      intros H. apply ord_prd_eq_0 in H as []...
Qed.

Theorem ordExp_add : ∀ α β γ ⋵ 𝐎𝐍, α ^ (β + γ) = α ^ β ⋅ α ^ γ.
Proof with eauto.
  intros α Hα β Hβ γ Hγ.
  generalize dependent β.
  generalize dependent α.
  generalize dependent γ.
  ord_induction; intros γ Hγ IH α Hα β Hβ.
  ord_destruct γ.
  - subst. rewrite ordAdd_0_r, ordExp_0_r, ordMul_1_r...
  - destruct Hsuc as [δ [Hδ Heq]]. subst.
    rewrite ordAdd_suc, ordExp_suc, ordExp_suc, IH, ordMul_assoc...
  - destruct (classic (β = 0)) as [|Hβ0]. {
      subst. rewrite ordAdd_0_l, ordExp_0_r, ordMul_1_l...
    }
    destruct (classic (α = 0)) as [|Hα0]. {
      subst. repeat rewrite ordExp_0_l... rewrite ordMul_0_r...
      intros H. apply ord_sum_eq_0 in H as []...
    }
    destruct (classic (α = 1)) as [|Hα1]. {
      subst. repeat rewrite ordExp_1_l... rewrite ordMul_1_r...
    }
    assert (H1α: 1 ∈ α). apply gt_1_iff_neq_0_1...
    ext ξ Hξ.
    + rewrite ordExp_limit in Hξ...
      2: apply ord_sum_is_limord...
      2: intros H; apply ord_sum_eq_0 in H as []...
      apply FUnionE in Hξ as [δ [Hδ Hξ]].
      rewrite ordAdd_limit in Hδ...
      apply FUnionE in Hδ as [ε [Hε Hδ]].
      assert (Hoε: ε ⋵ 𝐎𝐍). apply (ord_is_ords γ)...
      assert (Hoδ: δ ⋵ 𝐎𝐍). apply (ord_is_ords (β + ε))...
      eapply (ordExp_preserve_lt α) in Hδ...
      eapply ord_trans, ord_trans... rewrite IH...
      apply ordMul_normal, ordExp_normal...
      intros H. apply ord_pow_eq_0 in H...
    + rewrite ordMul_limit in Hξ...
      2: apply ord_pow_is_limord_r...
      2: intros H; apply ord_pow_eq_0 in H...
      apply FUnionE in Hξ as [δ [Hδ Hξ]].
      rewrite ordExp_limit in Hδ...
      apply FUnionE in Hδ as [ε [Hε Hδ]].
      assert (Hoε: ε ⋵ 𝐎𝐍). eapply ord_is_ords; revgoals...
      assert (Hoδ: δ ⋵ 𝐎𝐍). eapply ord_is_ords; revgoals...
      apply (ordMul_preserve_lt (α ^ β)) in Hδ...
      2: intros H'; apply ord_pow_eq_0 in H'...
      eapply ord_trans, ord_trans... rewrite <- IH...
      apply ordExp_normal, ordAdd_normal...
Qed.

Theorem ordExp_exp : ∀ α β γ ⋵ 𝐎𝐍, (α ^ β) ^ γ = α ^ (β ⋅ γ).
Proof with neauto.
  intros α Hα β Hβ γ Hγ.
  generalize dependent β.
  generalize dependent α.
  generalize dependent γ.
  ord_induction; intros γ Hγ IH α Hα β Hβ.
  ord_destruct γ.
  - subst. rewrite ordExp_0_r, ordMul_0_r, ordExp_0_r...
  - destruct Hsuc as [δ [Hδ Heq]]. subst.
    rewrite ordExp_suc, ordMul_suc, IH, ordExp_add...
  - destruct (classic (β = 0)) as [|Hβ0]. {
      subst. rewrite ordExp_0_r, ordExp_1_l, ordMul_0_l, ordExp_0_r...
    }
    destruct (classic (α = 0)) as [|Hα0]. {
      subst. repeat rewrite ordExp_0_l...
      intros H. apply ord_prd_eq_0 in H as []...
    }
    destruct (classic (α = 1)) as [|Hα1]. {
      subst. repeat rewrite ordExp_1_l...
    }
    assert (H1α: 1 ∈ α). apply gt_1_iff_neq_0_1...
    ext ξ Hξ.
    + rewrite ordExp_limit in Hξ...
      2: intros H; apply ord_pow_eq_0 in H...
      apply FUnionE in Hξ as [δ [Hδ Hξ]].
      eapply ord_trans... rewrite IH...
      apply ordExp_normal, ordMul_normal...
    + rewrite ordExp_limit in Hξ...
      2: apply ord_prd_is_limord_r...
      2: intros H; apply ord_prd_eq_0 in H as []...
      apply FUnionE in Hξ as [δ [Hδ Hξ]].
      rewrite ordMul_limit in Hδ...
      apply FUnionE in Hδ as [ε [Hε Hδ]].
      assert (Hoε: ε ⋵ 𝐎𝐍). eapply ord_is_ords; revgoals...
      assert (Hoδ: δ ⋵ 𝐎𝐍). eapply ord_is_ords; revgoals...
      apply (ordExp_preserve_lt α) in Hδ...
      eapply ord_trans, ord_trans... rewrite <- IH...
      apply ordExp_normal... apply ordExp_enlarge_lt...
Qed.

(** 吸收律 **)

Theorem ordAdd_1_absorption : ∀α ⋵ 𝐎𝐍, ω ⋸ α → 1 + α = α.
Proof with neauto.
  ord_induction. intros α Hα IH Hle.
  destruct Hle; revgoals. {
    subst. apply ordAdd_1_ω.
  }
  ord_destruct α.
  - subst. exfalso0.
  - destruct Hsuc as [β [Hβ Heq]]. subst.
    rewrite ordAdd_suc, IH... apply ord_le_iff_lt_suc...
  - rewrite ordAdd_limit... ext ξ Hξ.
    + apply FUnionE in Hξ as [β [Hβ Hξ]].
      destruct (classic (β ∈ ω)).
      * eapply ord_trans... rewrite ordAdd_1_l...
        apply sucord_in_limord...
      * rewrite IH in Hξ... eapply ord_trans...
        apply ord_le_iff_not_gt... eapply ord_is_ords...
    + assert (Hξo: ξ ⋵ 𝐎𝐍). eapply ord_is_ords...
      destruct (classic (ξ ∈ ω)) as [|Hle].
      * eapply FUnionI... rewrite ordAdd_1_l...
      * apply ord_le_iff_not_gt in Hle...
        eapply FUnionI. apply sucord_in_limord...
        rewrite ordAdd_suc, IH...
Qed.

Corollary ordAdd_n_absorption : ∀α ⋵ 𝐎𝐍, ∀n ∈ ω, ω ⋸ α → n + α = α.
Proof with neauto.
  intros α Hα n Hn Hle.
  ω_induction n. rewrite ordAdd_0_l...
  rewrite <- ordAdd_1_r, ordAdd_assoc, ordAdd_1_absorption...
Qed.

(* ω幂对加法的吸收律 *)
Corollary ω_pow_add_absorption : ∀β ⋵ 𝐎𝐍, ∀α ∈ β, ω ^ α + ω ^ β = ω ^ β.
Proof with neauto.
  intros β Hβ α Hlt. assert (α ⋸ β)...
  assert (Hα: α ⋵ 𝐎𝐍). eapply ord_is_ords...
  apply ord_subtraction in H as [δ [[Hδ Hsum] _]]... subst.
  rewrite ordExp_add... rewrite <- (ordMul_1_r (ω ^ α)) at 1...
  rewrite <- ordMul_distr... f_equal. apply ordAdd_1_absorption...
  rewrite <- ordExp_1_r at 1 3... apply ordExp_preserve_le_r...
  apply ord_le_iff_not_gt... intros H.
  rewrite one in H. apply SingE in H. subst.
  rewrite ordAdd_0_r in Hlt... eapply ord_irrefl...
Qed.
