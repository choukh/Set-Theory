(** Adapted from "Elements of Set Theory" Chapter 8 **)
(** Coq coding by choukh, Aug 2021 **)

Require Export ZFC.EST8_1.
Import 𝐎𝐍Operation.

(*** EST第八章6：序数算术（递归定义） ***)

Declare Scope OrdArith_scope.
Delimit Scope OrdArith_scope with oa.
Open Scope OrdArith_scope.

(* 序数加法 *)
Definition OrdAdd := λ α, Operation α Suc.
Notation "α + β" := (OrdAdd α β) : OrdArith_scope.

Theorem ordAdd_ident : ∀α ⋵ 𝐎𝐍, α + 0 = α.
Proof. intros α H. apply operation_0. Qed.

Theorem ordAdd_suc : ∀ α β ⋵ 𝐎𝐍, α + β⁺ = (α + β)⁺.
Proof. intros α H. apply operation_suc. Qed.

Theorem ordAdd_limit : ∀α ⋵ 𝐎𝐍, ∀𝜆 ⋵ 𝐎𝐍ˡⁱᵐ, 𝜆 ≠ ∅ →
  α + 𝜆 = sup {α + β | β ∊ 𝜆}.
Proof. intros α H 𝜆. apply operation_limit. Qed.

Corollary ordAdd_1 : ∀α ⋵ 𝐎𝐍, α + 1 = α⁺.
Proof.
  intros α Ho.
  rewrite pred, ordAdd_suc, ordAdd_ident; auto.
Qed.

Theorem ordAdd_ran : ∀ α β ⋵ 𝐎𝐍, α + β ⋵ 𝐎𝐍.
Proof. intros α Hoα β Hoβ. apply operation_operative; auto. Qed.

(* 有限序数加法等效于自然数加法 *)
Theorem fin_ordAdd_eq_add : ∀ m n ∈ ω, m + n = (m + n)%ω.
Proof with nauto.
  intros m Hm n Hn. generalize dependent m.
  ω_induction n; intros k Hk.
  - rewrite ordAdd_ident, add_ident...
    apply (ord_is_ords ω)...
  - rewrite ordAdd_suc, IH, suc, suc, add_assoc...
    apply add_ran... apply (ord_is_ords ω)... apply (ord_is_ords ω)...
Qed.

(* 有限序数的和是自然数 *)
Corollary fin_ordAdd_ran : ∀ m n ∈ ω, m + n ∈ ω.
Proof with auto.
  intros m Hm n Hn. rewrite fin_ordAdd_eq_add... apply add_ran...
Qed.

Example ordAdd_1_1 : 1 + 1 = 2.
Proof. rewrite pred, ordAdd_suc, ordAdd_ident; auto. Qed.

Example ordAdd_1_ω : 1 + ω = ω.
Proof with neauto.
  rewrite ordAdd_limit...
  apply ExtAx. split; intros Hx.
  - apply UnionAx in Hx as [y [Hy Hx]].
    apply ReplAx in Hy as [z [Hz H]]. subst y.
    eapply ω_trans... apply fin_ordAdd_ran...
  - apply UnionAx. exists x⁺. split...
    apply ReplAx. exists x. split...
    rewrite fin_ordAdd_eq_add, add_comm, suc...
Qed.

Example ordAdd_ω_1 : ω + 1 = ω⁺.
Proof. rewrite pred, ordAdd_suc, ordAdd_ident; auto. Qed.

(* 序数乘法 *)
Definition OrdMul := λ α, Operation 0 (OrdAdd α).
Notation "α ⋅ β" := (OrdMul α β) : OrdArith_scope.

Theorem ordMul_0 : ∀α ⋵ 𝐎𝐍, α ⋅ 0 = 0.
Proof. intros α H. apply operation_0. Qed.

Theorem ordMul_suc : ∀ α β ⋵ 𝐎𝐍, α ⋅ β⁺ = α + (α ⋅ β).
Proof. intros α H. apply operation_suc. Qed.

Theorem ordMul_limit : ∀α ⋵ 𝐎𝐍, ∀𝜆 ⋵ 𝐎𝐍ˡⁱᵐ, 𝜆 ≠ ∅ →
  α ⋅ 𝜆 = sup {α ⋅ β | β ∊ 𝜆}.
Proof. intros α H 𝜆. apply operation_limit. Qed.

Corollary ordMul_ident : ∀α ⋵ 𝐎𝐍, α ⋅ 1 = α.
Proof.
  intros α Ho.
  rewrite pred, ordMul_suc, ordMul_0, ordAdd_ident; auto.
Qed.

Theorem ordMul_ran : ∀ α β ⋵ 𝐎𝐍, α ⋅ β ⋵ 𝐎𝐍.
Proof.
  intros α Hoα β Hoβ.
  apply operation_operative; auto.
  apply ordAdd_ran; auto.
Qed.

(* 有限序数乘法等效于自然数乘法 *)
Theorem fin_ordMul_eq_mul : ∀ m n ∈ ω, m ⋅ n = (m ⋅ n)%ω.
Proof with nauto.
  intros m Hm n Hn. generalize dependent m.
  ω_induction n; intros k Hk.
  - rewrite ordMul_0, mul_0_r...
    apply (ord_is_ords ω)...
  - rewrite ordMul_suc, IH, mul_suc, fin_ordAdd_eq_add, add_comm...
    apply mul_ran... apply mul_ran...
    apply (ord_is_ords ω)... apply (ord_is_ords ω)...
Qed.

(* 有限序数的积是自然数 *)
Corollary fin_ordMul_ran : ∀ m n ∈ ω, m ⋅ n ∈ ω.
Proof with auto.
  intros m Hm n Hn. rewrite fin_ordMul_eq_mul... apply mul_ran...
Qed.

(* 序数乘方 *)
Definition OrdExp := λ α, Operation 1 (OrdMul α).
Notation "α ^ β" := (OrdExp α β) : OrdArith_scope.

Theorem ordExp_0_r : ∀α ⋵ 𝐎𝐍, α ^ 0 = 1.
Proof. intros α H. apply operation_0. Qed.

Theorem ordExp_suc : ∀ α β ⋵ 𝐎𝐍, α ^ β⁺ = α ⋅ (α ^ β).
Proof. intros α H. apply operation_suc. Qed.

Theorem ordExp_limit : ∀α ⋵ 𝐎𝐍, ∀𝜆 ⋵ 𝐎𝐍ˡⁱᵐ, 𝜆 ≠ ∅ →
  α ^ 𝜆 = sup {α ^ β | β ∊ 𝜆}.
Proof. intros α H 𝜆. apply operation_limit. Qed.

Corollary ordExp_1_r : ∀α ⋵ 𝐎𝐍, α ^ 1 = α.
Proof.
  intros α Ho.
  rewrite pred, ordExp_suc, ordExp_0_r, ordMul_ident; auto.
Qed.

Theorem ordExp_ran : ∀ α β ⋵ 𝐎𝐍, α ^ β ⋵ 𝐎𝐍.
Proof.
  intros α Hoα β Hoβ.
  apply operation_operative; nauto.
  apply ordMul_ran; auto.
Qed.

(* 有限序数乘方等效于自然数乘方 *)
Theorem fin_ordExp_eq_exp : ∀ m n ∈ ω, m ^ n = (m ^ n)%ω.
Proof with nauto.
  intros m Hm n Hn. generalize dependent m.
  ω_induction n; intros k Hk.
  - rewrite ordExp_0_r, exp_0_r...
    apply (ord_is_ords ω)...
  - rewrite ordExp_suc, IH, exp_suc, fin_ordMul_eq_mul, mul_comm...
    apply exp_ran... apply exp_ran...
    apply (ord_is_ords ω)... apply (ord_is_ords ω)...
Qed.

(* 有限序数的幂是自然数 *)
Corollary fin_ordExp_ran : ∀ m n ∈ ω, m ^ n ∈ ω.
Proof with auto.
  intros m Hm n Hn. rewrite fin_ordExp_eq_exp... apply exp_ran...
Qed.

Example ordExp_2_ω : 2 ^ ω = ω.
Proof with neauto.
  rewrite ordExp_limit...
  apply ExtAx. split; intros Hx.
  - apply UnionAx in Hx as [y [Hy Hx]].
    apply ReplAx in Hy as [z [Hz H]]. subst y.
    eapply ω_trans... apply fin_ordExp_ran...
  - apply UnionAx. exists (2 ^ x). split...
    apply ReplAx. exists x. split...
    rewrite fin_ordExp_eq_exp...
    apply lt_exp_enlarge... apply BUnionI2...
Qed.

(* TODO *)
(** 序数算术定律 **)

Theorem ordAdd_ident' : ∀α ⋵ 𝐎𝐍, 0 + α = α.
Proof.
  intros α Ho.
Admitted.

Theorem ordMul_ident' : ∀α ⋵ 𝐎𝐍, 1 ⋅ α = α.
Proof.
  intros α Ho.
Admitted.

Theorem ordMul_0' : ∀α ⋵ 𝐎𝐍, 0 ⋅ α = 0.
Proof.
  intros α Ho.
Admitted.

Theorem ordExp_0_l : ∀α ⋵ 𝐎𝐍, α ≠ 0 → 0 ^ α = 0.
Proof.
  intros α Ho.
Admitted.

Theorem ordExp_1_l : ∀α ⋵ 𝐎𝐍, 1 ^ α = 1.
Proof.
  intros α Ho.
Admitted.

Theorem ordAdd_assoc : ∀ α β γ ⋵ 𝐎𝐍, α + β + γ = α + (β + γ).
Proof.
  intros α Hoα β Hoβ γ Hoγ.
Admitted.

Theorem ordMul_assoc : ∀ α β γ ⋵ 𝐎𝐍, α ⋅ β ⋅ γ = α ⋅ (β ⋅ γ).
Proof.
  intros α Hoα β Hoβ γ Hoγ.
Admitted.

Theorem ordMul_distr : ∀ α β γ ⋵ 𝐎𝐍, α ⋅ (β + γ) = α ⋅ β + α ⋅ γ.
Proof.
  intros α Hoα β Hoβ γ Hoγ.
Admitted.
