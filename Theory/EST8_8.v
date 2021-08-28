(** Adapted from "Elements of Set Theory" Chapter 8 **)
(** Coq coding by choukh, Aug 2021 **)

Require Export ZFC.Theory.EST8_7.

(*** EST第八章8：ε数 ***)

Module EpsilonNumber.
Import OrdinalClass 𝐎𝐍Separation 𝐎𝐍Operation VeblenFixedPoint.

Local Hint Resolve
  ω_is_ords enum_operative operation_operative ordExp_ran : core.

(* ω指数塔 *)
Definition ω_tower := Operation ω (λ α, ω ^ α).

(* 0层塔 *)
Lemma ω_tower_0 : ω_tower 0 = ω.
Proof. apply operation_0. Qed.

(* 后继层塔 *)
Lemma ω_tower_suc : ∀α ⋵ 𝐎𝐍, ω_tower α⁺ = ω ^ ω_tower α.
Proof. apply operation_suc. Qed.

(* 1层塔 *)
Fact ω_tower_1 : ω_tower 1 = ω ^ ω.
Proof. rewrite pred, ω_tower_suc, ω_tower_0; auto. Qed.

(* 极限层塔 *)
Lemma ω_tower_limit : continuous ω_tower.
Proof. apply operation_limit. Qed.

(* 指数塔是序数 *)
Lemma ω_tower_ran : ∀α ⋵ 𝐎𝐍, ω_tower α ⋵ 𝐎𝐍.
Proof. apply operation_operative; auto. Qed.
Local Hint Resolve ω_tower_ran : core.

(* 有限层塔递增 *)
Lemma ω_tower_fin_ascending : ∀n ∈ ω, ω_tower n ∈ ω_tower n⁺.
Proof with nauto.
  intros n Hn. ω_induction n.
  - subst. rewrite ω_tower_suc, <- zero, ω_tower_0...
    apply ω_lt_ω_exp_ω.
  - rewrite ω_tower_suc, ω_tower_suc...
    apply ordExp_preserve_lt...
Qed.

(* 有限层塔的元素小于其以ω为底的幂 *)
Lemma ω_tower_upstairs : ∀n ∈ ω, ∀α ∈ ω_tower n, α ∈ ω ^ α.
Proof with neauto; try congruence.
  intros n Hn. ω_induction n; intros x Hx.
  + destruct (classic (x = 0)). {
      subst. rewrite ordExp_0_r, pred, pred...
    }
    rewrite <- zero, ω_tower_0 in Hx.
    apply ordExp_enlarge_lt...
  + destruct (classic (x ∈ ω_tower m)). apply IH...
    assert (Hox: x ⋵ 𝐎𝐍). apply (ord_is_ords (ω_tower m⁺))...
    rewrite ω_tower_suc in Hx...
    apply ord_leq_iff_not_gt in H as []...
    apply (ordExp_preserve_lt ω) in H...
    eapply ord_trans...
Qed.

(* ε₀定义为ω层塔 *)
Definition ε₀ := ω_tower ω.

(* ε₀是有限层塔序列的上界 *)
Remark ε₀_is_sup : ε₀ = sup{ω_tower α | α ∊ ω}.
Proof. apply ω_tower_limit; nauto. Qed.

(* ε₀是序数 *)
Lemma ε₀_is_ord : ε₀ ⋵ 𝐎𝐍.
Proof. apply operation_operative; auto. Qed.
Local Hint Resolve ε₀_is_ord : core.

(* ε₀里有0层塔 *)
Lemma ε₀_has_tower_0 : ω ∈ ε₀.
Proof with nauto.
  rewrite ε₀_is_sup. apply (FUnionI _ _ 1)...
  rewrite ω_tower_1. rewrite <- (ordExp_1_r) at 1...
  apply ordExp_preserve_lt...
Qed.

(* ε₀里有任意有限层塔 *)
Lemma ε₀_has_tower_n : ∀n ∈ ω, ω_tower n ∈ ε₀.
Proof with nauto.
  intros n Hn. rewrite ε₀_is_sup.
  eapply (FUnionI _ _ n⁺)... apply ω_inductive...
  apply ω_tower_fin_ascending...
Qed.

(* ε₀里有任意有限层塔里的元素 *)
Lemma ε₀_has_those_of_tower_n : ∀n ∈ ω, ∀α ∈ ω_tower n, α ∈ ε₀.
Proof with eauto.
  intros n Hn α Hα. eapply ord_trans...
  apply ε₀_has_tower_n...
Qed.
Local Notation ε₀I := ε₀_has_those_of_tower_n.

(* ε₀的任意元素都在某有限层塔里 *)
Lemma ε₀_has_only_those_of_tower_n : ∀α ∈ ε₀, ∃n ∈ ω, α ∈ ω_tower n.
Proof.
  intros α Hα. rewrite ε₀_is_sup in Hα.
  apply FUnionE in Hα; auto.
Qed.
Local Notation ε₀E := ε₀_has_only_those_of_tower_n.

(* ε₀里有且只有那些有限层塔里的元素 *)
Fact ε₀_iff_of_tower_n : ∀α ⋵ 𝐎𝐍, α ∈ ε₀ ↔ ∃n ∈ ω, α ∈ ω_tower n.
Proof.
  split. apply ε₀E.
  intros [n [Hn Hα]]. apply (ε₀I n); auto.
Qed.

(* ε₀是极限序数 *)
Lemma ε₀_is_limit : ε₀ ⋵ 𝐎𝐍ˡⁱᵐ.
Proof with eauto.
  split... ext.
  - apply ε₀E in H as [n [Hn Hx]].
    apply UnionAx. exists (ω_tower n⁺). split.
    + apply ε₀_has_tower_n. apply ω_inductive...
    + eapply ord_trans... apply ω_tower_fin_ascending...
  - apply UnionAx in H as [α [Hα Hx]].
    apply ε₀E in Hα as [n [Hn Hα]].
    eapply ord_trans, ord_trans... apply ε₀_has_tower_n...
Qed.
Local Hint Resolve ε₀_is_limit : core.

(* ε₀不等于0 *)
Lemma ε₀_neq_0 : ε₀ ≠ 0.
Proof.
  pose proof ε₀_has_tower_0. intros Heq.
  rewrite Heq in H. exfalso0.
Qed.
Local Hint Resolve ε₀_neq_0 : core.

(* 以ω为底，以ε₀的任意元素为指数的幂也在ε₀里 *)
Lemma ε₀_upstairs : ∀α ∈ ε₀, ω ^ α ∈ ε₀.
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
    apply FUnionE in H as [α [Hα Hx]].
    eapply ord_trans... apply ε₀_upstairs...
  - rewrite ordExp_limit... eapply FUnionI...
    apply ε₀E in H as [n [Hn Hx]].
    eapply ω_tower_upstairs...
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
Lemma ε_number_has_ω_tower_n : ∀n ∈ ω, ∀ε ⋵ ε_number, ω_tower n ∈ ε.
Proof with neauto.
  intros n Hn. ω_induction n; intros ε [Hε Heq].
  - rewrite <- zero, ω_tower_0, <- Heq.
    rewrite <- ordExp_1_r at 1...
    apply ordExp_preserve_lt...
    apply gt_1_iff_neq_0_1... split...
    apply ε_number_neq_0. split...
    apply ε_number_neq_1. split...
  - rewrite ω_tower_suc, <- Heq...
    apply ordExp_preserve_lt... apply IH. split...
Qed.

(* ε₀是最小的ε数 *)
Lemma ε₀_is_the_least_ε_number : ∀α ⋵ ε_number, ε₀ ⋸ α.
Proof with eauto.
  intros ε [Hε Heq]. apply ord_leq_iff_sub...
  intros x Hx. apply ε₀E in Hx as [n [Hn Hx]].
  eapply ord_trans... apply ε_number_has_ω_tower_n... split...
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

(* ε运算规范 *)
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
  apply sub_antisym; apply ord_leq_iff_sub...
  - apply ε_spec... apply ε₀_is_ε_number.
    intros H. apply ReplAx in H as [x [Hx _]]. exfalso0.
  - apply ε₀_is_the_least_ε_number...
Qed.

End EpsilonNumber.
