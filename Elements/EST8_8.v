(** Adapted from "Elements of Set Theory" Chapter 8 **)
(** Coq coding by choukh, Aug 2021 **)

Require ZFC.Lib.ChoiceFacts ZFC.Lib.OrdinalCountability.
Require Export ZFC.Elements.EST8_7.
Import OrdinalClass 𝐎𝐍Separation 𝐎𝐍Operation VeblenFixedPoint.

Local Hint Resolve
  enum_operative operation_operative ordExp_ran : core.

(*** EST第八章8：迭代幂次，ε数 ***)

(* 迭代幂次 *)
Definition Tetration := λ α, Operation α (OrdExp α).
Notation "α ^^ β" := (Tetration α β) (at level 25) : OrdArith_scope.

Theorem ordTet_0 : ∀α ⋵ 𝐎𝐍, α ^^ 0 = α.
Proof. intros α H. apply operation_0; auto. Qed.

Theorem ordTet_suc : ∀ α β ⋵ 𝐎𝐍, α ^^ β⁺ = α ^ (α ^^ β).
Proof. intros α Hα β Hβ. apply operation_suc; auto. Qed.

Theorem ordTet_limit : ∀α ⋵ 𝐎𝐍, continuous (Tetration α).
Proof. intros α Hα. apply operation_limit; auto. Qed.

Theorem ordTet_ran : ∀ α β ⋵ 𝐎𝐍, α ^^ β ⋵ 𝐎𝐍.
Proof. intros α Hα β Hβ. apply operation_operative; auto. Qed.
Local Hint Resolve ordTet_ran : core.

Fact ord_tower_eq_0 : ∀ α β ⋵ 𝐎𝐍, α ^^ β = 0 → α = 0.
Proof with eauto.
  intros α Hα β Hβ. generalize dependent β.
  ord_induction. intros β Hβ IH H0.
  ord_destruct β.
  - subst. rewrite ordTet_0 in H0...
  - destruct Hsuc as [γ [Hγ Heq]]. subst.
    rewrite ordTet_suc in H0...
    apply ord_pow_eq_0 in H0...
  - rewrite ordTet_limit in H0...
    apply union_eq_empty in H0 as [].
    + apply repl_eq_empty in H. exfalso...
    + apply EmptyNE in H1 as [γ Hγ].
      assert (Hoγ: γ ⋵ 𝐎𝐍). eapply ord_is_ords...
      apply sucord_in_limord in Hγ...
      eapply repl_eq_1 in Hγ as H0...
Qed.

(* 极限序数集的并是极限序数 *)
Lemma union_of_limords_is_limord : ∀ A, A ⪽ 𝐎𝐍ˡⁱᵐ → ⋃ A ⋵ 𝐎𝐍ˡⁱᵐ.
Proof with eauto; try congruence.
  intros A Hlim.
  destruct (classic (sup A ∈ A)) as []. apply Hlim...
  apply sup_ords_out_impl_is_limord...
Qed.

Fact ord_tower_is_limord : ∀α ⋵ 𝐎𝐍, ∀𝜆 ⋵ 𝐎𝐍ˡⁱᵐ, 𝜆 ≠ 0 → 𝜆 ^^ α ⋵ 𝐎𝐍ˡⁱᵐ.
Proof with auto.
  ord_induction. intros α Hα IH 𝜆 H𝜆 H0.
  assert (H := H𝜆). destruct H as [Ho𝜆 H𝜆eq].
  ord_destruct α.
  - subst. rewrite ordTet_0...
  - destruct Hsuc as [β [Hβ H]]. subst.
    rewrite ordTet_suc... apply ord_pow_is_limord_r...
    apply gt_1_iff_neq_0_1...
    + split... intros H. apply (limord_iff_not_sucord 𝜆)... exists 0...
    + intros H. apply ord_tower_eq_0 in H...
  - rewrite ordTet_limit...
    apply union_of_limords_is_limord. intros x Hx.
    apply ReplAx in Hx as [β [Hβ Hx]]. subst x. apply IH...
Qed.

(** ω指数塔 **)

(* 0层塔 *)
Lemma ω_tower_0 : ω ^^ 0 = ω.
Proof. apply ordTet_0; auto. Qed.

(* 后继层塔 *)
Lemma ω_tower_suc : ∀α ⋵ 𝐎𝐍, ω ^^ α⁺ = ω ^ (ω ^^ α).
Proof. apply ordTet_suc; auto. Qed.

(* 1层塔 *)
Fact ω_tower_1 : ω ^^ 1 = ω ^ ω.
Proof. rewrite pred, ω_tower_suc, ω_tower_0; auto. Qed.

(* 极限层塔 *)
Lemma ω_tower_limit : continuous (Tetration ω).
Proof. apply ordTet_limit; auto. Qed.

(* 指数塔是序数 *)
Lemma ω_tower_ran : ∀α ⋵ 𝐎𝐍, ω ^^ α ⋵ 𝐎𝐍.
Proof. apply ordTet_ran; auto. Qed.
Local Hint Resolve ω_tower_ran : core.

(* 有限层塔递增 *)
Lemma ω_tower_n_ascending : ∀n ∈ ω, ω ^^ n ∈ ω ^^ n⁺.
Proof with nauto.
  intros n Hn. ω_induction n.
  - rewrite ω_tower_suc, <- zero, ω_tower_0...
    apply ω_lt_ω_exp_ω.
  - rewrite ω_tower_suc, ω_tower_suc...
    apply ordExp_preserve_lt...
Qed.

(* 有限层塔单调 *)
Lemma ω_tower_n_monotone : ∀n ∈ ω, ∀m ∈ n, ω ^^ m ∈ ω ^^ n.
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
Lemma ω_tower_n_le_ω : ∀n ∈ ω, ω ⋸ ω ^^ n.
Proof with auto.
  intros n Hn. ω_destruct n; subst.
  - right. rewrite ordTet_0...
  - left. rewrite <- ordTet_0 at 1...
    apply ω_tower_n_monotone... apply suc_has_0...
Qed.

(* 有限层塔不等于任意自然数 *)
Lemma ω_tower_n_neq_nat : ∀ m n ∈ ω, ω ^^ m ≠ n.
Proof with neauto.
  intros m Hm n Hn Heq.
  apply (ord_irrefl ω)... eapply ord_trans_le_lt. auto.
  apply (ω_tower_n_le_ω m)... rewrite Heq...
Qed.

(* 有限层塔单射 *)
Lemma ω_tower_n_injective : ∀ m n ∈ ω, ω ^^ m = ω ^^ n → m = n.
Proof with neauto.
  intros n Hn. ω_induction n; intros k Hk H.
  - ω_destruct k... subst. rename n' into k.
    rewrite ordTet_0, ordTet_suc in H...
    rewrite <- ordExp_1_r in H at 1...
    apply ordExp_cancel in H...
    exfalso. apply (ω_tower_n_neq_nat k Hn' 1)...
  - ω_destruct k; subst.
    + rewrite ordTet_suc, ordTet_0 in H...
      rewrite <- ordExp_1_r in H...
      apply ordExp_cancel in H...
      exfalso. apply (ω_tower_n_neq_nat m Hm 1)...
    + rewrite ordTet_suc, ordTet_suc in H...
      apply ordExp_cancel in H...
      apply IH in H... subst...
Qed.

(* 有限层塔的元素小于其以ω为底的幂 *)
Lemma ω_tower_n_upstairs : ∀n ∈ ω, ∀α ∈ ω ^^ n, α ∈ ω ^ α.
Proof with neauto; try congruence.
  intros n Hn. ω_induction n; intros x Hx.
  + destruct (classic (x = 0)). {
      subst. rewrite ordExp_0_r, pred, pred...
    }
    rewrite <- zero, ω_tower_0 in Hx.
    apply ordExp_enlarge_lt...
  + destruct (classic (x ∈ ω ^^ m)). apply IH...
    assert (Hox: x ⋵ 𝐎𝐍). apply (ord_is_ords (ω ^^ m⁺))...
    rewrite ω_tower_suc in Hx...
    apply ord_le_iff_not_gt in H as []...
    apply (ordExp_preserve_lt ω) in H...
    eapply ord_trans...
Qed.

(* ε₀定义为ω层塔 *)
Definition ε₀ := ω ^^ ω.

(* ε₀是有限层塔序列的上界 *)
Remark ε₀_is_sup : ε₀ = sup{ω ^^ n | n ∊ ω}.
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
Lemma ε₀_has_tower_n : ∀n ∈ ω, ω ^^ n ∈ ε₀.
Proof with nauto.
  intros n Hn. rewrite ε₀_is_sup.
  eapply (FUnionI _ _ n⁺)... apply ω_inductive...
  apply ω_tower_n_ascending...
Qed.

(* ε₀里有任意有限层塔里的元素 *)
Lemma ε₀_has_those_of_tower_n : ∀n ∈ ω, ∀α ∈ ω ^^ n, α ∈ ε₀.
Proof with eauto.
  intros n Hn α Hα. eapply ord_trans...
  apply ε₀_has_tower_n...
Qed.
Local Notation ε₀I := ε₀_has_those_of_tower_n.

(* ε₀的任意元素都在某有限层塔里 *)
Lemma ε₀_has_only_those_of_tower_n : ∀α ∈ ε₀, ∃n ∈ ω, α ∈ ω ^^ n.
Proof.
  intros α Hα. rewrite ε₀_is_sup in Hα.
  apply FUnionE in Hα; auto.
Qed.
Local Notation ε₀E := ε₀_has_only_those_of_tower_n.

(* ε₀里有且只有那些有限层塔里的元素 *)
Fact ε₀_iff_of_tower_n : ∀α ⋵ 𝐎𝐍, α ∈ ε₀ ↔ ∃n ∈ ω, α ∈ ω ^^ n.
Proof.
  split. apply ε₀E.
  intros [n [Hn Hα]]. apply (ε₀I n); auto.
Qed.

(* ε₀是极限序数 *)
Lemma ε₀_is_limord : ε₀ ⋵ 𝐎𝐍ˡⁱᵐ.
Proof with nauto.
  rewrite ε₀_is_sup. apply union_of_limords_is_limord.
  intros x Hx. apply ReplAx in Hx as [n [Hn H]]. subst.
  apply ord_tower_is_limord...
Qed.
Local Hint Resolve ε₀_is_limord : core.

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

Module Import EpsilonNumber.

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
    eapply ω_tower_n_upstairs...
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
Lemma ε_number_has_ω_tower_n : ∀n ∈ ω, ∀ε ⋵ ε_number, ω ^^ n ∈ ε.
Proof with neauto.
  intros n Hn. ω_induction n; intros ε [Hε Heq].
  - rewrite <- zero, ω_tower_0, <- Heq.
    apply ordExp_enlarge...
    apply gt_1_iff_neq_0_1... split...
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
  eapply ord_trans... apply ε_number_has_ω_tower_n... split...
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

End EpsilonNumber.

Module Countability.
Import ZFC.Lib.Choice ZFC.Lib.OrdinalCountability.
Open Scope OrdArith_scope.

(* 有限层塔是可数无穷 *)
Lemma ω_tower_n_cntinf : AC_II → ∀n ∈ ω, |ω ^^ n| = ℵ₀.
Proof with nauto.
  intros AC2 n Hn. ω_induction n. rewrite ordTet_0...
  rewrite ordTet_suc, ordExp_limit...
  2: apply ord_tower_is_limord...
  2: apply ω_tower_n_neq_nat...
  apply (add_one_member_to_funion 0). rewrite ordExp_0_r...
  apply countableI1, nat_finite...
  apply countable_union_of_cntinf...
  - exists ω. apply ReplAx.
    exists 1. split. 2: rewrite ordExp_1_r...
    apply SepI. 2: apply SingNI...
    eapply ord_trans_lt_le. auto.
    apply embed_ran. apply ω_tower_n_le_ω...
  - apply countableI2, eqnum_repl.
    + apply CardAx1. apply remove_one_member_from_cntinf, IH.
    + intros x1 H1 x2 H2 H. apply SepE1 in H1, H2.
      apply ordExp_cancel in H... 1-2: apply (ord_is_ords (ω ^^ m))...
  - intros A H. apply ReplAx in H as [α [Hα H]]. subst.
    apply SepE in Hα as [Hα Hne]. apply SingNE in Hne.
    assert (Hoα: α ⋵ 𝐎𝐍). apply (ord_is_ords (ω ^^ m))...
    apply ord_pow_cntinf... eapply dominate_rewrite_r.
    apply CardAx1. apply IH.
    apply dominate_sub. apply ord_lt_iff_psub...
Qed.

(* ε₀是可数无穷 *)
Theorem ε₀_cntinf : AC_II → |ε₀| = ℵ₀.
Proof with nauto.
  intros AC2. rewrite ε₀_is_sup.
  apply countable_union_of_cntinf...
  - exists ω. apply ReplAx. exists 0. split... rewrite ordTet_0...
  - apply countableI2, eqnum_repl. reflexivity.
    apply ω_tower_n_injective.
  - intros A H. apply ReplAx in H as [n [Hn H]]. subst.
    apply ω_tower_n_cntinf...
Qed.

End Countability.
