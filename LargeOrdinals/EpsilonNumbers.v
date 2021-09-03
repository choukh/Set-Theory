(** Coq coding by choukh, Sep 2021 **)

Require Import ZFC.Elements.EST8_8.
Import OrdinalClass VeblenFixedPoint EpsilonNumber.

Local Hint Resolve
  ordAdd_ran ordMul_ran ordExp_ran ordTet_ran ε_operative : core.

(* continue from EST8_8 *)

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
    eapply (ord_trans _ _ _ (ε β))...
    apply monotone_operation_ascending... apply ε_normal.
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
  rewrite <- ordExp_add, ordAdd_1_absorption...
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
(* εtn := ε-tower of n stairs *)
(* 有限层ε塔 := 以任意ε数为底的有限层指数塔 *)

(* 有限层ε塔随层数递增 *)
Lemma εtn_ascending : ∀n ∈ ω, ∀α ⋵ 𝐎𝐍, ε α ^^ n ∈ ε α ^^ n⁺.
Proof with neauto; try congruence.
  intros n Hn. ω_induction n; intros α Hα.
  - rewrite ordTet_suc, <- zero, ordTet_0... apply ordExp_enlarge...
  - rewrite ordTet_suc, ordTet_suc... apply ordExp_preserve_lt...
Qed.

(* 有限层ε塔大于ω *)
Lemma εtn_has_ω : ∀n ∈ ω, ∀α ⋵ 𝐎𝐍, ω ∈ ε α ^^ n.
Proof with auto.
  intros n Hn α Hα. ω_induction n.
  - rewrite ordTet_0... apply ε_has_ω...
  - eapply ord_trans. auto. apply IH. apply εtn_ascending...
Qed.

(* supεtn := supremum of ε-tower of n stairs *)
(* 有限层ε塔上界 := 以任意ε数为底的有限层指数塔序列的上界 *)
Definition supεtn := λ α, sup {ε α ^^ n | n ∊ ω}.

(* 有限层ε塔上界是极限序数 *)
Lemma soεtn_is_limord : supεtn :ᶜ 𝐎𝐍 ⇒ 𝐎𝐍ˡⁱᵐ.
Proof.
  intros α Hα. apply union_of_limords_is_limord.
  intros x Hx. apply ReplAx in Hx as [n [Hn Hx]]. subst.
  apply ord_tower_is_limord; auto.
Qed.
Local Hint Resolve soεtn_is_limord : core.

(* 有限层ε塔上界是序数 *)
Corollary supεtn_is_ord : ∀α ⋵ 𝐎𝐍, supεtn α ⋵ 𝐎𝐍.
Proof. apply soεtn_is_limord. Qed.
Local Hint Resolve supεtn_is_ord : core.

(* 有限层ε塔上界不等于0 *)
Lemma soεtn_neq_0 : ∀α ⋵ 𝐎𝐍, supεtn α ≠ 0.
Proof with nauto.
  intros α Hα. eapply EmptyNI. exists ω.
  apply (FUnionI _ _ 0)...
  rewrite ordTet_0... apply ε_has_ω...
Qed.
Local Hint Resolve soεtn_neq_0 : core.

(* ε幂相乘的吸收律 *)
Lemma ε_pow_mul_absorption :
  ∀ α β ⋵ 𝐎𝐍, ∀n ∈ ω, ω ⋸ β → ε α ^ n ⋅ ε α ^ β = ε α ^ β.
Proof with auto.
  intros α Hα β Hβ n Hn Hωβ.
  rewrite <- epsilon, ordExp_exp, ordExp_exp, <- ordExp_add...
  f_equal. rewrite <- ordMul_distr... f_equal.
  apply ordAdd_n_absorption...
Qed.

(* 有限层ε塔上界是ε数 *)
Theorem supεtn_is_ε_number : ∀α ⋵ 𝐎𝐍, supεtn α ⋵ ε_number.
Proof with neauto.
  intros α Hα. split... ext.
  - rewrite ordExp_limit in H...
    apply FUnionE in H as [β [Hβ Hx]].
    apply FUnionE in Hβ as [n [Hn Hβ]].
    apply (FUnionI _ _ n⁺)... apply ω_inductive...
    rewrite ordTet_suc... eapply ord_trans... auto.
    assert (Hoβ: β ⋵ 𝐎𝐍). eapply ord_is_ords; revgoals...
    eapply ord_trans_le_lt. auto.
    apply ordExp_preserve_le_l; revgoals.
    left. apply ε_has_ω. apply Hα. 1-3:auto.
    apply ordExp_preserve_lt...
  - apply FUnionE in H as [n [Hn Hx]].
    rewrite ordExp_limit... eapply FUnionI.
    eapply FUnionI. apply ω_inductive, Hn. apply εtn_ascending...
    generalize dependent Hx. generalize dependent x.
    apply ord_le_iff_sub...
    ω_induction n.
    + rewrite ordTet_0 in *... rewrite epsilon...
    + rewrite ordTet_suc in *...
      rewrite <- (epsilon α) at 1 5... rewrite ordExp_exp...
      apply ordExp_preserve_le_r... 1-2:auto.
      rewrite <- (epsilon α) at 3 7... rewrite ordExp_exp...
      eapply ordMul_preserve_le_r in IH.
      4: apply (ε_is_limord α)... 2-3:auto.
      rewrite <- (epsilon α) in IH at 3 7...
      rewrite <- ordExp_add in IH...
      ω_destruct m.
      * subst. rewrite ordTet_0 in *...
        eapply ord_trans_le. auto. apply IH.
        apply ordExp_preserve_le_r... left.
        rewrite <- ordMul_2_r... apply ordMul_preserve_lt...
      * cut (ε α + ε α ^^ m = ε α ⋅ ε α ^^ m). congruence.
        subst. rename n' into m. rewrite ordTet_suc...
        rewrite <- (epsilon α) at 1 2...
        rewrite ordExp_exp, ω_pow_add_absorption...
        rewrite <- (ordExp_1_r (ε α)) at 3...
        rewrite ε_pow_mul_absorption, <- ordExp_exp, epsilon...
        left. apply εtn_has_ω... auto. apply ordMul_enlarge...
        eapply ord_trans. auto. apply embed_ran. apply εtn_has_ω...
Qed.
