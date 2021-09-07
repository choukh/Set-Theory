(** Coq coding by choukh, Aug 2021 **)

Require Import ZFC.Lib.ChoiceFacts.
Require Import ZFC.Lib.FuncFacts.
Require Import ZFC.Elements.EST8_7.
Require Export ZFC.Lib.OrdFacts.

Local Hint Resolve ordAdd_ran ordMul_ran ordExp_ran : core.

(*** 序数的可数性 ***)

(* 可数非零极限序数是可数无穷 *)
Theorem countable_limit_ordinal_cntinf :
  ∀𝜆 ⋵ 𝐎𝐍ˡⁱᵐ, 𝜆 ≠ ∅ → countable 𝜆 → 𝜆 ≈ ω.
Proof with auto.
  intros 𝜆 H𝜆 Hne Hcnt.
  apply limord_is_inford in H𝜆 as [H𝜆 Hinf]...
  apply countable_iff in Hcnt as []... exfalso...
Qed.

(* 可数集除去任意多个元素仍是可数集 *)
Lemma remove_members_from_cnt :
  ∀ A B, countable A → countable (A - B).
Proof.
  intros A B Hcnt. eapply dominate_trans. 2: apply Hcnt.
  apply dominate_sub. auto.
Qed.

(* 序数可数如果其后继可数 *)
Corollary ord_cnt_if_suc_cnt :
  ∀α ⋵ 𝐎𝐍, countable α⁺ → countable α.
Proof with auto.
  intros α Hα Hcnt. rewrite <- (add_one_member_then_remove α α).
  apply remove_members_from_cnt... apply ord_irrefl...
Qed.

(* 往可数无穷加入可数多个元素仍是可数无穷 *)
Lemma add_countably_many_members_to_cntinf :
  ∀ A B, |A| = ℵ₀ → countable B → |A ∪ B| = ℵ₀.
Proof with nauto.
  intros A B Hcinf Hcnt. rewrite <- ex2_11_2.
  apply CardAx1, cardAdd_disjoint_iff.
  apply binter_comp_empty. rewrite Hcinf.
  apply cardLe_antisym.
  - rewrite <- cardAdd_aleph0_aleph0 at 2.
    apply cardAdd_preserve_le'. apply cardLe_iff.
    apply remove_members_from_cnt...
  - rewrite <- cardAdd_0_r at 1. 2: exists ω...
    apply cardAdd_preserve_le'. repeat split...
    apply dominate_sub. intros x Hx. exfalso0.
Qed.

(* 可数无穷除去一个元素仍是可数无穷 *)
Lemma remove_one_member_from_cntinf :
  ∀ a A, |A| = ℵ₀ → |A - {a,}| = ℵ₀.
Proof with eauto; try congruence.
  intros a A Hcinf.
  destruct (classic (a ∈ A)) as [|Ha'].
  2: rewrite remove_no_member...
  symmetry. apply CardAx1.
  symmetry in Hcinf. apply CardAx1 in Hcinf as [f Hbi].
  assert (H' := Hbi). apply bijection_is_func in H' as [Hf [Hi Hr]].
  assert (H' := Hf). destruct H' as [_ [Hd _]].
  set (Func ω (A - {a,}) (λ n, match (ixm (n ∈ f⁻¹[a])) with
    | inl _ => f[n]
    | inr _ => f[n⁺]
  end)) as g.
  exists g. apply meta_bijection.
  - intros n Hn. destruct (ixm (n ∈ f⁻¹[a])).
    + apply SepI. eapply ap_ran...
      apply SingNI. intros Hfn.
      rewrite <- Hfn, inv_dom_reduction in i...
      apply (nat_irrefl n)...
    + apply SepI. eapply ap_ran... apply ω_inductive...
      apply SingNI. intros Hfn.
      rewrite <- Hfn, inv_dom_reduction in n0...
      rewrite Hd. apply ω_inductive...
  - intros n1 H1 n2 H2 Heq.
    destruct (ixm (n1 ∈ f⁻¹[a]));
    destruct (ixm (n2 ∈ f⁻¹[a])).
    + apply injectiveE in Heq...
    + apply injectiveE in Heq... 2: rewrite Hd; apply ω_inductive...
      exfalso. rewrite Heq in i. apply n. eapply nat_trans.
      eapply ap_ran... apply bijection_is_func, inv_bijection...
      2: apply i. apply BUnionI2...
    + apply injectiveE in Heq... 2: rewrite Hd; apply ω_inductive...
      exfalso. rewrite <- Heq in i. apply n. eapply nat_trans.
      eapply ap_ran... apply bijection_is_func, inv_bijection...
      2: apply i. apply BUnionI2...
    + apply injectiveE in Heq... 2-3: rewrite Hd; apply ω_inductive...
      apply suc_injective in Heq...
  - intros y Hy. apply SepE in Hy as [Hy Hy']. apply SingNE in Hy'.
    assert (Hyw: (f⁻¹)[y] ∈ ω). {
      eapply ap_ran... apply bijection_is_func, inv_bijection...
    }
    assert (Haw: (f⁻¹)[a] ∈ ω). {
      eapply ap_ran... apply bijection_is_func, inv_bijection...
    }
    destruct (classic (f⁻¹[y] ∈ f⁻¹[a])).
    + exists (f⁻¹[y]). split... destruct (ixm (f⁻¹[y] ∈ f⁻¹[a]))...
      rewrite inv_ran_reduction...
    + set (f⁻¹[y]) as n. assert (Hn: n ∈ ω)...
      ω_destruct n. {
        apply le_iff_not_gt in H0 as []...
        - rewrite H1 in H0. exfalso0.
        - apply injectiveE in H0... apply inv_injective.
          apply Hbi. 1-2: rewrite inv_dom...
      }
      exists n. split... destruct (ixm (n ∈ f⁻¹[a])).
      * apply le_iff_not_gt in H0 as []...
        rewrite Heq in H0. exfalso. apply (ω_not_dense n)...
        apply injectiveE in H0... apply inv_injective.
        apply Hbi. 1-2: rewrite inv_dom...
      * rewrite <- Heq. rewrite inv_ran_reduction...
Qed.

(* 往作为可数无穷的集族并中加入一个替代目标后仍是可数无穷 *)
Lemma add_one_member_to_funion : ∀ a F A, countable (F a) →
  |⋃ {F x | x ∊ A - {a,}}| = ℵ₀ → |⋃ {F x | x ∊ A}| = ℵ₀.
Proof with auto.
  intros * Hcnt Heq.
  destruct (classic (a ∈ A)) as [|Ha'].
  2: rewrite <- (remove_no_member A a)...
  rewrite <- (remove_one_member_then_return A a)...
  rewrite repl_bunion_distr, union_bunion_distr.
  rewrite repl_single, union_single.
  apply add_countably_many_members_to_cntinf...
Qed.

(* 可数集的替代可数 *)
Lemma repl_of_cnt_cnt : AC_II → ∀ F A, countable A → countable {F x | x ∊ A}.
Proof with auto.
  intros AC2 F A Hcnt. eapply dominate_trans. 2: apply Hcnt.
  set (Func A {F x | x ∊ A} F) as f.
  apply AC_II_to_IV, AC_IV_to_III, AC_III_to_I in AC2.
  apply (domain_of_surjection_dominate_range AC2 _ _ f).
  apply meta_surjection.
  - intros x Hx. eapply ReplI...
  - intros y Hy. apply ReplAx...
Qed.

(* 可数无穷序数非空 *)
Lemma cntinf_ord_neq_0 : ∀α ⋵ 𝐎𝐍, |α| = ℵ₀ → α ≠ 0.
Proof.
  intros α Hα Hcinf H0. subst. symmetry in Hcinf.
  rewrite pred, card_of_empty, card_eq_0 in Hcinf; nauto.
Qed.
Local Hint Resolve cntinf_ord_neq_0 : core.

(* 比可数序数小的序数可数 *)
Lemma ord_lt_cnt_cnt :
  ∀α ⋵ 𝐎𝐍, countable α → ∀β ∈ α, countable β.
Proof with eauto.
  intros α Hoα Hcnt β Hβ.
  assert (Hoβ: β ⋵ 𝐎𝐍). apply (ord_is_ords α)...
  eapply dominate_trans. apply dominate_sub.
  apply ord_lt_iff_psub; revgoals... apply Hcnt.
Qed.

(* 可数无穷序数的后继是可数无穷 *)
Theorem ord_suc_cntinf : AC_II → ∀α ⋵ 𝐎𝐍, |α| = ℵ₀ → |α⁺| = ℵ₀.
Proof with neauto.
  intros AC2 α Hα Hcinf.
  apply add_countably_many_members_to_cntinf...
  apply countableI1. apply single_finite.
Qed.

(* 可数无穷序数的可数次后继是可数无穷 *)
Theorem ord_sum_cntinf : AC_II → ∀α ⋵ 𝐎𝐍, |α| = ℵ₀ →
  ∀β ⋵ 𝐎𝐍, countable β → |α + β| = ℵ₀.
Proof with neauto.
  intros AC2 α Hα Hcinf. ord_induction.
  intros β Hβ IH Hcnt. ord_destruct β.
  - subst. rewrite ordAdd_0_r...
  - destruct Hsuc as [γ [Hγ Heq]]. subst.
    destruct (classic (γ = 0)) as [|Hγ0]. {
      subst. rewrite ordAdd_1_r... apply ord_suc_cntinf...
    }
    rewrite ordAdd_suc... apply ord_suc_cntinf...
    apply IH... rewrite <- (add_one_member_then_remove γ γ).
    apply remove_members_from_cnt... apply ord_irrefl...
  - rewrite ordAdd_limit...
    apply countable_union_of_cntinf...
    + exists α. apply ReplAx. exists 0. split.
      apply ord_neq_0_gt_0... rewrite ordAdd_0_r...
    + apply repl_of_cnt_cnt...
    + intros A H. apply ReplAx in H as [γ [Hγ H]]. subst.
      apply IH... eapply ord_lt_cnt_cnt...
Qed.

(* 可数无穷序数的非零可数乘积是可数无穷 *)
Theorem ord_prd_cntinf : AC_II → ∀α ⋵ 𝐎𝐍, |α| = ℵ₀ → 
  ∀β ⋵ 𝐎𝐍, β ≠ 0 → countable β → |α ⋅ β| = ℵ₀.
Proof with neauto.
  intros AC2 α Hα Hcinf. ord_induction.
  intros β Hβ IH Hβ0 Hcnt. ord_destruct β.
  - exfalso...
  - destruct Hsuc as [γ [Hγ Heq]]. subst.
    destruct (classic (γ = 0)) as [|Hγ0]. {
      subst. rewrite ordMul_1_r...
    }
    rewrite ordMul_suc... apply ord_sum_cntinf...
    + apply IH... rewrite <- (add_one_member_then_remove γ γ).
      apply remove_members_from_cnt... apply ord_irrefl...
    + apply countableI2. apply CardAx1...
  - clear H0. rewrite ordMul_limit...
    apply (add_one_member_to_funion 0). rewrite ordMul_0_r...
    apply countableI1...
    apply countable_union_of_cntinf...
    + exists α. apply ReplAx.
      exists 1. split. 2: rewrite ordMul_1_r...
      apply SepI... apply sucord_in_limord... apply SingNI...
    + apply repl_of_cnt_cnt, remove_members_from_cnt...
    + intros A H. apply ReplAx in H as [γ [Hγ H]]. subst.
      apply SepE in Hγ as [Hγ Hγ0]. apply SingNE in Hγ0.
      apply IH... eapply ord_lt_cnt_cnt...
Qed.

(* 可数无穷序数的非零可数次方是可数无穷 *)
Theorem ord_pow_cntinf : AC_II → ∀α ⋵ 𝐎𝐍, |α| = ℵ₀ → 
  ∀β ⋵ 𝐎𝐍, β ≠ 0 → countable β → |α ^ β| = ℵ₀.
Proof with neauto.
  intros AC2 α Hα Hcinf. ord_induction.
  intros β Hβ IH Hβ0 Hcnt. ord_destruct β.
  - exfalso...
  - destruct Hsuc as [γ [Hγ Heq]]. subst.
    destruct (classic (γ = 0)) as [|Hγ0]. {
      subst. rewrite ordExp_1_r...
    }
    rewrite ordExp_suc... apply ord_prd_cntinf...
    + apply IH... rewrite <- (add_one_member_then_remove γ γ).
      apply remove_members_from_cnt... apply ord_irrefl...
    + apply countableI2. apply CardAx1...
  - clear H0. rewrite ordExp_limit...
    apply (add_one_member_to_funion 0). rewrite ordExp_0_r...
    apply countableI1. apply nat_finite...
    apply countable_union_of_cntinf...
    + exists α. apply ReplAx.
      exists 1. split. 2: rewrite ordExp_1_r...
      apply SepI... apply sucord_in_limord... apply SingNI...
    + apply repl_of_cnt_cnt, remove_members_from_cnt...
    + intros A H. apply ReplAx in H as [γ [Hγ H]]. subst.
      apply SepE in Hγ as [Hγ Hγ0]. apply SingNE in Hγ0.
      apply IH... eapply ord_lt_cnt_cnt...
Qed.
