(** Based on "Elements of Set Theory" Chapter 8 Part 2 **)
(** Coq coding by choukh, Feb 2021 **)

Require Import ZFC.lib.Class.
Require Export ZFC.EST8_1.
Import OrdinalClass.

(*** EST第八章2：序数操作的性质，Veblen不动点定理 ***)

(* ex8_3_a 单调操作保序 *)
Fact monotone_operation_preserve_order :
  ∀ F, F:ᶜ 𝐎𝐍 ⇒ 𝐎𝐍 → monotone F →
  ∀ α β ⋵ 𝐎𝐍, α ∈ β ↔ F α ∈ F β.
Proof with auto.
  intros F HF Hmono α Hoα β Hoβ. split. apply Hmono...
  intros Hlt. destruct (classic (α = β)) as [|Hnq]. {
    exfalso. subst. apply (ord_irrefl (F β))... apply HF...
  }
  apply ord_connected in Hnq as []...
  exfalso. apply Hmono in H...
  apply (ord_not_lt_gt (F α) (HF α Hoα) (F β)); auto; apply HF...
Qed.

(* ex8_4 规范操作在极限处的值是极限 *)
Fact normal_operation_limit_is_limit :
  ∀ F, F:ᶜ 𝐎𝐍 ⇒ 𝐎𝐍 → normal F →
  ∀𝜆 ⋵ 𝐎𝐍ˡⁱᵐ, 𝜆 ≠ ∅ → F 𝜆 ⋵ 𝐎𝐍ˡⁱᵐ.
Proof with auto.
  intros F HF [Hmono Hcon] 𝜆 Hlim Hne.
  rewrite Hcon... split. {
    apply union_of_ords_is_ord. intros x Hx.
    apply ReplAx in Hx as [α [Hα HFα]]. subst x.
    apply HF. apply (ord_is_ords 𝜆)... apply Hlim.
  }
  apply ExtAx. split; intros Hx.
  - apply FUnionE in Hx as [α [Hα HFα]].
    apply UnionAx. exists (F α). split...
    eapply FUnionI... apply sucord_in_limord...
    apply Hα. apply Hmono... apply ord_suc_is_ord.
    apply (ord_is_ords 𝜆)... apply Hlim.
  - apply UnionAx in Hx as [α [Hα Hx]].
    apply FUnionE in Hα as [β [Hβ HFβ]].
    eapply FUnionI... apply Hβ. eapply ord_trans; eauto.
    apply HF. apply (ord_is_ords 𝜆)... apply Hlim.
Qed.

(* 规范操作的定义域有最大元 *)
Theorem normal_operation_domain_has_maximum :
  ∀ F, F:ᶜ 𝐎𝐍 ⇒ 𝐎𝐍 → normal F → ∀β ⋵ 𝐎𝐍, F 0 ∈ β →
  ∃γ ⋵ 𝐎𝐍, ε_maximum γ (Domain F (RangeAmong F β⁺)).
Proof with eauto.
  intros F HF [Hmono Hcon] β Hoβ Hlt.
  set (λ y, ∃α ⋵ 𝐎𝐍, F α = y) as C.
  assert (Hsur: F :ᶜ 𝐎𝐍 ⟹ C). {
    split. intros ξ Hoξ. exists ξ. split... intros ξ H...
  }
  assert (Hsub: C ⫃ 𝐎𝐍). {
    intros ξ [α [Hoα Heq]]. subst ξ. apply HF...
  }
  assert (Hinj: class_injective F 𝐎𝐍). {
    eapply monotone_operation_injective...
  }
  assert (Hran: ∀x ∈ RangeAmong F β⁺, x ⋵ C). {
    intros ξ Hξ. apply SepE2 in Hξ...
  }
  set (Domain F (RangeAmong F β⁺)) as γ.
  assert (Hoγ: γ ⋵ 𝐎𝐍). {
    apply transitive_set_well_ordered_by_epsilon_is_ord.
    - intros x y Hxy Hy.
      eapply domain_spec in Hy as [Hoy HFy]...
      assert (Hox: x ⋵ 𝐎𝐍). eapply ord_is_ords...
      eapply domain_spec... split...
      apply SepI; [apply SepE1 in HFy|exists x; split]...
      eapply ord_trans; revgoals... apply Hmono...
    - apply ords_woset. intros x Hx. eapply domain_spec...
  }
  destruct (sucord_or_limord γ) as [|Hlim]...
  - destruct H as [μ [Hoμ Heq]]. rewrite Heq.
    exists μ. split... split... intros x Hx.
    apply ord_leq_iff_lt_suc... eapply ord_is_ords; revgoals...
  - exfalso. destruct (classic (γ = 0)) as [|Hne].
    + eapply EmptyNI... exists 0.
      eapply domain_spec... split... apply SepI.
      apply BUnionI1... exists 0. split...
    + apply (ord_irrefl γ)...
      eapply domain_spec... split...
      apply SepI; [|exists γ; split]...
      apply ord_leq_iff_lt_suc... apply HF...
      rewrite Hcon... apply ord_sup_correct.
      * intros x Hx. apply ReplAx in Hx as [α [Hα Heq]].
        subst x. apply HF. eapply ord_is_ords...
      * split... intros x Hx.
        apply ReplAx in Hx as [α [Hα Heq]]. subst x.
        eapply domain_spec in Hα as [Hα HFα]...
        apply SepE1 in HFα. apply ord_leq_iff_lt_suc... apply HF...
Qed.

(* 序数集上界的规范操作等于序数集规范操作的上界 *)
Theorem operation_of_sup_eq_sup_of_operation :
  ∀ F, F:ᶜ 𝐎𝐍 ⇒ 𝐎𝐍 → normal F → ∀ S, S ⪽ 𝐎𝐍 → S ≠ ∅ →
  F (sup S) = sup (Range F S).
Proof with eauto; try congruence.
  intros F HF [Hmono Hcon] S Hos Hne.
  assert (HoS: sup S ⋵ 𝐎𝐍). apply union_of_ords_is_ord...
  assert (HoF: F (sup S) ⋵ 𝐎𝐍). apply HF...
  assert (HosR: Range F S ⪽ 𝐎𝐍). {
    intros x Hx. apply ReplAx in Hx as [α [Hoα Heq]].
    subst x. apply HF. apply Hos...
  }
  assert (HoR: sup (Range F S) ⋵ 𝐎𝐍). {
    apply union_of_ords_is_ord...
  }
  apply sub_antisym; apply ord_leq_iff_sub; revgoals...
  - apply ord_sup_correct... split...
    intros ξ Hξ. apply ReplAx in Hξ as [α [Hoα Heq]].
    subst ξ. apply ord_sup_is_ub in Hos as [Ho Hle].
    apply Hle in Hoα as []; [left|right]... apply Hmono...
  - destruct (sucord_or_limord (sup S)) as [|Hlim].
    + apply ord_sup_is_ub...
    + apply ord_sup_correct... eapply ReplI.
      apply sup_of_ords_is_suc_impl_in_ords...
    + destruct (classic (sup S = ∅)). {
        rewrite H. apply union_empty_iff in H as []...
        apply ord_sup_is_ub... rewrite H.
        eapply ReplI. apply SingI.
      }
      rewrite Hcon... apply ord_sup_correct.
      * intros x Hx. apply ReplAx in Hx as [α [Hα Heq]].
        subst x. apply HF. apply (ord_is_ords (sup S))...
      * split... intros ξ Hξ. left.
        apply ReplAx in Hξ as [α [Hα Heq]]. subst ξ.
        apply UnionAx in Hα as [γ [Hγ Hα]].
        apply UnionAx. exists (F γ). split.
        eapply ReplI... apply Hmono...
Qed.

(* ex8_5 单调操作的值不小于原值 *)
Lemma monotone_operation_leq :
  ∀ F, F:ᶜ 𝐎𝐍 ⇒ 𝐎𝐍 → monotone F → ∀α ⋵ 𝐎𝐍, α ⋸ F α.
Proof with auto.
  intros F HF Hmono. unfold all_in_class, all.
  apply transfinite_induction_schema_on_ordinals.
  intros α Hoα IH. apply ord_leq_iff_not_gt... apply HF...
  intros HFα. apply Hmono in HFα as HFFα...
  apply IH in HFα as [].
  eapply ord_not_lt_gt; revgoals; eauto; try repeat apply HF...
  eapply ord_not_lt_self; revgoals; eauto; try repeat apply HF...
Qed.

Module VeblenFixedPoint.
Import 𝐎𝐍Operation.

(* 序数操作的不动点 *)
Definition fixed_point := λ F α, α ⋵ 𝐎𝐍 ∧ F α = α.

(* Veblen不动点定理：规范操作存在任意大的不动点 *)
Theorem Veblen_fixed_point : ∀ F, F:ᶜ 𝐎𝐍 ⇒ 𝐎𝐍 → normal F →
  ∀β ⋵ 𝐎𝐍, ∃ γ, fixed_point F γ ∧ β ⋸ γ.
Proof with neauto; try congruence.
  intros F HF [Hmono Hcon] β Hoβ.
  eapply monotone_operation_leq in Hoβ as H...
  destruct H as [Heq|Hlt]; revgoals. exists β. repeat split...
  set (Operation β F) as f.
  set {f | n ∊ ω} as S.
  assert (Hne: S ≠ ∅). {
    apply EmptyNI. exists (f 0). eapply ReplI...
  }
  assert (Hos: S ⪽ 𝐎𝐍). {
    intros x Hx. apply ReplAx in Hx as [n [Hn Hfn]]. subst x.
    apply operation_operative... apply ω_is_ords...
  }
  exists (sup S). repeat split.
  - apply union_of_ords_is_ord...
  - rewrite operation_of_sup_eq_sup_of_operation; revgoals... split...
    apply ExtAx. split; intros Hx.
    + apply FUnionE in Hx as [α [Hα Hx]].
      apply ReplAx in Hα as [n [Hn Hfn]]. subst α.
      apply UnionAx. exists (f n⁺). split.
      eapply ReplI... apply ω_inductive...
      unfold f. rewrite operation_suc... apply ω_is_ords...
    + apply UnionAx in Hx as [y [Hy Hx]].
      apply ReplAx in Hy as [n [Hn Hfn]]. subst y.
      apply (FUnionI _ _ (f n)). eapply ReplI...
      assert (Hof: f n ⋵ 𝐎𝐍). {
        apply operation_operative... apply ω_is_ords...
      }
      eapply monotone_operation_leq in Hof as H...
      destruct H... eapply ord_trans... apply HF...
  - apply ord_sup_is_ub...
    apply ReplAx. exists 0. split...
    unfold f. rewrite operation_0...
Qed.

(* ex8_7 规范操作存在比指定序数大的最小不动点 *)
Corollary ex_least_fixed_point :
  ∀ F, F:ᶜ 𝐎𝐍 ⇒ 𝐎𝐍 → normal F →
  ∀β ⋵ 𝐎𝐍, ∃ γ, fixed_point F γ ∧ β ⋸ γ ∧
    ∀ ξ, fixed_point F ξ → β ⋸ ξ → γ ⋸ ξ.
Proof with eauto.
  intros F HF Hnml β Hoβ.
  eapply Veblen_fixed_point in Hoβ as [γ [[Hoγ HFγ] Hβγ]]...
  set {ξ ∊ γ⁺ | λ ξ, F ξ = ξ ∧ β ⋸ ξ} as Ω.
  pose proof (ords_woset Ω) as [_ Hmin]. {
    intros ξ Hξ. apply SepE1 in Hξ.
    apply (ord_is_ords γ⁺)...
  }
  pose proof (Hmin Ω) as [μ [Hμ Hmμ]]... {
    exists γ. apply SepI...
  }
  apply SepE in Hμ as [Hμ [HFμ Hβμ]].
  exists μ. repeat split... apply (ord_is_ords γ⁺)...
  intros ξ [Hoξ HFξ] Hβξ.
  destruct (classic (ξ = γ⁺)) as [|Hnq]. left. congruence.
  apply ord_connected in Hnq as [Hlt|Hne]...
  - assert (Hξ: ξ ∈ Ω). apply SepI...
    apply Hmμ in Hξ as []... apply binRelE3 in H...
  - left. eapply ord_trans...
Qed.

(* 不动点类无界 *)
Corollary fixed_point_class_unbounded :
  ∀ F, F:ᶜ 𝐎𝐍 ⇒ 𝐎𝐍 → normal F → unbounded (fixed_point F).
Proof with eauto.
  intros F HF Hnml α Hoα.
  assert (Hoα': α⁺ ⋵ 𝐎𝐍)...
  eapply ex_least_fixed_point in Hoα' as [β [[Hoβ HFβ] [Hle _]]]...
  exists β. repeat split... destruct Hle.
  eapply ord_trans... rewrite <- H... 
Qed.
Local Hint Resolve fixed_point_class_unbounded : core.

(* 不动点类是序数类的子类 *)
Lemma fixed_point_class_sub_on :
  ∀ F, F:ᶜ 𝐎𝐍 ⇒ 𝐎𝐍 → fixed_point F ⫃ 𝐎𝐍.
Proof.
  intros F HF α [Hoα HFα]. rewrite <- HFα.
  apply HF. apply Hoα.
Qed.
Local Hint Resolve fixed_point_class_sub_on : core.

Import 𝐎𝐍Separation.

(* 不动点的枚举操作 *)
Definition FixedPoint := λ F, Enumerate (fixed_point F).

(* 不动点的枚举操作是单调的 *)
Lemma fixed_point_monotone :
  ∀ F, F:ᶜ 𝐎𝐍 ⇒ 𝐎𝐍 → normal F → monotone (FixedPoint F).
Proof. intros F HF Hnml. apply enum_monotone; auto. Qed.

(* 不动点的枚举操作是连续的 *)
Lemma fixed_point_continuous :
  ∀ F, F:ᶜ 𝐎𝐍 ⇒ 𝐎𝐍 → normal F → continuous (FixedPoint F).
Proof with eauto; try congruence.
  intros F HF Hnml.
  apply (monotone_operation_continuous_if_range_closed _ (fixed_point F))...
  apply enum_onto_class... apply fixed_point_monotone...
  intros A Hne HA. split.
  - apply union_of_ords_is_ord.
    intros x Hx. apply HA...
  - assert (Hos: A ⪽ 𝐎𝐍). intros x Hx. apply HA...
    assert (Hou: sup A ⋵ 𝐎𝐍). apply union_of_ords_is_ord...
    apply ExtAx. split; intros Hx.
    + destruct (sucord_or_limord (sup A)) as [Hsuc|Hlim]... {
        apply sup_of_ords_is_suc_impl_in_ords in Hsuc...
        apply HA in Hsuc as [_ HFu]...
      }
      destruct Hnml as [Hmono Hcon].
      destruct (classic (sup A = ∅)) as [|Hne'].
      * apply union_empty_iff in H as [|HeqA]...
        rewrite HeqA in HA, Hx.
        unfold sup in Hx. rewrite union_one in Hx.
        assert (∅ ⋵ fixed_point F). apply HA. apply SingI.
        destruct H as [_ HF0]. rewrite HF0 in Hx. exfalso0.
      * rewrite Hcon in Hx...
        apply FUnionE in Hx as [α [Hα Hx]].
        apply UnionAx in Hα as [β [Hβ Hα]].
        apply UnionAx. exists β. split...
        apply HA in Hβ as [Hoβ HFβ].
        apply Hmono in Hα... rewrite <- HFβ.
        eapply ord_trans...
    + apply UnionAx in Hx as [α [Hα Hx]].
      assert (α ⋸ sup A). apply ord_sup_is_ub...
      apply HA in Hα as [Hoα HFα]. rewrite <- HFα in Hx.
      destruct H... eapply ord_trans... apply HF... apply Hnml...
Qed.

(* ex8_8 不动点的枚举操作是规范的 *)
Theorem fixed_point_normal :
  ∀ F, F:ᶜ 𝐎𝐍 ⇒ 𝐎𝐍 → normal F → normal (FixedPoint F).
Proof with auto.
  intros F HF Hnml. split.
  apply fixed_point_monotone...
  apply fixed_point_continuous...
Qed.

(* 存在不动点的不动点 *)
Corollary ex_fixed_point_of_fixed_point :
  ∀ F, F:ᶜ 𝐎𝐍 ⇒ 𝐎𝐍 → normal F →
  ∀β ⋵ 𝐎𝐍, ∃ γ, fixed_point (FixedPoint F) γ ∧ β ⋸ γ.
Proof with auto.
  intros F HF Hnml β Hoβ. apply Veblen_fixed_point...
  apply enum_operative... apply fixed_point_normal...
Qed.

End VeblenFixedPoint.
