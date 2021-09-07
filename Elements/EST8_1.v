(** Adapted from "Elements of Set Theory" Chapter 8 **)
(** Coq coding by choukh, Feb 2021 **)

Require Import ZFC.Lib.Class.
Require Import ZFC.Lib.ChoiceFacts.
Require Export ZFC.Lib.Ordinal.

(*** EST第八章1：序数类，序数运算，阿列夫数，ℶ数 ***)

Module Import OrdinalClass.

(* 序数运算的单调性 *)
Definition monotone := λ F,
  ∀α ⋵ 𝐎𝐍, ∀β ∈ α, F β ∈ F α.

(* 序数运算在极限处的连续性 *)
Definition continuous := λ F,
  ∀ 𝜆 ⋵ 𝐎𝐍ˡⁱᵐ, 𝜆 ≠ ∅ → F 𝜆 = sup{F α | α ∊ 𝜆}.

(* 序数运算的规范性 *)
Definition normal := λ F, monotone F ∧ continuous F.

(* 序数运算的递增性 *)
Definition ascending := λ F, ∀α ⋵ 𝐎𝐍, F α ∈ F α⁺.

(* 𝐎𝐍子类对上界的封闭性 *)
Definition closed := λ C : Class,
  ∀ A, A ≠ ∅ → (∀x ∈ A, x ⋵ C) → sup A ⋵ C.

(* 𝐎𝐍子类的有界性 *)
Definition bounded := λ C : Class,
  ∃α ⋵ 𝐎𝐍, ∀β ⋵ C, β ⋸ α.

(* 𝐎𝐍子类的无界性 *)
Definition unbounded := λ C : Class,
  ∀α ⋵ 𝐎𝐍, ∃β ⋵ C, α ∈ β.

(* 序数运算的与指定值域对应的定义域 *)
Definition Domain := λ F A,
  ϕ_Repl (λ x y, y ⋵ 𝐎𝐍 ∧ F y = x) A.

(* 序数运算的与指定定义域对应的值域 *)
Definition Range := λ F Ω,
  {F α | α ∊ Ω}.

(* 序数运算的包含于指定集合里的值域 *)
Definition RangeAmong := λ F Ω,
  {y ∊ Ω | ∃α ⋵ 𝐎𝐍, F α = y}.

Lemma domain_spec :
  ∀ F C, F:ᶜ 𝐎𝐍 ⟹ C → C ⫃ 𝐎𝐍 → class_injective F 𝐎𝐍 →
  ∀ A, (∀x ∈ A, x ⋵ C) → ∀ ξ, ξ ∈ Domain F A ↔ ξ ⋵ 𝐎𝐍 ∧ F ξ ∈ A.
Proof with eauto.
  intros F C [_ HR] Hsub Hinj A HA ξ.
  set (λ x y, y ⋵ 𝐎𝐍 ∧ F y = x) as ϕ.
  assert (Hϕ: ∀x ∈ A, ∃! y, ϕ x y). {
    intros x Hx. rewrite <- unique_existence.
    split. apply HR. apply HA...
    intros y1 y2 [H11 H12] [H21 H22]. subst x. eapply Hinj...
  }
  split.
  - intros Hξ. apply ϕ_ReplAx in Hξ as [α [Hα [Hoξ Heq]]]...
    split... congruence.
  - intros [Hoξ HFξ]. apply ϕ_ReplAx...
Qed.

End OrdinalClass.

(* 序数的后继运算是单调的 *)
Example ord_suc_monotone : monotone Suc.
Proof with eauto.
  intros α Hoα β Hβ.
  apply (ord_suc_preserve_lt β)...
  eapply ord_is_ords...
Qed.

(* ex8_3_b 单调运算具有单射性 *)
Lemma monotone_operation_injective :
  ∀ F C, F:ᶜ 𝐎𝐍 ⇒ C → C ⫃ 𝐎𝐍 →
  monotone F → class_injective F 𝐎𝐍.
Proof with auto.
  intros F C HF Hsub Hmono α Hoα β Hoβ Heq.
  contra as Hnq.
  apply ord_connected in Hnq as []; auto;
  eapply Hmono in H; eauto;
  rewrite Heq in H; eapply ord_irrefl; revgoals; eauto;
  apply Hsub; apply HF...
Qed.

Lemma unbounded_iff_not_bounded : ∀ C, C ⫃ 𝐎𝐍 →
  unbounded C ↔ ¬ bounded C.
Proof with eauto; try congruence.
  intros C Hsub. split.
  - intros Hbnd [μ [Hμ Hmax]].
    apply Hbnd in Hμ as H. destruct H as [β [Hβ Hlt]].
    apply Hmax in Hβ as Hle.
    eapply ord_not_le_gt; revgoals...
  - intros Hnb α Hoα.
    apply not_all_not_ex. intros H. apply Hnb.
    exists α. split... intros β Hβ. specialize H with β.
    apply not_and_or in H as []...
    apply ord_le_iff_not_gt...
Qed.

(* 𝐎𝐍子类是集合当且仅当它是有界的 *)
Lemma bounded_iff_is_set : ∀ C, C ⫃ 𝐎𝐍 → bounded C ↔ is_set C.
Proof with auto.
  intros C Hsub. split.
  - intros [α [Hoα Hle]]. exists {x ∊ α⁺ | C x}.
    intros x. split; intros Hx. apply SepE2 in Hx...
    apply SepI... apply ord_le_iff_lt_suc...
  - intros [A HA].
    assert (Hos: A ⪽ 𝐎𝐍). intros x Hx. apply HA in Hx...
    exists (sup A). split. apply union_of_ords_is_ord...
    intros β Hβ. apply HA in Hβ. apply ord_sup_is_ub...
Qed.

(* ex8_6_a 单调运算的值域无界 *)
Lemma monotone_operation_range_unbounded :
  ∀ F C, F:ᶜ 𝐎𝐍 ⟹ C → C ⫃ 𝐎𝐍 → monotone F → unbounded C.
Proof with eauto; try congruence.
  intros F C HF Hsub Hmono.
  apply unbounded_iff_not_bounded...
  intros H. apply bounded_iff_is_set in H as [A HA]...
  apply Burali_Forti. exists (Domain F A).
  intros α Hoα. eapply domain_spec...
  eapply monotone_operation_injective...
  apply HF. intros x Hx. apply HA...
  split... apply HA... apply HF...
Qed.

(* 如果具有单调性的序数运算的值域是封闭的，那么该序数运算具有连续性 *)
Lemma monotone_operation_continuous_if_range_closed :
  ∀ F C, F:ᶜ 𝐎𝐍 ⟹ C → C ⫃ 𝐎𝐍 →
  monotone F → closed C → continuous F.
Proof with eauto.
  intros F C [HF HR] Hsub Hmono Hcld 𝜆 Hlim Hne.
  assert (H := Hlim). destruct H as [Ho𝜆 _].
  set {F α | α ∊ 𝜆} as A.
  pose proof (ord_sup_is_ub A) as [_ Hub]. {
    intros x Hx. apply ReplAx in Hx as [α [Hα Hx]].
    subst x. apply Hsub. apply HF. eapply ord_is_ords...
  }
  assert (Hu: sup A ⋵ C). {
    apply Hcld.
    - apply EmptyNE in Hne as [α Hα].
      apply EmptyNI. exists (F α). eapply ReplI...
    - intros x Hx. apply ReplAx in Hx as [α [Hα Heq]].
      subst x. apply HF. eapply ord_is_ords; revgoals...
  }
  assert (HoF: ∀ α, α ⋵ 𝐎𝐍 → 𝐎𝐍 (F α)). {
    intros α Hoα. apply Hsub. apply HF...
  }
  apply HR in Hu as [α [Hoα HFα]].
  rewrite <- HFα. f_equal.
  contra as Hnq.
  apply ord_connected in Hnq as [H𝜆α|Hα𝜆]...
  - apply Hmono in H𝜆α... rewrite HFα in H𝜆α.
    apply FUnionE in H𝜆α as [β [Hβ Hlt]].
    assert (Hoβ: β ⋵ 𝐎𝐍). eapply ord_is_ords; revgoals...
    apply Hmono in Hβ... eapply ord_not_lt_gt; revgoals...
  - assert (F α⁺ ∈ A). eapply ReplI... apply sucord_in_limord...
    apply Hub in H. rewrite <- HFα in H.
    eapply (ord_not_le_gt (F α⁺)); swap 1 3...
Qed.

(* 如果序数集的上确界是后继序数，那么该上确界在该序数集内 *)
Lemma sup_ords_is_sucord_impl_in :
  ∀ A, A ⪽ 𝐎𝐍 → sup A ⋵ 𝐎𝐍ˢᵘᶜ → sup A ∈ A.
Proof with eauto; try congruence.
  intros A Hos [α [Hoα Heq]].
  apply ord_sup_correct in Hos as H.
  destruct H as [[Ho Hub] Hsup].
  destruct (classic (is_ub α A)).
  - exfalso. apply Hsup in H. rewrite Heq in H.
    eapply ord_not_le_gt; swap 1 3...
  - apply not_and_or in H as []...
    apply set_not_all_ex_not in H as [β [Hβ Hnle]].
    pose proof (Hub β Hβ) as []; rewrite Heq in H...
    apply ord_le_iff_lt_suc in H...
Qed.

(* 如果序数集的上确界在该序数集外，那么该上确界是极限序数 *)
Corollary sup_ords_out_impl_is_limord :
  ∀ A, A ⪽ 𝐎𝐍 → sup A ∉ A → sup A ⋵ 𝐎𝐍ˡⁱᵐ.
Proof with auto.
  intros A Hos Hout.
  assert (Hu: sup A ⋵ 𝐎𝐍). {
    apply union_of_ords_is_ord. intros α Hα. apply Hos...
  }
  pose proof (sucord_or_limord (sup A)) as []...
  exfalso. apply Hout. apply sup_ords_is_sucord_impl_in...
Qed.

(* 极限序数集的并是极限序数 *)
Corollary union_of_limords_is_limord : ∀ A, A ⪽ 𝐎𝐍ˡⁱᵐ → ⋃ A ⋵ 𝐎𝐍ˡⁱᵐ.
Proof with eauto; try congruence.
  intros A Hlim.
  destruct (classic (sup A ∈ A)) as []. apply Hlim...
  apply sup_ords_out_impl_is_limord...
Qed.

(* ex8_6_b 序数规范运算的值域封闭 *)
Lemma normal_operation_range_closed :
  ∀ F C, F:ᶜ 𝐎𝐍 ⟹ C → C ⫃ 𝐎𝐍 → normal F → closed C.
Proof with eauto; try congruence.
  intros F C HF Hsub [Hmono Hcon] A Hne HA.
  set (Domain F A) as Ω.
  set (sup Ω) as μ.
  assert (HΩ: ∀ ξ, ξ ∈ Ω ↔ ξ ⋵ 𝐎𝐍 ∧ F ξ ∈ A). {
    eapply domain_spec...
    eapply monotone_operation_injective... apply HF.
  }
  assert (HosA: A ⪽ 𝐎𝐍). intros x Hx. apply Hsub...
  assert (HosΩ: Ω ⪽ 𝐎𝐍). intros x Hx. apply HΩ...
  assert (Hoμ: μ ⋵ 𝐎𝐍). apply union_of_ords_is_ord...
  assert (HoA: sup A ⋵ 𝐎𝐍). apply union_of_ords_is_ord...
  assert (HoF: ∀ α, α ⋵ 𝐎𝐍 → 𝐎𝐍 (F α)). {
    intros α Hoα. apply Hsub. apply HF...
  }
  replace (sup A) with (F μ). apply HF...
  apply sub_antisym.
  - intros x Hx. apply UnionAx.
    ord_destruct μ.
    + rewrite H0 in Hx.
      apply union_eq_empty in H0 as [].
      * apply EmptyNE in Hne as [a Ha].
        apply HA in Ha as HaC.
        apply HF in HaC as [α [Hoα Heq]]. subst a.
        exfalso. eapply EmptyE... apply HΩ...
      * exists (F ∅). split... apply HΩ.
        rewrite H. apply SingI.
    + exists (F μ). split... apply HΩ.
      apply sup_ords_is_sucord_impl_in...
    + rewrite Hcon in Hx...
      apply FUnionE in Hx as [α [Hα Hx]].
      apply UnionAx in Hα as [β [Hβ Hα]].
      assert (Hoβ: β ⋵ 𝐎𝐍). apply HΩ...
      exists (F β). split. apply HΩ... eapply ord_trans...
  - apply ord_le_iff_sub...
    apply ord_sup_correct... split...
    intros x Hx. apply HA in Hx as HxC.
    apply HF in HxC as [α [Hoα Heq]]. subst x.
    assert (α ⋸ μ). apply ord_sup_is_ub... apply HΩ...
    destruct H; [left|right]...
Qed.

(* 具有单调性的序数运算的值域是封闭的当且仅当该序数运算具有连续性 *)
Fact monotone_operation_continuous_iff_range_closed :
  ∀ F C, F:ᶜ 𝐎𝐍 ⟹ C → C ⫃ 𝐎𝐍 → 
  monotone F → closed C ↔ continuous F.
Proof with eauto.
  intros F C HF Hsub Hmono. split.
  - eapply monotone_operation_continuous_if_range_closed...
  - intros Hcon.
    eapply normal_operation_range_closed...
    split...
Qed.

(* 单调运算递增 *)
Fact monotone_operation_ascending :
  ∀ F, F:ᶜ 𝐎𝐍 ⇒ 𝐎𝐍 → monotone F → ascending F.
Proof. intros F HF Hmono α Hoα. apply Hmono; auto. Qed.

(* 连续递增运算单调 *)
Theorem continuous_ascending_operation_monotone :
  ∀ F, F:ᶜ 𝐎𝐍 ⇒ 𝐎𝐍 → continuous F → ascending F → monotone F.
Proof with eauto.
  intros F HF Hcon Hasc α Hoα β Hlt.
  generalize dependent α.
  ord_induction. intros α Hoα IH Hlt.
  ord_destruct α.
  - subst. exfalso0.
  - destruct Hsuc as [γ [Hγ H]]. subst.
    apply BUnionE in Hlt as [].
    + eapply ord_trans. 3: apply Hasc... 1-2: auto.
    + apply SingE in H; subst. apply Hasc...
  - rewrite (Hcon α)... eapply FUnionI.
    apply sucord_in_limord... apply Hasc. eapply ord_is_ords...
Qed.

(* 序数子类的分离 *)
Module 𝐎𝐍Separation.
(* 序数上的超限递归模式 *)
Import RecursionSchemaOnOrdinals.

Definition γ := λ C f y, y ⋵ C ∧ y ∉ ran f ∧ ∀x ⋵ C, x ∉ ran f → y ⋸ x.
Definition Enumerate := λ C, Recursion (γ C).

Local Lemma unbounded_subclass_cannot_be_a_set :
  ∀ C, C ⫃ 𝐎𝐍 → unbounded C → ¬ ∃ A, ∀α ⋵ C, α ∈ A.
Proof with auto.
  intros C Hsub Hubd [A Hset]. apply Burali_Forti.
  exists (sup A). intros α Hoα. apply UnionAx.
  apply Hubd in Hoα as [β [Hα HC]].
  exists β. split...
Qed.

Local Lemma γ_functional :
  ∀ C f, C ⫃ 𝐎𝐍 → unbounded C → ∃! y, γ C f y.
Proof with eauto; try congruence.
  intros C f Hsub Hubd. rewrite <- unique_existence. split.
  - destruct (classic (∀α ⋵ C, α ∈ ran f)). {
      exfalso. eapply unbounded_subclass_cannot_be_a_set...
    }
    apply not_all_ex_not in H as [α H].
    apply imply_to_and in H as [HPα Hα].
    assert (Hoα: α ⋵ 𝐎𝐍). apply Hsub...
    set (λ α, α ⋵ C ∧ α ∉ ran f) as P.
    set (OrdMin α⁺ P) as μ.
    pose proof (ordMin_correct α⁺ P) as [Hμ Hmin]... {
      exists α. split. apply BUnionI2... split...
    }
    fold μ in Hμ, Hmin.
    apply SepE in Hμ as [Hμα [HPμ Hμ]].
    exists μ. split... split...
    intros x HPx Hx.
    destruct (classic (x ∈ α⁺)) as [Hxα|Hxα].
    + assert (x ∈ {ξ ∊ α⁺ | P ξ}). apply SepI... split...
      apply Hmin in H as []... apply binRelE3 in H...
    + assert (Hoμ: μ ⋵ 𝐎𝐍). apply Hsub...
      assert (Hox: x ⋵ 𝐎𝐍). apply Hsub...
      destruct (classic (μ = x)) as [|Hnq]...
      apply ord_connected in Hnq as []...
      exfalso. apply Hxα. eapply ord_trans...
  - intros x y [HxC [Hx H1]] [HyC [Hy H2]].
    apply H1 in Hy... apply H2 in Hx...
    destruct Hx; destruct Hy... exfalso.
    eapply ord_not_lt_gt; revgoals...
Qed.
Global Hint Immediate γ_functional : core.

(* 枚举元素是属于子类且与之前的元素都不同的最小序数 *)
Lemma enum_spec : ∀ C, C ⫃ 𝐎𝐍 → unbounded C →
  ∀α ⋵ 𝐎𝐍, ∀ξ ⋵ C, ξ ∉ {Enumerate C x | x ∊ α} → Enumerate C α ⋸ ξ.
Proof with auto.
  intros C Hsub Hund α Hoα ξ HξC Hout.
  pose proof (recursion_spec (γ C) α) as [_ [_ Hmin]]...
  apply Hmin... rewrite ran_of_op_repl...
Qed.

(* 枚举运算映射到子类 *)
Lemma enum_into_class : ∀ C, C ⫃ 𝐎𝐍 → unbounded C →
  Enumerate C :ᶜ 𝐎𝐍 ⇒ C.
Proof.
  intros C Hsub Hund α Hoα. unfold Enumerate.
  apply (recursion_spec (γ C) α); auto.
Qed.

(* 枚举是序数运算 *)
Lemma enum_operative : ∀ C, C ⫃ 𝐎𝐍 → unbounded C →
  Enumerate C :ᶜ 𝐎𝐍 ⇒ 𝐎𝐍.
Proof.
  intros C Hsub Hund α Hoα. apply Hsub.
  apply enum_into_class; auto.
Qed.

(* 枚举运算单调增 *)
Theorem enum_monotone : ∀ C, C ⫃ 𝐎𝐍 → unbounded C →
  monotone (Enumerate C).
Proof with eauto.
  intros C Hsub Hund α Hoα β Hβ.
  assert (Hoβ: β ⋵ 𝐎𝐍). eapply ord_is_ords...
  pose proof (recursion_spec (γ C) α) as [Hinf [Hout _]]...
  pose proof (recursion_spec (γ C) β) as [_ [_ Hmin]]...
  fold (Enumerate C) in *. rewrite ran_of_op_repl in *.
  assert (Enumerate C α ∉ {Enumerate C x | x ∊ β}). {
    intros H. apply ReplAx in H as [δ [Hδ H]].
    apply Hout. rewrite <- H. apply ReplI. eapply ord_trans...
  }
  apply Hmin in H as []...
  exfalso. apply Hout. rewrite <- H. apply ReplI...
Qed.

(* 枚举运算具有单射性 *)
Corollary enum_injective : ∀ C, C ⫃ 𝐎𝐍 → unbounded C →
  class_injective (Enumerate C) 𝐎𝐍.
Proof with eauto.
  intros C Hsub Hund.
  eapply monotone_operation_injective...
  apply enum_into_class... apply enum_monotone...
Qed.

(* 子类元素均被枚举 *)
Theorem enum_surjective : ∀ C, C ⫃ 𝐎𝐍 → unbounded C →
  class_surjective (Enumerate C) 𝐎𝐍 C.
Proof with eauto; try congruence.
  intros C Hsub Hund ξ H. apply Hsub in H as Hoξ.
  generalize dependent H. generalize dependent ξ.
  ord_induction. intros ξ Hoξ IH Hinfξ.
  set (λ x α, α ⋵ 𝐎𝐍 ∧ x = Enumerate C α) as ψ.
  set {x ∊ ξ | C x} as χ.
  set (ϕ_Repl ψ χ) as α.
  assert (Hψ: ∀x ∈ χ, ∃! y, ψ x y). {
    intros x Hx. apply SepE in Hx as [Hx Hinfx].
    rewrite <- unique_existence. split.
    - apply IH in Hx as [β [Hoβ Hx]]...
      exists β. split...
    - intros δ ε [Hoδ Hδ] [Hoε Hε].
      eapply enum_injective...
  }
  assert (Hoα: α ⋵ 𝐎𝐍). {
    apply transitive_set_well_ordered_by_epsilon_is_ord; revgoals.
    - apply ords_woset. intros x Hx.
      apply ϕ_ReplAx in Hx as [_ [_ [Ho _]]]...
    - intros ε δ Hε Hδ.
      apply ϕ_ReplAx in Hδ as [x [Hx [Hoδ Heqx]]]... subst x.
      assert (Hoε: ε ⋵ 𝐎𝐍). eapply ord_is_ords...
      apply ϕ_ReplAx... exists (Enumerate C ε). repeat split...
      apply SepE1 in Hx. apply SepI.
      + eapply enum_monotone in Hε... eapply ord_trans...
      + apply enum_into_class...
  }
  exists α. split...
  pose proof (recursion_spec (γ C) α) as [_ [Hout Hmin]]...
  fold (Enumerate C) in *. rewrite ran_of_op_repl in *.
  assert (Hle: Enumerate C α ⋸ ξ). {
    apply Hmin... intros Hξ.
    apply ReplAx in Hξ as [β [Hβ Heq]].
    apply ϕ_ReplAx in Hβ as [μ [Hμ [Hoβ Heqμ]]]...
    apply SepE1 in Hμ. subst. eapply ord_irrefl; revgoals...
  }
  destruct Hle...
  destruct (classic (ξ = Enumerate C α)) as [|Hnq]... exfalso.
  apply ord_connected in Hnq as []; [..|apply enum_operative]...
  - eapply ord_not_lt_gt; revgoals... apply enum_operative...
  - apply Hout. eapply ReplI. apply ϕ_ReplAx...
    exists (Enumerate C α). repeat split...
    apply SepI... apply enum_into_class...
Qed.

(* 枚举运算是到子类的满射 *)
Corollary enum_onto_class : ∀ C, C ⫃ 𝐎𝐍 → unbounded C →
  Enumerate C :ᶜ 𝐎𝐍 ⟹ C.
Proof with auto.
  intros C Hsub Hund. split.
  apply enum_into_class... apply enum_surjective...
Qed.

(* 子类元素等价于满足P的序数 *)
Theorem enum_iff_class : ∀ C, C ⫃ 𝐎𝐍 → unbounded C →
  ∀ ξ, ξ ⋵ C ↔ ∃ α, α ⋵ 𝐎𝐍 ∧ Enumerate C α = ξ.
Proof with auto.
  split. apply enum_surjective...
  intros [α [Hoα Heq]]. subst. apply enum_into_class...
Qed.

End 𝐎𝐍Separation.

(* 阿列夫数 *)
Section Aleph.
Import 𝐎𝐍Separation.

Definition ℵ := Enumerate 𝐂𝐃ⁱⁿᶠ.

Lemma infcard_is_sub : 𝐂𝐃ⁱⁿᶠ ⫃ 𝐎𝐍.
Proof. exact infcard_is_ord. Qed.
Local Hint Resolve infcard_is_sub : core.

Open Scope Card_scope.

Lemma infcard_unbounded : unbounded 𝐂𝐃ⁱⁿᶠ.
Proof with eauto.
  intros α Hoα.
  apply all_ord_ex_larger_card in Hoα as [𝜅 [H𝜅 Hα]].
  assert (Hcs: 𝜅 + ℵ₀ ⋵ 𝐂𝐃)...
  assert (Hos: 𝜅 + ℵ₀ ⋵ 𝐎𝐍)...
  apply all_ord_ex_larger_card in Hos as [𝜆 [H𝜆 Hlt]].
  exists 𝜆. split.
  - split... apply (parent_set_of_infinite_is_infinite (𝜅 + ℵ₀)).
    apply ord_le_iff_sub... apply cardAdd_infinite_iff...
  - eapply ord_trans...
    cut (𝜅 <𝐜 𝜆). apply cardLt_iff_ord_lt.
    eapply cardLe_lt_trans; revgoals.
    apply cardLt_iff_ord_lt... apply cardAdd_enlarge...
Qed.
Local Hint Resolve infcard_unbounded : core.

(* 阿列夫数是与之前的阿列夫数都不同的最小无限基数 *)
Lemma aleph_spec : ∀α ⋵ 𝐎𝐍, ∀ξ ⋵ 𝐂𝐃ⁱⁿᶠ, ξ ∉ {ℵ x | x ∊ α} → ℵ α ⋸ ξ.
Proof. intros α Hα ξ Hξ. apply (enum_spec 𝐂𝐃ⁱⁿᶠ); auto. Qed.

(* 阿列夫数是无限基数 *)
Lemma aleph_is_infcard : ℵ :ᶜ 𝐎𝐍 ⇒ 𝐂𝐃ⁱⁿᶠ.
Proof. apply enum_into_class; auto. Qed.

(* 阿列夫是序数运算 *)
Lemma aleph_operative : ℵ :ᶜ 𝐎𝐍 ⇒ 𝐎𝐍.
Proof. intros. apply enum_operative; auto. Qed.

(* 阿列夫数是基数 *)
Lemma aleph_is_card : ∀ α, α ⋵ 𝐎𝐍 → ℵ α ⋵ 𝐂𝐃.
Proof. intros. apply aleph_is_infcard; auto. Qed.
Local Hint Resolve aleph_is_card : core.

(* 阿列夫数是无限集 *)
Lemma aleph_infinite : ∀ α, α ⋵ 𝐎𝐍 → infinite (ℵ α).
Proof. intros. apply aleph_is_infcard; auto. Qed.
Local Hint Resolve aleph_infinite : core.

(* 阿列夫数单调增 *)
Theorem aleph_monotone : monotone ℵ.
Proof. apply enum_monotone; auto. Qed.

(* 阿列夫运算具有单射性 *)
Corollary aleph_injective : class_injective ℵ 𝐎𝐍.
Proof. apply enum_injective; auto. Qed.

(* 无限基数都是阿列夫数 *)
Theorem aleph_surjective : class_surjective ℵ 𝐎𝐍 𝐂𝐃ⁱⁿᶠ.
Proof. apply enum_surjective; auto. Qed.

(* 阿列夫数等价于无限基数 *)
Theorem aleph_iff_infcard :
  ∀ 𝜅, 𝜅 ⋵ 𝐂𝐃ⁱⁿᶠ ↔ ∃ α, α ⋵ 𝐎𝐍 ∧ ℵ α = 𝜅.
Proof. apply enum_iff_class; auto. Qed.

Local Hint Resolve empty_is_ord : core.

(* ==需要选择公理== *)
Theorem aleph_0 : AC_III → ℵ 0 = ℵ₀.
Proof with auto.
  intros AC3. ord_ext...
  - apply aleph_spec... intros H.
    apply ReplAx in H as [x [Hx _]]. exfalso0.
  - apply cardLe_to_ord_le.
    apply aleph0_is_the_least_infinite_card...
    apply aleph_is_infcard...
Qed.

Theorem aleph_suc : ∀α ⋵ 𝐎𝐍, ℵ α⁺ = (ℵ α)₊.
Proof with eauto.
  intros α Hoα.
  ord_ext...
  - assert (Hlt: ℵ α ∈ (ℵ α)₊). {
      rewrite card_of_card at 1...
      apply card_suc_has_card.
    }
    apply aleph_spec... split...
    + apply (parent_set_of_infinite_is_infinite (ℵ α))...
      apply ord_le_iff_sub...
    + intros H. apply ReplAx in H as [β [Hβ Heq]].
      apply BUnionE in Hβ as [].
      * apply aleph_monotone in H... rewrite Heq in H.
        eapply ord_not_lt_gt; revgoals...
      * apply SingE in H; subst.
        eapply ord_not_lt_self; revgoals...
  - eapply card_suc_correct...
    rewrite <- card_of_card...
    apply aleph_monotone...
Qed.

(* 基数集的并是基数 *)
Lemma union_of_cards_is_card : ∀ A, A ⪽ 𝐂𝐃 → sup A ⋵ 𝐂𝐃.
Proof with eauto.
  intros A Hcds.
  assert (Hods: A ⪽ 𝐎𝐍). {
    intros x Hx. apply card_is_ord. apply Hcds...
  }
  assert (Hou: sup A ⋵ 𝐎𝐍). {
    apply union_of_ords_is_ord...
  }
  exists (sup A). apply card_of_initord.
  split. apply union_of_ords_is_ord...
  intros α Hα Hqn. symmetry in Hqn.
  apply UnionAx in Hα as [κ [Hκ Hα]].
  assert (Hoκ: κ ⋵ 𝐎𝐍). apply Hods...
  assert (Hoα: α ⋵ 𝐎𝐍). eapply ord_is_ords...
  assert (H1: α ⊆ κ). apply ord_le_iff_sub...
  assert (H2: κ ⋸ sup A). apply ord_sup_is_ub...
  apply ord_le_iff_sub in H2...
  pose proof (sub_squeeze_to_eqnum _ _ _ H1 H2 Hqn) as [H _].
  apply Hcds in Hκ as [k Heq]. rewrite Heq in Hα, H.
  eapply (card_is_initord k)... symmetry...
Qed.

Theorem aleph_limit : continuous ℵ.
Proof with eauto.
  apply (monotone_operation_continuous_if_range_closed ℵ 𝐂𝐃ⁱⁿᶠ)...
  - split. apply aleph_is_infcard. apply aleph_surjective.
  - apply aleph_monotone.
  - intros A Hne HA. split.
    + apply union_of_cards_is_card.
      intros x Hx. apply HA...
    + intros Hfin. apply finite_union in Hfin as [_ Hfin].
      apply EmptyNE in Hne as [a Ha].
      apply Hfin in Ha as Hfina. apply HA in Ha as [_ Hinf]...
Qed.

(* 阿列夫是规范运算 *)
Theorem aleph_normal : normal ℵ.
Proof. split. apply aleph_monotone. apply aleph_limit. Qed.

End Aleph.

(* 序数运算 *)
Module 𝐎𝐍Operation.
Import RecursionSchemaOnOrdinals.

Definition γ := λ y₀ G f y, y =
  match (ixm (dom f = ∅)) with
  | inl _ => y₀
  | inr _ =>
    match (ixm (∃α ⋵ 𝐎𝐍ˢᵘᶜ, dom f = α)) with
    | inl _ => G f[sup (dom f)]
    | inr _ =>
      match (ixm (∃𝜆 ⋵ 𝐎𝐍ˡⁱᵐ, dom f = 𝜆)) with
      | inl _ => sup (ran f)
      | inr _ => ∅
      end
    end
  end.

Definition Operation := λ y₀ G, Recursion (γ y₀ G).

Lemma γ_functional : ∀ y₀ G f, ∃! y, γ y₀ G f y.
Proof.
  intros. unfold γ. rewrite <- unique_existence.
  split; eauto; congruence.
Qed.
Global Hint Immediate γ_functional : core.

Theorem operation_0 : ∀ y₀ G, Operation y₀ G ∅ = y₀.
Proof with auto.
  intros. unfold Operation.
  rewrite (recursion_spec (γ y₀ G) ∅), dom_of_op_repl...
  destruct (ixm (∅ = ∅))... exfalso...
Qed.

Theorem operation_suc : ∀ y₀ G, ∀α ⋵ 𝐎𝐍,
  Operation y₀ G α⁺ = G (Operation y₀ G α).
Proof with eauto.
  intros y₀ G α Hoα. unfold Operation.
  rewrite (recursion_spec (γ y₀ G) α⁺), dom_of_op_repl...
  destruct (ixm (α⁺ = ∅))... {
    exfalso. eapply ord_suc_neq_0...
  }
  destruct (ixm (∃β ⋵ 𝐎𝐍ˢᵘᶜ, α⁺ = β)). {
    rewrite sup_of_sucord, ap_of_op_repl...
  }
  destruct (ixm (∃𝜆 ⋵ 𝐎𝐍ˡⁱᵐ, α⁺ = 𝜆)); exfalso.
  - destruct e as [𝜆 [_ H]]. apply n0.
    exists 𝜆. split... exists α. split...
  - destruct (sucord_or_limord α⁺)...
Qed.

Theorem operation_limit : ∀ y₀ G, continuous (Operation y₀ G).
Proof with eauto; try congruence.
  intros * 𝜆 Hlim Hne. unfold Operation.
  assert (H := Hlim). destruct H as [Ho𝜆 _].
  rewrite (recursion_spec (γ y₀ G) 𝜆), dom_of_op_repl...
  destruct (ixm (𝜆 = ∅))...
  destruct (ixm (∃α ⋵ 𝐎𝐍ˢᵘᶜ, 𝜆 = α)). {
    destruct e as [α [Hsuc Heq]]. subst α.
    exfalso. eapply sucord_iff_not_limord...
  }
  destruct (ixm (∃κ ⋵ 𝐎𝐍ˡⁱᵐ, 𝜆 = κ)).
  - rewrite ran_of_op_repl...
  - exfalso. destruct (sucord_or_limord 𝜆)...
Qed.

Lemma operation_operative : ∀ y₀ G, y₀ ⋵ 𝐎𝐍 → G:ᶜ 𝐎𝐍 ⇒ 𝐎𝐍 →
  Operation y₀ G :ᶜ 𝐎𝐍 ⇒ 𝐎𝐍.
Proof with auto.
  intros y₀ G Hoy₀ HG.
  ord_induction. intros α Hoα IH.
  ord_destruct α.
  - subst. rewrite operation_0...
  - destruct Hsuc as [β [Hoβ Heq]]. subst.
    rewrite operation_suc...
  - rewrite operation_limit...
    apply union_of_ords_is_ord. intros x Hx.
    apply ReplAx in Hx as [β [Hβ Heq]]. subst. apply IH...
Qed.

Lemma operation_monotone : ∀ y₀ G, y₀ ⋵ 𝐎𝐍 → G:ᶜ 𝐎𝐍 ⇒ 𝐎𝐍 →
  ascending (Operation y₀ G) → monotone (Operation y₀ G).
Proof with eauto.
  intros * Hoy₀ Hop Hasc.
  apply continuous_ascending_operation_monotone...
  apply operation_operative...
  apply operation_limit.
Qed.

Theorem operation_normal : ∀ y₀ G, y₀ ⋵ 𝐎𝐍 → G:ᶜ 𝐎𝐍 ⇒ 𝐎𝐍 →
  ascending (Operation y₀ G) → normal (Operation y₀ G).
Proof.
  intros. split. apply operation_monotone; auto.
  apply operation_limit.
Qed.

End 𝐎𝐍Operation.

Module AlternativeAleph.
Import 𝐎𝐍Operation.

Definition ℵ' := Operation ℵ₀ (λ α, α₊).

(* ==需要选择公理== *)
Fact alternative_aleph_correct : AC_III → ∀α ⋵ 𝐎𝐍, ℵ' α = ℵ α.
Proof with auto.
  intros AC3.
  ord_induction. intros α Hoα IH. unfold ℵ'.
  ord_destruct α.
  - subst. rewrite operation_0, aleph_0...
  - destruct Hsuc as [β [Hoβ Heq]]. subst.
    rewrite operation_suc, aleph_suc...
    f_equal. apply IH...
  - rewrite operation_limit, aleph_limit... f_equal.
    apply repl_ext. intros ξ Hξ. apply IH...
Qed.

End AlternativeAleph.

(* ℶ数 *)
Section Beth.
Import 𝐎𝐍Operation.

Definition ℶ := Operation ℵ₀ (λ α, 2 ^ α).

Theorem beth_0 : ℶ 0 = ℵ₀.
Proof. apply operation_0. Qed.

Theorem beth_suc : ∀α ⋵ 𝐎𝐍, ℶ α⁺ = 2 ^ ℶ α.
Proof. apply operation_suc. Qed.

Theorem beth_limit : continuous ℶ.
Proof. apply operation_limit. Qed.

(* ℶ数是基数 *)
Lemma beth_is_card : ℶ:ᶜ 𝐎𝐍 ⇒ 𝐂𝐃.
Proof with eauto.
  intros α Hoα. ord_destruct α.
  - subst. rewrite beth_0...
  - destruct Hsuc as [β [Hoβ Heq]]. subst. rewrite beth_suc...
  - generalize dependent α.
    ord_induction. intros α Hoα IH Hne Hlim.
    rewrite beth_limit... apply union_of_cards_is_card.
    intros x Hx. apply ReplAx in Hx as [β [Hβ Hx]]. subst x.
    assert (Hoβ: β ⋵ 𝐎𝐍). eapply ord_is_ords...
    ord_destruct β.
    + subst. rewrite beth_0...
    + destruct Hsuc as [δ [Hoδ Heq]]. subst. rewrite beth_suc...
    + apply IH...
Qed.

(* ℶ数是序数 *)
Lemma beth_is_ord : ℶ:ᶜ 𝐎𝐍 ⇒ 𝐎𝐍.
Proof.
  intros α Ho. apply card_is_ord.
  apply beth_is_card. apply Ho.
Qed.

(* ℶ数是无限集 *)
Lemma beth_infinite : ℶ:ᶜ 𝐎𝐍 ⇒ infinite.
Proof with nauto.
  ord_induction. intros α Hoα IH.
  ord_destruct α.
  - subst. rewrite beth_0...
  - destruct Hsuc as [β [Hoβ Heq]]. subst. rewrite beth_suc...
    assert (Hinf: infinite (ℶ β)). apply IH...
    apply cardExp_infinite_iff... apply beth_is_card...
    apply ord_le_to_cardLe...
    apply EmptyNI. apply infinite_set_nonempty...
  - rewrite beth_limit... intros Hfin.
    apply finite_union in Hfin as [_ Hfin].
    assert (ℶ 0 ∈ {ℶ ξ | ξ ∊ α}). {
      eapply ReplI. apply ord_neq_0_gt_0...
    }
    apply Hfin in H. rewrite beth_0 in H.
    apply aleph0_infinite...
Qed.

(* ℶ数是无限基数 *)
Lemma beth_is_infcard : ℶ:ᶜ 𝐎𝐍 ⇒ 𝐂𝐃ⁱⁿᶠ.
Proof with auto.
  intros. split... apply beth_is_card... apply beth_infinite...
Qed.

(* ℶ是规范运算 *)
Theorem beth_normal : normal ℶ.
Proof with auto.
  apply operation_normal...
  intros α Hoα. apply cardLt_to_ord_lt. rewrite beth_suc...
  apply cardLt_power... apply beth_is_card...
Qed.

End Beth.

(* 连续统假设 *)
Definition CH := ℵ 1 = ℶ 1.
(* 广义连续统假设 *)
Definition GCH := ∀α ⋵ 𝐎𝐍, ℵ α = ℶ α.
