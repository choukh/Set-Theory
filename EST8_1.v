(** Based on "Elements of Set Theory" Chapter 8 Part 1 **)
(** Coq coding by choukh, Feb 2021 **)

Require Export ZFC.lib.Ordinal.
Require Import ZFC.lib.Choice.
Require Import ZFC.lib.Class.

(*** EST第八章1：序数类，序数操作，阿列夫数，ℶ数 ***)

Module Import OrdinalClass.

Notation 𝐎𝐍 := is_ord.
Notation 𝐂𝐃 := is_card.

(* 序数操作的单调性 *)
Definition monotone := λ F,
  ∀α ⋵ 𝐎𝐍, ∀β ∈ α, F β ∈ F α.

(* 序数操作在极限处的连续性 *)
Definition continuous := λ F,
  ∀ 𝜆, 𝜆 ≠ ∅ → is_limit 𝜆 → F 𝜆 = sup{F | α ∊ 𝜆}.

(* 序数操作的规范性 *)
Definition normal := λ F, monotone F ∧ continuous F.

(* 序数操作的递增性 *)
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

(* 序数操作的与指定值域对应的定义域 *)
Definition Domain := λ F A,
  ϕ_Repl (λ x y, y ⋵ 𝐎𝐍 ∧ F y = x) A.

(* 序数操作的与指定定义域对应的值域 *)
Definition Range := λ F Ω,
  {F | α ∊ Ω}.

(* 序数操作的包含于指定集合里的值域 *)
Definition RangeAmong := λ F Ω,
  {y ∊ Ω | λ y, ∃α ⋵ 𝐎𝐍, F α = y}.

Lemma domain_spec :
  ∀ F C, F:ᶜ 𝐎𝐍 ⟹ C → C ⫃ 𝐎𝐍 → class_injective F 𝐎𝐍 →
  ∀ A, (∀x ∈ A, x ⋵ C) → ∀ ξ, ξ ∈ Domain F A ↔ ξ ⋵ 𝐎𝐍 ∧ F ξ ∈ A.
Proof with eauto.
  intros F C [_ HR] Hsub Hinj A HA ξ.
  set (λ x y, y ⋵ 𝐎𝐍 ∧ F y = x) as ϕ.
  assert (Hϕ: ∀x ∈ A, ∃! y, ϕ x y). {
    intros x Hx. split. apply HR. apply HA...
    intros y1 y2 [H11 H12] [H21 H22]. subst x. eapply Hinj...
  }
  split.
  - intros Hξ. apply ϕ_ReplAx in Hξ as [α [Hα [Hoξ Heq]]]...
    split... congruence.
  - intros [Hoξ HFξ]. apply ϕ_ReplAx...
    exists (F ξ). split...
Qed.

End OrdinalClass.

(* 序数的后继操作是单调的 *)
Example ord_suc_monotone : monotone Suc.
Proof with eauto.
  intros α Hoα β Hβ.
  rewrite <- ord_suc_preserve_lt...
  eapply ord_is_ords...
Qed.

(* ex8_3_b 单调操作具有单射性 *)
Lemma monotone_operation_injective :
  ∀ F C, F:ᶜ 𝐎𝐍 ⇒ C → C ⫃ 𝐎𝐍 →
  monotone F → class_injective F 𝐎𝐍.
Proof with auto.
  intros F C HF Hsub Hmono α Hoα β Hoβ Heq.
  destruct (classic (α = β)) as [|Hnq]... exfalso.
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
    eapply ord_not_leq_gt; revgoals...
  - intros Hnb α Hoα. unfold ex_in_class.
    apply not_all_not_ex. intros H. apply Hnb.
    exists α. split... intros β Hβ. specialize H with β.
    apply not_and_or in H as []...
    apply ord_leq_iff_not_gt...
Qed.

(* 𝐎𝐍子类是集合当且仅当它是有界的 *)
Lemma bounded_iff_is_set : ∀ C, C ⫃ 𝐎𝐍 → bounded C ↔ is_set C.
Proof with auto.
  intros C Hsub. split.
  - intros [α [Hoα Hle]]. exists {x ∊ α⁺ | C}.
    intros x. split; intros Hx. apply SepE2 in Hx...
    apply SepI... apply ord_leq_iff_lt_suc... apply Hle...
  - intros [A HA].
    assert (Hos: is_ords A). intros x Hx. apply HA in Hx...
    exists (sup A). split. apply union_of_ords_is_ord...
    intros β Hβ. apply HA in Hβ. apply ord_sup_is_ub...
Qed.

(* ex8_6_a 单调操作的值域无界 *)
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

(* 如果具有单调性的序数操作的值域是封闭的，那么该序数操作具有连续性 *)
Lemma monotone_operation_continuous_if_range_closed :
  ∀ F C, F:ᶜ 𝐎𝐍 ⟹ C → C ⫃ 𝐎𝐍 →
  monotone F → closed C → continuous F.
Proof with eauto.
  intros F C [HF HR] Hsub Hmono Hcld 𝜆 Hne Hlim.
  assert (H := Hlim). destruct H as [Ho𝜆 _].
  set {F | α ∊ 𝜆} as A.
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
  destruct (classic (𝜆 = α)) as [|Hnq]... exfalso.
  apply ord_connected in Hnq as [H𝜆α|Hα𝜆]...
  - apply Hmono in H𝜆α... rewrite HFα in H𝜆α.
    apply FUnionE in H𝜆α as [β [Hβ Hlt]].
    assert (Hoβ: β ⋵ 𝐎𝐍). eapply ord_is_ords; revgoals...
    apply Hmono in Hβ... eapply ord_not_lt_gt; revgoals...
  - assert (F α⁺ ∈ A). eapply ReplI... apply suc_in_limit...
    apply Hub in H. rewrite <- HFα in H.
    apply (ord_not_leq_gt (F α⁺) (F α))... apply Hmono...
Qed.

(* 如果序数集的上确界是后继序数，那么该上确界在该序数集内 *)
Lemma sup_of_ords_is_suc_impl_in_ords :
  ∀ A, is_ords A → is_suc (sup A) → sup A ∈ A.
Proof with eauto; try congruence.
  intros A Hos [α [Hoα Heq]].
  apply ord_sup_correct in Hos as H.
  destruct H as [[Ho Hub] Hsup].
  destruct (classic (is_ub α A)).
  - exfalso. apply Hsup in H. rewrite Heq in H.
    eapply ord_not_leq_gt; revgoals...
  - apply not_and_or in H as []...
    apply set_not_all_ex_not in H as [β [Hβ Hnle]].
    pose proof (Hub β Hβ) as []; rewrite Heq in H...
    apply ord_leq_iff_lt_suc in H... apply Hos...
Qed.

(* ex8_6_b 序数规范操作的值域封闭 *)
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
  assert (HosA: is_ords A). intros x Hx. apply Hsub... apply HA...
  assert (HosΩ: is_ords Ω). intros x Hx. apply HΩ...
  assert (Hoμ: μ ⋵ 𝐎𝐍). apply union_of_ords_is_ord...
  assert (HoA: sup A ⋵ 𝐎𝐍). apply union_of_ords_is_ord...
  assert (HoF: ∀ α, α ⋵ 𝐎𝐍 → 𝐎𝐍 (F α)). {
    intros α Hoα. apply Hsub. apply HF...
  }
  replace (sup A) with (F μ). apply HF...
  apply sub_antisym.
  - intros x Hx. apply UnionAx.
    destruct (ord_is_suc_or_limit μ)...
    + exists (F μ). split... apply HΩ.
      apply sup_of_ords_is_suc_impl_in_ords...
    + destruct (classic (μ = ∅)). {
        rewrite H0 in Hx.
        apply union_empty_iff in H0 as [].
        - apply EmptyNE in Hne as [a Ha].
          apply HA in Ha as HaC.
          apply HF in HaC as [α [Hoα Heq]]. subst a.
          exfalso. eapply EmptyE... apply HΩ...
        - exists (F ∅). split... apply HΩ.
          rewrite H0. apply SingI.
      }
      rewrite Hcon in Hx...
      apply FUnionE in Hx as [α [Hα Hx]].
      apply UnionAx in Hα as [β [Hβ Hα]].
      assert (Hoβ: is_ord β). apply HΩ...
      exists (F β). split. apply HΩ...
      eapply ord_trans... apply Hmono...
  - apply ord_leq_iff_sub...
    apply ord_sup_correct... split...
    intros x Hx. apply HA in Hx as HxC.
    apply HF in HxC as [α [Hoα Heq]]. subst x.
    assert (α ⋸ μ). apply ord_sup_is_ub... apply HΩ...
    destruct H; [left|right]... apply Hmono...
Qed.

(* 具有单调性的序数操作的值域是封闭的当且仅当该序数操作具有连续性 *)
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

(* 单调操作递增 *)
Fact monotone_operation_ascending :
  ∀ F, F:ᶜ 𝐎𝐍 ⇒ 𝐎𝐍 → monotone F → ascending F.
Proof. intros F HF Hmono α Hoα. apply Hmono; auto. Qed.

(* 连续递增操作单调 *)
Theorem continuous_ascending_operation_monotone :
  ∀ F, F:ᶜ 𝐎𝐍 ⇒ 𝐎𝐍 → continuous F → ascending F → monotone F.
Proof with eauto.
  intros F HF Hcon Hasc α Hoα β Hlt.
  generalize dependent α.
  set (λ α, β ∈ α → F β ∈ F α) as ϕ.
  apply (transfinite_induction_schema_on_ordinals ϕ)...
  intros α Hoα IH Hlt.
  destruct (ord_is_suc_or_limit α)...
  - destruct H as [γ [Hγ H]]. subst.
    apply BUnionE in Hlt as [].
    + eapply ord_trans. apply HF... apply IH... apply Hasc...
    + apply SingE in H; subst. apply Hasc...
  - destruct (classic (α = ∅)). subst. exfalso0.
    rewrite (Hcon α)... eapply FUnionI.
    apply suc_in_limit... apply Hasc. eapply ord_is_ords...
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
  exists β. split... apply Hset...
Qed.

Local Lemma γ_functional :
  ∀ C f, C ⫃ 𝐎𝐍 → unbounded C → ∃! y, γ C f y.
Proof with eauto; try congruence.
  intros C f Hsub Hubd. split.
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
    + assert (x ∈ {ξ ∊ α⁺ | P}). apply SepI... split...
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
  ∀α ⋵ 𝐎𝐍, ∀ξ ⋵ C, ξ ∉ {Enumerate C | x ∊ α} → Enumerate C α ⋸ ξ.
Proof with auto.
  intros C Hsub Hund α Hoα ξ HξC Hout.
  pose proof (recursion_spec (γ C) α) as [_ [_ Hmin]]...
  apply Hmin... rewrite ran_of_op_repl...
Qed.

(* 枚举操作映射到子类 *)
Lemma enum_into_class : ∀ C, C ⫃ 𝐎𝐍 → unbounded C →
  Enumerate C :ᶜ 𝐎𝐍 ⇒ C.
Proof.
  intros C Hsub Hund α Hoα. unfold Enumerate.
  apply (recursion_spec (γ C) α); auto.
Qed.

(* 枚举是序数操作 *)
Lemma enum_operative : ∀ C, C ⫃ 𝐎𝐍 → unbounded C →
  Enumerate C :ᶜ 𝐎𝐍 ⇒ 𝐎𝐍.
Proof.
  intros C Hsub Hund α Hoα. apply Hsub.
  apply enum_into_class; auto.
Qed.

(* 枚举操作单调增 *)
Theorem enum_monotone : ∀ C, C ⫃ 𝐎𝐍 → unbounded C →
  monotone (Enumerate C).
Proof with eauto.
  intros C Hsub Hund α Hoα β Hβ.
  assert (Hoβ: β ⋵ 𝐎𝐍). eapply ord_is_ords...
  pose proof (recursion_spec (γ C) α) as [Hinf [Hout _]]...
  pose proof (recursion_spec (γ C) β) as [_ [_ Hmin]]...
  fold (Enumerate C) in *. rewrite ran_of_op_repl in *.
  assert (Enumerate C α ∉ {Enumerate C | x ∊ β}). {
    intros H. apply ReplAx in H as [δ [Hδ H]].
    apply Hout. rewrite <- H. apply ReplI. eapply ord_trans...
  }
  apply Hmin in H as []...
  exfalso. apply Hout. rewrite <- H. apply ReplI...
Qed.

(* 枚举操作具有单射性 *)
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
  set (λ ξ, ξ ⋵ C → ∃α ⋵ 𝐎𝐍, Enumerate C α = ξ) as ϕ.
  apply (transfinite_induction_schema_on_ordinals ϕ).
  intros ξ Hoξ IH Hinfξ.
  set (λ x α, α ⋵ 𝐎𝐍 ∧ x = Enumerate C α) as ψ.
  set {x ∊ ξ | C} as χ.
  set (ϕ_Repl ψ χ) as α.
  assert (Hψ: ∀x ∈ χ, ∃! y, ψ x y). {
    intros x Hx. apply SepE in Hx as [Hx Hinfx]. split.
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

(* 枚举操作是到子类的满射 *)
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

Definition ℵ := Enumerate infcard.

Lemma infcard_is_sub : infcard ⫃ 𝐎𝐍.
Proof. exact infcard_is_ord. Qed.
Local Hint Resolve infcard_is_sub : core.

Open Scope Card_scope.

Lemma infcard_unbounded : unbounded infcard.
Proof with eauto.
  intros α Hoα.
  apply all_ord_ex_larger_card in Hoα as [𝜅 [H𝜅 Hα]].
  assert (Hcs: 𝜅 + ℵ₀ ⋵ 𝐂𝐃)...
  assert (Hos: 𝜅 + ℵ₀ ⋵ 𝐎𝐍)...
  apply all_ord_ex_larger_card in Hos as [𝜆 [H𝜆 Hlt]].
  exists 𝜆. split.
  - split... apply (parent_set_of_infinite_is_infinite (𝜅 + ℵ₀)).
    apply ord_leq_iff_sub... apply cardAdd_infinite_iff...
  - eapply ord_trans...
    cut (𝜅 <𝐜 𝜆). apply cardLt_iff_ord_lt.
    eapply cardLeq_lt_tran; revgoals.
    apply cardLt_iff_ord_lt... apply cardAdd_enlarge...
Qed.
Local Hint Resolve infcard_unbounded : core.

(* 阿列夫数是与之前的阿列夫数都不同的最小无限基数 *)
Lemma aleph_spec : ∀α ⋵ 𝐎𝐍, ∀ξ ⋵ infcard, ξ ∉ {ℵ | x ∊ α} → ℵ α ⋸ ξ.
Proof. apply enum_spec; auto. Qed.

(* 阿列夫数是无限基数 *)
Lemma aleph_is_infcard : ℵ :ᶜ 𝐎𝐍 ⇒ infcard.
Proof. apply enum_into_class; auto. Qed.

(* 阿列夫是序数操作 *)
Lemma aleph_operative : ℵ :ᶜ 𝐎𝐍 ⇒ 𝐎𝐍.
Proof. intros. apply enum_operative; auto. Qed.

(* 阿列夫数是基数 *)
Lemma aleph_is_card : ∀ α, α ⋵ 𝐎𝐍 → is_card (ℵ α).
Proof. intros. apply aleph_is_infcard; auto. Qed.
Local Hint Resolve aleph_is_card : core.

(* 阿列夫数是无限集 *)
Lemma aleph_infinite : ∀ α, α ⋵ 𝐎𝐍 → infinite (ℵ α).
Proof. intros. apply aleph_is_infcard; auto. Qed.
Local Hint Resolve aleph_infinite : core.

(* 阿列夫数单调增 *)
Theorem aleph_monotone : monotone ℵ.
Proof. apply enum_monotone; auto. Qed.

(* 阿列夫操作具有单射性 *)
Corollary aleph_injective : class_injective ℵ 𝐎𝐍.
Proof. apply enum_injective; auto. Qed.

(* 无限基数都是阿列夫数 *)
Theorem aleph_surjective : class_surjective ℵ 𝐎𝐍 infcard.
Proof. apply enum_surjective; auto. Qed.

(* 阿列夫数等价于无限基数 *)
Theorem aleph_iff_infcard :
  ∀ 𝜅, infcard 𝜅 ↔ ∃ α, α ⋵ 𝐎𝐍 ∧ ℵ α = 𝜅.
Proof. apply enum_iff_class; auto. Qed.

Local Hint Resolve empty_is_ord : core.

(* ==需要选择公理== *)
Theorem aleph_0 : AC_III → ℵ 0 = ℵ₀.
Proof with auto.
  intros AC3.
  apply sub_antisym; apply ord_leq_iff_sub...
  - apply aleph_spec... intros H.
    apply ReplAx in H as [x [Hx _]]. exfalso0.
  - apply cardLeq_to_ord_leq.
    apply aleph0_is_the_least_infinite_card...
    apply aleph_is_infcard...
Qed.

Theorem aleph_suc : ∀α ⋵ 𝐎𝐍, ℵ α⁺ = (ℵ α)₊.
Proof with eauto.
  intros α Hoα.
  apply sub_antisym; apply ord_leq_iff_sub...
  - assert (Hlt: ℵ α ∈ (ℵ α)₊). {
      rewrite card_of_card at 1...
      apply card_suc_has_card.
    }
    apply aleph_spec... split...
    + apply (parent_set_of_infinite_is_infinite (ℵ α))...
      apply ord_leq_iff_sub...
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
Lemma union_of_cards_is_card : ∀ A,
  (∀x ∈ A, is_card x) → is_card (sup A).
Proof with eauto.
  intros A Hcds.
  assert (Hods: is_ords A). {
    intros x Hx. apply card_is_ord. apply Hcds...
  }
  assert (Hou: sup A ⋵ 𝐎𝐍). {
    apply union_of_ords_is_ord...
  }
  exists (sup A). apply card_of_initial_ord.
  split. apply union_of_ords_is_ord...
  intros α Hα Hqn. symmetry in Hqn.
  apply UnionAx in Hα as [κ [Hκ Hα]].
  assert (Hoκ: κ ⋵ 𝐎𝐍). apply Hods...
  assert (Hoα: α ⋵ 𝐎𝐍). eapply ord_is_ords...
  assert (H1: α ⊆ κ). apply ord_leq_iff_sub...
  assert (H2: κ ⋸ sup A). apply ord_sup_is_ub...
  apply ord_leq_iff_sub in H2...
  pose proof (sub_squeeze_to_eqnum _ _ _ H1 H2 Hqn) as [H _].
  apply Hcds in Hκ as [k Heq]. rewrite Heq in Hα, H.
  eapply (card_is_initial_ord k)... symmetry...
Qed.

Theorem aleph_limit : continuous ℵ.
Proof with eauto.
  eapply monotone_operation_continuous_if_range_closed...
  - split. apply aleph_is_infcard. apply aleph_surjective.
  - apply aleph_monotone.
  - intros A Hne HA. split.
    + apply union_of_cards_is_card.
      intros x Hx. apply HA...
    + intros Hfin. apply finite_union in Hfin as [_ Hfin].
      apply EmptyNE in Hne as [a Ha].
      apply Hfin in Ha as Hfina. apply HA in Ha as [_ Hinf]...
Qed.

(* 阿列夫是规范操作 *)
Theorem aleph_normal : normal ℵ.
Proof. split. apply aleph_monotone. apply aleph_limit. Qed.

End Aleph.

(* 序数操作 *)
Module 𝐎𝐍Operation.
Import RecursionSchemaOnOrdinals.

Definition γ := λ y₀ G f y, y =
  match (ixm (dom f = ∅)) with
  | inl _ => y₀
  | inr _ =>
    match (ixm (∃ α, is_suc α ∧ dom f = α)) with
    | inl _ => G f[sup (dom f)]
    | inr _ =>
      match (ixm (∃ 𝜆, is_limit 𝜆 ∧ dom f = 𝜆)) with
      | inl _ => sup (ran f)
      | inr _ => ∅
      end
    end
  end.

Definition Operation := λ y₀ G, Recursion (γ y₀ G).

Lemma γ_functional : ∀ y₀ G f, ∃! y, γ y₀ G f y.
Proof. intros. unfold γ. split; eauto; congruence. Qed.
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
  intros * α Hoα. unfold Operation.
  rewrite (recursion_spec (γ y₀ G) α⁺), dom_of_op_repl...
  destruct (ixm (α⁺ = ∅))... {
    exfalso. eapply ord_suc_neq_0...
  }
  destruct (ixm (∃ β, is_suc β ∧ α⁺ = β)). {
    rewrite sup_of_suc, ap_of_op_repl...
  }
  destruct (ixm (∃ 𝜆, is_limit 𝜆 ∧ α⁺ = 𝜆)); exfalso.
  - destruct e as [𝜆 [_ H]]. apply n0.
    exists 𝜆. split... exists α. split...
  - destruct (ord_is_suc_or_limit α⁺)...
Qed.

Theorem operation_limit : ∀ y₀ G, continuous (Operation y₀ G).
Proof with eauto; try congruence.
  intros * 𝜆 Hne Hlim. unfold Operation.
  assert (H := Hlim). destruct H as [Ho𝜆 _].
  rewrite (recursion_spec (γ y₀ G) 𝜆), dom_of_op_repl...
  destruct (ixm (𝜆 = ∅))...
  destruct (ixm (∃ α, is_suc α ∧ 𝜆 = α)). {
    destruct e as [α [Hsuc Heq]]. subst α.
    exfalso. eapply ord_is_suc_iff_not_limit...
  }
  destruct (ixm (∃ κ, is_limit κ ∧ 𝜆 = κ)).
  - rewrite ran_of_op_repl...
  - exfalso. destruct (ord_is_suc_or_limit 𝜆)...
Qed.

Lemma operation_operative : ∀ y₀ G, y₀ ⋵ 𝐎𝐍 → G:ᶜ 𝐎𝐍 ⇒ 𝐎𝐍 →
  Operation y₀ G :ᶜ 𝐎𝐍 ⇒ 𝐎𝐍.
Proof with auto.
  intros y₀ G Hoy₀ HG.
  unfold class_func, all_in_class, all.
  eapply transfinite_induction_schema_on_ordinals.
  intros α Hoα IH.
  destruct (ord_is_suc_or_limit α)...
  - destruct H as [β [Hoβ Heq]]. subst.
    rewrite operation_suc... apply HG. apply IH...
  - destruct (classic (α = ∅)).
    + subst. rewrite operation_0...
    + rewrite operation_limit...
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

Module AlternativeDefinitionOfAleph.
Import 𝐎𝐍Operation.

Definition ℵ' := Operation ℵ₀ (λ α, α₊).

(* ==需要选择公理== *)
Fact alternative_aleph_correct : AC_III → ∀α ⋵ 𝐎𝐍, ℵ' α = ℵ α.
Proof with auto.
  intros AC3. unfold all_in_class, all.
  eapply transfinite_induction_schema_on_ordinals.
  intros α Hoα IH. unfold ℵ'.
  destruct (ord_is_suc_or_limit α) as [|Hlim]...
  - destruct H as [β [Hoβ Heq]]. subst.
    rewrite operation_suc, aleph_suc...
    f_equal. apply IH...
  - destruct (classic (α = 0)) as [|Hne]. {
      subst. rewrite operation_0, aleph_0...
    }
    rewrite operation_limit, aleph_limit... f_equal.
    apply repl_rewrite. intros ξ Hξ. apply IH...
Qed.

End AlternativeDefinitionOfAleph.

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
  intros α Hoα.
  destruct (ord_is_suc_or_limit α)...
  - destruct H as [β [Hoβ Heq]]. subst. rewrite beth_suc...
  - destruct (classic (α = 0)). subst. rewrite beth_0...
    generalize dependent α.
    set (λ α, is_limit α → α ≠ 0 → is_card (ℶ α)) as ϕ.
    apply (transfinite_induction_schema_on_ordinals ϕ).
    intros α Hoα IH Hne Hlim. unfold ϕ.
    rewrite beth_limit... apply union_of_cards_is_card.
    intros x Hx. apply ReplAx in Hx as [β [Hβ Hx]]. subst x.
    assert (Hoβ: is_ord β). eapply ord_is_ords...
    destruct (ord_is_suc_or_limit β)...
    + destruct H as [δ [Hoδ Heq]]. subst. rewrite beth_suc...
    + destruct (classic (β = 0)). subst. rewrite beth_0...
      apply IH...
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
  unfold class_func, all_in_class, all.
  eapply transfinite_induction_schema_on_ordinals.
  intros α Hoα IH.
  destruct (ord_is_suc_or_limit α) as [|Hlim]...
  - destruct H as [β [Hoβ Heq]]. subst. rewrite beth_suc...
    assert (Hinf: infinite (ℶ β)). apply IH...
    apply cardExp_infinite_iff... apply beth_is_card...
    apply ord_leq_to_cardLeq...
    apply EmptyNI. apply infinite_set_nonempty...
  - destruct (classic (α = 0)) as [|Hne]. subst. rewrite beth_0...
    rewrite beth_limit... intros Hfin.
    apply finite_union in Hfin as [_ Hfin].
    assert (ℶ 0 ∈ {ℶ | ξ ∊ α}). {
      eapply ReplI. apply ord_nq_0_gt_0...
    }
    apply Hfin in H. rewrite beth_0 in H.
    apply aleph0_infinite...
Qed.

(* ℶ数是无限基数 *)
Lemma beth_is_infcard : ℶ:ᶜ 𝐎𝐍 ⇒ infcard.
Proof with auto.
  intros. split... apply beth_is_card... apply beth_infinite...
Qed.

(* ℶ是规范操作 *)
Theorem beth_normal : normal ℶ.
Proof with auto.
  apply operation_normal...
  - intros α Hoα. apply card_is_ord. apply cardExp_is_card.
  - intros α Hoα. apply cardLt_to_ord_lt. rewrite beth_suc...
    apply cardLt_power... apply beth_is_card...
Qed.

End Beth.

(* 连续统假设 *)
Definition CH := ℵ 1 = ℶ 1.
(* 广义连续统假设 *)
Definition GCH := ∀α ⋵ 𝐎𝐍, ℵ α = ℶ α.
