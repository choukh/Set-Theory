(** Based on "Elements of Set Theory" Chapter 8 Part 1 **)
(** Coq coding by choukh, Feb 2021 **)

Require Export ZFC.lib.Ordinal.
Require Import ZFC.lib.Choice.

(*** EST第八章1：𝐎𝐍子类的分离，阿列夫数，ℶ数 ***)

(* 𝐎𝐍子类的分离 *)
Module Import 𝐎𝐍Separation.
(* 序数上的超限递归模式 *)
Import RecursionSchemaOnOrdinals.

Definition is_sub := λ P : set → Prop, ∀ α, P α → is_ord α.
Definition unbounded := λ P : set → Prop, ∀ α, is_ord α → ∃ β, α ∈ β ∧ P β.
Definition γ := λ P f y, P y ∧ y ∉ ran f ∧ ∀x, P x → x ∉ ran f → y ⋸ x.
Definition Sub𝐎𝐍 := λ P, Recursion (γ P).

Local Lemma unbounded_subclass_cannot_be_a_set :
  ∀ P, is_sub P → unbounded P → ¬ ∃ A, ∀ α, P α → α ∈ A.
Proof with auto.
  intros P Hsub Hubd [A Hset]. apply Burali_Forti.
  exists (⋃ A). intros α Hoα. apply UnionAx.
  apply Hubd in Hoα as [β [Hα HP]].
  exists β. split...
Qed.

Local Lemma γ_functional :
  ∀ P f, is_sub P → unbounded P → ∃! y, γ P f y.
Proof with eauto; try congruence.
  intros P f Hsub Hubd. split.
  - destruct (classic (∀ α, P α → α ∈ ran f)). {
      exfalso. eapply unbounded_subclass_cannot_be_a_set...
    }
    apply not_all_ex_not in H as [α H].
    apply imply_to_and in H as [HPα Hα].
    assert (Hoα: is_ord α). apply Hsub...
    set (λ α, P α ∧ α ∉ ran f) as Q.
    set (OrdMin α⁺ Q) as μ.
    pose proof (ordMin_correct α⁺ Q) as [Hμ Hmin]... {
      exists α. split. apply BUnionI2... split...
    }
    fold μ in Hμ, Hmin.
    apply SepE in Hμ as [Hμα [HPμ Hμ]].
    exists μ. split... split...
    intros x HPx Hx.
    destruct (classic (x ∈ α⁺)) as [Hxα|Hxα].
    + assert (x ∈ {ξ ∊ α⁺ | Q}). apply SepI... split...
      apply Hmin in H as []... apply binRelE3 in H...
    + assert (Hoμ: is_ord μ). apply Hsub...
      assert (Hox: is_ord x). apply Hsub...
      destruct (classic (μ = x)) as [|Hnq]...
      apply ord_connected in Hnq as []...
      exfalso. apply Hxα. eapply ord_trans...
  - intros x y [HPx [Hx H1]] [HPy [Hy H2]].
    apply H1 in Hy... apply H2 in Hx...
    destruct Hx; destruct Hy... exfalso.
    eapply ord_not_lt_gt; revgoals...
Qed.
Hint Immediate γ_functional : core.

(* 子类元素是满足P且与之前的元素都不同的最小序数 *)
Lemma subon_spec : ∀ P, is_sub P → unbounded P →
  ∀ α ξ, is_ord α → P ξ → ξ ∉ {Sub𝐎𝐍 P | x ∊ α} → Sub𝐎𝐍 P α ⋸ ξ.
Proof with auto.
  intros P Hsub Hund α Hoα ξ HPξ Hout.
  pose proof (recursion_spec (γ P) α) as [_ [_ Hmin]]...
  apply Hmin... rewrite ran_of_op_repl...
Qed.

(* 子类元素具有性质P *)
Lemma subon_is_P : ∀ P, is_sub P → unbounded P →
  ∀ α, is_ord α → P (Sub𝐎𝐍 P α).
Proof.
  intros P Hsub Hund α Hoα. unfold Sub𝐎𝐍.
  apply (recursion_spec (γ P) α); auto.
Qed.

(* 子类元素是序数 *)
Lemma subon_is_ord : ∀ P, is_sub P → unbounded P →
  ∀ α, is_ord α → is_ord (Sub𝐎𝐍 P α).
Proof.
  intros P Hsub Hund α Hoα. apply Hsub.
  apply subon_is_P; auto.
Qed.
Hint Immediate subon_is_ord : core.

(* 子类元素单调增 *)
Theorem subon_monotone : ∀ P, is_sub P → unbounded P →
  ∀ α, is_ord α → ∀β ∈ α, Sub𝐎𝐍 P β ∈ Sub𝐎𝐍 P α.
Proof with eauto.
  intros P Hsub Hund α Hoα β Hβ.
  assert (Hoβ: is_ord β). eapply ord_is_ords...
  pose proof (recursion_spec (γ P) α) as [Hinf [Hout _]]...
  pose proof (recursion_spec (γ P) β) as [_ [_ Hmin]]...
  fold (Sub𝐎𝐍 P) in *. rewrite ran_of_op_repl in *.
  assert (Sub𝐎𝐍 P α ∉ {Sub𝐎𝐍 P | x ∊ β}). {
    intros H. apply ReplAx in H as [δ [Hδ H]].
    apply Hout. rewrite <- H. apply ReplI. eapply ord_trans...
  }
  apply Hmin in H as []...
  exfalso. apply Hout. rewrite <- H. apply ReplI...
Qed.

(* 子类元素映射具有单射性 *)
Corollary subon_injective : ∀ P, is_sub P → unbounded P →
  ∀ α β, is_ord α → is_ord β → Sub𝐎𝐍 P α = Sub𝐎𝐍 P β → α = β.
Proof with eauto.
  intros P Hsub Hund α β Hoα Hoβ Heq.
  destruct (classic (α = β)) as [|Hnq]... exfalso.
  apply ord_connected in Hnq as []; auto;
  eapply subon_monotone in H; eauto;
  rewrite Heq in H; eapply ord_irrefl; revgoals...
Qed.

(* 满足P的序数都是子类元素 *)
Theorem P_is_subon : ∀ P, is_sub P → unbounded P →
  ∀ ξ, P ξ → ∃ α, is_ord α ∧ ξ = Sub𝐎𝐍 P α.
Proof with eauto; try congruence.
  intros P Hsub Hund ξ H. apply Hsub in H as Hoξ.
  generalize dependent H. generalize dependent ξ.
  set (λ ξ, P ξ → ∃ α, is_ord α ∧ ξ = Sub𝐎𝐍 P α) as ϕ.
  apply (transfinite_induction_schema_on_ordinals ϕ).
  intros ξ Hoξ IH Hinfξ.
  set (λ x α, is_ord α ∧ x = Sub𝐎𝐍 P α) as ψ.
  set {x ∊ ξ | P} as χ.
  set (ϕ_Repl ψ χ) as α.
  assert (Hψ: ∀x ∈ χ, ∃! y, ψ x y). {
    intros x Hx. apply SepE in Hx as [Hx Hinfx]. split.
    - apply IH in Hx as [β [Hoβ Hx]]...
      exists β. split...
    - intros δ ε [Hoδ Hδ] [Hoε Hε].
      eapply subon_injective...
  }
  assert (Hoα: is_ord α). {
    apply transitive_set_well_ordered_by_epsilon_is_ord; revgoals.
    - apply ords_woset. intros x Hx.
      apply ϕ_ReplAx in Hx as [_ [_ [Ho _]]]...
    - intros ε δ Hε Hδ.
      apply ϕ_ReplAx in Hδ as [x [Hx [Hoδ Heqx]]]... subst x.
      assert (Hoε: is_ord ε). eapply ord_is_ords...
      apply ϕ_ReplAx... exists (Sub𝐎𝐍 P ε). repeat split...
      apply SepE1 in Hx. apply SepI.
      + eapply subon_monotone in Hε... eapply ord_trans...
      + apply subon_is_P...
  }
  exists α. split...
  pose proof (recursion_spec (γ P) α) as [_ [Hout Hmin]]...
  fold (Sub𝐎𝐍 P) in *. rewrite ran_of_op_repl in *.
  assert (Hle: Sub𝐎𝐍 P α ⋸ ξ). {
    apply Hmin... intros Hξ.
    apply ReplAx in Hξ as [β [Hβ Heq]].
    apply ϕ_ReplAx in Hβ as [μ [Hμ [Hoβ Heqμ]]]...
    apply SepE1 in Hμ. subst. eapply ord_irrefl; revgoals...
  }
  destruct Hle...
  destruct (classic (ξ = Sub𝐎𝐍 P α)) as [|Hnq]... exfalso.
  apply ord_connected in Hnq as []...
  - eapply ord_not_lt_gt; revgoals...
  - apply Hout. apply ReplAx. exists α. split...
    apply ϕ_ReplAx... exists (Sub𝐎𝐍 P α). repeat split...
    apply SepI... apply subon_is_P...
Qed.

(* 子类元素等价于满足P的序数 *)
Theorem subon_iff_P : ∀ P, is_sub P → unbounded P →
  ∀ ξ, P ξ ↔ ∃ α, is_ord α ∧ ξ = Sub𝐎𝐍 P α.
Proof with auto.
  split. apply P_is_subon...
  intros [α [Hoα Heq]]. subst. apply subon_is_P...
Qed.

End 𝐎𝐍Separation.

(* 阿列夫数 *)
Definition ℵ := Sub𝐎𝐍 infcard.

Lemma infcard_is_sub : is_sub infcard.
Proof. exact infcard_is_ord. Qed.
Local Hint Resolve infcard_is_sub : core.

Lemma infcard_unbounded : unbounded infcard.
Proof with eauto.
  intros α Hoα.
  apply all_ord_ex_larger_card in Hoα as [𝜅 [H𝜅 Hα]].
  assert (Hcs: is_card (𝜅 + ℵ₀))...
  assert (Hos: is_ord (𝜅 + ℵ₀))...
  apply all_ord_ex_larger_card in Hos as [𝜆 [H𝜆 Hlt]].
  exists 𝜆. split.
  - eapply ord_trans...
    cut (𝜅 <𝐜 𝜆). apply cardLt_iff_ord_lt.
    eapply cardLeq_lt_tran; revgoals.
    apply cardLt_iff_ord_lt... apply cardAdd_enlarge...
  - split... apply (parent_set_of_infinite_is_infinite (𝜅 + ℵ₀)).
    apply ord_leq_iff_sub... apply cardAdd_infinite_iff...
Qed.
Local Hint Resolve infcard_unbounded : core.

(* 阿列夫数是与之前的阿列夫数都不同的最小无限基数 *)
Lemma aleph_spec : ∀ α ξ, is_ord α →
  infcard ξ → ξ ∉ {ℵ | x ∊ α} → ℵ α ⋸ ξ.
Proof. apply subon_spec; auto. Qed.

(* 阿列夫数是无限基数 *)
Lemma aleph_is_infcard : ∀ α, is_ord α → infcard (ℵ α).
Proof. apply subon_is_P; auto. Qed.

(* 阿列夫数是序数 *)
Lemma aleph_is_ord : ∀ α, is_ord α → is_ord (ℵ α).
Proof. intros. apply subon_is_ord; auto. Qed.
Local Hint Resolve aleph_is_ord : core.

(* 阿列夫数是基数 *)
Lemma aleph_is_card : ∀ α, is_ord α → is_card (ℵ α).
Proof. intros. apply aleph_is_infcard; auto. Qed.
Local Hint Resolve aleph_is_card : core.

(* 阿列夫数是无限集 *)
Lemma aleph_infinite : ∀ α, is_ord α → infinite (ℵ α).
Proof. intros. apply aleph_is_infcard; auto. Qed.
Local Hint Resolve aleph_infinite : core.

(* 阿列夫数单调增 *)
Theorem aleph_monotone : ∀ α, is_ord α → ∀β ∈ α, ℵ β ∈ ℵ α.
Proof. apply subon_monotone; auto. Qed.

(* 阿列夫映射具有单射性 *)
Corollary aleph_injective : ∀ α β, is_ord α → is_ord β →
  ℵ α = ℵ β → α = β.
Proof. apply subon_injective; auto. Qed.

(* 无限基数都是阿列夫数 *)
Theorem infcard_is_aleph : ∀ 𝜅, infcard 𝜅 →
  ∃ α, is_ord α ∧ 𝜅 = ℵ α.
Proof. apply P_is_subon; auto. Qed.

(* 阿列夫数等价于无限基数 *)
Theorem aleph_iff_infcard :
  ∀ 𝜅, infcard 𝜅 ↔ ∃ α, is_ord α ∧ 𝜅 = ℵ α.
Proof. apply subon_iff_P; auto. Qed.

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

Theorem aleph_suc : ∀ α, is_ord α → ℵ α⁺ = (ℵ α)₊.
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
  (∀x ∈ A, is_card x) → is_card (⋃ A).
Proof with eauto.
  intros A Hcds.
  assert (Hods: is_ords A). {
    intros x Hx. apply card_is_ord. apply Hcds...
  }
  assert (Hou: is_ord (sup A)). {
    apply union_of_ords_is_ord...
  }
  exists (⋃ A). apply card_of_initial_ord.
  split. apply union_of_ords_is_ord...
  intros α Hα Hqn. symmetry in Hqn.
  apply UnionAx in Hα as [κ [Hκ Hα]].
  assert (Hoκ: is_ord κ). apply Hods...
  assert (Hoα: is_ord α). eapply ord_is_ords...
  assert (H1: α ⊆ κ). apply ord_leq_iff_sub...
  assert (H2: κ ⋸ sup A). apply ord_sup_is_ub...
  apply ord_leq_iff_sub in H2...
  pose proof (sub_squeeze_to_eqnum _ _ _ H1 H2 Hqn) as [H _].
  apply Hcds in Hκ as [k Heq]. rewrite Heq in Hα, H.
  eapply (card_is_initial_ord k)... symmetry...
Qed.

Theorem aleph_limit : ∀ α, α ≠ ∅ → is_limit α → ℵ α = ⋃{ℵ | β ∊ α}.
Proof with eauto.
  intros α Hne Hlim.
  assert (H := Hlim). destruct H as [Hoα _].
  assert (Hos: is_ords {ℵ | β ∊ α}). {
    intros x Hx.
    apply ReplAx in Hx as [β [Hβ Hx]]. subst x.
    apply aleph_is_ord. eapply ord_is_ords...
  }
  assert (Hou: is_ord ⋃{ℵ | β ∊ α}). {
    apply union_of_ords_is_ord...
  }
  assert (Hcu: infcard ⋃{ℵ | β ∊ α}). {
    split.
    - apply union_of_cards_is_card.
      intros x Hx. apply ReplAx in Hx as [β [Hβ H]]. subst x.
      apply aleph_is_card. apply (ord_is_ords α)...
    - intros Hfin. apply finite_union in Hfin as [_ Hfin].
      apply EmptyNE in Hne as [β Hβ].
      assert (Hoβ: is_ord β). eapply ord_is_ords; revgoals...
      assert (ℵ β ∈ {ℵ | β ∊ α}). eapply ReplI...
      apply Hfin in H. eapply aleph_infinite...
  }
  apply sub_antisym; apply ord_leq_iff_sub...
  - apply aleph_spec... intros H.
    apply ReplAx in H as [β [Hβ Heq]].
    assert (Hoβ: is_ord β). eapply ord_is_ords; revgoals...
    pose proof (ord_sup_is_ub {ℵ | β ∊ α}) as [_ Hub]...
    unfold sup in Hub. rewrite <- Heq in Hub.
    assert (ℵ β⁺ ∈ {ℵ | β ∊ α}). {
      eapply ReplI. apply suc_in_limit...
    }
    apply Hub in H. apply (ord_not_leq_gt (ℵ β⁺) (ℵ β))...
    apply aleph_monotone...
  - apply ord_sup_correct... split... intros x Hx.
    apply ReplAx in Hx as [β [Hβ Hx]]. subst x.
    left. apply aleph_monotone...
Qed.
