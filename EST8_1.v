(** Based on "Elements of Set Theory" Chapter 8 Part 1 **)
(** Coq coding by choukh, Feb 2021 **)

Require Export ZFC.lib.Ordinal.
Require Import ZFC.lib.Choice.

(*** EST第八章1：𝐎𝐍类函数，𝐎𝐍子类的分离，阿列夫数，𝐎𝐍规范操作，ℶ数 ***)

(* 𝐎𝐍类函数 *)
Module Import 𝐎𝐍Func.

(* 𝐎𝐍类函数的单调性 *)
Definition monotone := λ F, ∀ α, is_ord α → ∀β ∈ α, F β ∈ F α.
(* 𝐎𝐍类函数的连续性 *)
Definition continuous := λ F, ∀ 𝜆, 𝜆 ≠ ∅ → is_limit 𝜆 →
  F 𝜆 = ⋃{F | α ∊ 𝜆}.
(* 𝐎𝐍类函数的规范性 *)
Definition normal := λ F, monotone F ∧ continuous F.

End 𝐎𝐍Func.

(* 𝐎𝐍子类的分离 *)
Module 𝐎𝐍Separation.
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
  monotone (Sub𝐎𝐍 P).
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
Section Aleph.
Import 𝐎𝐍Separation.

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
Theorem aleph_monotone : monotone ℵ.
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

Theorem aleph_limit : continuous ℵ.
Proof with eauto.
  intros 𝜆 Hne Hlim.
  assert (H := Hlim). destruct H as [Ho𝜆 _].
  assert (Hos: is_ords {ℵ | α ∊ 𝜆}). {
    intros x Hx.
    apply ReplAx in Hx as [α [Hα Hx]]. subst x.
    apply aleph_is_ord. eapply ord_is_ords...
  }
  assert (Hou: is_ord ⋃{ℵ | α ∊ 𝜆}). {
    apply union_of_ords_is_ord...
  }
  assert (Hcu: infcard ⋃{ℵ | α ∊ 𝜆}). {
    split.
    - apply union_of_cards_is_card.
      intros x Hx. apply ReplAx in Hx as [α [Hα H]]. subst x.
      apply aleph_is_card. apply (ord_is_ords 𝜆)...
    - intros Hfin. apply finite_union in Hfin as [_ Hfin].
      apply EmptyNE in Hne as [α Hα].
      assert (Hoα: is_ord α). eapply ord_is_ords; revgoals...
      assert (ℵ α ∈ {ℵ | α ∊ 𝜆}). eapply ReplI...
      apply Hfin in H. eapply aleph_infinite...
  }
  apply sub_antisym; apply ord_leq_iff_sub...
  - apply aleph_spec... intros H.
    apply ReplAx in H as [α [Hα Heq]].
    assert (Hoα: is_ord α). eapply ord_is_ords; revgoals...
    pose proof (ord_sup_is_ub {ℵ | α ∊ 𝜆}) as [_ Hub]...
    unfold sup in Hub. rewrite <- Heq in Hub.
    assert (ℵ α⁺ ∈ {ℵ | α ∊ 𝜆}). {
      eapply ReplI. apply suc_in_limit...
    }
    apply Hub in H. apply (ord_not_leq_gt (ℵ α⁺) (ℵ α))...
    apply aleph_monotone...
  - apply ord_sup_correct... split... intros x Hx.
    apply ReplAx in Hx as [α [Hα Hx]]. subst x.
    left. apply aleph_monotone...
Qed.

(* 阿列夫是规范操作 *)
Theorem aleph_normal : normal ℵ.
Proof. split. apply aleph_monotone. apply aleph_limit. Qed.

End Aleph.

(* 𝐎𝐍规范操作 *)
Module 𝐎𝐍NormalOperation.
Import RecursionSchemaOnOrdinals.

Definition γ := λ y₀ G f y, y =
  match (ixm (dom f = ∅)) with
  | inl _ => y₀
  | inr _ =>
    match (ixm (∃ α, is_suc α ∧ dom f = α)) with
    | inl _ => G f[sup (dom f)]
    | inr _ =>
      match (ixm (∃ 𝜆, is_limit 𝜆 ∧ dom f = 𝜆)) with
      | inl _ => ⋃(ran f)
      | inr _ => ∅
      end
    end
  end.

Definition operative := λ G, ∀ α, is_ord α → is_ord (G α).
Definition Operation := λ y₀ G, Recursion (γ y₀ G).

Lemma γ_functional : ∀ y₀ G f, ∃! y, γ y₀ G f y.
Proof. intros. unfold γ. split; eauto; congruence. Qed.
Hint Immediate γ_functional : core.

Theorem operation_0 : ∀ y₀ G, Operation y₀ G ∅ = y₀.
Proof with auto.
  intros. unfold Operation.
  rewrite (recursion_spec (γ y₀ G) ∅), dom_of_op_repl...
  destruct (ixm (∅ = ∅))... exfalso...
Qed.

Theorem operation_suc : ∀ y₀ G α, is_ord α →
  Operation y₀ G α⁺ = G (Operation y₀ G α).
Proof with eauto.
  intros * Hoα. unfold Operation.
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

Lemma ran_of_operation : ∀ y₀ G, is_ord y₀ → operative G →
  ∀ α, is_ord α → is_ord (Operation y₀ G α).
Proof with auto.
  intros * Hoy₀ Hop.
  eapply transfinite_induction_schema_on_ordinals.
  intros α Hoα IH.
  destruct (ord_is_suc_or_limit α)...
  - destruct H as [β [Hoβ Heq]]. subst.
    rewrite operation_suc... apply Hop. apply IH...
  - destruct (classic (α = ∅)).
    + subst. rewrite operation_0...
    + rewrite operation_limit...
      apply union_of_ords_is_ord. intros x Hx.
      apply ReplAx in Hx as [β [Hβ Heq]]. subst. apply IH...
Qed.

Definition ascending := λ y₀ G, ∀ α, is_ord α →
  Operation y₀ G α ∈ G (Operation y₀ G α).

Lemma operation_suc_monotone :
  ∀ y₀ G, is_ord y₀ → operative G → ascending y₀ G →
  ∀ α, is_suc α → ∀β ∈ α, Operation y₀ G β ∈ Operation y₀ G α.
Proof with eauto.
  intros * Hoy₀ Hop Hasc α Hsuc β Hβ.
  assert (Hoα: is_ord α). {
    destruct Hsuc as [δ [Hoδ Heq]].
    subst. apply ord_suc_is_ord...
  }
  generalize dependent Hsuc.
  generalize dependent Hβ.
  generalize dependent α.
  set (λ α, β ∈ α → is_suc α → Operation y₀ G β ∈ Operation y₀ G α) as ϕ.
  apply (transfinite_induction_schema_on_ordinals ϕ).
  intros α Hoα IH Hβ [δ [Hoδ Heq]]. subst.
  assert (Hoβ: is_ord β). eapply ord_is_ords; revgoals...
  assert (Hoo: is_ord (Operation y₀ G δ)). apply ran_of_operation...
  rewrite operation_suc...
  apply BUnionE in Hβ as [].
  - destruct (ord_is_suc_or_limit δ)...
    + eapply ord_trans. apply Hop...
      apply IH... apply Hasc...
    + destruct (classic (δ = ∅)). subst. exfalso0.
      eapply ord_trans; revgoals...
      rewrite (operation_limit _ _ δ)...
      eapply FUnionI. apply suc_in_limit... apply IH...
      rewrite <- ord_suc_preserve_lt... exists β. split...
  - apply SingE in H; subst. apply Hasc...
Qed.

Lemma operation_monotone :
  ∀ y₀ G, is_ord y₀ → operative G → ascending y₀ G →
  monotone (Operation y₀ G).
Proof with eauto.
  intros * Hoy₀ Hop Hasc α Hoα β Hβ.
  assert (Hoβ: is_ord β). eapply ord_is_ords...
  destruct (classic (α = ∅)). subst. exfalso0.
  destruct (ord_is_suc_or_limit α)...
  - apply operation_suc_monotone...
  - rewrite (operation_limit _ _ α)...
    eapply FUnionI. apply suc_in_limit...
    eapply operation_suc_monotone... exists β. split...
Qed.

Theorem operation_normal :
  ∀ y₀ G, is_ord y₀ → operative G → ascending y₀ G →
  normal (Operation y₀ G).
Proof.
  intros. split. apply operation_monotone; auto.
  apply operation_limit.
Qed.

End 𝐎𝐍NormalOperation.

Module AlternativeDefinitionOfAleph.
Import 𝐎𝐍NormalOperation.

Definition ℵ' := Operation ℵ₀ (λ α, α₊).

(* ==需要选择公理== *)
Fact alternative_aleph_correct : AC_III →
  ∀ α, is_ord α → ℵ' α = ℵ α.
Proof with auto.
  intros AC3.
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
Import 𝐎𝐍NormalOperation.

Definition ℶ := Operation ℵ₀ (λ α, 2 ^ α).

Theorem beth_0 : ℶ 0 = ℵ₀.
Proof. apply operation_0. Qed.

Theorem beth_suc : ∀ α, is_ord α → ℶ α⁺ = 2 ^ ℶ α.
Proof. apply operation_suc. Qed.

Theorem beth_limit : continuous ℶ.
Proof. apply operation_limit. Qed.

(* ℶ数是基数 *)
Lemma beth_is_card : ∀ α, is_ord α → is_card (ℶ α).
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
Local Hint Resolve beth_is_card : core.

(* ℶ数是序数 *)
Lemma beth_is_ord : ∀ α, is_ord α → is_ord (ℶ α).
Proof. intros. apply card_is_ord; auto. Qed.

(* ℶ数是无限集 *)
Lemma beth_infinite : ∀ α, is_ord α → infinite (ℶ α).
Proof with nauto.
  eapply transfinite_induction_schema_on_ordinals.
  intros α Hoα IH.
  destruct (ord_is_suc_or_limit α) as [|Hlim]...
  - destruct H as [β [Hoβ Heq]]. subst. rewrite beth_suc...
    assert (Hinf: infinite (ℶ β)). apply IH...
    apply cardExp_infinite_iff...
    apply ord_leq_to_cardLeq...
    apply EmptyNI. apply infinite_set_nonempty...
  - destruct (classic (α = 0)) as [|Hne]. subst. rewrite beth_0...
    rewrite beth_limit... intros Hfin.
    apply finite_union in Hfin as [_ Hfin].
    assert (ℶ 0 ∈ {ℶ | ξ ∊ α}). {
      apply ReplAx. exists 0. split...
      apply ord_nq_0_gt_0...
    }
    apply Hfin in H. rewrite beth_0 in H.
    apply aleph0_infinite...
Qed.

(* ℶ数是无限基数 *)
Lemma beth_is_infcard : ∀ α, is_ord α → infcard (ℶ α).
Proof with auto.
  intros. split... apply beth_infinite...
Qed.

(* ℶ是规范操作 *)
Theorem beth_normal : normal ℶ.
Proof with auto.
  apply operation_normal...
  - intros α Hoα. apply card_is_ord. apply cardExp_is_card.
  - intros α Hoα. apply cardLt_to_ord_lt. apply cardLt_power...
Qed.

End Beth.

Definition CH := ℵ 1 = ℶ 1.
Definition GCH := ∀ α, is_ord α → ℵ α = ℶ α.
