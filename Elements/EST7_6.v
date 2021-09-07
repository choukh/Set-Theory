(** Adapted from "Elements of Set Theory" Chapter 7 **)
(** Coq coding by choukh, Jan 2021 **)

Require Export ZFC.Lib.Ordinal.
Require Import ZFC.Lib.FuncFacts.

(*** EST第七章6：序数上的超限递归模式，冯·诺伊曼宇宙，集合的秩，正则公理 ***)

(* 序数上的超限递归模式 *)
Import RecursionOnOrdinals.

(* 冯·诺伊曼宇宙层级 *)
Definition V := Recursion (λ A, ⋃{Power x | x ∊ A}).

(* 宇宙层级的递推公式 *)
Theorem V_hierarchy : ∀α ⋵ 𝐎𝐍, V α = ⋃{𝒫 (V β) | β ∊ α}.
Proof with eauto; try congruence.
  intros α Hoα. unfold V.
  rewrite recursion_spec at 1...
  ext Hx.
  - apply FUnionE in Hx as [y [Hy Hx]].
    apply ReplAx in Hy as [β [Hβ Hy]].
    eapply FUnionI...
  - apply FUnionE in Hx as [β [Hβ Hx]].
    eapply FUnionI... apply ReplI...
Qed.

Lemma V_intro : ∀α ⋵ 𝐎𝐍, ∀β ∈ α, ∀x ∈ 𝒫 (V β), x ∈ V α.
Proof with eauto.
  intros α Hoα β Hβ x Hx.
  rewrite V_hierarchy... eapply FUnionI...
Qed.

Lemma V_elim : ∀α ⋵ 𝐎𝐍, ∀x ∈ V α, ∃β ∈ α, x ∈ 𝒫 (V β).
Proof with auto.
  intros α Hoα x Hx.
  rewrite V_hierarchy in Hx...
  apply FUnionE in Hx as [β [Hβ Hx]].
  exists β. split...
Qed.

Lemma V_trans : ∀α ⋵ 𝐎𝐍, trans (V α).
Proof with eauto.
  intros α Hoα.
  cut (∀δ ⋵ 𝐎𝐍, ∀α ∈ δ, trans (V α)). {
    intros H. eapply (H α⁺)...
  }
  clear Hoα α. intros δ Hoδ α Hα.
  set {α ∊ δ | trans (V α)} as δ'.
  replace δ with δ' in Hα. apply SepE2 in Hα... clear Hα α.
  eapply transfinite_induction. apply ord_woset...
  split. intros α Hα. apply SepE1 in Hα...
  intros α Hα Hseg. rewrite seg_of_ord in Hseg...
  apply SepI... apply trans_sub. intros x Hx.
  assert (Hoα: α ⋵ 𝐎𝐍). eapply ord_is_ords...
  apply V_elim in Hx as [β [Hβ Hx]]...
  apply Hseg in Hβ as H. apply SepE2 in H. apply ex4_3 in H...
  intros w Hw. eapply V_intro...
Qed.

Theorem V_sub : ∀α ⋵ 𝐎𝐍, ∀β ∈ α, V β ⊆ V α.
Proof with eauto.
  intros α Hoα β Hβ.
  apply trans_sub. apply V_trans...
  eapply V_intro... apply all_in_its_power.
Qed.

Theorem V_0 : V ∅ = ∅.
Proof with auto.
  ext Hx.
  - apply V_elim in Hx as [n [Hn _]]... exfalso0.
  - exfalso0.
Qed.

Fact V_1 : V 1 = 1.
Proof with nauto.
  ext Hx.
  - apply V_elim in Hx as [n [Hn Hx]]...
    rewrite one in Hn. apply SingE in Hn. subst.
    rewrite V_0, power_empty, <- one in Hx...
  - eapply V_intro... apply suc_has_0...
    rewrite pred, V_0, power_empty, <- one...
Qed.

Fact V_2 : V 2 = 2.
Proof with nauto.
  ext Hx.
  - apply V_elim in Hx as [n [Hn Hx]]...
    rewrite two in *. apply TwoE in Hn as []; subst.
    + rewrite V_0, power_empty in Hx...
      apply SingE in Hx. apply TwoI3...
    + rewrite <- one, V_1, one, power_one in Hx...
  - rewrite two in Hx. apply TwoE in Hx as []; subst.
    + eapply V_intro... rewrite two. apply TwoI1.
      rewrite V_0, power_empty. apply SingI.
    + eapply V_intro... rewrite two. apply TwoI2.
      rewrite <- one, V_1, one, power_one. apply TwoI2.
Qed.

Theorem V_suc : ∀α ⋵ 𝐎𝐍, V α⁺ = 𝒫 (V α).
Proof with eauto.
  intros α Hoα.
  ext Hx.
  - apply V_elim in Hx as [β [Hβ Hx]]...
    apply BUnionE in Hβ as []; [|apply SingE in H; subst]...
    pose proof (V_sub α Hoα β) as Hsub.
    apply ex1_3 in Hsub...
  - eapply V_intro; revgoals...
Qed.

Theorem V_limit : ∀α ⋵ 𝐎𝐍ˡⁱᵐ, V α = ⋃{V β | β ∊ α}.
Proof with eauto.
  intros α Hlim.
  assert (H := Hlim). destruct H as [Hoα _].
  apply sub_antisym; intros x Hx.
  - apply V_elim in Hx as [β [Hβ Hx]]...
    rewrite <- V_suc in Hx; [|eapply ord_is_ords]...
    eapply FUnionI; revgoals... apply sucord_in_limord...
  - apply FUnionE in Hx as [β [Hβ Hx]]. eapply V_sub...
Qed.

(* 良基集 *)
Definition grounded := λ x, ∃α ⋵ 𝐎𝐍, x ⊆ V α.
Notation 𝐖𝐅 := grounded.

Definition rank_spec := λ A α, α ⋵ 𝐎𝐍 ∧ A ⊆ V α ∧
  ∀β ⋵ 𝐎𝐍, A ⊆ V β → α ⋸ β.

Lemma rank_exists : ∀A ⋵ 𝐖𝐅, ∃! α, rank_spec A α.
Proof with eauto; try congruence.
  intros A [α [Hoα Hsubα]].
  set {ξ ∊ α⁺ | A ⊆ V ξ} as B.
  destruct (ords_woset B) as [_ Hmin]. {
    intros x Hx. apply SepE1 in Hx.
    eapply ord_is_ords; revgoals...
  }
  pose proof (Hmin B) as [μ [Hμ Hle]]... {
    exists α. apply SepI...
  }
  apply SepE in Hμ as [Hμ Hsubμ].
  assert (Hoμ: μ ⋵ 𝐎𝐍). {
    eapply ord_is_ords; revgoals...
  }
  rewrite <- unique_existence. split.
  - exists μ. repeat split...
    intros β Hoβ Hsubβ.
    apply ord_le_iff_not_gt... intros Hβ.
    assert (β ∈ B). {
      apply SepI... eapply ord_trans...
    }
    apply Hle in H as [].
    + apply binRelE3 in H. eapply ord_not_lt_gt; revgoals...
    + eapply ord_not_lt_self...
  - intros a b [Ha [H11 H12]] [Hb [H21 H22]].
    apply H12 in H21... apply H22 in H11...
    apply ord_le_iff_sub in H11...
    apply ord_le_iff_sub in H21...
    apply sub_antisym...
Qed.

(* 秩 *)
Definition rank := λ A, describe (rank_spec A).

Lemma rank_spec_intro : ∀A ⋵ 𝐖𝐅, rank_spec A (rank A).
Proof.
  intros A Hgnd. apply (desc_spec (rank_spec A)).
  apply rank_exists. apply Hgnd.
Qed.

(* 秩是序数 *)
Lemma rank_is_ord : ∀ A, A ⋵ 𝐖𝐅 → rank A ⋵ 𝐎𝐍.
Proof.
  intros A Hgnd. apply rank_spec_intro. apply Hgnd.
Qed.
Global Hint Immediate rank_is_ord : core.

Lemma grounded_in_rank : ∀A ⋵ 𝐖𝐅, A ⊆ V (rank A).
Proof.
  intros A Hgnd. apply rank_spec_intro. apply Hgnd.
Qed.

Lemma grounded_under_rank : ∀A ⋵ 𝐖𝐅, A ∈ V (rank A)⁺.
Proof with auto.
  intros A Hgnd. rewrite V_suc...
  apply PowerAx. apply grounded_in_rank...
Qed.

(* 良基集的成员也是良基集 *)
Theorem member_grounded : ∀A ⋵ 𝐖𝐅, A ⪽ 𝐖𝐅.
Proof with eauto.
  intros A Hgnd a Ha.
  apply grounded_in_rank in Hgnd as HA. apply HA in Ha.
  apply V_elim in Ha as [β [Hβ Ha]]... apply PowerAx in Ha.
  exists β. split... eapply ord_is_ords; revgoals...
Qed.

(* 良基集的秩大于成员的秩 *)
Theorem rank_of_member : ∀A ⋵ 𝐖𝐅, ∀a ∈ A, rank a ∈ rank A.
Proof with eauto; try congruence.
  intros A Hgnd a Ha.
  apply grounded_in_rank in Hgnd as HA. apply HA in Ha.
  apply V_elim in Ha as [β [Hβ Ha]]... apply PowerAx in Ha.
  assert (Hoβ: β ⋵ 𝐎𝐍). eapply ord_is_ords; revgoals...
  assert (Hgnda: a ⋵ 𝐖𝐅). exists β. split... 
  pose proof (rank_spec_intro a Hgnda) as [_ [_ H]].
  pose proof (H β Hoβ Ha) as []... eapply ord_trans...
Qed.

Section RankRecurrence.

Let Ω := λ A, {(rank a)⁺ | a ∊ A}.
Let α := λ A, ⋃ (Ω A).

Local Lemma Ω_is_ords : ∀ A, A ⪽ 𝐖𝐅 → Ω A ⪽ 𝐎𝐍.
Proof.
  intros A Hgnd x Hx.
  apply ReplAx in Hx as [a [Ha Hx]].
  subst x. apply ord_suc_is_ord.
  apply rank_is_ord. apply Hgnd. apply Ha.
Qed.

Local Lemma α_is_ord : ∀ A, A ⪽ 𝐖𝐅 → α A ⋵ 𝐎𝐍.
Proof.
  intros A Hgnd. apply union_of_ords_is_ord.
  apply Ω_is_ords. apply Hgnd.
Qed.

Local Lemma grounded_in_α : ∀ A, A ⪽ 𝐖𝐅 → A ⊆ V (α A).
Proof with eauto; try congruence.
  intros A Hgnd a Ha. apply Hgnd in Ha as Hgnda.
  apply grounded_under_rank in Hgnda.
  assert ((rank a)⁺ ⋸ (α A)). {
    apply ord_sup_is_ub. apply Ω_is_ords...
    apply ReplAx. exists a. split...
  }
  destruct H as []... eapply V_sub... apply α_is_ord...
Qed.

(* 成员都是良基集的集合是良基集 *)
Theorem grounded_intro : ∀ A, A ⪽ 𝐖𝐅 → A ⋵ 𝐖𝐅.
Proof with auto.
  intros A Hgnd. exists (α A).
  split. apply α_is_ord... apply grounded_in_α...
Qed.

(* 秩的递推公式 *)
Theorem rank_recurrence : ∀A ⋵ 𝐖𝐅, rank A = α A.
Proof with eauto.
  intros A Hgnd.
  assert (Hoα: α A ⋵ 𝐎𝐍). {
    apply α_is_ord. apply member_grounded...
  }
  apply sub_antisym.
  - apply ord_le_iff_sub... apply rank_spec_intro...
    apply grounded_in_α. apply member_grounded...
  - intros x Hx.
    apply FUnionE in Hx as [a [Ha Hx]].
    apply rank_of_member in Ha...
    apply BUnionE in Hx as [].
    eapply ord_trans... apply SingE in H. subst...
Qed.

End RankRecurrence.

(* ex7_26 序数是良基集 *)
Fact ord_grounded : 𝐎𝐍 ⫃ 𝐖𝐅.
Proof.
  ord_induction. intros α Hα.
  now apply grounded_intro.
Qed.

(* ex7_26 序数的秩等于自身 *)
Fact rank_of_ord : ∀α ⋵ 𝐎𝐍, rank α = α.
Proof with eauto; try congruence.
  ord_induction. intros α Hα IH.
  rewrite rank_recurrence; [|apply ord_grounded]...
  ext Hx.
  - apply FUnionE in Hx as [β [Hβ Hx]].
    rewrite IH in Hx...
    apply BUnionE in Hx as [].
    eapply ord_trans... apply SingE in H...
  - apply IH in Hx as Heq.
    eapply FUnionI... rewrite Heq. apply suc_has_n.
Qed.

(* 任意集合都是良基集等价于正则公理 *)
Theorem all_grounded_iff_regularity : (∀ A, A ⋵ 𝐖𝐅) ↔ Regularity.
Proof with eauto; try congruence.
  split.
  - intros Hgnd A Hne.
    set {rank a | a ∊ A} as Ω.
    destruct (ords_woset Ω) as [_ Hmin]. {
      intros x Hx. apply ReplAx in Hx as [a [_ Hx]]. subst...
    }
    pose proof (Hmin Ω) as [μ [Hμ Hle]]... {
      apply EmptyNE in Hne as [a Ha].
      exists (rank a). apply ReplI...
    }
    apply ReplAx in Hμ as [m [Hm Hμ]].
    exists m. split...
    ext Hx; [|exfalso0].
    apply BInterE in Hx as [Hxm HxA].
    apply rank_of_member in Hxm; [|eapply member_grounded]...
    assert (rank x ∈ Ω). apply ReplI...
    exfalso. apply Hle in H as [].
    + apply binRelE3 in H. eapply ord_not_lt_gt; revgoals...
      eapply ord_is_ords; revgoals...
    + subst. eapply (ord_not_lt_self (rank x)); revgoals...
  - intros Reg.
    contra.
    apply not_all_ex_not in H as [c Hngc].
    set (𝗧𝗖 {c,}) as B.
    set {x ∊ B | ¬ x ⋵ 𝐖𝐅} as A.
    pose proof (Reg A) as [m [Hm H0]]. {
      apply EmptyNI. exists c. apply SepI...
      apply tc_contains...
    }
    apply SepE in Hm as [Hmb Hngm].
    apply Hngm. apply grounded_intro.
    intros x Hx. contra.
    assert (Hx': x ∈ A). apply SepI... eapply tc_trans...
    eapply EmptyNI in H0... exists x. apply BInterI...
Qed.

Module RegularityConsequences.

Axiom RegAx : Regularity.

(* 任意集合都是良基集 *)
Fact all_grounded : ∀ A, A ⋵ 𝐖𝐅.
Proof. apply all_grounded_iff_regularity. apply RegAx. Qed.
Local Hint Resolve all_grounded : core.

Fact rank_0 : ∀ a, rank a = ∅ → a = ∅.
Proof with eauto.
  intros a Ha. ext Hx; [exfalso|exfalso0].
  eapply EmptyE... apply rank_of_member...
Qed.

Fact rank_1 : ∀ a, rank a = 1 → a = 1.
Proof with neauto.
  intros a Ha. ext Hx.
  - apply rank_of_member in Hx...
    rewrite Ha, one in Hx. apply SingE in Hx.
    apply rank_0 in Hx. subst x. apply suc_has_0...
  - pose proof (rank_spec_intro a) as [_ [H _]]...
    rewrite Ha, V_1, one in H.
    apply subset_of_one in H as []; subst a.
    + rewrite rank_of_ord in Ha...
      exfalso. eapply suc_neq_0...
    + rewrite one in Hx...
Qed.

Fact rank_2 : ∀ a, rank a = 2 → a = 2 ∨ a = {1,}.
Proof with neauto.
  intros a Ha. destruct (classic (a = {1,})) as [|Hnq]... left.
  ext Hx.
  - apply rank_of_member in Hx...
    rewrite Ha, two in Hx. apply TwoE in Hx as [Hx|Hx].
    + apply rank_0 in Hx. subst x. apply BUnionI1...
    + rewrite <- one in Hx.
      apply rank_1 in Hx. subst x. apply BUnionI2...
  - pose proof (rank_spec_intro a) as [_ [H _]]...
    rewrite Ha, V_2 in H... apply PowerAx in H.
    rewrite power_two in H. apply BUnionE in H as [].
    + apply three_iff in H as [|[]]; subst;
      rewrite rank_of_ord in Ha; nauto; exfalso.
      * eapply suc_neq_0...
      * apply contra_1_2...
    + apply SingE in H. congruence.
Qed.

(* 任意集合均存在∈极小元 *)
Lemma ex_epsilon_minimal : ∀ A, A ≠ ∅ → ∃ m, ε_minimal m A.
Proof with auto.
  intros * Hne.
  pose proof (RegAx A Hne) as [m [Hm H]].
  exists m. split... intros x Hx.
  destruct (classic (x = m))... left.
  intros Hxm. eapply EmptyNI in H...
  exists x. apply BInterI...
Qed.

(* 不存在集合的无穷降链 *)
Theorem no_descending_chain : ¬ ∃ f,
  is_function f ∧ dom f = ω ∧ ∀n ∈ ω, f[n⁺] ∈ f[n].
Proof with nauto; try congruence.
  intros [f [Hf [Hd Hr]]].
  pose proof (RegAx (ran f)) as [m [Hm H0]]. {
    apply EmptyNI. exists (f[∅]).
    eapply ranI. apply func_correct... rewrite Hd...
  }
  apply ranE in Hm as Hp. destruct Hp as [n Hp].
  apply domI in Hp as Hn. apply func_ap in Hp... subst m.
  eapply EmptyNI in H0... exists (f[n⁺]).
  apply BInterI. apply Hr... eapply ranI. apply func_correct...
  rewrite Hd. apply ω_inductive...
Qed.

Corollary no_descending_chain_1 : ∀ A, A ∉ A.
Proof with auto.
  intros A H.
  set (Func ω A (λ n, A)) as f.
  assert (Hf: f: ω ⇒ A). {
    apply meta_function. intros n Hn...
  }
  apply no_descending_chain.
  exists f. split. apply Hf. split. apply Hf.
  intros n Hn. unfold f.
  repeat rewrite meta_func_ap... apply ω_inductive...
Qed.

Corollary no_descending_chain_2 : ∀ a b, a ∈ b → b ∉ a.
Proof with nauto.
  intros a b Ha Hb.
  set (Func ω {a, b} (λ n, match (ixm (even n)) with
    | inl _=> a
    | inr _=> b
  end)) as f.
  assert (Hf: f: ω ⇒ {a, b}). {
    apply meta_function. intros n Hn.
    destruct (ixm (even n)). apply PairI1. apply PairI2.
  }
  apply no_descending_chain.
  exists f. split. apply Hf. split. apply Hf.
  intros n Hn. unfold f.
  repeat rewrite meta_func_ap; [..|apply ω_inductive]...
  assert (Hnp: n⁺ ∈ ω). apply ω_inductive...
  destruct (ixm (even n⁺)); destruct (ixm (even n))...
  - exfalso. apply (no_even_and_odd n⁺)...
    split... apply even_iff_suc_odd...
  - exfalso. destruct (even_or_odd n⁺)...
    apply n1. apply even_iff_suc_odd...
Qed.

Corollary no_descending_chain_3 : ∀ a b c,
  a ∈ b → b ∈ c → c ∉ a.
Proof with auto; try congruence.
  intros a b c Ha Hb Hc.
  set ({a, b} ∪ {c,}) as A.
  assert (HaA: a ∈ A). apply BUnionI1; apply PairI1.
  assert (HbA: b ∈ A). apply BUnionI1; apply PairI2.
  assert (HcA: c ∈ A). apply BUnionI2...
  set (Func A A (λ x, match (ixm (x = a)) with
    | inl _ => c
    | inr _ => match (ixm (x = b)) with
      | inl _ => a
      | inr _ => b
  end end)) as F.
  assert (HF: F: A ⇒ A). {
    apply meta_function. intros x Hx.
    destruct (ixm (x = a))...
    destruct (ixm (x = b))...
  }
  pose proof (ω_recursion F A a) as [h [[Hh [Hd Hr]] [Hh0 Hhn]]]...
  apply no_descending_chain. exists h. split... split...
  intros n Hn. rewrite Hhn...
  rewrite <- Hd in Hn. apply func_correct in Hn...
  apply ranI in Hn. apply Hr in Hn.
  apply BUnionE in Hn as [];
  [apply PairE in H as []|apply SingE in H];
  rewrite H; unfold F; rewrite meta_func_ap...
  - destruct (ixm (a = a))...
  - destruct (ixm (b = a))...
    destruct (ixm (b = b))...
  - destruct (ixm (c = a))...
    destruct (ixm (c = b))...
Qed.

Corollary single_regularity : ∀ a, a ≠ {a,}.
Proof with eauto.
  intros a Heq. assert (a ∈ {a,})...
  rewrite <- Heq in H.
  eapply no_descending_chain_1...
Qed.

Corollary pair_regularity : ∀ a b, a ≠ {a, b}.
Proof with eauto.
  intros * Heq. assert (a ∈ {a, b}) by apply PairI1.
  rewrite <- Heq in H.
  eapply no_descending_chain_1...
Qed.

End RegularityConsequences.

Section MoreLemmaAboutRank.
Hint Resolve rank_is_ord : core.

Lemma V_grounded : ∀ α, α ⋵ 𝐎𝐍 → V α ⋵ 𝐖𝐅.
Proof. intros α H. exists α. split; auto. Qed.
Hint Resolve V_grounded : core.

Lemma rank_of_V : ∀α ⋵ 𝐎𝐍, rank (V α) = α.
Proof with eauto.
  intros α Hoα.
  apply sub_antisym.
  - apply ord_le_iff_sub... apply rank_spec_intro...
  - intros x Hx.
    rewrite rank_recurrence...
    rewrite <- (rank_of_ord α), rank_recurrence in Hx...
    apply FUnionE in Hx as [y [Hy Hx]].
    eapply FUnionI... rewrite <- (rank_of_ord α)...
    apply grounded_in_rank...
    apply ord_grounded... apply ord_grounded...
Qed.

Theorem V_iff_rank : ∀A ⋵ 𝐖𝐅, ∀α ⋵ 𝐎𝐍, A ∈ V α ↔ rank A ∈ α.
Proof with eauto.
  intros A Hg α Ho. split; intros.
  - apply rank_of_member in H... rewrite rank_of_V in H...
  - eapply V_intro... apply PowerAx... apply grounded_in_rank...
Qed.

(* 良基集的配对是良基集 *)
Lemma pair_grounded : ∀ a b ⋵ 𝐖𝐅, {a, b} ⋵ 𝐖𝐅.
Proof.
  intros a Hga b Hgb. apply grounded_intro.
  intros x Hx. apply PairE in Hx as []; subst; auto.
Qed.

(* 良基集的单集是良基集 *)
Lemma single_grounded : ∀a ⋵ 𝐖𝐅, {a,} ⋵ 𝐖𝐅.
Proof. intros a H. apply pair_grounded; auto. Qed.

(* 良基集的有序对是良基集 *)
Lemma op_grounded : ∀ a b ⋵ 𝐖𝐅, <a, b> ⋵ 𝐖𝐅.
Proof.
  intros a Hga b Hgb. apply grounded_intro.
  intros x Hx. apply PairE in Hx as []; subst;
  apply pair_grounded; auto.
Qed.

(* 良基集的笛卡尔积是良基集 *)
Lemma cprd_grounded : ∀ A B ⋵ 𝐖𝐅, A × B ⋵ 𝐖𝐅.
Proof.
  intros A HgA B HgB. apply grounded_intro.
  intros p Hp. apply CPrdE1 in Hp as [a [Ha [b [Hb Hp]]]];
  subst; apply op_grounded; eapply member_grounded; revgoals; eauto.
Qed.

(* 良基集的幂集是良基集 *)
Lemma power_grounded : ∀A ⋵ 𝐖𝐅, 𝒫 A ⋵ 𝐖𝐅.
Proof with eauto.
  intros A Hgnd. apply grounded_intro.
  intros a Ha. apply PowerAx in Ha.
  apply grounded_intro. intros x Hx.
  eapply member_grounded...
Qed.

(* 良基集的并集是良基集 *)
Lemma union_grounded : ∀A ⋵ 𝐖𝐅, ⋃ A ⋵ 𝐖𝐅.
Proof with eauto.
  intros A Hgnd. apply grounded_intro.
  intros x Hx. apply UnionAx in Hx as [y [Hy Hx]].
  eapply member_grounded; revgoals...
  eapply member_grounded...
Qed.

(* 配对的秩 *)
Lemma rank_of_pair_p : ∀ a b ⋵ 𝐖𝐅,
  rank a ⋸ rank b → rank {a, b} = (rank b)⁺.
Proof with eauto; try congruence.
  intros a Hga b Hgb Hle.
  rewrite rank_recurrence; [|apply pair_grounded]...
  ext Hx.
  - apply FUnionE in Hx as [y [Hy Hx]].
    apply BUnionE in Hx as [].
    + apply BUnionI1. apply PairE in Hy as []; subst...
      apply ord_le_iff_sub in Hle...
    + apply SingE in H. subst x.
      apply PairE in Hy as []; subst...
      apply ord_le_iff_lt_suc...
  - eapply FUnionI... apply PairI2.
Qed.

Lemma rank_of_pair : ∀ a b ⋵ 𝐖𝐅,
  rank {a, b} = (rank a ∪ rank b)⁺.
Proof with auto.
  intros a Hga b Hgb.
  destruct (ord_comparability (rank a) (rank_is_ord a Hga) (rank b))...
  - rewrite rank_of_pair_p... f_equal.
    symmetry. apply bunion_of_ords_eq_l...
  - rewrite (pair_ordering_agnostic a).
    rewrite rank_of_pair_p... f_equal.
    symmetry. apply bunion_of_ords_eq_r...
Qed.

(* 单集的秩 *)
Lemma rank_of_single : ∀a ⋵ 𝐖𝐅, rank {a,} = (rank a)⁺.
Proof. intros a H. apply rank_of_pair_p; auto. Qed.

(* 有序对的秩 *)
Lemma rank_of_op_l : ∀ a b ⋵ 𝐖𝐅,
  rank b ⋸ rank a → rank <a, b> = (rank a)⁺⁺.
Proof with auto.
  intros a Hga b Hgb Hle. unfold OPair.
  rewrite (pair_ordering_agnostic a).
  repeat rewrite rank_of_pair_p...
  apply single_grounded... apply pair_grounded...
  rewrite rank_of_single...
Qed.

Lemma rank_of_op_r : ∀ a b ⋵ 𝐖𝐅,
  rank a ⋸ rank b → rank <a, b> = (rank b)⁺⁺.
Proof with auto.
  intros a Hga b Hgb Hle. unfold OPair.
  repeat rewrite rank_of_pair_p...
  apply single_grounded... apply pair_grounded...
  rewrite rank_of_single...
  destruct Hle; [left|right; congruence].
  apply (ord_suc_preserve_lt (rank a))...
Qed.

Lemma rank_of_op : ∀ a b ⋵ 𝐖𝐅,
  rank <a, b> = (rank a ∪ rank b)⁺⁺.
Proof with auto.
  intros a Hga b Hgb.
  destruct (ord_comparability (rank a) (rank_is_ord a Hga) (rank b))...
  - rewrite rank_of_op_r... f_equal. f_equal.
    symmetry. apply bunion_of_ords_eq_l...
  - rewrite rank_of_op_l... f_equal. f_equal.
    symmetry. apply bunion_of_ords_eq_r...
Qed.

(* 秩的后继 *)
Lemma rank_suc : ∀a ⋵ 𝐖𝐅, (rank a)⁺ = rank 𝒫 (V (rank a)).
Proof with auto.
  intros a Hgnd. rewrite <- (rank_of_V (rank a)⁺)...
  f_equal. apply V_suc...
Qed.

(* 幂集的秩 *)
Lemma rank_of_power : ∀a ⋵ 𝐖𝐅, rank (𝒫 a) = (rank a)⁺.
Proof with eauto.
  intros a Hgnd.
  rewrite rank_recurrence; [|apply power_grounded]...
  ext Hx.
  - apply FUnionE in Hx as [y [Hy Hx]].
    rewrite rank_suc, rank_recurrence; [|apply power_grounded|]...
    eapply FUnionI... apply PowerAx.
    intros z Hz. apply grounded_in_rank...
    apply PowerAx in Hy. apply Hy...
  - eapply FUnionI... apply all_in_its_power.
Qed.

(* 并集的秩 *)
Lemma rank_of_union : ∀a ⋵ 𝐖𝐅, rank (⋃ a) ⋸ rank a.
Proof with eauto.
  intros a Hgnd. apply ord_le_iff_sub...
  apply rank_is_ord. apply union_grounded...
  rewrite rank_recurrence, rank_recurrence...
  intros x Hx. apply FUnionE in Hx as [y [Hy Hx]].
  apply UnionAx in Hy as [z [Hz Hy]].
  assert (Hgz: z ⋵ 𝐖𝐅). eapply member_grounded...
  assert (Hgy: y ⋵ 𝐖𝐅). eapply member_grounded...
  eapply FUnionI... eapply ord_trans...
  apply (ord_suc_preserve_lt (rank y))...
  apply rank_of_member... apply union_grounded...
Qed.

(* 如果良基集的所有成员等秩，那么该良基集的秩正好比成员的秩大1 *)
Lemma member_rank_up : ∀A ⋵ 𝐖𝐅,
  (∀ a b ∈ A, rank a = rank b) → ∀a ∈ A, rank A = (rank a)⁺.
Proof with eauto.
  intros A Hgnd Hsame a Ha.
  rewrite rank_recurrence...
  ext Hx.
  - apply FUnionE in Hx as [y [Hy Hx]]. erewrite Hsame...
  - eapply FUnionI...
Qed.

(* 如果良基集的所有成员等秩，那么该良基集与其任意非空子集等秩 *)
Lemma subset_same_rank : ∀A ⋵ 𝐖𝐅,
  (∀ a b ∈ A, rank a = rank b) →
  ∀B ∈ 𝒫 A, B ≠ ∅ → rank A = rank B.
Proof with eauto.
  intros A HgA Hsame B HB Hne.
  apply PowerAx in HB.
  apply EmptyNE in Hne as [b Hb].
  assert (HgB: B ⋵ 𝐖𝐅). {
    apply grounded_intro. intros x Hx.
    apply HB in Hx. eapply member_grounded...
  }
  ext Hx; rewrite rank_recurrence...
  - eapply FUnionI... replace (rank b)⁺ with (rank A)...
    apply member_rank_up...
  - eapply FUnionI... replace (rank b)⁺ with (rank B)...
    apply member_rank_up...
Qed.

End MoreLemmaAboutRank.
