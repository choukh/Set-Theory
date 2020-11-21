(** Based on "Elements of Set Theory" Chapter 7 Part 1 **)
(** Coq coding by choukh, Nov 2020 **)

Require Export ZFC.lib.Natural.

(*** EST第七章1：偏序结构，上下确界 ***)

(* 严格偏序，反自反偏序 *)
Definition partialOrder : set → Prop := λ R,
  is_rel R ∧ tranr R ∧ irrefl R.

(* 非对称性 *)
Definition asym : set → Prop := λ R,
  ∀ x y, <x, y> ∈ R → <y, x> ∉ R.

(* 反对称性 *)
Definition antisym : set → Prop := λ R,
  ∀ x y, <x, y> ∈ R → <y, x> ∈ R → x = y.

(* 偏序具有非对称性 *)
Fact partialOrder_asym : ∀ R, partialOrder R → asym R.
Proof.
  intros R [Hrl [Htr Hir]] x y Hxy Hyx.
  eapply Hir. eapply Htr; eauto.
Qed.

(* 偏序至多满足"<" "=" ">"之一 *)
Fact partialOrder_quasi_trich : ∀ R x y, partialOrder R →
  ¬(<x, y> ∈ R ∧ x = y) ∧
  ¬(<y, x> ∈ R ∧ x = y) ∧
  ¬(<x, y> ∈ R ∧ <y, x> ∈ R).
Proof with eauto.
  intros * [Hrl [Htr Hir]].
  repeat split; intros [H1 H2].
  - subst. eapply Hir...
  - subst. eapply Hir...
  - eapply Hir. eapply Htr...
Qed.

(* 偏序若满足"≤"且"≥"则满足"=" *)
Fact partialOrder_semi_antisym : ∀ R x y, partialOrder R →
  (<x, y> ∈ R ∨ x = y) ∧ (<y, x> ∈ R ∨ x = y) → x = y.
Proof with auto.
  intros * Hpo [H1 H2].
  destruct (classic (x = y))... exfalso.
  cut (¬(<x, y> ∈ R ∧ <y, x> ∈ R)). firstorder.
  apply partialOrder_quasi_trich...
Qed.

(* 严格全序，线序 *)
Print EST3_3.linearOrder.
(* Definition linearOrder : set → set → Prop := λ R A,
  is_binRel R A ∧ tranr R ∧ trich R A. *)

(* 线序是连通的偏序 *)
Fact linearOrder_is_connected_partialOrder : ∀ R A,
  linearOrder R A → connected R A ∧ partialOrder R.
Proof with eauto.
  intros * [Hrl [Htr Hir]]. repeat split...
  - eapply trich_iff...
  - intros x Hx. apply Hrl in Hx. apply CProdE2 in Hx...
  - eapply trich_iff...
Qed.

(* 结构 *)
Definition structure : set → set → Prop := λ A R,
  is_binRel R A.
Notation "⟨ A , R ⟩" := (structure A R).

(* 偏序结构 *)
(* partially ordered structure *)
Definition poset : set → set → Prop := λ A R,
  is_binRel R A ∧ partialOrder R.
Notation "⟨ A , R ⟩ₚₒ" := (poset A R).

(* 线序结构 *)
(* linear ordered structure *)
Definition loset : set → set → Prop := λ A R,
  linearOrder R A.
Notation "⟨ A , R ⟩ₗₒ" := (loset A R).

(* 线序结构等价于连通的偏序结构 *)
Fact loset_iff_connected_poset : ∀ A R,
  ⟨A, R⟩ₗₒ ↔ connected R A ∧ ⟨A, R⟩ₚₒ.
Proof with eauto.
  intros. split.
  - intros [Hrl [Htr Hir]]. repeat split...
    + eapply trich_iff...
    + intros x Hx. apply Hrl in Hx. apply CProdE2 in Hx...
    + eapply trich_iff...
  - intros [Hcon [Hbr [_ [Htr Htri]]]].
    split... split... apply trich_iff...
Qed.

(* 极小元 *)
Definition minimal : set → set → set → Prop := λ m A R,
  m ∈ A ∧ ¬∃x ∈ A, <x, m> ∈ R.

(* 最小元 *)
Print EST4_3.minimum.
(* Definition minimum : set → set → set → Prop := λ m A R,
  m ∈ A ∧ ∀x ∈ A, <m, x> ∈ R ∨ m = x. *)

(* 最小元也是极小元 *)
Fact minimum_is_minimal : ∀ m A R, partialOrder R →
  minimum m A R → minimal m A R.
Proof with auto.
  intros * Hpo [Hm H]. split... intros [x [Hx Hp]].
  apply partialOrder_asym in Hpo as Hasym.
  destruct Hpo as [_ [_ Hir]].
  apply H in Hx as []. firstorder. subst. firstorder.
Qed.

(* 线序上的极小元等价与最小元 *)
Fact linearOrder_minimal_iff_minimum : ∀ m A R, linearOrder R A →
  minimal m A R ↔ minimum m A R.
Proof with auto.
  intros * Hto. split; intros [Hm Hmin].
  - split... intros x Hx.
    destruct (classic (<m, x> ∈ R ∨ m = x))...
    exfalso. apply Hmin. apply not_or_and in H as [Hmx Hnq].
    exists x. split... apply linearOrder_connected in Hto. firstorder.
  - split... intros [x [Hx Hxm]].
    destruct Hto as [_ [_ Htri]]. firstorder.
Qed.

(* 最小元唯一 *)
Fact minimum_unique : ∀ m₁ m₂ A R, partialOrder R →
  minimum m₁ A R → minimum m₂ A R → m₁ = m₂.
Proof with auto.
  intros * Hpo [Hm1 H1] [Hm2 H2].
  apply H1 in Hm2 as []; apply H2 in Hm1 as []...
  apply partialOrder_asym in Hpo. firstorder.
Qed.

(* 极大元 *)
Definition maximal : set → set → set → Prop := λ m A R,
  m ∈ A ∧ ¬∃x ∈ A, <m, x> ∈ R.

(* 最大元 *)
Definition maximum : set → set → set → Prop := λ m A R,
  m ∈ A ∧ ∀x ∈ A, <x, m> ∈ R ∨ m = x.

(* 最大元也是极大元 *)
Fact maximum_is_maximal : ∀ m A R, partialOrder R →
  maximum m A R → maximal m A R.
Proof with auto.
  intros * Hpo [Hm H]. split... intros [x [Hx Hp]].
  apply partialOrder_asym in Hpo as Hasym.
  destruct Hpo as [_ [_ Hir]].
  apply H in Hx as []. firstorder. subst. firstorder.
Qed.

(* 线序上的极大元等价与最大元 *)
Fact linearOrder_maximal_iff_maximum : ∀ m A R, linearOrder R A →
  maximal m A R ↔ maximum m A R.
Proof with auto.
  intros * Hto. split; intros [Hm Hmin].
  - split... intros x Hx.
    destruct (classic (<x, m> ∈ R ∨ m = x))...
    exfalso. apply Hmin. apply not_or_and in H as [Hmx Hnq].
    exists x. split... apply linearOrder_connected in Hto. firstorder.
  - split... intros [x [Hx Hxm]].
    destruct Hto as [_ [_ Htri]]. firstorder.
Qed.

(* 最大元唯一 *)
Fact maximum_unique : ∀ m₁ m₂ A R, partialOrder R →
  maximum m₁ A R → maximum m₂ A R → m₁ = m₂.
Proof with auto.
  intros * Hpo [Hm1 H1] [Hm2 H2].
  apply H1 in Hm2 as []; apply H2 in Hm1 as []...
  apply partialOrder_asym in Hpo. firstorder.
Qed.

(* 偏序的逆仍是偏序 *)
Fact inv_partialOrder : ∀ R, partialOrder R → partialOrder R⁻¹.
Proof with auto.
  intros R [Hrl [Htr Hir]]. split; [|split].
  - apply inv_rel.
  - intros x y z Hxy Hyz. rewrite <- inv_op in *. firstorder.
  - intros x Hx. rewrite <- inv_op in Hx. firstorder.
Qed.

(* 极小元在逆关系下是极大元 *)
Fact minimal_iff_maximal_inv : ∀ m A R,
  minimal m A R ↔ maximal m A R⁻¹.
Proof with auto.
  intros; split; intros [Hm H]; split; auto;
  intros [x [Hx Hp]]; apply H; exists x; split...
  rewrite inv_op... rewrite <- inv_op...
Qed.

(* 极大元在逆关系下是极小元 *)
Fact maximal_iff_minimal_inv : ∀ m A R,
  maximal m A R ↔ minimal m A R⁻¹.
Proof with auto.
  intros; split; intros [Hm H]; split; auto;
  intros [x [Hx Hp]]; apply H; exists x; split...
  rewrite inv_op... rewrite <- inv_op...
Qed.

(* 最小元在逆关系下是最大元 *)
Fact minimum_iff_maximum_inv : ∀ m A R,
  minimum m A R ↔ maximum m A R⁻¹.
Proof with auto.
  intros; split; intros [Hm H]; split; auto;
  intros x Hx; apply H in Hx as []; auto; left.
  rewrite <- inv_op... rewrite inv_op...
Qed.

(* 最大元在逆关系下是最小元 *)
Fact maximum_iff_minimum_inv : ∀ m A R,
  maximum m A R ↔ minimum m A R⁻¹.
Proof with auto.
  intros; split; intros [Hm H]; split; auto;
  intros x Hx; apply H in Hx as []; auto; left.
  rewrite <- inv_op... rewrite inv_op...
Qed.

(* 上界 *)
Definition upperBound : set → set → set → set → Prop :=
  λ x B A R, ⟨A, R⟩ₚₒ ∧ B ⊆ A ∧ x ∈ A ∧ ∀y ∈ B, <y, x> ∈ R ∨ y = x.

(* 存在上界 *)
Definition boundedAbove : set → set → set → Prop :=
  λ B A R, ∃ x, upperBound x B A R.

(* 上确界 *)
Definition supremum : set → set → set → set → Prop :=
  λ x B A R, upperBound x B A R ∧
    ∀ y, upperBound y B A R → <x, y> ∈ R ∨ x = y.

(* 下界 *)
Definition lowerBound : set → set → set → set → Prop :=
  λ x B A R, ⟨A, R⟩ₚₒ ∧ B ⊆ A ∧ x ∈ A ∧ ∀y ∈ B, <x, y> ∈ R ∨ x = y.

(* 存在下界 *)
Definition boundedBelow : set → set → set → Prop :=
  λ B A R, ∃ x, lowerBound x B A R.

(* 下确界 *)
Definition infimum : set → set → set → set → Prop :=
  λ x B A R, lowerBound x B A R ∧
    ∀ y, lowerBound y B A R → <y, x> ∈ R ∨ y = x.

(* 真包含关系 *)
Definition SubRel : set → set := λ S,
  BinRel S (λ A B, A ⊂ B).

Lemma subRel_is_binRel : ∀ S, is_binRel (SubRel S) S.
Proof.
  intros S p Hp.
  apply binRel_iff in Hp as [a [Ha [b [Hb [Hp _]]]]].
  subst. apply CProdI; auto.
Qed.

Lemma subRel_tranr : ∀ S, tranr (SubRel S).
Proof with eauto.
  intros S a b c Hab Hbc.
  apply binRelE in Hab as [Ha [Hb [Hab Hnq]]].
  apply binRelE in Hbc as [_ [Hc [Hbc _]]].
  apply binRelI... split. eapply sub_tran...
  intros Heq. subst. apply Hnq. apply sub_antisym...
Qed.

Lemma subRel_irrefl : ∀ S, irrefl (SubRel S).
Proof.
  intros S x Hp. apply binRelE in Hp as [_ [_ [_ Heq]]]. auto.
Qed.

Lemma subRel_poset : ∀ S, ⟨S, SubRel S⟩ₚₒ.
Proof with auto.
  repeat split.
  - apply subRel_is_binRel.
  - eapply binRel_is_rel. apply subRel_is_binRel.
  - apply subRel_tranr.
  - apply subRel_irrefl.
Qed.

Example subRel_bunion_supremum : ∀ S, ∀ A B ∈ 𝒫 S,
  supremum (A ∪ B) {A, B} (𝒫 S) (SubRel (𝒫 S)).
Proof with auto.
  intros S A HAP B HBP.
  assert (Hu: A ∪ B ∈ 𝒫 S). {
    apply PowerAx in HAP. apply PowerAx in HBP.
    apply PowerAx. intros x Hx. apply BUnionE in Hx as [].
    apply HAP... apply HBP...
  }
  split.
  - split. apply subRel_poset.
    split. intros x Hx. apply PairE in Hx as []; subst...
    split... intros C HC.
    apply PairE in HC as []; subst.
    + destruct (classic (A = A ∪ B))... left.
      apply binRelI... split...
      intros x Hx. apply BUnionI1...
    + destruct (classic (B = A ∪ B))... left.
      apply binRelI... split...
      intros x Hx. apply BUnionI2...
  - intros C [_ [_ [HC Hle]]].
    destruct (classic (A ∪ B = C))... left.
    assert (HA: A ∈ {A, B}) by apply PairI1.
    assert (HB: B ∈ {A, B}) by apply PairI2.
    apply Hle in HA as [HA|HA]; apply Hle in HB as [HB|HB].
    + apply binRelE in HA as [_ [_ [HsubA HnqA]]].
      apply binRelE in HB as [_ [_ [HsubB HnqB]]].
      apply binRelI... split...
      intros x Hx. apply BUnionE in Hx as [].
      apply HsubA... apply HsubB...
    + apply binRelE in HA as [_ [_ [HsubA HnqA]]].
      apply binRelI... split...
      intros x Hx. apply BUnionE in Hx as [].
      apply HsubA... subst...
    + apply binRelE in HB as [_ [_ [HsubB HnqB]]].
      apply binRelI... split...
      intros x Hx. apply BUnionE in Hx as [].
      subst... apply HsubB...
    + apply binRelI... subst. split...
      intros x Hx. apply BUnionE in Hx as []; subst...
Qed.

Example subRel_binter_infimum : ∀ S, ∀ A B ∈ 𝒫 S,
  infimum (A ∩ B) {A, B} (𝒫 S) (SubRel (𝒫 S)).
Proof with auto.
  intros S A HAP B HBP.
  assert (HiP: A ∩ B ∈ 𝒫 S). {
    apply PowerAx in HAP. apply PowerAx.
    intros x Hx. apply BInterE in Hx as [Hx _]. apply HAP...
  }
  split.
  - split. apply subRel_poset.
    split. intros x Hx. apply PairE in Hx as []; subst...
    split... intros C HC.
    apply PairE in HC as []; subst.
    + destruct (classic (A ∩ B = A))... left.
      apply binRelI... split...
      intros x Hx. apply BInterE in Hx as []...
    + destruct (classic (A ∩ B = B))... left.
      apply binRelI... split...
      intros x Hx. apply BInterE in Hx as []...
  - intros C [_ [_ [HC Hle]]].
    destruct (classic (C = A ∩ B))... left.
    assert (HA: A ∈ {A, B}) by apply PairI1.
    assert (HB: B ∈ {A, B}) by apply PairI2.
    apply Hle in HA as [HA|HA]; apply Hle in HB as [HB|HB].
    + apply binRelE in HA as [_ [_ [HsubA HnqA]]].
      apply binRelE in HB as [_ [_ [HsubB HnqB]]].
      apply binRelI... split...
      intros x Hx. apply BInterI. apply HsubA... apply HsubB...
    + apply binRelE in HA as [_ [_ [HsubA HnqA]]].
      apply binRelI... split...
      intros x Hx. apply BInterI. apply HsubA... subst...
    + apply binRelE in HB as [_ [_ [HsubB HnqB]]].
      apply binRelI... split...
      intros x Hx. apply BInterI. subst... apply HsubB...
    + apply binRelI... subst... split...
      intros x Hx. apply BInterI; subst...
Qed.

Example subRel_union_supremum : ∀ S 𝒜, 𝒜 ⊆ 𝒫 S →
  supremum (⋃ 𝒜) 𝒜 (𝒫 S) (SubRel (𝒫 S)).
Proof with auto; try congruence.
  intros S 𝒜 Hsub.
  assert (Hu: ⋃ 𝒜 ∈ 𝒫 S). {
    apply PowerAx. intros x Hx.
    apply UnionAx in Hx as [A [HA Hx]].
    apply Hsub in HA. apply PowerAx in HA. apply HA...
  }
  split.
  - split. apply subRel_poset.
    split. intros x Hx. apply Hsub...
    split... intros C HC.
    destruct (classic (C = ⋃ 𝒜))... left.
    apply binRelI... apply Hsub... split...
    intros x Hx. apply UnionAx. exists C. split...
  - intros C [_ [_ [HC Hle]]].
    assert (Hsubu: ⋃ 𝒜 ⊆ C). {
      intros x Hx.
      apply UnionAx in Hx as [A [HA Hx]].
      apply Hle in HA as [HA|]...
      apply binRelE in HA as [_ [_ [HsubA _]]].
      apply HsubA...
    }
    destruct (classic (C ⊆ ⋃ 𝒜)).
    + right. apply sub_antisym...
    + left. apply binRelI... split...
Qed.

Example subRel_inter_infimum : ∀ S 𝒜, ⦿ 𝒜 → 𝒜 ⊆ 𝒫 S →
  infimum (⋂ 𝒜) 𝒜 (𝒫 S) (SubRel (𝒫 S)).
Proof with auto; try congruence.
  intros S 𝒜 Hne Hsub.
  assert (Hi: ⋂ 𝒜 ∈ 𝒫 S). {
    apply PowerAx. intros x Hx.
    apply InterE in Hx as [[A HA] H].
    apply H in HA as Hx. apply Hsub in HA.
    apply PowerAx in HA. apply HA...
  }
  split.
  - split. apply subRel_poset.
    split. intros x Hx. apply Hsub...
    split... intros C HC.
    destruct (classic (⋂ 𝒜 = C))... left.
    apply binRelI... apply Hsub... split...
    intros x Hx. apply InterE in Hx as [_ Hx]. apply Hx...
  - intros C [_ [_ [HC Hle]]].
    assert (HsubC: C ⊆ ⋂ 𝒜). {
      intros x Hx. apply InterI...
      intros y Hy. apply Hle in Hy as []; subst...
      apply binRelE in H as [_ [_ [HsubC _]]]... apply HsubC...
    }
    destruct (classic (⋂ 𝒜 ⊆ C)).
    + right. apply sub_antisym...
    + left. apply binRelI... split...
Qed.
