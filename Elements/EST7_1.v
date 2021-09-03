(** Adapted from "Elements of Set Theory" Chapter 7 **)
(** Coq coding by choukh, Nov 2020 **)

Require Export ZFC.Elements.EST3_3.

(*** EST第七章1：偏序，线序，极值，最值，确界 ***)

Definition relLt := λ x y R, <x, y> ∈ R.
Notation "x <ᵣ y" := (relLt x y) (at level 60).
Definition relLe := λ x y R, <x, y> ∈ R ∨ x = y.
Notation "x ≤ᵣ y" := (relLe x y) (at level 60).

Lemma relLt_irrefl : ∀ x R, irrefl R → (x <ᵣ x) R → False.
Proof. intros. eapply H. apply H0. Qed.

Lemma relLt_trans : ∀ x y z R, tranr R →
  (x <ᵣ y) R → (y <ᵣ z) R → (x <ᵣ z) R.
Proof. intros; eapply H; eauto. Qed.

Lemma relLe_trans : ∀ x y z R, tranr R →
  (x ≤ᵣ y) R → (y ≤ᵣ z) R → (x ≤ᵣ z) R.
Proof with eauto.
  intros * Htr [Hxy|Hxy] [Hyz|Hyz].
  - left. eapply Htr...
  - subst. left...
  - subst. left...
  - subst. right...
Qed.

Lemma relLt_le_trans : ∀ x y z R, tranr R →
  (x <ᵣ y) R → (y ≤ᵣ z) R → (x <ᵣ z) R.
Proof with eauto.
  intros * Htr Hxy [Hyz|Hyz]. eapply Htr... subst...
Qed.

Lemma relLe_lt_trans : ∀ x y z R, tranr R →
  (x ≤ᵣ y) R → (y <ᵣ z) R → (x <ᵣ z) R.
Proof with eauto.
  intros * Htr [Hxy|Hyx] Hyz. eapply Htr... subst...
Qed.

Lemma inv_relLt : ∀ x y R, (x <ᵣ y) R⁻¹ ↔ (y <ᵣ x) R.
Proof with auto.
  unfold relLt. split; intros.
  rewrite inv_op... rewrite <- inv_op...
Qed.

Lemma inv_relLe : ∀ x y R, (x ≤ᵣ y) R⁻¹ ↔ (y ≤ᵣ x) R.
Proof with auto.
  split; (intros []; [left|right])...
  rewrite inv_op... rewrite <- inv_op...
Qed.

(* 严格偏序，反自反偏序 *)
Definition partialOrder := λ R, is_rel R ∧ tranr R ∧ irrefl R.

(* 非对称性 *)
Definition asym := λ R, ∀ x y, (x <ᵣ y) R → ¬(y <ᵣ x) R.
(* 反对称性 *)
Definition antisym := λ R, ∀ x y, (x <ᵣ y) R → (y <ᵣ x) R → x = y.

Fact asym_iff_antisym_and_irrefl :
  ∀ R, asym R ↔ antisym R ∧ irrefl R.
Proof with auto.
  intro R. split.
  - intros Hasym. split.
    + intros x y Hxy Hyx. apply Hasym in Hyx. exfalso...
    + intros x Hx. apply Hasym in Hx as Hx'...
  - intros [Hanti Hir] x y Hxy Hyx.
    assert (x = y). apply Hanti...
    rewrite H in Hxy. apply (Hir y)...
Qed.

(* 偏序具有非对称性 *)
Fact po_asym : ∀ R, partialOrder R → asym R.
Proof.
  intros R [Hrl [Htr Hir]] x y Hxy Hyx.
  eapply Hir. eapply Htr; eauto.
Qed.

Definition at_most_trich := λ P Q R,
  ¬(P ∧ Q) ∧ ¬(R ∧ Q) ∧ ¬(P ∧ R).

(* 偏序至多满足"<" "=" ">"之一 *)
Fact po_at_most_trich : ∀ R x y, partialOrder R →
  at_most_trich ((x <ᵣ y) R) (x = y) ((y <ᵣ x) R).
Proof with eauto.
  intros * [Hrl [Htr Hir]].
  repeat split; intros [H1 H2].
  - subst. eapply Hir...
  - subst. eapply Hir...
  - eapply Hir. eapply Htr...
Qed.

(* 偏序若满足"⋸"且"≥"则满足"=" *)
Fact po_semi_antisym : ∀ R x y, partialOrder R →
  (x ≤ᵣ y) R ∧ (y ≤ᵣ x) R → x = y.
Proof with auto.
  intros * Hpo [H1 H2].
  contra.
  cut (¬((x <ᵣ y) R ∧ (y <ᵣ x) R)). firstorder.
  apply po_at_most_trich...
Qed.

(* 偏序结构 *)
Definition poset := λ A R, is_binRel R A ∧ partialOrder R.
(* 线序结构 *)
Definition loset := λ A R, linearOrder R A.

Lemma lo_not_le_gt : ∀ A R, loset A R →
  ∀ x y, (x ≤ᵣ y) R → (y <ᵣ x) R → False.
Proof.
  intros A R Hlo x y Hle Hgt.
  apply lo_irrefl in Hlo as Hir.
  destruct Hlo as [_ [Htr _]].
  destruct Hle; subst; eapply Hir; eapply Htr; eauto.
Qed.

(* 线序等价于连通的偏序 *)
Fact loset_iff_connected_poset : ∀ A R,
  loset A R ↔ connected R A ∧ poset A R.
Proof with eauto.
  intros. split.
  - intros [Hrl [Htr Hir]]. repeat split...
    + apply trich_iff...
    + intros x Hx. apply Hrl in Hx. apply cprd_is_pairs in Hx...
    + eapply trich_iff...
  - intros [Hcon [Hbr [_ [Htr Hir]]]]. repeat split...
    apply trich_iff...
Qed.

(* 极小元 *)
Definition minimal := λ m A R, m ∈ A ∧ ∀x ∈ A, ¬(x <ᵣ m) R ∨ x = m.
(* 最小元 *)
Definition minimum := λ m A R, m ∈ A ∧ ∀x ∈ A, (m ≤ᵣ x) R.

(* 最小元也是极小元 *)
Fact minimum_is_minimal : ∀ m A R, partialOrder R →
  minimum m A R → minimal m A R.
Proof with auto.
  intros * Hpo [Hm H]. split... intros x Hx.
  apply po_asym in Hpo as Hasym.
  destruct Hpo as [_ [_ Hir]].
  apply H in Hx as []. firstorder. subst. firstorder.
Qed.

(* 线序上的极小元等价与最小元 *)
Fact linearOrder_minimal_iff_minimum : ∀ m A R, linearOrder R A →
  minimal m A R ↔ minimum m A R.
Proof with eauto.
  intros * Hto. split; intros [Hm Hmin].
  - split... intros x Hx.
    destruct (classic (m = x)). right... left.
    eapply lo_connected in H as []...
    apply Hmin in Hx as []. exfalso... subst...
  - split... intros x Hx. assert (H := Hx).
    apply Hmin in H as []...
    destruct Hto as [_ [_ Htri]]. firstorder.
Qed.

(* 最小元唯一 *)
Fact minimum_unique : ∀ m₁ m₂ A R, partialOrder R →
  minimum m₁ A R → minimum m₂ A R → m₁ = m₂.
Proof with auto.
  intros * Hpo [Hm1 H1] [Hm2 H2].
  apply H1 in Hm2 as []; apply H2 in Hm1 as []...
  apply po_asym in Hpo. firstorder.
Qed.

(* 极大元 *)
Definition maximal := λ m A R, m ∈ A ∧ ∀x ∈ A, ¬(m <ᵣ x) R ∨ x = m.
(* 最大元 *)
Definition maximum := λ m A R, m ∈ A ∧ ∀x ∈ A, (x ≤ᵣ m) R.

(* 最大元也是极大元 *)
Fact maximum_is_maximal : ∀ m A R, partialOrder R →
  maximum m A R → maximal m A R.
Proof with auto.
  intros * Hpo [Hm H]. split... intros x Hx.
  apply po_asym in Hpo as Hasym.
  destruct Hpo as [_ [_ Hir]].
  apply H in Hx as []. firstorder. subst. firstorder.
Qed.

(* 线序上的极大元等价与最大元 *)
Fact linearOrder_maximal_iff_maximum : ∀ m A R, linearOrder R A →
  maximal m A R ↔ maximum m A R.
Proof with eauto.
  intros * Hto. split; intros [Hm Hmax].
  - split... intros x Hx.
    destruct (classic (m = x)). right... left.
    eapply lo_connected in H as []...
    apply Hmax in Hx as []. exfalso... subst...
  - split... intros x Hx. assert (H := Hx).
    apply Hmax in H as []...
    destruct Hto as [_ [_ Htri]]. firstorder.
Qed.

(* 最大元唯一 *)
Fact maximum_unique : ∀ m₁ m₂ A R, partialOrder R →
  maximum m₁ A R → maximum m₂ A R → m₁ = m₂.
Proof with auto.
  intros * Hpo [Hm1 H1] [Hm2 H2].
  apply H1 in Hm2 as []; apply H2 in Hm1 as []...
  apply po_asym in Hpo. firstorder.
Qed.

(* 二元关系的逆仍是二元关系 *)
Lemma inv_binRel : ∀ A R, is_binRel R A → is_binRel R⁻¹ A.
Proof.
  intros * Hbr p Hp.
  apply SepE in Hp as [H [_ Hp]].
  apply CPrdE1 in H as [a [_ [b [_ Heq]]]].
  subst p. zfc_simple. apply Hbr in Hp.
  apply CPrdE2 in Hp as [Ha Hb]. apply CPrdI; auto.
Qed.

(* 传递关系的逆仍是传递关系 *)
Lemma inv_trans : ∀ R, tranr R → tranr R⁻¹.
Proof.
  intros R Htr x y z Hxy Hyz. rewrite <- inv_op in *. firstorder.
Qed.

(* 反自反关系的逆仍是反自反关系 *)
Lemma inv_irrefl : ∀ R, irrefl R → irrefl R⁻¹.
Proof.
  intros R Htr x Hx. rewrite <- inv_op in Hx. firstorder.
Qed.

(* 连通关系的逆仍是连通关系 *)
Lemma inv_connected : ∀ R A, connected R A → connected R⁻¹ A.
Proof.
  intros R A Hcon x Hx y Hy Hnq.
  apply Hcon in Hnq as []; auto; [right|left];
  rewrite <- inv_op; auto.
Qed.

(* 偏序的逆仍是偏序 *)
Fact inv_po : ∀ R, partialOrder R → partialOrder R⁻¹.
Proof with auto.
  intros R [Hrl [Htr Hir]]. split; [|split].
  apply inv_rel. apply inv_trans... apply inv_irrefl...
Qed.

(* 线序的逆仍是线序 *)
Fact inv_lo : ∀ A R, loset A R → loset A R⁻¹.
Proof with auto.
  intros A R Hlo.
  apply loset_iff_connected_poset. split.
  apply inv_connected. apply lo_connected...
  split. apply inv_binRel. apply Hlo.
  apply inv_po. apply (loset_iff_connected_poset A)...
Qed.

(* 极小元在逆关系下是极大元 *)
Fact minimal_iff_maximal_inv : ∀ m A R,
  minimal m A R ↔ maximal m A R⁻¹.
Proof with auto.
  intros; split; intros [Hm H]; split; auto; 
  intros x Hx; apply H in Hx as []; auto; left.
  rewrite inv_relLt... rewrite inv_relLt in H0...
Qed.

(* 极大元在逆关系下是极小元 *)
Fact maximal_iff_minimal_inv : ∀ m A R,
  maximal m A R ↔ minimal m A R⁻¹.
  Proof with auto.
  intros; split; intros [Hm H]; split; auto; 
  intros x Hx; apply H in Hx as []; auto; left.
  rewrite inv_relLt... rewrite inv_relLt in H0...
Qed.

(* 最小元在逆关系下是最大元 *)
Fact minimum_iff_maximum_inv : ∀ m A R,
  minimum m A R ↔ maximum m A R⁻¹.
Proof with auto.
  intros; split; intros [Hm H]; split; auto;
  intros x Hx; apply H in Hx as []; unfold relLe; auto; left...
  rewrite <- inv_op... rewrite inv_op...
Qed.

(* 最大元在逆关系下是最小元 *)
Fact maximum_iff_minimum_inv : ∀ m A R,
  maximum m A R ↔ minimum m A R⁻¹.
Proof with auto.
  intros; split; intros [Hm H]; split; auto;
  intros x Hx; apply H in Hx as []; unfold relLe; auto; left...
  rewrite <- inv_op... rewrite inv_op...
Qed.

(* 上界 *)
Definition upperBound := λ x B A R, x ∈ A ∧ ∀y ∈ B, (y ≤ᵣ x) R.
(* 严格上界 *)
Definition strictUpperBound := λ x B A R, x ∈ A ∧ ∀y ∈ B, (y <ᵣ x) R.
(* 存在上界 *)
Definition boundedAbove := λ B A R, ∃ x, upperBound x B A R.
(* 上确界 *)
Definition supremum := λ x B A R, upperBound x B A R ∧
  ∀ y, upperBound y B A R → (x ≤ᵣ y) R.

(* 下界 *)
Definition lowerBound := λ x B A R, x ∈ A ∧ ∀y ∈ B, (x ≤ᵣ y) R.
(* 严格下界 *)
Definition strictLowerBound := λ x B A R, x ∈ A ∧ ∀y ∈ B, (x <ᵣ y) R.
(* 存在下界 *)
Definition boundedBelow := λ B A R, ∃ x, lowerBound x B A R.
(* 下确界 *)
Definition infimum := λ x B A R, lowerBound x B A R ∧
  ∀ y, lowerBound y B A R → (y ≤ᵣ x) R.

(* 成员关系 *)
Definition MemberRel := λ A, BinRel A (λ x y, x ∈ y).

Lemma memberRel_is_binRel : ∀ A, is_binRel (MemberRel A) A.
Proof.
  intros S p Hp.
  apply binRelE1 in Hp as [a [Ha [b [Hb [Hp _]]]]].
  subst. apply CPrdI; auto.
Qed.

Notation "a ⋸ b" := (a ∈ b ∨ a = b) (at level 70) : set_scope.

Definition ε_minimal := λ a A, a ∈ A ∧ ∀b ∈ A, b ∉ a ∨ a = b.
Definition ε_maximal := λ a A, a ∈ A ∧ ∀b ∈ A, a ∉ b ∨ a = b.
Definition ε_minimum := λ a A, a ∈ A ∧ ∀b ∈ A, a ⋸ b.
Definition ε_maximum := λ a A, a ∈ A ∧ ∀b ∈ A, b ⋸ a.

Lemma ε_minimal_iff : ∀ a A B, B ⊆ A →
  minimal a B (MemberRel A) ↔ ε_minimal a B.
Proof with auto.
  intros * Hsub. split.
  - intros [Ha Hmin]. split... intros b Hb.
    assert (H := Hb). apply Hmin in H as []...
    left. intros H'. apply H. apply binRelI; [apply Hsub..|]...
  - intros [Ha Hmin]. split... intros b Hb.
    assert (H := Hb). apply Hmin in H as []...
    left. intros H'. apply H. apply binRelE3 in H'...
Qed.

Lemma ε_maximal_iff : ∀ a A B, B ⊆ A →
  maximal a B (MemberRel A) ↔ ε_maximal a B.
Proof with auto.
  intros * Hsub. split.
  - intros [Ha Hmax]. split... intros b Hb.
    assert (H := Hb). apply Hmax in H as []...
    left. intros H'. apply H. apply binRelI; [apply Hsub..|]...
  - intros [Ha Hmax]. split... intros b Hb.
    assert (H := Hb). apply Hmax in H as []...
    left. intros H'. apply H. apply binRelE3 in H'...
Qed.

Lemma ε_minimum_iff : ∀ a A B, B ⊆ A →
  minimum a B (MemberRel A) ↔ ε_minimum a B.
Proof with auto.
  intros * Hsub. split.
  - intros [Ha Hle]. split... intros b Hb.
    assert (H := Hb). apply Hle in H as []...
    left. apply binRelE3 in H...
  - intros [Ha Hle]. split... intros b Hb.
    assert (H := Hb). apply Hle in H as []...
    left. apply binRelI; [apply Hsub..|]... right...
Qed.

Lemma ε_maximum_iff : ∀ a A B, B ⊆ A →
  maximum a B (MemberRel A) ↔ ε_maximum a B.
Proof with auto.
  intros * Hsub. split.
  - intros [Ha Hle]. split... intros b Hb.
    assert (H := Hb). apply Hle in H as []...
    left. apply binRelE3 in H...
  - intros [Ha Hle]. split... intros b Hb.
    assert (H := Hb). apply Hle in H as []...
    left. apply binRelI; [apply Hsub..|]... right...
Qed.

(* 真子集关系 *)
Definition SubsetRel := λ S, BinRel S (λ A B, A ⊂ B).

Lemma subsetRel_is_binRel : ∀ S, is_binRel (SubsetRel S) S.
Proof.
  intros S p Hp.
  apply binRelE1 in Hp as [a [Ha [b [Hb [Hp _]]]]].
  subst. apply CPrdI; auto.
Qed.

Lemma subsetRel_trans : ∀ S, tranr (SubsetRel S).
Proof with eauto.
  intros S a b c Hab Hbc.
  apply binRelE2 in Hab as [Ha [Hb [Hab Hnq]]].
  apply binRelE2 in Hbc as [_ [Hc [Hbc _]]].
  apply binRelI... split. eapply sub_trans...
  intros Heq. subst. apply Hnq. apply sub_antisym...
Qed.

Lemma subsetRel_irrefl : ∀ S, irrefl (SubsetRel S).
Proof.
  intros S x Hp. apply binRelE3 in Hp as [_ Heq]. auto.
Qed.

Lemma subsetRel_poset : ∀ S, poset S (SubsetRel S).
Proof with auto.
  repeat split.
  - apply subsetRel_is_binRel.
  - eapply binRel_is_rel. apply subsetRel_is_binRel.
  - apply subsetRel_trans.
  - apply subsetRel_irrefl.
Qed.

Example subsetRel_bunion_supremum : ∀ S, ∀ A B ∈ 𝒫 S,
  supremum (A ∪ B) {A, B} (𝒫 S) (SubsetRel (𝒫 S)).
Proof with auto.
  intros S A HAP B HBP.
  assert (Hu: A ∪ B ∈ 𝒫 S). {
    apply PowerAx in HAP. apply PowerAx in HBP.
    apply PowerAx. intros x Hx. apply BUnionE in Hx as [].
    apply HAP... apply HBP...
  }
  split.
  - split... intros C HC.
    apply PairE in HC as []; subst.
    + destruct (classic (A = A ∪ B)). right... left.
      apply binRelI... split...
      intros x Hx. apply BUnionI1...
    + destruct (classic (B = A ∪ B)). right... left.
      apply binRelI... split...
      intros x Hx. apply BUnionI2...
  - intros C [HC Hle].
    destruct (classic (A ∪ B = C)). right... left.
    assert (HA: A ∈ {A, B}) by apply PairI1.
    assert (HB: B ∈ {A, B}) by apply PairI2.
    apply Hle in HA as [HA|HA]; apply Hle in HB as [HB|HB].
    + apply binRelE3 in HA as [HsubA HnqA].
      apply binRelE3 in HB as [HsubB HnqB].
      apply binRelI... split...
      intros x Hx. apply BUnionE in Hx as [].
      apply HsubA... apply HsubB...
    + apply binRelE3 in HA as [HsubA HnqA].
      apply binRelI... split...
      intros x Hx. apply BUnionE in Hx as [].
      apply HsubA... subst...
    + apply binRelE3 in HB as [HsubB HnqB].
      apply binRelI... split...
      intros x Hx. apply BUnionE in Hx as [].
      subst... apply HsubB...
    + apply binRelI... subst. split...
      intros x Hx. apply BUnionE in Hx as []; subst...
Qed.

Example subsetRel_binter_infimum : ∀ S, ∀ A B ∈ 𝒫 S,
  infimum (A ∩ B) {A, B} (𝒫 S) (SubsetRel (𝒫 S)).
Proof with auto.
  intros S A HAP B HBP.
  assert (HiP: A ∩ B ∈ 𝒫 S). {
    apply PowerAx in HAP. apply PowerAx.
    intros x Hx. apply BInterE in Hx as [Hx _]. apply HAP...
  }
  split.
  - split... intros C HC.
    apply PairE in HC as []; subst.
    + destruct (classic (A ∩ B = A)). right... left.
      apply binRelI... split...
      intros x Hx. apply BInterE in Hx as []...
    + destruct (classic (A ∩ B = B)). right... left.
      apply binRelI... split...
      intros x Hx. apply BInterE in Hx as []...
  - intros C [HC Hle].
    destruct (classic (C = A ∩ B)). right... left.
    assert (HA: A ∈ {A, B}) by apply PairI1.
    assert (HB: B ∈ {A, B}) by apply PairI2.
    apply Hle in HA as [HA|HA]; apply Hle in HB as [HB|HB].
    + apply binRelE3 in HA as [HsubA HnqA].
      apply binRelE3 in HB as [HsubB HnqB].
      apply binRelI... split...
      intros x Hx. apply BInterI. apply HsubA... apply HsubB...
    + apply binRelE3 in HA as [HsubA HnqA].
      apply binRelI... split...
      intros x Hx. apply BInterI. apply HsubA... subst...
    + apply binRelE3 in HB as [HsubB HnqB].
      apply binRelI... split...
      intros x Hx. apply BInterI. subst... apply HsubB...
    + apply binRelI... subst... split...
      intros x Hx. apply BInterI; subst...
Qed.

(* 并集是包含关系的上界 *)
Lemma union_is_ub : ∀A, ∀a ∈ A, a ⊆ ⋃A.
Proof. exact ex2_3. Qed.

(* 并集是包含关系的上确界 *)
Lemma union_is_sup: ∀ A B, (∀a ∈ A, a ⊆ B) → ⋃A ⊆ B.
Proof. exact ex2_5. Qed.

Example subsetRel_union_supremum : ∀ S 𝒜, 𝒜 ⊆ 𝒫 S →
  supremum (⋃ 𝒜) 𝒜 (𝒫 S) (SubsetRel (𝒫 S)).
Proof with auto; try congruence.
  intros S 𝒜 Hsub.
  assert (Hu: ⋃ 𝒜 ∈ 𝒫 S). {
    apply PowerAx. apply union_is_sup.
    intros x Hx. apply Hsub in Hx. apply PowerAx...
  }
  split.
  - split... intros C HC.
    destruct (classic (C = ⋃ 𝒜)). right... left.
    apply binRelI... split... apply union_is_ub...
  - intros C [HC Hle].
    destruct (classic (⋃ 𝒜 = C)) as [|Hnq]. right... left.
    apply binRelI... split... apply union_is_sup.
    intros x Hx. apply Hle in Hx as []...
    apply binRelE3 in H as []...
Qed.

(* 交集是包含关系的下界 *)
Lemma inter_is_lb : ∀A, ∀a ∈ A, ⋂A ⊆ a.
Proof.
  intros A a Ha x Hx.
  apply InterE in Hx as [_ H]. apply H. apply Ha.
Qed.

(* 交集是包含关系的下确界 *)
Lemma inter_is_inf: ∀ A B, ⦿ A → (∀a ∈ A, B ⊆ a) → B ⊆ ⋂A.
Proof with auto.
  intros A B Hne Hlb x Hx. apply InterI... 
  intros y Hy. apply Hlb in Hy. apply Hy...
Qed.

Example subsetRel_inter_infimum : ∀ S 𝒜, ⦿ 𝒜 → 𝒜 ⊆ 𝒫 S →
  infimum (⋂ 𝒜) 𝒜 (𝒫 S) (SubsetRel (𝒫 S)).
Proof with auto; try congruence.
  intros S 𝒜 Hne Hsub.
  assert (Hi: ⋂ 𝒜 ∈ 𝒫 S). {
    apply PowerAx. intros x Hx.
    apply InterE in Hx as [[A HA] H].
    apply H in HA as Hx. apply Hsub in HA.
    apply PowerAx in HA. apply HA...
  }
  split.
  - split... intros C HC.
    destruct (classic (⋂ 𝒜 = C)). right... left.
    apply binRelI... split... apply inter_is_lb...
  - intros C [HC Hle].
    destruct (classic (C = ⋂ 𝒜)) as [|Hnq]. right... left.
    apply binRelI... split... apply inter_is_inf...
    intros x Hx. apply Hle in Hx as []...
    apply binRelE3 in H as []...
Qed.

Definition sub_minimal := λ a A, a ∈ A ∧ ∀b ∈ A, b ⊈ a ∨ a = b.
Definition sub_maximal := λ a A, a ∈ A ∧ ∀b ∈ A, a ⊈ b ∨ a = b.
Definition sub_minimum := λ a A, a ∈ A ∧ ∀b ∈ A, a ⊆ b.
Definition sub_maximum := λ a A, a ∈ A ∧ ∀b ∈ A, b ⊆ a.

Lemma sub_minimal_iff : ∀ a A B, B ⊆ A →
  minimal a B (SubsetRel A) ↔ sub_minimal a B.
Proof with auto.
  intros * Hsub. split.
  - intros [Ha Hmin]. split... intros b Hb.
    destruct (classic (a = b)) as [|Hnq]. right...
    assert (H := Hb). apply Hmin in H as []...
    left. intros H'. apply H. apply binRelI; [apply Hsub..|]...
  - intros [Ha Hmin]. split... intros b Hb.
    assert (H := Hb). apply Hmin in H as []...
    left. intros H'. apply H. apply binRelE3 in H' as []...
Qed.

Lemma sub_maximal_iff : ∀ a A B, B ⊆ A →
  maximal a B (SubsetRel A) ↔ sub_maximal a B.
Proof with auto.
  intros * Hsub. split.
  - intros [Ha Hmax]. split... intros b Hb.
    destruct (classic (a = b)) as [|Hnq]. right...
    assert (H := Hb). apply Hmax in H as []...
    left. intros H'. apply H. apply binRelI; [apply Hsub..|]...
  - intros [Ha Hmax]. split... intros b Hb.
    assert (H := Hb). apply Hmax in H as []...
    left. intros H'. apply H. apply binRelE3 in H' as []...
Qed.

Lemma sub_minimum_iff : ∀ a A B, B ⊆ A →
  minimum a B (SubsetRel A) ↔ sub_minimum a B.
Proof with auto.
  intros * Hsub. split.
  - intros [Ha Hle]. split...
    intros b Hb. apply Hle in Hb as []...
    apply binRelE3 in H as []... subst...
  - intros [Ha Hle]. split...
    intros b Hb. apply Hle in Hb as Han.
    destruct (classic (a = b)). right...
    left. apply binRelI...
Qed.

Lemma sub_maximum_iff : ∀ a A B, B ⊆ A →
  maximum a B (SubsetRel A) ↔ sub_maximum a B.
Proof with auto.
  intros * Hsub. split.
  - intros [Ha Hle]. split...
    intros b Hb. apply Hle in Hb as []...
    apply binRelE3 in H as []... subst...
  - intros [Ha Hle]. split...
    intros b Hb. apply Hle in Hb as Han.
    destruct (classic (a = b)). right...
    left. apply binRelI...
Qed.

(* 偏序集的阿基米德性 *)
Definition po_archimedean := λ A R, ∀x ∈ A, ∃y ∈ A, (x <ᵣ y) R.

(* 偏序集合具有阿基米德性当且仅当它没有极大元 *)
Lemma po_archimedean_iff_no_maximal : ∀ A R, poset A R →
  po_archimedean A R ↔ ¬ ∃ m, maximal m A R.
Proof with eauto; try congruence.
  intros A R [_ [_ [_ Hir]]]. split.
  - intros Harc [m [Hm Hmax]].
    apply Harc in Hm as [y [Hy Hmy]].
    apply Hmax in Hy as []... subst. eapply Hir...
  - intros Hnex x Hx.
    pose proof (not_ex_all_not set (λ x, maximal x A R) Hnex).
    specialize H with x.
    apply not_and_or in H as []...
    apply set_not_all_ex_not in H as [y [Hy H]].
    apply not_or_and in H as [H _].
    exists y. split... apply NNPP in H...
Qed.

(* 子关系 *)
Definition SubRel := λ R B, {p ∊ R | p ∈ B × B}.
Notation "R ⥏ B" := (SubRel R B) (at level 60).

Lemma subRel_is_binRel : ∀ R B, is_binRel (R ⥏ B) B.
Proof with auto.
  intros * p Hp. apply SepE2 in Hp...
Qed.

Lemma subRel_absorption : ∀ R A B, B ⊆ A → (R ⥏ A) ⥏ B = R ⥏ B.
Proof with auto.
  intros * Hsub. ext Hx.
  - apply SepE in Hx as [Hx Hp]. apply SepE1 in Hx.
    apply CPrdE1 in Hp as [a [Ha [b [Hb Heq]]]]. subst x.
    apply SepI... apply CPrdI...
  - apply SepE in Hx as [Hx Hp].
    apply CPrdE1 in Hp as [a [Ha [b [Hb Heq]]]]. subst x.
    apply SepI; [|apply CPrdI]...
    apply SepI... apply CPrdI; apply Hsub...
Qed.

(* Theorem 7J *)
Theorem subRel_poset : ∀ A R B, poset A R → B ⊆ A → poset B (R ⥏ B).
Proof with eauto.
  intros * [Hbr [_ [Htr Hir]]] Hsub.
  repeat split.
  - intros p Hp. apply SepE2 in Hp...
  - eapply binRel_is_rel.
    intros p Hp. apply SepE2 in Hp...
  - intros x y z Hxy Hyz.
    apply SepE in Hxy as [Hxy Hx]. apply CPrdE2 in Hx as [Hx _].
    apply SepE in Hyz as [Hyz Hz]. apply CPrdE2 in Hz as [_ Hz].
    apply SepI. eapply Htr... apply CPrdI...
  - intros x Hp. eapply Hir. apply SepE1 in Hp...
Qed.

(* Theorem 7J *)
Theorem subRel_loset : ∀ A R B, loset A R → B ⊆ A → loset B (R ⥏ B).
Proof with eauto.
  intros * Hlo Hsub.
  apply loset_iff_connected_poset in Hlo as [Hcon Hpo].
  apply loset_iff_connected_poset.
  split; [|eapply subRel_poset]...
  intros x Hx y Hy Hnq.
  apply Hcon in Hnq as []; [left|right|apply Hsub..]...
  - apply SepI... apply CPrdI...
  - apply SepI... apply CPrdI...
Qed.

Lemma subRel_empty : ∀ R, R ⥏ ∅ = ∅.
Proof with auto.
  intros. ext Hx.
  - apply SepE in Hx as [_ Hx].
    rewrite cprd_0_l in Hx. exfalso0.
  - exfalso0.
Qed.

Lemma empty_is_binRel : is_binRel ∅ ∅.
Proof. intros p Hp. exfalso0. Qed.

Lemma empty_trans : tranr ∅.
Proof. intros x y z Hxy. exfalso0. Qed.

Lemma empty_trich : trich ∅ ∅.
Proof. intros x Hx. exfalso0. Qed.

Lemma empty_loset : loset ∅ ∅.
Proof with auto.
  split; [|split]. apply empty_is_binRel.
  apply empty_trans. apply empty_trich.
Qed.
