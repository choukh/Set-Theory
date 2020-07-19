(** Based on "Elements of Set Theory" Chapter 5 Part 5 **)
(** Coq coding by choukh, July 2020 **)

Require Export ZFC.CH5_1.

(*** EST第五章5：实数的定义(戴德金分割)，实数的序，实数的完备性，
  实数运算：加法，加法逆元 ***)

(* 柯西序列 *)
Module CauchyReal.

Open Scope Rat_scope.

Definition CauchySeq : set :=
  {s ∊ ω ⟶ ℚ | λ s,
    ∀ε ∈ ℚ, ratPos ε → ∃k ∈ ω, ∀ m n ∈ ω, k ∈ m → k ∈ n →
    |s[m] - s[n]| <𝐪 ε
  }.

Definition CauchyEquiv : set :=
  Relation CauchySeq CauchySeq (λ r s,
    ∀ε ∈ ℚ, ratPos ε → ∃k ∈ ω, ∀n ∈ ω, k ∈ n →
    |r[n] - s[n]| <𝐪 ε
  ).

Declare Scope CauchyReal_scope.
Open Scope CauchyReal_scope.

Notation "~" := CauchyEquiv : CauchyReal_scope.
Notation "r ~ s" := (<r, s> ∈ CauchyEquiv)
  (at level 10) : CauchyReal_scope.

Definition ℝ : set := (CauchySeq/~)%zfc.

End CauchyReal.

(** 戴德金分割 **)
Definition is_DedekindCut : set → Prop := λ x,
  (* a. 非平凡 *) (x ≠ ∅ ∧ x ≠ ℚ) ∧
  (* b. 向下封闭 *) (∀ p q ∈ ℚ, p <𝐪 q → q ∈ x → p ∈ x) ∧
  (* c. 无最大数 *) ∀p ∈ x, ∃q ∈ x, p <𝐪 q.

Definition ℝ : set := {x ∊ 𝒫 ℚ | is_DedekindCut}.

Lemma reals_sub_power_rat : ℝ ⊆ 𝒫 ℚ.
Proof. intros x Hx. apply SepE in Hx as []; auto. Qed.

Lemma real_sub_rat : ∀x ∈ ℝ, x ⊆ ℚ.
Proof.
  intros x Hx. apply reals_sub_power_rat in Hx.
  apply PowerAx in Hx. apply Hx.
Qed.

Lemma comp_inhabited : ∀ a A, a ⊂ A → ⦿ (A - a)%zfc.
Proof with auto.
  intros * [Hsub Hnq]. apply EmptyNE.
  intros H0. apply ch2_17_1_2 in H0.
  apply Hnq. apply sub_asym...
Qed.

(* 左集存在有理数 *)
Lemma realE0 : ∀x ∈ ℝ, ∃r ∈ ℚ, r ∈ x.
Proof with auto.
  intros x Hx. apply real_sub_rat in Hx as Hsub.
  apply SepE in Hx as [_ [[H _] _]]. apply EmptyNE in H as [r Hr].
  exists r. split... apply Hsub...
Qed.

(* 右集也存在有理数 *)
Lemma realE1 : ∀x ∈ ℝ, ∃r ∈ ℚ, r ∉ x.
Proof with auto.
  intros x Hx.
  apply real_sub_rat in Hx as Hxsub.
  apply SepE in Hx as [_ [[_ H] _]].
  pose proof (comp_inhabited x ℚ) as [r Hr]. split...
  apply CompE in Hr as [Hrq Hrx]. exists r. split...
Qed.

(* 小于左集的都在左集 *)
Lemma realE2 : ∀x ∈ ℝ, ∀ p q ∈ ℚ, p <𝐪 q → q ∈ x → p ∈ x.
Proof. intros x Hx. apply SepE in Hx as [_ [_ [H _]]]. auto. Qed.

(* 左集里无最大 *)
Lemma realE3 : ∀x ∈ ℝ, ∀p ∈ x, ∃q ∈ x, p <𝐪 q.
Proof. intros x Hx. apply SepE in Hx as [_ [_ [_ H]]]. auto. Qed.

(* 右集的比左集的都大 *)
Lemma realE2_1 : ∀x ∈ ℝ, ∀ p q ∈ ℚ, p ∈ x → q ∉ x → p <𝐪 q.
Proof with auto.
  intros x Hx p Hp q Hq Hpx Hqx.
  destruct (classic (p = q)). subst. exfalso...
  apply ratLt_connected in H as []...
  apply realE2 in Hx. apply Hx in H... exfalso...
Qed.

(* 比右集的大的都在右集 *)
Lemma realE2_2 : ∀x ∈ ℝ, ∀ p q ∈ ℚ, p ∉ x → p <𝐪 q → q ∉ x.
Proof with eauto.
  intros x Hx p Hp q Hq Hpx Hpq.
  destruct (classic (q ∈ x))... exfalso.
  eapply realE2 in H...
Qed.

(* 存在比左集的都大的（在右集） *)
Lemma realE1' : ∀x ∈ ℝ, ∃r ∈ ℚ, ∀q ∈ x, q <𝐪 r.
Proof with eauto.
  intros x Hx. assert (Hx' := Hx).
  apply realE1 in Hx' as [r [Hrq Hrx]].
  exists r. split... intros q Hq.
  apply real_sub_rat in Hx as Hxq.
  apply Hxq in Hq as Hqq. eapply realE2_1...
Qed.

Close Scope Rat_scope.
Open Scope Int_scope.

(** 实数的序 **)
Definition RealLt : set := Relation ℝ ℝ (λ x y, x ⊂ y).
Notation "x <𝐫 y" := (<x, y> ∈ RealLt) (at level 70).

Lemma realLtI : ∀ x y ∈ ℝ, x ⊂ y → x <𝐫 y.
Proof with auto.
  intros x Hx y Hy Hsub.
  apply SepI. apply CProdI... zfcrewrite.
Qed.

Lemma realLtE : ∀ x y, x <𝐫 y → x ∈ ℝ ∧ y ∈ ℝ ∧ x ⊂ y.
Proof with auto.
  intros * Hsub.
  apply SepE in Hsub as [H1 H2].
  apply CProdE1 in H1 as [Hx Hy]. zfcrewrite...
Qed.

Lemma realLt : ∀ x y ∈ ℝ, x <𝐫 y ↔ x ⊂ y.
Proof with auto.
  intros x Hx y Hy. split. apply realLtE. apply realLtI...
Qed.

Lemma realLt_rel : rel RealLt ℝ.
Proof with auto.
  intros x Hx. apply SepE in Hx as []...
Qed.

Lemma realLt_tranr : tranr RealLt.
Proof with eauto.
  intros x y z H1 H2.
  apply realLtE in H1 as [Hx [Hy [Hxy1 Hxy2]]].
  apply realLtE in H2 as [_  [Hz [Hyz1 Hyz2]]].
  apply realLtI... split. eapply sub_tran...
  intros Heq. subst x. apply Hyz2. apply sub_asym...
Qed.

Lemma realLt_irreflexive : irreflexive RealLt ℝ.
Proof with auto.
  intros [x [Hx Hlt]].
  apply realLt in Hlt as [Hsub Hnq]...
Qed.

Lemma realLt_connected : connected RealLt ℝ.
Proof with eauto.
  intros x Hx y Hy Hnq.
  destruct (classic (x ⊆ y)).
  left. apply realLtI...
  right. apply realLtI... split... intros q Hqy.
  rewrite ch2_17_1_2 in H. apply EmptyNE in H as [r Hr].
  apply CompE in Hr as [Hrx Hry].
  assert (Hrq: r ∈ ℚ) by (eapply real_sub_rat; revgoals; eauto).
  assert (Hqq: q ∈ ℚ) by (eapply real_sub_rat; revgoals; eauto).
  eapply realE2; revgoals... eapply realE2_1...
Qed.

Lemma realLt_trich : trich RealLt ℝ.
Proof with auto.
  eapply trich_iff. apply realLt_rel. apply realLt_tranr. split.
  apply realLt_irreflexive. apply realLt_connected.
Qed.

Theorem realLt_totalOrd : totalOrd RealLt ℝ.
Proof with auto.
  split. apply realLt_rel. split. apply realLt_tranr.
  apply realLt_trich.
Qed.

Close Scope Int_scope.
Declare Scope Real_scope.
Open Scope Real_scope.
Delimit Scope Real_scope with r.

Notation "x ≤ y" := (x <𝐫 y ∨ x = y) (at level 70) : Real_scope.

Lemma realLeqI : ∀ x y ∈ ℝ, x ⊆ y → x ≤ y.
Proof with auto.
  intros x Hx y Hy Hsub.
  destruct (classic (x = y))...
  left. apply realLt...
Qed.

Lemma realLeqE : ∀ x y, x ≤ y → x ⊆ y.
Proof with auto.
  intros x y [Hlt|Heq].
  apply realLtE in Hlt as [_ [_ []]]...
  subst. apply sub_refl.
Qed.

Lemma realLeq : ∀ x y ∈ ℝ, x ≤ y ↔ x ⊆ y.
Proof with auto.
  intros x Hx y Hy. split. apply realLeqE. apply realLeqI...
Qed.

(* 上界 *)
Definition upper : set → set → set → Prop :=
  λ Ord A x, ∀y ∈ A, <y, x> ∈ Ord ∨ y = x.

(* 存在上界 *)
Definition boundedAbove : set → set → Prop :=
  λ Ord A, ∃ x, upper Ord A x.

(* 上确界 *)
Definition sup : set → set → set → Prop :=
  λ Ord A x, upper Ord A x ∧
    ∀ y, upper Ord A y → <x, y> ∈ Ord ∨ x = y.

(* 下界 *)
Definition lower : set → set → set → Prop :=
  λ Ord A x, ∀y ∈ A, <x, y> ∈ Ord ∨ x = y.

(* 存在下界 *)
Definition boundedBelow : set → set → Prop :=
  λ Ord A, ∃ x, lower Ord A x.

(* 下确界 *)
Definition inf : set → set → set → Prop :=
  λ Ord A x, lower Ord A x ∧
    ∀ y, lower Ord A y → <y, x> ∈ Ord ∨ y = x.

Lemma union_reals_sub_rat : ∀ A, A ⊆ ℝ → ⋃A ∈ 𝒫 ℚ.
Proof with auto.
  intros A H1. pose proof reals_sub_power_rat as H2.
  assert (H3: A ⊆ 𝒫 ℚ) by (eapply sub_tran; eauto).
  apply ch2_4 in H3. rewrite ch2_6_a in H3. apply PowerAx...
Qed.

Lemma union_reals_sub_upper : ∀ A z, upper RealLt A z → ⋃A ⊆ z.
Proof.
  intros A z Hupz. apply ch2_5.
  intros x Hx. apply realLeqE. apply Hupz. apply Hx.
Qed.

Lemma reals_upper_real : ∀ A x,
  A ≠ ∅ → A ⊆ ℝ → upper RealLt A x → x ∈ ℝ.
Proof with auto.
  intros A x Hi Hsub Hup. apply EmptyNE in Hi as [y Hy].
  apply Hup in Hy as Hleq. destruct Hleq as [Hlt|Heq].
  - apply realLtE in Hlt as [_ [Hx _]]...
  - subst. apply Hsub...
Qed.

Lemma union_reals_boundedAbove_real : ∀ A,
  A ≠ ∅ → A ⊆ ℝ → boundedAbove RealLt A → ⋃A ∈ ℝ.
Proof with eauto.
  intros A Hi Hsub [z Hupz]. apply SepI.
  apply union_reals_sub_rat... repeat split.
  - apply EmptyNE in Hi as [x Hx]. apply Hsub in Hx as Hxr.
    apply realE0 in Hxr as [w [_ Hw]]. apply EmptyNI.
    exists w. apply UnionAx. exists x. split...
  - apply reals_upper_real in Hupz as Hz...
    apply real_sub_rat in Hz as Hzsub.
    apply union_reals_sub_upper in Hupz.
    intros Heq. rewrite Heq in Hupz.
    apply SepE in Hz as [_ [[_ Hznq] _]].
    apply Hznq. apply sub_asym...
  - intros p Hpq q Hqq Hlt Hq.
    apply UnionAx in Hq as [x [Hx Hq]].
    apply UnionAx. exists x. split...
    apply Hsub in Hx. apply realE2 in Hx. eapply Hx...
  - intros p Hp. apply UnionAx in Hp as [x [Hx Hp]].
    apply Hsub in Hx as Hxr. apply realE3 in Hp as [q [Hq Hlt]]...
    exists q. split... apply UnionAx. exists x. split...
Qed.

(** 实数的戴德金完备性（上确界性） **)
Theorem reals_boundedAbove_has_sup : ∀ A,
  A ≠ ∅ → A ⊆ ℝ → boundedAbove RealLt A →
  ∃s ∈ ℝ, sup RealLt A s.
Proof with eauto.
  intros A Hi Hsub Hbnd.
  apply union_reals_boundedAbove_real in Hbnd as Huar...
  exists (⋃A). repeat split...
  - intros x Hxa. apply realLeq...
    apply Hsub... apply ch2_3...
  - intros y Hupy. apply realLeqI...
    eapply reals_upper_real... apply union_reals_sub_upper...
Qed.

Close Scope Real_scope.
Open Scope Int_scope.

Lemma ω_embeddable : ∀a ∈ ℤ, Int 0 ≤ a ↔ ∃n ∈ ω, a = ω_Embed[n].
Proof with nauto.
  intros a Ha. split.
  - intros [Hpa|H0]. 
    + apply intPos_natPos in Hpa as [m [Hm [Heq _]]]...
      exists m. split... rewrite ω_embed_n...
    + exists 0. split... rewrite ω_embed_n...
  - intros [n [Hn Heq]]. subst a. rewrite ω_embed_n...
    destruct (classic (n = ∅)). right. subst...
    apply lt_connected in H as []... exfalso0.
    left. apply intLt... rewrite add_0_r, add_0_r...
Qed.

Lemma ints_lower_int : ∀ A a,
  A ≠ ∅ → A ⊆ ℤ → lower IntLt A a → a ∈ ℤ.
Proof with auto.
  intros A a Hi Hsub Hlow. apply EmptyNE in Hi as [b Hb].
  apply Hlow in Hb as Hleq. destruct Hleq as [Hlt|Heq].
  - apply SepE in Hlt as [Hp _].
    apply CProdE1 in Hp as [Ha _]. zfcrewrite.
  - subst. apply Hsub...
Qed.

(* 整数的向上封闭的非空子集具有良序性 *)
Lemma ints_boundedBelow_has_min : ∀ A,
  A ≠ ∅ → A ⊆ ℤ → boundedBelow IntLt A →
  ∃a ∈ A, ∀b ∈ A, a ≤ b.
Proof with auto.
  intros A Hi Hsub [b Hlow].
  apply ints_lower_int in Hlow as Hbz...
  set {λ a, a - b | a ∊ A} as A'.
  set {n ∊ ω | λ n, ω_Embed[n] ∈ A'} as N.
  assert (Hnb: -b ∈ ℤ) by (apply intAddInv_int; auto).
  assert (Hnn: ∀a' ∈ A', Int 0 ≤ a'). {
    intros a' Ha'. apply ReplAx in Ha' as [a [Ha Heq]]. subst a'.
    apply Hsub in Ha as Haz. apply Hlow in Ha as [].
    - left. rewrite <- (intAddInv_annih b)...
      apply intLt_both_side_add...
    - right. rewrite H, intAddInv_annih...
  }
  assert (HA': ∀a ∈ A, a - b ∈ A'). {
    intros a Ha. apply ReplAx. exists a. split...
  }
  assert (Hemb: ∀a ∈ A, ∃n ∈ ω, a - b = ω_Embed[n]). {
    intros a Ha. apply Hsub in Ha as Haz. apply ω_embeddable.
    apply intAdd_ran... apply Hnn. apply HA'...
  }
  assert (H0: N ≠ ∅). {
    apply EmptyNE in Hi as [c Hc]. assert (Hc' := Hc).
    apply Hemb in Hc' as [k [Hk Heqk]]... apply EmptyNI.
    exists k. apply SepI... rewrite <- Heqk... apply HA'...
  }
  assert (H1: N ⊆ ω). {
    intros n Hn. apply SepE in Hn as []...
  }
  apply ω_wellOrder in H1 as [m [Hm Hmin]]...
  apply SepE in Hm as [Hmw Hm].
  assert (Hmz: ω_Embed[m] ∈ ℤ) by (apply ω_embed_int; auto).
  exists (ω_Embed[m] + b). split.
  - apply ReplAx in Hm as [a [Ha Heq]]. apply Hsub in Ha as Haz.
    assert (Heqa: a - b + b = ω_Embed[m] + b) by congruence.
    rewrite <- Heqa, intAdd_assoc, (intAdd_comm (-b)),
      intAddInv_annih, intAdd_ident...
  - intros c Hc. apply Hsub in Hc as Hcz.
    apply HA' in Hc as Hcb. apply Hemb in Hc as [n [Hnw Heq]].
    eapply intLeq_both_side_add. apply intAdd_ran... auto. apply Hnb.
    rewrite intAdd_assoc, intAddInv_annih, intAdd_ident, Heq...
    assert (Hn: n ∈ N) by (apply SepI; congruence).
    apply Hmin in Hn as [].
    left. apply ω_embed_lt in H... right. congruence.
Qed.

Corollary ints_boundedBelow_has_min' : ∀ A,
  A ≠ ∅ → A ⊆ ℤ → boundedBelow IntLt A →
  ∃a ∈ A, (a - Int 1) ∉ A.
Proof with neauto.
  intros A Hi Hsub Hlow.
  apply ints_boundedBelow_has_min in Hlow as [a [Ha Hmin]]...
  apply Hsub in Ha as Haz. exists a. split...
  destruct (classic (a - Int 1 ∈ A))... exfalso.
  apply Hmin in H. eapply intLeq_both_side_add in H; revgoals.
  apply (int_n 1). apply intAdd_ran... auto.
  rewrite intAdd_assoc, (intAdd_comm (-Int 1)),
    intAddInv_annih, intAdd_ident in H...
  apply intLt_iff_leq_suc in H... eapply intLt_not_refl; revgoals...
Qed.

Close Scope Int_scope.
Open Scope Rat_scope.

Lemma ch5_19 : ∀x ∈ ℝ, ∀p ∈ ℚ, ratPos p →
  ∃q ∈ ℚ, q ∈ x ∧ p + q ∉ x.
Proof with neauto.
  intros x Hx p Hp Hpp.
  pose proof (realE0 x Hx) as [r [Hrq Hrx]].
  pose proof (realE1 x Hx) as [s [Hsq Hsx]].
  pose proof (ch5_18_2 p Hp r Hrq Hpp) as [b [Hb Hlo]].
  pose proof (ch5_18_1 p Hp s Hsq Hpp) as [d [Hd Hup]].
  assert (Hbq: IntEmbed[b] ∈ ℚ) by (apply intEmbed_rat; auto).
  assert (Hdq: IntEmbed[d] ∈ ℚ) by (apply intEmbed_rat; auto).
  set {a ∊ ℤ | λ a, p ⋅ IntEmbed[a] ∉ x} as A.
  pose proof (ints_boundedBelow_has_min' A) as [c [Hc Hc']].
  - apply EmptyNI. exists d. apply SepI...
    eapply realE2_2; revgoals... apply ratMul_ran...
  - intros a Ha. apply SepE in Ha as []...
  - exists b. intros a Ha. apply SepE in Ha as [Haz Hax].
    assert (Haq: IntEmbed[a] ∈ ℚ) by (apply intEmbed_rat; auto).
    destruct (classic (a = b))...
    apply intLt_connected in H as [Hlt|]... exfalso.
    apply intEmbed_lt in Hlt...
    apply (ratLt_both_side_mul _ Haq _ Hbq p) in Hlt...
    rewrite ratMul_comm, (ratMul_comm (IntEmbed[b])) in Hlt...
    assert (p ⋅ IntEmbed [a] <𝐪 r) by (eapply ratLt_tranr; eauto).
    apply Hax. eapply realE2; revgoals... apply ratMul_ran...
  - apply SepE in Hc as [Hcz Hleft].
    assert (Hc'z: (c - Int 1)%z ∈ ℤ) by (apply intAdd_ran; nauto).
    exists (p ⋅ IntEmbed[(c - Int 1)%z]). repeat split.
    + apply ratMul_ran... apply intEmbed_rat...
    + destruct (classic (p ⋅ IntEmbed[(c - Int 1)%z] ∈ x))...
      exfalso. apply Hc'. apply SepI...
    + assert (Hcq: IntEmbed[c] ∈ ℚ) by (apply intEmbed_rat; auto).
      assert (Hpcq: p ⋅ IntEmbed[c] ∈ ℚ) by (apply ratMul_ran; auto).
      assert (Hnp: -p ∈ ℚ) by (apply ratAddInv_rat; auto).
      rewrite intEmbed_add, ratMul_distr, intEmbed_addInv,
        ratMul_addInv_r, ratMul_ident, ratAdd_comm, ratAdd_assoc,
        (ratAdd_comm (-p)), ratAddInv_annih, ratAdd_ident...
      apply ratAdd_ran... apply intEmbed_rat...
Qed.

Close Scope Rat_scope.
Open Scope Real_scope.

(** 实数加法 **)
Definition RealAdd : set → set → set := λ x y,
  {λ p, (π1 p + π2 p)%q | p ∊ x × y}.
Notation "x + y" := (RealAdd x y) : Real_scope.

Lemma realAddI1 : ∀ p, ∀ x y ∈ ℝ,
  ∀q ∈ x, ∀r ∈ y, (q + r)%q = p → p ∈ x + y.
Proof with auto.
  intros p x Hx y Hy q Hqx r Hry Heq.
  apply ReplAx. exists <q, r>. split.
  apply CProdI... zfcrewrite.
Qed.

Lemma realAddI2 : ∀ x y ∈ ℝ,
  ∀q ∈ x, ∀r ∈ y, (q + r)%q ∈ x + y.
Proof with auto.
  intros x Hx y Hy q Hqx r Hry.
  apply ReplAx. exists <q, r>. split.
  apply CProdI... zfcrewrite.
Qed.

Lemma realAddE : ∀ x y ∈ ℝ, ∀z ∈ x + y,
  ∃ q r ∈ ℚ, (q ∈ x ∧ r ∈ y) ∧ (q + r)%q = z.
Proof with eauto.
  intros x Hx y Hy z Hz. assert (Hz' := Hz).
  apply ReplE in Hz' as [s [Hs Heq]].
  apply CProd_correct in Hs as [q [Hq [r [Hr Hs]]]].
  exists q. split. eapply real_sub_rat; revgoals...
  exists r. split. eapply real_sub_rat; revgoals...
  subst. zfcrewrite. split...
Qed.

Lemma realAdd_sub_rat : ∀ x y ∈ ℝ, x + y ∈ 𝒫 ℚ.
Proof with auto.
  intros x Hx y Hy. apply PowerAx. intros s Hs.
  apply ReplAx in Hs as [p [Hp Hs]].
  apply CProd_correct in Hp as [q [Hq [r [Hr Hp]]]].
  subst. zfcrewrite. apply ratAdd_ran.
  apply real_sub_rat in Hx. apply Hx...
  apply real_sub_rat in Hy. apply Hy...
Qed.

Lemma ExtNI : ∀ x, (∃r ∈ ℚ, r ∉ x) → x ≠ ℚ.
Proof with auto.
  intros x [r [Hrq Hrx]] Hext.
  rewrite ExtAx in Hext. apply Hext in Hrq...
Qed.

Lemma realAdd_ran : ∀ x y ∈ ℝ, x + y ∈ ℝ.
Proof with eauto.
  intros x Hx y Hy.
  apply SepI. apply realAdd_sub_rat... repeat split.
  - apply realE0 in Hx as [q [_ Hq]].
    apply realE0 in Hy as [r [_ Hr]].
    apply EmptyNI. exists (q + r)%q. apply ReplAx.
    exists <q, r>. split. apply CProdI... zfcrewrite.
  - assert (Hx' := Hx). assert (Hy' := Hy).
    apply realE1' in Hx' as [q [Hq H1]]...
    apply realE1' in Hy' as [r [Hr H2]]...
    assert (Hqr : (q + r)%q ∈ ℚ) by (apply ratAdd_ran; auto).
    apply ExtNI. exists (q + r)%q. split... intros H.
    apply (ratLt_not_refl (q + r)%q)...
    cut (∀p ∈ x + y, p <𝐪 (q + r)%q). intros Hlt. apply Hlt...
    intros p Hp. apply realAddE in Hp
      as [s [Hs [t [Ht [[Hsx Hty] Hst]]]]]... subst.
    eapply ratLt_both_side_add_tran... apply H1... apply H2...
  - intros p Hp s Hs Hlt H. apply realAddE in H
      as [q [Hq [r [Hr [[Hqx Hry] Hqr]]]]]... subst s.
    assert (Hnq: (-q)%q ∈ ℚ) by (apply ratAddInv_rat; auto).
    eapply ratLt_both_side_add in Hlt;
      try assumption; revgoals. apply Hnq.
    rewrite ratAdd_assoc, (ratAdd_comm r),
      <- ratAdd_assoc, ratAddInv_annih, ratAdd_ident' in Hlt...
    eapply realE2 in Hry; revgoals... apply ratAdd_ran...
    cut ((q + (p - q))%q = p). intros Heq.
    eapply realAddI1; revgoals... rewrite (ratAdd_comm p),
      <- ratAdd_assoc, ratAddInv_annih, ratAdd_ident'...
  - intros p Hp. apply realAddE in Hp
      as [q [Hq [r [Hr [[Hqx Hry] Hqr]]]]]... subst.
    apply realE3 in Hx as Hx3. apply Hx3 in Hqx as [s [Hs H1]].
    apply realE3 in Hy as Hy3. apply Hy3 in Hry as [t [Ht H2]].
    exists (s + t)%q. split. apply realAddI2...
    apply ratLt_both_side_add_tran; auto;
      eapply real_sub_rat; revgoals...
Qed.

Theorem realAdd_comm : ∀ x y ∈ ℝ, x + y = y + x.
Proof with auto.
  intros x Hx y Hy.
  apply ExtAx. intros p. split; intros Hp.
  - apply realAddE in Hp as [q [Hq [r [Hr [[Hqx Hry] Hqr]]]]]...
    subst. rewrite (ratAdd_comm)... apply realAddI2...
  - apply realAddE in Hp as [q [Hq [r [Hr [[Hqx Hry] Hqr]]]]]...
    subst. rewrite (ratAdd_comm)... apply realAddI2...
Qed.

Theorem realAdd_assoc : ∀ x y z ∈ ℝ, (x + y) + z = x + (y + z).
Proof with auto.
  intros x Hx y Hy z Hz.
  assert (Hxy: x + y ∈ ℝ) by (apply realAdd_ran; auto).
  assert (Hyz: y + z ∈ ℝ) by (apply realAdd_ran; auto).
  apply ExtAx. intros p. split; intros Hp.
  - apply realAddE in Hp as [q [Hq [r [Hr [[Hqx Hry] Hqr]]]]]...
    apply realAddE in Hqx as [s [Hs [t [Ht [[Hsx Hty] Hst]]]]]...
    subst. rewrite ratAdd_assoc...
    apply realAddI2... apply realAddI2...
  - apply realAddE in Hp as [q [Hq [r [Hr [[Hqx Hry] Hqr]]]]]...
    apply realAddE in Hry as [s [Hs [t [Ht [[Hsx Hty] Hst]]]]]...
    subst. rewrite <- ratAdd_assoc...
    apply realAddI2... apply realAddI2...
Qed.

Definition Real : nat → set := λ n, {r ∊ ℚ | λ r, r <𝐪 Rat n}.

Theorem real_n : ∀ n, Real n ∈ ℝ.
Proof with neauto.
  intros. assert (Hsubq: Real n ⊆ ℚ). {
    intros q Hq. apply SepE in Hq as []...
  }
  apply SepI. apply PowerAx... repeat split.
  - apply EmptyNI. exists (Rat n - Rat 1)%q.
    apply SepI. apply ratAdd_ran... rewrite ratAdd_comm...
    rewrite <- (ratAdd_ident' (Rat n)) at 2...
    apply ratLt_both_side_add... apply ratNeg_sn.
  - apply ExtNI. exists (Rat n). split...
    intros H. apply SepE in H as [_ H].
    eapply ratLt_not_refl; revgoals...
  - intros p Hp q Hq Hlt Hqn. apply SepE in Hqn as [_ Hqn].
    apply SepI... eapply ratLt_tranr...
  - intros p Hpn. apply SepE in Hpn as [Hp Hpn].
    apply ch5_14 in Hpn as [q [Hq [Hpq Hqn]]]...
    exists q. split... apply SepI...
Qed.
Hint Immediate real_n : number_hint.

Theorem realAdd_ident : ∀ x ∈ ℝ, x + Real 0 = x.
Proof with nauto.
  intros x Hx. apply ExtAx. intros p. split; intros Hp.
  - apply realAddE in Hp as [q [Hq [r [Hr [[Hqx Hr0] Hqr]]]]]...
    subst. apply SepE in Hr0 as [_ Hr0].
    eapply realE2; revgoals; eauto; revgoals. apply ratAdd_ran...
    rewrite ratAdd_comm... rewrite <- (ratAdd_ident' q) at 2...
    apply ratLt_both_side_add... 
  - apply real_sub_rat in Hp as Hpq... assert (Hp' := Hp).
    apply realE3 in Hp' as [r [Hr Hpr]]...
    apply real_sub_rat in Hr as Hrq...
    assert (Hnrq : (-r)%q ∈ ℚ) by (apply ratAddInv_rat; auto).
    eapply realAddI1... apply Hr. apply SepI.
    eapply ratAdd_ran. apply Hpq. apply Hnrq.
    rewrite (ratLt_both_side_add p Hpq r Hrq _ Hnrq) in Hpr.
    rewrite ratAddInv_annih in Hpr... rewrite (ratAdd_comm p),
      <- ratAdd_assoc, ratAddInv_annih, ratAdd_ident'...
Qed.

Corollary realAdd_ident' : ∀ x ∈ ℝ, Real 0 + x = x.
Proof with nauto.
  intros x Hx. rewrite realAdd_comm, realAdd_ident...
Qed.

(** 实数加法逆元 **)
Definition RealAddInv : set → set := λ x,
  {r ∊ ℚ | λ r, ∃s ∈ ℚ, r <𝐪 s ∧ (-s)%q ∉ x}.
Notation "- x" := (RealAddInv x) : Real_scope.
Notation "x - y" := (x + (-y)) : Real_scope.

Lemma realAddInv_sub_rat : ∀x ∈ ℝ, -x ∈ 𝒫 ℚ.
Proof with auto.
  intros x Hx. apply PowerAx. intros p Hp.
  apply SepE in Hp as []...
Qed.

Theorem realAddInv_real : ∀x ∈ ℝ, -x ∈ ℝ.
Proof with neauto.
  intros x Hx. assert (Hx' := Hx). apply SepI. 
  apply realAddInv_sub_rat... repeat split.
  - apply realE1 in Hx' as [t [Htq Htx]].
    apply EmptyNI. exists (-t - Rat 1)%q.
    assert (Hntq : (-t)%q ∈ ℚ) by (apply ratAddInv_rat; auto).
    apply SepI. apply ratAdd_ran... exists (-t)%q. split... split.
    + rewrite ratAdd_comm...
      rewrite <- (ratAdd_ident' (-t)%q) at 2...
      apply ratLt_both_side_add... apply ratNeg_sn.
    + rewrite ratAddInv_double...
  - apply realE0 in Hx' as [p [Hp Hpx]]. apply ExtNI.
    assert (Hnpq : (-p)%q ∈ ℚ) by (apply ratAddInv_rat; auto).
    exists (-p)%q. split... intros H.
    apply SepE in H as [_ [s [Hsq [Hlt Hsx]]]].
    assert (Hnsq : (-s)%q ∈ ℚ) by (apply ratAddInv_rat; auto).
    apply Hsx. clear Hsx. eapply realE2; swap 4 5.
    apply Hx. apply Hnsq. apply Hp. apply Hpx.
    rewrite (ratLt_both_side_add _ Hnpq _ Hsq _ Hp) in Hlt.
    rewrite ratAdd_comm, ratAddInv_annih, <- (ratAddInv_annih s),
      ratAdd_comm, (ratAdd_comm s) in Hlt...
    apply ratLt_both_side_add in Hlt...
  - intros p Hp q Hq Hpq Hqx.
    apply SepE in Hqx as [_ [s [Hs [Hqs Hsx]]]]. apply SepI...
    exists s. split... split... eapply ratLt_tranr...
  - intros p Hp. apply SepE in Hp as [Hp [s [Hs [Hps Hsx]]]].
    apply ch5_14 in Hps as [r [Hr [Hpr Hrs]]]...
    exists r. split... apply SepI... exists s. split...
Qed.

Lemma ratLt_r2_1 : (Rat 2)⁻¹%q <𝐪 Rat 1.
Proof with nauto.
  unfold Rat.
  rewrite ratMulInv... apply ratLt...
  rewrite intMul_ident', intMul_ident'...
  apply intLt... rewrite add_0_r, add_0_r, (pred 2)...
Qed.

Theorem realAdd_annih : ∀x ∈ ℝ, x - x = Real 0.
Proof with neauto.
  intros x Hx. apply ExtAx.
  assert (Hnx: -x ∈ ℝ) by (apply realAddInv_real; auto).
  intros p. split; intros Hp.
  - apply realAddE in Hp as [q [Hq [r [Hr [[Hqx Hrx] Heq]]]]]...
    apply SepE in Hrx as [_ [s [Hs [Hrs Hsx]]]].
    subst p. apply SepI. apply ratAdd_ran...
    rewrite ratAdd_comm, <- (ratAddInv_annih s)...
    Close Scope Real_scope. Open Scope Rat_scope.
    assert (Hns: -s ∈ ℚ) by (apply ratAddInv_rat; auto).
    apply ratLt_both_side_add_tran...
    eapply realE2_1; revgoals...
  - apply SepE in Hp as [Hp Hnp]. apply rat_neg_pos in Hnp.
    assert (Hnpq: -p ∈ ℚ) by (apply ratAddInv_rat; auto).
    assert (H2q: p / Rat 2 ∈ ℚ) by (apply ratMul_ran; nauto).
    assert (Hp2: ratPos (-p / Rat 2))
      by (eapply ratMul_pos_prod; neauto).
    apply (ch5_19 x) in Hp2 as [q [Hqq [Hq Hleft]]];
      [|auto|apply ratMul_ran; nauto].
    assert (Hnqq: -q ∈ ℚ) by (apply ratAddInv_rat; auto).
    assert (Heq: q + (p - q) = p). {
      rewrite (ratAdd_comm p), <- ratAdd_assoc,
        ratAddInv_annih, ratAdd_ident'; auto.
    }
    eapply realAddI1... apply SepI. apply ratAdd_ran...
    exists (p / Rat 2 - q). split. apply ratAdd_ran... split.
    + apply ratLt_both_side_add... apply ratLt_addInv...
      rewrite <- ratMul_addInv_l, ratMul_comm...
      rewrite <- (ratMul_ident' (-p)) at 2...
      apply ratLt_both_side_mul... apply ratLt_r2_1.
    + rewrite ratAddInv_diff, ratAdd_comm, <- ratMul_addInv_l...
      apply ratAddInv_rat...
Qed.

Close Scope Rat_scope.
Open Scope Real_scope.

Corollary realAddInv_double : ∀x ∈ ℝ, --x = x.
Proof with auto.
  intros x Hx.
  assert (Hn: -x ∈ ℝ) by (apply realAddInv_real; auto).
  assert (Hnn: --x ∈ ℝ) by (apply realAddInv_real; auto).
  rewrite <- (realAdd_ident (--x)), <- (realAdd_annih x),
    realAdd_comm, realAdd_assoc, realAdd_annih, realAdd_ident...
  apply realAdd_ran...
Qed.
