(** Coq coding by choukh, Jav 2021 **)

Require Import FinFun.
Require Import Relation_Definitions.
Require Import RelationClasses.
Require Import ZFC.Theory.EST7_6.
Import RegularityConsequences.

Module ForAnyType.

Local Hint Resolve all_grounded : core.

Local Definition F := λ T, T → set.
Local Definition R := λ T, relation T.

Local Definition 𝒜 {T} : F T → R T → T → set :=
  λ F R t, {B ∊ V (rank (F t))⁺ | ∃ s, B = F s ∧ R s t}.
Local Definition P {T} : F T → R T → T → set → Prop :=
  λ F R t ξ, 𝒜 F R t ∩ V ξ ≠ ∅.
Local Definition Ω {T} : F T → R T → T → set :=
  λ F R t, {ξ ∊ (rank (F t))⁺⁺ | P F R t ξ}.
Local Definition μ {T} : F T → R T → T → set :=
  λ F R t, OrdMin (rank (F t))⁺⁺ (P F R t).

Definition scott {T} : F T → R T → T → set :=
  λ F R t, 𝒜 F R t ∩ V (μ F R t).

Local Lemma A_in_𝒜 {T} {F : F T} {R : R T} :
  Equivalence R → ∀ t, F t ∈ 𝒜 F R t.
Proof with auto.
  intros. apply SepI... apply grounded_under_rank...
  exists t. split... apply H.
Qed.
Local Hint Resolve A_in_𝒜 : core.

Local Lemma μ_is_min {T} {F : F T} {R : R T} :
  Equivalence R → ∀ t, μ F R t ∈ Ω F R t ∧
  ∀ξ ∈ Ω F R t, (μ F R t ≤ᵣ ξ) (MemberRel (rank (F t))⁺⁺).
Proof with auto.
  intros. apply ordMin_correct...
  exists (rank (F t))⁺. split. apply BUnionI2...
  apply EmptyNI. exists (F t). apply BInterI...
  apply grounded_under_rank...
Qed.

Local Lemma μ_is_ord {T} {F : F T} {R : R T} :
  Equivalence R → ∀ t, μ F R t ⋵ 𝐎𝐍.
Proof.
  intros. destruct (@μ_is_min T F R H t) as [Hμ _].
  apply SepE1 in Hμ. eapply ord_is_ords; revgoals; eauto.
Qed.
Local Hint Resolve μ_is_ord : core.

Local Fact μ_is_suc {T} {F : F T} {R : R T} :
  Equivalence R → ∀ t, μ F R t ⋵ 𝐎𝐍ˢᵘᶜ.
Proof with eauto.
  intros Heq t. destruct (@μ_is_min T F R Heq t) as [Hμ Hmin]...
  apply SepE in Hμ as [Hμ HP].
  destruct (sucord_or_limord (μ F R t)) as [|Hlim]... exfalso.
  apply V_limit in Hlim. apply EmptyNE in HP as [B HB].
  apply BInterE in HB as [H1 H2]. rewrite Hlim in H2.
  apply FUnionE in H2 as [ξ [Hξ Ha]].
  assert (ξ ∈ Ω F R t). {
    apply SepI. eapply ord_trans...
    apply EmptyNI. exists B. apply BInterI...
  }
  apply Hmin in H as [].
  - apply binRelE3 in H. eapply ord_not_lt_gt; revgoals...
    eapply ord_is_ords; revgoals...
  - subst. eapply ord_not_lt_gt; revgoals...
Qed.

Lemma scott_nonempty {T} {F : F T} {R : R T} :
  Equivalence R → ∀ t, scott F R t ≠ ∅.
Proof.
  intros. destruct (@μ_is_min T F R H t) as [Hμ _].
  apply SepE2 in Hμ. apply Hμ.
Qed.

Lemma scott_intro {T} {F : F T} {R : R T} :
  Equivalence R → ∀ t B, (∃ u, B = F u ∧ R u t ∧
    ∀ v, R u v → rank (F u) ⋸ rank (F v)
  ) → B ∈ scott F R t.
Proof with eauto.
  intros Heq * [u [HFu [Hut Hrank]]]. subst B.
  apply Hrank in Hut as Hle.
  apply ord_le_iff_lt_suc in Hle...
  apply BInterI. apply SepI...
  apply V_iff_rank... apply V_iff_rank...
  destruct (@μ_is_min T F R Heq t) as [Hμ _]...
  apply SepE2 in Hμ.
  apply EmptyNE in Hμ as [C HC].
  apply BInterE in HC as [H1 H2].
  apply V_iff_rank in H2...
  apply SepE2 in H1 as [v [HFv H1]].
  subst C. rewrite <- Hut in H1.
  symmetry in H1. apply Hrank in H1 as [].
  eapply ord_trans... rewrite H...
Qed.

Lemma scott_elim {T} {F : F T} {R : R T} :
  Equivalence R → ∀ t, ∀B ∈ scott F R t,
  ∃ u, B = F u ∧ R u t ∧ ∀ v, R u v → rank (F u) ⋸ rank (F v).
Proof with eauto.
  intros Heq t B HB.
  apply BInterE in HB as [H1 H2].
  apply SepE in H1 as [H1 [u [HFu Hut]]].
  subst B. exists u. repeat split... intros v Huv.
  apply V_iff_rank in H1...
  apply V_iff_rank in H2...
  apply ord_le_iff_not_gt... intros Hlt.
  assert (rank (F u) ∈ Ω F R t). {
    apply SepI. apply BUnionI1... apply EmptyNI.
    exists (F v). apply BInterI. apply SepI.
    - apply V_iff_rank... eapply ord_trans...
    - exists v. split...
      eapply Equivalence_Transitive... symmetry...
    - eapply V_intro... apply PowerAx...
      apply grounded_in_rank...
  }
  destruct (@μ_is_min T F R Heq t) as [_ Hmin]...
  apply Hmin in H as [].
  - apply binRelE3 in H. eapply ord_not_lt_gt; revgoals...
  - rewrite H in H2. eapply ord_irrefl; revgoals...
Qed.

Fact scott_spec {T} {F : F T} {R : R T} :
  Equivalence R → ∀ t B,
  (∃ u, B = F u ∧ R u t ∧ ∀ v, R u v → rank (F u) ⋸ rank (F v)) ↔
  B ∈ scott F R t.
Proof.
  split; intros.
  - apply scott_intro; tauto.
  - apply scott_elim; auto.
Qed.

Theorem scott_correct {T} {F : F T} {R : R T} :
  Injective F → Equivalence R →
  ∀ t u, scott F R t = scott F R u ↔ R t u.
Proof with eauto.
  intros Hinj Heq *. split; intros.
  - pose proof (@scott_nonempty T F R Heq t) as Hne.
    apply EmptyNE in Hne as [C HC]...
    assert (HD := HC). rewrite H in HD.
    apply scott_elim in HC as [v [HFv [Hvt _]]]...
    apply scott_elim in HD as [w [HFw [Hwt _]]]...
    subst C. apply Hinj in HFw. subst w.
    eapply Equivalence_Transitive... symmetry...
  - ext Hx.
    + apply scott_elim in Hx as [v [HFv [Hqn Hmin]]]...
      apply scott_intro... exists v. repeat split...
      eapply Equivalence_Transitive...
    + apply scott_elim in Hx as [v [HFv [Hqn Hmin]]]...
      apply scott_intro... exists v. repeat split...
      eapply Equivalence_Transitive... symmetry...
Qed.

End ForAnyType.

Module ForSet.
Import ForAnyType.

Definition scott := λ R A, scott (λ x, x) R A.

Lemma scott_nonempty : ∀ R A, Equivalence R → scott R A ≠ ∅.
Proof.
  intros. apply scott_nonempty. apply H.
Qed.

Lemma scott_intro : ∀ R A B, Equivalence R → R B A →
  (∀ C, R B C → rank B ⋸ rank C) → B ∈ scott R A.
Proof with auto.
  intros. apply scott_intro... exists B. repeat split...
Qed.

Lemma scott_elim : ∀ R A, ∀B ∈ scott R A, Equivalence R → 
  R B A ∧ ∀ C, R B C → rank B ⋸ rank C.
Proof.
  intros R A B HB H.
  destruct (@scott_elim set (λ x, x) R H A B HB)
    as [C [Heq [Hr Hrank]]]. subst C. split; auto.
Qed.

Fact scott_spec : ∀ R A B, Equivalence R →
  (R B A ∧ ∀ C, R B C → rank B ⋸ rank C) ↔ B ∈ scott R A.
Proof.
  split; intros.
  - apply scott_intro; tauto.
  - apply scott_elim; auto.
Qed.

Theorem scott_correct : ∀ R A B, Equivalence R →
  scott R A = scott R B ↔ R A B.
Proof with auto.
  intros * Heq. apply scott_correct... intros x y...
Qed.

End ForSet.
