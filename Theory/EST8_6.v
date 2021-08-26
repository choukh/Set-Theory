(** Adapted from "Elements of Set Theory" Chapter 8 **)
(** Coq coding by choukh, June 2021 **)

Require Import ZFC.Lib.WoStructExtension.
Require Export ZFC.Theory.EST8_5.
Import OrderType.
Import WoStruct.
Import StructureCasting.

(*** EST第八章6：序数算术（基于序类型算术） ***)

Declare Scope OrdArithₜ_scope.
Delimit Scope OrdArithₜ_scope with oaₜ.
Open Scope OrdArithₜ_scope.

Definition ordSum_spec := λ α β γ,
  ∀ S T, α = ord S → β = ord T → γ = ord (S + T).

Lemma ordSum_exists : ∀ α β ⋵ 𝐎𝐍, ∃! γ, ordSum_spec α β γ.
Proof.
  intros α [S Hα] β [T Hβ]. rewrite <- unique_existence. split.
  - exists (ord (S + T)). intros S' T' HS' HT'. subst.
    apply ord_well_defined in HS'.
    apply ord_well_defined in HT'.
    apply ord_well_defined.
    apply woAdd_well_defined; auto.
  - intros α' β' Hα' Hβ'.
    pose proof (Hα' S T Hα Hβ).
    pose proof (Hβ' S T Hα Hβ). congruence.
Qed.

(* 序数加法（基于序类型） *)
Definition OrdAddₜ := λ α β, describe (ordSum_spec α β).
Notation "α + β" := (OrdAddₜ α β) : OrdArithₜ_scope.

Lemma ordSum_spec_intro : ∀ α β ⋵ 𝐎𝐍, ordSum_spec α β (α + β).
Proof.
  intros α Hoα β Hoβ. apply (desc_spec (ordSum_spec α β)).
  apply ordSum_exists; auto.
Qed.

Lemma ordAddₜ_ran : ∀ α β ⋵ 𝐎𝐍, α + β ⋵ 𝐎𝐍.
Proof.
  intros α [S HS] β [T HT]. subst.
  erewrite ordSum_spec_intro; auto.
Qed.

Lemma ordAddₜ_eq_ord_of_woAdd : ∀ S T, ord S + ord T = ord (S + T)%wo.
Proof.
  intros. apply ordSum_spec_intro; auto.
Qed.

Theorem ordAddₜ_well_defined : ∀ S S' T T',
  S ≅ S' → T ≅ T' → ord S + ord T = ord S' + ord T'.
Proof.
  intros * HisoS HisoT. do 2 rewrite ordAddₜ_eq_ord_of_woAdd.
  apply ord_well_defined. apply woAdd_well_defined; auto.
Qed.

Lemma ordAddₜ_iff_woAdd : ∀ S T U,
  ord S + ord T = ord U ↔ (S + T)%wo ≅ U.
Proof.
  intros. split; intros H.
  - apply ord_well_defined.
    rewrite <- ordAddₜ_eq_ord_of_woAdd. apply H.
  - rewrite ordAddₜ_eq_ord_of_woAdd.
    apply ord_well_defined. apply H.
Qed.

Fact ordAddₜ_iff_otAdd : ∀ S T U,
  ord S + ord T = ord U ↔ (otʷ S + otʷ T = otʷ U)%ot.
Proof.
  intros. rewrite ordAddₜ_iff_woAdd, woAdd_iff_loAdd.
  unfold otʷ. rewrite otAdd_iff_loAdd. reflexivity.
Qed.

Fact otAdd_eq_ot_of_woAdd : ∀ S T, (otʷ S + otʷ T)%ot = otʷ (S + T)%wo.
Proof.
  intros. apply ordAddₜ_iff_otAdd. apply ordAddₜ_eq_ord_of_woAdd.
Qed.

Lemma ordAddₜ_n_m : ∀ n m : nat, n + m = (n + m)%nat.
Proof.
  intros. pose proof (woAdd_n_m n m).
  apply ord_well_defined in H.
  rewrite <- ordAddₜ_eq_ord_of_woAdd in H.
  repeat rewrite ord_WOⁿ_id in H. apply H.
Qed.

Example ordAddₜ_1_1 : 1 + 1 = 2.
Proof. apply ordAddₜ_n_m. Qed.

Example ordAddₜ_1_ω : 1 + ω = ω.
Proof.
  rewrite <- ord_WOⁿ_id, <- (ord_WOᵒ_id ω ω_is_ord).
  apply ordAddₜ_iff_otAdd. apply otAdd_1_ω.
Qed.

Example ordAddₜ_ω_1 : ω + 1 = ω⁺.
Proof.
  rewrite <- ord_WOⁿ_id.
  rewrite <- (ord_WOᵒ_id ω ω_is_ord) at 1.
  rewrite <- (ord_WOᵒ_id ω⁺ (ord_suc_is_ord ω ω_is_ord)).
  apply ordAddₜ_iff_otAdd. apply otAdd_ω_1.
Qed.

Lemma ordAddₜ_1 : ∀α ⋵ 𝐎𝐍, α + 1 = α⁺.
Proof.
  intros α Ho.
  rewrite <- ord_WOⁿ_id.
  rewrite <- (ord_WOᵒ_id α Ho) at 1.
  rewrite <- (ord_WOᵒ_id α⁺ (ord_suc_is_ord α Ho)).
  apply ordAddₜ_iff_woAdd. apply woAdd_suc.
Qed.

Definition ordPrd_spec := λ α β γ,
  ∀ S T, α = ord S → β = ord T → γ = ord (S ⋅ T).

Lemma ordPrd_exists : ∀ α β ⋵ 𝐎𝐍, ∃! γ, ordPrd_spec α β γ.
Proof.
  intros α [S Hα] β [T Hβ]. rewrite <- unique_existence. split.
  - exists (ord (S ⋅ T)). intros S' T' HS' HT'. subst.
    apply ord_well_defined in HS'.
    apply ord_well_defined in HT'.
    apply ord_well_defined.
    apply woMul_well_defined; auto.
  - intros α' β' Hα' Hβ'.
    pose proof (Hα' S T Hα Hβ).
    pose proof (Hβ' S T Hα Hβ). congruence.
Qed.

(* 序数加法（基于序类型） *)
Definition OrdMulₜ := λ α β, describe (ordPrd_spec α β).
Notation "α ⋅ β" := (OrdMulₜ α β) : OrdArithₜ_scope.

Lemma ordPrd_spec_intro : ∀ α β ⋵ 𝐎𝐍, ordPrd_spec α β (α ⋅ β).
Proof.
  intros α Hoα β Hoβ. apply (desc_spec (ordPrd_spec α β)).
  apply ordPrd_exists; auto.
Qed.

Lemma ordMulₜ_ran : ∀ α β ⋵ 𝐎𝐍, α ⋅ β ⋵ 𝐎𝐍.
Proof.
  intros α [S HS] β [T HT]. subst.
  erewrite ordPrd_spec_intro; auto.
Qed.

Lemma ordMulₜ_eq_ord_of_woMul : ∀ S T, ord S ⋅ ord T = ord (S ⋅ T)%wo.
Proof.
  intros. apply ordPrd_spec_intro; auto.
Qed.

Theorem ordMulₜ_well_defined : ∀ S S' T T',
  S ≅ S' → T ≅ T' → ord S ⋅ ord T = ord S' ⋅ ord T'.
Proof.
  intros * HisoS HisoT. do 2 rewrite ordMulₜ_eq_ord_of_woMul.
  apply ord_well_defined. apply woMul_well_defined; auto.
Qed.

Lemma ordMulₜ_iff_woMul : ∀ S T U,
  ord S ⋅ ord T = ord U ↔ (S ⋅ T)%wo ≅ U.
Proof.
  intros. split; intros H.
  - apply ord_well_defined.
    rewrite <- ordMulₜ_eq_ord_of_woMul. apply H.
  - rewrite ordMulₜ_eq_ord_of_woMul.
    apply ord_well_defined. apply H.
Qed.

Fact ordMulₜ_iff_otMul : ∀ S T U,
  ord S ⋅ ord T = ord U ↔ (otʷ S ⋅ otʷ T = otʷ U)%ot.
Proof.
  intros. rewrite ordMulₜ_iff_woMul, woMul_iff_loMul.
  unfold otʷ. rewrite otMul_iff_loMul. reflexivity.
Qed.

Fact otMul_eq_ot_of_woMul : ∀ S T, (otʷ S ⋅ otʷ T)%ot = otʷ (S ⋅ T)%wo.
Proof.
  intros. apply ordMulₜ_iff_otMul. apply ordMulₜ_eq_ord_of_woMul.
Qed.

Lemma ordMulₜ_n_m : ∀ n m : nat, n ⋅ m = (n * m)%nat.
Proof.
  intros. pose proof (woMul_n_m n m).
  apply ord_well_defined in H.
  rewrite <- ordMulₜ_eq_ord_of_woMul in H.
  repeat rewrite ord_WOⁿ_id in H. apply H.
Qed.

Example ordMulₜ_2_3 : 2 ⋅ 3 = 6.
Proof. apply ordMulₜ_n_m. Qed.

(** 序数算术定律 **)

Theorem ordAddₜ_assoc : ∀ α β γ ⋵ 𝐎𝐍, α + β + γ = α + (β + γ).
Proof.
  intros α Hoα β Hoβ γ Hoγ.
  rewrite <- (ord_WOᵒ_id α Hoα), <- (ord_WOᵒ_id β Hoβ), <- (ord_WOᵒ_id γ Hoγ).
  repeat rewrite ordAddₜ_eq_ord_of_woAdd.
  apply otʷ_iff_ord.
  repeat rewrite <- otAdd_eq_ot_of_woAdd.
  apply otAdd_assoc; apply ot_is_ot.
Qed.

Theorem ordMulₜ_assoc : ∀ α β γ ⋵ 𝐎𝐍, α ⋅ β ⋅ γ = α ⋅ (β ⋅ γ).
Proof.
  intros α Hoα β Hoβ γ Hoγ.
  rewrite <- (ord_WOᵒ_id α Hoα), <- (ord_WOᵒ_id β Hoβ), <- (ord_WOᵒ_id γ Hoγ).
  repeat rewrite ordMulₜ_eq_ord_of_woMul.
  apply otʷ_iff_ord.
  repeat rewrite <- otMul_eq_ot_of_woMul.
  apply otMul_assoc; apply ot_is_ot.
Qed.

Theorem ordMulₜ_distr : ∀ α β γ ⋵ 𝐎𝐍, α ⋅ (β + γ) = α ⋅ β + α ⋅ γ.
Proof.
  intros α Hoα β Hoβ γ Hoγ.
  rewrite <- (ord_WOᵒ_id α Hoα), <- (ord_WOᵒ_id β Hoβ), <- (ord_WOᵒ_id γ Hoγ).
  rewrite ordAddₜ_eq_ord_of_woAdd.
  repeat rewrite ordMulₜ_eq_ord_of_woMul.
  rewrite ordAddₜ_eq_ord_of_woAdd.
  apply otʷ_iff_ord.
  rewrite <- otAdd_eq_ot_of_woAdd.
  repeat rewrite <- otMul_eq_ot_of_woMul.
  rewrite <- otAdd_eq_ot_of_woAdd.
  apply otMul_distr; apply ot_is_ot.
Qed.

Theorem ordAddₜ_0_r : ∀α ⋵ 𝐎𝐍, α + 0 = α.
Proof.
  intros α Ho.
  rewrite <- (ord_WOᵒ_id α Ho), <- (ord_WOᵒ_id 0 (nat_is_ord 0)).
  rewrite ordAddₜ_eq_ord_of_woAdd.
  apply otʷ_iff_ord.
  rewrite <- otAdd_eq_ot_of_woAdd.
  apply otAdd_0_r. apply ot_is_ot.
Qed.

Theorem ordAddₜ_0_l : ∀α ⋵ 𝐎𝐍, 0 + α = α.
Proof.
  intros α Ho.
  rewrite <- (ord_WOᵒ_id α Ho), <- (ord_WOᵒ_id 0 (nat_is_ord 0)).
  rewrite ordAddₜ_eq_ord_of_woAdd.
  apply otʷ_iff_ord.
  rewrite <- otAdd_eq_ot_of_woAdd.
  apply otAdd_0_l. apply ot_is_ot.
Qed.

Theorem ordMulₜ_1_r : ∀α ⋵ 𝐎𝐍, α ⋅ 1 = α.
Proof.
  intros α Ho.
  rewrite <- (ord_WOᵒ_id α Ho), <- (ord_WOᵒ_id 1 (nat_is_ord 1)).
  rewrite ordMulₜ_eq_ord_of_woMul.
  apply otʷ_iff_ord.
  rewrite <- otMul_eq_ot_of_woMul.
  apply otMul_1_r. apply ot_is_ot.
Qed.

Theorem ordMulₜ_1_l : ∀α ⋵ 𝐎𝐍, 1 ⋅ α = α.
Proof.
  intros α Ho.
  rewrite <- (ord_WOᵒ_id α Ho), <- (ord_WOᵒ_id 1 (nat_is_ord 1)).
  rewrite ordMulₜ_eq_ord_of_woMul.
  apply otʷ_iff_ord.
  rewrite <- otMul_eq_ot_of_woMul.
  apply otMul_1_l. apply ot_is_ot.
Qed.

Theorem ordMulₜ_0_r : ∀α ⋵ 𝐎𝐍, α ⋅ 0 = 0.
Proof.
  intros α Ho.
  rewrite <- (ord_WOᵒ_id α Ho), <- (ord_WOᵒ_id 0 (nat_is_ord 0)).
  rewrite ordMulₜ_eq_ord_of_woMul.
  apply otʷ_iff_ord.
  rewrite <- otMul_eq_ot_of_woMul.
  apply otMul_0_r. apply ot_is_ot.
Qed.

Theorem ordMulₜ_0_l : ∀α ⋵ 𝐎𝐍, 0 ⋅ α = 0.
Proof.
  intros α Ho.
  rewrite <- (ord_WOᵒ_id α Ho), <- (ord_WOᵒ_id 0 (nat_is_ord 0)).
  rewrite ordMulₜ_eq_ord_of_woMul.
  apply otʷ_iff_ord.
  rewrite <- otMul_eq_ot_of_woMul.
  apply otMul_0_l. apply ot_is_ot.
Qed.

Theorem ordAddₜ_suc : ∀ α β ⋵ 𝐎𝐍, α + β⁺ = (α + β)⁺.
Proof with nauto.
  intros α Hoα β Hoβ.
  rewrite <- ordAddₜ_1, <- ordAddₜ_1...
  rewrite ordAddₜ_assoc... apply ordAddₜ_ran...
Qed.

Theorem ordMulₜ_suc : ∀ α β ⋵ 𝐎𝐍, α ⋅ β⁺ = α ⋅ β + α.
Proof with nauto.
  intros α Hoα β Hoβ.
  rewrite <- ordAddₜ_1...
  rewrite ordMulₜ_distr, ordMulₜ_1_r...
Qed.

(* 有限序数加法等效于自然数加法 *)
Theorem fin_ordAddₜ_eq_add : ∀ m n ∈ ω, m + n = (m + n)%ω.
Proof with nauto.
  intros m Hm n Hn. generalize dependent m.
  ω_induction n; intros k Hk.
  - rewrite ordAddₜ_0_r, add_0_r...
    apply (ord_is_ords ω)...
  - rewrite ordAddₜ_suc, IH, suc, suc, add_assoc...
    apply add_ran... apply (ord_is_ords ω)... apply (ord_is_ords ω)...
Qed.

(* 有限序数乘法等效于自然数乘法 *)
Theorem fin_ordMulₜ_eq_mul : ∀ m n ∈ ω, m ⋅ n = (m ⋅ n)%ω.
Proof with nauto.
  intros m Hm n Hn. generalize dependent m.
  ω_induction n; intros k Hk.
  - rewrite ordMulₜ_0_r, mul_0_r...
    apply (ord_is_ords ω)...
  - rewrite ordMulₜ_suc, IH, mul_suc, fin_ordAddₜ_eq_add, add_comm...
    apply mul_ran... apply mul_ran...
    apply (ord_is_ords ω)... apply (ord_is_ords ω)...
Qed.

(* 有限序数的和是自然数 *)
Corollary fin_ordAddₜ_ran : ∀ m n ∈ ω, m + n ∈ ω.
Proof with auto.
  intros m Hm n Hn. rewrite fin_ordAddₜ_eq_add... apply add_ran...
Qed.

(* 有限序数的积是自然数 *)
Corollary fin_ordMul_ran : ∀ m n ∈ ω, m ⋅ n ∈ ω.
Proof with auto.
  intros m Hm n Hn. rewrite fin_ordMulₜ_eq_mul... apply mul_ran...
Qed.

Section AddLimit.

Let WOₒAdd := λ α β, (WOₒ α + WOₒ β)%wo.

Local Lemma A_WOₒAdd : ∀α ⋵ 𝐎𝐍, ∀β ⋵ 𝐎𝐍,
  A (WOₒAdd α β) = α × ⎨0⎬ ∪ β × ⎨1⎬.
Proof.
  intros α Hoα β Hoβ.
  unfold WOₒAdd, WoAdd. simpl. unfold WoDisj_A.
  now repeat rewrite A_WOₒ_id.
Qed.

Local Lemma R_WOₒAdd : ∀α ⋵ 𝐎𝐍, ∀β ⋵ 𝐎𝐍, R (WOₒAdd α β) =
  {<<π1 p, 0>, <π2 p, 0>> | p ∊ MemberRel α} ∪
  {<<π1 p, 1>, <π2 p, 1>> | p ∊ MemberRel β} ∪
  (α × ⎨0⎬) × (β × ⎨1⎬).
Proof.
  intros α Hoα β Hoβ.
  unfold WOₒAdd, WoAdd, WoAdd_R. simpl.
  unfold WoDisj_A, WoDisj_R.
  now repeat rewrite A_WOₒ_id, R_WOₒ.
Qed.

Local Lemma ord_WOₒAdd : ∀α ⋵ 𝐎𝐍, ∀β ⋵ 𝐎𝐍,
  ord (WOₒAdd α β) = α + β.
Proof.
  intros α Hoα β Hoβ. unfold WOₒAdd.
  rewrite <- ordAddₜ_eq_ord_of_woAdd.
  now repeat rewrite ord_WOₒ_id.
Qed.

Let 𝒞 := λ α 𝜆, {let S := WOₒAdd α β in <A S, R S> | β ∊ 𝜆}.

Local Lemma 𝒞_is_wos : ∀α ⋵ 𝐎𝐍, ∀𝜆 ⋵ 𝐎𝐍, wos (𝒞 α 𝜆).
Proof.
  intros α Hα 𝜆 H𝜆 p Hp.
  apply ReplAx in Hp as [β [Hβ Heq]].
  exists (WOₒAdd α β). congruence.
Qed.

Local Lemma WOₒAdd_ees : ∀α ⋵ 𝐎𝐍, ∀β1 ⋵ 𝐎𝐍, ∀β2 ⋵ 𝐎𝐍,
  β1 ⋸ β2 → WOₒAdd α β1 ⊑⊑ WOₒAdd α β2.
Proof with auto.
  intros α Hoα β1 Ho1 β2 Ho2 Hsub.
  apply ord_leq_iff_sub in Hsub...
  repeat split.
  - rewrite A_WOₒAdd, A_WOₒAdd...
    intros x Hx. apply BUnionE in Hx as [].
    + apply BUnionI1...
    + apply CProdE1 in H as [a [Ha [b [Hb H0]]]].
      apply SingE in Hb. subst.
      apply BUnionI2. apply CProdI...
  - rewrite A_WOₒAdd, R_WOₒAdd, R_WOₒAdd...
    ext Hx. {
      apply BUnionE in Hx as [Hx|Hx];
      [apply BUnionE in Hx as [Hx|Hx]|].
      - apply SepI.
        + apply BUnionI1. apply BUnionI1...
        + apply ReplAx in Hx as [p [Hp Hx]].
          apply binRelE1 in Hp as [a [Ha [b [Hb [Hp Hlt]]]]].
          subst. zfc_simple.
          apply CProdI; apply BUnionI1; apply CProdI...
      - apply ReplAx in Hx as [p [Hp Hx]].
        apply binRelE1 in Hp as [a [Ha [b [Hb [Hp Hlt]]]]].
        subst. zfc_simple. apply SepI.
        + apply BUnionI1. apply BUnionI2.
          apply ReplAx. exists <a, b>. split.
          apply binRelI... zfc_simple.
        + apply CProdI; apply BUnionI2; apply CProdI...
      - apply CProdE1 in Hx as [a [Ha [b [Hb Hx]]]].
        subst. apply SepI.
        + apply BUnionI2. apply CProdI...
          apply CProdE1 in Hb as [c [Hc [d [Hd Hb]]]].
          apply SingE in Hd. subst. apply CProdI...
        + apply CProdI. apply BUnionI1... apply BUnionI2...
    } {
      apply SepE in Hx as [H1 H2].
      apply BUnionE in H1 as [Hx|Hx];
      [apply BUnionE in Hx as [Hx|Hx]|].
      - apply BUnionI1. apply BUnionI1...
      - apply BUnionI1. apply BUnionI2.
        apply ReplAx in Hx as [p [Hp Hx]].
        apply binRelE1 in Hp as [a [Ha [b [Hb [Hp Hlt]]]]].
        subst. zfc_simple.
        apply CProdE2 in H2 as [H1 H2].
        apply BUnionE in H1 as [|H1]. {
          apply CProdE2 in H as [_ H].
          apply SingE in H. exfalso. nauto.
        }
        apply BUnionE in H2 as [|H2]. {
          apply CProdE2 in H as [_ H].
          apply SingE in H. exfalso. nauto.
        }
        apply CProdE2 in H1 as [H1 _].
        apply CProdE2 in H2 as [H2 _].
        apply ReplAx. exists <a, b>. split.
        apply binRelI... zfc_simple.
      - apply BUnionI2.
        apply CProdE1 in Hx as [a [Ha [b [Hb Hx]]]]. subst.
        apply CProdI...
        apply CProdE2 in H2 as [_ H].
        apply BUnionE in H as []... exfalso.
        apply CProdE1 in Hb as [c [Hc [d [Hd H1]]]].
        apply SingE in Hd. subst.
        apply CProdE2 in H as [_ H]. apply SingE in H. nauto.
    }
  - intros x Hx y Hy.
    rewrite A_WOₒAdd in Hx...
    rewrite A_WOₒAdd, A_WOₒAdd in Hy...
    rewrite R_WOₒAdd...
    apply SepE in Hy as [Hy Hy'].
    apply BUnionE in Hx as [Hx|Hx];
    apply BUnionE in Hy as [Hy|Hy].
    + exfalso. apply Hy'. apply BUnionI1...
    + apply BUnionI2. apply CProdI...
    + exfalso. apply Hy'. apply BUnionI1...
    + apply BUnionI1. apply BUnionI2.
      apply CProdE1 in Hx as [a [Ha [b [Hb Hx]]]].
      apply CProdE1 in Hy as [c [Hc [d [Hd Hy]]]].
      apply SingE in Hb. apply SingE in Hd. subst.
      apply ReplAx. exists <a, c>. split; zfc_simple.
      assert (Hoa: a ⋵ 𝐎𝐍). apply (ord_is_ords β1)...
      assert (Hoc: c ⋵ 𝐎𝐍). apply (ord_is_ords β2)...
      apply binRelI... apply ord_lt_iff_not_sub...
      intros Hca. apply ord_leq_iff_sub in Hca...
      apply Hy'. apply BUnionI2. apply CProdI...
      destruct Hca. eapply ord_trans; eauto. subst...
Qed.

Local Lemma 𝒞_is_ees : ∀α ⋵ 𝐎𝐍, ∀𝜆 ⋵ 𝐎𝐍, ees (𝒞 α 𝜆).
Proof with auto.
  intros α Hα 𝜆 H𝜆 S T H1 H2.
  apply ReplAx in H1 as [β1 [Hβ1 H1]].
  apply ReplAx in H2 as [β2 [Hβ2 H2]].
  apply op_iff in H1 as [H11 H12].
  apply op_iff in H2 as [H21 H22].
  assert (HS: S = WOₒAdd α β1). apply eq_intro...
  assert (HT: T = WOₒAdd α β2). apply eq_intro...
  assert (Ho1: β1 ⋵ 𝐎𝐍). apply (ord_is_ords 𝜆)...
  assert (Ho2: β2 ⋵ 𝐎𝐍). apply (ord_is_ords 𝜆)...
  destruct (ord_comparability β1 Ho1 β2 Ho2);
  auto; [left|right]; rewrite HS, HT; apply WOₒAdd_ees...
Qed.

Local Lemma ordsₛ_𝒞 : ∀α ⋵ 𝐎𝐍, ∀𝜆 ⋵ 𝐎𝐍,
  ordsₛ (𝒞 α 𝜆) = {α + β | β ∊ 𝜆}.
Proof with eauto.
  intros α Hoα 𝜆 Ho𝜆.
  ext Hx.
  - apply ReplAx in Hx as [p [Hp Heq]]. subst.
    apply ReplAx in Hp as [β [Hβ Heq]]. subst.
    apply ReplAx. exists β. split...
    unfold ordₛ. rewrite WOₛ_pair_id.
    rewrite ord_WOₒAdd... apply (ord_is_ords 𝜆)...
  - apply ReplAx in Hx as [β [Hβ Heq]]. subst.
    apply ReplAx. exists <A (WOₒAdd α β), R (WOₒAdd α β)>.
    split. apply ReplAx. exists β. split...
    unfold ordₛ. rewrite WOₛ_pair_id.
    rewrite ord_WOₒAdd... apply (ord_is_ords 𝜆)...
Qed.

Local Lemma ord_union_𝒞 : ∀α ⋵ 𝐎𝐍, ∀𝜆 ⋵ 𝐎𝐍,
  ord ⊔(𝒞 α 𝜆) = sup {α + β | β ∊ 𝜆}.
Proof with eauto.
  intros α Hoα 𝜆 Ho𝜆.
  replace {α + β | β ∊ 𝜆} with (ordsₛ (𝒞 α 𝜆)).
  apply ord_union_eq_sup_ordsₛ_wos.
  apply 𝒞_is_wos... apply 𝒞_is_ees...
  apply ordsₛ_𝒞...
Qed.

Local Lemma π1_𝒞 : ∀α ⋵ 𝐎𝐍, ∀𝜆 ⋵ 𝐎𝐍,
  {π1 p | p ∊ 𝒞 α 𝜆} = {A (WOₒAdd α β) | β ∊ 𝜆}.
Proof with eauto.
  intros α Hoα 𝜆 Ho𝜆.
  ext Hx.
  - apply ReplAx in Hx as [p [Hp Heq]]. subst.
    apply ReplAx in Hp as [β [Hβ Heq]]. subst.
    apply ReplAx. exists β. split... zfc_simple.
  - apply ReplAx in Hx as [β [Hβ Heq]]. subst.
    apply ReplAx. exists <A (WOₒAdd α β), R (WOₒAdd α β)>.
    split. apply ReplAx. exists β. split... zfc_simple.
Qed.

Local Lemma π2_𝒞 : ∀α ⋵ 𝐎𝐍, ∀𝜆 ⋵ 𝐎𝐍,
  {π2 p | p ∊ 𝒞 α 𝜆} = {R (WOₒAdd α β) | β ∊ 𝜆}.
Proof with eauto.
  intros α Hoα 𝜆 Ho𝜆.
  ext Hx.
  - apply ReplAx in Hx as [p [Hp Heq]]. subst.
    apply ReplAx in Hp as [β [Hβ Heq]]. subst.
    apply ReplAx. exists β. split... zfc_simple.
  - apply ReplAx in Hx as [β [Hβ Heq]]. subst.
    apply ReplAx. exists <A (WOₒAdd α β), R (WOₒAdd α β)>.
    split. apply ReplAx. exists β. split... zfc_simple.
Qed.

Local Lemma Unionₐ_𝒞 : ∀α ⋵ 𝐎𝐍, ∀𝜆 ⋵ 𝐎𝐍ˡⁱᵐ, 𝜆 ≠ ∅ →
  Unionₐ (𝒞 α 𝜆) = α × ⎨0⎬ ∪ 𝜆 × ⎨1⎬.
Proof with eauto.
  intros α Ho 𝜆 [Ho𝜆 Heq𝜆] Hne.
  unfold Unionₐ. rewrite π1_𝒞...
  ext Hx.
  - apply UnionAx in Hx as [p [Hp Hx]].
    apply ReplAx in Hp as [β [Hβ Hp]]. subst.
    rewrite A_WOₒAdd in Hx; [|auto|apply (ord_is_ords 𝜆)]...
    apply BUnionE in Hx as []; [apply BUnionI1|apply BUnionI2]...
    apply CProdE1 in H as [a [Ha [b [Hb H]]]].
    apply SingE in Hb. subst. apply CProdI... eapply ord_trans...
  - apply BUnionE in Hx as [].
    + apply EmptyNE in Hne as [β Hβ].
      assert (Hoβ: β ⋵ 𝐎𝐍). apply (ord_is_ords 𝜆)...
      apply UnionAx. exists (α × ⎨0⎬ ∪ β × ⎨1⎬). split.
      * apply ReplAx. exists β. split... apply A_WOₒAdd...
      * apply BUnionI1...
    + apply CProdE1 in H as [β [Hβ [b [Hb H]]]].
      apply SingE in Hb. subst.
      assert (Hoβ: β ⋵ 𝐎𝐍). apply (ord_is_ords 𝜆)...
      apply UnionAx. exists (α × ⎨0⎬ ∪ β⁺ × ⎨1⎬). split.
      * apply ReplAx. exists β⁺. split.
        apply sucord_in_limord... split... apply A_WOₒAdd...
      * apply BUnionI2... apply CProdI...
Qed.

Local Lemma Unionᵣ_𝒞 : ∀α ⋵ 𝐎𝐍, ∀𝜆 ⋵ 𝐎𝐍ˡⁱᵐ, 𝜆 ≠ ∅ →
  Unionᵣ (𝒞 α 𝜆) =
  {<π1 p, 0, <π2 p, 0>> | p ∊ MemberRel α} ∪
  {<π1 p, 1, <π2 p, 1>> | p ∊ MemberRel 𝜆} ∪
  (α × ⎨0⎬) × (𝜆 × ⎨1⎬).
Proof with eauto.
  intros α Ho 𝜆 [Ho𝜆 Heq𝜆] Hne.
  unfold Unionᵣ. rewrite π2_𝒞...
  ext Hx.
  - apply UnionAx in Hx as [p [Hp Hx]].
    apply ReplAx in Hp as [β [Hβ Hp]]. subst.
    assert (Hoβ: β ⋵ 𝐎𝐍). apply (ord_is_ords 𝜆)...
    rewrite R_WOₒAdd in Hx...
    apply BUnionE in Hx as [Hx|Hx];
    [apply BUnionE in Hx as [Hx|Hx]|].
    + apply BUnionI1. apply BUnionI1...
    + apply BUnionI1. apply BUnionI2.
      apply ReplAx in Hx as [p [Hp Hx]].
      apply binRelE1 in Hp as [a [Ha [b [Hb [Heq Hp]]]]].
      subst. zfc_simple. apply ReplAx. exists <a, b>.
      split; zfc_simple. apply binRelI...
      apply (ord_trans 𝜆 Ho𝜆 a β)...
      apply (ord_trans 𝜆 Ho𝜆 b β)...
    + apply BUnionI2.
      apply CProdE1 in Hx as [a [Ha [b [Hb Hx]]]].
      subst. apply CProdI...
      apply CProdE1 in Hb as [c [Hc [d [Hd Hb]]]].
      apply SingE in Hd. subst. apply CProdI...
      eapply ord_trans...
  - apply BUnionE in Hx as [Hx|Hx];
    [apply BUnionE in Hx as [Hx|Hx]|].
    + apply ReplAx in Hx as [p [Hp Hx]].
      apply binRelE1 in Hp as [a [Ha [b [Hb [Heq Hp]]]]].
      subst. zfc_simple.
      apply EmptyNE in Hne as [β Hβ].
      assert (Hoβ: β ⋵ 𝐎𝐍). apply (ord_is_ords 𝜆)...
      apply UnionAx. exists (R (WOₒAdd α β)). split.
      apply ReplAx. exists β. split... rewrite R_WOₒAdd...
      apply BUnionI1. apply BUnionI1.
      apply ReplAx. exists <a, b>. split.
      apply binRelI... zfc_simple.
    + apply ReplAx in Hx as [p [Hp Hx]].
      apply binRelE1 in Hp as [a [Ha [b [Hb [Heq Hp]]]]].
      subst. zfc_simple.
      apply UnionAx. exists (R (WOₒAdd α b⁺)). split.
      apply ReplAx. exists b⁺. split...
      apply sucord_in_limord... split... rewrite R_WOₒAdd...
      apply BUnionI1. apply BUnionI2.
      apply ReplAx. exists <a, b>. split; zfc_simple.
      apply binRelI... apply BUnionI1...
      apply ord_suc_is_ord. apply (ord_is_ords 𝜆)...
    + apply CProdE1 in Hx as [a [Ha [b [Hb Hx]]]].
      apply CProdE1 in Hb as [β [Hβ [d [Hd Hb]]]].
      apply SingE in Hd. subst.
      assert (Hoβ: β ⋵ 𝐎𝐍). apply (ord_is_ords 𝜆)...
      apply UnionAx. exists (R (WOₒAdd α β⁺)). split.
      apply ReplAx. exists β⁺. split...
      apply sucord_in_limord... split... rewrite R_WOₒAdd...
      apply BUnionI2. apply CProdI... apply CProdI...
Qed.

Theorem ordAddₜ_limit : ∀α ⋵ 𝐎𝐍, ∀𝜆 ⋵ 𝐎𝐍ˡⁱᵐ, 𝜆 ≠ ∅ →
  α + 𝜆 = sup {α + β | β ∊ 𝜆}.
Proof with eauto.
  intros α Ho 𝜆 [Ho𝜆 Heq𝜆] Hne.
  rewrite <- ord_union_𝒞...
  rewrite <- (ord_WOₒ_id α), <- (ord_WOₒ_id 𝜆) at 1...
  apply ordAddₜ_iff_woAdd.
  replace (WOₒ α + WOₒ 𝜆)%wo with (⊔(𝒞 α 𝜆)). reflexivity.
  pose proof (unionStruct_spec_intro (𝒞 α 𝜆)) as [HA HR].
  apply 𝒞_is_wos... apply 𝒞_is_ees...
  apply eq_intro; simpl.
  - unfold WoDisj_A. repeat rewrite A_WOₒ_id...
    rewrite HA. apply Unionₐ_𝒞... split...
  - unfold WoDisj, WoAdd_R, WoDisj_R, WoDisj_A. simpl.
    repeat rewrite A_WOₒ_id, R_WOₒ...
    rewrite HR. apply Unionᵣ_𝒞... split...
Qed.

End AddLimit.

Section MulLimit.

Let WOₒMul := λ α β, (WOₒ α ⋅ WOₒ β)%wo.

Local Lemma A_WOₒMul : ∀α ⋵ 𝐎𝐍, ∀β ⋵ 𝐎𝐍,
  A (WOₒMul α β) = α × β.
Proof.
  intros α Hoα β Hoβ.
  unfold WOₒMul, WoMul. simpl.
  now repeat rewrite A_WOₒ_id.
Qed.

Let BR := λ α β, BinRel (α × β) (λ p1 p2,
  (π2 p1 <ᵣ π2 p2) (MemberRel β) ∨
  (π1 p1 <ᵣ π1 p2) (MemberRel α) ∧ π2 p1 = π2 p2).

Local Lemma R_WOₒMul : ∀α ⋵ 𝐎𝐍, ∀β ⋵ 𝐎𝐍,
  R (WOₒMul α β) = BR α β.
Proof.
  intros α Hoα β Hoβ.
  unfold WOₒMul, WoMul, WoMul_R, BinRel. simpl.
  now repeat rewrite A_WOₒ_id, R_WOₒ.
Qed.

Local Lemma ord_WOₒMul : ∀α ⋵ 𝐎𝐍, ∀β ⋵ 𝐎𝐍,
  ord (WOₒMul α β) = α ⋅ β.
Proof.
  intros α Hoα β Hoβ. unfold WOₒMul.
  rewrite <- ordMulₜ_eq_ord_of_woMul.
  now repeat rewrite ord_WOₒ_id.
Qed.

Let 𝒟 := λ α 𝜆, {let S := WOₒMul α β in <A S, R S> | β ∊ 𝜆}.

Local Lemma 𝒟_is_wos : ∀α ⋵ 𝐎𝐍, ∀𝜆 ⋵ 𝐎𝐍, wos (𝒟 α 𝜆).
Proof.
  intros α Hα 𝜆 H𝜆 p Hp.
  apply ReplAx in Hp as [β [Hβ Heq]].
  exists (WOₒMul α β). congruence.
Qed.

Local Lemma WOₒMul_ees : ∀α ⋵ 𝐎𝐍, ∀β1 ⋵ 𝐎𝐍, ∀β2 ⋵ 𝐎𝐍,
  β1 ⋸ β2 → WOₒMul α β1 ⊑⊑ WOₒMul α β2.
Proof with eauto.
  intros α Hoα β1 Ho1 β2 Ho2 Hsub.
  apply ord_leq_iff_sub in Hsub...
  repeat split.
  - rewrite A_WOₒMul, A_WOₒMul... intros x Hx.
    eapply sub_mono_cprod'...
  - rewrite A_WOₒMul, R_WOₒMul, R_WOₒMul...
    ext Hx. {
      apply binRelE1 in Hx as [a [Ha [b [Hb [Hx []]]]]]; subst x;
      (apply SepI; [
        apply binRelI; [eapply sub_mono_cprod'..|]|
        apply CProdI
      ])...
      left. apply binRelE2 in H as [H1 [H2 H3]]. apply binRelI...
    } {
      apply SepE in Hx as [H1 H2].
      apply CProdE1 in H2 as [a [Ha [b [Hb Hx]]]]; subst x.
      apply binRelE3 in H1 as []; apply binRelI...
      left. apply binRelI.
      - apply CProdE0 in Ha as [_ Ha]... 
      - apply CProdE0 in Hb as [_ Hb]...
      - apply binRelE3 in H...
    }
  - intros x Hx y Hy.
    rewrite A_WOₒMul in Hx...
    rewrite A_WOₒMul, A_WOₒMul in Hy...
    rewrite R_WOₒMul...
    apply SepE in Hy as [Hy Hy'].
    apply CProdE1 in Hx as [a [Ha [b [Hb Hx]]]].
    apply CProdE1 in Hy as [c [Hc [d [Hd Hy]]]]. subst.
    apply binRelI... apply CProdI... apply CProdI...
    zfc_simple. left. apply binRelI...
    contra. apply Hy'.
    apply ord_leq_iff_not_gt in H; [|eapply ord_is_ords..]...
    apply CProdI... destruct H. eapply ord_trans... congruence.
Qed.

Local Lemma 𝒟_is_ees : ∀α ⋵ 𝐎𝐍, ∀𝜆 ⋵ 𝐎𝐍, ees (𝒟 α 𝜆).
Proof with auto.
  intros α Hα 𝜆 H𝜆 S T H1 H2.
  apply ReplAx in H1 as [β1 [Hβ1 H1]].
  apply ReplAx in H2 as [β2 [Hβ2 H2]].
  apply op_iff in H1 as [H11 H12].
  apply op_iff in H2 as [H21 H22].
  assert (HS: S = WOₒMul α β1). apply eq_intro...
  assert (HT: T = WOₒMul α β2). apply eq_intro...
  assert (Ho1: β1 ⋵ 𝐎𝐍). apply (ord_is_ords 𝜆)...
  assert (Ho2: β2 ⋵ 𝐎𝐍). apply (ord_is_ords 𝜆)...
  destruct (ord_comparability β1 Ho1 β2 Ho2);
  auto; [left|right]; rewrite HS, HT; apply WOₒMul_ees...
Qed.

Local Lemma ordsₛ_𝒟 : ∀α ⋵ 𝐎𝐍, ∀𝜆 ⋵ 𝐎𝐍,
  ordsₛ (𝒟 α 𝜆) = {α ⋅ β | β ∊ 𝜆}.
Proof with eauto.
  intros α Hoα 𝜆 Ho𝜆.
  ext Hx.
  - apply ReplAx in Hx as [p [Hp Heq]]. subst.
    apply ReplAx in Hp as [β [Hβ Heq]]. subst.
    apply ReplAx. exists β. split...
    unfold ordₛ. rewrite WOₛ_pair_id.
    rewrite ord_WOₒMul... apply (ord_is_ords 𝜆)...
  - apply ReplAx in Hx as [β [Hβ Heq]]. subst.
    apply ReplAx. exists <A (WOₒMul α β), R (WOₒMul α β)>.
    split. apply ReplAx. exists β. split...
    unfold ordₛ. rewrite WOₛ_pair_id.
    rewrite ord_WOₒMul... apply (ord_is_ords 𝜆)...
Qed.

Local Lemma ord_union_𝒟 : ∀α ⋵ 𝐎𝐍, ∀𝜆 ⋵ 𝐎𝐍,
  ord ⊔(𝒟 α 𝜆) = sup {α ⋅ β | β ∊ 𝜆}.
Proof with eauto.
  intros α Hoα 𝜆 Ho𝜆.
  replace {α ⋅ β | β ∊ 𝜆} with (ordsₛ (𝒟 α 𝜆)).
  apply ord_union_eq_sup_ordsₛ_wos.
  apply 𝒟_is_wos... apply 𝒟_is_ees...
  apply ordsₛ_𝒟...
Qed.

Local Lemma π1_𝒟 : ∀α ⋵ 𝐎𝐍, ∀𝜆 ⋵ 𝐎𝐍,
  {π1 p | p ∊ 𝒟 α 𝜆} = {A (WOₒMul α β) | β ∊ 𝜆}.
Proof with eauto.
  intros α Hoα 𝜆 Ho𝜆.
  ext Hx.
  - apply ReplAx in Hx as [p [Hp Heq]]. subst.
    apply ReplAx in Hp as [β [Hβ Heq]]. subst.
    apply ReplAx. exists β. split... zfc_simple.
  - apply ReplAx in Hx as [β [Hβ Heq]]. subst.
    apply ReplAx. exists <A (WOₒMul α β), R (WOₒMul α β)>.
    split. apply ReplAx. exists β. split... zfc_simple.
Qed.

Local Lemma π2_𝒟 : ∀α ⋵ 𝐎𝐍, ∀𝜆 ⋵ 𝐎𝐍,
  {π2 p | p ∊ 𝒟 α 𝜆} = {R (WOₒMul α β) | β ∊ 𝜆}.
Proof with eauto.
  intros α Hoα 𝜆 Ho𝜆.
  ext Hx.
  - apply ReplAx in Hx as [p [Hp Heq]]. subst.
    apply ReplAx in Hp as [β [Hβ Heq]]. subst.
    apply ReplAx. exists β. split... zfc_simple.
  - apply ReplAx in Hx as [β [Hβ Heq]]. subst.
    apply ReplAx. exists <A (WOₒMul α β), R (WOₒMul α β)>.
    split. apply ReplAx. exists β. split... zfc_simple.
Qed.

Local Lemma Unionₐ_𝒟 : ∀α ⋵ 𝐎𝐍, ∀𝜆 ⋵ 𝐎𝐍ˡⁱᵐ, 𝜆 ≠ ∅ →
  Unionₐ (𝒟 α 𝜆) = α × 𝜆.
Proof with eauto.
  intros α Ho 𝜆 [Ho𝜆 Heq𝜆] Hne.
  unfold Unionₐ. rewrite π1_𝒟...
  ext Hx.
  - apply UnionAx in Hx as [p [Hp Hx]].
    apply ReplAx in Hp as [β [Hβ Hp]]. subst.
    rewrite A_WOₒMul in Hx; [|auto|apply (ord_is_ords 𝜆)]...
    assert (β ⋵ 𝐎𝐍). eapply ord_is_ords...
    apply ord_lt_iff_psub in Hβ as [Hβ _]...
    eapply sub_mono_cprod'...
  - apply CProdE1 in Hx as [a [Ha [b [Hb Hx]]]]. subst x.
    apply UnionAx. exists (α × b⁺). split...
    apply ReplAx. exists b⁺. split.
    apply sucord_in_limord... split...
    assert (b ⋵ 𝐎𝐍). eapply ord_is_ords...
    rewrite A_WOₒMul... apply CProdI...
Qed.

Local Lemma Unionᵣ_𝒟 : ∀α ⋵ 𝐎𝐍, ∀𝜆 ⋵ 𝐎𝐍ˡⁱᵐ, 𝜆 ≠ ∅ →
  Unionᵣ (𝒟 α 𝜆) = BR α 𝜆.
Proof with eauto.
  intros α Ho 𝜆 [Ho𝜆 Heq𝜆] Hne.
  unfold Unionᵣ. rewrite π2_𝒟...
  ext Hx.
  - apply UnionAx in Hx as [p [Hp Hx]].
    apply ReplAx in Hp as [β [Hβ Hp]]. subst.
    assert (Hoβ: β ⋵ 𝐎𝐍). apply (ord_is_ords 𝜆)...
    rewrite R_WOₒMul in Hx...
    apply ord_lt_iff_psub in Hβ as [Hβ _]...
    apply binRelE1 in Hx as [a [Ha [b [Hb [Hx []]]]]]; subst x;
    (apply binRelI; [eapply sub_mono_cprod'..|])...
    left. apply binRelE2 in H as [H1 [H2 H3]]. apply binRelI...
  - apply binRelE1 in Hx as [a [Ha [b [Hb [Hx []]]]]]; subst;
    apply CProdE1 in Ha as [s [Hs [t [Ht Ha]]]]; subst a;
    apply CProdE1 in Hb as [u [Hu [v [Hc Hb]]]]; subst b; zfc_simple.
    + apply binRelE3 in H.
      apply UnionAx. exists (BR α v⁺). split.
      apply ReplAx. exists v⁺. split.
      apply sucord_in_limord... split...
      rewrite R_WOₒMul... apply ord_suc_is_ord. eapply ord_is_ords...
      apply binRelI; [apply CProdI..|zfc_simple]... apply BUnionI1...
      left. apply binRelI... apply BUnionI1...
    + destruct H as [H Heq].
      apply binRelE3 in H. subst v.
      apply UnionAx. exists (BR α t⁺). split.
      apply ReplAx. exists t⁺. split.
      apply sucord_in_limord... split...
      rewrite R_WOₒMul... apply ord_suc_is_ord. eapply ord_is_ords...
      apply binRelI; [apply CProdI..|zfc_simple]...
      right. split... apply binRelI...
Qed.

Theorem ordMulₜ_limit : ∀α ⋵ 𝐎𝐍, ∀𝜆 ⋵ 𝐎𝐍ˡⁱᵐ, 𝜆 ≠ ∅ →
  α ⋅ 𝜆 = sup {α ⋅ β | β ∊ 𝜆}.
Proof with auto.
  intros α Hoα 𝜆 [Ho𝜆 Heq𝜆] Hne.
  rewrite <- ord_union_𝒟...
  rewrite <- (ord_WOₒ_id α), <- (ord_WOₒ_id 𝜆) at 1...
  apply ordMulₜ_iff_woMul.
  replace (WOₒ α ⋅ WOₒ 𝜆)%wo with (⊔(𝒟 α 𝜆)). reflexivity.
  pose proof (unionStruct_spec_intro (𝒟 α 𝜆)) as [HA HR].
  apply 𝒟_is_wos... apply 𝒟_is_ees...
  apply eq_intro; simpl.
  - repeat rewrite A_WOₒ_id...
    rewrite HA. apply Unionₐ_𝒟... split...
  - unfold WoMul_R.
    repeat rewrite A_WOₒ_id, R_WOₒ...
    rewrite HR. apply Unionᵣ_𝒟... split...
Qed.

End MulLimit.
