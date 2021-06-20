(** Based on "Elements of Set Theory" Chapter 8 Part 6 **)
(** Coq coding by choukh, June 2021 **)

Require Import ZFC.lib.WoStructExtension.
Require Export ZFC.EST8_5.
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
  rewrite ordSum_spec_intro; auto.
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
  rewrite ordPrd_spec_intro; auto.
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

Example ordAddₜ_1_1 : 1 + 1 = 2.
Proof. apply ordAddₜ_n_m. Qed.

Example ordAddₜ_2_3 : 2 ⋅ 3 = 6.
Proof. apply ordMulₜ_n_m. Qed.

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

Theorem ordAddₜ_ident : ∀α ⋵ 𝐎𝐍, α + 0 = α.
Proof.
  intros α Ho.
  rewrite <- (ord_WOᵒ_id α Ho), <- (ord_WOᵒ_id 0 (nat_is_ord 0)).
  rewrite ordAddₜ_eq_ord_of_woAdd.
  apply otʷ_iff_ord.
  rewrite <- otAdd_eq_ot_of_woAdd.
  apply otAdd_ident. apply ot_is_ot.
Qed.

Theorem ordAddₜ_ident' : ∀α ⋵ 𝐎𝐍, 0 + α = α.
Proof.
  intros α Ho.
  rewrite <- (ord_WOᵒ_id α Ho), <- (ord_WOᵒ_id 0 (nat_is_ord 0)).
  rewrite ordAddₜ_eq_ord_of_woAdd.
  apply otʷ_iff_ord.
  rewrite <- otAdd_eq_ot_of_woAdd.
  apply otAdd_ident'. apply ot_is_ot.
Qed.

Theorem ordMulₜ_ident : ∀α ⋵ 𝐎𝐍, α ⋅ 1 = α.
Proof.
  intros α Ho.
  rewrite <- (ord_WOᵒ_id α Ho), <- (ord_WOᵒ_id 1 (nat_is_ord 1)).
  rewrite ordMulₜ_eq_ord_of_woMul.
  apply otʷ_iff_ord.
  rewrite <- otMul_eq_ot_of_woMul.
  apply otMul_ident. apply ot_is_ot.
Qed.

Theorem ordMulₜ_ident' : ∀α ⋵ 𝐎𝐍, 1 ⋅ α = α.
Proof.
  intros α Ho.
  rewrite <- (ord_WOᵒ_id α Ho), <- (ord_WOᵒ_id 1 (nat_is_ord 1)).
  rewrite ordMulₜ_eq_ord_of_woMul.
  apply otʷ_iff_ord.
  rewrite <- otMul_eq_ot_of_woMul.
  apply otMul_ident'. apply ot_is_ot.
Qed.

Theorem ordMulₜ_0 : ∀α ⋵ 𝐎𝐍, α ⋅ 0 = 0.
Proof.
  intros α Ho.
  rewrite <- (ord_WOᵒ_id α Ho), <- (ord_WOᵒ_id 0 (nat_is_ord 0)).
  rewrite ordMulₜ_eq_ord_of_woMul.
  apply otʷ_iff_ord.
  rewrite <- otMul_eq_ot_of_woMul.
  apply otMul_0. apply ot_is_ot.
Qed.

Theorem ordMulₜ_0' : ∀α ⋵ 𝐎𝐍, 0 ⋅ α = 0.
Proof.
  intros α Ho.
  rewrite <- (ord_WOᵒ_id α Ho), <- (ord_WOᵒ_id 0 (nat_is_ord 0)).
  rewrite ordMulₜ_eq_ord_of_woMul.
  apply otʷ_iff_ord.
  rewrite <- otMul_eq_ot_of_woMul.
  apply otMul_0'. apply ot_is_ot.
Qed.

Theorem ordAddₜ_0 : ∀α ⋵ 𝐎𝐍, α + 0 = α.
Proof. exact ordAddₜ_ident. Qed.

Theorem ordAddₜ_suc : ∀ α β ⋵ 𝐎𝐍, α + β⁺ = (α + β)⁺.
Proof with nauto.
  intros α Hoα β Hoβ.
  rewrite <- ordAddₜ_1, <- ordAddₜ_1...
  rewrite ordAddₜ_assoc... apply ordAddₜ_ran...
Qed.

Theorem ordAddₜ_limit : ∀α ⋵ 𝐎𝐍, ∀𝜆 ⋵ 𝐎𝐍ˡⁱᵐ,
  α + 𝜆 = sup{λ β, α + β | β ∊ 𝜆}.
Proof with auto.
  intros * Hoα Ho𝜆.
Admitted.

Theorem ordMulₜ_suc : ∀ α β ⋵ 𝐎𝐍, α ⋅ β⁺ = α ⋅ β + α.
Proof with nauto.
  intros α Hoα β Hoβ.
  rewrite <- ordAddₜ_1...
  rewrite ordMulₜ_distr, ordMulₜ_ident...
Qed.

Theorem ordMulₜ_limit : ∀α ⋵ 𝐎𝐍, ∀𝜆 ⋵ 𝐎𝐍ˡⁱᵐ,
  α ⋅ 𝜆 = sup{λ β, α ⋅ β | β ∊ 𝜆}.
Proof with auto.
  intros * Hoα Ho𝜆.
Admitted.
