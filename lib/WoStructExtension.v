(** Coq coding by choukh, June 2021 **)

Require Import ZFC.lib.FuncFacts.
Require Import ZFC.lib.Ordinal.
Import WoStruct.
Import WoStruct.EpsilonImage.

Definition wos_spec := λ p S, p = <A S, R S>.

Lemma wos_unique : ∀ p, uniqueness (wos_spec p).
Proof.
  intros p S T H1 H2. unfold wos_spec in *. subst.
  apply op_iff in H2 as []. apply eq_intro; auto.
Qed.

(* 从良序集到良序结构 *)
Definition WOₛ := λ p, iota (inhabits ø̃) (wos_spec p).

Lemma wos_spec_intro : ∀ p, (∃ S, wos_spec p S) → wos_spec p (WOₛ p).
Proof.
  intros p [S H].
  apply (iota_spec (inhabits ø̃) (wos_spec p)).
  rewrite <- unique_existence. split.
  exists S. apply H. apply wos_unique.
Qed.

Lemma wos_pair_id : ∀ S, WOₛ <A S, R S> = S.
Proof.
  intros. pose proof (wos_spec_intro <A S, R S>).
  apply op_iff in H as [HA HR].
  apply eq_intro; auto. exists S. reflexivity.
Qed.

(* 良序结构集 well-ordered structures *)
Definition woss := λ 𝒞, ∀p ∈ 𝒞, ∃ S, wos_spec p S.

Lemma wos_spec_intro_for_woss :
  ∀ 𝒞, woss 𝒞 → ∀p ∈ 𝒞, wos_spec p (WOₛ p).
Proof.
  intros 𝒞 Hwoss p Hp.
  apply (iota_spec (inhabits ø̃) (wos_spec p)).
  rewrite <- unique_existence. split.
  apply Hwoss. auto. apply wos_unique.
Qed.

(* 从良序集到序数*)
Definition ordₛ := λ p, ord (WOₛ p).
(* 从良序结构集到序数集 *)
Definition ords := λ 𝒞, {ordₛ | p ∊ 𝒞}.

(* 从良序集到伊普西隆映射 *)
Definition Eₛ := λ p, E (WOₛ p).
(* 从良序结构集到伊普西隆映射集 *)
Definition Es := λ 𝒞, {Eₛ | p ∊ 𝒞}.

(* 尾扩张 *)
Definition EndExtension := λ S T, S ⊑ T ∧
  ∀a ∈ A S, ∀b ∈ A T - A S, (a <ᵣ b) (R T).
Notation "S ⊑⊑ T" := (EndExtension S T) (at level 70) : WoStruct_scope.

(* 尾扩张结构集 end extension structures *)
Definition eess := λ 𝒞, ∀ S T,
  <A S, R S> ∈ 𝒞 → <A T, R T> ∈ 𝒞 → S ⊑⊑ T ∨ T ⊑⊑ S.

Lemma es_is_chain : ∀ 𝒞, woss 𝒞 → eess 𝒞 → is_chain (Es 𝒞).
Admitted.

(* Lemma foo : ∀ 𝒞, woss 𝒞 → eess 𝒞 → ⋃(Es 𝒞) *)

(* 良序结构集的并 *)
Definition Union_A := λ 𝒞, ⋃{π1 | p ∊ 𝒞}.
Definition Union_R := λ 𝒞, ⋃{π2 | p ∊ 𝒞}.

(* 良序结构尾扩张集的并是良序结构 *)
Lemma union_is_woset : ∀ 𝒞, woss 𝒞 → eess 𝒞 →
  woset (Union_A 𝒞) (Union_R 𝒞).
Proof with auto.
  intros 𝒞 Hwoss Heess.
Admitted.

Definition unionStruct_spec := λ 𝒞 S,
  A S = Union_A 𝒞 ∧ R S = Union_R 𝒞.

Lemma unionStruct_exists : ∀ 𝒞, woss 𝒞 → eess 𝒞 →
  ∃! S, unionStruct_spec 𝒞 S.
Proof.
  intros 𝒞 Hwoss Heess.
  pose proof (union_is_woset 𝒞 Hwoss Heess) as Hwo.
  rewrite <- unique_existence. split.
  - exists (constr (Union_A 𝒞) (Union_R 𝒞) Hwo). split; auto.
  - intros S T [H11 H12] [H21 H22].
    apply eq_intro; congruence.
Qed.

(* 结构并 *)
Definition UnionStruct :=
  λ 𝒞, iota (inhabits ø̃) (unionStruct_spec 𝒞).
Notation "⊔ 𝒞" := (UnionStruct 𝒞) (at level 9, format "⊔ 𝒞") : WoStruct_scope.

Lemma unionStruct_spec_intro : ∀ 𝒞, woss 𝒞 → eess 𝒞 →
  unionStruct_spec 𝒞 ⊔𝒞.
Proof.
  intros 𝒞 Hwoss Heess.
  apply (iota_spec (inhabits ø̃) (unionStruct_spec 𝒞)).
  apply unionStruct_exists; auto.
Qed.

(* 良序结构尾扩张集𝒞的并的序数等于𝒞对应序数集的上确界 *)
Lemma ord_of_union_eq_union_of_ord : ∀ 𝒞,
  woss 𝒞 → eess 𝒞 → ord ⊔𝒞 = sup (ords 𝒞).
Admitted.
