(** Based on "Elements of Set Theory" Chapter 7 Part 5 **)
(** Coq coding by choukh, Jan 2021 **)

Require Export ZFC.EST7_4.
Require Import ZFC.lib.Dominate.

(*** EST第七章5：哈托格斯定理，良序定理 ***)

Theorem Hartogs' : ∀ A, ∃ α, is_ord α ∧ ¬ α ≼ A ∧
  ∀ β, is_ord β → ¬ β ≼ A → α ≤ β.
Proof with auto.
  intros.
  set {B ∊ 𝒫 A | λ B, ∃ R, woset B R} as W.
Admitted.
