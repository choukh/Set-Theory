(** Coq coding by choukh, June 2021 **)

Require Export ZFC.Lib.ChoiceFacts.

Axiom AC : ∀ 𝒜, ∅ ∉ 𝒜 →
  (∀ A B ∈ 𝒜, A ≠ B → A ∩ B = ∅) →
  ∃ C, ∀A ∈ 𝒜, ∃ x, A ∩ C = {x,}.

Theorem ac4 : AC_IV.
Proof. exact AC. Qed.

Theorem ac3 : AC_III.
Proof. apply AC_IV_to_III. apply ac4. Qed.

Theorem ac3' : AC_III'.
Proof. apply AC_III_iff_III'. apply ac3. Qed.

Theorem ac1 : AC_I.
Proof. apply AC_III_to_I. apply ac3. Qed.

Theorem ac2 : AC_II.
Proof. apply AC_I_to_II. apply ac1. Qed.
