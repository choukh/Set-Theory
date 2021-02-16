(** Coq coding by choukh, Feb 2021 **)

Require Export ZFC.EST8_1.

Section EX8_1_and_2.
Import 𝐎𝐍NormalOperation.

Definition t := Operation 5 Suc.

Example ex8_2_a : ∀α ∈ ω, t α = 5 + α.
Proof with auto.
  intros α Hα.
Admitted.

Example ex8_2_b : ∀ α, is_ord α → ω ⋸ α → t α = α.
Proof with auto.
  intros α Hoα Hle.
Admitted.

End EX8_1_and_2.
