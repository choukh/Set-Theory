(** Coq coding by choukh, Sep 2021 **)

Require Export ZFC.Elements.EST8_8.
Require Import ZFC.LargeOrdinals.GeneralEpsilon.
Import OrdinalClass 𝐎𝐍Operation.

Local Hint Resolve
  add_ran mul_ran exp_ran ordAdd_ran ordMul_ran
  preOrdExp_ran ordExp_ran ordTetL_ran : core.

(** 迭代幂次 **)
(** Tetration **)
(* adapted from https://math.stackexchange.com/a/3768438/815418 *)

Definition OrdTetR := λ α, Operation α (λ ξ, ξ ^ α).
Notation "α ^^ᴿ β" := (OrdTetR α β) (at level 25) : OrdArith_scope.

Definition OrdTet := λ α β, α ^^ᴸ β ∪ α ^^ᴿ β.
Notation "α ^^ β" := (OrdTet α β) (at level 25) : OrdArith_scope.

Theorem ordTetR_ran : ∀ α β ⋵ 𝐎𝐍, α ^^ᴿ β ⋵ 𝐎𝐍.
Proof. intros α Hα β Hβ. apply operation_operative; auto. Qed.
Local Hint Resolve ordTetR_ran : core.

Lemma ordTetL : ∀ α β ⋵ 𝐎𝐍, α ^^ᴿ β ⋸ α ^^ᴸ β → α ^^ β = α ^^ᴸ β.
Proof.
  intros α Hα β Hβ Hle. unfold OrdTet.
  rewrite ord_max_l; auto.
Qed.

Lemma ordTetR : ∀ α β ⋵ 𝐎𝐍, α ^^ᴸ β ⋸ α ^^ᴿ β → α ^^ β = α ^^ᴿ β.
Proof.
  intros α Hα β Hβ Hle. unfold OrdTet.
  rewrite ord_max_r; auto.
Qed.

Theorem ordTet_ran : ∀ α β ⋵ 𝐎𝐍, α ^^ β ⋵ 𝐎𝐍.
Proof with auto.
  intros α Hα β Hβ.
  epose proof (ord_comparability (α ^^ᴸ β) _ (α ^^ᴿ β)) as []...
  - rewrite ordTetR...
  - rewrite ordTetL...
  Unshelve. auto.
Qed.
Local Hint Resolve ordTet_ran : core.

Lemma ordTetR_0 : ∀α ⋵ 𝐎𝐍, α ^^ᴿ 0 = α.
Proof. intros α H. apply operation_0; auto. Qed.

Theorem ordTet_0 : ∀α ⋵ 𝐎𝐍, α ^^ 0 = α.
Proof with auto.
  intros α H. rewrite ordTetL, ordTetL_0...
  rewrite ordTetL_0, ordTetR_0...
Qed.

Lemma ordTetR_suc : ∀ α β ⋵ 𝐎𝐍, α ^^ᴿ β⁺ = (α ^^ᴿ β) ^ α.
Proof. intros α Hα β Hβ. apply operation_suc; auto. Qed.

Lemma ordTetR_limit : ∀α ⋵ 𝐎𝐍, continuous (OrdTetR α).
Proof. intros α Hα. apply operation_limit; auto. Qed.

Lemma ordTetR_1_r : ∀α ⋵ 𝐎𝐍, α ^^ᴿ 1 = α ^ α.
Proof.
  intros α H. rewrite pred, ordTetR_suc, ordTetR_0; auto.
Qed.

Theorem ordTet_1_r : ∀α ⋵ 𝐎𝐍, α ^^ 1 = α ^ α.
Proof with nauto.
  intros α H. rewrite ordTetL, ordTetL_1_r...
  rewrite ordTetL_1_r, ordTetR_1_r...
Qed.

(* TODO *)
