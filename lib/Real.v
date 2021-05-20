(** Coq coding by choukh, Aug 2020 **)

Require Export ZFC.EST5_7.
Require Import ZFC.lib.FuncFacts.

Lemma int_injective : ∀ n m : nat, Int n = Int m → n = m.
Proof with nauto.
  intros. unfold Int in H. apply int_ident in H...
  rewrite add_ident, add_ident in H...
  apply embed_injective in H...
Qed.

Lemma rat_injective : ∀ n m : nat, Rat n = Rat m → n = m.
Proof with nauto.
  intros. unfold Rat in H. apply rat_ident in H...
  rewrite intMul_ident, intMul_ident in H...
  apply int_injective...
Qed.

Lemma real_injective : ∀ n m : nat, Real n = Real m → n = m.
Proof with nauto.
  intros. apply realq_injective in H...
  apply rat_injective...
Qed.

Lemma intAddInv_injective : ∀ x y ∈ ℤ, (-x)%z = (-y)%z → x = y.
Proof with auto.
  intros x Hx y Hy Heq.
  assert ((--x)%z = (--y)%z) by congruence.
  do 2 rewrite intAddInv_double in H...
Qed.

Lemma intAddInv_bijective : Func ℤ ℤ IntAddInv : ℤ ⟺ ℤ.
Proof with auto.
  apply meta_bijection.
  - apply intAddInv_ran.
  - apply intAddInv_injective.
  - intros y Hy. exists (-y)%z. split.
    apply intAddInv_ran... apply intAddInv_double...
Qed.

Lemma ratAddInv_injective : ∀ x y ∈ ℚ, (-x)%q = (-y)%q → x = y.
Proof with auto.
  intros x Hx y Hy Heq.
  assert ((--x)%q = (--y)%q) by congruence.
  do 2 rewrite ratAddInv_double in H...
Qed.

Lemma ratAddInv_bijective : Func ℚ ℚ RatAddInv : ℚ ⟺ ℚ.
Proof with auto.
  apply meta_bijection.
  - apply ratAddInv_ran.
  - apply ratAddInv_injective.
  - intros y Hy. exists (-y)%q. split.
    apply ratAddInv_ran... apply ratAddInv_double...
Qed.

Lemma realAddInv_injective : ∀ x y ∈ ℝ, (-x)%r = (-y)%r → x = y.
Proof with auto.
  intros x Hx y Hy Heq.
  assert ((--x)%r = (--y)%r) by congruence.
  do 2 rewrite realAddInv_double in H...
Qed.

Lemma realAddInv_bijective : Func ℝ ℝ RealAddInv : ℝ ⟺ ℝ.
Proof with auto.
  apply meta_bijection.
  - apply realAddInv_ran.
  - apply realAddInv_injective.
  - intros y Hy. exists (-y)%r. split.
    apply realAddInv_ran... apply realAddInv_double...
Qed.

Lemma rat_lt : ∀ n m ∈ ω, n ∈ m → Rat n <𝐪 Rat m.
Proof with nauto.
  intros n Hn m Hm Hnm.
  apply ratLt... rewrite intMul_ident, intMul_ident...
  apply intLt... rewrite add_ident, add_ident...
  rewrite embed_proj_id, embed_proj_id...
Qed.
