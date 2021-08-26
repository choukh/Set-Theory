(** Coq coding by choukh, Oct 2020 **)

Require Import Coq.Unicode.Utf8_core.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Mult.

Lemma eq_2n3m : ∀ n m, 2 ^ n = 3 ^ m → n = 0 ∧ m = 0.
Proof with auto.
  intros.
  destruct n. {
    rewrite Nat.pow_0_r in H.
    rewrite <- (Nat.pow_0_r 3) in H at 1.
    apply Nat.pow_inj_r in H...
  }
  destruct m. {
    rewrite Nat.pow_0_r in H.
    rewrite <- (Nat.pow_0_r 2) in H at 2.
    apply Nat.pow_inj_r in H...
  }
  assert (Hodd: Nat.odd (3 ^ S m) = true). {
    rewrite Nat.odd_pow...
  }
  rewrite <- H, Nat.odd_pow, Nat.odd_2 in Hodd...
  discriminate.
Qed.

Lemma inj_2n3m_0 : ∀ n m p q,
  p <= n → q <= m →
  2 ^ n * 3 ^ m = 2 ^ p * 3 ^ q →
  n = p ∧ m = q.
Proof with auto.
  intros * Hltn Hltm Heq.
  assert (H20: 2 ^ p ≠ 0) by (apply Nat.pow_nonzero; auto).
  assert (H30: 3 ^ q ≠ 0) by (apply Nat.pow_nonzero; auto).
  assert (Hdiv: Nat.divide (2 ^ p) (2 ^ p)). {
    exists 1; rewrite Nat.mul_1_l...
  }
  assert (Hdiv2: Nat.divide (2 ^ p) (2 ^ n)). {
    exists (2 ^ (n - p)). rewrite <- Nat.pow_add_r, Nat.sub_add...
  }
  assert (Hdiv3: Nat.divide (3 ^ q) (3 ^ m)). {
    exists (3 ^ (m - q)). rewrite <- Nat.pow_add_r, Nat.sub_add...
  }
  assert (H1: 2 ^ n * 3 ^ m / 2 ^ p = 2 ^ p * 3 ^ q / 2 ^ p) by auto.
  rewrite Nat.mul_comm, Nat.divide_div_mul_exact, Nat.mul_comm in H1...
  rewrite (Nat.mul_comm (2 ^ p)) in H1...
  rewrite Nat.divide_div_mul_exact in H1...
  rewrite Nat.div_same, Nat.mul_1_r in H1...
  assert (H2: 2 ^ n / 2 ^ p * 3 ^ m / 3 ^ q = 3 ^ q / 3 ^ q) by auto.
  rewrite Nat.div_same, Nat.divide_div_mul_exact in H2...
  apply Mult.mult_is_one in H2 as [H2 H3].
  rewrite <- Nat.pow_sub_r in H2, H3...
  rewrite <- (Nat.pow_0_r 2) in H2 at 2.
  rewrite <- (Nat.pow_0_r 3) in H3 at 2.
  apply Nat.pow_inj_r in H2... apply Nat.sub_0_le in H2.
  apply Nat.pow_inj_r in H3... apply Nat.sub_0_le in H3.
  split; apply Nat.le_antisymm...
Qed.

Lemma inj_2n3m_1 : ∀ n m p q,
  p <= n → m <= q →
  2 ^ n * 3 ^ m = 2 ^ p * 3 ^ q →
  n = p ∧ m = q.
Proof with auto.
  intros * Hltn Hltm Heq.
  assert (H20: 2 ^ p ≠ 0) by (apply Nat.pow_nonzero; auto).
  assert (H30: 3 ^ m ≠ 0) by (apply Nat.pow_nonzero; auto).
  assert (Hdiv0: Nat.divide (2 ^ p) (2 ^ p)). {
    exists 1; rewrite Nat.mul_1_l...
  }
  assert (Hdiv1: Nat.divide (3 ^ m) (3 ^ m)). {
    exists 1; rewrite Nat.mul_1_l...
  }
  assert (Hdiv2: Nat.divide (2 ^ p) (2 ^ n)). {
    exists (2 ^ (n - p)). rewrite <- Nat.pow_add_r, Nat.sub_add...
  }
  assert (Hdiv3: Nat.divide (3 ^ m) (3 ^ q)). {
    exists (3 ^ (q - m)). rewrite <- Nat.pow_add_r, Nat.sub_add...
  }
  assert (H1: 2 ^ n * 3 ^ m / 2 ^ p = 2 ^ p * 3 ^ q / 2 ^ p) by auto.
  rewrite Nat.mul_comm, Nat.divide_div_mul_exact, Nat.mul_comm in H1...
  rewrite (Nat.mul_comm (2 ^ p)) in H1...
  rewrite Nat.divide_div_mul_exact in H1...
  rewrite Nat.div_same, Nat.mul_1_r in H1...
  assert (H2: 2 ^ n / 2 ^ p * 3 ^ m / 3 ^ m = 3 ^ q / 3 ^ m) by auto.
  rewrite Nat.divide_div_mul_exact, Nat.div_same, Nat.mul_1_r in H2...
  rewrite <- Nat.pow_sub_r, <- Nat.pow_sub_r in H2...
  apply eq_2n3m in H2 as [H2 H3].
  apply Nat.sub_0_le in H2.
  apply Nat.sub_0_le in H3. split; apply Nat.le_antisymm...
Qed.

Fact inj_2n3m : ∀ n m p q,
  2 ^ n * 3 ^ m = 2 ^ p * 3 ^ q →
  n = p ∧ m = q.
Proof with auto.
  intros * Heq.
  specialize Nat.le_ge_cases with p n as [H1|H1];
  specialize Nat.le_ge_cases with q m as [H2|H2].
  - apply inj_2n3m_0...
  - apply inj_2n3m_1...
  - symmetry in Heq. apply inj_2n3m_1 in Heq as []...
  - symmetry in Heq. apply inj_2n3m_0 in Heq as []...
Qed.
