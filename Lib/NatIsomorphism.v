(** Coq coding by choukh, Oct 2020 **)

Require Import Coq.Arith.PeanoNat.
Require Import ZFC.Lib.Natural.

Lemma suc_isomorphic_n : ∀ n : nat, S n = n⁺.
Proof.
  intros. rewrite <- (proj_embed_id (S n)). reflexivity.
Qed.

Lemma suc_isomorphic_ω : ∀ n : set, n ∈ ω → n⁺ = S n.
Proof with auto.
  intros n Hn. rewrite suc_isomorphic_n.
  repeat rewrite embed_proj_id... apply ω_inductive...
Qed.

Lemma add_isomorphic_n : ∀ n m, (n + m)%nat = n + m.
Proof with nauto.
  intros. induction m.
  - rewrite Nat.add_0_r, add_0_r, proj_embed_id...
  - assert (Hmw: m⁺ ∈ ω) by (apply ω_inductive; nauto).
    assert (Hnm: n + m ∈ ω) by (apply add_ran; nauto).
    rewrite Nat.add_succ_r, (suc_isomorphic_n m), embed_proj_id...
    rewrite suc, <- add_assoc, <- suc...
    rewrite suc_isomorphic_ω, IHm, proj_embed_id...
Qed.

Lemma add_isomorphic_ω : ∀ n m ∈ ω, n + m = (n + m)%nat.
Proof with nauto.
  intros n Hn m Hm. rewrite add_isomorphic_n.
  repeat rewrite embed_proj_id... apply add_ran...
Qed.

Lemma mul_isomorphic_n : ∀ n m, n * m = n ⋅ m.
Proof with nauto.
  intros. induction m.
  - rewrite Nat.mul_0_r, mul_0_r, proj_embed_id...
  - assert (Hmw: m⁺ ∈ ω) by (apply ω_inductive; nauto).
    assert (Hnm: n ⋅ m ∈ ω) by (apply mul_ran; nauto).
    rewrite Nat.mul_succ_r, (suc_isomorphic_n m), embed_proj_id...
    rewrite mul_suc, add_comm, IHm...
    rewrite add_isomorphic_n, embed_proj_id...
Qed.

Lemma mul_isomorphic_ω : ∀ n m ∈ ω, n ⋅ m = n * m.
Proof with nauto.
  intros n Hn m Hm. rewrite mul_isomorphic_n.
  repeat rewrite embed_proj_id... apply mul_ran...
Qed.

Lemma pow_isomorphic_n : ∀ n m, (n ^ m)%nat = n ^ m.
Proof with nauto.
  intros. induction m.
  - rewrite Nat.pow_0_r, exp_0_r, proj_embed_id...
  - assert (Hmw: m⁺ ∈ ω) by (apply ω_inductive; nauto).
    assert (Hnm: n ^ m ∈ ω) by (apply exp_ran; nauto).
    rewrite Nat.pow_succ_r', (suc_isomorphic_n m), embed_proj_id...
    rewrite exp_suc, IHm...
    rewrite mul_isomorphic_n, embed_proj_id...
Qed.

Lemma pow_isomorphic_ω : ∀ n m ∈ ω, n ^ m = (n ^ m)%nat.
Proof with nauto.
  intros n Hn m Hm. rewrite pow_isomorphic_n.
  repeat rewrite embed_proj_id... apply exp_ran...
Qed.

Lemma le_isomorphic : ∀ n m, n <= m ↔ n ⊆ m.
Proof with nauto.
  split; intros.
  - induction m.
    + intros. apply Le.le_n_0_eq in H. subst...
    + intros. apply PeanoNat.Nat.le_succ_r in H as []; [|subst]...
      eapply sub_tran... rewrite suc_isomorphic_n, embed_proj_id.
      intros x Hx. apply BUnionI1... apply ω_inductive...
  - rename m into k. pose proof (embed_ran k) as Hk.
    rewrite <- (proj_embed_id k).
    generalize dependent n.
    set (Embed k) as k'. fold k' in Hk.
    ω_induction k'; intros n Hn.
    + apply sub_empty in Hn.
      rewrite <- Hn, proj_embed_id...
    + assert (Hmw: m⁺ ∈ ω) by (apply ω_inductive; auto).
      apply leq_iff_sub in Hn as []...
      * apply lt_suc_iff_sub in H... apply IH in H.
        rewrite suc_isomorphic_ω, proj_embed_id...
      * rewrite <- H, proj_embed_id...
Qed.

Definition halve : set → set := λ n, (n / 2)%nat.
Notation "½ n" := (halve n) (at level 7, format "½ n") : omega_scope.

Lemma halve_ran : ∀n ∈ ω, ½n ∈ ω.
Proof. intros n Hn. apply embed_ran. Qed.

Lemma halve_even : ∀n ∈ ω, ½(2 ⋅ n) = n.
Proof with nauto.
  intros n Hn. unfold halve.
  rewrite mul_comm, mul_isomorphic_ω...
  rewrite (proj_embed_id (n * Embed 2)), (proj_embed_id 2).
  rewrite Nat.div_mul, embed_proj_id...
Qed.

Lemma even_halve : ∀n ∈ ω, even n → 2 ⋅ ½n = n.
Proof with auto.
  intros n Hn [k [Hk Heq]]. subst.
  repeat f_equal. apply halve_even...
Qed.

Lemma halve_odd : ∀n ∈ ω, ½(2 ⋅ n + 1) = n.
Proof with nauto.
  intros n Hn. unfold halve.
  rewrite mul_comm, mul_isomorphic_ω, add_isomorphic_ω...
  rewrite (proj_embed_id (n * Embed 2)), (proj_embed_id 2).
  rewrite (proj_embed_id (n * 2 + Embed 1)), (proj_embed_id 1).
  rewrite Nat.div_add_l, Nat.div_1_l...
  rewrite Nat.add_0_r, embed_proj_id...
Qed.

Lemma odd_halve : ∀n ∈ ω, odd n → 2 ⋅ ½n + 1 = n.
Proof with auto.
  intros n Hn [k [Hk Heq]]. subst.
  repeat f_equal. apply halve_odd...
Qed.

Lemma odd_halve_suc : ∀n ∈ ω, odd n → ½n⁺ = (½n)⁺.
Proof with nauto.
  intros n Hn H.
  assert (Hh: ½n ∈ ω). apply halve_ran...
  assert (Hnp: n⁺ ∈ ω). apply ω_inductive...
  assert (Hprd: 2 ⋅ ½n ∈ ω). apply mul_ran...
  cut (2 ⋅ ½n⁺ = 2 ⋅ (½n)⁺). {
    apply mul_cancel'... apply halve_ran...
    apply ω_inductive... apply suc_neq_0.
  }
  rewrite even_halve, mul_suc, add_comm...
  rewrite <- add_1_1 at 2.
  rewrite <- add_assoc, odd_halve, suc...
  apply odd_iff_suc_even...
Qed.

Lemma even_halve_suc : ∀n ∈ ω, even n → ½n⁺ = ½n.
Proof with nauto.
  intros n Hn H.
  assert (Hh: ½n ∈ ω). apply halve_ran...
  assert (Hnp: n⁺ ∈ ω). apply ω_inductive...
  assert (Hprd: 2 ⋅ ½n ∈ ω). apply mul_ran...
  cut (2 ⋅ ½n⁺ = 2 ⋅ ½n). {
    apply mul_cancel'... apply halve_ran... apply suc_neq_0.
  }
  rewrite (even_halve n)...
  cut (2 ⋅ ½n⁺ + 1 = n + 1). {
    apply add_cancel... apply mul_ran... apply halve_ran...
  }
  rewrite odd_halve, suc...
  apply even_iff_suc_odd...
Qed.
