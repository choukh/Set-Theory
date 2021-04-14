(** Coq coding by choukh, Oct 2020 **)

Require Import Coq.Arith.PeanoNat.
Require Import ZFC.lib.Natural.

Lemma suc_isomorphic_n : ∀ n : nat, S n = n⁺.
Proof.
  intros. rewrite <- (proj_embed_id (S n)). reflexivity.
Qed.

Lemma suc_isomorphic_ω : ∀n ∈ ω, n⁺ = S n.
Proof with auto.
  intros n Hn. rewrite suc_isomorphic_n.
  repeat rewrite embed_proj_id... apply ω_inductive...
Qed.

Lemma add_isomorphic_n : ∀ n m, (n + m)%nat = n + m.
Proof with nauto.
  intros. induction m.
  - rewrite Nat.add_0_r, add_ident, proj_embed_id...
  - assert (Hmw: m⁺ ∈ ω) by (apply ω_inductive; nauto).
    assert (Hnm: n + m ∈ ω) by (apply add_ran; nauto).
    rewrite Nat.add_succ_r, (suc_isomorphic_n m), embed_proj_id...
    rewrite add_suc, <- add_assoc, <- add_suc...
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
    rewrite mul_m_n, add_comm, IHm...
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
    rewrite exp_m_n, IHm...
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
    set {k ∊ ω | λ k, ∀ n : nat, n ⊆ k → n <= k} as N.
    ω_induction N Hk; intros n Hn.
    + apply sub_empty in Hn.
      rewrite <- Hn, proj_embed_id...
    + assert (Hmw: m⁺ ∈ ω) by (apply ω_inductive; auto).
      apply leq_iff_sub in Hn as []...
      * apply lt_suc_iff_sub in H... apply IH in H.
        rewrite suc_isomorphic_ω, proj_embed_id...
      * rewrite <- H, proj_embed_id...
Qed.
