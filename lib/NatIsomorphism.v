(** Coq coding by choukh, Oct 2020 **)

Require Import ZFC.lib.Natural.

Lemma Suc_isomorphic_1 : ∀ n : nat, S n = 「n⁺」.
Proof.
  intros. rewrite <- (embed_proj_id (S n)). reflexivity.
Qed.

Lemma Suc_isomorphic_2 : ∀n ∈ ω, n⁺ = S「n」.
Proof.
  intros n Hn. rewrite <- (proj_embed_id n) at 1.
  reflexivity. apply Hn.
Qed.

Lemma Le_isomorphic : ∀ n m, n <= m ↔ n ⊆ m.
Proof with nauto.
  split; intros.
  - induction m.
    + intros. apply Le.le_n_0_eq in H. subst...
    + intros. apply PeanoNat.Nat.le_succ_r in H as []; [|subst]...
      eapply sub_tran... rewrite Suc_isomorphic_1, proj_embed_id.
      intros x Hx. apply BUnionI1...
      apply ω_inductive. apply embed_ran.
  - rename m into k. pose proof (embed_ran k) as Hk.
    rewrite <- (embed_proj_id k).
    generalize dependent n.
    set {k ∊ ω | λ k, ∀ n : nat, n ⊆ k → n <=「k」} as N.
    ω_induction N Hk; intros n Hn.
    + apply sub_empty in Hn.
      rewrite <- Hn, embed_proj_id...
    + assert (Hmw: m⁺ ∈ ω) by (apply ω_inductive; auto).
      apply leq_iff_sub in Hn as []...
      * apply lt_suc_iff_sub in H... apply IH in H.
        rewrite Suc_isomorphic_2, embed_proj_id...
      * rewrite <- H, embed_proj_id...
Qed.