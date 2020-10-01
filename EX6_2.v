(** Solutions to "Elements of Set Theory" Chapter 6 Part 2 **)
(** Coq coding by choukh, Sep 2020 **)

Require Export ZFC.EST6_4.

(* 所有集合的支配集不能构成一个集合 *)
Example ex6_15 : ¬∃ 𝒜, ∀ B, ∃A ∈ 𝒜, B ≼ A.
Proof with eauto.
  intros [𝒜 H].
  specialize H with (𝒫 ⋃𝒜) as [A [H1 H2]].
  apply union_dominate in H1.
  assert (𝒫 ⋃𝒜 ≼ ⋃𝒜) by (eapply dominate_tran; eauto).
  apply cardLeq_iff in H. rewrite card_of_power in H.
  destruct (cardLt_power (|⋃𝒜|)) as [H3 H4]...
  apply H4. eapply cardLeq_asym...
Qed.

Example ex6_16_1 : ∀ A, A ≼ A ⟶ 2.
Proof with neauto; try congruence.
  intros.
  set (λ x y : set, match (ixm (x = y)) with
    | inl _ => Embed 0
    | inr _ => Embed 1
  end) as ℱ.
  set (Func A (A ⟶ 2) (λ x, Func A 2 (ℱ x))) as F.
  assert (HF: ∀x ∈ A, Func A 2 (ℱ x): A ⇒ 2). {
    intros x Hx. apply meta_maps_into. intros y Hy.
    unfold ℱ. destruct (ixm (x = y))...
    apply suc_has_0; apply ω_inductive... apply suc_has_n.
  }
  exists F. apply meta_injective.
  - intros x Hx. apply SepI.
    + apply PowerAx. intros f Hf. apply SepE in Hf as []...
    + apply HF...
  - intros x1 H1 x2 H2 Heq.
    assert ((Func A 2 (ℱ x1))[x1] = (Func A 2 (ℱ x2))[x1]) by congruence.
    rewrite meta_func_ap, meta_func_ap in H...
    unfold ℱ in H. destruct (ixm (x1 = x1))...
    destruct (ixm (x2 = x1))... exfalso. eapply suc_neq_0...
    apply HF... apply HF...
Qed.

Example ex6_16_2 : ∀ A, A ≉ A ⟶ 2.
Proof with neauto; try congruence.
  intros A [F [[Hf Hs] [Hd Hr]]].
  set (Func A 2 (λ x, match (ixm (F[x][x] = 0)) with
    | inl _ => 1
    | inr _ => 0
  end)) as g.
  assert (Hgf: g: A ⇒ 2). {
    apply meta_maps_into. intros x Hx.
    destruct (ixm (F[x][x] = 0)). apply suc_has_n.
    apply suc_has_0; apply ω_inductive...
  }
  assert (Hg: g ∈ A ⟶ 2). {
    apply SepI... apply PowerAx.
    intros p Hp. apply SepE in Hp as []...
  }
  rewrite <- Hr in Hg. apply ranE in Hg as [x Hp].
  apply domI in Hp as Hx. apply func_ap in Hp...
  assert (F[x][x] = g[x]) by congruence.
  unfold g in H. rewrite meta_func_ap in H...
  destruct (ixm (F[x][x] = 0))...
  rewrite e in H. eapply suc_neq_0...
Qed.

Example ex6_17_a : Embed 0 <𝐜 ℵ₀ ∧ 0 + ℵ₀ = ℵ₀ + ℵ₀.
Proof with nauto.
  split. apply cardLt_nat_aleph0...
  rewrite cardAdd_comm, cardAdd_ident, cardAdd_aleph0_aleph0...
Qed.

Example ex6_17_b : Embed 1 <𝐜 2 ^ ℵ₀ ∧ 1 ⋅ 2 ^ ℵ₀ = 2 ^ ℵ₀ ⋅ 2 ^ ℵ₀.
Proof with nauto.
  split. eapply cardLeq_lt_tran.
  apply cardLt_nat_aleph0... apply cardLt_power...
  rewrite cardMul_comm, cardMul_ident, cardMul_2aleph0_2aleph0...
Qed.

Example ex6_17_c : Embed 1 <𝐜 Embed 2 ∧ 1 ^ 0 = 2 ^ 0.
Proof with nauto.
  split. apply fin_cardLt_iff_lt... apply suc_has_n...
  rewrite cardExp_0_r, cardExp_0_r...
Qed.

Example ex6_17_d : Embed 1 <𝐜 Embed 2 ∧ 0 ^ 1 = 0 ^ 2.
Proof with nauto.
  split. apply fin_cardLt_iff_lt... apply suc_has_n...
  rewrite cardExp_0_l, cardExp_0_l...
  apply suc_neq_0. apply suc_neq_0.
Qed.


