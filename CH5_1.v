(** Solutions to "Elements of Set Theory" Chapter 5 Part 1 **)
(** Coq coding by choukh, June 2020 **)

Require Export ZFC.EST5_4.

Local Ltac nz := try (apply nzInt; assumption).
Local Ltac mr := apply intMul_ran; auto.
Local Ltac amr := apply intAdd_ran; apply intMul_ran; auto.
Local Ltac nzmr := apply nzIntMul_ranI; auto.

(* ch5_4 see EST5_1 Theorem intAdd_assoc *)
(* ch5_5 see EST5_1 Definition IntInv *)
(* ch5_6 see EST5_2 Lemma intMul_a_0 *)
(* ch5_7 see EST5_2 Lemma int_eq_mul_inv_0, 1 *)
(* ch5_8 see EST5_2 Theorem ω_embed_add, mul, lt *)
(* ch5_9 see EST5_2 Theorem ω_embed_subtr *)
(* ch5_10 see EST5_3 Lemma ratMul_0_l *)

Example ch5_11: ∀ r s ∈ ℚ,
  r ⋅ s = Rat 0 → r = Rat 0 ∨ s = Rat 0.
Proof with auto.
  intros r Hr s Hs H.
  apply pQuotE in Hr as [a [Ha [b [Hb Hr]]]].
  apply pQuotE in Hs as [c [Hc [d [Hd Hs]]]].
  subst r s. rewrite ratMul_a_b_c_d in H...
  apply rat_ident in H; auto; [|mr|nzmr]...
  rewrite intMul_ident, intMul_0_l in H; [|mr;nz..].
  apply int_no_0_div in H as []; subst; auto; [left|right];
    apply rat_ident; auto; rewrite intMul_0_l, intMul_0_l; nz...
Qed.

Example ch5_12: ∀r ∈ ℚ, ratNeg r ↔ ratPos (-r).
Proof with auto.
  intros r Hr. split. apply rat_neg_pos. intros Hp.
  apply pQuotE in Hr as [a [Ha [b [Hb Hr]]]]. subst r.
  rewrite ratAddInv in Hp... apply rat_pos_neg in Hp.
  rewrite ratAddInv in Hp... rewrite intAddInv_double in Hp...
  apply intAddInv_in_int...
Qed.

Close Scope Rat_scope.
Open Scope Int_scope.

Example ch5_13: ∀ a b c ∈ ℤ, a + c = b + c → a = b.
Proof with eauto.
  intros a Ha b Hb c Hc Heq.
  assert (a + c - c = b + c - c) by congruence.
  rewrite (intAdd_assoc a), (intAdd_assoc b) in H...
  rewrite intAdd_inv, intAdd_ident, intAdd_ident in H...
  apply intAddInv_in_int... apply intAddInv_in_int...
Qed.

Close Scope Int_scope.
Open Scope Nat_scope.

Lemma add_1_1 : 1 + 1 = 2.
Proof with auto.
  rewrite Pred, add_m_n, add_m_n', add_0_r...
Qed.

Lemma mul_2_l : ∀m ∈ ω, 2 ⋅ m = m + m.
Proof with auto.
  intros n Hn.
  assert (Hw2: 2 ∈ ω) by (apply ω_inductive; auto).
  set {n ∊ ω | λ n, 2 ⋅ n = n + n} as N.
  ω_induction N Hn.
  - rewrite mul_0_r, add_0_r...
  - rewrite mul_m_n, IH...
    assert (Hmm: m + m ∈ ω) by (apply add_ran; auto).
    rewrite add_m_n, add_m_n', suc_eq_add_1, suc_eq_add_1...
    rewrite (add_assoc (m + m)), (add_comm 2), add_1_1...
    apply ω_inductive... apply ω_inductive...
Qed.

Close Scope Nat_scope.
Open Scope Int_scope.

Lemma intMul_2_a : ∀a ∈ ℤ, Int 2 ⋅ a = a + a.
Proof with auto.
  intros a Ha. unfold Int.
  assert (Hw2: 2 ∈ ω) by (apply ω_inductive; auto).
  apply pQuotE in Ha as [m [Hm [n [Hn Ha]]]]. subst a.
  rewrite intMul_m_n_p_q, intAdd_m_n_p_q...
  rewrite mul_0_l, mul_0_l, add_0_r, add_0_r...
  rewrite mul_2_l, mul_2_l...
  apply mul_ran... apply mul_ran...
Qed.

Example ch5_14: ∀ p s ∈ ℚ, p <𝐪 s → ∃r ∈ ℚ, p <𝐪 r ∧ r <𝐪 s.
Proof with eauto.
  intros p Hp s Hs Hlt.
  assert (H2w: 2 ∈ ω) by (apply ω_inductive; auto).
  assert (H2z': Int 2 ∈ ℤ'). {
    apply nzIntI. apply pQuotI...
    intros Heq. apply int_ident in Heq...
    rewrite add_0_r, add_0_r in Heq... eapply S_neq_0...
  }
  assert (H2z: Int 2 ∈ ℤ) by nz.
  assert (Hp2: intPos (Int 2)). {
    apply intLt... rewrite add_0_r, add_0_r... apply empty_in_s...
  }
  apply pQuotE_ratPosDenom in Hp as [a [Ha [b [Hb [Hp Hpb]]]]].
  apply pQuotE_ratPosDenom in Hs as [c [Hc [d [Hd [Hs Hpd]]]]].
  subst p s. apply ratLt in Hlt...
  exists ([<a⋅d + c⋅b, Int 2 ⋅ b ⋅ d>]~). split.
  apply pQuotI; [amr;nz|nzmr; nzmr].
  assert (Hpp: intPos ((Int 2 ⋅ b) ⋅ d)). {
    apply intMul_pos_prod; nz... mr;nz.
    apply intMul_pos_prod; nz...
  }
  split; (apply ratLt; auto; [amr;nz|nzmr; nzmr|]).
  rewrite
    <- (intMul_assoc a), <- (intMul_assoc a), (intMul_comm a),
    (intMul_assoc (Int 2)), (intMul_assoc (Int 2)),
    (intMul_assoc a), (intMul_comm b), <- (intMul_assoc a),
    (intAdd_comm (a⋅d)), intMul_distr', intMul_2_a;
    nz; auto; [|mr;nz..]; [|mr;nz].
  apply int_ineq_both_side_add; revgoals; [|mr;[mr;nz|nz]..].
  apply int_ineq_both_side_mul; nz; auto; mr; nz.
  rewrite
    <- (intMul_assoc c), <- (intMul_assoc c),
    (intMul_comm c Hc (Int 2)),
    (intMul_assoc (Int 2)), (intMul_assoc (Int 2)),
    intMul_distr', intMul_2_a; nz; auto; [|mr;nz..]; [|mr;nz].
  apply int_ineq_both_side_add; revgoals; [|mr;[mr;nz|nz]..].
  apply int_ineq_both_side_mul; nz; auto; mr; nz.
Qed.
