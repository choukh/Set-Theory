(** Adapted from "Elements of Set Theory" Chapter 5 **)
(** Coq coding by choukh, June 2020 **)

Require Export ZFC.Elements.EST5_1.
Require Import ZFC.Lib.FuncFacts.

Local Ltac mr := apply mul_ran; auto.
Local Ltac ar := apply add_ran; auto.
Local Ltac amr := apply add_ran; apply mul_ran; auto.

(*** EST第五章2：整数乘法，整数的序，自然数嵌入 ***)

Close Scope Int_scope.
Open Scope omega_scope.

Definition PreIntMul : set :=
  PlaneArith ω ω (λ m n p q, <m⋅p + n⋅q, m⋅q + n⋅p>).
Notation "a ⋅ᵥ b" := (PreIntMul[<a, b>])
  (at level 50) : PreInt_scope.

Lemma mul_split : ∀ a b ∈ ω, ∃ m n p q ∈ ω,
  a = m⋅p + n⋅q ∧ b = m⋅q + n⋅p.
Proof with try apply ω_inductive; nauto.
  intros a Ha b Hb.
  exists a. split... exists b. split...
  exists 1. split... exists 0. split...
  repeat rewrite mul_1_r, mul_0_r...
  rewrite add_0_r, add_0_l...
Qed.

Lemma preIntMul_maps_onto : PreIntMul: (ω²)² ⟹ ω².
Proof with eauto.
  apply planeArith_maps_onto.
  - intros m Hm n Hn p Hp q Hq.
    apply CPrdI; apply add_ran; apply mul_ran...
  - intros a Ha b Hb. pose proof mul_split
      as [m [Hm [n [Hn [p [Hp [q [Hq H1]]]]]]]].
    apply Ha. apply Hb.
    exists m. split... exists n. split...
    exists p. split... exists q. split...
    apply op_iff...
Qed.

Lemma preIntMul_m_n_p_q : ∀ m n p q ∈ ω,
  <m, n> ⋅ᵥ <p, q> = <m⋅p + n⋅q, m⋅q + n⋅p>.
Proof with auto.
  intros m Hm n Hn p Hp q Hq.
  eapply func_ap. destruct preIntMul_maps_onto...
  apply SepI. apply CPrdI; apply CPrdI;
    try apply CPrdI; try apply add_ran; try apply mul_ran...
  zfc_simple...
Qed.

Lemma preIntMul_binCompatible :
  binCompatible (PlaneEquiv ω ω IntEq) ω² PreIntMul.
Proof with auto.
  split. apply intEquiv_equiv. split.
  destruct preIntMul_maps_onto as [Hf [Hd Hr]].
  split... split... rewrite Hr. apply sub_refl.
  intros x Hx y Hy u Hu v Hv H1 H2.
  apply CPrdE1 in Hx as [m [Hm [n [Hn Hxeq]]]].
  apply CPrdE1 in Hy as [p [Hp [q [Hq Hyeq]]]].
  apply CPrdE1 in Hu as [m' [Hm' [n' [Hn' Hueq]]]].
  apply CPrdE1 in Hv as [p' [Hp' [q' [Hq' Hveq]]]]. subst.
  apply planeEquiv in H1... apply planeEquiv in H2...
  rewrite preIntMul_m_n_p_q, preIntMul_m_n_p_q...
  apply SepI. apply CPrdI; apply CPrdI;
    apply add_ran; apply mul_ran... zfc_simple. simpl.
  unfold IntEq in *.
  assert (H3: (m+n')⋅p = (m'+n)⋅p) by congruence.
  rewrite mul_distr', mul_distr' in H3; [|auto..].
  assert (H4: (m'+n)⋅q = (m+n')⋅q) by congruence.
  rewrite mul_distr', mul_distr' in H4; [|auto..].
  assert (H5: m'⋅(p+q') = m'⋅(p'+q)) by congruence.
  rewrite mul_distr, mul_distr in H5; [|auto..].
  assert (H6: n'⋅(p'+q) = n'⋅(p+q')) by congruence.
  rewrite mul_distr, mul_distr in H6; [|auto..].
  rewrite (add_comm (m'⋅p)) in H3; [|mr;auto..].
  rewrite (add_comm (m'⋅p)) in H5; [|mr;auto..].
  assert (H35: m⋅p + n'⋅p + (m'⋅q' + m'⋅p) =
    n⋅p + m'⋅p + (m'⋅p' + m'⋅q)) by congruence.
  rewrite (add_comm (n⋅p + m'⋅p)) in H35; [|amr;auto..].
  rewrite <- add_assoc, <- add_assoc in H35; [|amr|mr|mr|amr|mr..].
  apply add_cancel in H35; [|ar;[amr|mr]|ar;[amr|mr]|mr].
  assert (H46: m'⋅q + n⋅q + (n'⋅p' + n'⋅q) =
               m⋅q + n'⋅q + (n'⋅p + n'⋅q')) by congruence.
  rewrite (add_comm (m⋅q + n'⋅q)) in H46; [|amr;auto..].
  rewrite <- add_assoc, <- add_assoc in H46; [|amr|mr|mr|amr|mr..].
  apply add_cancel in H46; swap 2 4; [|mr|ar;[amr|mr]..].
  rewrite (add_comm (m⋅p)), add_assoc in H35; [|mr;auto..].
  assert (H: n'⋅p + (m⋅p + m'⋅q') + (m'⋅q + n⋅q + n'⋅p') =
    m'⋅p' + m'⋅q + n⋅p + (n'⋅p + n'⋅q' + m⋅q)) by congruence.
  rewrite add_assoc in H; [|mr|amr|ar;[amr|mr]].
  rewrite (add_comm (m'⋅p' + m'⋅q + n⋅p)) in H; [|ar;[amr|mr];auto..].
  rewrite (add_assoc (n'⋅p)) in H; [|mr;auto..].
  rewrite (add_assoc (n'⋅p)) in H; [|mr|amr|ar;[amr|mr]].
  apply add_cancel' in H; swap 2 4; [|mr|ar;[ar|ar;[ar|]];mr..].
  rewrite (add_comm (m'⋅q)) in H; [|mr;auto..].
  rewrite (add_comm (n⋅q + m'⋅q)) in H; [|amr|mr].
  rewrite <- add_assoc in H; [|amr|mr|amr].
  rewrite <- add_assoc in H; [|ar;[ar|];mr|mr..].
  rewrite (add_comm (m'⋅p' + m'⋅q)) in H; [|amr|mr].
  rewrite <- add_assoc in H; [|amr|mr|amr].
  rewrite <- add_assoc in H; [|ar;[ar|];mr|mr..].
  apply add_cancel in H; swap 2 4; [|mr|ar;[ar;[ar|]|];mr..].
  rewrite add_assoc; [|mr|mr|amr].
  rewrite (add_comm (n⋅q)); [|mr|amr].
  rewrite <- add_assoc, <- add_assoc; swap 2 6; [|amr|mr..].
  rewrite (add_assoc (m'⋅p')); [|mr|mr|amr].
  rewrite (add_comm (m'⋅p')); [|mr|ar;[mr|amr]].
  rewrite <- (add_assoc (n'⋅q')); [|mr;auto..]. apply H.
Qed.

Close Scope omega_scope.
Open Scope Int_scope.

(** 整数乘法 **)
Definition IntMul : set :=
  QuotionFunc (PlaneEquiv ω ω IntEq) ω² PreIntMul.
Notation "a ⋅ b" := (IntMul[<a, b>]) : Int_scope.

Lemma intMul_maps_onto : IntMul: ℤ × ℤ ⟹ ℤ.
Proof.
  apply quotionFunc_maps_onto.
  apply preIntMul_binCompatible.
  apply preIntMul_maps_onto.
Qed.

Lemma intMul_a_b : ∀ a b ∈ ω², [a]~ ⋅ [b]~ = [a ⋅ᵥ b]~.
Proof.
  intros a Ha b Hb. apply binCompatibleE; auto.
  apply preIntMul_binCompatible.
Qed.

Global Opaque IntMul.

Lemma intMul_m_n_p_q : ∀ m n p q ∈ ω,
  [<m, n>]~ ⋅ [<p, q>]~ = ([<m⋅p + n⋅q, m⋅q + n⋅p>]~)%ω.
Proof with auto.
  intros m Hm n Hn p Hp q Hq.
  rewrite intMul_a_b, preIntMul_m_n_p_q...
  apply CPrdI... apply CPrdI...
Qed.

Lemma intMul_0_r_r : ∀a ∈ ℤ, a ⋅ Int 0 = Int 0.
Proof with nauto.
  intros a Ha.
  apply pQuotE in Ha as [m [Hm [n [Hn Ha]]]]. subst a.
  unfold Int. rewrite intMul_m_n_p_q...
  repeat rewrite mul_0_r...
  repeat rewrite add_0_r...
Qed.

Lemma intMul_ran : ∀ a b ∈ ℤ, a ⋅ b ∈ ℤ.
Proof with auto.
  intros a Ha b Hb.
  apply pQuotE in Ha as [m [Hm [n [Hn Ha]]]]. subst a.
  apply pQuotE in Hb as [p [Hp [q [Hq Hb]]]]. subst b.
  rewrite intMul_m_n_p_q...
  apply pQuotI; apply add_ran; apply mul_ran...
Qed.

Example intMul_2_n2 : Int 2 ⋅ -Int 2 = -Int 4.
Proof with nauto.
  unfold Int. rewrite intAddInv, intAddInv...
  rewrite intMul_m_n_p_q...
  rewrite mul_0_l, mul_0_r, mul_0_r, add_0_r, add_0_r...
  rewrite mul_2_2... apply mul_ran...
Qed.

Close Scope Int_scope.
Open Scope omega_scope.

Theorem intMul_comm : ∀ a b ∈ ℤ, (a ⋅ b = b ⋅ a)%z.
Proof with try assumption.
  intros a Ha b Hb.
  apply pQuotE in Ha as [m [Hm [n [Hn Ha]]]].
  apply pQuotE in Hb as [p [Hp [q [Hq Hb]]]]. subst.
  rewrite intMul_m_n_p_q, intMul_m_n_p_q...
  rewrite (mul_comm p), (mul_comm n)...
  rewrite (mul_comm m Hm q), (mul_comm n Hn p)...
  rewrite (add_comm (q⋅m)); [|apply mul_ran; auto..]. reflexivity.
Qed.

Theorem intMul_assoc : ∀ a b c ∈ ℤ, (a ⋅ b ⋅ c = a ⋅ (b ⋅ c))%z.
Proof.
  intros a Ha b Hb c Hc.
  apply pQuotE in Ha as [m [Hm [n [Hn Ha]]]].
  apply pQuotE in Hb as [p [Hp [q [Hq Hb]]]].
  apply pQuotE in Hc as [r [Hr [s [Hs Hc]]]]. subst.
  repeat rewrite intMul_m_n_p_q; [|auto;amr..].
  apply int_ident; swap 1 5; [|ar;mr;ar;mr..].
  repeat rewrite mul_distr, mul_distr'; [|auto;mr..].
  repeat rewrite <- mul_assoc; [|auto..].
  cut (∀ x1 x2 x3 x4 x5 x6 x7 x8 ∈ ω,
    x1 + x4 + (x2 + x3) + (x5 + x7 + (x8 + x6)) =
    x1 + x2 + (x3 + x4) + (x5 + x6 + (x7 + x8))).
  intros H. apply H; mr; mr.
  clear Hm Hn Hp Hq Hr Hs m n p q r s.
  intros x1 H1 x2 H2 x3 H3 x4 H4 x5 H5 x6 H6 x7 H7 x8 H8.
  rewrite (add_assoc x1), (add_comm x4); [|auto;ar;auto..].
  rewrite (add_assoc x2), <- (add_assoc x1); [|auto;ar;auto..].
  rewrite (add_assoc x5), <- (add_assoc x7); [|auto;ar;auto..].
  rewrite (add_comm (x7+x8)), (add_assoc x5); [|auto;ar;auto..].
  reflexivity.
Qed.

Theorem intMul_distr : ∀ a b c ∈ ℤ, (a ⋅ (b + c) = a ⋅ b + a ⋅ c)%z.
Proof.
  intros a Ha b Hb c Hc.
  apply pQuotE in Ha as [m [Hm [n [Hn Ha]]]].
  apply pQuotE in Hb as [p [Hp [q [Hq Hb]]]].
  apply pQuotE in Hc as [r [Hr [s [Hs Hc]]]]. subst.
  rewrite intAdd_m_n_p_q; [|auto..].
  rewrite intMul_m_n_p_q, intMul_m_n_p_q, intMul_m_n_p_q; [|auto;ar..].
  repeat rewrite intAdd_m_n_p_q; [|amr;auto..].
  apply int_ident; [ar;mr;ar|ar;mr;ar|
    ar;amr|ar;amr|].
  repeat rewrite mul_distr; [|auto..].
  cut (∀ x1 x2 x3 x4 x5 x6 x7 x8 ∈ ω,
    x1 + x3 + (x2 + x4) + (x5 + x7 + (x6 + x8)) =
    x1 + x2 + (x3 + x4) + (x5 + x6 + (x7 + x8))).
  intros H. apply H; mr; auto.
  clear Hm Hn Hp Hq Hr Hs m n p q r s.
  intros x1 H1 x2 H2 x3 H3 x4 H4 x5 H5 x6 H6 x7 H7 x8 H8.
  rewrite (add_assoc x1), <- (add_assoc x3),
    (add_comm x3), (add_assoc x2), <- (add_assoc x1);
    swap 2 4; swap 3 15; [|ar|ar|auto..].
  rewrite (add_assoc x5), <- (add_assoc x7),
    (add_comm x7), (add_assoc x6), <- (add_assoc x5);
    swap 2 4; swap 3 15; [|ar|ar|auto..].
  reflexivity.
Qed.

Theorem intMul_distr' : ∀ a b c ∈ ℤ, ((b + c) ⋅ a = b ⋅ a + c ⋅ a)%z.
Proof with auto.
  intros a Ha b Hb c Hc.
  rewrite (intMul_comm (b + c)%z), intMul_distr, intMul_comm,
    (intMul_comm c)... apply intAdd_ran...
Qed.

Theorem int_suc_neq_0 : ∀ n, Int (S n) ≠ Int 0.
Proof with neauto.
  intros n H. apply int_ident in H...
  rewrite add_0_r, add_0_r in H... eapply suc_neq_0...
Qed.
Global Hint Immediate int_suc_neq_0 : number_hint.

Theorem int_no_0_div : ∀ a b ∈ ℤ,
  (a ⋅ b = Int 0)%z → a = Int 0 ∨ b = Int 0.
Proof with nauto.
  intros a Ha b Hb Heq.
  destruct (classic (a = Int 0)) as [|H1];
  destruct (classic (b = Int 0)) as [|H2]... exfalso.
  cut ((a ⋅ b)%z ≠ Int 0). intros... clear Heq.
  apply pQuotE in Ha as [m [Hm [n [Hn Ha]]]].
  apply pQuotE in Hb as [p [Hp [q [Hq Hb]]]].
  subst a b. rewrite intMul_m_n_p_q...
  cut (m⋅p + n⋅q ≠ m⋅q + n⋅p). intros Hnq Heq. apply Hnq.
  apply int_ident in Heq; [|nauto;amr..]...
  rewrite add_0_r, add_0_l in Heq; auto; amr...
  assert (Hmn: m ≠ n). {
    intros H. apply H1. apply int_ident...
    rewrite add_0_r, add_0_l...
  }
  assert (Hpq: p ≠ q). {
    intros H. apply H2. apply int_ident...
    rewrite add_0_r, add_0_l...
  }
  clear H1 H2.
  assert (Hw: m⋅q + n⋅p ∈ ω) by (amr; auto).
  apply nat_connected in Hmn as [H1|H1];
  apply nat_connected in Hpq as [H2|H2]; auto;
  intros Heq; eapply nat_irrefl; revgoals.
  pose proof (ex4_25 m Hm n Hn p Hp q Hq H1 H2).
  rewrite Heq in H. apply H. auto.
  pose proof (ex4_25 m Hm n Hn q Hq p Hp H1 H2).
  rewrite Heq in H. apply H. auto.
  pose proof (ex4_25 n Hn m Hm p Hp q Hq H1 H2).
  rewrite add_comm, (add_comm (n⋅p)), Heq in H; [|mr;auto..]. apply H. auto.
  pose proof (ex4_25 n Hn m Hm q Hq p Hp H1 H2).
  rewrite add_comm, (add_comm (n⋅q)), Heq in H; [|mr;auto..]. apply H. auto.
Qed.

Close Scope omega_scope.
Open Scope Int_scope.

Theorem intMul_1_r : ∀a ∈ ℤ, a ⋅ Int 1 = a.
Proof with nauto.
  intros a Ha.
  apply pQuotE in Ha as [m [Hm [n [Hn Ha]]]]. subst a.
  unfold Int. rewrite intMul_m_n_p_q...
  rewrite mul_1_r, mul_1_r, mul_0_r, mul_0_r, add_0_r, add_0_l...
Qed.

Corollary intMul_1_l : ∀a ∈ ℤ, Int 1 ⋅ a = a.
Proof with nauto.
  intros a Ha. rewrite intMul_comm, intMul_1_r...
Qed.

Lemma intMul_addInv : ∀a ∈ ℤ, -Int 1 ⋅ a = -a.
Proof with nauto.
  intros a Ha.
  apply pQuotE in Ha as [m [Hm [n [Hn Ha]]]]. subst a.
  unfold Int. rewrite intAddInv, intAddInv, intMul_m_n_p_q...
  rewrite mul_0_l, mul_0_l, (mul_comm 1), (mul_comm 1)...
  rewrite mul_1_r, mul_1_r, add_0_l, add_0_l...
Qed.

Lemma intMul_0_l : ∀a ∈ ℤ, Int 0 ⋅ a = Int 0.
Proof.
  intros a Ha. rewrite intMul_comm, intMul_0_r_r; nauto.
Qed.

Lemma intMul_addInv_lr : ∀ a b ∈ ℤ, a ⋅ -b = -a ⋅ b.
Proof with auto.
  intros a Ha b Hb.
  apply pQuotE in Ha as [m [Hm [n [Hn Ha]]]]. subst a.
  apply pQuotE in Hb as [p [Hp [q [Hq Hb]]]]. subst b.
  rewrite intAddInv, intAddInv, intMul_m_n_p_q, intMul_m_n_p_q,
    add_comm, (add_comm (m⋅p)%ω); auto; mr; auto.
Qed.

Lemma intMul_addInv_r : ∀ a b ∈ ℤ, a ⋅ -b = -(a ⋅ b).
Proof with auto.
  intros a Ha b Hb.
  apply pQuotE in Ha as [m [Hm [n [Hn Ha]]]]. subst a.
  apply pQuotE in Hb as [p [Hp [q [Hq Hb]]]]. subst b.
  rewrite intAddInv, intMul_m_n_p_q, intMul_m_n_p_q, intAddInv;
    auto; amr; auto.
Qed.

Lemma intMul_addInv_l : ∀ a b ∈ ℤ, -a ⋅ b = -(a ⋅ b).
Proof with auto.
  intros a Ha b Hb.
  rewrite <- intMul_addInv_lr, intMul_addInv_r...
Qed.

Close Scope Int_scope.
Open Scope omega_scope.

(** 整数的序 **)

Lemma int_orderable : ∀ m n m' n' p q p' q',
  <m, n> ~ <m', n'> → <p, q> ~ <p', q'> →
  m + q ∈ p + n ↔ m' + q' ∈ p' + n'.
Proof.
  intros * H1 H2.
  apply planeEquivE2 in H1 as [H1 [Hm [Hn [Hm' Hn']]]].
  apply planeEquivE2 in H2 as [H2 [Hp [Hq [Hp' Hq']]]].
  assert (Hmq: m + q ∈ ω) by (ar; auto).
  assert (Hpn: p + n ∈ ω) by (ar; auto).
  assert (Hn'q': n' + q' ∈ ω) by (ar; auto).
  rewrite (add_preserve_lt _ Hmq _ Hpn _ Hn'q').
  rewrite (add_assoc m), (add_comm q), <- (add_assoc m),
  <- (add_assoc m), (add_comm n'), (add_assoc p),
    (add_comm n), <- (add_assoc p), <- (add_assoc p),
    H1, H2, (add_assoc m'), (add_comm n), <- (add_assoc m'),
    (add_assoc (m'+q')), (add_assoc p'), (add_comm q),
    <- (add_assoc p'), (add_assoc (p'+n')), (add_comm q);
    [|auto;ar;auto..].
  assert (Hm'q': m' + q' ∈ ω) by (ar; auto).
  assert (Hp'n': p' + n' ∈ ω) by (ar; auto).
  assert (Hnq: n + q ∈ ω) by (ar; auto).
  rewrite <- (add_preserve_lt _ Hm'q' _ Hp'n' _ Hnq).
  reflexivity.
Qed.

(* 整数的小于关系 *)
Definition IntLt : set := BinRel ℤ (λ a b,
  let u := IntProj a in let v := IntProj b in
  let m := π1 u in let n := π2 u in
  let p := π1 v in let q := π2 v in
  m + q ∈ p + n
).
Notation "a <𝐳 b" := (<a, b> ∈ IntLt) (at level 70).

Lemma intLtI : ∀ m n p q ∈ ω,
  m + q ∈ p + n → [<m, n>]~ <𝐳 [<p, q>]~.
Proof with auto.
  intros m Hm n Hn p Hp q Hq Hlt.
  apply binRelI. apply pQuotI... apply pQuotI...
  pose proof (intProj m Hm n Hn)
    as [m' [Hm' [n' [Hn' [H11 [H12 _]]]]]].
  pose proof (intProj p Hp q Hq)
    as [p' [Hp' [q' [Hq' [H21 [H22 _]]]]]].
  pose proof intEquiv_equiv as [_ [_ [Hsym _]]].
  rewrite H11, H21. simpl. zfc_simple. eapply int_orderable.
  apply Hsym. apply H12. apply Hsym. apply H22. apply Hlt.
Qed.

Lemma intLtE : ∀ a b, a <𝐳 b → ∃ m n p q ∈ ω,
  a = [<m, n>]~ ∧ b = [<p, q>]~ ∧ m + q ∈ p + n.
Proof with auto.
  intros a b Hlt. apply SepE in Hlt as [H1 H2].
  apply CPrdE2 in H1 as [Ha Hb]. zfc_simple.
  apply pQuotE in Ha as [m [Hm [n [Hn Ha]]]].
  apply pQuotE in Hb as [p [Hp [q [Hq Hb]]]]. subst.
  exists m. split... exists n. split...
  exists p. split... exists q. split... split... split...
  pose proof (intProj m Hm n Hn) as [r [Hr [s [Hs [H11 [H12 _]]]]]].
  pose proof (intProj p Hp q Hq) as [u [Hu [v [Hv [H21 [H22 _]]]]]].
  rewrite H11, H21 in H2. simpl in H2. zfc_simple.
  eapply int_orderable; eauto.
Qed.

Lemma intLt : ∀ m n p q ∈ ω,
  [<m, n>]~ <𝐳 [<p, q>]~ ↔ m + q ∈ p + n.
Proof.
  intros m Hm n Hn p Hp q Hq. split; intros.
  - apply SepE in H as [H1 H2].
    apply CPrdE2 in H1 as [Ha Hb]. zfc_simple.
    pose proof (intProj m Hm n Hn) as [r [Hr [s [Hs [H11 [H12 _]]]]]].
    pose proof (intProj p Hp q Hq) as [u [Hu [v [Hv [H21 [H22 _]]]]]].
    rewrite H11, H21 in H2. simpl in H2. zfc_simple.
    eapply int_orderable; eauto.
  - apply intLtI; auto.
Qed.

Lemma intNeqE : ∀ m n p q ∈ ω,
  [<m, n>]~ ≠ [<p, q>]~ → m + q ≠ p + n.
Proof with auto.
  intros m Hm n Hn p Hp q Hq Hnq Heq.
  apply Hnq. apply int_ident...
Qed.

Lemma intLt_trans : tranr IntLt.
Proof with auto.
  intros x y z H1 H2.
  assert (H1' := H1). assert (H2' := H2).
  apply intLtE in H1'
    as [m [Hm [n [Hn [p [Hp [q [Hq [Hx [Hy _]]]]]]]]]].
  apply intLtE in H2'
    as [_ [_ [_ [_ [r [Hr [s [Hs [_ [Hz _]]]]]]]]]]. subst x y z.
  apply intLt in H1... apply intLt in H2... apply intLt...
  assert (H1': m + q + s ∈ p + n + s)
    by (apply add_preserve_lt; auto; ar; auto).
  assert (H2': p + s + n ∈ r + q + n)
    by (apply add_preserve_lt; auto; ar; auto).
  rewrite (add_assoc m), (add_comm q), <- (add_assoc m),
    (add_assoc p), (add_comm n), <- (add_assoc p) in H1'...
  rewrite (add_assoc r), (add_comm q), <- (add_assoc r) in H2'...
  eapply add_preserve_lt; revgoals; swap 1 2; [apply Hq| |ar..].
  eapply nat_trans; revgoals; eauto; ar; ar.
Qed.

Lemma intLt_irrefl : irrefl IntLt.
Proof with auto.
  intros a Hlt. assert (H := Hlt). apply intLtE in H
    as [m [Hm [n [Hn [_ [_ [_ [_ [Ha _]]]]]]]]].
  subst a. apply intLt in Hlt...
  eapply nat_irrefl; revgoals. apply Hlt. ar...
Qed.

Lemma intLt_connected : connected IntLt ℤ.
Proof with auto.
  intros x Hx y Hy Hnq.
  apply pQuotE in Hx as [m [Hm [n [Hn Hx]]]].
  apply pQuotE in Hy as [p [Hp [q [Hq Hy]]]].
  subst x y. apply intNeqE in Hnq...
  apply nat_connected in Hnq as []; [| |ar;auto..].
  + left. apply intLtI...
  + right. apply intLtI...
Qed.

Lemma intLt_trich : trich IntLt ℤ.
Proof.
  eapply trich_iff. apply binRel_is_binRel.
  apply intLt_trans. split.
  apply intLt_irrefl. apply intLt_connected.
Qed.

Theorem intLt_linearOrder : linearOrder IntLt ℤ.
Proof.
  split. apply binRel_is_binRel. split.
  apply intLt_trans. apply intLt_trich.
Qed.

Close Scope omega_scope.
Open Scope Int_scope.

Definition intPos : set → Prop := λ a, Int 0 <𝐳 a.
Definition intNeg : set → Prop := λ a, a <𝐳 Int 0.

Lemma int_neq_0 : ∀a ∈ ℤ, intPos a ∨ intNeg a → a ≠ Int 0.
Proof.
  intros a Ha [Hpa|Hna]; intros H; subst;
  eapply intLt_irrefl; eauto.
Qed.

Lemma intLt_addInv : ∀ a b ∈ ℤ, a <𝐳 b ↔ -b <𝐳 -a.
Proof with auto.
  intros a Ha b Hb.
  apply pQuotE in Ha as [m [Hm [n [Hn Ha]]]].
  apply pQuotE in Hb as [p [Hp [q [Hq Hb]]]].
  subst a b. split; intros.
  - apply intLt in H...
    rewrite intAddInv, intAddInv... apply intLt...
    rewrite add_comm, (add_comm n)...
  - rewrite intAddInv, intAddInv in H... apply intLt in H...
    apply intLt... rewrite add_comm, (add_comm p)...
Qed.

Lemma intPos_neg : ∀ a, intPos a → intNeg (-a).
Proof with nauto.
  intros. assert (Ha: a ∈ ℤ). {
    apply SepE in H as [H _]. apply CPrdE2 in H as []...
  }
  apply intLt_addInv in H... rewrite intAddInv_0 in H...
Qed.

Lemma intNeg_pos : ∀ a, intNeg a → intPos (-a).
Proof with nauto.
  intros. assert (Ha: a ∈ ℤ). {
    apply SepE in H as [H _]. apply CPrdE2 in H as []...
  }
  apply intLt_addInv in H... rewrite intAddInv_0 in H...
Qed.

Close Scope Int_scope.
Open Scope omega_scope.

Theorem intAdd_preserve_lt : ∀ a b c ∈ ℤ,
  a <𝐳 b ↔ (a + c <𝐳 b + c)%z.
Proof with auto.
  intros a Ha b Hb c Hc.
  apply pQuotE in Ha as [m [Hm [n [Hn Ha]]]]. subst a.
  apply pQuotE in Hb as [p [Hp [q [Hq Hb]]]]. subst b.
  apply pQuotE in Hc as [r [Hr [s [Hs Hc]]]]. subst c.
  rewrite (intLt m Hm n Hn p Hp q Hq).
  rewrite intAdd_m_n_p_q, intAdd_m_n_p_q...
  assert (Hw1: m + r ∈ ω) by (ar; auto).
  assert (Hw2: n + s ∈ ω) by (ar; auto).
  assert (Hw3: p + r ∈ ω) by (ar; auto).
  assert (Hw4: q + s ∈ ω) by (ar; auto).
  rewrite (intLt (m+r) Hw1 (n+s) Hw2 (p+r) Hw3 (q+s) Hw4).
  rewrite (add_assoc m), <- (add_assoc r), (add_comm r),
    (add_assoc q), <- (add_assoc m),
    (add_assoc p), <- (add_assoc r), (add_comm r Hr n Hn),
    (add_assoc n), <- (add_assoc p); [|auto;ar;auto..].
  apply add_preserve_lt; ar...
Qed.

Theorem intMul_preserve_lt : ∀ a b c ∈ ℤ,
  intPos c → a <𝐳 b ↔ (a ⋅ c <𝐳 b ⋅ c)%z.
Proof with neauto.
  cut (∀ a b c ∈ ℤ, intPos c → a <𝐳 b → (a ⋅ c <𝐳 b ⋅ c)%z).
  intros Hright a Ha b Hb c Hc Hpc. split; intros Hlt.
  apply Hright... destruct (classic (a = b)).
  subst. exfalso. eapply intLt_irrefl...
  apply intLt_connected in H as []... exfalso.
  eapply (Hright b Hb a Ha c Hc Hpc) in H.
  eapply intLt_irrefl. eapply intLt_trans...
  intros a Ha b Hb c Hc Hpc Hlt.
  apply pQuotE in Ha as [m [Hm [n [Hn Ha]]]]. subst a.
  apply pQuotE in Hb as [p [Hp [q [Hq Hb]]]]. subst b.
  apply pQuotE in Hc as [r [Hr [s [Hs Hc]]]]. subst c.
  apply intLt in Hpc... rewrite add_0_r, add_0_l in Hpc...
  rewrite (intLt m Hm n Hn p Hp q Hq) in Hlt.
  rewrite (intMul_m_n_p_q m Hm n Hn r Hr s Hs).
  rewrite (intMul_m_n_p_q p Hp q Hq r Hr s Hs).
  assert (Hw1: m ⋅ r + n ⋅ s ∈ ω) by (amr; auto).
  assert (Hw2: m ⋅ s + n ⋅ r ∈ ω) by (amr; auto).
  assert (Hw3: p ⋅ r + q ⋅ s ∈ ω) by (amr; auto).
  assert (Hw4: p ⋅ s + q ⋅ r ∈ ω) by (amr; auto).
  rewrite (intLt (m⋅r + n⋅s) Hw1 (m⋅s + n⋅r) Hw2
    (p⋅r + q⋅s) Hw3 (p⋅s + q⋅r) Hw4).
  rewrite (add_comm (p⋅s)), (add_assoc (m⋅r)),
    <- (add_assoc (n⋅s)), (add_comm (n⋅s)),
    (add_assoc (q⋅r)), <- (add_assoc (m⋅r));
    swap 2 4; swap 3 15; [|amr|amr|mr..]...
  rewrite (add_comm (m⋅s)), (add_assoc (p⋅r)),
    <- (add_assoc (q⋅s)), (add_comm (q⋅s)),
    (add_assoc (n⋅r)), <- (add_assoc (p⋅r));
    swap 2 4; swap 3 15; [|amr|amr|mr..]...
  rewrite (mul_comm m), (mul_comm q), (mul_comm n), (mul_comm p),
    (mul_comm p), (mul_comm n), (mul_comm q), (mul_comm m)...
  repeat rewrite <- mul_distr...
  rewrite (add_comm n), (add_comm q)...
  apply ex4_25; auto; ar...
Qed.

Close Scope omega_scope.
Open Scope Int_scope.

Corollary intAdd_preserve_lt_trans : ∀ a b c d ∈ ℤ,
  a <𝐳 b → c <𝐳 d → a + c <𝐳 b + d.
Proof with auto.
  intros a Ha b Hb c Hc d Hd H1 H2.
  apply (intAdd_preserve_lt a Ha b Hb c Hc) in H1.
  apply (intAdd_preserve_lt c Hc d Hd b Hb) in H2.
  rewrite (intAdd_comm c), (intAdd_comm d) in H2...
  eapply intLt_trans; eauto.
Qed.

Corollary intAdd_cancel : ∀ a b c ∈ ℤ, a + c = b + c → a = b.
Proof with eauto.
  intros a Ha b Hb c Hc Heq.
  contra.
  apply intLt_connected in H as []; auto;
  eapply intAdd_preserve_lt in H; eauto;
  rewrite Heq in H; eapply intLt_irrefl...
Qed.

Corollary intAdd_cancel' : ∀ a b c ∈ ℤ, c + a = c + b → a = b.
Proof with eauto.
  intros a Ha b Hb c Hc Heq.
  eapply intAdd_cancel...
  rewrite intAdd_comm, (intAdd_comm b)...
Qed.

Corollary intMul_cancel : ∀ a b c ∈ ℤ,
  c ≠ Int 0 → a ⋅ c = b ⋅ c → a = b.
Proof with neauto.
  intros a Ha b Hb c Hc Hnq0 Heq.
  contra.
  apply intLt_connected in Hnq0 as [Hneg|Hpos]...
  - apply intNeg_pos in Hneg as Hpos.
    assert (Heq': a ⋅ -c = b ⋅ -c). {
      repeat rewrite intMul_addInv_r... congruence.
    }
    assert (Hnc: -c ∈ ℤ) by (apply intAddInv_ran; auto).
    apply intLt_connected in H as [H|H]; [|auto..];
      eapply intMul_preserve_lt in H; swap 1 5; swap 2 10;
        [apply Hpos|apply Hpos|auto..];
      rewrite Heq' in H;
      eapply intLt_irrefl; [apply H|apply H]...
  - apply intLt_connected in H as [H|H]; [|auto..];
      eapply intMul_preserve_lt in H; swap 1 5; swap 2 10;
        [apply Hpos|apply Hpos|auto..];
      rewrite Heq in H;
      eapply intLt_irrefl; [apply H|apply H]...
Qed.

Notation "a ≤ b" := (a <𝐳 b ∨ a = b) (at level 70) : Int_scope.

Corollary intAdd_preserve_le : ∀ a b c ∈ ℤ,
  a ≤ b ↔ a + c ≤ b + c.
Proof with eauto.
  intros a Ha b Hb c Hc. split; intros [].
  - left. apply intAdd_preserve_lt...
  - right. congruence.
  - left. apply intAdd_preserve_lt in H...
  - right. apply intAdd_cancel in H...
Qed.

Corollary intMul_preserve_le : ∀ a b c ∈ ℤ,
  intPos c → a ≤ b ↔ a ⋅ c ≤ b ⋅ c.
Proof with neauto.
  intros a Ha b Hb c Hc Hpc. split; intros [].
  - left. apply intMul_preserve_lt...
  - right. congruence.
  - left. apply intMul_preserve_lt in H...
  - right. apply intMul_cancel in H...
    destruct (classic (c = Int 0))... apply int_neq_0...
Qed.

Lemma intLt_iff_le_suc : ∀a b ∈ ℤ, a <𝐳 b ↔ a + Int 1 ≤ b.
Proof with neauto.
  intros a Ha b Hb.
  apply pQuotE in Ha as [m [Hm [n [Hn Ha]]]]. subst a.
  apply pQuotE in Hb as [p [Hp [q [Hq Hb]]]]. subst b.
  unfold Int. rewrite intAdd_m_n_p_q, add_0_r...
  assert (Heq: (m + q)%ω⁺ = (m + 1 + q)%ω). {
    rewrite suc, add_assoc, (add_comm q),
      <- add_assoc; nauto; ar...
  } split; intros.
  - apply intLt in H...
    destruct (classic (m + 1 + q = p + n)%ω).
    + right. apply int_ident; auto; ar...
    + left. apply intLt; auto; [ar|]...
      apply nat_connected in H0 as []; [| |ar;ar|ar]...
      exfalso. eapply (ω_not_dense (m + q)%ω); [ar|]...
      exists (p + n)%ω. split. ar... split... rewrite Heq...
  - apply intLt... destruct H.
    + apply intLt in H; auto; [|ar]... rewrite <- Heq in H.
      eapply nat_trans; revgoals... ar...
    + apply int_ident in H; auto; [|ar]...
      assert ((m + q)%ω ∈ (m + q)%ω⁺) by nauto. congruence.
Qed.

Lemma intNonNeg_iff : ∀a ∈ ℤ, ¬intNeg a ↔ Int 0 ≤ a.
Proof with neauto.
  intros a Ha. split; intros H.
  - destruct (classic (Int 0 = a))...
    apply intLt_connected in H0 as []... exfalso...
  - intros Hneg. destruct H; eapply intLt_irrefl.
    eapply intLt_trans... subst...
Qed.

Lemma intNonNeg_ex_nat : ∀a ∈ ℤ, ¬intNeg a → ∃ n, a = Int n.
Proof with nauto.
  intros a Ha Hnn.
  apply intNonNeg_iff in Hnn as [Hlt|H0]; [|exists 0|]...
  apply pQuotE in Ha as [m [Hm [n [Hn Ha]]]]. subst a.
  apply intLt in Hlt... rewrite add_0_r, add_0_l in Hlt...
  apply nat_subtr' in Hlt as [d [Hd [Heq _]]]...
  exists d. apply int_ident...
  rewrite add_0_r, add_comm, (embed_proj_id d)...
Qed.

(** 自然数嵌入 **)
Definition ω_Embed := Func ω ℤ (λ n, [<n, 0>]~).

Theorem ω_embed_function : ω_Embed: ω ⇒ ℤ.
Proof.
  apply meta_function.
  intros x Hx. apply pQuotI; nauto.
Qed.

Corollary ω_embed_ran : ∀n ∈ ω, ω_Embed[n] ∈ ℤ.
Proof with auto.
  pose proof ω_embed_function as [Hf [Hd Hr]].
  intros n Hn. apply Hr. eapply ranI.
  apply func_correct... rewrite Hd...
Qed. 

Theorem ω_embed_injective : injective ω_Embed.
Proof with nauto.
  apply meta_injection. intros x Hx. apply pQuotI...
  intros x1 Hx1 x2 Hx2 Heq. apply int_ident in Heq...
  rewrite add_0_r, add_0_r in Heq...
Qed.

Lemma ω_embed_n : ∀n ∈ ω, ω_Embed[n] = [<n, 0>]~.
Proof with nauto.
  intros n Hn. unfold ω_Embed. rewrite meta_func_ap...
  apply ω_embed_function.
Qed.

Theorem ω_embed : ∀ n : nat, ω_Embed[n] = Int n.
Proof. intros. rewrite ω_embed_n; nauto. Qed.

Theorem ω_embed_add : ∀ m n ∈ ω,
  ω_Embed[(m + n)%ω] = ω_Embed[m] + ω_Embed[n].
Proof with nauto.
  intros m Hm n Hn.
  repeat rewrite ω_embed_n; [|auto;ar;auto..].
  rewrite intAdd_m_n_p_q, add_0_r...
Qed.

Theorem ω_embed_mul : ∀ m n ∈ ω,
  ω_Embed[(m ⋅ n)%ω] = ω_Embed[m] ⋅ ω_Embed[n].
Proof with nauto.
  intros m Hm n Hn.
  repeat rewrite ω_embed_n; [|auto;mr;auto..].
  rewrite intMul_m_n_p_q, mul_0_r, mul_0_r,
    mul_0_l, add_0_r, add_0_r... apply mul_ran...
Qed.

Theorem ω_embed_lt : ∀ m n ∈ ω,
  m ∈ n ↔ ω_Embed[m] <𝐳 ω_Embed[n].
Proof with auto.
  intros m Hm n Hn.
  repeat rewrite ω_embed_n...
  pose proof ω_has_0 as H0.
  rewrite (intLt m Hm 0 H0 n Hn 0 H0).
  rewrite add_0_r, add_0_r... reflexivity.
Qed.

Theorem ω_embed_subtr : ∀ m n ∈ ω,
  [<m, n>]~ = ω_Embed[m] - ω_Embed[n].
Proof with nauto.
  intros m Hm n Hn.
  repeat rewrite ω_embed_n...
  rewrite intAddInv, intAdd_m_n_p_q, add_0_r, add_0_l...
Qed.
