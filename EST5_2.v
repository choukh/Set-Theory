(** Based on "Elements of Set Theory" Chapter 5 Part 2 **)
(** Coq coding by choukh, June 2020 **)

Require Export ZFC.EST5_1.

Local Ltac mr := apply mul_ran.
Local Ltac ar := apply add_ran.
Local Ltac amr := apply add_ran; apply mul_ran.

(*** EST第五章2：整数乘法，整数的序 ***)

Close Scope Int_scope.
Open Scope Nat_scope.

Definition PreIntMul : set :=
  IntArith (λ m n p q, <m⋅p + n⋅q, m⋅q + n⋅p>).
Notation "a ⋅ᵥ b" := (PreIntMul[<a, b>]) (at level 50).

Lemma cross_mul_rev : ∀ a b ∈ ω, ∃ m n p q ∈ ω,
  a = m⋅p + n⋅q ∧ b = m⋅q + n⋅p.
Proof with try apply ω_inductive; auto.
  intros a Ha b Hb.
  exists a. split... exists b. split...
  exists 1. split... exists 0. split...
  repeat rewrite mul_n_1, mul_m_0...
  rewrite add_m_0, add_0_n...
Qed.

Lemma preIntMul_maps_onto : PreIntMul: ℕ² × ℕ² ⟹ ℕ².
Proof with eauto.
  apply IntArithE_maps_onto.
  - intros m Hm n Hn p Hp q Hq.
    apply CProdI; apply add_ran; apply mul_ran...
  - intros a Ha b Hb.
    pose proof cross_mul_rev
      as [m [Hm [n [Hn [p [Hp [q [Hq H1]]]]]]]].
    apply Ha. apply Hb.
    exists m. split... exists n. split...
    exists p. split... exists q. split...
    apply op_correct...
Qed.

Lemma preIntMul_m_n_p_q : ∀ m n p q ∈ ω,
  <m, n> ⋅ᵥ <p, q> = <m⋅p + n⋅q, m⋅q + n⋅p>.
Proof with auto.
  intros m Hm n Hn p Hp q Hq.
  eapply func_ap. destruct preIntMul_maps_onto...
  apply SepI. apply CProdI; apply CProdI;
    try apply CProdI; try apply add_ran; try apply mul_ran...
  zfcrewrite...
Qed.

Lemma preIntMul_binCompatible : binCompatible IntEquiv ℕ² PreIntMul.
Proof with auto.
  split. apply intEquiv_equiv. split.
  destruct preIntMul_maps_onto as [Hf [Hd Hr]].
  split... split... rewrite Hr. apply sub_refl.
  intros x Hx y Hy u Hu v Hv H1 H2.
  apply CProd_correct in Hx as [m [Hm [n [Hn Hxeq]]]].
  apply CProd_correct in Hy as [p [Hp [q [Hq Hyeq]]]].
  apply CProd_correct in Hu as [m' [Hm' [n' [Hn' Hueq]]]].
  apply CProd_correct in Hv as [p' [Hp' [q' [Hq' Hveq]]]]. subst.
  apply intEquiv in H1... apply intEquiv in H2...
  rewrite preIntMul_m_n_p_q, preIntMul_m_n_p_q...
  apply SepI. apply CProdI; apply CProdI;
    apply add_ran; apply mul_ran... zfcrewrite. simpl.
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
  rewrite add_assoc, add_assoc in H35; [|amr|mr|mr|amr|mr..]...
  apply add_cancel in H35; [|ar;[amr|mr]|ar;[amr|mr]|mr]...
  assert (H46: m'⋅q + n⋅q + (n'⋅p' + n'⋅q) =
               m⋅q + n'⋅q + (n'⋅p + n'⋅q')) by congruence.
  rewrite (add_comm (m⋅q + n'⋅q)) in H46; [|amr;auto..].
  rewrite add_assoc, add_assoc in H46; [|amr|mr|mr|amr|mr..]...
  apply add_cancel in H46; swap 2 4; [|mr|ar;[amr|mr]..]...
  rewrite (add_comm (m⋅p)), <- add_assoc in H35; [|mr;auto..].
  assert (H: n'⋅p + (m⋅p + m'⋅q') + (m'⋅q + n⋅q + n'⋅p') =
    m'⋅p' + m'⋅q + n⋅p + (n'⋅p + n'⋅q' + m⋅q)) by congruence.
  rewrite <- add_assoc in H; [|mr|amr|ar;[amr|mr]]...
  rewrite (add_comm (m'⋅p' + m'⋅q + n⋅p)) in H; [|ar;[amr|mr];auto..].
  rewrite <- (add_assoc (n'⋅p)) in H; [|mr;auto..].
  rewrite <- (add_assoc (n'⋅p)) in H; [|mr|amr|ar;[amr|mr]]...
  apply add_cancel' in H; swap 2 4; [|mr|ar;[ar|ar;[ar|]];mr..]...
  rewrite (add_comm (m'⋅q)) in H; [|mr;auto..].
  rewrite (add_comm (n⋅q + m'⋅q)) in H; [|amr|mr]...
  rewrite add_assoc in H; [|amr|mr|amr]...
  rewrite add_assoc in H; [|ar;[ar|];mr|mr..]...
  rewrite (add_comm (m'⋅p' + m'⋅q)) in H; [|amr|mr]...
  rewrite add_assoc in H; [|amr|mr|amr]...
  rewrite add_assoc in H; [|ar;[ar|];mr|mr..]...
  apply add_cancel in H; swap 2 4; [|mr|ar;[ar;[ar|]|];mr..]...
  rewrite <- add_assoc; [|mr|mr|amr]...
  rewrite (add_comm (n⋅q)); [|mr|amr]...
  rewrite add_assoc, add_assoc; swap 2 6; [|amr|mr..]...
  rewrite <- (add_assoc (m'⋅p')); [|mr|mr|amr]...
  rewrite (add_comm (m'⋅p')); [|mr|ar;[mr|amr]]...
  rewrite (add_assoc (n'⋅q')); [|mr;auto..]. apply H.
Qed.

Close Scope Nat_scope.
Open Scope Int_scope.

(** 整数乘法 **)
Definition IntMul : set :=
  QuotionFunc IntEquiv ℕ² PreIntMul.
Notation "a ⋅ b" := (IntMul[<a, b>]) : Int_scope.

Lemma intMul_maps_onto : IntMul: ℤ × ℤ ⟹ ℤ.
Proof.
  apply quotionFunc_maps_onto.
  apply preIntMul_binCompatible.
  apply preIntMul_maps_onto.
Qed.

Lemma intMul_a_b : ∀ a b ∈ ℕ², [a]~ ⋅ [b]~ = [a ⋅ᵥ b]~.
Proof.
  apply binCompatibleE. apply preIntMul_binCompatible.
Qed.

Lemma intMul_m_n_p_q : ∀ m n p q ∈ ω,
  [<m, n>]~ ⋅ [<p, q>]~ = ([<m⋅p + n⋅q, m⋅q + n⋅p>]~)%n.
Proof with auto.
  intros m Hm n Hn p Hp q Hq.
  rewrite intMul_a_b, preIntMul_m_n_p_q...
  apply CProdI... apply CProdI...
Qed.

Lemma intMul_ran : ∀ a b ∈ ℤ, a ⋅ b ∈ ℤ.
Proof with auto.
  intros a Ha b Hb.
  apply intE in Ha as [m [Hm [n [Hn Ha]]]]. subst a.
  apply intE in Hb as [p [Hp [q [Hq Hb]]]]. subst b.
  rewrite intMul_m_n_p_q...
  apply intI; apply add_ran; apply mul_ran...
Qed.

Example intMul_2_n2 : Int 2 ⋅ -Int 2 = -Int 4.
Proof with auto.
  assert (H1w: 1 ∈ ω) by repeat apply ω_inductive.
  assert (H2w: 2 ∈ ω) by repeat apply ω_inductive.
  assert (H4w: 4 ∈ ω) by repeat apply ω_inductive.
  unfold Int. rewrite intInv, intInv...
  rewrite intMul_m_n_p_q...
  rewrite mul_0_n, mul_m_0, mul_m_0, add_m_0, add_m_0...
  rewrite mul_2_2... apply mul_ran...
Qed.

Close Scope Int_scope.
Open Scope Nat_scope.

Theorem intMul_comm : ∀ a b ∈ ℤ, (a ⋅ b = b ⋅ a)%z.
Proof with auto.
  intros a Ha b Hb.
  apply intE in Ha as [m [Hm [n [Hn Ha]]]].
  apply intE in Hb as [p [Hp [q [Hq Hb]]]]. subst.
  rewrite intMul_m_n_p_q, intMul_m_n_p_q...
  rewrite (mul_comm p), (mul_comm n)...
  rewrite (mul_comm m Hm q), (mul_comm n Hn p)...
  rewrite (add_comm (q⋅m)); [|apply mul_ran; auto ..]...
Qed.

Theorem intMul_assoc : ∀ a b c ∈ ℤ, (a ⋅ b ⋅ c = a ⋅ (b ⋅ c))%z.
Proof.
  intros a Ha b Hb c Hc.
  apply intE in Ha as [m [Hm [n [Hn Ha]]]].
  apply intE in Hb as [p [Hp [q [Hq Hb]]]].
  apply intE in Hc as [r [Hr [s [Hs Hc]]]]. subst.
  repeat rewrite intMul_m_n_p_q; [|auto;amr;auto..].
  apply int_ident; swap 1 5; [|ar;mr;auto;ar;mr;auto..].
  repeat rewrite mul_distr, mul_distr'; [|auto;mr;auto..].
  repeat rewrite mul_assoc; [|auto..].
  cut (∀ x1 x2 x3 x4 x5 x6 x7 x8 ∈ ω,
    x1 + x4 + (x2 + x3) + (x5 + x7 + (x8 + x6)) =
    x1 + x2 + (x3 + x4) + (x5 + x6 + (x7 + x8))).
  intros H. apply H; mr; auto; mr; auto.
  clear Hm Hn Hp Hq Hr Hs m n p q r s.
  intros x1 H1 x2 H2 x3 H3 x4 H4 x5 H5 x6 H6 x7 H7 x8 H8.
  rewrite <- (add_assoc x1), (add_comm x4); [|auto;ar;auto..].
  rewrite <- (add_assoc x2), (add_assoc x1); [|auto;ar;auto..].
  rewrite <- (add_assoc x5), (add_assoc x7); [|auto;ar;auto..].
  rewrite (add_comm (x7+x8)), <- (add_assoc x5); [|auto;ar;auto..].
  reflexivity.
Qed.

Theorem intMul_distr : ∀ a b c ∈ ℤ, (a ⋅ (b + c) = a ⋅ b + a ⋅ c)%z.
Proof.
  intros a Ha b Hb c Hc.
  apply intE in Ha as [m [Hm [n [Hn Ha]]]].
  apply intE in Hb as [p [Hp [q [Hq Hb]]]].
  apply intE in Hc as [r [Hr [s [Hs Hc]]]]. subst.
  rewrite intAdd_m_n_p_q; [|auto..].
  repeat rewrite intMul_m_n_p_q; [|auto;ar;auto..].
  repeat rewrite intAdd_m_n_p_q; [|amr;auto..].
  apply int_ident; [ar;mr;auto;ar;auto|ar;mr;auto;ar;auto|
    ar;amr;auto|ar;amr;auto|].
  repeat rewrite mul_distr; [|auto..].
  cut (∀ x1 x2 x3 x4 x5 x6 x7 x8 ∈ ω,
    x1 + x3 + (x2 + x4) + (x5 + x7 + (x6 + x8)) =
    x1 + x2 + (x3 + x4) + (x5 + x6 + (x7 + x8))).
  intros H. apply H; mr; auto.
  clear Hm Hn Hp Hq Hr Hs m n p q r s.
  intros x1 H1 x2 H2 x3 H3 x4 H4 x5 H5 x6 H6 x7 H7 x8 H8.
  rewrite <- (add_assoc x1), (add_assoc x3),
    (add_comm x3), <- (add_assoc x2), (add_assoc x1);
    swap 2 4; swap 3 15; [|ar;auto|ar;auto|auto..].
  rewrite <- (add_assoc x5), (add_assoc x7),
    (add_comm x7), <- (add_assoc x6), (add_assoc x5);
    swap 2 4; swap 3 15; [|ar;auto|ar;auto|auto..].
  reflexivity.
Qed.

Theorem intMul_ident : ∀a ∈ ℤ, (a ⋅ Int 1 = a)%z.
Proof with auto.
  assert (H1w: 1 ∈ ω) by repeat apply ω_inductive.
  intros a Ha. apply intE in Ha as [m [Hm [n [Hn Ha]]]].
  subst a. unfold Int. rewrite intMul_m_n_p_q...
  rewrite mul_n_1, mul_n_1, mul_m_0, mul_m_0, add_m_0, add_0_n...
Qed.

Theorem int_0_neq_1 : Int 0 ≠ Int 1.
Proof with auto.
  assert (H1w: 1 ∈ ω) by repeat apply ω_inductive.
  unfold Int. intros H. apply int_ident in H...
  rewrite add_m_0, add_m_0 in H... eapply S_neq_0. eauto.
Qed.

Theorem int_no_0_div : ∀ a b ∈ ℤ,
  (a ⋅ b = Int 0)%z → a = Int 0 ∨ b = Int 0.
Proof with auto.
  intros a Ha b Hb Heq.
  destruct (classic (a = Int 0)) as [|H1];
  destruct (classic (b = Int 0)) as [|H2]... exfalso.
  cut ((a ⋅ b)%z ≠ Int 0). intros... clear Heq.
  apply intE in Ha as [m [Hm [n [Hn Ha]]]].
  apply intE in Hb as [p [Hp [q [Hq Hb]]]].
  subst a b. rewrite intMul_m_n_p_q...
  cut (m⋅p + n⋅q ≠ m⋅q + n⋅p). intros Hnq Heq. apply Hnq.
  apply int_ident in Heq; [|auto;amr..]...
  rewrite add_m_0, add_0_n in Heq; auto; amr...
  assert (Hmn: m ≠ n). {
    intros H. apply H1. apply int_ident...
    rewrite add_m_0, add_0_n...
  }
  assert (Hpq: p ≠ q). {
    intros H. apply H2. apply int_ident...
    rewrite add_m_0, add_0_n...
  }
  clear H1 H2.
  assert (Hw: m⋅q + n⋅p ∈ ω) by (amr; auto).
  apply ω_connected in Hmn as [H1|H1];
  apply ω_connected in Hpq as [H2|H2]; auto;
  intros Heq; eapply lt_not_refl; revgoals;
  (eapply ch4_25 in H1; [apply H1 in H2| | | |]; [|auto..]);
  try apply Hw; [|
    |rewrite add_comm, (add_comm (n⋅p)) in H2; [|mr;auto..]
    |rewrite add_comm, (add_comm (n⋅q)) in H2; [|mr;auto..]
  ];
  rewrite Heq in H2; apply H2.
Qed.

Example intMul_n1_a : ∀ a ∈ ℤ, (-Int 1 ⋅ a = -a)%z.
Proof with auto.
  intros a Ha.
  assert (H1w: 1 ∈ ω) by repeat apply ω_inductive.
  apply intE in Ha as [m [Hm [n [Hn Ha]]]]. subst a.
  unfold Int. rewrite intInv, intInv, intMul_m_n_p_q...
  rewrite mul_0_n, mul_0_n, (mul_comm 1), (mul_comm 1)...
  rewrite mul_n_1, mul_n_1, add_0_n, add_0_n...
Qed.

(** 整数的序 **)

Lemma int_orderable : ∀ m n m' n' p q p' q',
  <m, n> ~ <m', n'> → <p, q> ~ <p', q'> →
  m + q ∈ p + n ↔ m' + q' ∈ p' + n'.
Proof.
  intros * H1 H2.
  apply intEquivE2 in H1 as [H1 [Hm [Hn [Hm' Hn']]]].
  apply intEquivE2 in H2 as [H2 [Hp [Hq [Hp' Hq']]]].
  assert (Hmq: m + q ∈ ω) by (ar; auto).
  assert (Hpn: p + n ∈ ω) by (ar; auto).
  assert (Hn'q': n' + q' ∈ ω) by (ar; auto).
  rewrite (ineq_both_side_add _ Hmq _ Hpn _ Hn'q').
  rewrite <- (add_assoc m), (add_comm q), (add_assoc m),
    (add_assoc m), (add_comm n'), <- (add_assoc p),
    (add_comm n), (add_assoc p), (add_assoc p),
    H1, H2, <- (add_assoc m'), (add_comm n), (add_assoc m'),
    <- (add_assoc (m'+q')), <- (add_assoc p'), (add_comm q),
    (add_assoc p'), <- (add_assoc (p'+n')), (add_comm q);
    [|auto;ar;auto..].
  assert (Hm'q': m' + q' ∈ ω) by (ar; auto).
  assert (Hp'n': p' + n' ∈ ω) by (ar; auto).
  assert (Hnq: n + q ∈ ω) by (ar; auto).
  rewrite <- (ineq_both_side_add _ Hm'q' _ Hp'n' _ Hnq).
  reflexivity.
Qed.

(* 整数的小于关系 *)
Definition IntLt : set := Relation ℤ ℤ (λ a b,
  let u := IntProj a in let v := IntProj b in
  let m := π1 u in let n := π2 u in
  let p := π1 v in let q := π2 v in
  m + q ∈ p + n
).
Notation "a <𝐳 b" := (<a, b> ∈ IntLt) (at level 70).

Lemma intLtI : ∀ m n p q ∈ ω,
  m + q ∈ p + n → [<m, n>]~ <𝐳 [<p, q>]~.
Proof with auto.
  intros m Hm n Hn p Hp q Hq Heq.
  apply SepI. apply CProdI; apply intI... zfcrewrite.
  pose proof (intProj m Hm n Hn)
    as [m' [Hm' [n' [Hn' [H11 H12]]]]].
  pose proof (intProj p Hp q Hq)
    as [p' [Hp' [q' [Hq' [H21 H22]]]]].
  pose proof intEquiv_equiv as [_ [_ [Hsym _]]].
  rewrite H11, H21. simpl. zfcrewrite. eapply int_orderable.
  apply Hsym. apply H12. apply Hsym. apply H22. apply Heq.
Qed.

Lemma intLtE : ∀ a b, a <𝐳 b → ∃ m n p q ∈ ω,
  a = [<m, n>]~ ∧ b = [<p, q>]~ ∧ m + q ∈ p + n.
Proof with auto.
  intros a b Hlt. apply SepE in Hlt as [H1 H2].
  apply CProdE1 in H1 as [Ha Hb]; zfcrewrite.
  apply intE in Ha as [m [Hm [n [Hn Ha]]]].
  apply intE in Hb as [p [Hp [q [Hq Hb]]]]. subst.
  exists m. split... exists n. split...
  exists p. split... exists q. split... split... split...
  pose proof (intProj m Hm n Hn) as [r [Hr [s [Hs [H11 H12]]]]].
  pose proof (intProj p Hp q Hq) as [u [Hu [v [Hv [H21 H22]]]]].
  rewrite H11, H21 in H2. simpl in H2. zfcrewrite.
  eapply int_orderable; eauto.
Qed.

Lemma intLt : ∀ m n p q ∈ ω,
  [<m, n>]~ <𝐳 [<p, q>]~ ↔ m + q ∈ p + n.
Proof.
  intros m Hm n Hn p Hp q Hq. split; intros.
  - apply SepE in H as [H1 H2].
    apply CProdE1 in H1 as [Ha Hb]; zfcrewrite.
    pose proof (intProj m Hm n Hn) as [r [Hr [s [Hs [H11 H12]]]]].
    pose proof (intProj p Hp q Hq) as [u [Hu [v [Hv [H21 H22]]]]].
    rewrite H11, H21 in H2. simpl in H2. zfcrewrite.
    eapply int_orderable; eauto.
  - apply intLtI; auto.
Qed.

Lemma intNeqE : ∀ m n p q ∈ ω,
  [< m, n>]~ ≠ [< p, q>]~ → m + q ≠ p + n.
Proof with auto.
  intros m Hm n Hn p Hp q Hq Hnq. intros Heq.
  apply Hnq. apply int_ident...
Qed.

Theorem totalOrd_intLt : totalOrd IntLt ℤ.
Proof with auto.
  assert (Hrel: rel IntLt ℤ). {
    intros x Hx. apply SepE in Hx as []...
  }
  assert (Htr: tranr IntLt). {
    intros x y z H1 H2.
    apply intLtE in H1
      as [m [Hm [n [Hn [p [Hp [q [Hq [Hx [Hy1 H1]]]]]]]]]].
    apply intLtE in H2
      as [p' [Hp' [q' [Hq' [r [Hr [s [Hs [Hy2 [Hz H2]]]]]]]]]].
    subst x y z. apply int_ident in Hy2... apply intLtI...
    assert (H2': p' + s + (p + q') ∈ r + q' + (p + q')). {
      apply ineq_both_side_add; auto; ar...
    }
    rewrite Hy2 in H2' at 2.
    rewrite (add_comm p'), (add_comm p), <- add_assoc,
      (add_assoc p'), (add_comm (p' + q')), add_assoc,
      <- (add_assoc r), (add_assoc q'), (add_comm q'),
      (add_comm (p' + q')), (add_assoc r) in H2';
      [|auto;ar;auto..].
    apply ineq_both_side_add in H2'; [|ar;auto..].
    assert (H1': m + q + s ∈ p + n + s). {
      apply ineq_both_side_add; auto; ar...
    }
    assert (H2'': s + p + n ∈ r + q + n). {
      apply ineq_both_side_add; auto; ar...
    }
    rewrite <- add_assoc, add_comm in H2''; [|auto;ar;auto..].
    assert (H: m + q + s ∈ r + q + n). {
      eapply nat_trans; revgoals; eauto. ar; [ar|]...
    }
    rewrite <- add_assoc, (add_comm q), add_assoc,
      <- (add_assoc r), (add_comm q), (add_assoc r) in H...
    apply ineq_both_side_add in H; auto; ar...
  }
  split... split... apply trich_iff... split.
  - intros [x [Hx Hlt]]. apply intLtE in Hlt
      as [m [Hm [n [Hn [p [Hp [q [Hq [H1 [H2 Hlt]]]]]]]]]].
    subst x. apply int_ident in H2... rewrite H2 in Hlt.
    eapply lt_not_refl; revgoals; eauto; ar...
  - intros x Hx y Hy Hnq.
    apply intE in Hx as [m [Hm [n [Hn Hx]]]].
    apply intE in Hy as [p [Hp [q [Hq Hy]]]].
    subst x y. apply intNeqE in Hnq...
    apply ω_connected in Hnq as []; [| |ar;auto..].
    + left. apply intLtI...
    + right. apply intLtI...
Qed.

Definition positive : set → Prop := λ x, Int 0 <𝐳 x.
Definition negative : set → Prop := λ x, x <𝐳 Int 0.

Lemma int_pos_neg : ∀ x, positive x → negative (-x)%z.
Proof with auto.
  intros. apply intLtE in H
    as [m [Hm [n [Hn [p [Hp [q [Hq [H1 [H2 Hlt]]]]]]]]]].
  apply int_ident in H1... rewrite add_m_0, add_0_n in H1...
  subst x n. rewrite intInv... apply intLtI...
  rewrite add_m_0, add_0_n... rewrite add_comm in Hlt...
  apply ineq_both_side_add in Hlt...
Qed.

Lemma int_neg_pos : ∀ x, negative x → positive (-x)%z.
Proof with auto.
  intros. apply intLtE in H
    as [m [Hm [n [Hn [p [Hp [q [Hq [H1 [H2 Hlt]]]]]]]]]].
  apply int_ident in H2... rewrite add_m_0, add_0_n in H2...
  subst x q. rewrite intInv... apply intLtI...
  rewrite add_m_0, add_0_n... rewrite (add_comm p) in Hlt...
  apply ineq_both_side_add in Hlt...
Qed.

Lemma tranr_intLt : tranr IntLt.
Proof. destruct totalOrd_intLt as [_ []]. auto. Qed.

Lemma int_connected : ∀ a b ∈ ℤ,
  a ≠ b → a <𝐳 b ∨ b <𝐳 a.
Proof.
  intros a Ha Hnq0. pose proof totalOrd_connected.
  eapply H. apply totalOrd_intLt. apply Ha.
Qed.

Lemma intLt_not_refl : ∀a ∈ ℤ, a <𝐳 a → ⊥.
Proof with auto.
  intros a Ha Hc.
  apply intE in Ha as [m [Hm [n [Hn Ha]]]]. subst a.
  apply intLt in Hc... eapply lt_not_refl; revgoals.
  apply Hc. ar...
Qed.

Theorem int_ineq_both_side_add : ∀ a b c ∈ ℤ,
  a <𝐳 b ↔ (a + c <𝐳 b + c)%z.
Proof with auto.
  intros a Ha b Hb c Hc.
  apply intE in Ha as [m [Hm [n [Hn Ha]]]]. subst a.
  apply intE in Hb as [p [Hp [q [Hq Hb]]]]. subst b.
  apply intE in Hc as [r [Hr [s [Hs Hc]]]]. subst c.
  rewrite (intLt m Hm n Hn p Hp q Hq).
  rewrite intAdd_m_n_p_q, intAdd_m_n_p_q...
  assert (Hw1: m + r ∈ ω) by (ar; auto).
  assert (Hw2: n + s ∈ ω) by (ar; auto).
  assert (Hw3: p + r ∈ ω) by (ar; auto).
  assert (Hw4: q + s ∈ ω) by (ar; auto).
  rewrite (intLt (m+r) Hw1 (n+s) Hw2 (p+r) Hw3 (q+s) Hw4).
  rewrite <- (add_assoc m), (add_assoc r), (add_comm r),
    <- (add_assoc q), (add_assoc m),
    <- (add_assoc p), (add_assoc r), (add_comm r Hr n Hn),
    <- (add_assoc n), (add_assoc p); [|auto;ar;auto..].
  apply ineq_both_side_add; ar...
Qed.

Theorem int_ineq_both_side_mul : ∀ a b c ∈ ℤ,
  positive c → a <𝐳 b ↔ (a ⋅ c <𝐳 b ⋅ c)%z.
Proof with auto.
  cut (∀ a b c ∈ ℤ, positive c → a <𝐳 b → (a ⋅ c <𝐳 b ⋅ c)%z).
  intros Hright a Ha b Hb c Hc Hpc. split; intros.
  apply Hright... destruct (classic (a = b)).
  subst. exfalso. eapply intLt_not_refl; revgoals.
  apply H. apply intMul_ran...
  apply int_connected in H0 as []... exfalso.
  eapply Hright in H0... eapply intLt_not_refl; revgoals.
  eapply tranr_intLt. apply H. apply H0.
  apply intMul_ran... apply Hc. apply Hpc.
  intros a Ha b Hb c Hc Hpc Hlt.
  apply intE in Ha as [m [Hm [n [Hn Ha]]]]. subst a.
  apply intE in Hb as [p [Hp [q [Hq Hb]]]]. subst b.
  apply intE in Hc as [r [Hr [s [Hs Hc]]]]. subst c.
  apply intLt in Hpc... rewrite add_m_0, add_0_n in Hpc...
  rewrite (intLt m Hm n Hn p Hp q Hq) in Hlt.
  rewrite (intMul_m_n_p_q m Hm n Hn r Hr s Hs).
  rewrite (intMul_m_n_p_q p Hp q Hq r Hr s Hs).
  assert (Hw1: m ⋅ r + n ⋅ s ∈ ω) by (amr; auto).
  assert (Hw2: m ⋅ s + n ⋅ r ∈ ω) by (amr; auto).
  assert (Hw3: p ⋅ r + q ⋅ s ∈ ω) by (amr; auto).
  assert (Hw4: p ⋅ s + q ⋅ r ∈ ω) by (amr; auto).
  rewrite (intLt (m⋅r + n⋅s) Hw1 (m⋅s + n⋅r) Hw2
    (p⋅r + q⋅s) Hw3 (p⋅s + q⋅r) Hw4).
  rewrite (add_comm (p⋅s)), <- (add_assoc (m⋅r)),
    (add_assoc (n⋅s)), (add_comm (n⋅s)),
    <- (add_assoc (q⋅r)), (add_assoc (m⋅r));
    swap 2 4; swap 3 15; [|amr|amr|mr..]...
  rewrite (add_comm (m⋅s)), <- (add_assoc (p⋅r)),
    (add_assoc (q⋅s)), (add_comm (q⋅s)),
    <- (add_assoc (n⋅r)), (add_assoc (p⋅r));
    swap 2 4; swap 3 15; [|amr|amr|mr..]...
  rewrite (mul_comm m), (mul_comm q), (mul_comm n), (mul_comm p),
    (mul_comm p), (mul_comm n), (mul_comm q), (mul_comm m)...
  repeat rewrite <- mul_distr...
  rewrite (add_comm n), (add_comm q)...
  apply ch4_25; auto; ar...
Qed.

Close Scope Nat_scope.
Open Scope Int_scope.

Corollary intAdd_cancel : ∀ a b c ∈ ℤ, a + c = b + c → a = b.
Proof with eauto.
  intros a Ha b Hb c Hc Heq.
  destruct (classic (a = b))... exfalso.
  apply int_connected in H as []...
  - eapply int_ineq_both_side_add in H... rewrite Heq in H.
    eapply intLt_not_refl; revgoals... apply intAdd_ran...
  - eapply int_ineq_both_side_add in H... rewrite Heq in H.
    eapply intLt_not_refl; revgoals... apply intAdd_ran...
Qed.

Corollary add_cancel' : ∀ a b c ∈ ℤ, c + a = c + b → a = b.
Proof with eauto.
  intros a Ha b Hb c Hc Heq.
  eapply intAdd_cancel...
  rewrite intAdd_comm, (intAdd_comm b)...
Qed.

Lemma intInv_n1 : ∀a ∈ ℤ, -a = -Int 1 ⋅ a.
Proof with eauto.
  intros a Ha.
  assert (Hw: 1 ∈ ω) by (apply ω_inductive; auto).
  apply intE in Ha as [m [Hm [n [Hn Ha]]]]. subst a.
  rewrite intInv... unfold Int. rewrite intInv...
  rewrite intMul_m_n_p_q... apply int_ident...
  rewrite mul_0_n, mul_comm, mul_n_1, add_0_n...
  rewrite mul_0_n, mul_comm, mul_n_1, add_0_n...
  rewrite mul_0_n, mul_comm, mul_n_1, add_0_n,
    mul_0_n, mul_comm, mul_n_1, add_0_n...
Qed.

Corollary mul_cancel : ∀ a b c ∈ ℤ,
  c ≠ Int 0 → a ⋅ c = b ⋅ c → a = b.
Proof with eauto.
  intros a Ha b Hb c Hc Hnq0 Heq.
  destruct (classic (a = b))... exfalso.
  assert (Hw: 1 ∈ ω) by (apply ω_inductive; auto).
  assert (Hzn1: - Int 1 ∈ ℤ). {
    unfold Int. rewrite intInv... apply intI...
  }
  apply int_connected in Hnq0 as [];
  apply int_connected in H as []...
  - apply intE in Hc as [m [Hm [n [Hn Hceq]]]]. subst c.
    assert (Hmn: [<m, n>]~ ∈ ℤ) by (apply intI; auto).
    assert (Hnm: [<n, m>]~ ∈ ℤ) by (apply intI; auto).
    apply int_neg_pos in H0. rewrite intInv in H0...
    eapply int_ineq_both_side_mul in H; revgoals.
    apply H0. apply intI... apply Hb. apply Ha.
    rewrite (intMul_comm a), (intMul_comm b) in Heq...
    assert (-([<m, n>]~ ⋅ a) = -([<m, n>]~ ⋅ b)) by congruence.
    rewrite intInv_n1, (intInv_n1 ([< m, n >] ~ ⋅ b)) in H1;
      [|apply intMul_ran..]...
    rewrite <- intMul_assoc, <- intMul_assoc in H1...
    rewrite <- intInv_n1, intInv in H1...
    rewrite intMul_comm, (intMul_comm ([<n, m>]~)) in H1...
    rewrite H1 in H. eapply intLt_not_refl; revgoals...
    apply intMul_ran...
  -
Qed.













