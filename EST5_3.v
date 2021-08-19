(** Adapted from "Elements of Set Theory" Chapter 5 **)
(** Coq coding by choukh, June 2020 **)

Require Export ZFC.EST5_2.
Require Import ZFC.lib.WosetMin.
Import WosetMin.SimpleVer.

Local Ltac mr := apply intMul_ran; nauto.
Local Ltac ar := apply intAdd_ran; nauto.
Local Ltac amr := apply intAdd_ran; apply intMul_ran; nauto.

(*** EST第五章3：有理数的定义
  有理数算术：加法，加法逆元，乘法，乘法逆元 ***)

(* 非零整数 *)
Definition ℤ' := (ℤ - ⎨Int 0⎬)%set.

Lemma nzIntI0 : ∀a ∈ ℤ, a ≠ Int 0 → a ∈ ℤ'.
Proof with auto.
  intros a Ha Hnq0. apply CompI... apply SingNI...
Qed.

Lemma nzIntI1 : ∀ n : nat, [<(S n), 0>]~%pz ∈ ℤ'.
Proof with neauto.
  intros. apply CompI... apply SingNI.
  intros H. apply int_ident in H...
  rewrite add_ident, add_ident' in H... eapply suc_neq_0...
Qed.
Global Hint Immediate nzIntI1 : number_hint.

Lemma nzIntE0 : ∀a ∈ ℤ', a ≠ Int 0.
Proof with auto.
  intros a Ha H0. apply CompE in Ha as [_ Ha].
  apply SingNE in Ha...
Qed.

Lemma nzIntE1 : ∀a ∈ ℤ', a ∈ ℤ.
Proof with auto.
  intros a Ha. apply CompE in Ha as [Ha _]...
Qed.
Local Ltac nz := try (apply nzIntE1; assumption).

Lemma int_sn : ∀ n, Int (S n) ∈ ℤ'.
Proof.
  intros. apply CompI; nauto.
  apply SingNI. apply int_suc_neq_0.
Qed.
Global Hint Immediate int_sn : number_hint.

Lemma nzIntMul_ranI : ∀ a b ∈ ℤ', a ⋅ b ∈ ℤ'.
Proof with neauto.
  intros a Ha' b Hb'.
  apply nzIntE1 in Ha' as Ha. apply nzIntE1 in Hb' as Hb.
  apply nzIntI0. apply intMul_ran; nz...
  apply nzIntE0 in Ha' as Ha0. apply nzIntE0 in Hb' as Hb0.
  intros H0. apply int_no_0_div in H0 as []...
Qed.
Local Ltac amr_n := apply add_ran; apply mul_ran; auto.

Lemma nzIntMul_ranE : ∀ a b ∈ ℤ, a ⋅ b ∈ ℤ' → a ∈ ℤ' ∧ b ∈ ℤ'.
Proof with nauto.
  intros a Ha b Hb Hab.
  apply pQuotE in Ha as [m [Hm [n [Hn Ha]]]]. subst a.
  apply pQuotE in Hb as [p [Hp [q [Hq Hb]]]]. subst b.
  rewrite intMul_m_n_p_q in Hab... apply nzIntE0 in Hab.
  split; (apply CompI; [apply pQuotI; auto|]); apply SingNI;
    intros H; apply Hab; clear Hab;
    apply int_ident in H; nauto; rewrite add_ident, add_ident' in H;
    subst; auto; apply int_ident; try amr_n...
  rewrite add_ident, add_ident', add_comm...
  apply mul_ran... apply mul_ran... amr_n. amr_n.
  rewrite add_ident, add_ident'... amr_n. amr_n.
Qed.

Local Ltac nzmr := apply nzIntMul_ranI; nauto.

Close Scope PreInt_scope.
Declare Scope PreRat_scope.
Open Scope PreRat_scope.
Delimit Scope PreRat_scope with pq.

(* 整数平面上的用于构造有理数的等价关系 *)
Definition RatEq : PlaneEq := λ a b c d, a ⋅ d = c ⋅ b.
Notation "~" := (PlaneEquiv ℤ ℤ' RatEq) : PreRat_scope.
Notation "r ~ s" := (<r, s> ∈ PlaneEquiv ℤ ℤ' RatEq)
  (at level 10) : PreRat_scope.

Lemma ratEqRefl : planeEqRefl RatEq.
Proof. intros a b. reflexivity. Qed.

Lemma ratEqSymm : planeEqSymm RatEq.
Proof. intros a b c d Heq. symmetry. auto. Qed.

Lemma ratEqTran : planeEqTran ℤ ℤ' RatEq.
Proof with eauto.
  intros a Ha b Hb c Hc d Hd e He f Hf H1 H2.
  unfold RatEq in *.
  apply CompE in Hb as [Hb _].
  apply CompE in Hf as [Hf _].
  apply CompE in Hd as [Hd1 Hd2].
  assert (H1': a ⋅ d ⋅ f = c ⋅ b ⋅ f) by congruence.
  assert (H2': c ⋅ f ⋅ b = e ⋅ d ⋅ b) by congruence.
  rewrite intMul_assoc, (intMul_comm f), <- intMul_assoc in H2'...
  rewrite H2' in H1'.
  rewrite intMul_assoc, (intMul_comm d), <- intMul_assoc,
    (intMul_assoc e), (intMul_comm d), <- (intMul_assoc e) in H1'...
  eapply intMul_cancel; revgoals; [apply H1'|..]...
  intros Heq. apply Hd2. rewrite Heq... mr... mr...
Qed.

Theorem ratEquiv_equiv : equiv (PlaneEquiv ℤ ℤ' RatEq) (ℤ × ℤ').
Proof.
  apply planeEquiv_equiv.
  apply ratEqRefl. apply ratEqSymm. apply ratEqTran. 
Qed.

(** 有理数 **)
Definition ℚ : set := (ℤ × ℤ')/~.

Lemma rat_ident : ∀a ∈ ℤ, ∀b ∈ ℤ', ∀c ∈ ℤ, ∀d ∈ ℤ',
  a ⋅ d = c ⋅ b ↔ [<a, b>]~ = [<c, d>]~.
Proof with eauto.
  intros a Ha b Hb c Hc d Hd.
  now apply (pQuot_ident ℤ ℤ' RatEq ratEqRefl ratEqSymm ratEqTran).
Qed.

Definition PreRatAdd : set :=
  PlaneArith ℤ ℤ' (λ a b c d, <a⋅d + c⋅b, b⋅d>).
Notation "a +ᵥ b" := (PreRatAdd[<a, b>]) (at level 50) : PreRat_scope.

Lemma preRatAdd_maps_onto : PreRatAdd: (ℤ × ℤ')² ⟹ (ℤ × ℤ').
Proof with neauto.
  apply planeArith_maps_onto.
  - intros a Ha b Hb c Hc d Hd. apply CProdI. amr;nz. nzmr.
  - intros a Ha b Hb.
    exists a. split... exists b. split...
    exists (Int 0). split... exists (Int 1). split...
    apply CompE in Hb as [Hb _]. apply op_iff.
    rewrite intMul_ident, intMul_ident... split...
    rewrite intMul_comm, intMul_0_r, intAdd_ident...
Qed.

Lemma preRatAdd_a_b_c_d : ∀a ∈ ℤ, ∀b ∈ ℤ', ∀c ∈ ℤ, ∀d ∈ ℤ',
  <a, b> +ᵥ <c, d> = <a⋅d + c⋅b, b⋅d>.
Proof with auto.
  intros a Ha b Hb c Hc d Hd.
  eapply func_ap. destruct preRatAdd_maps_onto...
  apply SepI. apply CProdI; apply CProdI.
  apply CProdI... apply CProdI... amr;nz. nzmr. zfc_simple...
Qed.

Lemma preRatAdd_binCompatible :
  binCompatible (PlaneEquiv ℤ ℤ' RatEq) (ℤ × ℤ') PreRatAdd.
Proof with eauto.
  split. apply ratEquiv_equiv. split.
  destruct preRatAdd_maps_onto as [Hf [Hd Hr]].
  split... split... rewrite Hr. apply sub_refl. 
  intros x Hx y Hy u Hu v Hv H1 H2.
  apply CProdE1 in Hx as [a [Ha [b [Hb Hxeq]]]].
  apply CProdE1 in Hy as [c [Hc [d [Hd Hyeq]]]].
  apply CProdE1 in Hu as [a' [Ha' [b' [Hb' Hueq]]]].
  apply CProdE1 in Hv as [c' [Hc' [d' [Hd' Hveq]]]]. subst.
  apply planeEquiv in H1... apply planeEquiv in H2...
  rewrite preRatAdd_a_b_c_d, preRatAdd_a_b_c_d...
  apply SepI. apply CProdI; (apply CProdI; [amr;nz|nzmr]).
  zfc_simple. simpl. unfold RatEq in *.
  rewrite intMul_distr', intMul_distr'; [|mr;nz..].
  erewrite 
    (intMul_assoc a), (intMul_comm d), (intMul_assoc b'), <- (intMul_assoc a),
    (intMul_assoc a'), (intMul_comm d' _ (b⋅d)), (intMul_assoc b), <- (intMul_assoc a'),
    (intMul_assoc c), (intMul_comm b), (intMul_comm b'), (intMul_assoc d'), <- (intMul_assoc c),
    (intMul_assoc c'), (intMul_comm b' _ (b⋅d)), (intMul_comm b), (intMul_assoc d), <- (intMul_assoc c'),
    (intMul_comm d'), (intMul_comm b');
    [|auto;nz;mr;nz..]. congruence. Unshelve. nz. nz.
Qed.

Close Scope Int_scope.
Declare Scope Rat_scope.
Open Scope Rat_scope.
Delimit Scope Rat_scope with q.

(**有理数加法 **)
Definition RatAdd : set :=
  QuotionFunc (PlaneEquiv ℤ ℤ' RatEq) (ℤ × ℤ') PreRatAdd.
Notation "r + s" := (RatAdd[<r, s>]) : Rat_scope.

Lemma ratAdd_maps_onto : RatAdd: ℚ × ℚ ⟹ ℚ.
Proof.
  apply quotionFunc_maps_onto.
  apply preRatAdd_binCompatible.
  apply preRatAdd_maps_onto.
Qed.

Lemma ratAdd_r_s : ∀ r s ∈ (ℤ × ℤ'), [r]~ + [s]~ = [r +ᵥ s]~.
Proof.
  intros r Hr s Hs. apply binCompatibleE; auto.
  apply preRatAdd_binCompatible.
Qed.

Global Opaque RatAdd.

Lemma ratAdd_a_b_c_d : ∀a ∈ ℤ, ∀b ∈ ℤ', ∀c ∈ ℤ, ∀d ∈ ℤ',
  [<a, b>]~ + [<c, d>]~ = ([<a⋅d + c⋅b, b⋅d>]~)%z.
Proof with auto.
  intros a Ha b Hb c Hc d Hd.
  rewrite ratAdd_r_s, preRatAdd_a_b_c_d...
  apply CProdI... apply CProdI...
Qed.

Lemma ratAdd_ran : ∀ r s ∈ ℚ, r + s ∈ ℚ.
Proof with auto.
  intros r Hr s Hs.
  apply pQuotE in Hr as [a [Ha [b [Hb Hr]]]]. subst r.
  apply pQuotE in Hs as [c [Hc [d [Hd Hs]]]]. subst s.
  rewrite ratAdd_a_b_c_d... apply pQuotI. amr;nz. nzmr.
Qed.

Definition Rat : nat → set := λ n, [<Int n, Int 1>]~.

Lemma ratI : ∀ m n : nat, [<Int m, Int (S n)>]~ ∈ ℚ.
Proof. intros. apply pQuotI; nauto. Qed.
Global Hint Immediate ratI : number_hint.

Lemma rat_n : ∀ n, Rat n ∈ ℚ.
Proof. intros. unfold Rat. nauto. Qed.
Global Hint Immediate rat_n : number_hint.

Example ratAdd_1_2 : Rat 1 + Rat 2 = Rat 3.
Proof with nauto.
  unfold Rat. rewrite ratAdd_a_b_c_d...
  rewrite intMul_ident, intMul_ident, intAdd_1_2...
Qed.

Theorem ratAdd_comm : ∀ r s ∈ ℚ, r + s = s + r.
Proof with auto.
  intros r Hr s Hs.
  apply pQuotE in Hr as [a [Ha [b [Hb Hr]]]]. subst r.
  apply pQuotE in Hs as [c [Hc [d [Hd Hs]]]]. subst s.
  rewrite ratAdd_a_b_c_d, ratAdd_a_b_c_d; [|auto..].
  rewrite (intAdd_comm (a⋅d)%z), (intMul_comm d); auto;nz;mr;nz.
Qed.

Theorem ratAdd_assoc : ∀ q r s ∈ ℚ,
  (q + r) + s = q + (r + s).
Proof with auto.
  intros q Hq r Hr s Hs.
  apply pQuotE in Hq as [a [Ha [b [Hb Hq]]]]. subst q.
  apply pQuotE in Hr as [c [Hc [d [Hd Hr]]]]. subst r.
  apply pQuotE in Hs as [e [He [f [Hf Hs]]]]. subst s.
  repeat rewrite ratAdd_a_b_c_d;
    try assumption; [|amr|nzmr|amr|nzmr]; nz.
  erewrite intMul_distr', intMul_distr', intAdd_assoc,
    (intMul_assoc a), (intMul_assoc b),
    (intMul_assoc e), (intMul_assoc c), (intMul_assoc c),
    (intMul_comm f), (intMul_comm d _ b);
    [auto|try mr; try mr; auto; nz..]. Unshelve. nz.
Qed.

Theorem ratAdd_ident : ∀r ∈ ℚ, r + Rat 0 = r.
Proof.
  intros r Hr.
  apply pQuotE in Hr as [a [Ha [b [Hb Hr]]]]. subst r.
  unfold Rat. rewrite ratAdd_a_b_c_d, intMul_ident, intMul_ident,
    intMul_0_l, intAdd_ident; nauto; nz.
Qed.

Corollary ratAdd_ident' : ∀r ∈ ℚ, Rat 0 + r = r.
Proof.
  intros r Hr. rewrite ratAdd_comm, ratAdd_ident; nauto.
Qed.

Theorem ratAddInv_exists : ∀r ∈ ℚ, ∃s ∈ ℚ, r + s = Rat 0.
Proof with nauto.
  intros r Hr. apply pQuotE in Hr as [a [Ha [b [Hb Hr]]]].
  assert ((-a)%z ∈ ℤ) by (apply intAddInv_ran; auto).
  exists ([<(-a)%z, b>]~). split. apply pQuotI...
  subst r. rewrite ratAdd_a_b_c_d...
  apply rat_ident... amr;nz. nzmr.
  rewrite intMul_ident, intMul_0_l, intMul_addInv_l,
    intAddInv_annih... mr;nz. nz. mr;nz. ar;mr;nz.
Qed.

Theorem ratAddInv_unique : ∀r ∈ ℚ, ∃!s, s ∈ ℚ ∧ r + s = Rat 0.
Proof with auto.
  intros r Hr. rewrite <- unique_existence.
  split. apply ratAddInv_exists...
  intros s s' [Hs H1] [Hs' H2].
  rewrite <- (ratAdd_ident s), <- (ratAdd_ident s')...
  rewrite <- H2 at 1. rewrite <- H1.
  rewrite <- ratAdd_assoc, (ratAdd_comm r), (ratAdd_comm s')...
  apply ratAdd_ran...
Qed.

Close Scope Rat_scope.
Open Scope Int_scope.

Lemma intAddInv_inzInt : ∀a ∈ ℤ', -a ∈ ℤ'.
Proof with nauto.
  intros a Ha'. apply nzIntE1 in Ha' as Ha.
  apply pQuotE in Ha as [m [Hm [n [Hn Heq]]]]. subst a.
  rewrite intAddInv... apply nzIntI0. apply pQuotI...
  apply nzIntE0 in Ha' as Hnq0. intros H0. apply Hnq0.
  apply int_ident in H0... rewrite add_ident, add_ident' in H0... subst.
  apply int_ident... rewrite add_ident, add_ident'...
Qed.

Lemma planeEquiv_intAddInv : ∀ a b c d,
  <a, b> ~ <c, d> → <a, b> ~ < -c, -d>.
Proof with auto.
  intros. apply planeEquivE2 in H as [H [Ha [Hb [Hc Hd]]]].
  apply planeEquivI... apply intAddInv_ran...
  apply intAddInv_inzInt... unfold RatEq in *.
  rewrite intMul_addInv_l, intMul_addInv_r; nz... congruence.
Qed.

(* 有理数投射 *)
Definition PosDenoms := λ r,
  {p ∊ r | intPos (π2 p)}.
Definition NatDenoms := λ r,
  {π1 (IntProj (π2 p)) | p ∊ PosDenoms r}.
Definition MinNatDenom := λ r,
  (Min Lt)[NatDenoms r].
Definition PreRatProj := λ r,
  {p ∊ PosDenoms r | π2 p = ω_Embed[MinNatDenom r]}.
Definition RatProj := λ r,
  ⋃ (PreRatProj r).

Lemma posDenoms_nonempty : ∀a ∈ ℤ, ∀b ∈ ℤ',
  ⦿ PosDenoms ([<a, b>]~).
Proof with nauto.
  intros a Ha b Hb.
  destruct ratEquiv_equiv as [_ [Hrefl _]].
  apply nzIntE0 in Hb as Hb0.
  apply intLt_connected in Hb0 as [Hnb|Hpb]; nz...
  - exists < -a, -b>. apply SepI. apply eqvcI.
    apply planeEquiv_intAddInv. apply Hrefl. apply CProdI...
    zfc_simple. apply intNeg_pos...
  - exists <a, b>. apply SepI. apply eqvcI.
    apply Hrefl. apply CProdI... zfc_simple...
Qed.

Lemma natDenoms_nonempty : ∀a ∈ ℤ, ∀b ∈ ℤ',
  ⦿ NatDenoms ([<a, b>]~).
Proof with nauto.
  intros a Ha b Hb.
  pose proof (posDenoms_nonempty a Ha b Hb) as [s Hs].
  apply SepE in Hs as [Hs Hpos].
  apply eqvcE in Hs. apply planeEquivE1 in Hs
    as [a' [Ha' [b' [Hb' [c [Hc [d [Hd [H1 [H2 H3]]]]]]]]]].
  apply op_iff in H1 as []; subst a' b' s. zfc_simple.
  exists (π1 (IntProj d)). apply ReplAx.
  exists <c, d>. split; zfc_simple.
  apply SepI. apply eqvcI. apply planeEquiv... zfc_simple.
Qed.

Lemma natDenoms_is_nats : ∀a ∈ ℤ, ∀b ∈ ℤ',
  NatDenoms ([<a, b>]~) ⊆ ω.
Proof with nauto.
  intros a Ha b Hb n Hn.
  apply ReplAx in Hn as [s [Hs Heq]].
  apply SepE1 in Hs. apply eqvcE in Hs.
  apply planeEquivE1 in Hs
    as [a' [Ha' [b' [Hb' [c [Hc [d [Hd [H1 [H2 _]]]]]]]]]].
  apply op_iff in H1 as []; subst a' b' s n. zfc_simple.
  apply SepE1 in Hd.
  apply pQuotE in Hd as [m [Hm [n [Hn Hd]]]]. subst d.
  pose proof (intProj m Hm n Hn) as [p [Hp [q [Hq [H1 _]]]]].
  rewrite H1. zfc_simple.
Qed.

Lemma natDenoms : ∀a ∈ ℤ, ∀b ∈ ℤ', ∀n ∈ NatDenoms ([<a, b>]~),
  ∃c ∈ ℤ, <a, b> ~ <c, ω_Embed[n]> ∧ intPos ω_Embed[n].
Proof with nauto.
  intros a Ha b Hb n Hn.
  apply ReplAx in Hn as [s [Hs Heq]].
  apply SepE in Hs as [Hs Hpos]. apply eqvcE in Hs.
  apply planeEquivE1 in Hs
    as [a' [Ha' [b' [Hb' [c [Hc [d [Hd [H1 [H2 H3]]]]]]]]]].
  apply op_iff in H1 as []; subst a' b' s n. zfc_simple.
  exists c. split... apply SepE in Hd as [Hd Hd'].
  apply pQuotE in Hd as [m [Hm [n [Hn Hd]]]]. subst d.
  pose proof (intProj m Hm n Hn) as [p [Hp [q [Hq [H1 [H2 H0]]]]]].
  rewrite H1. zfc_simple. rewrite ω_embed_n...
  cut ([<p, 0>]~%pz = [<m, n>]~%pz). {
    intros. rewrite H. split...
    apply planeEquiv... apply SepI... apply pQuotI...
  }
  apply planeEquiv in H2... unfold IntEq in H2.
  apply int_ident... destruct H0; subst...
  exfalso. destruct (classic (q = 0)); subst.
  - apply SingNE in Hd'. apply Hd'. apply int_ident...
  - apply intLt in Hpos...
    rewrite add_ident, add_ident' in Hpos...
    rewrite add_ident' in H2... rewrite <- H2 in Hpos.
    rewrite <- (add_ident m) in Hpos at 2...
    apply add_preserve_lt' in Hpos... exfalso0.
Qed.

Lemma preRatProjE : ∀a ∈ ℤ, ∀b ∈ ℤ', ∀x ∈ PreRatProj ([<a, b>]~),
  ∃c ∈ ℤ, ∃d ∈ ℤ', x = <c, d> ∧ <a, b> ~ <c, d> ∧
    d = ω_Embed[MinNatDenom ([<a, b>]~)] ∧ intPos d.
Proof with auto.
  intros a Ha b Hb x Hx.
  apply SepE in Hx as [Hx Heq].
  apply SepE in Hx as [Hx Hpos].
  apply eqvcE in Hx. apply planeEquivE1 in Hx
    as [a' [Ha' [b' [Hb' [c [Hc [d [Hd [H1 [H2 H3]]]]]]]]]].
  apply op_iff in H1 as []; subst a' b' x. zfc_simple.
  exists c. split... exists d. split...
  split... split... apply planeEquivI...
Qed.

Lemma preRatProj_unique : ∀r ∈ ℚ, ∃! p, p ∈ PreRatProj r.
Proof with neauto; try congruence.
  intros r Hr.
  apply pQuotE in Hr as [a [Ha [b [Hb Hr]]]].
  subst r. rewrite <- unique_existence. split.
  - set (MinNatDenom ([<a, b>]~)) as n.
    pose proof (natDenoms a Ha b Hb n) as [c [Hc [Heq Hpos]]].
    apply ω_min. apply natDenoms_nonempty...
    apply natDenoms_is_nats...
    exists <c, ω_Embed[n]>. apply SepI. apply SepI.
    apply eqvcI... zfc_simple. zfc_simple. reflexivity.
  - intros x1 x2 H1 H2.
    apply preRatProjE in H1 as [c1 [Hc1 [d1 [Hd1 [H11 [H12 [H13 _]]]]]]]...
    apply preRatProjE in H2 as [c2 [Hc2 [d2 [Hd2 [H21 [H22 [H23 _]]]]]]]...
    subst x1 x2. apply op_iff. split...
    assert (RatEq c1 d1 c2 d1). {
      rewrite H23, <- H13 in H22.
      apply planeEquiv in H12...
      apply planeEquiv in H22...
      eapply ratEqTran; revgoals...
    }
    apply SepE in Hd1 as [H1 H2].
    apply intMul_cancel in H... apply SingNE in H2...
Qed.

Lemma preRatProj : ∀r ∈ ℚ, ∃p, PreRatProj r = ⎨p⎬.
Proof with auto.
  intros r Hr.
  apply preRatProj_unique in Hr as [p [Hp Hu]].
  exists p. apply ExtAx. split; intros Hx.
  - cut (p = x). intros Heq. subst... apply Hu...
  - apply SingE in Hx. subst...
Qed.

Lemma ratProj : ∀a ∈ ℤ, ∀b ∈ ℤ', ∃c ∈ ℤ, ∃d ∈ ℤ',
  RatProj ([<a, b>]~) = <c, d> ∧ <a, b> ~ <c, d> ∧
  (a ∈ ℤ' → c ∈ ℤ') ∧ intPos d.
Proof with auto.
  intros a Ha b Hb.
  pose proof (preRatProj ([<a, b>]~)) as [x Hsg].
  apply pQuotI... assert (Hx: x ∈ ⎨x⎬) by apply SingI.
  rewrite <- Hsg in Hx. apply preRatProjE in Hx
    as [c [Hc [d [Hd [Hx [H1 [H2 H3]]]]]]]...
  exists c. split... exists d. repeat split...
  - rewrite <- Hx. unfold RatProj. rewrite Hsg.
    apply union_single.
  - intros Ha'. apply planeEquiv in H1... unfold RatEq in H1.
    assert (H: (a ⋅ d)%z ∈ ℤ') by (apply nzIntMul_ranI; auto).
    rewrite H1 in H. apply nzIntMul_ranE in H as []... nz.
Qed.

Global Opaque RatProj.

Lemma ratProj_η : ∀r ∈ ℚ, r = [RatProj r]~.
Proof with auto.
  intros r Hr.
  apply pQuotE in Hr as [a [Ha [b [Hb Hr]]]].
  pose proof (ratProj a Ha b Hb)
    as [c [Hc [d [Hd [H1 [H2 _]]]]]].
  apply planeEquiv in H2... unfold RatEq. subst r.
  rewrite H1. apply rat_ident...
Qed.

Close Scope Int_scope.
Open Scope Rat_scope.

(** 有理数加法逆元 **)
Definition RatAddInv : set → set := λ r,
  let p := (RatProj r) in [<(-π1 p)%z, π2 p>]~.
Notation "- a" := (RatAddInv a) : Rat_scope.
Notation "a - b" := (a + (-b)) : Rat_scope.

Lemma ratAddInv : ∀a ∈ ℤ, ∀b ∈ ℤ', (-[<a, b>]~) = [<(-a)%z, b>]~.
Proof with eauto.
  intros a Ha b Hb.
  pose proof (ratProj a Ha b Hb) as [c [Hc [d [Hd [H1 [H2 _]]]]]].
  assert (Hna: (-a)%z ∈ ℤ) by (apply intAddInv_ran; auto).
  assert (Hnc: (-c)%z ∈ ℤ) by (apply intAddInv_ran; auto).
  destruct ratEquiv_equiv as [_ [_ [_ Htr]]].
  apply ExtAx. split; intros Hx.
  - apply eqvcE in Hx. rewrite H1 in Hx. zfc_simple.
    apply eqvcI. cut (<(-a)%z, b> ~ <(-c)%z, d>). intros.
    eapply Htr; [apply H|..]... apply planeEquivI... unfold RatEq.
    apply planeEquiv in H2; [|auto..]. unfold RatEq in H2.
    rewrite intMul_addInv_l, intMul_addInv_l; nz; [|auto..]. congruence.
  - apply eqvcI. rewrite H1. zfc_simple.
    apply eqvcE in Hx. cut (<(-c)%z, d> ~ <(-a)%z, b>). intros.
    eapply Htr; [apply H|..]... apply planeEquivI... unfold RatEq.
    apply planeEquiv in H2; [|auto..]. unfold RatEq in H2.
    rewrite intMul_addInv_l, intMul_addInv_l; nz; [|auto..]. congruence.
Qed.

Global Opaque RatAddInv.

Lemma ratAddInv_double : ∀r ∈ ℚ, --r = r.
Proof with auto.
  intros r Hr.
  apply pQuotE in Hr as [a [Ha [b [Hb Hr]]]]. subst r.
  rewrite ratAddInv, ratAddInv, intAddInv_double...
  apply intAddInv_ran...
Qed.

Lemma ratAddInv_ran : ∀r ∈ ℚ, -r ∈ ℚ.
Proof with auto.
  intros r Hr.
  apply pQuotE in Hr as [a [Ha [b [Hb Heq]]]]. subst r.
  rewrite ratAddInv... apply pQuotI... apply intAddInv_ran...
Qed.

Lemma neg_rat_n : ∀ n, -Rat n ∈ ℚ.
Proof. intros. apply ratAddInv_ran. nauto. Qed.
Global Hint Immediate neg_rat_n : number_hint.

Lemma ratAddInv_0 : -Rat 0 = Rat 0.
Proof. unfold Rat. rewrite ratAddInv, intAddInv_0; nauto. Qed.

Lemma ratAddInv_annih : ∀r ∈ ℚ, r - r = Rat 0.
Proof with nauto.
  intros r Hr.
  apply pQuotE in Hr as [a [Ha [b [Hb Hr]]]]. subst r.
  assert (Hna: (-a)%z ∈ ℤ) by (apply intAddInv_ran; auto).
  rewrite ratAddInv, ratAdd_a_b_c_d...
  apply rat_ident... amr;nz. nzmr.
  rewrite intMul_ident, intMul_0_l, intMul_addInv_l,
    intAddInv_annih; auto; nz; [mr|mr|amr]; nz.
Qed.

Example ratAdd_2_n3 : Rat 2 - Rat 3 = -Rat 1.
Proof with nauto.
  unfold Rat. rewrite ratAddInv, ratAddInv, ratAdd_a_b_c_d...
  rewrite intMul_ident, intMul_ident, intMul_ident, intAdd_2_n3...
Qed.

Close Scope Rat_scope.
Open Scope Int_scope.

(** 有理数乘法 **)
Definition PreRatMul : set :=
  PlaneArith ℤ ℤ' (λ a b c d, <a ⋅ c, b ⋅ d>).
Notation "r ⋅ᵥ s" := (PreRatMul[<r, s>])
  (at level 50) : PreRat_scope.

Lemma preRatMul_maps_onto : PreRatMul: (ℤ × ℤ')² ⟹ ℤ × ℤ'.
Proof with neauto.
  apply planeArith_maps_onto.
  - intros a Ha b Hb c Hc d Hd. apply CProdI; [mr|nzmr].
  - intros r Hr s Hs.
    exists r. split... exists s. split...
    exists (Int 1). split... exists (Int 1). split...
    rewrite intMul_ident, intMul_ident; nz...
Qed.

Lemma preRatMul_a_b_c_d : ∀a ∈ ℤ, ∀b ∈ ℤ', ∀c ∈ ℤ, ∀d ∈ ℤ',
  <a, b> ⋅ᵥ <c, d> = <a ⋅ c, b ⋅ d>.
Proof with auto.
  intros a Ha b Hb c Hc d Hd.
  eapply func_ap. destruct preRatMul_maps_onto...
  apply SepI. apply CProdI; apply CProdI.
  apply CProdI... apply CProdI... mr. nzmr. zfc_simple...
Qed.

Lemma preRatMul_binCompatible :
  binCompatible (PlaneEquiv ℤ ℤ' RatEq) (ℤ × ℤ') PreRatMul.
Proof with auto.
  split. apply ratEquiv_equiv. split.
  destruct preRatMul_maps_onto as [Hf [Hd Hr]].
  split... split... rewrite Hr. apply sub_refl.
  intros x Hx y Hy u Hu v Hv H1 H2.
  apply CProdE1 in Hx as [a [Ha [b [Hb Hxeq]]]].
  apply CProdE1 in Hy as [c [Hc [d [Hd Hyeq]]]].
  apply CProdE1 in Hu as [a' [Ha' [b' [Hb' Hueq]]]].
  apply CProdE1 in Hv as [c' [Hc' [d' [Hd' Hveq]]]]. subst.
  apply planeEquiv in H1... apply planeEquiv in H2...
  rewrite preRatMul_a_b_c_d, preRatMul_a_b_c_d...
  apply SepI. apply CProdI; apply CProdI; try mr; try nzmr.
  zfc_simple. simpl. unfold RatEq in *.
  rewrite
    (intMul_assoc a), (intMul_comm c),
    (intMul_assoc b'), <- (intMul_assoc a),
    (intMul_assoc a'), (intMul_comm c'),
    (intMul_assoc b), <- (intMul_assoc a'),
    (intMul_comm d'), (intMul_comm d);
    [congruence|auto;try mr;nz..].
Qed.

Close Scope Int_scope.
Open Scope Rat_scope.

(** 有理数乘法 **)
Definition RatMul : set :=
  QuotionFunc (PlaneEquiv ℤ ℤ' RatEq) (ℤ × ℤ') PreRatMul.
Notation "r ⋅ s" := (RatMul[<r, s>]) : Rat_scope.

Lemma ratMul_maps_onto : RatMul: ℚ × ℚ ⟹ ℚ.
Proof.
  apply quotionFunc_maps_onto.
  apply preRatMul_binCompatible.
  apply preRatMul_maps_onto.
Qed.

Lemma ratMul_r_s : ∀ r s ∈ (ℤ × ℤ'), [r]~ ⋅ [s]~ = [r ⋅ᵥ s]~.
Proof.
  intros r Hr s Hs. apply binCompatibleE; auto.
  apply preRatMul_binCompatible.
Qed.

Global Opaque RatMul.

Lemma ratMul_a_b_c_d : ∀a ∈ ℤ, ∀b ∈ ℤ', ∀c ∈ ℤ, ∀d ∈ ℤ',
  [<a, b>]~ ⋅ [<c, d>]~ = ([<a ⋅ c, b ⋅ d>]~)%z.
Proof with auto.
  intros a Ha b Hb c Hc d Hd.
  rewrite ratMul_r_s, preRatMul_a_b_c_d...
  apply CProdI... apply CProdI...
Qed.

Lemma ratMul_0_r : ∀r ∈ ℚ, r ⋅ Rat 0 = Rat 0.
Proof with nauto.
  intros r Hr.
  apply pQuotE in Hr as [a [Ha [b [Hb Hr]]]]. subst r.
  unfold Rat. rewrite ratMul_a_b_c_d...
  apply rat_ident... mr. nzmr.
  rewrite intMul_0_r, intMul_ident, intMul_0_l...
  rewrite intMul_ident; nz.
Qed.

Lemma ratMul_ran : ∀ r s ∈ ℚ, r ⋅ s ∈ ℚ.
Proof with auto.
  intros r Hr s Hs.
  apply pQuotE in Hr as [a [Ha [b [Hb Hr]]]]. subst r.
  apply pQuotE in Hs as [c [Hc [d [Hd Hs]]]]. subst s.
  rewrite ratMul_a_b_c_d... apply pQuotI; [mr|nzmr].
Qed.

Example ratMul_2_n2 : Rat 2 ⋅ -Rat 2 = -Rat 4.
Proof with nauto.
  unfold Rat. rewrite ratAddInv, ratAddInv, ratMul_a_b_c_d...
  rewrite intMul_2_n2, intMul_ident...
Qed.

Theorem ratMul_comm : ∀ q r ∈ ℚ, q ⋅ r = r ⋅ q.
Proof with auto.
  intros q Hq r Hr.
  apply pQuotE in Hq as [a [Ha [b [Hb Hq]]]].
  apply pQuotE in Hr as [c [Hc [d [Hd Hr]]]]. subst.
  rewrite ratMul_a_b_c_d, ratMul_a_b_c_d...
  rewrite intMul_comm, (intMul_comm b); nz...
Qed.

Theorem ratMul_assoc : ∀ p q r ∈ ℚ,
  (p ⋅ q) ⋅ r = p ⋅ (q ⋅ r).
Proof with auto.
  intros p Hp q Hq r Hr.
  apply pQuotE in Hp as [a [Ha [b [Hb Hp]]]]. subst p.
  apply pQuotE in Hq as [c [Hc [d [Hd Hq]]]]. subst q.
  apply pQuotE in Hr as [e [He [f [Hf Hr]]]]. subst r.
  repeat rewrite ratMul_a_b_c_d; [|auto;try mr;try nzmr..].
  rewrite intMul_assoc, (intMul_assoc b); auto; nz.
Qed.

Theorem ratMul_distr : ∀ p q r ∈ ℚ, p ⋅ (q + r) = p ⋅ q + p ⋅ r.
Proof with auto.
  intros p Hp q Hq r Hr.
  apply pQuotE in Hp as [a [Ha [b [Hb Hp]]]].
  apply pQuotE in Hq as [c [Hc [d [Hd Hq]]]].
  apply pQuotE in Hr as [e [He [f [Hf Hr]]]]. subst.
  rewrite (ratAdd_a_b_c_d c Hc d Hd e He f Hf).
  rewrite (ratMul_a_b_c_d a Ha b Hb c Hc d Hd).
  rewrite (ratMul_a_b_c_d a Ha b Hb e He f Hf).
  rewrite ratMul_a_b_c_d; [|auto..|amr;nz|nzmr].
  rewrite ratAdd_a_b_c_d; [|try mr;try nzmr..].
  erewrite
    (intMul_assoc a), (intMul_comm c Hc (b⋅f)%z),
    (intMul_assoc b), <- (intMul_assoc a), (intMul_comm f),
    (intMul_assoc a Ha e), (intMul_comm e He (b⋅d)%z),
    (intMul_assoc b _ d), <- (intMul_assoc a Ha b),
    (intMul_comm d _ e), <- (intMul_distr),
    (intMul_comm a Ha b), (intMul_assoc b), (intMul_assoc b),
    <- (intMul_assoc d), (intMul_comm d _ b), (intMul_assoc b);
    [|auto;nz..]; [|mr;nz|amr;nz|mr;nz..].
  cut (∀a ∈ ℤ, ∀b ∈ ℤ', ∀c ∈ ℤ' , [<a, b>]~ = [(<c⋅a, c⋅b>)%z]~).
  intros H. apply H; auto; [mr|nzmr]; [amr|nzmr]; nz. clear.
  intros a Ha b Hb c Hc. apply rat_ident; auto; [mr;nz|nzmr|].
  rewrite <- (intMul_assoc a), (intMul_comm a); nz...
  Unshelve. nz. nz. nz.
Qed.

Corollary ratMul_distr' : ∀ p q r ∈ ℚ, (q + r) ⋅ p = q ⋅ p + r ⋅ p.
Proof with auto.
  intros p Hp q Hq r Hr.
  rewrite (ratMul_comm (q + r)), ratMul_distr...
  rewrite (ratMul_comm p Hp q Hq), (ratMul_comm p Hp r Hr)...
  apply ratAdd_ran...
Qed.

Lemma ratMul_ident : ∀r ∈ ℚ, r ⋅ Rat 1 = r.
Proof with nauto.
  intros r Hr.
  apply pQuotE in Hr as [a [Ha [b [Hb Hr]]]]. subst r.
  unfold Rat. rewrite ratMul_a_b_c_d...
  rewrite intMul_ident, intMul_ident; nz...
Qed.

Lemma ratMul_ident' : ∀r ∈ ℚ, Rat 1 ⋅ r = r.
Proof.
  intros a Ha. rewrite ratMul_comm, ratMul_ident; nauto.
Qed.

Lemma ratMul_addInv : ∀r ∈ ℚ, -Rat 1 ⋅ r = -r.
Proof with nauto.
  intros r Hr.
  apply pQuotE in Hr as [a [Ha [b [Hb Hr]]]]. subst r.
  unfold Rat. rewrite ratAddInv, ratAddInv, ratMul_a_b_c_d...
  rewrite intMul_addInv, (intMul_comm (Int 1)),
    intMul_ident; nz...
Qed.

Lemma ratMul_0_l : ∀s ∈ ℚ, Rat 0 ⋅ s = Rat 0.
Proof.
  intros s Hs. rewrite ratMul_comm, ratMul_0_r; nauto.
Qed.

Lemma zRat_zInt : ∀a ∈ ℤ, ∀b ∈ ℤ', [<a, b>]~ = Rat 0 → a = Int 0.
Proof with nauto.
  unfold Rat. intros a Ha b Hb H0.
  apply rat_ident in H0...
  rewrite intMul_ident, intMul_0_l in H0; nz...
Qed.

Lemma zInt_zRat : ∀a ∈ ℤ, ∀b ∈ ℤ', a = Int 0 → [<a, b>]~ = Rat 0.
Proof with nauto.
  unfold Rat. intros a Ha b Hb H0. subst a.
  apply rat_ident... rewrite intMul_0_l, intMul_0_l; nz...
Qed.

Lemma nzRat_nzInt : ∀a ∈ ℤ, ∀b ∈ ℤ', [<a, b>]~ ≠ Rat 0 → a ≠ Int 0.
Proof with auto.
  intros a Ha b Hb Hnq0. intros H0. apply Hnq0. apply zInt_zRat...
Qed.

Lemma nzInt_nzRat : ∀a ∈ ℤ, ∀b ∈ ℤ', a ≠ Int 0 → [<a, b>]~ ≠ Rat 0.
Proof with eauto.
  intros a Ha b Hb Hnq0. intros H0. apply Hnq0. eapply zRat_zInt...
Qed.

(* 非零有理数 *)
Definition ℚ' := (ℚ - ⎨Rat 0⎬)%set.

Lemma nzRatI0 : ∀r ∈ ℚ, r ≠ Rat 0 → r ∈ ℚ'.
Proof with auto.
  intros a Ha Hnq0. apply CompI... apply SingNI...
Qed.

Lemma nzRatI1 : ∀ n : nat, [<Int (S n), Int 1>]~ ∈ ℚ'.
Proof with neauto.
  intros. apply CompI... apply SingNI.
  intros H. apply rat_ident in H...
  rewrite intMul_ident, intMul_ident in H...
  eapply int_suc_neq_0...
Qed.
Global Hint Immediate nzRatI1 : number_hint.

Lemma nzRatI2 : ∀ a b ∈ ℤ', [<a, b>]~ ∈ ℚ'.
Proof with auto.
  intros a Ha b Hb. apply nzRatI0.
  apply pQuotI; nz... apply nzInt_nzRat; nz... apply nzIntE0...
Qed.

Lemma nzRatE0 : ∀r ∈ ℚ', r ≠ Rat 0.
Proof with auto.
  intros a Ha H0. apply CompE in Ha as [_ Ha].
  apply SingNE in Ha...
Qed.

Lemma nzRatE1 : ∀r ∈ ℚ', r ∈ ℚ.
Proof with auto.
  intros a Ha. apply CompE in Ha as [Ha _]...
Qed.

Lemma nzRatE2 : ∀r ∈ ℚ', ∃ a b ∈ ℤ', r = [<a, b>]~.
Proof with auto.
  intros r Hr. apply nzRatE0 in Hr as Hnq0. apply nzRatE1 in Hr.
  apply pQuotE in Hr as [a [Ha [b [Hb Hr]]]]. subst r.
  apply nzRat_nzInt in Hnq0...
  exists a. split. apply nzIntI0... exists b. split...
Qed.

Lemma rat_suc_neq_0 : ∀ n, Rat (S n) ≠ Rat 0.
Proof with neauto.
  intros n H. apply rat_ident in H...
  rewrite intMul_ident, intMul_ident in H...
  eapply int_suc_neq_0...
Qed.
Global Hint Immediate rat_suc_neq_0 : number_hint.

Lemma rat_sn : ∀ n, Rat (S n) ∈ ℚ'.
Proof.
  intros. apply CompI; nauto.
  apply SingNI. apply rat_suc_neq_0.
Qed.
Global Hint Immediate rat_sn : number_hint.

Local Ltac nz_q := try (apply nzRatE1; assumption).

Theorem ratMulInv_exists : ∀r ∈ ℚ', ∃q ∈ ℚ', r ⋅ q = Rat 1.
Proof with auto.
  intros r Hr.
  apply nzRatE2 in Hr as [a [Ha [b [Hb Hr]]]]. subst r.
  exists ([<b, a>]~). split.
  - apply nzRatI2...
  - rewrite ratMul_a_b_c_d; nz... unfold Rat.
    apply rat_ident; nauto; [mr;nz|nzmr|].
    rewrite intMul_ident, intMul_ident', intMul_comm;
      auto; nz; mr; nz.
Qed.

Theorem ratMulInv_unique : ∀r ∈ ℚ', ∃!q, q ∈ ℚ' ∧ r ⋅ q = Rat 1.
Proof with auto.
  intros r Hr. rewrite <- unique_existence. split.
  pose proof (ratMulInv_exists r Hr)...
  intros q q' [Hq H1] [Hq' H2].
  rewrite <- (ratMul_ident q), <- (ratMul_ident q'); nz_q...
  rewrite <- H2 at 1. rewrite <- H1.
  rewrite <- ratMul_assoc, (ratMul_comm r), (ratMul_comm q'); nz_q...
  apply ratMul_ran; nz_q...
Qed.

Lemma nzRatMul_ran : ∀ r s ∈ ℚ', r ⋅ s ∈ ℚ'.
Proof with neauto.
  intros r Hr s Hs.
  apply nzRatI0. apply ratMul_ran; nz_q...
  assert (Hr' := Hr). assert (Hs' := Hs).
  apply ratMulInv_exists in Hr' as [r' [Hr' Hr1]].
  apply ratMulInv_exists in Hs' as [s' [Hs' Hs1]].
  assert ((r ⋅ r') ⋅ (s ⋅ s') = Rat 1). {
    rewrite Hr1, Hs1, ratMul_ident...
  }
  rewrite ratMul_assoc, (ratMul_comm r'),
    (ratMul_assoc s), <- ratMul_assoc in H; nz_q;
    [|apply ratMul_ran;nz_q..].
  destruct (classic (r ⋅ s = Rat 0))...
  rewrite H0 in H. rewrite ratMul_0_l in H.
  exfalso. eapply rat_suc_neq_0. symmetry. apply H.
  apply ratMul_ran; nz_q.
Qed.

Theorem rat_no_0_div : ∀ r s ∈ ℚ,
  r ⋅ s = Rat 0 → r = Rat 0 ∨ s = Rat 0.
Proof with auto.
  intros r Hr s Hs H0.
  destruct (classic (r = Rat 0)) as [|Hr'];
  destruct (classic (s = Rat 0)) as [|Hs']... exfalso.
  apply nzRatI0 in Hr'... apply nzRatI0 in Hs'...
  pose proof (nzRatMul_ran r Hr' s Hs'). apply nzRatE0 in H...
Qed.

(** 有理数乘法逆元 **)
Definition RatMulInv : set → set := λ r,
  let p := (RatProj r) in [<π2 p, π1 p>]~.
Notation "a ⁻¹" := (RatMulInv a) : Rat_scope.
Notation "a / b" := (a ⋅ b⁻¹) : Rat_scope.

Lemma ratMulInv : ∀a ∈ ℤ', ∀b ∈ ℤ', ([<a, b>]~)⁻¹ = [<b, a>]~.
Proof with eauto.
  intros a Ha' b Hb'. apply nzIntE1 in Ha' as Ha.
  pose proof (ratProj a Ha b Hb') as [c [Hc [d [Hd [H1 [H2 [H3 _]]]]]]].
  unfold RatMulInv. rewrite H1. zfc_simple. apply rat_ident; nz...
  apply planeEquivE2 in H2 as [H2 _]. unfold RatEq in H2.
  rewrite intMul_comm, (intMul_comm b); nz...
Qed.

Global Opaque RatMulInv.

Lemma ratMulInv_double : ∀r ∈ ℚ', r⁻¹⁻¹ = r.
Proof with auto.
  intros r Hr.
  apply nzRatE2 in Hr as [a [Ha [b [Hb Hr]]]]. subst r.
  rewrite ratMulInv, ratMulInv...
Qed.

Lemma ratMulInv_ran : ∀r ∈ ℚ', r⁻¹ ∈ ℚ'.
Proof with auto.
  intros r Hr.
  apply nzRatE2 in Hr as [a [Ha [b [Hb Hr]]]]. subst r.
  rewrite ratMulInv... apply nzRatI2...
Qed.

Lemma rat_sn_mulInv : ∀ n, (Rat (S n))⁻¹ ∈ ℚ.
Proof. intros. unfold Rat. rewrite ratMulInv; nauto. Qed.
Global Hint Immediate rat_sn_mulInv : number_hint.

Lemma ratMulInv_1 : (Rat 1)⁻¹ = Rat 1.
Proof. unfold Rat. rewrite ratMulInv; nauto. Qed.

Lemma ratMulInv_annih : ∀r ∈ ℚ', r / r = Rat 1.
Proof with nauto.
  intros r Hr.
  apply nzRatE2 in Hr as [a [Ha [b [Hb Hr]]]]. subst r.
  rewrite ratMulInv, ratMul_a_b_c_d; nz...
  apply rat_ident... mr;nz. nzmr.
  rewrite intMul_ident, intMul_ident', intMul_comm;
    auto; nz; mr; nz.
Qed.

Example ratMul_n4_r2 : -Rat 4 / Rat 2 = -Rat 2.
Proof.
  unfold Rat. rewrite ratAddInv, ratAddInv, ratMulInv,
    ratMul_a_b_c_d; [|nauto..].
  unfold Int. rewrite intAddInv, intAddInv,
    intMul_m_n_p_q, intMul_m_n_p_q,
    mul_ident, mul_ident, mul_0_r, mul_0_r,
    (mul_comm 1), mul_ident, mul_0_r, mul_0_l,
    add_ident, add_ident, add_ident'; [|nauto..].
  apply rat_ident; [nauto..|].
  rewrite intMul_m_n_p_q, intMul_m_n_p_q,
    mul_0_l, mul_0_l, mul_0_l, mul_0_r, mul_0_r,
    mul_ident, mul_2_2, add_ident', add_ident'; [|nauto..].
  reflexivity.
Qed.

Example ratAdd_r2_r2_1 : (Rat 2) ⁻¹ + (Rat 2) ⁻¹ = Rat 1.
Proof with nauto.
  unfold Rat. repeat rewrite ratMulInv...
  rewrite ratAdd_a_b_c_d, intMul_ident'...
  unfold Int. rewrite intAdd_m_n_p_q, intMul_m_n_p_q...
  rewrite mul_0_l, mul_0_l, mul_0_r, add_ident...
  replace (2 + 2)%ω with (Embed 4).
  replace (2 ⋅ 2)%ω with (Embed 4).
  rewrite add_ident... apply rat_ident...
  rewrite intMul_m_n_p_q, intMul_m_n_p_q; [|nauto..].
  repeat rewrite mul_0_l; [|nauto..].
  repeat rewrite mul_0_r; [|nauto..].
  rewrite mul_ident, (mul_comm 1), mul_ident...
  rewrite (pred 2), mul_suc, mul_ident, add_suc, <- suc;
    repeat apply ω_inductive...
  rewrite (pred 2), add_suc, <- suc;
    repeat apply ω_inductive...
Qed.

Example ratAdd_r6_r3_r2 : (Rat 6) ⁻¹ + (Rat 3) ⁻¹ = (Rat 2) ⁻¹.
Proof with nauto.
  unfold Rat. repeat rewrite ratMulInv...
  rewrite ratAdd_a_b_c_d, intMul_ident', intMul_ident'...
  unfold Int. rewrite intAdd_m_n_p_q, intMul_m_n_p_q...
  rewrite mul_0_l, mul_0_l, mul_0_r, add_ident...
  replace (3 + 6)%ω with (Embed 9).
  replace (6 ⋅ 3)%ω with (Embed 18).
  rewrite add_ident... apply rat_ident...
  rewrite intMul_m_n_p_q, intMul_m_n_p_q; [|nauto..].
  repeat rewrite mul_0_l; [|nauto..].
  repeat rewrite mul_0_r; [|nauto..].
  replace (9 ⋅ 2)%ω with (Embed 18).
  replace (1 ⋅ 18)%ω with (Embed 18).
  - repeat rewrite add_ident... - rewrite mul_comm, mul_ident...
  - repeat rewrite pred.
    repeat rewrite mul_suc; repeat apply ω_inductive...
    rewrite mul_0_r, add_ident; repeat apply ω_inductive...
    repeat rewrite add_suc; try rewrite add_ident;
      repeat apply ω_inductive...
  - repeat rewrite pred.
    repeat rewrite mul_suc; repeat apply ω_inductive...
    rewrite mul_0_r, add_ident; repeat apply ω_inductive...
    repeat (repeat rewrite add_suc; try rewrite add_ident;
      repeat apply ω_inductive)...
  - repeat rewrite pred.
    repeat rewrite add_suc; try rewrite add_ident;
      repeat apply ω_inductive...
Qed.
