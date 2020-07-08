(** Based on "Elements of Set Theory" Chapter 5 Part 3 **)
(** Coq coding by choukh, June 2020 **)

Require Export ZFC.EST5_2.

Local Ltac mr := apply intMul_ran; auto.
Local Ltac ar := apply intAdd_ran; auto.
Local Ltac amr := apply intAdd_ran; apply intMul_ran; auto.

(*** EST第五章3：有理数：加法，投射，加法逆元，减法，乘法，乘法逆元，除法 ***)

Lemma SingNI : ∀ A B, A ≠ B → A ∉ ⎨B⎬.
Proof with auto.
  intros * Hnq H. apply Hnq. apply SingE in H...
Qed.

Lemma SingNE : ∀ A B, A ∉ ⎨B⎬ → A ≠ B.
Proof with auto.
  intros * H Heq. apply H. subst A. apply SingI.
Qed.

(* 非零整数 *)
Definition ℤ' := (ℤ - ⎨Int 0⎬)%zfc.

Lemma int_has_1 : Int 1 ∈ ℤ.
Proof. apply pQuotI; auto. Qed.

Lemma nzInt_has_1 : Int 1 ∈ ℤ'.
Proof with auto.
  apply CompI... apply pQuotI...
  apply SingNI. intros H. apply int_0_neq_1...
Qed.

Hint Immediate int_has_1 : core.
Hint Immediate nzInt_has_1 : core.

Lemma nzIntI : ∀a ∈ ℤ, a ≠ Int 0 → a ∈ ℤ'.
Proof with auto.
  intros a Ha Hnq0. apply CompI... apply SingNI...
Qed.

Lemma nzIntE : ∀a ∈ ℤ', a ≠ Int 0.
Proof with auto.
  intros a Ha H0. apply CompE in Ha as [_ Ha].
  apply SingNE in Ha...
Qed.

Lemma nzInt : ∀a ∈ ℤ', a ∈ ℤ.
Proof with auto.
  intros a Ha. apply CompE in Ha as [Ha _]...
Qed.

Local Ltac nz := try (apply nzInt; assumption).

Lemma nzIntMul_ranI : ∀ a b ∈ ℤ', a ⋅ b ∈ ℤ'.
Proof with auto.
  intros a Ha b Hb.
  apply CompE in Ha as [Ha Ha0].
  apply CompE in Hb as [Hb Hb0].
  apply CompI. mr. intros H. apply SingE in H.
  apply int_no_0_div in H as []...
  apply Ha0. subst a. apply SingI.
  apply Hb0. subst b. apply SingI.
Qed.

Local Ltac amr_n := apply add_ran; apply mul_ran; auto.

Lemma nzIntMul_ranE : ∀ a b ∈ ℤ, a ⋅ b ∈ ℤ' → a ∈ ℤ' ∧ b ∈ ℤ'.
Proof with auto.
  intros a Ha b Hb Hab.
  apply pQuotE in Ha as [m [Hm [n [Hn Ha]]]]. subst a.
  apply pQuotE in Hb as [p [Hp [q [Hq Hb]]]]. subst b.
  rewrite intMul_m_n_p_q in Hab... apply nzIntE in Hab.
  split; (apply CompI; [apply pQuotI; auto|]); apply SingNI;
    intros H; apply Hab; clear Hab;
    apply int_ident in H; auto; rewrite add_0_r, add_0_l in H;
    subst; auto; apply int_ident; try amr_n...
  rewrite add_0_r, add_0_l, add_comm...
  apply mul_ran... apply mul_ran... amr_n. amr_n.
  rewrite add_0_r, add_0_l... amr_n. amr_n.
Qed.

Local Ltac nzmr := apply nzIntMul_ranI; auto.

Close Scope PreInt_scope.
Declare Scope PreRat_scope.
Open Scope PreRat_scope.

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
  eapply intMul_cancel; revgoals...
  intros Heq. apply Hd2. rewrite Heq. apply SingI. mr... mr...
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
  apply pQuot_ident.
  apply ratEqRefl. apply ratEqSymm. apply ratEqTran. 
Qed.

Definition PreRatAdd : set :=
  PlaneArith ℤ ℤ' (λ a b c d, <a⋅d + c⋅b, b⋅d>).
Notation "a +ᵥ b" := (PreRatAdd[<a, b>]) (at level 50) : PreRat_scope.

Lemma preRatAdd_maps_onto : PreRatAdd: (ℤ × ℤ')² ⟹ (ℤ × ℤ').
Proof with eauto.
  apply planeArith_maps_onto.
  - intros a Ha b Hb c Hc d Hd. apply CProdI. amr;nz. nzmr.
  - intros a Ha b Hb.
    exists a. split... exists b. split...
    exists (Int 0). split... exists (Int 1). split...
    apply CompE in Hb as [Hb _]. apply op_correct.
    rewrite intMul_ident, intMul_ident... split...
    rewrite intMul_comm, intMul_0_r, intAdd_ident...
Qed.

Lemma preRatAdd_a_b_c_d : ∀a ∈ ℤ, ∀b ∈ ℤ', ∀c ∈ ℤ, ∀d ∈ ℤ',
  <a, b> +ᵥ <c, d> = <a⋅d + c⋅b, b⋅d>.
Proof with auto.
  intros a Ha b Hb c Hc d Hd.
  eapply func_ap. destruct preRatAdd_maps_onto...
  apply SepI. apply CProdI; apply CProdI.
  apply CProdI... apply CProdI... amr;nz. nzmr. zfcrewrite...
Qed.

Lemma preRatAdd_binCompatible :
  binCompatible (PlaneEquiv ℤ ℤ' RatEq) (ℤ × ℤ') PreRatAdd.
Proof with eauto.
  split. apply ratEquiv_equiv. split.
  destruct preRatAdd_maps_onto as [Hf [Hd Hr]].
  split... split... rewrite Hr. apply sub_refl. 
  intros x Hx y Hy u Hu v Hv H1 H2.
  apply CProd_correct in Hx as [a [Ha [b [Hb Hxeq]]]].
  apply CProd_correct in Hy as [c [Hc [d [Hd Hyeq]]]].
  apply CProd_correct in Hu as [a' [Ha' [b' [Hb' Hueq]]]].
  apply CProd_correct in Hv as [c' [Hc' [d' [Hd' Hveq]]]]. subst.
  apply planeEquiv in H1... apply planeEquiv in H2...
  rewrite preRatAdd_a_b_c_d, preRatAdd_a_b_c_d...
  apply SepI. apply CProdI; (apply CProdI; [amr;nz|nzmr]).
  zfcrewrite. simpl. unfold RatEq in *.
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
  apply binCompatibleE. apply preRatAdd_binCompatible.
Qed.

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

Definition Rat : nat → set :=  λ n, [<Int n, Int 1>]~.

Lemma rat_has_0 : Rat 0 ∈ ℚ.
Proof. apply pQuotI; auto. Qed.
Hint Immediate rat_has_0 : core.

Example ratAdd_1_2 : Rat 1 + Rat 2 = Rat 3.
Proof with auto.
  assert (H2w: 2 ∈ ω) by repeat apply ω_inductive.
  assert (H2z: Int 2 ∈ ℤ) by (apply pQuotI; auto).
  unfold Rat. rewrite ratAdd_a_b_c_d...
  rewrite intMul_ident, intMul_ident, intAdd_1_2...
Qed.

Theorem ratAdd_comm : ∀ r s ∈ ℚ, r + s = s + r.
Proof with auto.
  intros r Hr s Hs.
  apply pQuotE in Hr as [a [Ha [b [Hb Hr]]]]. subst r.
  apply pQuotE in Hs as [c [Hc [d [Hd Hs]]]]. subst s.
  repeat rewrite ratAdd_a_b_c_d...
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
    auto; [|amr|nzmr|amr|nzmr]; nz.
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
    intMul_0_l, intAdd_ident; auto; nz.
Qed.

Theorem ratAddInv_exists : ∀r ∈ ℚ, ∃s ∈ ℚ, r + s = Rat 0.
Proof with auto.
  intros r Hr. apply pQuotE in Hr as [a [Ha [b [Hb Hr]]]].
  assert ((-a)%z ∈ ℤ) by (apply intAddInv_in_int; auto).
  exists ([<(-a)%z, b>]~). split. apply pQuotI...
  subst r. rewrite ratAdd_a_b_c_d...
  apply rat_ident... amr;nz. nzmr.
  rewrite intMul_ident, intMul_0_l, intMul_addInv_l,
    intAdd_inv... mr;nz. nz. mr;nz. ar;mr;nz.
Qed.

Theorem ratAddInv_unique : ∀r ∈ ℚ, ∃!s, s ∈ ℚ ∧ r + s = Rat 0.
Proof with auto.
  intros r Hr. split. apply ratAddInv_exists...
  intros s s' [Hs H1] [Hs' H2].
  rewrite <- ratAdd_ident, <- (ratAdd_ident s')...
  rewrite <- H2 at 1. rewrite <- H1.
  rewrite <- ratAdd_assoc, (ratAdd_comm r), (ratAdd_comm s')...
  apply ratAdd_ran...
Qed.

Close Scope Rat_scope.
Open Scope Int_scope.

Lemma intAddInv_in_nzInt : ∀a ∈ ℤ', -a ∈ ℤ'.
Proof with auto.
  intros a Ha'. apply nzInt in Ha' as Ha.
  apply pQuotE in Ha as [m [Hm [n [Hn Heq]]]]. subst a.
  rewrite intAddInv... apply nzIntI. apply pQuotI...
  apply nzIntE in Ha' as Hnq0. intros H0. apply Hnq0.
  apply int_ident in H0... rewrite add_0_r, add_0_l in H0... subst.
  apply int_ident... rewrite add_0_r, add_0_l...
Qed.

Lemma planeEquiv_intAddInv : ∀ a b c d,
  <a, b> ~ <c, d> → <a, b> ~ < -c, -d>.
Proof with auto.
  intros. apply planeEquivE2 in H as [H [Ha [Hb [Hc Hd]]]].
  apply planeEquivI... apply intAddInv_in_int...
  apply intAddInv_in_nzInt... unfold RatEq in *.
  rewrite intMul_addInv_l, intMul_addInv_r; nz... congruence.
Qed.

(** 有理数投射 **)
Definition RatPosDenom : set → set := λ a,
  {p ∊ a | λ p, intPos (π2 p)}.
Definition RatProj : set → set := λ a, cho (RatPosDenom a).

Lemma ratPosDenom_inhabited : ∀a ∈ ℤ, ∀b ∈ ℤ',
  ⦿ RatPosDenom ([<a, b>]~).
Proof with auto.
  intros a Ha b Hb.
  destruct ratEquiv_equiv as [_ [Hrefl _]].
  apply nzIntE in Hb as Hb0.
  apply int_connected in Hb0 as [Hnb|Hpb]; nz...
  - exists < -a, -b>. apply SepI. apply eqvcI.
    apply planeEquiv_intAddInv. apply Hrefl. apply CProdI...
    zfcrewrite. apply int_neg_pos...
  - exists <a, b>. apply SepI. apply eqvcI.
    apply Hrefl. apply CProdI... zfcrewrite...
Qed.

Lemma ratProj : ∀a ∈ ℤ, ∀b ∈ ℤ', ∃c ∈ ℤ, ∃d ∈ ℤ',
  RatProj ([<a, b>]~) = <c, d> ∧ <a, b> ~ <c, d> ∧
  (a ∈ ℤ' → c ∈ ℤ') ∧ intPos d.
Proof with auto.
  intros a Ha b Hb.
  pose proof (chosen_contained (RatPosDenom ([<a, b>]~))
    (ratPosDenom_inhabited a Ha b Hb)).
  apply SepE in H as [H Hpos]. apply eqvcE in H.
  apply planeEquivE1 in H
    as [a' [_ [b' [_ [c [Hc [d [Hd [H1 [H2 H3]]]]]]]]]].
  apply op_correct in H1 as []; subst a' b'.
  exists c. split... exists d. split...
  split... split. apply planeEquivI... split.
  - intros Ha'. unfold RatEq in H3.
    assert (H: (a ⋅ d)%z ∈ ℤ') by (apply nzIntMul_ranI; auto).
    rewrite H3 in H. apply nzIntMul_ranE in H as []... nz.
  - rewrite H2 in Hpos. zfcrewrite.
Qed.

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
  assert (Hna: (-a)%z ∈ ℤ) by (apply intAddInv_in_int; auto).
  assert (Hnc: (-c)%z ∈ ℤ) by (apply intAddInv_in_int; auto).
  destruct ratEquiv_equiv as [_ [_ [_ Htr]]].
  apply ExtAx. split; intros Hx.
  - apply eqvcE in Hx. rewrite H1 in Hx. zfcrewrite.
    apply eqvcI. cut (<(-a)%z, b> ~ <(-c)%z, d>). intros.
    eapply Htr... apply planeEquivI... unfold RatEq.
    apply planeEquiv in H2... unfold RatEq in H2.
    rewrite intMul_addInv_l, intMul_addInv_l; nz... congruence.
  - apply eqvcI. rewrite H1. zfcrewrite.
    apply eqvcE in Hx. cut (<(-c)%z, d> ~ <(-a)%z, b>). intros.
    eapply Htr... apply planeEquivI... unfold RatEq.
    apply planeEquiv in H2... unfold RatEq in H2.
    rewrite intMul_addInv_l, intMul_addInv_l; nz... congruence.
Qed.

Lemma ratAddInv_double : ∀r ∈ ℚ, --r = r.
Proof with auto.
  intros r Hr.
  apply pQuotE in Hr as [a [Ha [b [Hb Hr]]]]. subst r.
  rewrite ratAddInv, ratAddInv, intAddInv_double...
  apply intAddInv_in_int...
Qed.

Lemma ratAddInv_in_int : ∀r ∈ ℚ, -r ∈ ℚ.
Proof with auto.
  intros r Hr.
  apply pQuotE in Hr as [a [Ha [b [Hb Heq]]]]. subst r.
  rewrite ratAddInv... apply pQuotI... apply intAddInv_in_int...
Qed.

Lemma ratAdd_inv : ∀r ∈ ℚ, r - r = Rat 0.
Proof with auto.
  intros r Hr.
  apply pQuotE in Hr as [a [Ha [b [Hb Hr]]]]. subst r.
  assert (Hna: (-a)%z ∈ ℤ) by (apply intAddInv_in_int; auto).
  rewrite ratAddInv, ratAdd_a_b_c_d...
  apply rat_ident... amr;nz. nzmr.
  rewrite intMul_ident, intMul_0_l, intMul_addInv_l,
    intAdd_inv; auto; nz; [mr|mr|amr]; nz.
Qed.

Example ratAdd_2_n3 : Rat 2 - Rat 3 = -Rat 1.
Proof with auto.
  assert (H2w: 2 ∈ ω) by repeat apply ω_inductive.
  assert (H3w: 3 ∈ ω) by repeat apply ω_inductive.
  assert (H2z: Int 2 ∈ ℤ) by (apply pQuotI; auto).
  assert (H3z: Int 3 ∈ ℤ) by (apply pQuotI; auto).
  assert (Hn3z: (-Int 3)%z ∈ ℤ) by (apply intAddInv_in_int; auto).
  unfold Rat. rewrite ratAddInv, ratAddInv, ratAdd_a_b_c_d...
  repeat rewrite intMul_ident... rewrite intAdd_2_n3...
Qed.

Close Scope Rat_scope.
Open Scope Int_scope.

(** 有理数乘法 **)
Definition PreRatMul : set :=
  PlaneArith ℤ ℤ' (λ a b c d, <a ⋅ c, b ⋅ d>).
Notation "r ⋅ᵥ s" := (PreRatMul[<r, s>])
  (at level 50) : PreRat_scope.

Lemma preRatMul_maps_onto : PreRatMul: (ℤ × ℤ')² ⟹ ℤ × ℤ'.
Proof with eauto.
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
  apply CProdI... apply CProdI... mr. nzmr. zfcrewrite...
Qed.

Lemma preRatMul_binCompatible :
  binCompatible (PlaneEquiv ℤ ℤ' RatEq) (ℤ × ℤ') PreRatMul.
Proof with auto.
  split. apply ratEquiv_equiv. split.
  destruct preRatMul_maps_onto as [Hf [Hd Hr]].
  split... split... rewrite Hr. apply sub_refl.
  intros x Hx y Hy u Hu v Hv H1 H2.
  apply CProd_correct in Hx as [a [Ha [b [Hb Hxeq]]]].
  apply CProd_correct in Hy as [c [Hc [d [Hd Hyeq]]]].
  apply CProd_correct in Hu as [a' [Ha' [b' [Hb' Hueq]]]].
  apply CProd_correct in Hv as [c' [Hc' [d' [Hd' Hveq]]]]. subst.
  apply planeEquiv in H1... apply planeEquiv in H2...
  rewrite preRatMul_a_b_c_d, preRatMul_a_b_c_d...
  apply SepI. apply CProdI; apply CProdI; try mr; try nzmr.
  zfcrewrite. simpl. unfold RatEq in *.
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
  apply binCompatibleE. apply preRatMul_binCompatible.
Qed.

Lemma ratMul_a_b_c_d : ∀a ∈ ℤ, ∀b ∈ ℤ', ∀c ∈ ℤ, ∀d ∈ ℤ',
  [<a, b>]~ ⋅ [<c, d>]~ = ([<a ⋅ c, b ⋅ d>]~)%z.
Proof with auto.
  intros a Ha b Hb c Hc d Hd.
  rewrite ratMul_r_s, preRatMul_a_b_c_d...
  apply CProdI... apply CProdI...
Qed.

Lemma ratMul_0_l : ∀r ∈ ℚ, r ⋅ Rat 0 = Rat 0.
Proof with auto.
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
Proof with auto.
  assert (H2w: 2 ∈ ω) by repeat apply ω_inductive.
  assert (H4w: 4 ∈ ω) by repeat apply ω_inductive.
  assert (H2z: Int 2 ∈ ℤ) by (apply pQuotI; auto).
  assert (H4z: Int 4 ∈ ℤ) by (apply pQuotI; auto).
  assert (Hn2z: (-Int 2)%z ∈ ℤ) by (apply intAddInv_in_int; auto).
  assert (Hn4z: (-Int 4)%z ∈ ℤ) by (apply intAddInv_in_int; auto).
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
  rewrite ratAdd_a_b_c_d; [|auto; nz..].
  repeat rewrite ratMul_a_b_c_d; auto; [|amr;nz|nzmr].
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

Lemma ratMul_ident : ∀r ∈ ℚ, r ⋅ Rat 1 = r.
Proof with auto.
  intros r Hr.
  apply pQuotE in Hr as [a [Ha [b [Hb Hr]]]]. subst r.
  unfold Rat. rewrite ratMul_a_b_c_d...
  rewrite intMul_ident, intMul_ident; nz...
Qed.

Lemma ratMul_ident' : ∀r ∈ ℚ, Rat 1 ⋅ r = r.
Proof with auto.
  intros a Ha.
  rewrite ratMul_comm, ratMul_ident... apply pQuotI...
Qed.

Lemma ratMul_addInv : ∀r ∈ ℚ, -Rat 1 ⋅ r = -r.
Proof with auto.
  intros r Hr.
  apply pQuotE in Hr as [a [Ha [b [Hb Hr]]]]. subst r.
  unfold Rat. rewrite ratAddInv, ratAddInv, ratMul_a_b_c_d...
  rewrite intMul_n1_l, (intMul_comm (Int 1)),
    intMul_ident; nz... apply intAddInv_in_int...
Qed.

Lemma ratMul_0_r : ∀s ∈ ℚ, Rat 0 ⋅ s = Rat 0.
Proof. intros s Hs. rewrite ratMul_comm, ratMul_0_l; auto. Qed.

Lemma rat_0_neq_1 : Rat 0 ≠ Rat 1.
Proof with auto.
  unfold Rat. intros H. apply rat_ident in H...
  rewrite intMul_ident, intMul_ident in H...
  apply int_0_neq_1...
Qed.

Lemma zRat_zInt : ∀a ∈ ℤ, ∀b ∈ ℤ', [<a, b>]~ = Rat 0 → a = Int 0.
Proof with auto.
  unfold Rat. intros a Ha b Hb H0.
  apply rat_ident in H0...
  rewrite intMul_ident, intMul_0_l in H0; nz...
Qed.

Lemma zInt_zRat : ∀a ∈ ℤ, ∀b ∈ ℤ', a = Int 0 → [<a, b>]~ = Rat 0.
Proof with auto.
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
Definition ℚ' := (ℚ - ⎨Rat 0⎬)%zfc.

Lemma rat_has_1 : Rat 1 ∈ ℚ.
Proof. apply pQuotI; auto. Qed.

Lemma nzRat_has_1 : Rat 1 ∈ ℚ'.
Proof with auto.
  apply CompI... apply pQuotI...
  apply SingNI. intros H. apply rat_0_neq_1...
Qed.

Hint Immediate rat_has_1 : core.
Hint Immediate nzRat_has_1 : core.

Lemma nzRatI : ∀r ∈ ℚ, r ≠ Rat 0 → r ∈ ℚ'.
Proof with auto.
  intros a Ha Hnq0. apply CompI... apply SingNI...
Qed.

Lemma nzRatE : ∀r ∈ ℚ', r ≠ Rat 0.
Proof with auto.
  intros a Ha H0. apply CompE in Ha as [_ Ha].
  apply SingNE in Ha...
Qed.

Lemma nzRat : ∀r ∈ ℚ', r ∈ ℚ.
Proof with auto.
  intros a Ha. apply CompE in Ha as [Ha _]...
Qed.

Local Ltac nz_q := try (apply nzRat; assumption).

Theorem ratMulInv_exists : ∀r ∈ ℚ', ∃q ∈ ℚ', r ⋅ q = Rat 1.
Proof with auto.
  intros r Hr. apply nzRatE in Hr as Hr'. apply nzRat in Hr.
  apply pQuotE in Hr as [a [Ha [b [Hb Hr]]]]. subst r.
  apply nzRat_nzInt, nzIntI in Hr'...
  exists ([<b, a>]~). split.
  - apply nzRatI. apply pQuotI; nz...
    apply nzInt_nzRat; nz... apply nzIntE in Hb...
  - rewrite ratMul_a_b_c_d; nz... unfold Rat.
    apply rat_ident; auto; [mr;nz|nzmr|].
    rewrite intMul_ident, intMul_ident', intMul_comm;
      auto; nz; mr; nz.
Qed.

Theorem ratMulInv_unique : ∀r ∈ ℚ', ∃!q, q ∈ ℚ' ∧ r ⋅ q = Rat 1.
Proof with auto.
  intros r Hr. split.
  pose proof (ratMulInv_exists r Hr)...
  intros q q' [Hq H1] [Hq' H2].
  rewrite <- ratMul_ident, <- (ratMul_ident q'); nz_q...
  rewrite <- H2 at 1. rewrite <- H1.
  rewrite <- ratMul_assoc, (ratMul_comm r), (ratMul_comm q'); nz_q...
  apply ratMul_ran; nz_q...
Qed.

Lemma nzRatMul_ranI : ∀ r s ∈ ℚ', r ⋅ s ∈ ℚ'.
Proof with auto.
  intros r Hr s Hs.
  apply nzRatI. apply ratMul_ran; nz_q...
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
  rewrite H0 in H. rewrite ratMul_0_r in H.
  exfalso. apply rat_0_neq_1... apply ratMul_ran; nz_q.
Qed.

Theorem rat_no_0_div : ∀ r s ∈ ℚ,
  r ⋅ s = Rat 0 → r = Rat 0 ∨ s = Rat 0.
Proof with auto.
  intros r Hr s Hs H0.
  destruct (classic (r = Rat 0)) as [|Hr'];
  destruct (classic (s = Rat 0)) as [|Hs']... exfalso.
  apply nzRatI in Hr'... apply nzRatI in Hs'...
  pose proof (nzRatMul_ranI r Hr' s Hs'). apply nzRatE in H...
Qed.

(** 有理数乘法逆元 **)
Definition RatMulInv : set → set := λ r,
  let p := (RatProj r) in [<π2 p, π1 p>]~.
Notation "a ⁻¹" := (RatMulInv a) : Rat_scope.
Notation "a / b" := (a ⋅ b⁻¹) : Rat_scope.

Lemma ratMulInv : ∀a ∈ ℤ', ∀b ∈ ℤ', ([<a, b>]~)⁻¹ = [<b, a>]~.
Proof with eauto.
  intros a Ha' b Hb'. apply nzInt in Ha' as Ha.
  pose proof (ratProj a Ha b Hb') as [c [Hc [d [Hd [H1 [H2 [H3 _]]]]]]].
  unfold RatMulInv. rewrite H1. zfcrewrite. apply rat_ident; nz...
  apply planeEquivE2 in H2 as [H2 _]. unfold RatEq in H2.
  rewrite intMul_comm, (intMul_comm b); nz...
Qed.

Lemma ratMulInv_double : ∀r ∈ ℚ', r⁻¹⁻¹ = r.
Proof with auto.
  intros r Hr'.
  apply nzRatE in Hr' as Hnq0. apply nzRat in Hr' as Hr.
  apply pQuotE in Hr as [a [Ha [b [Hb Hr]]]]. subst r.
  apply nzRat_nzInt in Hnq0...
  assert (Ha': a ∈ ℤ') by (apply nzIntI; auto).
  rewrite ratMulInv, ratMulInv...
Qed.

Lemma ratMulInv_in_int : ∀r ∈ ℚ', r⁻¹ ∈ ℚ'.
Proof with auto.
  intros r Hr. assert (Hr' := Hr).
  apply CompE in Hr as [Hr _].
  apply pQuotE in Hr as [a [Ha [b [Hb Heq]]]]. subst r.
  apply nzRatE, nzRat_nzInt in Hr' as Ha'... apply nzIntI in Ha'...
  rewrite ratMulInv... apply nzRatI. apply pQuotI; nz...
  apply nzInt_nzRat; nz... apply nzIntE...
Qed.

Lemma ratMul_inv : ∀r ∈ ℚ', r / r = Rat 1.
Proof with auto.
  intros r Hr'. apply nzRat in Hr' as Hr.
  apply pQuotE in Hr as [a [Ha [b [Hb Hr]]]]. subst r.
  apply nzRatE, nzRat_nzInt, nzIntI in Hr'...
  rewrite ratMulInv, ratMul_a_b_c_d; nz...
  apply rat_ident... mr;nz. nzmr.
  rewrite intMul_ident, intMul_ident', intMul_comm;
    auto; nz; mr; nz.
Qed.

Example ratMul_n4_2' : -Rat 4 / Rat 2 = -Rat 2.
Proof with auto.
  assert (H2w: 2 ∈ ω) by repeat apply ω_inductive.
  assert (H4w: 4 ∈ ω) by repeat apply ω_inductive.
  assert (H2z: Int 2 ∈ ℤ) by (apply pQuotI; auto).
  assert (H4z: Int 4 ∈ ℤ) by (apply pQuotI; auto).
  assert (Hn4z: (-Int 4)%z ∈ ℤ) by (apply intAddInv_in_int; auto).
  assert (H2z': Int 2 ∈ ℤ'). {
    apply nzIntI... intros H. apply int_ident in H...
    rewrite add_0_r, add_0_r in H... eapply S_neq_0; eauto.
  }
  unfold Rat. rewrite ratAddInv, ratAddInv, ratMulInv...
  rewrite ratMul_a_b_c_d...
  unfold Int. rewrite intAddInv, intAddInv...
  rewrite intMul_m_n_p_q, intMul_m_n_p_q...
  rewrite mul_1_r, mul_1_r, mul_0_r, mul_0_r,
    (mul_comm 1), mul_1_r, mul_0_r, mul_0_l,
    add_0_r, add_0_r, add_0_l...
  apply rat_ident... apply pQuotI... apply pQuotI...
  rewrite intMul_m_n_p_q, intMul_m_n_p_q...
  rewrite mul_0_l, mul_0_l, mul_0_l, mul_0_r, mul_0_r,
    mul_1_r, mul_2_2, add_0_l, add_0_l...
Qed.
