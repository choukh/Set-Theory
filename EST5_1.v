(** Based on "Elements of Set Theory" Chapter 5 Part 1 **)
(** Coq coding by choukh, June 2020 **)

Require Export ZFC.lib.Natural.

(*** EST第五章1：整数的定义，整数算术：加法，加法逆元 ***)

(* 二元函数与等价关系的相容性 *)
Definition binCompatible : set → set → set → Prop := λ R A F,
  equiv R A ∧ F: A × A ⇒ A ∧
  ∀ x y u v ∈ A, <x, u> ∈ R → <y, v> ∈ R →
  <F[<x, y>], F[<u, v>]> ∈ R.

(* 相容函数在商集上的相似函数 *)
Definition QuotionFunc : set → set → set → set := λ R A F,
  {λ p, <<[π1 p]R, [π2 p]R>, [F[<π1 p, π2 p>]]R> | p ∊ A × A}.

Lemma quotionFunc_maps_into : ∀ R A F,
  binCompatible R A F →
  (QuotionFunc R A F): (A/R) × (A/R) ⇒ A/R.
Proof with eauto.
  intros * [Hqv [[Hf [Hdf Hrf]] Hc]]. repeat split.
  - (* is_rel *) intros p Hp.
    apply ReplAx in Hp as [x []]. subst p. eexists...
  - apply domE in H...
  - (* single-valued *) intros y1 y2 Hy1 Hy2.
    apply domE in H as [y0 Hy0].
    apply ReplAx in Hy0 as [a0 [_ Heq0]].
    apply ReplAx in Hy1 as [a1 [Ha1 Heq1]].
    apply ReplAx in Hy2 as [a2 [Ha2 Heq2]].
    apply op_iff in Heq0 as [Heq0 _].
    apply op_iff in Heq1 as [Heq1 Hy1].
    apply op_iff in Heq2 as [Heq2 Hy2].
    subst x y1 y2. rewrite <- Heq2 in Heq1. clear Heq2.
    apply op_iff in Heq1 as [H1 H2].
    apply CProdE1 in Ha1 as [Ha11 Ha12].
    apply CProdE1 in Ha2 as [Ha21 Ha22].
    eapply eqvc_ident in H1...
    eapply eqvc_ident in H2...
    assert (<F[<π1 a1, π2 a1>], F[<π1 a2, π2 a2>]> ∈ R)
      by (apply Hc; eauto).
    assert (Hd1: <π1 a1, π2 a1> ∈ A × A) by (apply CProdI; eauto).
    assert (Hd2: <π1 a2, π2 a2> ∈ A × A) by (apply CProdI; eauto).
    rewrite <- Hdf in Hd1, Hd2.
    apply func_correct in Hd1... apply func_correct in Hd2...
    apply ranI, Hrf in Hd1. apply ranI, Hrf in Hd2.
    eapply eqvc_ident...
  - (* dom F' = (A/R) × (A/R) *)
    apply ExtAx. split; intros Hx.
    + apply domE in Hx as [y Hp]. apply ReplAx in Hp as [a [Hp Heq]].
      apply op_iff in Heq as [Heq _]. subst x.
      apply CProdE1 in Hp as [H1 H2]. apply CProdI; apply quotI...
    + apply CProdE2 in Hx as Hxp. apply op_η in Hxp.
      apply CProdE1 in Hx as [H1 H2].
      apply quotE in H1 as [a [Ha Heqa]].
      apply quotE in H2 as [b [Hb Heqb]].
      eapply domI. apply ReplAx. exists <a, b>. split.
      apply CProdI... rewrite π1_correct, π2_correct.
      apply op_iff... split. rewrite Hxp.
      apply op_iff... reflexivity.
  - (* ran F' ⊆ A/R *)
    intros y Hy. apply ranE in Hy as [].
    apply ReplAx in H as [a [Ha Heq]].
    apply CProdE2 in Ha as Hap. apply op_η in Hap.
    apply op_iff in Heq as [_ Hy]. subst y. rewrite <- Hap.
    rewrite <- Hdf in Ha. apply func_correct in Ha as Hp...
    apply ranI in Hp as Hr. apply Hrf in Hr. apply quotI...
Qed.

Lemma quotionFunc_maps_onto : ∀ R A F,
  binCompatible R A F → F: A × A ⟹ A →
  (QuotionFunc R A F): (A/R) × (A/R) ⟹ A/R.
Proof with eauto.
  intros * Hc [Hf [Hdf Hrf]].
  pose proof (quotionFunc_maps_into) as [Hf' [Hdf' Hrf']]...
  split... split... apply sub_antisym...
  intros y Hy. apply quotE in Hy as [p [Hp Heq]].
  rewrite <- Hrf in Hp. apply ranE in Hp as [x Hp].
  apply domI in Hp as Hd. rewrite Hdf in Hd.
  eapply ranI. apply ReplAx. exists x. split...
  apply op_iff. split... apply CProdE2 in Hd.
  apply op_η in Hd. rewrite <- Hd.
  cut (F[x] = p). congruence. apply func_ap...
Qed.

Lemma binCompatibleE: ∀ R A F,
  binCompatible R A F →
  let F' := QuotionFunc R A F in
  ∀ x y ∈ A, F'[<[x]R, [y]R>] = [F[<x, y>]]R.
Proof with eauto.
  intros * Hc F' x Hx y Hy.
  pose proof (quotionFunc_maps_into) as [Hf' [Hdf' Hrf']]...
  destruct Hc as [Hqv [[Hf [Hdf Hrf]] Hc]].
  assert (Hdx: [x]R ∈ A/R) by (apply quotI; auto).
  assert (Hdy: [y]R ∈ A/R) by (apply quotI; auto).
  assert (Hd: <[x]R, [y]R> ∈ (A/R) × (A/R)) by (apply CProdI; auto).
  rewrite <- Hdf' in Hd. apply func_correct in Hd...
  apply ReplAx in Hd as [b [Hb Heq]].
  apply op_iff in Heq as [H1 H2]. unfold F'.
  rewrite <- H2. eapply eqvc_ident; swap 1 3...
  - apply Hrf. eapply ranI... apply func_correct...
    rewrite Hdf. apply CProdE1 in Hb as []. apply CProdI...
  - apply Hrf. eapply ranI... apply func_correct...
    rewrite Hdf. apply CProdE1 in Hb as []. apply CProdI...
  - apply op_iff in H1 as [H11 H12].
    apply CProdE1 in Hb as [Hb1 Hb2].
    eapply eqvc_ident in H11...
    eapply eqvc_ident in H12... apply Hc...
Qed.

Theorem quotionFunc_unique: ∀ R A F,
  binCompatible R A F →
  ∃!F', F': (A/R) × (A/R) ⇒ A/R ∧
    ∀ x y ∈ A, F'[<[x]R, [y]R>] = [F[<x, y>]]R.
Proof with eauto.
  intros * Hc. split.
  exists (QuotionFunc R A F). split.
  apply quotionFunc_maps_into...
  apply binCompatibleE...
  intros F1 F2 [[HF1 [Hd1 Hr1]] H1] [[HF2 [Hd2 Hr2]] H2].
  apply func_ext_intro... rewrite Hd1, Hd2...
  intros x Hx. rewrite Hd1 in Hx.
  apply CProdE2 in Hx as Hxp. apply op_η in Hxp.
  apply CProdE1 in Hx as [Hx1 Hx2].
  apply quotE in Hx1 as [a [Ha Haeq]].
  apply quotE in Hx2 as [b [Hb Hbeq]].
  pose proof (H1 a Ha b Hb) as H3.
  pose proof (H2 a Ha b Hb) as H4. simpl in *. congruence.
Qed.

Notation "A ²" := (A × A) (at level 9).

(* 整数定义和有理数定义通用的平面构造 *)
Lemma plane2E : ∀ A B, ∀x ∈ (A × B)²,
  ∃m ∈ A, ∃n ∈ B, ∃p ∈ A, ∃q ∈ B, x = <<m, n>, <p, q>>.
Proof with auto.
  intros * x Hx.
  apply cprod_iff in Hx as [u [Hu [v [Hv Hx]]]].
  apply cprod_iff in Hu as [m [Hm [n [Hn Hu]]]].
  apply cprod_iff in Hv as [p [Hp [q [Hq Hv]]]].
  exists m. split... exists n. split...
  exists p. split... exists q. split... congruence.
Qed.

Declare Scope PlaneEquiv_scope.
Open Scope PlaneEquiv_scope.

(* 平面上的等价关系 *)
Definition PlaneEq := set → set → set → set → Prop.
Definition PlaneEquiv : set → set → PlaneEq → set :=
  λ A B Eq, Rel (A × B) (A × B) (λ a b,
    let m := π1 a in let n := π2 a in
    let p := π1 b in let q := π2 b in
    Eq m n p q
  ).
Notation "~" := PlaneEquiv : PlaneEquiv_scope.
Notation "a ~ b" := (λ A B Eq, <a, b> ∈ PlaneEquiv A B Eq)
  (at level 10) : PlaneEquiv_scope.

Lemma planeEquivI : ∀ A B (Eq : PlaneEq),
  ∀m ∈ A, ∀n ∈ B, ∀p ∈ A, ∀q ∈ B,
  Eq m n p q → (<m, n> ~ <p, q>) A B Eq.
Proof with auto.
  intros * m Hm n Hn p Hp q Hq Heq.
  apply SepI. apply CProdI; apply CProdI... zfcrewrite...
Qed.

Lemma planeEquivE1 : ∀ A B Eq, ∀ x y, (x ~ y) A B Eq →
  ∃m ∈ A, ∃n ∈ B, ∃p ∈ A, ∃q ∈ B,
  x = <m, n> ∧ y = <p, q> ∧ Eq m n p q.
Proof with auto.
  intros * Hqv. apply SepE in Hqv as [Hxy Heq].
  apply plane2E in Hxy as [m [Hm [n [Hn [p [Hp [q [Hq Hxy]]]]]]]].
  apply op_iff in Hxy as []; subst.
  zfcrewrite. simpl in Heq.
  exists m. split... exists n. split...
  exists p. split... exists q. split...
Qed.

Lemma planeEquivE2 : ∀ A B Eq, ∀ m n p q,
  (<m, n> ~ <p, q>) A B Eq →
  Eq m n p q ∧ m ∈ A ∧ n ∈ B ∧ p ∈ A ∧ q ∈ B.
Proof.
  intros * Hqv. apply planeEquivE1 in Hqv
    as [a [Ha [b [Hb [c [Hc [d [Hd [H1 [H2 H3]]]]]]]]]].
  apply op_iff in H1 as [];
  apply op_iff in H2 as []; subst a b c d. auto.
Qed.

Lemma planeEquiv : ∀ A B Eq, ∀m ∈ A, ∀n ∈ B, ∀p ∈ A, ∀q ∈ B,
  (<m, n> ~ <p, q>) A B Eq ↔ Eq m n p q.
Proof with eauto.
  intros * m Hm n Hn p Hp q Hq. split; intros.
  - eapply planeEquivE2...
  - apply planeEquivI...
Qed.

Definition planeEqRefl : PlaneEq → Prop := λ Eq,
  ∀ m n, Eq m n m n.
Definition planeEqSymm : PlaneEq → Prop := λ Eq,
  ∀ m n p q, Eq m n p q → Eq p q m n.
Definition planeEqTran : set → set → PlaneEq → Prop := λ A B Eq,
  ∀m ∈ A, ∀n ∈ B, ∀p ∈ A, ∀q ∈ B, ∀r ∈ A, ∀s ∈ B,
  Eq m n p q → Eq p q r s → Eq m n r s.

Theorem planeEquiv_equiv : ∀ A B (Eq : PlaneEq),
  planeEqRefl Eq → planeEqSymm Eq → planeEqTran A B Eq →
  equiv (PlaneEquiv A B Eq) (A × B).
Proof with eauto.
  intros * Hrefl Hsymm Htran. repeat split.
  - intros x Hx. apply SepE in Hx as []...
  - intros x Hx. apply SepI. apply CProdI...
    apply cprod_iff in Hx as [a [Ha [b [Hb Heq]]]].
    subst x. zfcrewrite...
  - intros x y Hqv. apply planeEquivE1 in Hqv
      as [m [Hm [n [Hn [p [Hp [q [Hq [Hx [Hy Heq]]]]]]]]]].
    subst. apply SepI. apply CProdI; apply CProdI...
    zfcrewrite. simpl in *. apply Hsymm...
  - intros x y z H1 H2.
    apply planeEquivE1 in H1
      as [m [Hm [n [Hn [p [Hp [q [Hq [Hx [Hy H1]]]]]]]]]]. subst.
    apply planeEquivE1 in H2
      as [p' [_ [q' [_ [r [Hr [s [Hs [Hx [Hy H2]]]]]]]]]]. subst.
    apply op_iff in Hx as []; subst p' q'.
    apply SepI. apply CProdI; apply CProdI...
    zfcrewrite. simpl in *. eapply Htran; revgoals...
Qed.

(* 平面上的商集 *)
Definition PlaneQuotient : set → set → PlaneEq → set := λ A B Eq,
  A × B / ~ A B Eq.

Lemma pQuotI : ∀ A B Eq, ∀m ∈ A, ∀n ∈ B,
  [<m, n>]~ A B Eq ∈ PlaneQuotient A B Eq.
Proof. intros * m Hm n Hn. apply quotI. apply CProdI; auto. Qed.

Lemma pQuotE : ∀ A B Eq, ∀x ∈ PlaneQuotient A B Eq,
  ∃m ∈ A, ∃n ∈ B, x = [<m, n>]~ A B Eq.
Proof with auto.
  intros * x Hx. apply quotE in Hx as [p [Hx Heq1]].
  apply cprod_iff in Hx as [a [Ha [b [Hb Heq2]]]].
  exists a. split... exists b. split... congruence.
Qed.

Lemma pQuot_ident : ∀ A B Eq,
  planeEqRefl Eq → planeEqSymm Eq → planeEqTran A B Eq →
  ∀m ∈ A, ∀n ∈ B, ∀p ∈ A, ∀q ∈ B,
  Eq m n p q ↔ [<m, n>]~ A B Eq = [<p, q>]~ A B Eq.
Proof with eauto.
  intros * Hrefl Hsymm Htran m Hm n Hn p Hp q Hq. split; intros Heq.
  - eapply eqvc_ident; swap 1 3. apply planeEquiv_equiv...
    apply CProdI... apply CProdI... apply planeEquivI...
  - cut ((<m, n> ~ <p, q>) A B Eq). intros H.
    apply planeEquiv in H...
    eapply eqvc_ident; revgoals. apply Heq.
    apply planeEquiv_equiv... apply CProdI... apply CProdI...
Qed.

(* 平面算术定义Helper *)
Definition PlaneF := set → set → set → set → set.
Definition PlaneArith : set → set → PlaneF → set :=
  λ A B F, Rel (A × B)² (A × B) (λ x y,
  let m := π1 (π1 x) in let n := π2 (π1 x) in
  let p := π1 (π2 x) in let q := π2 (π2 x) in
  y = F m n p q
).

Lemma planeArithE : ∀ A B F x y, <x, y> ∈ PlaneArith A B F →
  ∃m ∈ A, ∃n ∈ B, ∃p ∈ A, ∃q ∈ B,
  x = <<m, n>, <p, q>> ∧ y = F m n p q.
Proof with auto.
  intros * Hxy. apply SepE in Hxy as [Hxy Heq].
  apply CProdE1 in Hxy as [Hx _]; zfcrewrite.
  apply plane2E in Hx as [m [Hm [n [Hn [p [Hp [q [Hq Hx]]]]]]]].
  subst x. zfcrewrite. simpl in Heq.
  exists m. split... exists n. split...
  exists p. split... exists q. split...
Qed.

Lemma planeArith_maps_onto : ∀ A B F,
  (∀m ∈ A, ∀n ∈ B, ∀p ∈ A, ∀q ∈ B, F m n p q ∈ A × B) →
  (∀a ∈ A, ∀b ∈ B, ∃m ∈ A, ∃n ∈ B, ∃p ∈ A, ∃q ∈ B, <a, b> = F m n p q) →
  (PlaneArith A B F): (A × B)² ⟹ A × B.
Proof with eauto.
  intros * HF1 HF2. repeat split.
  - (* is_rel *) intros x Hx.
    apply SepE in Hx as [Hx _]. apply CProdE2 in Hx...
  - apply domE in H...
  - (* single-valued *) intros y1 y2 H1 H2.
    apply planeArithE in H1
      as [m1 [Hm1 [n1 [Hn1 [p1 [Hp1 [q1 [Hq1 [Hx1 Hy1]]]]]]]]].
    apply planeArithE in H2
      as [m2 [Hm2 [n2 [Hn2 [p2 [Hp2 [q2 [Hq2 [Hx2 Hy2]]]]]]]]].
    subst x. apply op_iff in Hx2 as [H1 H2].
    apply op_iff in H1 as [H11 H12].
    apply op_iff in H2 as [H21 H22]. congruence.
  - (* dom planeArith = A² × A² *)
    apply ExtAx. intros x. split; intros Hx.
    + apply domE in Hx as [y Hx]. apply SepE in Hx as [Hx _].
      apply CProdE1 in Hx as []. zfcrewrite.
    + assert (Hx' := Hx).
      apply plane2E in Hx' as [m [Hm [n [Hn [p [Hp [q [Hq Hx']]]]]]]].
      eapply domI. apply SepI. apply CProdI...
      apply HF1. apply Hm. apply Hn. apply Hp. apply Hq.
      subst x. zfcrewrite. simpl. reflexivity.
  - (* ran planeArith = A² *)
    apply ExtAx. intros y. split; intros Hy.
    + apply ranE in Hy as [x Hp]. apply SepE in Hp as [Hp _].
      apply CProdE1 in Hp as []; zfcrewrite.
    + assert (Hy' := Hy).
      apply cprod_iff in Hy' as [a [Ha [b [Hb Heq]]]].
      edestruct HF2 as [m [Hm [n [Hn [p [Hp [q [Hq]]]]]]]].
      apply Ha. apply Hb. eapply ranI. apply SepI.
      apply CProdI... apply CProdI; apply CProdI.
      apply Hm. apply Hn. apply Hp. apply Hq.
      subst. zfcrewrite. simpl. congruence.
Qed.

Close Scope PlaneEquiv_scope.
Declare Scope PreInt_scope.
Open Scope PreInt_scope.
Delimit Scope PreInt_scope with pz.

(* 自然数平面上的用于构造整数的等价关系 *)
Definition IntEq : PlaneEq := λ m n p q, m + q = p + n.
Notation "~" := (PlaneEquiv ω ω IntEq) : PreInt_scope.
Notation "a ~ b" := (<a, b> ∈ PlaneEquiv ω ω IntEq)
  (at level 10) : PreInt_scope.

Lemma intEqRefl : planeEqRefl IntEq.
Proof. intros m n. reflexivity. Qed.

Lemma intEqSymm : planeEqSymm IntEq.
Proof. intros m n p q Heq. symmetry. auto. Qed.

Lemma intEqTran : planeEqTran ω ω IntEq.
Proof with eauto; try repeat apply add_ran; auto.
  intros m Hm n Hn p Hp q Hq r Hr s Hs H1 H2. unfold IntEq.
  assert (m + q + (p + s) = p + n + (r + q)) by congruence.
  rewrite (add_comm (m+q)) in H...
  rewrite <- (add_assoc (p+s)) in H...
  rewrite <- (add_assoc (p+n)) in H...
  assert (p + s + m = p + n + r). {
    eapply add_cancel; revgoals; [apply H|..]...
  }
  rewrite add_assoc, add_assoc in H0...
  rewrite add_comm, (add_comm p) in H0...
  rewrite add_comm, (add_comm r)...
  eapply add_cancel; revgoals; [apply H0|..]...
Qed.

Theorem intEquiv_equiv : equiv (PlaneEquiv ω ω IntEq) ω².
Proof with eauto; try repeat apply add_ran; auto.
  apply planeEquiv_equiv.
  apply intEqRefl. apply intEqSymm. apply intEqTran.
Qed.

(** 整数 **)
Definition ℤ : set := ω²/~.

Lemma int_ident : ∀ m n p q ∈ ω,
  m + q = p + n ↔ [<m, n>]~ = [<p, q>]~.
Proof with eauto.
  apply pQuot_ident.
  apply intEqRefl. apply intEqSymm. apply intEqTran.
Qed.

Definition PreIntAdd : set :=
  PlaneArith ω ω (λ m n p q, <m + p, n + q>).
Notation "a +ᵥ b" := (PreIntAdd[<a, b>]) (at level 50) : PreInt_scope.

Lemma add_split : ∀x ∈ ω, ∃ m n ∈ ω, x = m + n.
Proof with nauto.
  intros n Hn.
  set {n ∊ ω | λ n, ∃ a b ∈ ω, n = a + b} as N.
  ω_induction N Hn.
  - exists 0. split... exists 0. split... rewrite add_ident...
  - destruct IH as [a [Ha [b [Hb Heq]]]].
    exists a. split... exists (b⁺). split. apply ω_inductive...
    rewrite add_m_n... congruence.
Qed.

Lemma preIntAdd_maps_onto : PreIntAdd: (ω²)² ⟹ ω².
Proof with eauto.
  apply planeArith_maps_onto.
  - intros m Hm n Hn p Hp q Hq. apply CProdI; apply add_ran...
  - intros a Ha b Hb.
    apply add_split in Ha as [m [Hm [p [Hp Ha]]]].
    apply add_split in Hb as [n [Hn [q [Hq Hb]]]].
    exists m. split... exists n. split...
    exists p. split... exists q. split... congruence.
Qed.

Lemma preIntAdd_m_n_p_q : ∀ m n p q ∈ ω,
  <m, n> +ᵥ <p, q> = <m + p, n + q>.
Proof with auto.
  intros m Hm n Hn p Hp q Hq.
  eapply func_ap. destruct preIntAdd_maps_onto...
  apply SepI. apply CProdI; apply CProdI;
    try apply CProdI; try apply add_ran... zfcrewrite...
Qed.

Lemma preIntAdd_binCompatible :
  binCompatible (PlaneEquiv ω ω IntEq) ω² PreIntAdd.
Proof with eauto.
  split. apply intEquiv_equiv. split.
  destruct preIntAdd_maps_onto as [Hf [Hd Hr]].
  split... split... rewrite Hr. apply sub_refl. 
  intros x Hx y Hy u Hu v Hv H1 H2.
  apply cprod_iff in Hx as [m [Hm [n [Hn Hxeq]]]].
  apply cprod_iff in Hy as [p [Hp [q [Hq Hyeq]]]].
  apply cprod_iff in Hu as [m' [Hm' [n' [Hn' Hueq]]]].
  apply cprod_iff in Hv as [p' [Hp' [q' [Hq' Hveq]]]]. subst.
  apply planeEquiv in H1... apply planeEquiv in H2...
  rewrite preIntAdd_m_n_p_q, preIntAdd_m_n_p_q...
  apply SepI. apply CProdI; apply CProdI; apply add_ran...
  zfcrewrite. simpl. unfold IntEq in *.
  rewrite (add_comm m), <- add_assoc, (add_comm (p+m+n')),
    <- add_assoc, <- add_assoc, add_assoc, (add_comm q');
    try repeat apply add_ran...
  rewrite (add_comm m'), <- (add_assoc (p'+m')), (add_comm (p'+m'+n)),
    <- (add_assoc q), <- (add_assoc q), (add_assoc (q+p')), (add_comm q);
    try repeat apply add_ran... congruence.
Qed.

Close Scope Nat_scope.
Declare Scope Int_scope.
Open Scope Int_scope.
Delimit Scope Int_scope with z.

(** 整数加法 **)
Definition IntAdd : set :=
  QuotionFunc (PlaneEquiv ω ω IntEq) ω² PreIntAdd.
Notation "a + b" := (IntAdd[<a, b>]) : Int_scope.

Lemma intAdd_maps_onto : IntAdd: ℤ × ℤ ⟹ ℤ.
Proof.
  apply quotionFunc_maps_onto.
  apply preIntAdd_binCompatible.
  apply preIntAdd_maps_onto.
Qed.

Lemma intAdd_a_b : ∀ a b ∈ ω², [a]~ + [b]~ = [a +ᵥ b]~.
Proof.
  apply binCompatibleE. apply preIntAdd_binCompatible.
Qed.

Lemma intAdd_m_n_p_q : ∀ m n p q ∈ ω,
  [<m, n>]~ + [<p, q>]~ = ([<m + p, n + q>]~)%n.
Proof with auto.
  intros m Hm n Hn p Hp q Hq.
  rewrite intAdd_a_b, preIntAdd_m_n_p_q...
  apply CProdI... apply CProdI...
Qed.

Lemma intAdd_ran : ∀ a b ∈ ℤ, a + b ∈ ℤ.
Proof with auto.
  intros a Ha b Hb.
  apply pQuotE in Ha as [m [Hm [n [Hn Ha]]]]. subst a.
  apply pQuotE in Hb as [p [Hp [q [Hq Hb]]]]. subst b.
  rewrite intAdd_m_n_p_q... apply pQuotI; apply add_ran...
Qed.

Definition Int : nat → set := λ n, [<n, 0>]~.

Lemma intI : ∀ m n : nat, [<m, n>]~ ∈ ℤ.
Proof. intros. apply pQuotI; nauto. Qed.
Hint Immediate intI : number_hint.

Lemma int_n : ∀ n, Int n ∈ ℤ.
Proof. intros. unfold Int. nauto. Qed.
Hint Immediate int_n : number_hint.

Example intAdd_1_2 : Int 1 + Int 2 = Int 3.
Proof with nauto.
  unfold Int. rewrite intAdd_m_n_p_q, add_ident...
  rewrite add_1_2. apply int_ident...
Qed.

Theorem intAdd_comm : ∀ a b ∈ ℤ, a + b = b + a.
Proof with auto.
  intros a Ha b Hb.
  apply pQuotE in Ha as [m [Hm [n [Hn Ha]]]]. subst a.
  apply pQuotE in Hb as [p [Hp [q [Hq Hb]]]]. subst b.
  repeat rewrite intAdd_m_n_p_q...
  rewrite (add_comm m), (add_comm q)...
Qed.

Theorem intAdd_assoc : ∀ a b c ∈ ℤ,
  (a + b) + c = a + (b + c).
Proof with auto.
  intros a Ha b Hb c Hc.
  apply pQuotE in Ha as [m [Hm [n [Hn Ha]]]]. subst a.
  apply pQuotE in Hb as [p [Hp [q [Hq Hb]]]]. subst b.
  apply pQuotE in Hc as [r [Hr [s [Hs Hc]]]]. subst c.
  repeat rewrite intAdd_m_n_p_q; try apply add_ran...
  repeat rewrite <- add_assoc; try repeat apply add_ran...
Qed.

Theorem intAdd_ident : ∀a ∈ ℤ, a + Int 0 = a.
Proof with nauto.
  intros a Ha. apply pQuotE in Ha as [m [Hm [n [Hn Ha]]]].
  subst a. unfold Int. rewrite intAdd_m_n_p_q, add_ident, add_ident...
Qed.

Corollary intAdd_ident' : ∀a ∈ ℤ, Int 0 + a = a.
Proof with nauto.
  intros a Ha. rewrite intAdd_comm, intAdd_ident...
Qed.

Theorem intAddInv_exists : ∀a ∈ ℤ, ∃b ∈ ℤ, a + b = Int 0.
Proof with nauto.
  intros a Ha. apply pQuotE in Ha as [m [Hm [n [Hn Ha]]]].
  exists ([<n, m>]~). split. apply pQuotI...
  subst a. rewrite intAdd_m_n_p_q...
  apply int_ident; try apply add_ran...
  rewrite add_ident, add_ident', add_comm; try apply add_ran...
Qed.

Theorem intAddInv_unique : ∀a ∈ ℤ, ∃!b, b ∈ ℤ ∧ a + b = Int 0.
Proof with auto.
  intros a Ha. split. apply intAddInv_exists...
  intros b b' [Hb H1] [Hb' H2].
  rewrite <- intAdd_ident, <- (intAdd_ident b')...
  rewrite <- H2 at 1. rewrite <- H1.
  rewrite <- intAdd_assoc, (intAdd_comm a), (intAdd_comm b')...
  apply intAdd_ran...
Qed.

Close Scope Int_scope.
Open Scope Nat_scope.

Lemma diff_exists : ∀ m n ∈ ω, m ∈ n → ∃d ∈ ω, m + d = n ∧ d ≠ 0.
Proof with nauto.
  intros k Hk n Hn.
  set {n ∊ ω | λ n, k ∈ n → ∃d ∈ ω, k + d = n ∧ d ≠ 0} as N.
  ω_induction N Hn; intros Hlt. exfalso0.
  apply leq_iff_lt_suc in Hlt as []...
  - apply IH in H as [d [Hd [H1 H2]]].
    exists d⁺. split. apply ω_inductive...
    split. rewrite add_m_n... subst... apply suc_neq_0.
  - exists 1. split. apply ω_inductive...
    split. rewrite add_suc... subst... apply suc_neq_0.
Qed.

(* 整数投射 *)
Definition PreIntProj : set → set := λ a,
  {p ∊ a | λ p, π1 p = 0 ∨ π2 p = 0}.
Definition IntProj : set → set := λ a,
  ⋃ (PreIntProj a).

Lemma preIntProjI1 : ∀ m n p ∈ ω,
  n + p = m → <p, 0> ∈ PreIntProj ([<m, n>]~).
Proof with nauto.
  intros m Hm n Hn p Hp Heq.
  apply SepI. apply eqvcI. apply planeEquivI... unfold IntEq.
  rewrite add_ident... subst. rewrite add_comm... zfcrewrite...
Qed.

Lemma preIntProjI2 : ∀ m n q ∈ ω,
  m + q = n → <0, q> ∈ PreIntProj ([<m, n>]~).
Proof with nauto.
  intros m Hm n Hn q Hq Heq.
  apply SepI. apply eqvcI. apply planeEquivI... unfold IntEq.
  rewrite add_ident'... zfcrewrite...
Qed.

Lemma preIntProjE : ∀ m n ∈ ω, ∀x ∈ PreIntProj ([<m, n>]~),
  ∃ p q ∈ ω, x = <p, q> ∧ <m, n> ~ <p, q> ∧
    (p = 0 ∨ q = 0).
Proof with auto.
  intros m Hm n Hn x Hx.
  apply SepE in Hx as [Hx H0]. apply eqvcE in Hx.
  assert (Hx' := Hx). apply planeEquivE1 in Hx'
    as [m' [Hm' [n' [Hn' [p [Hp [q [Hq [H1 [H2 _]]]]]]]]]].
  apply op_iff in H1 as []; subst m' n'.
  subst x. zfcrewrite. destruct H0; subst.
  exists 0. split... exists q... split...
  exists p. split... exists 0... split...
Qed.

Lemma preIntProj_single : ∀a ∈ ℤ, ∃! p, p ∈ PreIntProj a.
Proof with neauto.
  intros a Ha.
  apply pQuotE in Ha as [m [Hm [n [Hn Ha]]]].
  subst a. split.
  - destruct (classic (m = n)) as [Hmn|Hmn].
    + exists <0, 0>. apply preIntProjI1... rewrite add_ident...
    + apply lt_connected in Hmn as []...
      * apply diff_exists in H as [b [Hb [Heq _]]]...
        exists <0, b>. apply preIntProjI2...
      * apply diff_exists in H as [b [Hb [Heq _]]]...
        exists <b, 0>. apply preIntProjI1...
  - intros x1 x2 H1 H2.
    apply preIntProjE in H1 as [p1 [Hp1 [q1 [Hq1 [Hx1 [H1 []]]]]]];
    apply preIntProjE in H2 as [p2 [Hp2 [q2 [Hq2 [Hx2 [H2 []]]]]]];
      subst; auto; apply op_iff;
      apply planeEquiv in H1; apply planeEquiv in H2;
      unfold IntEq in *...
    + split... rewrite add_ident' in *... subst n.
      eapply add_cancel'; revgoals...
    + rewrite add_ident' in H1...
      rewrite add_ident in H2... subst m.
      rewrite add_assoc, add_comm,
        add_assoc in H1; [|auto; apply add_ran..]...
      apply add_a_b_a in H1...
      apply add_m_n_0 in H1 as []... apply add_ran...
    + rewrite add_ident in H1...
      rewrite add_ident' in H2... subst m.
      rewrite add_assoc, add_comm,
        add_assoc in H2; [|auto; apply add_ran..]...
      apply add_a_b_a in H2...
      apply add_m_n_0 in H2 as []... apply add_ran...
    + split... rewrite add_ident in *... subst m.
      eapply add_cancel; revgoals...
Qed.

Lemma preIntProj : ∀ a ∈ ℤ, ∃p, PreIntProj a = ⎨p⎬.
Proof with auto.
  intros a Ha.
  apply preIntProj_single in Ha as [[p Hp] Hu].
  exists p. apply ExtAx. split; intros Hx.
  pose proof (Hu x p Hx Hp). subst...
  apply SingE in Hx. subst...
Qed.

Lemma intProj : ∀ m n ∈ ω, ∃ p q ∈ ω,
  IntProj ([<m, n>]~) = <p, q> ∧ <m, n> ~ <p, q>.
Proof with auto.
  intros m Hm n Hn.
  pose proof (preIntProj ([<m, n>]~)) as [x Hsg].
  apply pQuotI... assert (Hx: x ∈ ⎨x⎬) by apply SingI.
  rewrite <- Hsg in Hx. apply preIntProjE in Hx
    as [p [Hp [q [Hq [Hx [H H0]]]]]]...
  exists p. split... exists q. split... split...
  rewrite <- Hx. unfold IntProj. rewrite Hsg.
  apply union_single.
Qed.

Lemma intProj_η : ∀a ∈ ℤ, a = [IntProj a]~.
Proof with auto.
  intros a Ha.
  apply pQuotE in Ha as [m [Hm [n [Hn Ha]]]].
  pose proof (intProj m Hm n Hn)
    as [p [Hp [q [Hq [H1 H2]]]]].
  apply planeEquiv in H2... unfold IntEq. subst a.
  rewrite H1. apply int_ident...
Qed.

Close Scope Nat_scope.
Open Scope Int_scope.

(** 整数加法逆元 **)
Definition IntAddInv : set → set := λ a,
  let p := (IntProj a) in [<π2 p, π1 p>]~.
Notation "- a" := (IntAddInv a) : Int_scope.
Notation "a - b" := (a + (-b)) : Int_scope.

Lemma intAddInv : ∀ m n ∈ ω, (-[<m, n>]~) = [<n, m>]~.
Proof with eauto.
  intros m Hm n Hn.
  pose proof (intProj m Hm n Hn) as [p [Hp [q [Hq [H1 H2]]]]].
  destruct intEquiv_equiv as [_ [_ [_ Htr]]].
  apply ExtAx. split; intros Hx.
  - apply eqvcE in Hx. rewrite H1 in Hx. zfcrewrite.
    apply eqvcI. cut (<n, m> ~ <q, p>). intros. eapply Htr...
    apply planeEquivI... unfold IntEq.
    apply planeEquiv in H2... unfold IntEq in H2.
    rewrite (add_comm n), (add_comm q)...
  - apply eqvcI. rewrite H1. zfcrewrite.
    apply eqvcE in Hx. cut (<q, p> ~ <n, m>). intros. eapply Htr...
    apply planeEquivI... unfold IntEq.
    apply planeEquiv in H2... unfold IntEq in H2.
    rewrite (add_comm n), (add_comm q)...
Qed.

Lemma intAddInv_double : ∀a ∈ ℤ, --a = a.
Proof with auto.
  intros a Ha.
  apply pQuotE in Ha as [m [Hm [n [Hn Ha]]]]. subst a.
  rewrite intAddInv, intAddInv...
Qed.

Lemma intAddInv_ran : ∀a ∈ ℤ, -a ∈ ℤ.
Proof with auto.
  intros a Ha.
  apply pQuotE in Ha as [m [Hm [n [Hn Heq]]]]. subst a.
  rewrite intAddInv... apply pQuotI...
Qed.

Lemma neg_int_n : ∀ n, -Int n ∈ ℤ.
Proof with nauto.
  intros. apply intAddInv_ran...
Qed.
Hint Immediate neg_int_n : number_hint.

Lemma intAddInv_0 : -Int 0 = Int 0.
Proof. unfold Int. rewrite intAddInv; nauto. Qed.

Lemma intAddInv_annih : ∀a ∈ ℤ, a - a = Int 0.
Proof with nauto.
  intros a Ha.
  apply pQuotE in Ha as [m [Hm [n [Hn Ha]]]]. subst a.
  rewrite intAddInv, intAdd_m_n_p_q...
  apply int_ident; try apply add_ran...
  rewrite add_ident, add_ident', add_comm; try apply add_ran...
Qed.

Example intAdd_2_n3 : Int 2 - Int 3 = -Int 1.
Proof with nauto.
  unfold Int. rewrite intAddInv, intAddInv...
  rewrite intAdd_m_n_p_q, add_ident, add_ident'...
  apply int_ident... rewrite (pred 1), add_m_n, add_ident, add_ident'...
Qed.
