(** Based on "Elements of Set Theory" Chapter 5 Part 1 **)
(** Coq coding by choukh, June 2020 **)

Require Export ZFC.CH4.

(*** EST第五章1：二元函数与等价关系的相容性，整数加法, 整数乘法 ***)

(** 二元函数与等价关系的相容性 **)
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
  - (* is_relation *) intros p Hp.
    apply ReplE in Hp as [x []]. subst p. eexists...
  - apply domE in H...
  - (* single-valued *) intros y1 y2 Hy1 Hy2.
    apply domE in H as [y0 Hy0].
    apply ReplE in Hy0 as [a0 [_ Heq0]].
    apply ReplE in Hy1 as [a1 [Ha1 Heq1]].
    apply ReplE in Hy2 as [a2 [Ha2 Heq2]].
    apply op_correct in Heq0 as [Heq0 _].
    apply op_correct in Heq1 as [Heq1 Hy1].
    apply op_correct in Heq2 as [Heq2 Hy2].
    subst x y1 y2. rewrite <- Heq2 in Heq1. clear Heq2.
    apply op_correct in Heq1 as [H1 H2].
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
    + apply domE in Hx as [y Hp]. apply ReplE in Hp as [a [Hp Heq]].
      apply op_correct in Heq as [Heq _]. subst x.
      apply CProdE1 in Hp as [H1 H2]. apply CProdI; apply quotI...
    + apply CProdE2 in Hx as Hxp. apply op_η in Hxp.
      apply CProdE1 in Hx as [H1 H2].
      apply quotE in H1 as [a [Ha Heqa]].
      apply quotE in H2 as [b [Hb Heqb]].
      eapply domI. apply ReplAx. exists <a, b>. split.
      apply CProdI... rewrite π1_correct, π2_correct.
      apply op_correct... split. rewrite Hxp.
      apply op_correct... reflexivity.
  - (* ran F' ⊆ A/R *)
    intros y Hy. apply ranE in Hy as [].
    apply ReplE in H as [a [Ha Heq]].
    apply CProdE2 in Ha as Hap. apply op_η in Hap.
    apply op_correct in Heq as [_ Hy]. subst y. rewrite <- Hap.
    rewrite <- Hdf in Ha. apply func_correct in Ha as Hp...
    apply ranI in Hp as Hr. apply Hrf in Hr. apply quotI...
Qed.

Lemma quotionFunc_maps_onto : ∀ R A F,
  binCompatible R A F → F: A × A ⟹ A →
  (QuotionFunc R A F): (A/R) × (A/R) ⟹ A/R.
Proof with eauto.
  intros * Hc [Hf [Hdf Hrf]].
  pose proof (quotionFunc_maps_into) as [Hf' [Hdf' Hrf']]...
  split... split... apply sub_asym...
  intros y Hy. apply quotE in Hy as [p [Hp Heq]].
  rewrite <- Hrf in Hp. apply ranE in Hp as [x Hp].
  apply domI in Hp as Hd. rewrite Hdf in Hd.
  eapply ranI. apply ReplAx. exists x. split...
  apply op_correct. split... apply CProdE2 in Hd.
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
  apply ReplE in Hd as [b [Hb Heq]].
  apply op_correct in Heq as [H1 H2]. unfold F'.
  rewrite <- H2. eapply eqvc_ident; swap 1 3...
  - apply Hrf. eapply ranI... apply func_correct...
    rewrite Hdf. apply CProdE1 in Hb as []. apply CProdI...
  - apply Hrf. eapply ranI... apply func_correct...
    rewrite Hdf. apply CProdE1 in Hb as []. apply CProdI...
  - apply op_correct in H1 as [H11 H12].
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
  apply func_ext... rewrite Hd1, Hd2...
  intros x Hx. rewrite Hd1 in Hx.
  apply CProdE2 in Hx as Hxp. apply op_η in Hxp.
  apply CProdE1 in Hx as [Hx1 Hx2].
  apply quotE in Hx1 as [a [Ha Haeq]].
  apply quotE in Hx2 as [b [Hb Hbeq]].
  pose proof (H1 a Ha b Hb) as H3.
  pose proof (H2 a Ha b Hb) as H4. simpl in *. congruence.
Qed.

Notation "ℕ²" := (ω × ω).

Lemma N2xN2E : ∀x ∈ ℕ² × ℕ²,
  ∃ m n p q ∈ ω, x = <<m, n>, <p, q>>.
Proof with auto.
  intros x Hx.
  apply CProd_correct in Hx as [u [Hu [v [Hv Hx]]]].
  apply CProd_correct in Hu as [m [Hm [n [Hn Hu]]]].
  apply CProd_correct in Hv as [p [Hp [q [Hq Hv]]]].
  exists m. split... exists n. split...
  exists p. split... exists q. split... congruence.
Qed.

Definition IntEquiv : set := Relation ℕ² ℕ² (λ a b,
  let m := π1 a in let n := π2 a in
  let p := π1 b in let q := π2 b in
  m + q = p + n
).

Notation "~" := IntEquiv.
Notation "a ~ b" := (<a, b> ∈ IntEquiv) (at level 10).

Lemma IntEquivI : ∀ m n p q ∈ ω,
  m + q = p + n → <m, n> ~ <p, q>.
Proof with auto.
  intros m Hm n Hn p Hp q Hq Heq.
  apply SepI. apply CProdI; apply CProdI... zfcrewrite...
Qed.

Lemma IntEquivE1 : ∀ x y, x ~ y → ∃ m n p q ∈ ω,
  x = <m, n> ∧ y = <p, q> ∧ m + q = p + n.
Proof with auto.
  intros x y Hqv. apply SepE in Hqv as [Hxy Heq].
  apply N2xN2E in Hxy as [m [Hm [n [Hn [p [Hp [q [Hq Hxy]]]]]]]].
  apply op_correct in Hxy as []; subst.
  zfcrewrite. simpl in Heq.
  exists m. split... exists n. split...
  exists p. split... exists q. split...
Qed.

Lemma IntEquivE2 : ∀ m n p q, <m, n> ~ <p, q> →
  m ∈ ω ∧ n ∈ ω ∧ p ∈ ω ∧ q ∈ ω ∧ m + q = p + n.
Proof.
  intros * Hqv. apply IntEquivE1 in Hqv
    as [a [Ha [b [Hb [c [Hc [d [Hd [H1 [H2 H3]]]]]]]]]].
  apply op_correct in H1 as [];
  apply op_correct in H2 as []; subst a b c d. tauto.
Qed.

Theorem intEquiv_equiv : equiv IntEquiv ℕ².
Proof with eauto; try repeat apply add_ran; auto.
  repeat split.
  - intros x Hx. apply SepE in Hx as []...
  - intros x Hx. apply SepI. apply CProdI...
    apply CProd_correct in Hx as [a [Ha [b [Hb Heq]]]].
    subst x. zfcrewrite...
  - intros x y Hqv. apply IntEquivE1 in Hqv
      as [m [Hm [n [Hn [p [Hp [q [Hq [Hx [Hy Heq]]]]]]]]]].
    subst. apply SepI. apply CProdI; apply CProdI...
    zfcrewrite. simpl in *. symmetry...
  - intros x y z H1 H2.
    apply IntEquivE1 in H1
      as [m [Hm [n [Hn [p [Hp [q [Hq [Hx [Hy H1]]]]]]]]]]. subst.
    apply IntEquivE1 in H2
      as [p' [_ [q' [_ [r [Hr [s [Hs [Hx [Hy H2]]]]]]]]]]. subst.
    apply op_correct in Hx as []; subst p' q'.
    apply SepI. apply CProdI; apply CProdI...
    zfcrewrite. simpl in *.
    assert (m + q + (p + s) = p + n + (r + q)) by congruence.
    rewrite (add_comm (m+q)) in H...
    rewrite (add_assoc (p+s)) in H...
    rewrite (add_assoc (p+n)) in H...
    assert (p + s + m = p + n + r). {
      eapply add_elim; revgoals...
    }
    rewrite <- add_assoc, <- add_assoc in H0...
    rewrite add_comm, (add_comm p) in H0...
    rewrite add_comm, (add_comm r)...
    eapply add_elim; revgoals...
Qed.

(** 整数 **)
Definition ℤ : set := ℕ²/~.

Lemma IntI : ∀ m n ∈ ω, [<m, n>]~ ∈ ℤ.
Proof. intros m Hm n Hn. apply quotI. apply CProdI; auto. Qed.

Lemma IntE : ∀x ∈ ℤ, ∃ m n ∈ ω, x = [<m, n>]~.
Proof with auto.
  intros x Hx. apply quotE in Hx as [p [Hx Heq1]].
  apply CProd_correct in Hx as [a [Ha [b [Hb Heq2]]]].
  exists a. split... exists b. split... congruence.
Qed.

Lemma int_ident : ∀ m n p q ∈ ω,
  m + q = p + n ↔ [<m, n>]~ = [<p, q>]~.
Proof with eauto.
  intros m Hm n Hn p Hp q Hq. split; intros Heq.
  - eapply eqvc_ident; swap 1 3. apply intEquiv_equiv.
    apply CProdI... apply CProdI... apply IntEquivI...
  - cut (<m, n> ~ <p, q>). intros H.
    apply IntEquivE2 in H as [_ [_ [_ []]]]...
    eapply eqvc_ident; revgoals. apply Heq.
    apply intEquiv_equiv. apply CProdI... apply CProdI...
Qed.

(* 整数算术定义Helper *)
Definition IntArith : (set → set → set → set → set) → set :=
  λ F, Relation (ℕ² × ℕ²) ℕ² (λ x y,
  let m := π1 (π1 x) in let n := π2 (π1 x) in
  let p := π1 (π2 x) in let q := π2 (π2 x) in
  y = F m n p q
).

Lemma IntArithE : ∀ F x y, <x, y> ∈ IntArith F →
  ∃ m n p q ∈ ω, x = <<m, n>, <p, q>> ∧ y = F m n p q.
Proof with auto.
  intros * Hxy. apply SepE in Hxy as [Hxy Heq].
  apply CProdE1 in Hxy as [Hx _]; zfcrewrite.
  apply N2xN2E in Hx as [m [Hm [n [Hn [p [Hp [q [Hq Hx]]]]]]]].
  subst x. zfcrewrite. simpl in Heq.
  exists m. split... exists n. split...
  exists p. split... exists q. split...
Qed.

Lemma IntArithE_maps_onto : ∀ F,
  (∀ m n p q ∈ ω, F m n p q ∈ ℕ²) →
  (∀ a b ∈ ω, ∃ m n p q ∈ ω, <a, b> = F m n p q) →
  (IntArith F): ℕ² × ℕ² ⟹ ℕ².
Proof with eauto.
  intros F HF1 HF2. repeat split.
  - (* is_relation *) intros x Hx.
    apply SepE in Hx as [Hx _]. apply CProdE2 in Hx...
  - apply domE in H...
  - (* single-valued *) intros y1 y2 H1 H2.
    apply IntArithE in H1
      as [m1 [Hm1 [n1 [Hn1 [p1 [Hp1 [q1 [Hq1 [Hx1 Hy1]]]]]]]]].
    apply IntArithE in H2
      as [m2 [Hm2 [n2 [Hn2 [p2 [Hp2 [q2 [Hq2 [Hx2 Hy2]]]]]]]]].
    subst x. apply op_correct in Hx2 as [H1 H2].
    apply op_correct in H1 as [H11 H12].
    apply op_correct in H2 as [H21 H22]. congruence.
  - (* dom PreIntAdd = ℕ² × ℕ² *)
    apply ExtAx. intros x. split; intros Hx.
    + apply domE in Hx as [y Hx]. apply SepE in Hx as [Hx _].
      apply CProdE1 in Hx as []. zfcrewrite.
    + assert (Hx' := Hx).
      apply N2xN2E in Hx' as [m [Hm [n [Hn [p [Hp [q [Hq Hx']]]]]]]].
      eapply domI. apply SepI. apply CProdI...
      apply HF1. apply Hm. apply Hn. apply Hp. apply Hq.
      subst x. zfcrewrite. simpl. reflexivity.
  - (* ran PreIntAdd = ℕ² *)
    apply ExtAx. intros y. split; intros Hy.
    + apply ranE in Hy as [x Hp]. apply SepE in Hp as [Hp _].
      apply CProdE1 in Hp as []; zfcrewrite.
    + assert (Hy' := Hy).
      apply CProd_correct in Hy' as [a [Ha [b [Hb Heq]]]].
      edestruct HF2 as [m [Hm [n [Hn [p [Hp [q [Hq]]]]]]]].
      apply Ha. apply Hb. eapply ranI. apply SepI.
      apply CProdI... apply CProdI; apply CProdI.
      apply Hm. apply Hn. apply Hp. apply Hq.
      subst. zfcrewrite. simpl. congruence.
Qed.

Definition PreIntAdd : set :=
  IntArith (λ m n p q, <m + p, n + q>).
Notation "a +ᵥ b" := (PreIntAdd[<a, b>]) (at level 50).

Lemma add_m_n_rev : ∀x ∈ ω, ∃ m n ∈ ω, x = m + n.
Proof with auto.
  intros n Hn.
  set {n ∊ ω | λ n, ∃ a b ∈ ω, n = a + b} as N.
  ω_induction N Hn.
  - exists 0. split... exists 0. split... rewrite add_m_0...
  - destruct IH as [a [Ha [b [Hb Heq]]]].
    exists a. split... exists (b⁺). split. apply ω_inductive...
    rewrite add_m_n... congruence.
Qed.

Lemma preIntAdd_maps_onto : PreIntAdd: ℕ² × ℕ² ⟹ ℕ².
Proof with eauto.
  apply IntArithE_maps_onto.
  - intros m Hm n Hn p Hp q Hq. apply CProdI; apply add_ran...
  - intros a Ha b Hb.
    apply add_m_n_rev in Ha as [m [Hm [p [Hp Ha]]]].
    apply add_m_n_rev in Hb as [n [Hn [q [Hq Hb]]]].
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

Lemma preIntAdd_binCompatible : binCompatible IntEquiv ℕ² PreIntAdd.
Proof with eauto.
  split. apply intEquiv_equiv. split.
  destruct preIntAdd_maps_onto as [Hf [Hd Hr]].
  split... split... rewrite Hr. apply sub_refl. 
  intros x Hx y Hy u Hu v Hv H1 H2.
  apply CProd_correct in Hx as [m [Hm [n [Hn Hxeq]]]].
  apply CProd_correct in Hy as [p [Hp [q [Hq Hyeq]]]].
  apply CProd_correct in Hu as [m' [Hm' [n' [Hn' Hueq]]]].
  apply CProd_correct in Hv as [p' [Hp' [q' [Hq' Hveq]]]]. subst.
  apply IntEquivE2 in H1 as [_ [_ [_ [_ H1]]]].
  apply IntEquivE2 in H2 as [_ [_ [_ [_ H2]]]].
  rewrite preIntAdd_m_n_p_q, preIntAdd_m_n_p_q...
  apply SepI. apply CProdI; apply CProdI; apply add_ran...
  zfcrewrite. simpl.
  rewrite (add_comm m), add_assoc, (add_comm (p+m+n')),
    add_assoc, add_assoc, <- add_assoc, (add_comm q');
    try repeat apply add_ran...
  rewrite (add_comm m'), (add_assoc (p'+m')), (add_comm (p'+m'+n)),
    (add_assoc q), (add_assoc q), <- (add_assoc (q+p')), (add_comm q);
    try repeat apply add_ran... congruence.
Qed.

Close Scope Nat_scope.
Declare Scope Int_scope.
Open Scope Int_scope.
Delimit Scope Int_scope with z.

(** 整数加法 **)
Definition IntAdd : set :=
  QuotionFunc IntEquiv ℕ² PreIntAdd.
Notation "a + b" := (IntAdd[<a, b>]) : Int_scope.

Lemma intAdd_maps_onto : IntAdd: ℤ × ℤ ⟹ ℤ.
Proof.
  apply quotionFunc_maps_onto.
  apply preIntAdd_binCompatible.
  apply preIntAdd_maps_onto.
Qed.

Lemma intAdd_a_b : ∀ a b ∈ ℕ², [a]~ + [b]~ = [a +ᵥ b]~.
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
  apply IntE in Ha as [m [Hm [n [Hn Ha]]]]. subst a.
  apply IntE in Hb as [p [Hp [q [Hq Hb]]]]. subst b.
  rewrite intAdd_m_n_p_q... apply IntI; apply add_ran...
Qed.

Theorem intAdd_comm : ∀ a b ∈ ℤ, a + b = b + a.
Proof with auto.
  intros a Ha b Hb.
  apply IntE in Ha as [m [Hm [n [Hn Ha]]]]. subst a.
  apply IntE in Hb as [p [Hp [q [Hq Hb]]]]. subst b.
  repeat rewrite intAdd_m_n_p_q...
  apply int_ident; try apply add_ran...
  rewrite (add_comm m), (add_comm q)...
Qed.

Theorem intAdd_assoc : ∀ a b c ∈ ℤ,
  (a + b + c) = a + (b + c).
Proof with auto.
  intros a Ha b Hb c Hc.
  apply IntE in Ha as [m [Hm [n [Hn Ha]]]]. subst a.
  apply IntE in Hb as [p [Hp [q [Hq Hb]]]]. subst b.
  apply IntE in Hc as [r [Hr [s [Hs Hc]]]]. subst c.
  repeat rewrite intAdd_m_n_p_q; try apply add_ran...
  apply int_ident; try repeat apply add_ran...
  repeat rewrite add_assoc; try repeat apply add_ran...
Qed.

Definition Int : nat → set :=  λ n, [<n, 0>]~.

Theorem intAdd_ident : ∀a ∈ ℤ, a + Int 0 = a.
Proof with auto.
  intros a Ha. apply IntE in Ha as [m [Hm [n [Hn Ha]]]].
  subst a. unfold Int. rewrite intAdd_m_n_p_q, add_m_0, add_m_0...
Qed.

Theorem intAdd_inv_exists : ∀a ∈ ℤ, ∃b ∈ ℤ, a + b = Int 0.
Proof with auto.
  intros a Ha. apply IntE in Ha as [m [Hm [n [Hn Ha]]]].
  exists ([<n, m>]~). split. apply IntI...
  subst a. rewrite intAdd_m_n_p_q...
  apply int_ident; try apply add_ran...
  rewrite add_m_0, add_0_n, add_comm; try apply add_ran...
Qed.

Theorem intAdd_inv_unique : ∀a ∈ ℤ, ∃!b, b ∈ ℤ ∧ a + b = Int 0.
Proof with auto.
  intros a Ha. split. apply intAdd_inv_exists...
  intros b b' [Hb H1] [Hb' H2].
  rewrite <- intAdd_ident, <- (intAdd_ident b')...
  rewrite <- H2 at 1. rewrite <- H1.
  rewrite <- intAdd_assoc, (intAdd_comm a), (intAdd_comm b')...
  apply intAdd_ran...
Qed.

(* 相反数 *)
Definition IntInv : set → set := λ a,
  {λ p, <π2 p, π1 p> | p ∊ a}.
Notation "- a" := (IntInv a) : Int_scope.
Notation "a - b" := (a + (-b)) : Int_scope.

Lemma intInv : ∀ m n ∈ ω, (-[<m, n>]~) = [<n, m>]~.
Proof with auto.
  intros m Hm n Hn. apply ExtAx. split; intros Hx.
  - apply ReplE in Hx as [b [Hb Hx]].
    apply eqvcE in Hb. apply IntEquivE1 in Hb
      as [m' [Hm' [n' [Hn' [p [Hp [q [Hq [H1 [H2 H3]]]]]]]]]].
    apply op_correct in H1 as []; subst b m' n'; zfcrewrite.
    subst x. apply eqvcI. apply IntEquivI...
    rewrite add_comm, (add_comm q)...
  - apply eqvcE in Hx. apply IntEquivE1 in Hx
      as [n' [Hn' [m' [Hm' [q [Hq [p [Hp [H1 [H2 H3]]]]]]]]]].
    apply op_correct in H1 as []; subst x m' n'; zfcrewrite.
    apply ReplAx. exists <p, q>. split; zfcrewrite.
    apply eqvcI. apply IntEquivI...
    rewrite add_comm, (add_comm p)...
Qed.

Lemma intSub_self : ∀a ∈ ℤ, a - a = Int 0.
Proof with auto.
  intros a Ha.
  apply IntE in Ha as [m [Hm [n [Hn Ha]]]]. subst a.
  rewrite intInv, intAdd_m_n_p_q...
  apply int_ident; try apply add_ran...
  rewrite add_m_0, add_0_n, add_comm; try apply add_ran...
Qed.

Example intAdd_2_n3 : Int 2 - Int 3 = -Int 1.
Proof with auto.
  assert (H1w: 1 ∈ ω) by repeat apply ω_inductive.
  assert (H2w: 2 ∈ ω) by repeat apply ω_inductive.
  assert (H3w: 3 ∈ ω) by repeat apply ω_inductive.
  unfold Int. rewrite intInv, intInv...
  rewrite intAdd_m_n_p_q, add_m_0, add_0_n...
  apply int_ident... rewrite (Pred 1), add_m_n, add_m_0, add_0_n...
Qed.

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

Local Ltac mr := apply mul_ran.
Local Ltac ar := apply add_ran.
Local Ltac amr := apply add_ran; apply mul_ran. 

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
  apply IntEquivE2 in H1 as [_ [_ [_ [_ H1]]]].
  apply IntEquivE2 in H2 as [_ [_ [_ [_ H2]]]].
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
  apply add_elim in H35; [|ar;[amr|mr]|ar;[amr|mr]|mr]...
  assert (H46: m'⋅q + n⋅q + (n'⋅p' + n'⋅q) =
               m⋅q + n'⋅q + (n'⋅p + n'⋅q')) by congruence.
  rewrite (add_comm (m⋅q + n'⋅q)) in H46; [|amr;auto..].
  rewrite add_assoc, add_assoc in H46; [|amr|mr|mr|amr|mr..]...
  apply add_elim in H46; swap 2 4; [|mr|ar;[amr|mr]..]...
  rewrite (add_comm (m⋅p)), <- add_assoc in H35; [|mr;auto..].
  assert (H: n'⋅p + (m⋅p + m'⋅q') + (m'⋅q + n⋅q + n'⋅p') =
    m'⋅p' + m'⋅q + n⋅p + (n'⋅p + n'⋅q' + m⋅q)) by congruence.
  rewrite <- add_assoc in H; [|mr|amr|ar;[amr|mr]]...
  rewrite (add_comm (m'⋅p' + m'⋅q + n⋅p)) in H; [|ar;[amr|mr];auto..].
  rewrite <- (add_assoc (n'⋅p)) in H; [|mr;auto..].
  rewrite <- (add_assoc (n'⋅p)) in H; [|mr|amr|ar;[amr|mr]]...
  apply add_elim' in H; swap 2 4; [|mr|ar;[ar|ar;[ar|]];mr..]...
  rewrite (add_comm (m'⋅q)) in H; [|mr;auto..].
  rewrite (add_comm (n⋅q + m'⋅q)) in H; [|amr|mr]...
  rewrite add_assoc in H; [|amr|mr|amr]...
  rewrite add_assoc in H; [|ar;[ar|];mr|mr..]...
  rewrite (add_comm (m'⋅p' + m'⋅q)) in H; [|amr|mr]...
  rewrite add_assoc in H; [|amr|mr|amr]...
  rewrite add_assoc in H; [|ar;[ar|];mr|mr..]...
  apply add_elim in H; swap 2 4; [|mr|ar;[ar;[ar|]|];mr..]...
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
  apply IntE in Ha as [m [Hm [n [Hn Ha]]]]. subst a.
  apply IntE in Hb as [p [Hp [q [Hq Hb]]]]. subst b.
  rewrite intMul_m_n_p_q...
  apply IntI; apply add_ran; apply mul_ran...
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
  apply IntE in Ha as [m [Hm [n [Hn Ha]]]].
  apply IntE in Hb as [p [Hp [q [Hq Hb]]]]. subst.
  rewrite intMul_m_n_p_q, intMul_m_n_p_q...
  rewrite (mul_comm p), (mul_comm n)...
  rewrite (mul_comm m Hm q), (mul_comm n Hn p)...
  rewrite (add_comm (q⋅m)%n); [|apply mul_ran; auto ..]...
Qed.

Theorem intMul_assoc : ∀ a b c ∈ ℤ, (a ⋅ b ⋅ c = a ⋅ (b ⋅ c))%z.
Proof.
  intros a Ha b Hb c Hc.
  apply IntE in Ha as [m [Hm [n [Hn Ha]]]].
  apply IntE in Hb as [p [Hp [q [Hq Hb]]]].
  apply IntE in Hc as [r [Hr [s [Hs Hc]]]]. subst.
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
  apply IntE in Ha as [m [Hm [n [Hn Ha]]]].
  apply IntE in Hb as [p [Hp [q [Hq Hb]]]].
  apply IntE in Hc as [r [Hr [s [Hs Hc]]]]. subst.
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
  intros a Ha. apply IntE in Ha as [m [Hm [n [Hn Ha]]]].
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
  apply IntE in Ha as [m [Hm [n [Hn Ha]]]].
  apply IntE in Hb as [p [Hp [q [Hq Hb]]]].
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
  intros Heq; eapply nat_reg; revgoals;
  (eapply ch4_25 in H1; [apply H1 in H2| | | |]; [|auto..]);
  try apply Hw; [|
    |rewrite add_comm, (add_comm (n⋅p)) in H2; [|mr;auto..]
    |rewrite add_comm, (add_comm (n⋅q)) in H2; [|mr;auto..]
  ];
  rewrite Heq in H2; apply H2.
Qed.

Close Scope Nat_scope.
Open Scope Int_scope.

Example intMul_n1_a : ∀ a ∈ ℤ, -Int 1 ⋅ a = -a.
Proof with auto.
  intros a Ha.
  assert (H1w: 1 ∈ ω) by repeat apply ω_inductive.
  apply IntE in Ha as [m [Hm [n [Hn Ha]]]]. subst a.
  unfold Int. rewrite intInv, intInv, intMul_m_n_p_q...
  rewrite mul_0_n, mul_0_n, (mul_comm 1), (mul_comm 1)...
  rewrite mul_n_1, mul_n_1, add_0_n, add_0_n...
Qed.
