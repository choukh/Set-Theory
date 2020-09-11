(** Based on "Elements of Set Theory" Chapter 5 Part 4 **)
(** Coq coding by choukh, July 2020 **)

Require Export ZFC.EST5_3.
Require Import ZFC.lib.FuncFacts.

Local Ltac nz := try (apply nzIntE1; assumption).
Local Ltac mr := apply intMul_ran; nauto.
Local Ltac ar := apply intAdd_ran; nauto.
Local Ltac amr := apply intAdd_ran; apply intMul_ran; nauto.
Local Ltac nzmr := apply nzIntMul_ranI; nauto.

(*** EST第五章4：有理数的序，整数嵌入，关于逆元的运算律 ***)

Close Scope Rat_scope.
Open Scope Int_scope.

Lemma intPos_sn : ∀ n, intPos (Int (S n)).
Proof with nauto.
  intros. apply intLt... rewrite add_ident, add_ident...
  apply suc_has_0. apply embed_ran.
Qed.
Hint Immediate intPos_sn : number_hint.

Lemma intNeg_sn : ∀ n, intNeg (-Int (S n)).
Proof. intros. apply intPos_neg. nauto. Qed.
Hint Immediate intNeg_sn : number_hint.

Lemma intMul_pos_prod : ∀a b ∈ ℤ,
  intPos a → intPos b → intPos (a ⋅ b).
Proof with nauto.
  intros a Ha b Hb Hpa Hpb. unfold intPos.
  rewrite <- (intMul_0_l b)...
  apply intLt_both_side_mul...
Qed.

Lemma intMul_pos_factor : ∀a b ∈ ℤ,
  intPos b → intPos (a ⋅ b) → intPos a.
Proof with neauto.
  intros a Ha b Hb Hpb Hpp.
  destruct (classic (a = Int 0)).
  - subst a. exfalso. rewrite intMul_0_l in Hpp...
    eapply intLt_not_refl; revgoals...
  - apply intLt_connected in H as []... exfalso.
    eapply intLt_both_side_mul in H...
    rewrite intMul_0_l in H...
    eapply intLt_not_refl; revgoals.
    eapply intLt_tranr... mr.
Qed.

Lemma intMul_neg_factor : ∀a b ∈ ℤ,
  intPos b → intNeg (a ⋅ b) → intNeg a.
Proof with neauto.
  intros a Ha b Hb Hpb Hpp.
  destruct (classic (a = Int 0)).
  - subst a. exfalso. rewrite intMul_0_l in Hpp...
    eapply intLt_not_refl; revgoals...
  - apply intLt_connected in H as []... exfalso.
    eapply intLt_both_side_mul in H.
    apply H in Hpb as Hc.
    rewrite (intMul_comm b), intMul_0_l in Hc...
    eapply intLt_not_refl; revgoals.
    eapply intLt_tranr... mr. nauto. auto. auto.
Qed.

Lemma pQuotE_ratPosDenom : ∀r ∈ ℚ, ∃a ∈ ℤ, ∃b ∈ ℤ',
  r = [<a, b>]~ ∧ intPos b.
Proof with nauto.
  intros r Hr.
  apply pQuotE in Hr as [a [Ha [b [Hb Hr]]]]. subst.
  apply nzIntE0 in Hb as Hb0.
  apply intLt_connected in Hb0 as [Hnb|Hpb]; nz...
  - assert (Hnaz: -a ∈ ℤ) by (apply intAddInv_ran; auto).
    assert (Hnbz: -b ∈ ℤ') by (apply intAddInv_inzInt; auto).
    exists (-a). split... exists (-b). split...
    split. apply rat_ident... rewrite intMul_addInv_lr; nz...
    apply intNeg_pos...
  - exists a. split... exists b. split...
Qed.

(** 有理数的序 **)

Lemma rat_orderable : ∀ a b a' b' c d c' d',
  intPos b → intPos d → intPos b' → intPos d' →
  <a, b> ~ <a', b'> → <c, d> ~ <c', d'> →
  a ⋅ d <𝐳 c ⋅ b ↔ a' ⋅ d' <𝐳 c' ⋅ b'.
Proof.
  intros * Hpb Hpd Hpb' Hpd' H1 H2.
  apply planeEquivE2 in H1 as [H1 [Ha [Hb [Ha' Hb']]]].
  apply planeEquivE2 in H2 as [H2 [Hc [Hd [Hc' Hd']]]].
  assert (Had: a⋅d ∈ ℤ) by (mr;nz).
  assert (Hcb: c⋅b ∈ ℤ) by (mr;nz).
  assert (Hb'd': b'⋅d' ∈ ℤ) by (mr;nz).
  assert (Hpb'd': intPos (b'⋅d')) by (apply intMul_pos_prod; auto; nz).
  rewrite (intLt_both_side_mul _ Had _ Hcb _ Hb'd' Hpb'd').
  rewrite (intMul_assoc a), (intMul_comm d), (intMul_assoc b'),
    <- (intMul_assoc a), (intMul_assoc c), (intMul_comm b),
    (intMul_comm b'), (intMul_assoc d'), <- (intMul_assoc c),
    H1, H2, (intMul_assoc a'), (intMul_comm b), (intMul_assoc d'),
    <- (intMul_assoc a'), (intMul_comm d), (intMul_assoc c'),
    (intMul_comm d), (intMul_assoc b'), <- (intMul_assoc c');
    [|auto;nz;mr;nz..].
  assert (Ha'd': a'⋅d' ∈ ℤ) by (mr;nz).
  assert (Hc'b': c'⋅b' ∈ ℤ) by (mr;nz).
  assert (Hbd: b⋅d ∈ ℤ) by (mr;nz).
  assert (Hpbd: intPos (b⋅d)) by (apply intMul_pos_prod; auto; nz).
  erewrite <- (intLt_both_side_mul _ Ha'd' _ Hc'b' _ Hbd Hpbd).
  reflexivity.
Qed.

(* 有理数的小于关系 *)
Definition RatLt : set := Relation ℚ ℚ (λ r s,
  let u := RatProj r in let v := RatProj s in
  let a := π1 u in let b := π2 u in
  let c := π1 v in let d := π2 v in
  a ⋅ d <𝐳 c ⋅ b
).
Notation "a <𝐪 b" := (<a, b> ∈ RatLt) (at level 70).

Lemma ratLtI : ∀a ∈ ℤ, ∀b ∈ ℤ', ∀c ∈ ℤ, ∀d ∈ ℤ',
  intPos b → intPos d → 
  a ⋅ d <𝐳 c ⋅ b → [<a, b>]~ <𝐪 [<c, d>]~.
Proof with eauto.
  intros a Ha b Hb c Hc d Hd Hpb Hpd Hlt.
  apply SepI. apply CProdI; apply pQuotI... zfcrewrite.
  pose proof (ratProj a Ha b Hb)
    as [a' [Ha' [b' [Hb' [H11 [H12 [_ Hpb']]]]]]].
  pose proof (ratProj c Hc d Hd)
    as [c' [Hc' [d' [Hd' [H21 [H22 [_ Hpd']]]]]]].
  pose proof ratEquiv_equiv as [_ [_ [Hsym _]]].
  rewrite H11, H21. simpl. zfcrewrite.
  eapply rat_orderable; revgoals...
Qed.

Lemma ratLtE : ∀ r s, r <𝐪 s → ∃a ∈ ℤ, ∃b ∈ ℤ', ∃c ∈ ℤ, ∃d ∈ ℤ',
  intPos b ∧ intPos d ∧
  r = [<a, b>]~ ∧ s = [<c, d>]~ ∧ a ⋅ d <𝐳 c ⋅ b.
Proof with eauto.
  intros r s Hlt. apply SepE in Hlt as [H1 H2].
  apply CProdE1 in H1 as [Hr Hs]; zfcrewrite.
  apply pQuotE_ratPosDenom in Hr as [a [Ha [b [Hb [Hr Hpb]]]]].
  apply pQuotE_ratPosDenom in Hs as [c [Hc [d [Hd [Hs Hpd]]]]]. subst.
  exists a. split... exists b. split...
  exists c. split... exists d. split... repeat split...
  pose proof (ratProj a Ha b Hb)
    as [a' [Ha' [b' [Hb' [H11 [H12 [_ Hpb']]]]]]].
  pose proof (ratProj c Hc d Hd)
    as [c' [Hc' [d' [Hd' [H21 [H22 [_ Hpd']]]]]]].
  rewrite H11, H21 in H2. simpl in H2. zfcrewrite.
  eapply rat_orderable; revgoals...
Qed.

Lemma ratLt : ∀a ∈ ℤ, ∀b ∈ ℤ', ∀c ∈ ℤ, ∀d ∈ ℤ',
  intPos b → intPos d →
  [<a, b>]~ <𝐪 [<c, d>]~ ↔ a ⋅ d <𝐳 c ⋅ b.
Proof with eauto.
  intros a Ha b Hb c Hc d Hd Hpb Hpd. split; intros.
  - apply SepE in H as [H1 H2].
    apply CProdE1 in H1 as [Hr Hs]; zfcrewrite.
    pose proof (ratProj a Ha b Hb)
      as [a' [Ha' [b' [Hb' [H11 [H12 [_ Hpb']]]]]]].
    pose proof (ratProj c Hc d Hd)
      as [c' [Hc' [d' [Hd' [H21 [H22 [_ Hpd']]]]]]].
    rewrite H11, H21 in H2. simpl in H2. zfcrewrite.
    eapply rat_orderable; revgoals...
  - apply ratLtI...
Qed.

Lemma ratLt_not_refl : ∀r ∈ ℚ, r <𝐪 r → ⊥.
Proof with eauto.
  intros r Hr Hc.
  apply pQuotE_ratPosDenom in Hr as [a [Ha [b [Hb [Hr Hpb]]]]]. subst r.
  apply ratLt in Hc... eapply intLt_not_refl; revgoals... mr;nz.
Qed.

Lemma ratNeqE : ∀a ∈ ℤ, ∀b ∈ ℤ', ∀c ∈ ℤ, ∀d ∈ ℤ',
  [<a, b>]~ ≠ [<c, d>]~ → a ⋅ d ≠ c ⋅ b.
Proof with auto.
  intros a Ha b Hb c Hc d Hd Hnq Heq.
  apply Hnq. apply rat_ident...
Qed.

Lemma ratLt_rel : binRel RatLt ℚ.
Proof with auto.
  intros x Hx. apply SepE in Hx as []...
Qed.

Lemma ratLt_tranr : tranr RatLt.
Proof with auto.
  intros x y z H1 H2.
  assert (H1' := H1). assert (H2' := H2).
  apply ratLtE in H1' as [a [Ha [b [Hb [c [Hc [d [Hd
    [Hpb [Hpd [Hx [Hy _]]]]]]]]]]]].
  apply ratLtE in H2' as [_ [_ [_ [_ [e [He [f [Hf
    [_ [Hpf [_ [Hz _]]]]]]]]]]]]. subst x y z.
  apply ratLt in H1... apply ratLt in H2... apply ratLt...
  assert (H1': a ⋅ d ⋅ f <𝐳 c ⋅ b ⋅ f)
    by (apply intLt_both_side_mul; auto; nz; mr; nz).
  assert (H2': c ⋅ f ⋅ b <𝐳 e ⋅ d ⋅ b)
    by (apply intLt_both_side_mul; auto; nz; mr; nz).
  rewrite
    (intMul_assoc a), (intMul_comm d), <- (intMul_assoc a),
    (intMul_assoc c), (intMul_comm b), <- (intMul_assoc c)
    in H1'; nz...
  rewrite
    (intMul_assoc e), (intMul_comm d), <- (intMul_assoc e)
    in H2'; nz...
  eapply intLt_both_side_mul; revgoals; [
    eapply intLt_tranr; revgoals|..
  ]; try eassumption; nz; mr; nz.
Qed.

Lemma ratLt_irreflexive : irreflexive RatLt ℚ.
Proof with auto.
  intros [x [Hx Hlt]]. apply ratLtE in Hlt
    as [a [Ha [b [Hb [c [Hc [d [Hd [Hpb [Hpd [H1 [H2 Hlt]]]]]]]]]]]].
  subst x. apply rat_ident in H2... rewrite H2 in Hlt.
  eapply intLt_not_refl; revgoals; eauto; mr; nz.
Qed.

Lemma ratLt_connected : connected RatLt ℚ.
Proof with auto.
  intros x Hx y Hy Hnq.
  apply pQuotE_ratPosDenom in Hx as [a [Ha [b [Hb [Hx Hpb]]]]].
  apply pQuotE_ratPosDenom in Hy as [c [Hc [d [Hd [Hy Hpd]]]]].
  subst x y. apply ratNeqE in Hnq...
  apply intLt_connected in Hnq as []; [| |mr;nz..].
  + left. apply ratLtI...
  + right. apply ratLtI...
Qed.

Lemma ratLt_trich : trich RatLt ℚ.
Proof with auto.
  eapply trich_iff. apply ratLt_rel. apply ratLt_tranr. split.
  apply ratLt_irreflexive. apply ratLt_connected.
Qed.

Theorem ratLt_totalOrd : totalOrd RatLt ℚ.
Proof with auto.
  split. apply ratLt_rel. split. apply ratLt_tranr.
  apply ratLt_trich.
Qed.

Close Scope Int_scope.
Open Scope Rat_scope.

Definition ratPos : set → Prop := λ r, Rat 0 <𝐪 r.
Definition ratNeg : set → Prop := λ r, r <𝐪 Rat 0.

Lemma rat_neq_0 : ∀r ∈ ℚ, ratPos r ∨ ratNeg r → r ≠ Rat 0.
Proof.
  intros r Hr [Hpr|Hnr]; intros H; subst;
  eapply ratLt_not_refl; revgoals; eauto.
Qed.

Lemma ratPos_intPos : ∀a ∈ ℤ, ∀b ∈ ℤ',
  intPos b → ratPos ([<a, b>]~) → intPos a.
Proof with nauto.
  intros a Ha b Hb Hpb Hpr. apply ratLt in Hpr...
  rewrite intMul_0_l, intMul_ident in Hpr... nz.
Qed.

Lemma ratLt_addInv : ∀ q r ∈ ℚ, q <𝐪 r ↔ -r <𝐪 -q.
Proof with auto.
  intros q Hq r Hr.
  apply pQuotE_ratPosDenom in Hq as [a [Ha [b [Hb [Hp Hpb]]]]].
  apply pQuotE_ratPosDenom in Hr as [c [Hc [d [Hd [Hq Hpd]]]]].
  subst q r. split; intros.
  - apply ratLt in H...
    rewrite ratAddInv, ratAddInv... apply ratLt...
    apply intAddInv_ran... apply intAddInv_ran...
    rewrite intMul_addInv_l, intMul_addInv_l; nz...
    apply intLt_addInv in H; auto; mr; nz.
  - rewrite ratAddInv, ratAddInv in H... apply ratLt in H...
    rewrite intMul_addInv_l, intMul_addInv_l in H; nz...
    apply ratLt... apply intLt_addInv; auto; mr; nz.
    apply intAddInv_ran... apply intAddInv_ran...
Qed.

Lemma ratLt_mulInv : ∀ q r ∈ ℚ, ratPos q → q <𝐪 r → r⁻¹ <𝐪 q⁻¹.
Proof with neauto.
  intros q Hq r Hr Hpq H.
  apply pQuotE_ratPosDenom in Hq as [a [Ha [b [Hb [Hp Hpb]]]]].
  apply pQuotE_ratPosDenom in Hr as [c [Hc [d [Hd [Hq Hpd]]]]].
  subst q r. apply ratLt in H...
  assert (Hpa: intPos a). { eapply ratPos_intPos; revgoals... }
  assert (Ha': a ∈ ℤ'). { apply nzIntI0... apply int_neq_0... }
  assert (Hpad: intPos (a ⋅ d)%z) by (apply intMul_pos_prod; nz; auto).
  assert (Hpcb: intPos (c ⋅ b)%z) by (eapply intLt_tranr; eauto).
  assert (Hpc: intPos c) by (eapply intMul_pos_factor; revgoals; eauto; nz).
  assert (Hc': c ∈ ℤ'). { apply nzIntI0... apply int_neq_0... }
  rewrite ratMulInv, ratMulInv... apply ratLt; nz...
  rewrite intMul_comm, (intMul_comm b); nz...
Qed.

Lemma ratPos_rat : ∀ r, ratPos r → r ∈ ℚ.
Proof with auto.
  intros. apply SepE in H as [H _].
  apply CProdE1 in H as [_ H]. zfcrewrite.
Qed.

Lemma ratNeg_rat : ∀ r, ratNeg r → r ∈ ℚ.
Proof with auto.
  intros. apply SepE in H as [H _].
  apply CProdE1 in H as [H _]. zfcrewrite.
Qed.

Lemma ratPos_neg : ∀ r, ratPos r → ratNeg (-r).
Proof with nauto.
  intros. assert (Hr: r ∈ ℚ) by (apply ratPos_rat; auto).
  apply ratLt_addInv... apply ratAddInv_ran...
  rewrite ratAddInv_0, ratAddInv_double...
Qed.

Lemma ratNeg_pos : ∀ r, ratNeg r → ratPos (-r).
Proof with nauto.
  intros. assert (Hr: r ∈ ℚ) by (apply ratNeg_rat; auto).
  rewrite (ratLt_addInv _ Hr _ (rat_n 0)) in H.
  rewrite ratAddInv_0 in H...
Qed.

Lemma ratPos_mulInv : ∀ r, ratPos r → ratPos r⁻¹.
Proof with neauto.
  intros. assert (Hr: r ∈ ℚ) by (apply ratPos_rat; auto).
  apply pQuotE_ratPosDenom in Hr as [a [Ha [b [Hb' [Hp Hpb]]]]].
  assert (Hb: b ∈ ℤ) by (apply nzIntE1; auto).
  subst. apply ratLt in H...
  rewrite intMul_0_l, intMul_ident in H...
  assert (Ha': a ∈ ℤ'). {
    apply nzIntI0... intros Heq. rewrite Heq in H.
    eapply intLt_not_refl; revgoals...
  }
  rewrite ratMulInv... apply ratLt...
  rewrite intMul_0_l, intMul_ident...
Qed.

Lemma ratPos_sm_sn : ∀ m n, ratPos ([<Int (S m), Int (S n)>]~).
Proof with nauto.
  intros. apply ratLt...
  rewrite intMul_0_l, intMul_ident... apply intPos_sn.
Qed.
Hint Immediate ratPos_sm_sn : number_hint.

Lemma ratPos_sn : ∀ n, ratPos (Rat (S n)).
Proof. intros. unfold Rat. nauto. Qed.
Hint Immediate ratPos_sn : number_hint.

Lemma ratNeg_sn : ∀ n, ratNeg (-Rat (S n)).
Proof. intros. apply ratPos_neg. nauto. Qed.
Hint Immediate ratNeg_sn : number_hint.

Lemma ratPos_r_sn : ∀ n, ratPos (Rat (S n))⁻¹.
Proof. intros n. unfold Rat. rewrite ratMulInv; nauto. Qed.
Hint Immediate ratPos_r_sn : number_hint.

Notation "r ≤ s" := (r <𝐪 s ∨ r = s) (at level 70) : Rat_scope.
Notation "r ≥ s" := (s ≤ r) (only parsing, at level 70): Rat_scope.

Definition ratNonNeg : set → Prop := λ r, r ≥ Rat 0.
Definition ratNonPos : set → Prop := λ r, r ≤ Rat 0.

Lemma ratNonNeg_not_neg : ∀r ∈ ℚ, ¬ ratNeg r ↔ ratNonNeg r.
Proof with neauto.
  intros r Hr. split; intros.
  - destruct (classic (ratNonNeg r))... exfalso.
    apply not_or_and in H0 as [].
    apply ratLt_connected in H1 as []...
  - intros Hn. destruct H.
    + eapply ratLt_not_refl; revgoals.
      eapply ratLt_tranr... auto.
    + subst. eapply ratLt_not_refl...
Qed.

Lemma ratNeg_not_nonNeg : ∀r ∈ ℚ, ¬ ratNonNeg r ↔ ratNeg r.
Proof with neauto.
  intros r Hr. split; intros.
  - destruct (classic (ratNeg r))... exfalso.
    apply ratNonNeg_not_neg in H0...
  - intros Hnn. eapply ratNonNeg_not_neg...
Qed.

Lemma ratNonPos_not_pos : ∀r ∈ ℚ, ¬ ratPos r ↔ ratNonPos r.
Proof with neauto.
  intros r Hr. split; intros.
  - destruct (classic (ratNonPos r))... exfalso.
    apply not_or_and in H0 as [].
    apply ratLt_connected in H1 as []...
  - intros Hp. destruct H.
    + eapply ratLt_not_refl; revgoals.
      eapply ratLt_tranr... nauto.
    + subst. eapply ratLt_not_refl...
Qed.

Lemma ratPos_not_nonPos : ∀r ∈ ℚ, ¬ ratNonPos r ↔ ratPos r.
Proof with neauto.
  intros r Hr. split; intros.
  - destruct (classic (ratPos r))... exfalso.
    apply ratNonPos_not_pos in H0...
  - intros Hnp. eapply ratNonPos_not_pos...
Qed.

(* 有理数绝对值 *)
Definition RatAbs : set → set := λ r,
  match (ixm (ratPos (-r))) with
  | inl _ => -r
  | inr _ => r
  end.
Notation "| r |" := (RatAbs r) (at level 40) : Rat_scope.

Lemma ratAbs_geq_0 : ∀r ∈ ℚ, ratNonNeg (|r|).
Proof with neauto.
  intros r Hr. unfold RatAbs.
  destruct (ixm (ratPos (-r))) as [H|H].
  - destruct (classic (r = Rat 0)).
    + right. rewrite H0, ratAddInv_0...
    + apply ratLt_connected in H0 as []... left...
      apply ratPos_neg in H0. exfalso.
      eapply ratLt_not_refl; revgoals.
      eapply ratLt_tranr... apply ratAddInv_ran...
  - destruct (classic (r = Rat 0)). right...
    apply ratLt_connected in H0 as []...
    exfalso. apply H. apply ratNeg_pos... left...
Qed.

Close Scope Rat_scope.
Open Scope Int_scope.

Theorem ratLt_both_side_add : ∀ r s t ∈ ℚ,
  r <𝐪 s ↔ (r + t <𝐪 s + t)%q.
Proof with auto.
  intros r Hr s Hs t Ht.
  apply pQuotE_ratPosDenom in Hr as [a [Ha [b [Hb [Hr Hpb]]]]].
  apply pQuotE_ratPosDenom in Hs as [c [Hc [d [Hd [Hs Hpd]]]]].
  apply pQuotE_ratPosDenom in Ht as [e [He [f [Hf [Ht Hpf]]]]].
  subst r s t. rewrite (ratLt a Ha b Hb c Hc d Hd Hpb Hpd).
  rewrite ratAdd_a_b_c_d, ratAdd_a_b_c_d...
  assert (Hz1: a⋅f + e⋅b ∈ ℤ) by (amr;nz).
  assert (Hz2: b⋅f ∈ ℤ') by nzmr.
  assert (Hz3: c⋅f + e⋅d ∈ ℤ) by (amr;nz).
  assert (Hz4: d⋅f ∈ ℤ') by nzmr.
  assert (Hpbf: intPos (b⋅f)) by (apply intMul_pos_prod; nz; auto).
  assert (Hpdf: intPos (d⋅f)) by (apply intMul_pos_prod; nz; auto).
  rewrite (ratLt _ Hz1 _ Hz2 _ Hz3 _ Hz4 Hpbf Hpdf).
  rewrite intMul_distr', intMul_distr'; [|mr;nz..].
  assert (Hzf: f ∈ ℤ) by nz.
  rewrite
    (intMul_assoc a), (intMul_comm f),
    (intMul_assoc d), <- (intMul_assoc a),
    (intMul_assoc c), (intMul_comm f Hzf (b⋅f)),
    (intMul_assoc b), <- (intMul_assoc c),
    (intMul_assoc e), (intMul_comm b),
    (intMul_assoc d), <- (intMul_assoc e), (intMul_comm b);
      nz; auto; [|mr;nz..].
  assert (Hz5: (a⋅d)⋅(f⋅f) ∈ ℤ) by (mr;mr;nz).
  assert (Hz6: (c⋅b)⋅(f⋅f) ∈ ℤ) by (mr;mr;nz).
  assert (Hz7: (e⋅d)⋅(f⋅b) ∈ ℤ) by (mr;mr;nz).
  rewrite <- (intLt_both_side_add _ Hz5 _ Hz6 _ Hz7).
  apply intLt_both_side_mul; revgoals; [|mr;nz..].
  apply intMul_pos_prod...
Qed.

Theorem ratLt_both_side_mul : ∀ r s t ∈ ℚ,
  ratPos t → r <𝐪 s ↔ (r ⋅ t <𝐪 s ⋅ t)%q.
Proof with nauto.
  cut (∀ r s t ∈ ℚ, ratPos t → r <𝐪 s → (r ⋅ t <𝐪 s ⋅ t)%q).
  intros Hright r Hr s Hs t Ht Hpt. split; intros Hlt.
  apply Hright... destruct (classic (r = s)).
  subst. exfalso. eapply ratLt_not_refl; revgoals.
  apply Hlt. apply ratMul_ran...
  apply ratLt_connected in H as []... exfalso.
  apply (Hright s Hs r Hr t Ht Hpt) in H.
  eapply ratLt_not_refl; revgoals.
  eapply ratLt_tranr; eauto. apply ratMul_ran...
  intros r Hr s Hs t Ht Hpt Hlt.
  apply pQuotE_ratPosDenom in Hr as [a [Ha [b [Hb [Hr Hpb]]]]].
  apply pQuotE_ratPosDenom in Hs as [c [Hc [d [Hd [Hs Hpd]]]]].
  apply pQuotE_ratPosDenom in Ht as [e [He [f [Hf [Ht Hpf]]]]]. subst.
  apply ratLt in Hpt... rewrite intMul_0_l, intMul_ident in Hpt; nz...
  apply ratLt in Hlt... rewrite ratMul_a_b_c_d, ratMul_a_b_c_d...
  apply ratLt. mr. nzmr. mr. nzmr.
  apply intMul_pos_prod; nz... apply intMul_pos_prod; nz...
  rewrite
    (intMul_assoc a), (intMul_comm e),
    (intMul_assoc d), <- (intMul_assoc a),
    (intMul_assoc c), (intMul_comm e),
    (intMul_assoc b), <- (intMul_assoc c);
      nz; auto; [|mr;nz..].
  apply intLt_both_side_mul... mr;nz. mr;nz. mr;nz.
  apply intMul_pos_prod; nz...
Qed.

Close Scope Int_scope.
Open Scope Rat_scope.

Corollary ratLt_both_side_add' : ∀ r s t ∈ ℚ,
  r <𝐪 s ↔ (t + r <𝐪 t + s)%q.
Proof with auto.
  intros r Hr s Hs t Ht.
  rewrite ratAdd_comm, (ratAdd_comm t)...
  apply ratLt_both_side_add...
Qed.

Corollary ratLt_both_side_add_tran : ∀ q r s t ∈ ℚ,
  q <𝐪 r → s <𝐪 t → q + s <𝐪 r + t.
Proof with auto.
  intros q Hq r Hr s Hs t Ht H1 H2.
  apply (ratLt_both_side_add q Hq r Hr s Hs) in H1.
  apply (ratLt_both_side_add s Hs t Ht r Hr) in H2.
  rewrite (ratAdd_comm s), (ratAdd_comm t) in H2...
  eapply ratLt_tranr; eauto.
Qed.

Corollary ratLt_both_side_mul' : ∀ r s t ∈ ℚ,
  ratPos t → r <𝐪 s ↔ t ⋅ r <𝐪 t ⋅ s.
Proof with auto.
  intros r Hr s Hs t Ht.
  rewrite ratMul_comm, (ratMul_comm t)...
  apply ratLt_both_side_mul...
Qed.

Corollary ratLt_both_side_mul_tran : ∀ q r s t ∈ ℚ,
  ratPos r → ratPos s → q <𝐪 r → s <𝐪 t → q ⋅ s <𝐪 r ⋅ t.
Proof with auto.
  intros q Hq r Hr s Hs t Ht Hpr Hps H1 H2.
  apply (ratLt_both_side_mul q Hq r Hr s Hs) in H1...
  apply (ratLt_both_side_mul s Hs t Ht r Hr) in H2...
  rewrite (ratMul_comm s), (ratMul_comm t) in H2...
  eapply ratLt_tranr; eauto.
Qed.

Theorem ratAdd_cancel : ∀ r s t ∈ ℚ, r + t = s + t → r = s.
Proof with eauto.
  intros r Hr s Hs t Ht Heq.
  assert (r + t - t = s + t - t) by congruence.
  rewrite ratAdd_assoc, (ratAdd_assoc s) in H...
  rewrite ratAddInv_annih, ratAdd_ident, ratAdd_ident in H...
  apply ratAddInv_ran... apply ratAddInv_ran...
Qed.

Corollary ratAdd_cancel' : ∀ r s t ∈ ℚ, t + r = t + s → r = s.
Proof with eauto.
  intros r Hr s Hs t Ht Heq.
  eapply ratAdd_cancel...
  rewrite ratAdd_comm, (ratAdd_comm s)...
Qed.

Theorem ratMul_cancel : ∀ r s ∈ ℚ, ∀ t ∈ ℚ', r ⋅ t = s ⋅ t → r = s.
Proof with eauto.
  intros r Hr s Hs t Ht' Heq.
  assert (r ⋅ t / t = s ⋅ t / t) by congruence.
  assert (Ht: t ∈ ℚ) by (apply nzRatE1; auto).
  assert (Hrt: t⁻¹ ∈ ℚ) by (apply nzRatE1; apply ratMulInv_ran; auto).
  rewrite (ratMul_assoc r), (ratMul_assoc s) in H...
  rewrite ratMulInv_annih, ratMul_ident, ratMul_ident in H...
Qed.

Corollary ratMul_cancel' : ∀ r s ∈ ℚ, ∀ t ∈ ℚ', t ⋅ r = t ⋅ s → r = s.
Proof with eauto.
  intros r Hr s Hs t Ht Heq.
  eapply ratMul_cancel...
  rewrite ratMul_comm, (ratMul_comm s); auto; apply nzRatE1...
Qed.

Corollary ratLeq_both_side_mul : ∀ r s t ∈ ℚ,
  ratPos t → r ≤ s ↔ r ⋅ t ≤ s ⋅ t.
Proof with auto.
  intros r Hr s Hs t Ht Hpt. split; intros [Hlt|Heq].
  - left. apply ratLt_both_side_mul...
  - right. subst...
  - left. apply ratLt_both_side_mul in Hlt...
  - right. apply ratMul_cancel in Heq...
    apply nzRatI0... apply rat_neq_0...
Qed.

Lemma ratAdd_pos_sum : ∀ r s ∈ ℚ,
  ratPos r → ratPos s → ratPos (r + s).
Proof with nauto.
  intros r Hr s Hs Hnr Hns.
  unfold ratPos. rewrite <- (ratAdd_ident (Rat 0))...
  apply ratLt_both_side_add_tran...
Qed.

Lemma ratAdd_neg_sum : ∀ r s ∈ ℚ,
  ratNeg r → ratNeg s → ratNeg (r + s).
Proof with nauto.
  intros r Hr s Hs Hnr Hns.
  unfold ratNeg. rewrite <- (ratAdd_ident (Rat 0))...
  apply ratLt_both_side_add_tran...
Qed.

Lemma ratAdd_nonNeg_sum : ∀ p q ∈ ℚ,
  ratNonNeg p → ratNonNeg q → ratNonNeg (p + q).
Proof with nauto.
  intros p Hp q Hq Hnnp Hnnq.
  destruct (classic (p = Rat 0 ∨ q = Rat 0)).
  - destruct H; subst.
    rewrite ratAdd_ident'... rewrite ratAdd_ident...
  - apply not_or_and in H as [].
    destruct Hnnp; destruct Hnnq; [|exfalso; auto..].
    left. apply ratAdd_pos_sum...
Qed.

Lemma ratMul_pos_prod : ∀ p q ∈ ℚ,
  ratPos p → ratPos q → ratPos (p ⋅ q).
Proof with nauto.
  intros p Hp q Hq Hpp Hpq. unfold ratPos.
  rewrite <- (ratMul_0_l q)...
  apply ratLt_both_side_mul...
Qed.

Lemma ratMul_neg_prod : ∀ p q ∈ ℚ,
  ratPos p → ratNeg q → ratNeg (p ⋅ q).
Proof with nauto.
  intros p Hp q Hq Hpp Hnq.
  unfold ratNeg. rewrite ratMul_comm, <- (ratMul_0_l p)...
  apply ratLt_both_side_mul...
Qed.

Lemma ratMul_nonNeg_prod : ∀ p q ∈ ℚ,
  ratNonNeg p → ratNonNeg q → ratNonNeg (p ⋅ q).
Proof with nauto.
  intros p Hp q Hq Hnnp Hnnq.
  destruct (classic (p = Rat 0 ∨ q = Rat 0)).
  - destruct H; subst.
    rewrite ratMul_0_l... rewrite ratMul_0_r...
  - apply not_or_and in H as [].
    destruct Hnnp; destruct Hnnq; [|exfalso; auto..].
    left. apply ratMul_pos_prod...
Qed.

(** 整数嵌入 **)
Definition IntEmbed := Func ℤ ℚ (λ a, [<a, Int 1>]~).

Theorem intEmbed_maps_into : IntEmbed: ℤ ⇒ ℚ.
Proof.
  apply meta_maps_into.
  intros x Hx. apply pQuotI; nauto.
Qed.

Corollary intEmbed_ran : ∀a ∈ ℤ, IntEmbed[a] ∈ ℚ.
Proof with auto.
  pose proof intEmbed_maps_into as [Hf [Hd Hr]].
  intros a Ha. apply Hr. eapply ranI.
  apply func_correct... rewrite Hd...
Qed. 

Theorem intEmbed_injective : injective IntEmbed.
Proof with nauto.
  apply meta_injective. intros x Hx. apply pQuotI...
  intros x1 Hx1 x2 Hx2 Heq. apply rat_ident in Heq...
  rewrite intMul_ident, intMul_ident in Heq...
Qed.

Lemma intEmbed_a : ∀a ∈ ℤ, IntEmbed[a] = [<a, Int 1>]~.
Proof with nauto.
  intros a Ha. unfold IntEmbed. rewrite meta_func_ap...
  apply intEmbed_maps_into.
Qed.

Theorem intEmbed : ∀ n : nat, IntEmbed[Int n] = Rat n.
Proof. intros. rewrite intEmbed_a; nauto. Qed.

Lemma intEmbed_addInv : ∀a ∈ ℤ, IntEmbed[(-a)%z] = -[<a, Int 1>]~.
Proof with nauto.
  intros a Ha. rewrite intEmbed_a, ratAddInv...
  apply intAddInv_ran...
Qed.

Theorem intEmbed_add : ∀ a b ∈ ℤ,
  IntEmbed[(a + b)%z] = IntEmbed[a] + IntEmbed[b].
Proof with nauto.
  intros a Ha b Hb.
  repeat rewrite intEmbed_a; [|auto;ar..].
  rewrite ratAdd_a_b_c_d...
  rewrite intMul_ident, intMul_ident, intMul_ident...
Qed.

Theorem intEmbed_mul : ∀ a b ∈ ℤ,
  IntEmbed[(a ⋅ b)%z] = IntEmbed[a] ⋅ IntEmbed[b].
Proof with nauto.
  intros a Ha b Hb.
  repeat rewrite intEmbed_a; [|auto;mr..].
  rewrite ratMul_a_b_c_d, intMul_ident...
Qed.

Theorem intEmbed_lt : ∀ a b ∈ ℤ,
  a <𝐳 b ↔ IntEmbed[a] <𝐪 IntEmbed[b].
Proof with auto.
  intros a Ha b Hb.
  repeat rewrite intEmbed_a...
  pose proof (int_sn 0) as Hz1.
  pose proof (intPos_sn 0) as Hp1.
  rewrite (ratLt a Ha (Int 1) Hz1 b Hb (Int 1) Hz1 Hp1 Hp1).
  rewrite intMul_ident, intMul_ident... reflexivity.
Qed.

Theorem intEmbed_div : ∀a ∈ ℤ, ∀b ∈ ℤ',
  [<a, b>]~ = IntEmbed[a] / IntEmbed[b].
Proof with nauto.
  intros a Ha b Hb.
  repeat rewrite intEmbed_a; nz...
  rewrite ratMulInv, ratMul_a_b_c_d...
  rewrite intMul_ident, intMul_ident'; nz...
Qed.

Close Scope Rat_scope.
Open Scope Int_scope.

(** 关于逆元的运算律 **)

Lemma intAddInv_sum : ∀ a b ∈ ℤ, -(a + b) = -a - b.
Proof with auto.
  intros a Ha b Hb.
  apply pQuotE in Ha as [m [Hm [n [Hn Ha]]]]. subst a.
  apply pQuotE in Hb as [p [Hp [q [Hq Hd]]]]. subst b.
  rewrite intAddInv, intAddInv, intAdd_m_n_p_q,
    intAdd_m_n_p_q, intAddInv; auto; apply add_ran...
Qed.

Lemma intAddInv_diff : ∀ a b ∈ ℤ, -(a - b) = b - a.
Proof with auto.
  intros a Ha b Hb.
  rewrite intAddInv_sum, intAddInv_double, intAdd_comm;
    auto; apply intAddInv_ran...
Qed.

Lemma ratAddInv_sum : ∀ r s ∈ ℚ, (-(r + s) = -s - r)%q.
Proof with auto.
  intros r Hr s Hs.
  apply pQuotE in Hr as [a [Ha [b [Hb Hr]]]]. subst r.
  apply pQuotE in Hs as [c [Hc [d [Hd Hs]]]]. subst s.
  assert (H1: a ⋅ d + c ⋅ b ∈ ℤ) by (amr;nz).
  assert (H2: b ⋅ d ∈ ℤ') by nzmr.
  assert (H3: d ⋅ b ∈ ℤ') by nzmr.
  assert (H4: -a ∈ ℤ) by (apply intAddInv_ran; auto).
  assert (H5: -c ∈ ℤ) by (apply intAddInv_ran; auto).
  rewrite ratAddInv, ratAddInv, ratAdd_a_b_c_d,
    ratAdd_a_b_c_d, ratAddInv...
  apply rat_ident... apply intAddInv_ran... amr;nz.
  assert (H6: a ⋅ d ∈ ℤ) by (mr;nz).
  assert (H7: c ⋅ b ∈ ℤ) by (mr;nz).
  rewrite intMul_addInv_l, intMul_distr', intMul_distr',
    intAddInv_sum, (intMul_comm d), intAdd_comm, intMul_addInv_l,
    intMul_addInv_l, intMul_addInv_l, intMul_addInv_l; nz...
  apply intAddInv_ran; mr;nz.
  apply intAddInv_ran; mr;nz. mr;nz. mr;nz.
  rewrite intMul_addInv_l; nz... apply intAddInv_ran...
  rewrite intMul_addInv_l; nz... apply intAddInv_ran...
Qed.

Close Scope Int_scope.
Open Scope Rat_scope.

Lemma ratAddInv_diff : ∀ r s ∈ ℚ, -(r - s) = s - r.
Proof with auto.
  intros r Hr s Hs.
  rewrite ratAddInv_sum, ratAddInv_double, ratAdd_comm;
    auto; apply ratAddInv_ran...
Qed.

Lemma ratMulInv_prod : ∀ r s ∈ ℚ', (r ⋅ s)⁻¹ = r⁻¹ ⋅ s⁻¹.
Proof with auto.
  intros r Hr s Hs.
  apply nzRatE2 in Hr as [a [Ha [b [Hb Hr]]]]. subst r.
  apply nzRatE2 in Hs as [c [Hc [d [Hd Hs]]]]. subst s.
  rewrite ratMulInv, ratMulInv, ratMul_a_b_c_d,
    ratMul_a_b_c_d, ratMulInv; nz; auto; nzmr.
Qed.

Lemma ratMulInv_quot : ∀ r s ∈ ℚ', (r / s)⁻¹ = s / r.
Proof with auto.
  intros r Hr s Hs.
  rewrite ratMulInv_prod, ratMulInv_double, ratMul_comm...
  apply nzRatE1. apply ratMulInv_ran...
  apply nzRatE1... apply ratMulInv_ran...
Qed.

Lemma ratMul_addInv_l : ∀ p q ∈ ℚ, -p ⋅ q = -(p ⋅ q).
Proof with auto.
  intros p Hp q Hq.
  apply pQuotE in Hp as [a [Ha [b [Hb Hp]]]]. subst p.
  apply pQuotE in Hq as [c [Hc [d [Hd Hq]]]]. subst q.
  rewrite ratAddInv, ratMul_a_b_c_d, ratMul_a_b_c_d,
    ratAddInv, intMul_addInv_l... mr. nzmr.
  apply intAddInv_ran...
Qed.

Lemma ratMul_addInv_r : ∀ p q ∈ ℚ, p ⋅ -q = -(p ⋅ q).
Proof with auto.
  intros p Hp q Hq.
  apply pQuotE in Hp as [a [Ha [b [Hb Hp]]]]. subst p.
  apply pQuotE in Hq as [c [Hc [d [Hd Hq]]]]. subst q.
  rewrite ratAddInv, ratMul_a_b_c_d, ratMul_a_b_c_d,
    ratAddInv, intMul_addInv_r... mr. nzmr.
  apply intAddInv_ran...
Qed.

Lemma ratMul_addInv_lr : ∀ p q ∈ ℚ, p ⋅ -q = -p ⋅ q.
Proof with auto.
  intros p Hp q Hq.
  rewrite ratMul_addInv_l, ratMul_addInv_r...
Qed.
