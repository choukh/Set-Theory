(** Coq coding by choukh, May 2021 **)

Require Import ZFC.Lib.Real.
Require Import ZFC.Lib.LoStruct.
Require Import ZFC.Elements.EST8_4.
Require Import ZFC.Elements.EX7_1.
Require Import ZFC.Elements.EX8_2.
Require Import ZFC.Elements.EX8_3.
Import OrderType.

(** EX8_19 **)

Open Scope LoStruct_scope.

Lemma loAdd_loRat_loRat_cnt : ω ≈ A (ℚ̃ + ℚ̃).
Proof.
  simpl. unfold LoDisj_A. simpl.
  symmetry. apply cardAdd_iff.
  rewrite card_rat_cntinf.
  apply cardAdd_aleph0_aleph0.
Qed.

Lemma loAdd_loRat_loRat_unbounded : unbounded (A (ℚ̃ + ℚ̃)) (R (ℚ̃ + ℚ̃)).
Proof with nauto.
  destruct ratLt_unbounded as [Hlu Hru].
  simpl. unfold LoDisj_A. simpl. split.
  - intros x Hx. apply BUnionE in Hx as [Hx|Hx];
    apply CPrdE1 in Hx as [s [Hs [n [Hn Heq]]]];
    apply SingE in Hn; subst.
    + apply Hlu in Hs as [r [Hr Hrs]].
      exists <r, 0>. split.
      * apply BUnionI1. apply CPrdI...
      * apply BUnionI1. apply BUnionI1. apply ReplAx.
        exists <r, s>. split... zfc_simple.
    + exists <Rat 0, 0>. split.
      * apply BUnionI1. apply CPrdI...
      * apply BUnionI2. apply CPrdI; apply CPrdI...
  - intros x Hx. apply BUnionE in Hx as [Hx|Hx];
    apply CPrdE1 in Hx as [r [Hr [n [Hn Heq]]]];
    apply SingE in Hn; subst.
    + exists <Rat 0, 1>. split.
      * apply BUnionI2. apply CPrdI...
      * apply BUnionI2. apply CPrdI; apply CPrdI...
    + apply Hru in Hr as [s [Hs Hrs]].
      exists <s, 1>. split.
      * apply BUnionI2. apply CPrdI...
      * apply BUnionI1. apply BUnionI2. apply ReplAx.
        exists <r, s>. split... zfc_simple.
Qed.

Lemma loAdd_loRat_loRat_dense : dense (R (ℚ̃ + ℚ̃)).
Proof with auto.
  intros x z Hxz.
  pose proof ratLt_linearOrder as [Hbr _].
  apply BUnionE in Hxz as [Hxz|Hxz];
  [apply BUnionE in Hxz as [Hxz|Hxz]|].
  - apply ReplAx in Hxz as [p [Hrt Heq]].
    apply Hbr in Hrt as H.
    apply CPrdE1 in H as [r [Hr [t [Ht Hp]]]].
    subst. zfc_simple. apply op_iff in Heq as []; subst.
    apply ratLt_dense in Hrt as [s [Hrs Hst]].
    exists <s, 0>. split; apply BUnionI1;
    apply BUnionI1; apply ReplAx.
    + exists <r, s>. split... zfc_simple.
    + exists <s, t>. split... zfc_simple.
  - apply ReplAx in Hxz as [p [Hrt Heq]].
    apply Hbr in Hrt as H.
    apply CPrdE1 in H as [r [Hr [t [Ht Hp]]]].
    subst. zfc_simple. apply op_iff in Heq as []; subst.
    apply ratLt_dense in Hrt as [s [Hrs Hst]].
    exists <s, 1>. split; apply BUnionI1;
    apply BUnionI2; apply ReplAx.
    + exists <r, s>. split... zfc_simple.
    + exists <s, t>. split... zfc_simple.
  - apply CPrdE1 in Hxz as [a [Ha [b [Hb Heq]]]].
    apply CPrdE1 in Ha as [r [Hr [n [Hn Ha]]]].
    apply CPrdE1 in Hb as [t [Ht [m [Hm Hb]]]].
    apply SingE in Hn. apply SingE in Hm.
    apply op_iff in Heq as []; subst.
    destruct ratLt_unbounded as [_ Hru].
    apply Hru in Hr as [s [Hs Hrs]].
    exists <s, 0>. split.
    + apply BUnionI1. apply BUnionI1. apply ReplAx.
      exists <r, s>. split... zfc_simple.
    + apply BUnionI2. apply CPrdI; apply CPrdI...
Qed.

Lemma loMul_loRat_loRat_cnt : ω ≈ A (ℚ̃ ⋅ ℚ̃).
Proof with auto.
  simpl. symmetry. apply cardMul_iff.
  rewrite card_rat_cntinf.
  apply cardMul_aleph0_aleph0.
Qed.

Lemma loMul_loRat_loRat_unbounded : unbounded (A (ℚ̃ ⋅ ℚ̃)) (R (ℚ̃ ⋅ ℚ̃)).
Proof with auto.
  destruct ratLt_unbounded as [Hlu Hru].
  split; intros x Hx;
  apply CPrdE1 in Hx as [r [Hr [s [Hs Hx]]]];
  simpl in Hr, Hs; subst.
  - assert (H := Hs). apply Hlu in Hs as [q [Hq Hqs]].
    exists <q, q>. split. apply CPrdI...
    apply binRelI. apply CPrdI... apply CPrdI...
    zfc_simple. left...
  - assert (H := Hr). apply Hru in Hr as [q [Hq Hqr]].
    exists <q, s>. split. apply CPrdI...
    apply binRelI. apply CPrdI... apply CPrdI...
    zfc_simple. right...
Qed.

Lemma loMul_loRat_loRat_dense : dense (R (ℚ̃ ⋅ ℚ̃)).
Proof with auto.
  intros x z Hxz.
  apply binRelE1 in Hxz as [a [Ha [b [Hb [Heq H]]]]].
  apply CPrdE1 in Ha as [p [Hp [q [Hq Ha]]]].
  apply CPrdE1 in Hb as [s [Hs [r [Hr Hb]]]].
  apply op_iff in Heq as []; subst. zfc_simple.
  destruct H.
  - apply ratLt_dense in H as [t [Hqt Htr]].
    assert (H := Hqt). apply binRelE2 in H as [_ [Ht _]].
    exists <q, t>. split;
    (apply binRelI; [apply CPrdI; auto..|]); zfc_simple; left...
  - destruct H as [H Heq]. subst.
    apply ratLt_dense in H as [t [Hpt Htp]].
    assert (H := Hpt). apply binRelE2 in H as [_ [Ht _]].
    exists <t, r>. split;
    (apply binRelI; [apply CPrdI; auto..|]); zfc_simple; right...
Qed.

Open Scope OrderType_scope.

(* ex8_19_1 *)
Theorem otAdd_otRat_otRat_eq_otRat : ℚ̅ + ℚ̅ = ℚ̅.
Proof with auto.
  rewrite otAdd_eq_ot_of_loAdd. apply ot_correct.
  apply countable_unbounded_dense_loset_iso.
  - apply loAdd_loRat_loRat_cnt.
  - apply loAdd_loRat_loRat_unbounded.
  - apply loAdd_loRat_loRat_dense.
  - apply CardAx1. symmetry. apply card_rat_cntinf.
  - apply ratLt_unbounded.
  - apply ratLt_dense.
Qed.

(* ex8_19_2 *)
Theorem otMul_otRat_otRat_eq_otRat : ℚ̅ ⋅ ℚ̅ = ℚ̅.
Proof with auto.
  rewrite otMul_eq_ot_of_loMul. apply ot_correct.
  apply countable_unbounded_dense_loset_iso.
  - apply loMul_loRat_loRat_cnt.
  - apply loMul_loRat_loRat_unbounded.
  - apply loMul_loRat_loRat_dense.
  - apply CardAx1. symmetry. apply card_rat_cntinf.
  - apply ratLt_unbounded.
  - apply ratLt_dense.
Qed.
