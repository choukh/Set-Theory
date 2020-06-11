(** Based on "Elements of Set Theory" Chapter 4 Part 2 **)
(** Coq coding by choukh, May 2020 **)

Global Set Warnings "-notation-overridden,-parsing".
Require Export ZFC.EST4_1.

(*** EST第四章2：自然数算术：加法，乘法，运算律 ***)

Notation "0" := ∅.
Notation "1" := 0⁺.
Notation "2" := 1⁺.
Notation "3" := 2⁺.
Notation "4" := 3⁺.

(* 算术递归定义Helper *)
Definition pre_Arith : set → set → set := λ F a,
  {h ∊ ω ⟶ ω | λ h, h[0] = a ∧ ∀n ∈ ω, h[n⁺] = F[h[n]]}.
Definition Arith : set → set → set := λ F a,
  ⋃ (pre_Arith F a).

Lemma pre_arith_correct : ∀ F a, F: ω ⇒ ω → a ∈ ω →
  ∃h, h: ω ⇒ ω ∧ (pre_Arith F a) = ⎨h⎬ ∧
  h[0] = a ∧ ∀n ∈ ω, h[n⁺] = F[h[n]].
Proof with eauto; try congruence.
  intros F a HF Ha.
  pose proof (ω_recursion F ω a HF Ha) as [[h Hh] Hu].
  exists h. split. destruct Hh as []... split.
  apply ExtAx. intros f. split; intros Hf.
  - cut (f = h). intros. rewrite H. apply SingI. apply Hu...
    apply SepE in Hf as [Hf [Hf0 Hf1]].
    apply SepE in Hf as [_ Hf]. split...
  - destruct Hh as [[Hh [Hdh Hrh]] [Hh0 Hh1]].
    apply SingE in Hf. subst f. apply SepI.
    apply Arrow_correct. split... split... intros x Hx.
    apply Hrh. eapply ranI. apply func_correct... split...
  - destruct Hh as [[Hh [Hdh Hrh]] [Hh0 Hh1]]. split...
Qed.

Lemma arith_correct : ∀ F a, F: ω ⇒ ω → a ∈ ω →
  ∃h, h: ω ⇒ ω ∧ (Arith F a) = h ∧
  h[0] = a ∧ ∀n ∈ ω, h[n⁺] = F[h[n]].
Proof with eauto; try congruence.
  intros F a HF Ha.
  destruct (pre_arith_correct F a) as [h [Hh [Heq [Hh0 Hh1]]]]...
  exists h. split... split; [|split; auto].
  apply ExtAx. split; intros.
  - apply UnionAx in H as [f [Hf Hx]].
    rewrite Heq in Hf. apply SingE in Hf...
  - eapply UnionI. rewrite Heq. apply SingI. apply H.
Qed.

(** 加法 **)
Definition Add : set → set := λ m, Arith σ m.

Lemma add_correct : ∀m ∈ ω,
  ∃h, h: ω ⇒ ω ∧ (Add m) = h ∧
  h[0] = m ∧ ∀n ∈ ω, h[n⁺] = h[n]⁺.
Proof with eauto; try congruence.
  intros m Hm.
  destruct (arith_correct σ m σ_func) as [h [Hh [Heq [Hh0 Hh1]]]]...
  exists h. split... split... split...
  intros n Hn. apply Hh1 in Hn as Hap. rewrite σ_ap in Hap...
  destruct Hh as [Hh [Hdh Hrh]].
  apply Hrh. eapply ranI. apply func_correct...
Qed.

Lemma add_0 : ∀m ∈ ω, (Add m)[0] = m.
Proof with congruence.
  intros m Hm.
  destruct (add_correct m) as [h [_ [Heq [Hh0 _]]]]...
Qed.

Lemma add_n : ∀ m n ∈ ω, (Add m)[n⁺] = (Add m)[n]⁺.
Proof with auto.
  intros m Hm.
  destruct (add_correct m) as [h [_ [Heq [_ Hh1]]]]...
  rewrite Heq...
Qed.

(* 二元运算 *)
Definition BinOp : set → (set → set) → set := λ A F,
  {q ∊ (A × A) × A | λ q,
    let m := π1 (π1 q) in
    let n := π2 (π1 q) in
    let p := π2 q in
    m ∈ A ∧ n ∈ A ∧ p = (F m)[n]
  }.

(* 自动化证明 *)
Hint Immediate ω_has_0 : core.
Hint Immediate S_has_x : core.
Hint Rewrite π1_correct π2_correct : ZFC.
Ltac zfcrewrite :=
  autorewrite with ZFC in *; try congruence.
(* Print HintDb arith.
Print Rewrite HintDb arith. *)

Lemma binop_is_func : ∀ A F, is_function (BinOp A F).
Proof with auto.
  repeat split.
  - intros x Hx. apply SepE in Hx as [Hx _].
    apply CProdE2 in Hx...
  - apply domE in H...
  - intros y1 y2 H1 H2.
    apply SepE in H1 as [_ [_ [_ Hp1]]].
    apply SepE in H2 as [_ [_ [_ Hp2]]]. zfcrewrite.
Qed.

Lemma binop_dom : ∀ A F, (∀a ∈ A, F a: A ⇒ A) →
  dom (BinOp A F) = A × A.
Proof with eauto; try congruence.
  intros. apply ExtAx. split; intros Hx.
  - apply domE in Hx as [y Hp]. apply SepE in Hp as [Hx _].
    apply CProdE1 in Hx as [Hx _]. zfcrewrite.
  - assert (Hx' := Hx).
    apply CProd_correct in Hx' as [a [Ha [b [Hb Heq]]]].
    destruct (H a) as [Hh [Hhd Hhr]]...
    rewrite <- Hhd in Hb. apply func_correct in Hb as Hbp...
    eapply domI. apply SepI. apply CProdI. apply Hx.
    apply Hhr. eapply ranI... subst x. split; zfcrewrite. split...
Qed.  

Definition Addition : set := BinOp ω Add.
Notation "x + y" := (Addition[<x, y>]).

Lemma add_maps_onto : Addition: ω × ω ⟹ ω.
Proof with eauto; try congruence.
  split. apply binop_is_func.
  split. apply binop_dom. intros a Ha.
  destruct (add_correct a) as [h [Hh [Hheq _]]]...
  apply ExtAx. intros y. split; intros Hy.
  - apply ranE in Hy as [n Hp]. apply SepE in Hp as [Hp _].
    apply CProdE1 in Hp as [_ Hy]. zfcrewrite.
  - destruct (add_correct y) as [h [[Hh [Hhd Hhr]] [Hheq _]]]...
    cut (<0, h[0]> ∈ h). intros H0.
    eapply ranI. apply SepI. apply CProdI. apply CProdI.
    apply Hy. apply ω_has_0. apply Hy. split; zfcrewrite.
    split... rewrite add_0... apply func_correct... rewrite Hhd...
Qed.

Lemma add_is_func : is_function Addition.
Proof. destruct add_maps_onto as []; auto. Qed.

Lemma add_ran : ∀ m n ∈ ω, m + n ∈ ω.
Proof with auto.
  intros n Hn m Hm. destruct add_maps_onto as [Hf [Hd Hr]].
  rewrite <- Hr. eapply ranI. apply func_correct...
  rewrite Hd. apply CProdI...
Qed.

Theorem add_m_0 : ∀m ∈ ω, m + 0 = m.
Proof with auto.
  intros m Hm. eapply func_ap... apply add_is_func.
  apply SepI. apply CProdI... apply CProdI...
  split; zfcrewrite. split... rewrite add_0...
Qed.

Theorem add_m_n : ∀ m n ∈ ω, m + n⁺ = (m + n)⁺.
Proof with auto.
  intros m Hm n Hn. eapply func_ap... apply add_is_func.
  apply SepI. apply CProdI... apply CProdI...
  apply ω_inductive... apply ω_inductive... apply add_ran...
  split; zfcrewrite. split. apply ω_inductive...
  cut (m + n = (Add m)[n]). intros Heq. rewrite Heq, add_n...
  eapply func_ap... apply add_is_func.
  apply SepI. apply CProdI... apply CProdI...
  destruct (add_correct m) as [h [[Hh [Hhd Hhr]] [Hheq _]]]...
  rewrite Hheq. apply Hhr. eapply ranI. apply func_correct...
  congruence. split; zfcrewrite. split...
Qed.

Lemma add_m_ap : ∀ m n ∈ ω, (Add m)[n] = m + n.
Proof with auto.
  intros m Hm n Hn. generalize dependent m.
  set {n ∊ ω | λ n, ∀m ∈ ω, (Add m)[n] = m + n} as T.
  ω_induction T Hn; intros k Hk.
  - rewrite add_0, add_m_0...
  - cut ((Add k)[m] = k + m). intros Heq.
    rewrite add_n, Heq, add_m_n... apply IH...
Qed.

(** 乘法 **)
Definition Mult : set → set := λ m, Arith (Add m) 0.

Lemma mult_correct : ∀m ∈ ω,
  ∃h, h: ω ⇒ ω ∧ (Mult m) = h ∧
  h[0] = 0 ∧ ∀n ∈ ω, h[n⁺] = m + h[n].
Proof with auto; try congruence.
  intros m Hm.
  destruct (add_correct m) as [g [Hg [Hgeq _]]]...
  destruct (arith_correct (Add m) 0) as [h [Hh [Hheq [Hh0 Hh1]]]]...
  exists h. split... split... split... intros n Hn.
  apply Hh1 in Hn as Hap. rewrite Hap, add_m_ap...
  destruct Hh as [Hh [Hdh Hrh]].
  apply Hrh. eapply ranI. apply func_correct...
Qed.

Lemma mult_0 : ∀m ∈ ω, (Mult m)[0] = 0.
Proof with congruence.
  intros m Hm.
  destruct (mult_correct m) as [h [_ [Heq [Hh0 _]]]]...
Qed.

Lemma mult_n : ∀ m n ∈ ω, (Mult m)[n⁺] = m + (Mult m)[n].
Proof with auto.
  intros m Hm.
  destruct (mult_correct m) as [h [_ [Heq [_ Hh1]]]]...
  rewrite Heq...
Qed.

Definition Multiplication : set := BinOp ω Mult.
Notation "x ⋅ y" := (Multiplication[<x, y>]) (at level 40).

Lemma mult_maps_onto : Multiplication: ω × ω ⟹ ω.
Proof with auto; try congruence.
  split. apply binop_is_func.
  split. apply binop_dom. intros a Ha.
  destruct (mult_correct a) as [h [Hh [Hheq _]]]...
  apply ExtAx. intros y. split; intros Hy.
  - apply ranE in Hy as [n Hp]. apply SepE in Hp as [Hp _].
    apply CProdE1 in Hp as [_ Hy]. zfcrewrite.
  - destruct (mult_correct y) as [h [[Hh [Hhd Hhr]] [Hheq _]]]...
    cut (<1, h[1]> ∈ h). intros H0.
    assert (H1: 0⁺ ∈ ω) by (apply ω_inductive; auto).
    eapply ranI. apply SepI. apply CProdI. apply CProdI.
    apply Hy. apply H1. apply Hy. split; zfcrewrite.
    split... rewrite mult_n, mult_0, add_m_0...
    apply func_correct... rewrite Hhd. apply ω_inductive...
Qed.

Lemma mult_is_func : is_function Multiplication.
Proof. destruct mult_maps_onto as []; auto. Qed.

Lemma mult_ran : ∀ m n ∈ ω, m ⋅ n ∈ ω.
Proof with auto.
  intros n Hn m Hm. destruct mult_maps_onto as [Hf [Hd Hr]].
  rewrite <- Hr. eapply ranI. apply func_correct...
  rewrite Hd. apply CProdI...
Qed.

Theorem mult_m_0 : ∀m ∈ ω, m ⋅ 0 = 0.
Proof with auto.
  intros m Hm. eapply func_ap. apply mult_is_func.
  apply SepI... apply CProdI... apply CProdI...
  split; zfcrewrite. split... rewrite mult_0...
Qed.

Theorem mult_m_n : ∀ m n ∈ ω, m ⋅ n⁺ = m + m ⋅ n.
Proof with auto; try congruence.
  intros m Hm n Hn. eapply func_ap. apply mult_is_func.
  apply SepI. apply CProdI... apply CProdI...
  apply ω_inductive... apply add_ran... apply mult_ran...
  split; zfcrewrite. split. apply ω_inductive...
  cut (m ⋅ n = (Mult m)[n]). intros Heq. rewrite Heq, mult_n...
  eapply func_ap. apply mult_is_func.
  apply SepI. apply CProdI... apply CProdI...
  destruct (mult_correct m) as [h [[Hh [Hhd Hhr]] [Hheq _]]]...
  rewrite Hheq. apply Hhr. eapply ranI. apply func_correct...
  split; zfcrewrite. split...
Qed.

Lemma mult_m_ap : ∀ m n ∈ ω, (Mult m)[n] = m ⋅ n.
Proof with auto.
  intros m Hm n Hn. generalize dependent m.
  set {n ∊ ω | λ n, ∀m ∈ ω, (Mult m)[n] = m ⋅ n} as T.
  ω_induction T Hn; intros k Hk.
  - rewrite mult_0... rewrite mult_m_0...
  - cut ((Mult k)[m] = k ⋅ m). intros Heq.
    rewrite mult_n, Heq, mult_m_n... apply IH...
Qed.

(** 指数运算 **)
Definition Exp : set → set := λ m, Arith (Mult m) 1.

Lemma exp_correct : ∀m ∈ ω,
  ∃h, h: ω ⇒ ω ∧ (Exp m) = h ∧
  h[0] = 1 ∧ ∀n ∈ ω, h[n⁺] = m ⋅ h[n].
Proof with auto; try congruence.
  intros m Hm.
  destruct (mult_correct m) as [g [Hg [Hgeq _]]]...
  destruct (arith_correct (Mult m) 1)
    as [h [Hh [Hheq [Hh0 Hh1]]]]...
  apply ω_inductive...
  exists h. split... split... split...
  intros n Hn. apply Hh1 in Hn as Hap.
  rewrite Hap, mult_m_ap...
  destruct Hh as [Hh [Hdh Hrh]].
  apply Hrh. eapply ranI. apply func_correct...
Qed.

Lemma exp_0 : ∀m ∈ ω, (Exp m)[0] = 1.
Proof with congruence.
  intros m Hm.
  destruct (exp_correct m) as [h [_ [Heq [Hh0 _]]]]...
Qed.

Lemma exp_n : ∀ m n ∈ ω, (Exp m)[n⁺] = m ⋅ (Exp m)[n].
Proof with auto.
  intros m Hm.
  destruct (exp_correct m) as [h [_ [Heq [_ Hh1]]]]...
  rewrite Heq...
Qed.

Definition Exponentiation : set := BinOp ω Exp.
Notation "x ^ y" := (Exponentiation[<x, y>]).

Lemma exp_maps_onto : Exponentiation: ω × ω ⟹ ω.
Proof with auto; try congruence.
  split. apply binop_is_func.
  split. apply binop_dom. intros a Ha.
  destruct (exp_correct a) as [h [Hh [Hheq _]]]...
  apply ExtAx. intros y. split; intros Hy.
  - apply ranE in Hy as [n Hp]. apply SepE in Hp as [Hp _].
    apply CProdE1 in Hp as [_ Hy]. zfcrewrite.
  - destruct (exp_correct y) as [h [[Hh [Hhd Hhr]] [Hheq _]]]...
    cut (<1, h[1]> ∈ h). intros H0.
    assert (H1: 0⁺ ∈ ω) by (apply ω_inductive; auto).
    eapply ranI. apply SepI. apply CProdI. apply CProdI.
    apply Hy. apply H1. apply Hy.
    split; zfcrewrite. split...
    rewrite exp_n, exp_0, mult_m_n, mult_m_0, add_m_0...
    apply func_correct... rewrite Hhd. apply ω_inductive...
Qed.

Lemma exp_is_func : is_function Exponentiation.
Proof. destruct exp_maps_onto as []; auto. Qed.

Lemma exp_ran : ∀ m n ∈ ω, m ^ n ∈ ω.
Proof with auto.
  intros n Hn m Hm. destruct exp_maps_onto as [Hf [Hd Hr]].
  rewrite <- Hr. eapply ranI. apply func_correct...
  rewrite Hd. apply CProdI...
Qed.

Theorem exp_m_0 : ∀m ∈ ω, m ^ 0 = 1.
Proof with auto.
  intros m Hm. eapply func_ap. apply exp_is_func.
  apply SepI... apply CProdI... apply CProdI...
  apply ω_inductive... split; zfcrewrite.
  split... rewrite exp_0...
Qed.

Theorem exp_m_n : ∀ m n ∈ ω, m ^ n⁺ = m ⋅ m ^ n.
Proof with auto; try congruence.
  intros m Hm n Hn. eapply func_ap. apply exp_is_func.
  apply SepI. apply CProdI. apply CProdI...
  apply ω_inductive... apply mult_ran... apply exp_ran...
  split; zfcrewrite. split. apply ω_inductive...
  cut (m ^ n = (Exp m)[n]). intros. rewrite H.
  rewrite exp_n; auto. eapply func_ap. apply exp_is_func.
  apply SepI. apply CProdI. apply CProdI...
  destruct (exp_correct m) as [h [[Hh [Hhd Hhr]] [Hheq _]]]...
  rewrite Hheq. apply Hhr. eapply ranI. apply func_correct...
  split; zfcrewrite. split...
Qed.

Lemma exp_m_ap : ∀ m n ∈ ω, (Exp m)[n] = m ^ n.
Proof with auto.
  intros m Hm n Hn. generalize dependent m.
  set {n ∊ ω | λ n, ∀m ∈ ω, (Exp m)[n] = m ^ n} as T.
  ω_induction T Hn; intros k Hk.
  - rewrite exp_0, exp_m_0...
  - cut ((Exp k)[m] = k ^ m). intros.
    rewrite exp_m_n, exp_n, H... apply IH...
Qed.

Example arith_ex_0 : 1 + 2 = 3.
Proof with auto.
  rewrite add_m_n, add_m_n, add_m_0; try (apply ω_inductive)...
Qed.

Example arith_ex_1 : 2 ⋅ 2 = 4.
Proof.
  Ltac ind := try do 2 apply ω_inductive; try apply ω_has_0.
  rewrite mult_m_n, mult_m_n, mult_m_0; ind.
  rewrite add_m_0, add_m_n, add_m_n, add_m_0; ind. reflexivity.
Qed.

(* 加法结合律 *)
Theorem add_assoc : ∀ m n p ∈ ω, m + (n + p) = (m + n) + p.
Proof with auto.
  intros n Hn m Hm p Hp.
  generalize dependent n. generalize dependent m.
  set {p ∊ ω | λ p, ∀ m, m ∈ ω → ∀ n, n ∈ ω →
    m + (n + p) = (m + n) + p} as N.
  ω_induction N Hp; intros n Hn k Hk.
  - repeat rewrite add_m_0... apply add_ran...
  - repeat rewrite add_m_n; try apply add_ran... rewrite IH...
Qed.

Lemma add_0_n : ∀n ∈ ω, 0 + n = n.
Proof with auto.
  intros n Hn.
  set {n ∊ ω | λ n, 0 + n = n} as N.
  ω_induction N Hn. rewrite add_m_0...
  rewrite add_m_n... rewrite IH...
Qed.

Lemma add_m_n' : ∀ m n ∈ ω, m⁺ + n = (m + n)⁺.
Proof with auto.
  intros m Hm n Hn. generalize dependent m.
  set {n ∊ ω | λ n, ∀ m, m ∈ ω → m⁺ + n = (m + n)⁺} as N.
  ω_induction N Hn; intros k Hk.
  - repeat rewrite add_m_0... apply ω_inductive...
  - repeat rewrite add_m_n...
    rewrite IH... apply ω_inductive...
Qed.

(* 加法交换律 *)
Theorem add_comm : ∀ m n ∈ ω, m + n = n + m.
Proof with auto.
  intros n Hn m Hm. ω_destruct m; subst m.
  rewrite add_0_n, add_m_0...
  rewrite add_m_n...
  clear Hm. generalize dependent n'.
  set {n ∊ ω | λ n, ∀ n', n' ∈ ω → (n + n')⁺ = n'⁺ + n} as N.
  ω_induction N Hn; intros k Hk.
  - rewrite add_0_n, add_m_0... apply ω_inductive...
  - rewrite add_m_n, add_m_n'...
    rewrite IH... apply ω_inductive...
Qed.

Lemma add_comm_123_213 : ∀ m n p ∈ ω, m + n + p = n + m + p.
Proof with auto.
  intros m Hm n Hn p Hp. rewrite add_comm...
  rewrite (add_comm (n + m))... rewrite (add_comm m)...
  apply add_ran... apply add_ran...
Qed.

(* 乘法分配律 *)
Theorem mult_distr : ∀ m n p ∈ ω, m ⋅ (n + p) = m ⋅ n + m ⋅ p.
Proof with auto.
  intros m Hm n Hn p Hp.
  generalize dependent n. generalize dependent m.
  set {p ∊ ω | λ p, ∀ m, m ∈ ω → ∀ n, n ∈ ω →
    m ⋅ (n + p) = m ⋅ n + m ⋅ p} as N.
  ω_induction N Hp; intros n Hn k Hk.
  - rewrite add_m_0, mult_m_0, add_m_0... apply mult_ran...
  - rewrite add_m_n, mult_m_n, mult_m_n... rewrite IH...
    rewrite add_comm... rewrite (add_comm n)...
    rewrite add_assoc; try apply mult_ran... apply mult_ran...
    apply add_ran; apply mult_ran... apply add_ran...
Qed.

(* 乘法结合律 *)
Theorem mult_assoc : ∀ m n p ∈ ω, m ⋅ (n ⋅ p) = (m ⋅ n) ⋅ p.
Proof with auto.
  intros n Hn m Hm p Hp.
  generalize dependent n. generalize dependent m.
  set {p ∊ ω | λ p, ∀ m, m ∈ ω → ∀ n, n ∈ ω →
    m ⋅ (n ⋅ p) = (m ⋅ n) ⋅ p} as N.
  ω_induction N Hp; intros n Hn k Hk.
  - repeat rewrite mult_m_0... apply mult_ran...
  - repeat rewrite mult_m_n... rewrite mult_distr...
    rewrite IH... apply mult_ran... apply mult_ran...
Qed.

Lemma mult_0_n : ∀n ∈ ω, 0 ⋅ n = 0.
Proof with auto.
  intros n Hn.
  set {n ∊ ω | λ n, 0 ⋅ n = 0} as N.
  ω_induction N Hn. rewrite mult_m_0...
  rewrite mult_m_n... rewrite IH... rewrite add_m_0...
Qed.

Lemma mult_m_n' : ∀ m n ∈ ω, m⁺ ⋅ n = n + (m ⋅ n).
Proof with auto.
  intros m Hm n Hn. generalize dependent m.
  set {n ∊ ω | λ n, ∀ m, m ∈ ω → m⁺ ⋅ n = n + (m ⋅ n)} as N.
  ω_induction N Hn; intros k Hk.
  - repeat rewrite mult_m_0...
    rewrite add_m_0... apply ω_inductive...
  - repeat rewrite mult_m_n; try apply ω_inductive...
    rewrite IH... repeat rewrite add_m_n';
      try apply add_ran; try apply mult_ran...
    repeat rewrite add_assoc; try apply mult_ran...
    rewrite add_comm_123_213... apply mult_ran...
Qed.

(* 乘法交换律 *)
Theorem mult_comm : ∀ m n ∈ ω, m ⋅ n = n ⋅ m.
Proof with auto.
  intros n Hn m Hm. ω_destruct m; subst m.
  rewrite mult_0_n, mult_m_0...
  rewrite mult_m_n...
  clear Hm. generalize dependent n'.
  set {n ∊ ω | λ n, ∀ n', n' ∈ ω → n + n ⋅ n' = n'⁺ ⋅ n} as N.
  ω_induction N Hn; intros k Hk.
  - rewrite mult_0_n, mult_m_0, add_m_0... apply ω_inductive...
  - rewrite mult_m_n, mult_m_n'; try apply ω_inductive...
    repeat rewrite add_m_n'... rewrite <- IH...
    repeat rewrite add_assoc; try apply mult_ran...
    rewrite add_comm_123_213; try apply mult_ran...
    apply mult_ran... apply ω_inductive...
    apply add_ran... apply mult_ran...
Qed.

Lemma add_0_n_0 : ∀n ∈ ω, 0 + n = 0 → n = 0.
Proof with eauto.
  intros n Hn H0.
  ω_destruct n... subst n. rewrite add_m_n in H0...
  exfalso. eapply S_neq_0...
Qed.

Lemma add_m_n_0 : ∀ m n ∈ ω, m + n = 0 → m = 0 ∧ n = 0.
Proof with eauto.
  intros m Hm n Hn H0.
  ω_destruct m; ω_destruct n; subst m n. split...
  split... apply add_0_n_0...
  split... apply add_0_n_0... rewrite add_comm...
  rewrite add_m_n in H0... exfalso. eapply S_neq_0...
Qed.

Lemma mult_m_n_0 : ∀ m n ∈ ω, m ⋅ n = 0 → m = 0 ∨ n = 0.
Proof with eauto.
  intros m Hm n Hn H0.
  ω_destruct m. left... ω_destruct n. right...
  exfalso. subst m n. rewrite mult_m_n, mult_m_n' in H0...
  apply add_m_n_0 in H0 as [H1 _]...
  exfalso. eapply S_neq_0... apply add_ran... apply mult_ran...
Qed.

Definition even : set → Prop := λ n,
  n ∈ ω ∧ ∃m ∈ ω, n = 2 ⋅ m.

Definition odd : set → Prop := λ n,
  n ∈ ω ∧ ∃p ∈ ω, n = 2 ⋅ p + 1.

Lemma add_n_1 : ∀n ∈ ω, n⁺ = n + 1.
Proof with eauto.
  intros n Hn.
  set {n ∊ ω | λ n, n⁺ = n + 1} as N.
  ω_induction N Hn.
  - rewrite add_0_n... apply ω_inductive...
  - rewrite add_m_n'... rewrite IH... apply ω_inductive...
Qed.

Lemma mult_n_1 : ∀n ∈ ω, n ⋅ 1 = n.
Proof with eauto.
  intros n Hn.
  set {n ∊ ω | λ n, n ⋅ 1 = n} as N.
  ω_induction N Hn.
  - rewrite mult_0_n... apply ω_inductive...
  - rewrite mult_m_n'... rewrite IH.
    rewrite (add_n_1 m)... rewrite add_comm...
    apply ω_inductive... apply ω_inductive...
Qed.

Theorem exp_distr : ∀ m n p ∈ ω, m ^ (n + p) = m ^ n ⋅ m ^ p.
Proof with try assumption; try congruence.
  intros n Hn m Hm p Hp.
  generalize dependent n. generalize dependent m.
  set {p ∊ ω | λ p, ∀ m, m ∈ ω → ∀ n, n ∈ ω →
    n ^ (m + p) = n ^ m ⋅ n ^ p} as N.
  ω_induction N Hp; intros n Hn k Hk.
  - rewrite add_m_0, exp_m_0, mult_n_1... apply exp_ran...
  - rewrite add_m_n, exp_m_n, exp_m_n; try apply add_ran...
    rewrite (IH n Hn k Hk).
    rewrite mult_assoc, mult_assoc; try apply exp_ran...
    rewrite (mult_comm k); try apply exp_ran...
Qed.
