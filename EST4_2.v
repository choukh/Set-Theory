(** Based on "Elements of Set Theory" Chapter 4 Part 2 **)
(** Coq coding by choukh, May 2020 **)

Global Set Warnings "-ambiguous-paths".

Require Export ZFC.EST4_1.

(*** EST第四章2：nat的嵌入与投射，自然数算术：加法，乘法，运算律 ***)

(* 自动化证明 *)
Global Hint Immediate ω_has_0 : number_hint.
Global Hint Immediate ω_neq_0 : number_hint.
Global Hint Immediate suc_inc_n : number_hint.
Ltac nauto := auto with number_hint.
Ltac neauto := eauto with number_hint.

(** nat的嵌入与投射 **)

(* 对x迭代n次f：特别地，有 iter n S O = n *)
Fixpoint iter (n : nat) {X : Type} (f : X → X) (x : X) :=
  match n with
  | O => x
  | S n' => f (iter n' f x)
  end.

(* 元语言自然数嵌入到集合论自然数（自动类型转换） *)
Coercion Embed := λ n, iter n Suc ∅.

Lemma pred : ∀ n, Embed n =
  match n with | O => ∅ | S n' => (Embed n')⁺ end.
Proof. intros. destruct n; auto. Qed.

Lemma embed_ran : ∀ n : nat, n ∈ ω.
Proof with nauto. induction n... apply ω_inductive... Qed.
Global Hint Immediate embed_ran : number_hint.

Lemma zero : Embed 0 = ∅.
Proof. reflexivity. Qed.

Lemma one : Embed 1 = 1%zfc1.
Proof.
  apply ExtAx. intros x. split; intros Hx.
  - apply BUnionE in Hx as []. exfalso0. apply H.
  - apply BUnionI2. apply Hx.
Qed.

Lemma two : Embed 2 = 2%zfc1.
Proof.
  apply ExtAx. intros x. split; intros Hx.
  - rewrite pred in Hx.
    apply BUnionE in Hx as []; rewrite one in H.
    + apply PairE in H as []; subst; apply PairI1.
    + apply SingE in H. subst. apply PairI2.
  - apply PairE in Hx as []; subst.
    + apply BUnionI1. apply suc_has_n.
    + rewrite <- one. apply suc_has_n.
Qed.

(* 嵌入是单射 *)
Lemma embed_injective : ∀ m n : nat,
  Embed m = Embed n → m = n.
Proof with auto.
  induction m; destruct n; unfold Embed; simpl; intros.
  - reflexivity.
  - exfalso. eapply suc_neq_0. symmetry. apply H.
  - exfalso. eapply suc_neq_0. apply H.
  - apply suc_injective in H... apply embed_ran. apply embed_ran.
Qed.

(* 集合论自然数投射出元语言自然数 *)
Coercion Proj (N : set) : nat :=
  match dit (sig (λ n, iter n Suc ∅ = N)) with
    | inl (exist _ n _) => n
    | inr _ => 0
  end.

Lemma proj : ∀n ∈ ω, ∃ m : nat, Embed m = n.
Proof with auto.
  intros n Hn.
  set {n ∊ ω | λ n, ∃ k : nat, Embed k = n} as N.
  ω_induction N Hn. exists 0...
  destruct IH as [k' Heq]. subst. exists (S k')...
Qed.

(* 集合论自然数与元语言自然数同构 *)
Lemma proj_embed_id : ∀ n : nat, Proj n = n. 
Proof.
  intros. unfold Proj.
  destruct (dit (sig (λ k, iter k Suc ∅ = Embed n))).
  - destruct s as [k H]. apply embed_injective in H. apply H.
  - exfalso. apply f. exists n. reflexivity.
Qed.

Lemma embed_proj_id : ∀n ∈ ω, Embed n = n.
Proof.
  intros n Hn. destruct (proj n Hn) as [m Heq].
  subst. rewrite proj_embed_id. reflexivity.
Qed.

(* 投射是单射 *)
Lemma proj_injective : ∀ n m ∈ ω, Proj n = Proj m → n = m.
Proof.
  intros n Hn m Hm Heq.
  assert (Embed n = Embed m) by auto.
  do 2 rewrite embed_proj_id in H; auto.
Qed.

(** 自然数算术 **)

(* 算术递归定义Helper *)
Definition PreArith : set → set → set := λ F a,
  {h ∊ ω ⟶ ω | λ h, h[0] = a ∧ ∀n ∈ ω, h[n⁺] = F[h[n]]}.
Definition Arith : set → set → set := λ F a,
  ⋃ (PreArith F a).

Lemma preArith_correct : ∀ F a, F: ω ⇒ ω → a ∈ ω →
  ∃h, h: ω ⇒ ω ∧ (PreArith F a) = ⎨h⎬ ∧
  h[0] = a ∧ ∀n ∈ ω, h[n⁺] = F[h[n]].
Proof with eauto; try congruence.
  intros F a HF Ha.
  pose proof (ω_recursion_uniqueness F ω a HF Ha) as [[h Hh] Hu].
  exists h. split. destruct Hh as []... split.
  apply ExtAx. intros f. split; intros Hf.
  - cut (f = h). intros. rewrite H... apply Hu...
    apply SepE in Hf as [Hf [Hf0 Hf1]].
    apply SepE in Hf as [_ Hf]. split...
  - destruct Hh as [[Hh [Hdh Hrh]] [Hh0 Hh1]].
    apply SingE in Hf. subst f. apply SepI.
    apply arrow_iff. split... split...
    intros x Hx. eapply ap_ran... split... split...
  - destruct Hh as [[Hh [Hdh Hrh]] [Hh0 Hh1]]. split...
Qed.

Lemma arith_correct : ∀ F a, F: ω ⇒ ω → a ∈ ω →
  ∃h, h: ω ⇒ ω ∧ (Arith F a) = h ∧
  h[0] = a ∧ ∀n ∈ ω, h[n⁺] = F[h[n]].
Proof with eauto; try congruence.
  intros F a HF Ha.
  destruct (preArith_correct F a) as [h [Hh [Heq [Hh0 Hh1]]]]...
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
  destruct (arith_correct σ m σ_function) as [h [Hh [Heq [Hh0 Hh1]]]]...
  exists h. split... split... split...
  intros n Hn. apply Hh1 in Hn as Hap.
  rewrite σ_ap in Hap... eapply ap_ran...
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

Lemma binop_is_func : ∀ A F, is_function (BinOp A F).
Proof with auto.
  repeat split.
  - intros x Hx. apply SepE in Hx as [Hx _].
    apply cprod_is_pairs in Hx...
  - apply domE in H...
  - intros y1 y2 H1 H2.
    apply SepE in H1 as [_ [_ [_ Hp1]]].
    apply SepE in H2 as [_ [_ [_ Hp2]]]. zfc_simple.
Qed.

Lemma binop_dom : ∀ A F, (∀a ∈ A, F a: A ⇒ A) →
  dom (BinOp A F) = A × A.
Proof with eauto; try congruence.
  intros. apply ExtAx. split; intros Hx.
  - apply domE in Hx as [y Hp]. apply SepE in Hp as [Hx _].
    apply CProdE2 in Hx as [Hx _]...
  - assert (Hx' := Hx).
    apply CProdE1 in Hx' as [a [Ha [b [Hb Heq]]]].
    destruct (H a) as [Hh [Hhd Hhr]]...
    rewrite <- Hhd in Hb. apply func_correct in Hb as Hbp...
    eapply domI. apply SepI. apply CProdI. apply Hx.
    apply Hhr. eapply ranI... subst x. split; zfc_simple. split...
Qed.

Declare Scope Nat_scope.
Delimit Scope Nat_scope with n.
Open Scope Nat_scope.

Definition Addition : set := BinOp ω Add.
Notation "x + y" := (Addition[<x, y>]) : Nat_scope.

Lemma add_maps_onto : Addition: ω × ω ⟹ ω.
Proof with neauto; try congruence.
  split. apply binop_is_func.
  split. apply binop_dom. intros a Ha.
  destruct (add_correct a) as [h [Hh [Hheq _]]]...
  apply ExtAx. intros y. split; intros Hy.
  - apply ranE in Hy as [n Hp]. apply SepE in Hp as [Hp _].
    apply CProdE2 in Hp as [_ Hy]...
  - destruct (add_correct y) as [h [[Hh [Hhd Hhr]] [Hheq _]]]...
    cut (<0, h[0]> ∈ h). intros H0.
    eapply ranI. apply SepI. apply CProdI. apply CProdI.
    apply Hy. apply ω_has_0. apply Hy. split; zfc_simple.
    split... rewrite add_0... apply func_correct... rewrite Hhd...
Qed.

Lemma add_is_func : is_function Addition.
Proof. destruct add_maps_onto as []; auto. Qed.

Lemma add_ran : ∀ m n ∈ ω, m + n ∈ ω.
Proof with eauto.
  intros n Hn m Hm. eapply ap_ran. apply surjection_is_func.
  apply add_maps_onto. apply CProdI...
Qed.

Theorem add_ident : ∀m ∈ ω, m + 0 = m.
Proof with nauto.
  intros m Hm. eapply func_ap... apply add_is_func.
  apply SepI. apply CProdI... apply CProdI...
  split; zfc_simple. split... rewrite add_0...
Qed.

Theorem add_m_n : ∀ m n ∈ ω, m + n⁺ = (m + n)⁺.
Proof with eauto.
  intros m Hm n Hn. eapply func_ap... apply add_is_func.
  apply SepI. apply CProdI... apply CProdI...
  apply ω_inductive... apply ω_inductive... apply add_ran...
  split; zfc_simple. split. apply ω_inductive...
  cut (m + n = (Add m)[n]). intros Heq. rewrite Heq, add_n...
  eapply func_ap... apply add_is_func.
  apply SepI. apply CProdI... apply CProdI...
  destruct (add_correct m) as [h [Hh [Hheq _]]]...
  rewrite Hheq. eapply ap_ran... split; zfc_simple. split...
Qed.

Lemma add_m_ap : ∀ m n ∈ ω, (Add m)[n] = m + n.
Proof with auto.
  intros m Hm n Hn. generalize dependent m.
  set {n ∊ ω | λ n, ∀m ∈ ω, (Add m)[n] = m + n} as T.
  ω_induction T Hn; intros k Hk.
  - rewrite add_0, add_ident...
  - cut ((Add k)[m] = k + m). intros Heq.
    rewrite add_n, Heq, add_m_n... apply IH...
Qed.

(** 乘法 **)
Definition Mul : set → set := λ m, Arith (Add m) 0.

Lemma mul_correct : ∀m ∈ ω,
  ∃h, h: ω ⇒ ω ∧ (Mul m) = h ∧
  h[0] = 0 ∧ ∀n ∈ ω, h[n⁺] = m + h[n].
Proof with neauto; try congruence.
  intros m Hm.
  destruct (add_correct m) as [g [Hg [Hgeq _]]]...
  destruct (arith_correct (Add m) 0) as [h [Hh [Hheq [Hh0 Hh1]]]]...
  exists h. split... split... split... intros n Hn.
  apply Hh1 in Hn as Hap. rewrite Hap, add_m_ap...
  eapply ap_ran...
Qed.

Lemma mul_0 : ∀m ∈ ω, (Mul m)[0] = 0.
Proof with congruence.
  intros m Hm.
  destruct (mul_correct m) as [h [_ [Heq [Hh0 _]]]]...
Qed.

Lemma mul_n : ∀ m n ∈ ω, (Mul m)[n⁺] = m + (Mul m)[n].
Proof with auto.
  intros m Hm.
  destruct (mul_correct m) as [h [_ [Heq [_ Hh1]]]]...
  rewrite Heq...
Qed.

Definition Muliplication : set := BinOp ω Mul.
Notation "x ⋅ y" := (Muliplication[<x, y>])
  (at level 40) : Nat_scope.

Lemma mul_maps_onto : Muliplication: ω × ω ⟹ ω.
Proof with nauto; try congruence.
  split. apply binop_is_func.
  split. apply binop_dom. intros a Ha.
  destruct (mul_correct a) as [h [Hh [Hheq _]]]...
  apply ExtAx. intros y. split; intros Hy.
  - apply ranE in Hy as [n Hp]. apply SepE in Hp as [Hp _].
    apply CProdE2 in Hp as [_ Hy]...
  - destruct (mul_correct y) as [h [[Hh [Hhd Hhr]] [Hheq _]]]...
    cut (<1, h[1]> ∈ h). intros H0.
    eapply ranI. apply SepI. apply CProdI. apply CProdI.
    apply Hy. apply (embed_ran 1). apply Hy. split; zfc_simple.
    split... rewrite pred, mul_n, mul_0, add_ident...
    apply func_correct... rewrite Hhd...
Qed.

Lemma mul_is_func : is_function Muliplication.
Proof. destruct mul_maps_onto as []; auto. Qed.

Lemma mul_ran : ∀ m n ∈ ω, m ⋅ n ∈ ω.
Proof with auto.
  intros n Hn m Hm. eapply ap_ran. apply surjection_is_func.
  apply mul_maps_onto. apply CProdI...
Qed.

Theorem mul_0_r : ∀m ∈ ω, m ⋅ 0 = 0.
Proof with nauto.
  intros m Hm. eapply func_ap. apply mul_is_func.
  apply SepI... apply CProdI... apply CProdI...
  split; zfc_simple. split... rewrite mul_0...
Qed.

Theorem mul_m_n : ∀ m n ∈ ω, m ⋅ n⁺ = m + m ⋅ n.
Proof with eauto; try congruence.
  intros m Hm n Hn. eapply func_ap. apply mul_is_func.
  apply SepI. apply CProdI... apply CProdI...
  apply ω_inductive... apply add_ran... apply mul_ran...
  split; zfc_simple. split. apply ω_inductive...
  cut (m ⋅ n = (Mul m)[n]). intros Heq. rewrite Heq, mul_n...
  eapply func_ap. apply mul_is_func.
  apply SepI. apply CProdI... apply CProdI...
  destruct (mul_correct m) as [h [Hh [Heq _]]]...
  rewrite Heq. eapply ap_ran... split; zfc_simple. split...
Qed.

Lemma mul_m_ap : ∀ m n ∈ ω, (Mul m)[n] = m ⋅ n.
Proof with auto.
  intros m Hm n Hn. generalize dependent m.
  set {n ∊ ω | λ n, ∀m ∈ ω, (Mul m)[n] = m ⋅ n} as T.
  ω_induction T Hn; intros k Hk.
  - rewrite mul_0... rewrite mul_0_r...
  - cut ((Mul k)[m] = k ⋅ m). intros Heq.
    rewrite mul_n, Heq, mul_m_n... apply IH...
Qed.

(** 指数运算 **)
Definition Exp : set → set := λ m, Arith (Mul m) 1.

Lemma exp_correct : ∀m ∈ ω,
  ∃h, h: ω ⇒ ω ∧ (Exp m) = h ∧
  h[0] = 1 ∧ ∀n ∈ ω, h[n⁺] = m ⋅ h[n].
Proof with neauto; try congruence.
  intros m Hm.
  destruct (mul_correct m) as [g [Hg [Hgeq _]]]...
  destruct (arith_correct (Mul m) 1)
    as [h [Hh [Hheq [Hh0 Hh1]]]]...
  exists h. split... split... split...
  intros n Hn. apply Hh1 in Hn as Hap.
  rewrite Hap, mul_m_ap... eapply ap_ran...
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
Notation "x ^ y" := (Exponentiation[<x, y>]) : Nat_scope.

Lemma exp_maps_onto : Exponentiation: ω × ω ⟹ ω.
Proof with nauto; try congruence.
  split. apply binop_is_func.
  split. apply binop_dom. intros a Ha.
  destruct (exp_correct a) as [h [Hh [Hheq _]]]...
  apply ExtAx. intros y. split; intros Hy.
  - apply ranE in Hy as [n Hp]. apply SepE in Hp as [Hp _].
    apply CProdE2 in Hp as [_ Hy]...
  - destruct (exp_correct y) as [h [[Hh [Hhd Hhr]] [Hheq _]]]...
    cut (<1, h[1]> ∈ h). intros H0.
    eapply ranI. apply SepI. apply CProdI. apply CProdI.
    apply Hy. apply (embed_ran 1). apply Hy.
    split; zfc_simple. split...
    rewrite pred, exp_n, exp_0, pred, mul_m_n, mul_0_r, add_ident...
    apply func_correct... rewrite Hhd...
Qed.

Lemma exp_is_func : is_function Exponentiation.
Proof. destruct exp_maps_onto as []; auto. Qed.

Lemma exp_ran : ∀ m n ∈ ω, m ^ n ∈ ω.
Proof with auto.
  intros n Hn m Hm. eapply ap_ran. apply surjection_is_func.
  apply exp_maps_onto. apply CProdI...
Qed.

Theorem exp_0_r : ∀m ∈ ω, m ^ 0 = 1.
Proof with nauto.
  intros m Hm. eapply func_ap. apply exp_is_func.
  apply SepI... apply CProdI... apply CProdI...
  split; zfc_simple. split... rewrite exp_0...
Qed.

Theorem exp_m_n : ∀ m n ∈ ω, m ^ n⁺ = m ⋅ m ^ n.
Proof with eauto; try congruence.
  intros m Hm n Hn. eapply func_ap. apply exp_is_func.
  apply SepI. apply CProdI. apply CProdI...
  apply ω_inductive... apply mul_ran... apply exp_ran...
  split; zfc_simple. split. apply ω_inductive...
  cut (m ^ n = (Exp m)[n]). intros. rewrite H.
  rewrite exp_n; auto. eapply func_ap. apply exp_is_func.
  apply SepI. apply CProdI. apply CProdI...
  destruct (exp_correct m) as [h [Hh [Heq _]]]...
  rewrite Heq. eapply ap_ran... split; zfc_simple. split...
Qed.

Lemma exp_m_ap : ∀ m n ∈ ω, (Exp m)[n] = m ^ n.
Proof with auto.
  intros m Hm n Hn. generalize dependent m.
  set {n ∊ ω | λ n, ∀m ∈ ω, (Exp m)[n] = m ^ n} as T.
  ω_induction T Hn; intros k Hk.
  - rewrite exp_0, exp_0_r...
  - cut ((Exp k)[m] = k ^ m). intros.
    rewrite exp_m_n, exp_n, H... apply IH...
Qed.

Example add_1_2 : 1 + 2 = 3.
Proof.
  rewrite (pred 2), add_m_n, (pred 1), add_m_n, add_ident;
    auto; repeat apply ω_inductive...
Qed.

Example mul_2_2 : 2 ⋅ 2 = 4.
Proof with auto.
  rewrite (pred 2), mul_m_n, (pred 1), mul_m_n, mul_0_r,
    add_ident, add_m_n, add_m_n, add_ident;
    auto; repeat apply ω_inductive...
Qed.

(* 加法结合律 *)
Theorem add_assoc : ∀ m n p ∈ ω, (m + n) + p = m + (n + p).
Proof with auto.
  intros n Hn m Hm p Hp.
  generalize dependent n. generalize dependent m.
  set {p ∊ ω | λ p, ∀ m, m ∈ ω → ∀ n, n ∈ ω →
    (m + n) + p = m + (n + p)} as N.
  ω_induction N Hp; intros n Hn k Hk.
  - repeat rewrite add_ident... apply add_ran...
  - repeat rewrite add_m_n; try apply add_ran... rewrite IH...
Qed.

Lemma add_ident' : ∀n ∈ ω, 0 + n = n.
Proof with nauto.
  intros n Hn.
  set {n ∊ ω | λ n, 0 + n = n} as N.
  ω_induction N Hn. rewrite add_ident...
  rewrite add_m_n... rewrite IH...
Qed.

Lemma add_m_n' : ∀ m n ∈ ω, m⁺ + n = (m + n)⁺.
Proof with auto.
  intros m Hm n Hn. generalize dependent m.
  set {n ∊ ω | λ n, ∀ m, m ∈ ω → m⁺ + n = (m + n)⁺} as N.
  ω_induction N Hn; intros k Hk.
  - repeat rewrite add_ident... apply ω_inductive...
  - repeat rewrite add_m_n...
    rewrite IH... apply ω_inductive...
Qed.

(* 加法交换律 *)
Theorem add_comm : ∀ m n ∈ ω, m + n = n + m.
Proof with auto.
  intros n Hn m Hm. ω_destruct m; subst m.
  rewrite add_ident', add_ident...
  rewrite add_m_n...
  clear Hm. generalize dependent n'.
  set {n ∊ ω | λ n, ∀ n', n' ∈ ω → (n + n')⁺ = n'⁺ + n} as N.
  ω_induction N Hn; intros k Hk.
  - rewrite add_ident', add_ident... apply ω_inductive...
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
Theorem mul_distr : ∀ m n p ∈ ω, m ⋅ (n + p) = m ⋅ n + m ⋅ p.
Proof with auto.
  intros m Hm n Hn p Hp.
  generalize dependent n. generalize dependent m.
  set {p ∊ ω | λ p, ∀ m, m ∈ ω → ∀ n, n ∈ ω →
    m ⋅ (n + p) = m ⋅ n + m ⋅ p} as N.
  ω_induction N Hp; intros n Hn k Hk.
  - rewrite add_ident, mul_0_r, add_ident... apply mul_ran...
  - rewrite add_m_n, mul_m_n, mul_m_n... rewrite IH...
    rewrite add_comm... rewrite (add_comm n)...
    rewrite add_assoc; try apply mul_ran... apply mul_ran...
    apply add_ran; apply mul_ran... apply add_ran...
Qed.

(* 乘法结合律 *)
Theorem mul_assoc : ∀ m n p ∈ ω, (m ⋅ n) ⋅ p = m ⋅ (n ⋅ p).
Proof with auto.
  intros n Hn m Hm p Hp.
  generalize dependent n. generalize dependent m.
  set {p ∊ ω | λ p, ∀ m, m ∈ ω → ∀ n, n ∈ ω →
    (m ⋅ n) ⋅ p = m ⋅ (n ⋅ p)} as N.
  ω_induction N Hp; intros n Hn k Hk.
  - repeat rewrite mul_0_r... apply mul_ran...
  - repeat rewrite mul_m_n... rewrite mul_distr...
    rewrite IH... apply mul_ran... apply mul_ran...
Qed.

Lemma mul_0_l : ∀n ∈ ω, 0 ⋅ n = 0.
Proof with nauto.
  intros n Hn.
  set {n ∊ ω | λ n, 0 ⋅ n = 0} as N.
  ω_induction N Hn. rewrite mul_0_r...
  rewrite mul_m_n... rewrite IH... rewrite add_ident...
Qed.

Lemma mul_m_n' : ∀ m n ∈ ω, m⁺ ⋅ n = n + (m ⋅ n).
Proof with nauto.
  intros m Hm n Hn. generalize dependent m.
  set {n ∊ ω | λ n, ∀ m, m ∈ ω → m⁺ ⋅ n = n + (m ⋅ n)} as N.
  ω_induction N Hn; intros k Hk.
  - repeat rewrite mul_0_r...
    rewrite add_ident... apply ω_inductive...
  - repeat rewrite mul_m_n; try apply ω_inductive...
    rewrite IH... repeat rewrite add_m_n';
      try apply add_ran; try apply mul_ran...
    repeat rewrite <- add_assoc; try apply mul_ran...
    rewrite add_comm_123_213... apply mul_ran...
Qed.

(* 乘法交换律 *)
Theorem mul_comm : ∀ m n ∈ ω, m ⋅ n = n ⋅ m.
Proof with nauto.
  intros n Hn m Hm. ω_destruct m; subst m.
  rewrite mul_0_l, mul_0_r...
  rewrite mul_m_n...
  clear Hm. generalize dependent n'.
  set {n ∊ ω | λ n, ∀ n', n' ∈ ω → n + n ⋅ n' = n'⁺ ⋅ n} as N.
  ω_induction N Hn; intros k Hk.
  - rewrite mul_0_l, mul_0_r, add_ident... apply ω_inductive...
  - rewrite mul_m_n, mul_m_n'; try apply ω_inductive...
    repeat rewrite add_m_n'... rewrite <- IH...
    repeat rewrite <- add_assoc; try apply mul_ran...
    rewrite add_comm_123_213; try apply mul_ran...
    apply mul_ran... apply ω_inductive...
    apply add_ran... apply mul_ran...
Qed.

Lemma mul_distr' : ∀ m n p ∈ ω, (m + n) ⋅ p = m ⋅ p + n ⋅ p.
Proof with auto.
  intros m Hm n Hn p Hp.
  rewrite mul_comm, mul_distr, mul_comm, (mul_comm p)...
  apply add_ran...
Qed.

Lemma add_a_b_a : ∀ a b ∈ ω, a + b = a → b = 0.
Proof with auto.
  intros a Ha b Hb.
  set {a ∊ ω | λ a, a + b = a → b = 0} as N.
  ω_induction N Ha; intros Heq.
  - rewrite add_ident' in Heq...
  - rewrite add_m_n' in Heq...
    apply suc_injective in Heq... apply add_ran...
Qed.

Lemma add_0_l_0 : ∀n ∈ ω, 0 + n = 0 → n = 0.
Proof with neauto.
  intros n Hn H0.
  ω_destruct n... subst n. rewrite add_m_n in H0...
  exfalso. eapply suc_neq_0...
Qed.

Lemma add_m_n_0 : ∀ m n ∈ ω, m + n = 0 → m = 0 ∧ n = 0.
Proof with eauto.
  intros m Hm n Hn H0.
  ω_destruct m; ω_destruct n; subst m n. split...
  split... eapply add_a_b_a; revgoals...
  split... eapply add_a_b_a; revgoals.
  rewrite add_comm... apply Hm. apply ω_has_0.
  rewrite add_m_n in H0... exfalso. eapply suc_neq_0...
Qed.

Lemma mul_m_n_0 : ∀ m n ∈ ω, m ⋅ n = 0 → m = 0 ∨ n = 0.
Proof with eauto.
  intros m Hm n Hn H0.
  ω_destruct m. left... ω_destruct n. right...
  exfalso. subst m n. rewrite mul_m_n, mul_m_n' in H0...
  apply add_m_n_0 in H0 as [H1 _]...
  exfalso. eapply suc_neq_0... apply add_ran... apply mul_ran...
Qed.

Definition even : set → Prop := λ n, ∃m ∈ ω, n = 2 ⋅ m.

Definition odd : set → Prop := λ n, ∃p ∈ ω, n = 2 ⋅ p + 1.

Lemma add_suc : ∀n ∈ ω, n⁺ = n + 1.
Proof with neauto.
  intros n Hn.
  set {n ∊ ω | λ n, n⁺ = n + 1} as N.
  ω_induction N Hn.
  - rewrite add_ident'...
  - rewrite add_m_n'... rewrite IH...
Qed.

Lemma mul_ident : ∀n ∈ ω, n ⋅ 1 = n.
Proof with neauto.
  intros n Hn.
  set {n ∊ ω | λ n, n ⋅ 1 = n} as N.
  ω_induction N Hn.
  - rewrite mul_0_l...
  - rewrite mul_m_n'... rewrite IH.
    rewrite (add_suc m)... rewrite add_comm...
Qed.

Theorem exp_distr : ∀ m n p ∈ ω, m ^ (n + p) = m ^ n ⋅ m ^ p.
Proof with try assumption; try congruence.
  intros n Hn m Hm p Hp.
  generalize dependent n. generalize dependent m.
  set {p ∊ ω | λ p, ∀ m, m ∈ ω → ∀ n, n ∈ ω →
    n ^ (m + p) = n ^ m ⋅ n ^ p} as N.
  ω_induction N Hp; intros n Hn k Hk.
  - rewrite add_ident, exp_0_r, mul_ident... apply exp_ran...
  - rewrite add_m_n, exp_m_n, exp_m_n; try apply add_ran...
    rewrite (IH n Hn k Hk).
    rewrite <- mul_assoc, <- mul_assoc; try apply exp_ran...
    rewrite (mul_comm k); try apply exp_ran...
Qed.
