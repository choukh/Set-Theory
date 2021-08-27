(** Adapted from "Elements of Set Theory" Chapter 4 **)
(** Coq coding by choukh, May 2020 **)

Global Set Warnings "-ambiguous-paths".

Require Export ZFC.Theory.EST4_1.

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
  ext Hx.
  - apply BUnionE in Hx as []. exfalso0. apply H.
  - apply BUnionI2. apply Hx.
Qed.

Lemma two : Embed 2 = 2%zfc1.
Proof.
  ext Hx.
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
  ω_induction n. exists 0...
  destruct IH as [k' Heq]. subst. exists (S k')...
Qed.

(* 集合论自然数与元语言自然数同构 *)
Lemma proj_embed_id : ∀ n : nat, Proj (Embed n) = n. 
Proof.
  intros. unfold Proj.
  destruct (dit (sig (λ k, iter k Suc ∅ = Embed n))).
  - destruct s as [k H]. now apply embed_injective in H.
  - exfalso. apply f. exists n. reflexivity.
Qed.

Lemma embed_proj_id : ∀n ∈ ω, Embed (Proj n) = n.
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

Declare Scope omega_scope.
Delimit Scope omega_scope with ω.
Open Scope omega_scope.

(* 二元运算 *)
Definition BinOp : set → (set → set) → set := λ A F,
  {q ∊ (A × A) × A |
    let m := π1 (π1 q) in
    let n := π2 (π1 q) in
    let p := π2 q in
    m ∈ A ∧ n ∈ A ∧ p = (F m)[n]
  }.

Lemma binop_is_func : ∀ A F, is_function (BinOp A F).
Proof with auto.
  split.
  - intros x Hx. apply SepE in Hx as [Hx _].
    apply cprd_is_pairs in Hx...
  - intros x Hx. rewrite <- unique_existence.
    split. apply domE in Hx...
    intros y1 y2 H1 H2.
    apply SepE in H1 as [_ [_ [_ Hp1]]].
    apply SepE in H2 as [_ [_ [_ Hp2]]]. zfc_simple.
Qed.

Lemma binop_dom : ∀ A F, (∀a ∈ A, F a: A ⇒ A) →
  dom (BinOp A F) = A × A.
Proof with eauto; try congruence.
  intros. ext Hx.
  - apply domE in Hx as [y Hp]. apply SepE in Hp as [Hx _].
    apply CPrdE2 in Hx as [Hx _]...
  - assert (Hx' := Hx).
    apply CPrdE1 in Hx' as [a [Ha [b [Hb Heq]]]].
    destruct (H a) as [Hh [Hhd Hhr]]...
    rewrite <- Hhd in Hb. apply func_correct in Hb as Hbp...
    eapply domI. apply SepI. apply CPrdI. apply Hx.
    apply Hhr. eapply ranI... subst x. split; zfc_simple. split...
Qed.

(* 加法 *)
Definition Add : set → set := λ m, ω_Recursion σ ω m.

Lemma add_function : ∀ m ∈ ω, Add m : ω ⇒ ω.
Proof.
  intros m Hm.
  apply ω_recursion_spec_intro; auto. apply σ_function.
Qed.

Lemma add_m_ran : ∀ m n ∈ ω, (Add m)[n] ∈ ω.
Proof with eauto.
  intros m Hm n Hn.
  eapply ap_ran... apply add_function...
Qed.

Lemma add_m_0 : ∀m ∈ ω, (Add m)[0] = m.
Proof.
  intros m Hm.
  apply ω_recursion_spec_intro; auto. apply σ_function.
Qed.

Lemma add_m_suc : ∀ m n ∈ ω, (Add m)[n⁺] = (Add m)[n]⁺.
Proof with eauto.
  intros m Hm n Hn.
  rewrite <- (σ_ap (Add m)[n]).
  apply ω_recursion_spec_intro... apply σ_function.
  apply add_m_ran...
Qed.

Definition BinAdd : set := BinOp ω Add.
Notation "x + y" := (BinAdd[<x, y>]) : omega_scope.

Lemma binAdd_surjection : BinAdd: ω × ω ⟹ ω.
Proof with neauto; try congruence.
  split. apply binop_is_func.
  split. apply binop_dom. intros a Ha.
  apply add_function...
  ext y Hy.
  - apply ranE in Hy as [n Hp]. apply SepE in Hp as [Hp _].
    apply CPrdE2 in Hp as [_ Hy]...
  - eapply ranI. apply SepI. apply CPrdI. apply CPrdI.
    apply Hy. apply ω_has_0. apply Hy. split; zfc_simple.
    split... rewrite add_m_0...
Qed.

Lemma binAdd_is_func : is_function BinAdd.
Proof. destruct binAdd_surjection as []; auto. Qed.

Lemma add_ran : ∀ m n ∈ ω, m + n ∈ ω.
Proof with eauto.
  intros n Hn m Hm. eapply ap_ran. apply surjection_is_func.
  apply binAdd_surjection. apply CPrdI...
Qed.
Local Hint Resolve add_ran : core.

Theorem add_0_r : ∀m ∈ ω, m + 0 = m.
Proof with nauto.
  intros m Hm. eapply func_ap... apply binAdd_is_func.
  apply SepI. apply CPrdI... apply CPrdI...
  split; zfc_simple. split... rewrite add_m_0...
Qed.

Theorem add_suc : ∀ m n ∈ ω, m + n⁺ = (m + n)⁺.
Proof with eauto.
  intros m Hm n Hn. eapply func_ap... apply binAdd_is_func.
  apply SepI. apply CPrdI... apply CPrdI...
  apply ω_inductive... apply ω_inductive...
  split; zfc_simple. split. apply ω_inductive...
  cut (m + n = (Add m)[n]). intros Heq. rewrite Heq, add_m_suc...
  eapply func_ap... apply binAdd_is_func.
  apply SepI. apply CPrdI... apply CPrdI...
  apply add_m_ran... split; zfc_simple. split...
Qed.

Lemma add_m_ap : ∀ m n ∈ ω, (Add m)[n] = m + n.
Proof with auto.
  intros m Hm n Hn. generalize dependent m.
  ω_induction n; intros k Hk.
  - rewrite add_m_0, add_0_r...
  - cut ((Add k)[m] = k + m). intros Heq.
    rewrite add_m_suc, Heq, add_suc... apply IH...
Qed.

(* 乘法 *)
Definition Mul : set → set := λ m, ω_Recursion (Add m) ω 0.

Lemma mul_function : ∀ m ∈ ω, Mul m : ω ⇒ ω.
Proof with neauto.
  intros m Hm.
  apply ω_recursion_spec_intro... apply add_function...
Qed.

Lemma mul_m_ran : ∀ m n ∈ ω, (Mul m)[n] ∈ ω.
Proof with eauto.
  intros m Hm n Hn.
  eapply ap_ran... apply mul_function...
Qed.

Lemma mul_m_0 : ∀m ∈ ω, (Mul m)[0] = 0.
Proof with nauto.
  intros m Hm.
  apply ω_recursion_spec_intro... apply add_function...
Qed.

Lemma mul_m_suc : ∀ m n ∈ ω, (Mul m)[n⁺] = m + (Mul m)[n].
Proof with neauto.
  intros m Hm n Hn.
  rewrite <- add_m_ap...
  apply ω_recursion_spec_intro...
  apply add_function... apply mul_m_ran...
Qed.

Definition BinMul : set := BinOp ω Mul.
Notation "x ⋅ y" := (BinMul[<x, y>])
  (at level 40) : omega_scope.

Lemma binMul_surjection : BinMul: ω × ω ⟹ ω.
Proof with nauto; try congruence.
  split. apply binop_is_func.
  split. apply binop_dom. intros a Ha.
  apply mul_function...
  ext y Hy.
  - apply ranE in Hy as [n Hp]. apply SepE in Hp as [Hp _].
    apply CPrdE2 in Hp as [_ Hy]...
  - eapply ranI. apply SepI. apply CPrdI. apply CPrdI.
    apply Hy. apply (embed_ran 1). apply Hy. split; zfc_simple.
    split... rewrite pred, mul_m_suc, mul_m_0, add_0_r...
Qed.

Lemma binMul_is_func : is_function BinMul.
Proof. destruct binMul_surjection as []; auto. Qed.

Lemma mul_ran : ∀ m n ∈ ω, m ⋅ n ∈ ω.
Proof with auto.
  intros n Hn m Hm. eapply ap_ran. apply surjection_is_func.
  apply binMul_surjection. apply CPrdI...
Qed.
Local Hint Resolve mul_ran : core.

Theorem mul_0_r : ∀m ∈ ω, m ⋅ 0 = 0.
Proof with nauto.
  intros m Hm. eapply func_ap. apply binMul_is_func.
  apply SepI... apply CPrdI... apply CPrdI...
  split; zfc_simple. split... rewrite mul_m_0...
Qed.

Theorem mul_suc : ∀ m n ∈ ω, m ⋅ n⁺ = m + m ⋅ n.
Proof with eauto; try congruence.
  intros m Hm n Hn. eapply func_ap. apply binMul_is_func.
  apply SepI. apply CPrdI... apply CPrdI... apply ω_inductive...
  split; zfc_simple. split. apply ω_inductive...
  cut (m ⋅ n = (Mul m)[n]). intros Heq. rewrite Heq, mul_m_suc...
  eapply func_ap. apply binMul_is_func.
  apply SepI. apply CPrdI... apply CPrdI...
  apply mul_m_ran... split; zfc_simple. split...
Qed.

Lemma mul_m_ap : ∀ m n ∈ ω, (Mul m)[n] = m ⋅ n.
Proof with auto.
  intros m Hm n Hn. generalize dependent m.
  ω_induction n; intros k Hk.
  - rewrite mul_m_0... rewrite mul_0_r...
  - cut ((Mul k)[m] = k ⋅ m). intros Heq.
    rewrite mul_m_suc, Heq, mul_suc... apply IH...
Qed.

(* 乘方 *)
Definition Exp : set → set := λ m, ω_Recursion (Mul m) ω 1.

Lemma exp_function : ∀ m ∈ ω, Exp m : ω ⇒ ω.
Proof with neauto.
  intros m Hm.
  apply ω_recursion_spec_intro... apply mul_function...
Qed.

Lemma exp_m_ran : ∀ m n ∈ ω, (Exp m)[n] ∈ ω.
Proof with neauto.
  intros m Hm n Hn.
  eapply ap_ran... apply exp_function...
Qed.

Lemma exp_m_0 : ∀m ∈ ω, (Exp m)[0] = 1.
Proof with nauto.
  intros m Hm.
  apply ω_recursion_spec_intro... apply mul_function...
Qed.

Lemma exp_m_suc : ∀ m n ∈ ω, (Exp m)[n⁺] = m ⋅ (Exp m)[n].
Proof with neauto.
  intros m Hm n Hn.
  rewrite <- mul_m_ap...
  apply ω_recursion_spec_intro...
  apply mul_function... apply exp_m_ran...
Qed.

Definition BinExp : set := BinOp ω Exp.
Notation "x ^ y" := (BinExp[<x, y>]) : omega_scope.

Lemma binExp_surjection : BinExp: ω × ω ⟹ ω.
Proof with nauto; try congruence.
  split. apply binop_is_func.
  split. apply binop_dom. intros a Ha.
  apply exp_function...
  ext y Hy.
  - apply ranE in Hy as [n Hp]. apply SepE in Hp as [Hp _].
    apply CPrdE2 in Hp as [_ Hy]...
  - eapply ranI. apply SepI. apply CPrdI. apply CPrdI.
    apply Hy. apply (embed_ran 1). apply Hy.
    split; zfc_simple. split...
    rewrite pred, exp_m_suc, exp_m_0, pred,
      mul_suc, mul_0_r, add_0_r...
Qed.

Lemma binExp_is_func : is_function BinExp.
Proof. destruct binExp_surjection as []; auto. Qed.

Lemma exp_ran : ∀ m n ∈ ω, m ^ n ∈ ω.
Proof with auto.
  intros n Hn m Hm. eapply ap_ran. apply surjection_is_func.
  apply binExp_surjection. apply CPrdI...
Qed.
Local Hint Resolve exp_ran : core.

Theorem exp_0_r : ∀n ∈ ω, n ^ 0 = 1.
Proof with nauto.
  intros n Hn. eapply func_ap. apply binExp_is_func.
  apply SepI... apply CPrdI... apply CPrdI...
  split; zfc_simple. split... rewrite exp_m_0...
Qed.

Theorem exp_suc : ∀ m n ∈ ω, m ^ n⁺ = m ⋅ m ^ n.
Proof with eauto; try congruence.
  intros m Hm n Hn. eapply func_ap. apply binExp_is_func.
  apply SepI. apply CPrdI. apply CPrdI...
  apply ω_inductive... apply mul_ran...
  split; zfc_simple. split. apply ω_inductive...
  cut (m ^ n = (Exp m)[n]). intros. rewrite H.
  rewrite exp_m_suc; auto. eapply func_ap. apply binExp_is_func.
  apply SepI. apply CPrdI. apply CPrdI...
  apply exp_m_ran... split; zfc_simple. split...
Qed.

Lemma exp_m_ap : ∀ m n ∈ ω, (Exp m)[n] = m ^ n.
Proof with auto.
  intros m Hm n Hn. generalize dependent m.
  ω_induction n; intros k Hk.
  - rewrite exp_m_0, exp_0_r...
  - cut ((Exp k)[m] = k ^ m). intros.
    rewrite exp_suc, exp_m_suc, H... apply IH...
Qed.

Example add_1_1 : 1 + 1 = 2.
Proof with auto.
  rewrite pred, add_suc, add_0_r;
    auto; repeat apply ω_inductive.
Qed.

Example add_1_2 : 1 + 2 = 3.
Proof.
  rewrite (pred 2), add_suc, (pred 1), add_suc, add_0_r;
    auto; repeat apply ω_inductive...
Qed.

Example mul_2_2 : 2 ⋅ 2 = 4.
Proof with auto.
  rewrite (pred 2), mul_suc, (pred 1), mul_suc, mul_0_r,
    add_0_r, add_suc, add_suc, add_0_r;
    auto; repeat apply ω_inductive...
Qed.

(* 加法结合律 *)
Theorem add_assoc : ∀ m n p ∈ ω, (m + n) + p = m + (n + p).
Proof with auto.
  intros n Hn m Hm p Hp.
  generalize dependent n. generalize dependent m.
  ω_induction p; intros n Hn k Hk.
  - repeat rewrite add_0_r...
  - repeat rewrite add_suc... rewrite IH...
Qed.

Lemma add_0_l : ∀n ∈ ω, 0 + n = n.
Proof with nauto.
  intros n Hn.
  ω_induction n. rewrite add_0_r...
  rewrite add_suc... rewrite IH...
Qed.

Lemma add_suc' : ∀ m n ∈ ω, m⁺ + n = (m + n)⁺.
Proof with auto.
  intros m Hm n Hn. generalize dependent m.
  ω_induction n; intros k Hk.
  - repeat rewrite add_0_r... apply ω_inductive...
  - repeat rewrite add_suc...
    rewrite IH... apply ω_inductive...
Qed.

(* 加法交换律 *)
Theorem add_comm : ∀ m n ∈ ω, m + n = n + m.
Proof with auto.
  intros n Hn m Hm. ω_destruct m; subst m.
  rewrite add_0_l, add_0_r...
  rewrite add_suc...
  clear Hm. generalize dependent n'.
  ω_induction n; intros k Hk.
  - rewrite add_0_l, add_0_r... apply ω_inductive...
  - rewrite add_suc, add_suc'...
    rewrite IH... apply ω_inductive...
Qed.

Corollary add_comm_123_213 : ∀ m n p ∈ ω, m + n + p = n + m + p.
Proof with auto.
  intros m Hm n Hn p Hp. rewrite add_comm...
  rewrite (add_comm (n + m))... rewrite (add_comm m)...
Qed.

(* 乘法分配律 *)
Theorem mul_distr : ∀ m n p ∈ ω, m ⋅ (n + p) = m ⋅ n + m ⋅ p.
Proof with auto.
  intros m Hm n Hn p Hp.
  generalize dependent n. generalize dependent m.
  ω_induction p; intros n Hn k Hk.
  - rewrite add_0_r, mul_0_r, add_0_r...
  - rewrite add_suc, mul_suc, mul_suc... rewrite IH...
    rewrite add_comm, (add_comm n), add_assoc...
Qed.

(* 乘法结合律 *)
Theorem mul_assoc : ∀ m n p ∈ ω, (m ⋅ n) ⋅ p = m ⋅ (n ⋅ p).
Proof with auto.
  intros n Hn m Hm p Hp.
  generalize dependent n. generalize dependent m.
  ω_induction p; intros n Hn k Hk.
  - repeat rewrite mul_0_r...
  - repeat rewrite mul_suc... rewrite mul_distr, IH...
Qed.

Lemma mul_0_l : ∀n ∈ ω, 0 ⋅ n = 0.
Proof with nauto.
  intros n Hn.
  ω_induction n. rewrite mul_0_r...
  rewrite mul_suc, IH, add_0_r...
Qed.

Lemma mul_suc' : ∀ m n ∈ ω, m⁺ ⋅ n = n + (m ⋅ n).
Proof with nauto.
  intros m Hm n Hn. generalize dependent m.
  ω_induction n; intros k Hk.
  - repeat rewrite mul_0_r...
    rewrite add_0_r... apply ω_inductive...
  - repeat rewrite mul_suc; try apply ω_inductive...
    rewrite IH... repeat rewrite add_suc'...
    repeat rewrite <- add_assoc...
    rewrite add_comm_123_213...
Qed.

(* 乘法交换律 *)
Theorem mul_comm : ∀ m n ∈ ω, m ⋅ n = n ⋅ m.
Proof with nauto.
  intros n Hn m Hm. ω_destruct m; subst m.
  rewrite mul_0_l, mul_0_r...
  rewrite mul_suc...
  clear Hm. generalize dependent n'.
  ω_induction n; intros k Hk.
  - rewrite mul_0_l, mul_0_r, add_0_r... apply ω_inductive...
  - rewrite mul_suc, mul_suc'; try apply ω_inductive...
    repeat rewrite add_suc'... rewrite <- IH...
    repeat rewrite <- add_assoc...
    rewrite add_comm_123_213...
    apply mul_ran... apply ω_inductive...
Qed.

Lemma mul_distr' : ∀ m n p ∈ ω, (m + n) ⋅ p = m ⋅ p + n ⋅ p.
Proof with auto.
  intros m Hm n Hn p Hp.
  rewrite mul_comm, mul_distr, mul_comm, (mul_comm p)...
Qed.

Lemma suc : ∀n ∈ ω, n⁺ = n + 1.
Proof with neauto.
  intros n Hn.
  ω_induction n.
  - rewrite add_0_l...
  - rewrite add_suc'... rewrite IH...
Qed.

Corollary add_1_r : ∀n ∈ ω, n + 1 = n⁺.
Proof. intros n Hn. rewrite suc; auto. Qed.

Corollary add_1_l : ∀n ∈ ω, 1 + n = n⁺.
Proof. intros n Hn. rewrite add_comm, add_1_r; nauto. Qed.

Lemma mul_2_l : ∀m ∈ ω, 2 ⋅ m = m + m.
Proof with nauto.
  intros n Hn.
  ω_induction n.
  - rewrite mul_0_r, add_0_r...
  - rewrite mul_suc, IH...
    assert (Hmm: m + m ∈ ω) by (apply add_ran; auto).
    rewrite add_suc, add_suc', suc, suc...
    rewrite (add_assoc (m + m)), (add_comm 2), add_1_1...
    apply ω_inductive... apply ω_inductive...
Qed.

Lemma mul_1_r : ∀n ∈ ω, n ⋅ 1 = n.
Proof with neauto.
  intros n Hn. ω_induction n.
  - rewrite mul_0_l...
  - rewrite mul_suc'... rewrite IH.
    rewrite (suc m)... rewrite add_comm...
Qed.

Corollary mul_1_l : ∀n ∈ ω, 1 ⋅ n = n.
Proof with nauto.
  intros n Hn. rewrite mul_comm... apply mul_1_r...
Qed.

Theorem exp_0_l : ∀n ∈ ω, n ≠ 0 → 0 ^ n = 0.
Proof with nauto.
  intros n Hn. ω_destruct n; subst; intros Hne. exfalso...
  rewrite exp_suc, mul_0_l...
Qed.

Theorem exp_1_r : ∀ n ∈ ω, n ^ 1 = n.
Proof.
  intros n Hn.
  rewrite pred, exp_suc, exp_0_r, mul_1_r; nauto.
Qed.

Theorem exp_1_l : ∀ n ∈ ω, 1 ^ n = 1.
Proof with nauto.
  intros n Hn. ω_induction n.
  - apply exp_0_r...
  - rewrite exp_suc, IH, mul_1_r...
Qed.

Theorem exp_add : ∀ m n p ∈ ω, m ^ (n + p) = m ^ n ⋅ m ^ p.
Proof with auto.
  intros n Hn m Hm p Hp.
  generalize dependent n. generalize dependent m.
  ω_induction p; intros n Hn k Hk.
  - rewrite add_0_r, exp_0_r, mul_1_r...
  - rewrite add_suc, exp_suc, exp_suc...
    rewrite (IH n Hn k Hk).
    rewrite <- mul_assoc, <- mul_assoc...
    rewrite (mul_comm k)...
Qed.

Theorem exp_mul : ∀ m n p ∈ ω, (m ⋅ n) ^ p = m ^ p ⋅ n ^ p.
Proof with nauto.
  intros m Hm n Hn p Hp.
  generalize dependent n. generalize dependent m.
  ω_induction p; intros n Hn k Hk.
  - repeat rewrite exp_0_r... rewrite mul_1_r...
  - repeat rewrite exp_suc...
    rewrite <- mul_assoc, (mul_comm (n ⋅ n ^ m)),
      <- mul_assoc, (mul_comm k), (mul_assoc (n ⋅ k)), IH...
Qed.

Theorem exp_exp : ∀ m n p ∈ ω, (m ^ n) ^ p = m ^ (n ⋅ p).
Proof with nauto.
  intros m Hm n Hn p Hp.
  generalize dependent n. generalize dependent m.
  ω_induction p; intros n Hn k Hk.
  - rewrite mul_0_r, exp_0_r, exp_0_r...
  - rewrite exp_suc, mul_suc, exp_add, IH...
Qed.

Lemma add_a_b_eq_a : ∀ a b ∈ ω, a + b = a → b = 0.
Proof with auto.
  intros a Ha b Hb.
  ω_induction a; intros Heq.
  - rewrite add_0_l in Heq...
  - rewrite add_suc' in Heq...
    apply suc_injective in Heq...
Qed.

Lemma add_0_l_eq_0 : ∀n ∈ ω, 0 + n = 0 → n = 0.
Proof with neauto.
  intros n Hn H0.
  ω_destruct n... subst n. rewrite add_suc in H0...
  exfalso. eapply suc_neq_0...
Qed.

Lemma add_eq_0 : ∀ m n ∈ ω, m + n = 0 → m = 0 ∧ n = 0.
Proof with eauto.
  intros m Hm n Hn H0.
  ω_destruct m; ω_destruct n; subst; split...
  - rewrite add_0_l in H0...
  - rewrite add_0_r in H0...
  - rewrite add_suc in H0... exfalso. eapply suc_neq_0...
  - rewrite add_suc in H0... exfalso. eapply suc_neq_0...
Qed.

Lemma mul_eq_0 : ∀ m n ∈ ω, m ⋅ n = 0 → m = 0 ∨ n = 0.
Proof with eauto.
  intros m Hm n Hn. generalize dependent m.
  ω_induction n; intros k Hk H0. right...
  rewrite mul_suc in H0...
  apply add_eq_0 in H0 as []...
Qed.

Lemma exp_eq_0 : ∀ m n ∈ ω, m ^ n = 0 → m = 0.
Proof with eauto.
  intros m Hm n Hn. generalize dependent m.
  ω_induction n; intros k Hk H0.
  - rewrite exp_0_r in H0... exfalso. eapply suc_neq_0...
  - rewrite exp_suc in H0...
    apply mul_eq_0 in H0 as []...
Qed.

Definition even : set → Prop := λ n, ∃m ∈ ω, n = 2 ⋅ m.
Definition odd : set → Prop := λ n, ∃p ∈ ω, n = 2 ⋅ p + 1.
