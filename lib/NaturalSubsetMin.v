(** Coq coding by choukh, Oct 2020 **)

Require Import ZFC.lib.Natural.

(* ω子集的极小元函数 *)
(* 相当于ω上的选择函数 *)

Local Definition F := λ n, {λ N, <N, n> | N ∊ 𝒫 ω - ⎨∅⎬}.
Local Definition P := λ p, π2 p ∈ π1 p ∧ ∀m ∈ π1 p, π2 p ⊆ m.
Local Definition G := λ n, {p ∊ F n | P}.
Definition min := ⋃{G | n ∊ ω}.

Lemma minE : ∀ N n, <N, n> ∈ min →
  N ∈ 𝒫 ω - ⎨∅⎬ ∧ n ∈ N ∧ ∀m ∈ N, n ⊆ m.
Proof.
  intros. apply UnionAx in H as [f [Hf Hp]].
  apply ReplAx in Hf as [m [Hm Heqn]]. subst f.
  apply SepE in Hp as [Hp [Hn Hmin]]. zfcrewrite.
  apply ReplAx in Hp as [M [HM Heqp]].
  apply op_iff in Heqp as []; subst M m. split; auto.
Qed.

Lemma min_maps_into : min: 𝒫 ω - ⎨∅⎬ ⇒ ω.
Proof with auto.
  split; split.
  - intros p Hp.
    apply UnionAx in Hp as [f [Hf Hp]].
    apply ReplAx in Hf as [m [Hm Heqn]]. subst f.
    apply SepE in Hp as [Hp _].
    apply ReplAx in Hp as [N [HN Heqp]]. subst p...
  - intros N HN. split. apply domE in HN...
    intros n1 n2 H1 H2.
    apply minE in H1 as [_ [Hn1 H1]].
    apply minE in H2 as [_ [Hn2 H2]].
    apply H1 in Hn2. apply H2 in Hn1. apply sub_asym...
  - apply ExtAx. intros N. split; intros HN.
    + apply domE in HN as [n Hp].
      apply minE in Hp as []...
    + apply SepE in HN as [HN HN'].
      apply PowerAx in HN as Hsub. apply SingNE in HN' as Hne.
      pose proof (ω_wellOrder N Hne Hsub) as [n [Hn Hmin]].
      eapply domI. apply UnionAx. exists (G n). split.
      * apply ReplAx. exists n. split... apply Hsub...
      * apply SepI. apply ReplAx. exists N. split.
        apply SepI... apply op_iff...
        unfold P. zfcrewrite. split...
        intros m Hm. apply leq_iff_sub.
        apply Hsub... apply Hsub... apply Hmin... 
  - intros n Hn. apply ranE in Hn as [N Hp].
    apply minE in Hp as [HN [Hn _]]. apply SepE in HN as [HN _].
    apply PowerAx in HN. apply HN...
Qed.

Lemma min_correct : ∀ N, ⦿ N → N ⊆ ω →
  min[N] ∈ N ∧ ∀n ∈ N, min[N] ⊆ n.
Proof with auto.
  intros N Hne Hsub.
  destruct min_maps_into as [Hfm [Hdm _]].
  assert (HN: N ∈ dom min). {
    rewrite Hdm. apply SepI. apply PowerAx...
    apply SingNI. apply EmptyNI...
  }
  apply domE in HN as [n Hp].
  apply func_ap in Hp as Hap...
  rewrite Hap. apply minE...
Qed.

Definition 𝒩suc : set → set := λ n, {x ∊ ω | λ x, n ∈ x}.
Definition Suc' : set → set := λ n, min[𝒩suc n].

Definition 𝒩xt : set → set → set := λ N n, {x ∊ N | λ x, n ∈ x}.
Definition Next : set → set → set := λ N n, min[𝒩xt N n].

Definition 𝒩id : set → set → set := λ N n, {x ∊ N | λ x, n ⊆ x}.
Definition Ident' : set → set → set := λ N n, min[𝒩id N n].

(* ω的大于给定自然数n的子集的最小数是n的后继 *)
Lemma min_suc : ∀n ∈ ω, Suc' n = Suc n.
Proof with auto.
  intros n Hn.
  apply ω_inductive in Hn as Hn1.
  specialize (min_correct (𝒩suc n)) as [Hm Hmin].
  - exists n⁺. apply SepI... apply suc_has_n.
  - intros x Hx. apply SepE in Hx as []...
  - apply SepE in Hm as [Hm Hnm].
    destruct (classic (Suc' n = Suc n))... exfalso.
    apply lt_connected in H as []...
    + apply lt_suc_iff_sub in H...
      apply H in Hnm. apply (lt_irrefl n)...
    + apply lt_iff_not_sub in H... apply H.
      apply Hmin. apply SepI... apply suc_has_n.
Qed.

(* 自然数集子集的阿基米德性 *)
Definition archimedean : set → Prop := λ N,
  ∀n ∈ ω, ∃m ∈ N, n ∈ m.

(* ω的具有阿基米德性的非空子集N的大于给定成员n的子集的最小数是在N里n的下一个数 *)
Lemma min_next : ∀ N, ⦿ N → N ⊆ ω → archimedean N →
  ∀n ∈ N, Next N n ∈ N ∧ n ∈ Next N n ∧
    ∀m ∈ 𝒩xt N n, Next N n ⊆ m.
Proof with auto.
  intros N Hne Hsub Harc n Hn.
  apply Hsub in Hn as Hnw.
  specialize (min_correct (𝒩xt N n)) as [Hm Hmin].
  - apply Harc in Hnw as [m [Hm Hnm]].
    exists m. apply SepI...
  - intros x Hx. apply Hsub. apply SepE in Hx as []...
  - apply SepE in Hm as [Hm Hnm]. split...
Qed.

Lemma next_injective : ∀ N, ⦿ N → N ⊆ ω → archimedean N →
  ∀ n m ∈ N, Next N n = Next N m → n = m.
Proof with auto; try congruence.
  intros N Hne Hsub Harc n Hn m Hm Heq.
  apply Hsub in Hn as Hnw. apply Hsub in Hm as Hmw.
  pose proof (min_next N Hne Hsub Harc n Hn) as [_ [Hn1 Hn2]]...
  pose proof (min_next N Hne Hsub Harc m Hm) as [_ [Hm1 Hm2]]...
  destruct (classic (n = m))... exfalso.
  apply lt_connected in H as []...
  - apply (lt_irrefl m)... apply Hn2... apply SepI...
  - apply (lt_irrefl n)... apply Hm2... apply SepI...
Qed.

(* ω的子集的大于等于给定成员n的子集的最小数是n *)
Lemma min_ident : ∀ N, N ⊆ ω → ∀n ∈ N, Ident' N n = n.
Proof with eauto.
  intros N Hsub n Hn.
  specialize (min_correct (𝒩id N n)) as [Hm Hmin]...
  - exists n. apply SepI...
  - intros x Hx. apply Hsub. apply SepE in Hx as []...
  - apply SepE in Hm as [Hm Hnm].
    apply Hsub in Hm as Hmw. apply Hsub in Hn as Hnw.
    destruct (classic (Ident' N n = n))... exfalso.
    apply lt_connected in H as []...
    + apply Hnm in H. eapply lt_irrefl...
    + apply lt_iff_not_sub in H... apply H.
      apply Hmin. apply SepI...
Qed.
