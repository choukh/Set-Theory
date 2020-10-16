(** Coq coding by choukh, Oct 2020 **)

Require Import ZFC.lib.Natural.

(* 自然数子集的极小元函数 *)

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
