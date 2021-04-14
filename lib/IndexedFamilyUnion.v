(** Coq coding by choukh, Aug 2020 **)

Require Import ZFC.lib.Natural.

(* 以ω为指标集的集族的并 *)
Definition IFUnion : (set → set) → set :=
  λ F, ⋃{F | n ∊ ω}.
Notation "'⋃ᵢ' F" := (IFUnion F)
  (at level 9, right associativity).

Lemma IFUnionI : ∀ F : set → set, ∀n ∈ ω, F n ⊆ ⋃ᵢ F.
Proof.
  intros * n Hn. apply FUnionI. apply Hn.
Qed.

Lemma IFUnionE : ∀ F : set → set, ∀x ∈ ⋃ᵢ F, ∃n ∈ ω, x ∈ F n.
Proof.
  intros F x Hx. apply FUnionE in Hx as [n [Hn H]].
  exists n. split; auto.
Qed.

Lemma nat_IFUnionI : ∀ F : nat → set, ∀ n : nat, F n ⊆ ⋃ᵢ F.
Proof.
  intros * x Hx. eapply FUnionI. apply (embed_ran n).
  rewrite proj_embed_id. apply Hx.
Qed.

Lemma nat_IFUnionE : ∀ F : nat → set, ∀x ∈ ⋃ᵢ F, ∃ n, x ∈ F n.
Proof.
  intros F x Hx. apply FUnionE in Hx as [n [Hn H]].
  exists n. apply H.
Qed.
