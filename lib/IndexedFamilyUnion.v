(** Coq coding by choukh, Aug 2020 **)

Require Import ZFC.lib.Natural.

(* 以ω为指标集的集族的并 *)
Definition IFUnion : (nat → set) → set := λ F,
  ⋃{(λ n, F (Proj n)) | n ∊ ω}.
Notation "'⋃ᵢ' F" := (IFUnion F) (at level 9, right associativity).

Lemma IFUnionI : ∀ F : nat → set, ∀ n : nat, F n ⊆ ⋃ᵢ F.
Proof.
  intros * x Hx. eapply FUnionI. apply (embed_ran n).
  rewrite embed_proj_id. apply Hx.
Qed.

Lemma IFUnionE : ∀ F : nat → set, ∀x ∈ ⋃ᵢ F, ∃ n, x ∈ F n.
Proof.
  intros F x Hx. apply FUnionE in Hx as [n [Hn H]].
  exists (Proj n). apply H.
Qed.
