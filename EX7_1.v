(** Solutions to "Elements of Set Theory" Chapter 7 Part 1 **)
(** Coq coding by choukh, Nov 2020 **)

Require Export ZFC.EST7_2.
Require Import ZFC.lib.Real.
Require Import ZFC.lib.Cardinal.

(* ex7_1
  (a) No (b) No
    let < be divisibility
    let A = {2, 3, 6}
    let B = {3, 3, 6}
*)
(* ex7_2 see EST7_1 Fact inv_partialOrder *)
(* ex7_3 Combination (n, 2) = n! / 2!(n - 2)! = (1/2)n(n-1) *)
(* ex7_4 skip *)

(* ==需要选择公理== *)
Example ex7_5 : AC_I → ∀ A R f, wellOrder R A → f: A ⇒ A →
  (∀ x y ∈ A, <x, y> ∈ R → <f[x], f[y]> ∈ R) →
  ∀x ∈ A, <x, f[x]> ∈ R ∨ x = f[x].
Proof with eauto; try congruence.
  intros AC1 * Hwo Hf Hord x Hxa.
  assert (H := Hwo). destruct H as [Hlo _].
  assert (Hfx: f[x] ∈ A) by (eapply ap_ran; eauto).
  destruct (classic (x = f[x])) as [|Hnq]...
  eapply linearOrder_connected in Hnq as [|Hfxx]... exfalso.
  eapply woset_iff_no_descending_chain...
  pose proof (ω_recursion f A x Hf Hxa) as [h [Hh [Hh0 Hhn]]].
  exists h. split... intros n Hn. rewrite Hhn...
  set {n ∊ ω | λ n, <f[h[n]], h[n]> ∈ R} as N.
  ω_induction N Hn... rewrite Hhn... apply Hord...
  eapply ap_ran... eapply ap_ran... eapply ap_ran...
Qed.

(* 对实数的任意子集，如果它按小于关系是良序集，那么它是可数的 *)
Example ex7_6 : ∀ A, A ⊆ ℝ → woset A RealLt → countable A.
Proof with auto.
Admitted.
