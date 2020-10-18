(** Coq coding by choukh, Aug 2020 **)

Require Export ZFC.EX4.

Lemma injective_recursion : ∀ f A a, f: A ⇔ A → a ∈ A - ran f →
  ∃ h, h: ω ⇔ A ∧ h[∅] = a ∧ ∀n ∈ ω, h[n⁺] = f[h[n]].
Proof with eauto.
  intros f A a Hf Ha.
  apply injection_is_func in Hf as [Hf Hi].
  assert (Ha' := Ha). apply SepE in Ha' as [Ha' _].
  pose proof (ω_recursion_0 f A a Hf Ha') as [h [Hh [Hh0 Hhn]]].
  exists h. split... apply injection_is_func.
  split... eapply ex4_8...
Qed.
