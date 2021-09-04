(** Solutions to "Elements of Set Theory" Chapter 4 **)
(** Coq coding by choukh, May 2020 **)

Require Export ZFC.Elements.EST4_3.

Example ex4_2: ∀ a, trans a → trans a⁺.
Proof with eauto.
  intros a Ht c b Hc Hb. apply BUnionE in Hb as [].
  - apply BUnionI1. eapply Ht...
  - apply BUnionI1. apply SingE in H. subst...
Qed.  

Example ex4_3: ∀ a, trans a ↔ trans 𝒫 a.
Proof with eauto.
  split; intros Ht c b Hc Hb.
  - rewrite PowerAx. intros x Hx. eapply Ht...
    rewrite PowerAx in Hb. apply Hb...
  - apply trans_union_sub in Ht. rewrite ex2_6_a in Ht.
    apply Ht in Hb. rewrite PowerAx in Hb. apply Hb...
Qed.

Example ex4_4: ∀ a, trans a → trans ⋃a.
Proof with eauto.
  intros a Ht c b Hc Hb. apply trans_union_sub in Ht.
  apply Ht in Hb. eapply UnionI...
Qed.

Example ex4_5_a: ∀ 𝒜, (∀A ∈ 𝒜, trans A) → trans ⋃𝒜.
Proof with eauto.
  intros * H a A Ha HA. apply UnionAx in HA as [B [H1 H2]].
  apply H in H1 as Htb.  eapply UnionI...
Qed.

Example ex4_5_b: ∀ 𝒜, (∀A ∈ 𝒜, trans A) → trans ⋂𝒜.
Proof with eauto.
  intros * H a A Ha HA. apply InterE in HA as [Hi HA].
  apply InterI... intros B HB. apply H in HB as Htb.
  apply HA in HB. eapply Htb...
Qed.

Example ex4_6: ∀ a, ⋃a⁺ = a → trans a.
Proof. apply trans_union_suc. Qed.

(* ex4_7 see EST4_1.v Theorem ω_recursion_uniqueness *)

Example ex4_8: ∀ f A h c, injective f → f: A ⇒ A →
  c ∈ A - ran f → h: ω ⇒ A →
  h[∅] = c → (∀n ∈ ω, h[n⁺] = f[h[n]]) →
  injective h.
Proof with eauto; try congruence.
  intros * Hinj [Hff [Hdf Hrf]] Hc [Hfh [Hdh Hrh]] Hh0 Hh1.
  split... intros y Hy. rewrite <- unique_existence.
  split. apply ranE in Hy...
  assert (Hnq0: ∀n ∈ ω, h[n⁺] ≠ c). {
    intros n Hn Heq1. apply Hh1 in Hn as Heq2.
    assert (Heq: f[h[n]] = c) by congruence.
    apply CompE in Hc as [_ Hc]. apply Hc. rewrite <- Heq.
    eapply ap_ran. split... apply Hrh.
    eapply ap_ran... split...
  }
  intros k l Hpk. apply domI in Hpk as Hk. rewrite Hdh in Hk.
  generalize Hpk. generalize dependent l.
  clear Hy Hpk. generalize dependent y.
  ω_induction k; intros y l H1 H2; apply domI in H2 as Hdl;
    apply func_ap in H1; eauto; apply func_ap in H2...
  - rewrite Hdh in Hdl. ω_destruct l... exfalso.
    apply Hh1 in Hp as Heq. eapply Hnq0...
  - rewrite Hdh in Hdl. ω_destruct l... exfalso. apply (Hnq0 m)...
    apply Hh1 in Hm as Heq1. apply Hh1 in Hp as Heq2.
    assert (f[h[l]] = f[h[m]]) by congruence.
    cut (m = l)... eapply IH. apply func_correct...
    cut (h[l] = h[m]). intros Heq.
    rewrite <- Heq. apply func_correct...
    eapply injectiveE; eauto; rewrite Hdf; apply Hrh;
      eapply ranI; apply func_correct...
Qed.

Example ex4_9: ∀ f A B h, f: B ⇒ B → A ⊆ B →
  is_function h → dom h = ω →
  h[∅] = A → (∀n ∈ ω, h[n⁺] = h[n] ∪ f⟦h[n]⟧) →
  let C1 := ⋂{X ∊ 𝒫 B | A ⊆ X ∧ X ⊆ B ∧ f⟦X⟧ ⊆ X} in
  let C2 := ⋃{h[i] | i ∊ ω} in
  C1 = C2.
Proof with neauto; try congruence.
  intros * [Hff [Hdf Hrf]] Hsub Hfh Hdh Hh0 Hh1 C1 C2.
  assert (Hrh: ran h ⊆ 𝒫 B). {
    intros y Hy. rewrite PowerAx. apply ranE in Hy as [n Hp].
    apply domI in Hp as Hn. rewrite Hdh in Hn.
    generalize Hp. clear Hp. generalize dependent y.
    ω_induction n; intros y Hy.
    - apply func_ap in Hy... subst...
    - apply func_ap in Hy... subst y. intros x Hx.
      apply Hh1 in Hm as Heq. rewrite Heq in Hx.
      apply BUnionE in Hx as [].
      + rewrite <- Hdh in Hm. apply func_correct in Hm...
        apply IH in Hm. apply Hm...
      + apply imgE in H as [y [_ Hp]].
        apply ranI in Hp. apply Hrf...
  }
  ext c Hc.
  - (* C1 ⊆ C2 *) apply InterE in Hc as [_ H]. apply H.
    assert (Hsub2: C2 ⊆ B). {
      intros y Hy. apply FUnionE in Hy as [n [Hn Hy]].
      rewrite <- Hdh in Hn. apply func_correct in Hn...
      apply ranI in Hn. apply Hrh in Hn.
      rewrite PowerAx in Hn. apply Hn...
    }
    apply SepI. rewrite PowerAx... split; [|split; auto].
    + (* A ⊆ C2 *) intros x Hx.
      rewrite <- Hh0 in Hx. eapply FUnionI; revgoals...
    + (* f⟦C2⟧ ⊆ C2 *) intros y Hy.
      apply imgE in Hy as [x [Hx Hp]]. apply ranI in Hp as Hr.
      apply func_ap in Hp as Hap... subst y.
      apply FUnionE in Hx as [n [Hn Hx]].
      assert (Hn1: n⁺ ∈ ω) by (apply ω_inductive; auto).
      eapply FUnionI. apply Hn1. apply Hh1 in Hn.
      rewrite Hn. apply BUnionI2. eapply imgI...
  - (* C2 ⊆ C1 *)
    apply FUnionE in Hc as [n [Hn Hc]].
    assert (Hi: ⦿ {X ∊ 𝒫 B | A ⊆ X ∧ X ⊆ B ∧ f⟦X⟧ ⊆ X}). {
      exists B. apply SepI. apply PowerAx... split... split...
      intros x Hx. apply imgE in Hx as [w [_ Hx]].
      apply ranI in Hx. apply Hrf...
    }
    generalize dependent c.
    ω_induction n; intros c Hc; apply InterI...
    + intros y Hy. rewrite Hh0 in Hc.
      apply SepE in Hy as [_ [H _]]. apply H...
    + intros y Hy. apply Hh1 in Hm as Heq. rewrite Heq in Hc.
      apply BUnionE in Hc as [].
      * apply IH in H. apply InterE in H as [_ H]. apply H...
      * apply imgE in H as [w [Hw Hc]].
        apply SepE in Hy as [_ [H1 [H2 H3]]].
        apply H3. eapply imgI... apply IH in Hw.
        apply InterE in Hw as [_ Hy]. apply Hy.
        apply SepI. apply PowerAx... split...
Qed.

Example ex4_13: ∀ m n ∈ ω, m ⋅ n = 0 → m = 0 ∨ n = 0.
Proof. exact mul_eq_0. Qed.

Example ex4_14: ∀n ∈ ω,
  (even n ∨ odd n) ∧ ¬ (even n ∧ odd n).
Proof with eauto; try apply mul_ran; repeat apply ω_inductive; auto.
  intros n Hn. split.
  - ω_induction n.
    + left. exists 0. split... rewrite mul_0_r...
    + destruct IH.
      * right. destruct H as [k [Hk Heq]].
        exists k. split... rewrite Heq, suc...
      * left. destruct H as [k [Hk Heq]].
        exists k⁺. split. apply ω_inductive...
        rewrite Heq, (pred 1), add_suc, add_0_r...
        rewrite suc, suc, mul_suc...
        rewrite (add_comm 2)...
        rewrite (add_assoc (2⋅k))...
        cut (1 + 1 = 2); try congruence...
        rewrite pred, add_suc, add_0_r... apply mul_ran...
  - ω_induction n; intros [[k [Hk Hkeq]] [p [Hp Hpeq]]].
    + rewrite <- suc in Hpeq...
      exfalso. eapply suc_neq_0. rewrite Hpeq...
    + apply IH. split.
      * exists p. split...
        rewrite <- suc in Hpeq... apply suc_injective in Hpeq...
      * ω_destruct k.
        rewrite mul_0_r in Hkeq... exfalso. eapply suc_neq_0...
        exists k. split...
        rewrite pred, mul_suc, add_comm, add_suc in Hkeq...
        apply suc_injective in Hkeq... apply add_ran...
Qed.

(* ex4_15 ex4_16 ex4_17 see EST4_2.v *)

Example ex4_19: ∀ m d ∈ ω, d ≠ 0 →
  ∃ q r ∈ ω, m = (d ⋅ q) + r ∧ r ∈ d.
Proof with neauto.
  intros n Hn.
  ω_induction n; intros d Hd Hnq0.
  - exists 0. split... exists 0. split... split.
    rewrite mul_0_r, add_0_r... apply neq_0_gt_0...
  - apply (IH d Hd) in Hnq0 as [q [Hq [r [Hr [Heq Hrd]]]]]...
    apply suc_preserve_lt in Hrd...
    apply le_iff_lt_suc in Hrd as []; try apply ω_inductive...
    + exists q. split... exists r⁺. split.
      apply ω_inductive... split... rewrite add_suc...
      congruence. apply mul_ran...
    + subst d. exists q⁺. split. apply ω_inductive...
      exists 0. split... split; [|apply suc_has_0; auto].
      rewrite add_0_r, mul_suc, add_comm, add_suc; try apply mul_ran...
      congruence. apply ω_inductive...
Qed.

Example ex4_20: ∀ A, A ≠ ∅ → A ⊆ ω → ⋃A = A → A = ω.
Proof with eauto.
  intros A Hnq0 HA HU. apply ω_ind... split.
  - apply EmptyNE in Hnq0 as [a Ha].
    destruct (classic (a = ∅)). subst a...
    rewrite <- HU. apply UnionAx. exists a. split...
    apply HA in Ha. apply neq_0_gt_0...
  - intros a Ha. apply HA in Ha as Haw. rewrite <- HU in Ha.
    apply UnionAx in Ha as [b [Hb Ha]]. apply HA in Hb as Hbw.
    assert (Ha1: a⁺ ∈ ω) by (apply ω_inductive; auto).
    destruct (classic (b = a⁺)). subst...
    apply nat_connected in H as []...
    + exfalso. apply le_iff_lt_suc in H...
      apply (nat_not_le_gt b Hbw a Haw)...
    + rewrite <- HU. apply UnionAx. exists b. split...
Qed.

Example ex4_21: ¬ ∃ n ∈ ω, ∃ m ∈ n, n ⊆ m.
Proof with eauto.
  intros [n [Hn [m [Hm H]]]].
  assert (Hmw: m ∈ ω) by (eapply ω_trans; eauto).
  ω_destruct n. exfalso0. clear Hn Hp.
  apply H in Hm as Hmm. eapply nat_irrefl...
Qed.

Example ex4_22: ∀ m p ∈ ω, m ∈ m + p⁺.
Proof with eauto.
  intros n Hn.
  ω_induction n; intros k Hk.
  - rewrite add_0_l. apply suc_has_0... apply ω_inductive...
  - rewrite add_suc'... apply (suc_preserve_lt m)...
    apply add_ran... apply ω_inductive... apply ω_inductive...
Qed.

Example ex4_23: ∀ m n ∈ ω, m ∈ n → ∃p ∈ ω, m + p⁺ = n.
Proof with eauto.
  intros k Hk.
  ω_induction k; intros n Hn H.
  - apply neq_0_gt_0 in H... apply pred_exists in H as [n' [Hn' Heq]]...
    exists n'. split... rewrite add_0_l... congruence.
  - ω_destruct n. exfalso0.
    apply suc_preserve_lt in H...
    apply IH in H as [p [Hpw Heq]]...
    exists p. split... rewrite add_suc'... congruence.
    apply ω_inductive...
Qed.

Example ex4_24: ∀ m n p q ∈ ω, m + n = p + q →
  m ∈ p ↔ q ∈ n.
Proof with try apply add_ran; try apply ω_inductive; auto.
  intros m Hm n Hn p Hp q Hq Heq. split; intros.
  - apply ex4_23 in H as [k [Hk Hkeq]]... subst p.
    rewrite add_comm in Heq... rewrite (add_assoc m) in Heq...
    rewrite (add_comm m) in Heq...
    apply add_cancel in Heq... subst n.
    rewrite add_comm... apply ex4_22...
  - apply ex4_23 in H as [k [Hk Hkeq]]... subst n.
    rewrite (add_comm q) in Heq...
    rewrite <- add_assoc in Heq...
    apply add_cancel in Heq... subst p. apply ex4_22...
Qed.

Example ex4_25: ∀ m n p q ∈ ω, n ∈ m → q ∈ p →
  m ⋅ q + n ⋅ p ∈ m ⋅ p + n ⋅ q.
Proof with try apply ω_inductive; auto.
  intros m Hm n Hn p Hp q Hq Hnm Hqp.
  apply ex4_23 in Hqp as [s [Hs Hseq]]... subst p.
  rewrite mul_distr... rewrite mul_distr...
  assert (Hmq: m ⋅ q ∈ ω). { apply mul_ran... }
  assert (Hnq: n ⋅ q ∈ ω). { apply mul_ran... }
  assert (Hns: n ⋅ s⁺ ∈ ω). { apply mul_ran... }
  assert (Hms: m ⋅ s⁺ ∈ ω). { apply mul_ran... }
  rewrite add_comm; revgoals... apply add_ran...
  rewrite (add_assoc (m⋅q))...
  rewrite (add_comm (m⋅q)); revgoals... apply add_ran...
  apply add_preserve_lt... apply add_ran... apply add_ran...
  rewrite add_comm... apply add_preserve_lt...
  apply mul_preserve_lt...
Qed.

Example ex4_26: ∀n ∈ ω, ∀ f, f: n⁺ ⇒ ω →
  ∃m ∈ ran f, ∀k ∈ ran f, k ⋸ m.
Proof with eauto.
  intros n Hn.
  ω_induction n; intros f [Hff [Hfd Hfr]].
  - exists (f[0]). split.
    + eapply ap_ran. split... nauto.
    + intros k Hk. apply ranE in Hk as [x Hp].
      apply domI in Hp as Hx. rewrite Hfd in Hx.
      apply BUnionE in Hx as []. exfalso0.
      apply SingE in H. subst x. apply func_ap in Hp...
  - assert (Hres: f ↾ m⁺: m⁺ ⇒ ω). {
      split. apply restr_func...
      split. ext Hx.
      + apply domE in Hx as [y Hp].
        apply restrE2 in Hp as []...
      + eapply domI. apply restrI... apply func_correct...
        rewrite Hfd. apply BUnionI1...
      + intros y Hy. apply ranE in Hy as [x Hp].
        apply restrE2 in Hp as [Hp _]...
        apply ranI in Hp. apply Hfr in Hp...
    }
    assert (Hreq: ran f = f⟦m⁺⟧ ∪ {f[m⁺],}). {
      ext y Hy.
      - apply ranE in Hy as [x Hp].
        apply domI in Hp as Hd. rewrite Hfd in Hd.
        apply BUnionE in Hd as [].
        + apply BUnionI1. eapply imgI...
        + apply BUnionI2. apply SingE in H. subst x.
          apply func_ap in Hp... subst y...
      - apply BUnionE in Hy as [].
        + apply imgE in H as [x [_ Hp]]. eapply ranI...
        + apply SingE in H. subst y. eapply ranI.
          apply func_correct... rewrite Hfd. apply BUnionI2...
    }
    assert (Hm1: m⁺ ∈ dom f). {
      rewrite Hfd. apply BUnionI2...
    }
    assert (Hfm1: f[m⁺] ∈ ω). {
      eapply ap_ran. split... nauto.
    }
    pose proof (IH _ Hres) as [M [HM IHk]].
    destruct Hres as [_ [_ Hresr]].
    assert (HMw: M ∈ ω) by (apply Hresr; auto).
    destruct (classic (f[m⁺] = M)).
    + exists M. split. eapply ranI.
      apply func_correct in Hm1... rewrite H in Hm1. apply Hm1.
      intros k Hk. rewrite Hreq in Hk.
      apply BUnionE in Hk as []. apply IHk...
      apply SingE in H0. subst k. right...
    + apply nat_connected in H as []...
      * exists M. split. rewrite Hreq. apply BUnionI1...
        intros k Hk. rewrite Hreq in Hk.
        apply BUnionE in Hk as []. apply IHk...
        apply SingE in H0. subst k. left...
      * exists (f[m⁺]). split. eapply ap_ran. split... nauto.
        intros k Hk. rewrite Hreq in Hk.
        apply BUnionE in Hk as []. apply IHk in H0 as []; left.
        eapply nat_trans; revgoals... congruence.
        right. apply SingE in H0...
Qed.

Example ex4_27: ∀ A G f₁ f₂, is_function G →
  f₁: ω ⇒ A → f₂: ω ⇒ A →
  (∀n ∈ ω,
    f₁ ↾ n ∈ dom G ∧ f₂ ↾ n ∈ dom G ∧
    f₁[n] = G[f₁ ↾ n] ∧ f₂[n] = G[f₂ ↾ n]
  ) →
  f₁ = f₂.
Proof with eauto; try congruence.
  intros A G f₁ f₂ HG [Hf₁ [Hf₁d Hf₁r]] [Hf₂ [Hf₂d Hf₂r]] H...
  apply func_ext_intro... intros n Hn. rewrite Hf₁d in Hn.
  pose proof (H n) as [_ [_ [Heq1 Heq2]]]...
  cut (f₁ ↾ n = f₂ ↾ n)... clear Heq1 Heq2.
  ω_induction n.
  - ext Hx.
    + apply restrE1 in Hx as [a [_ [Ha _]]]. exfalso0.
    + apply restrE1 in Hx as [a [_ [Ha _]]]. exfalso0.
  - assert (Heq1: f₁ ↾ m⁺ = (f₁ ↾ m) ∪ (f₁ ↾ {m,})) by apply ex3_22_c.
    assert (Heq2: f₂ ↾ m⁺ = (f₂ ↾ m) ∪ (f₂ ↾ {m,})) by apply ex3_22_c.
    cut (f₁ ↾ {m,} = f₂ ↾ {m,})... clear Heq1 Heq2.
    pose proof (H m) as [_ [_ [Heq1 Heq2]]]...
    assert (Heq3: f₁[m] = f₂[m]) by congruence.
    ext Hx.
    + apply restrE1 in Hx as [a [b [Ha [Hq Heq]]]].
      apply SingE in Ha. apply func_ap in Hq... subst a b x.
      apply restrI... rewrite Heq3.
      apply func_correct...
    + apply restrE1 in Hx as [a [b [Ha [Hq Heq]]]].
      apply SingE in Ha. apply func_ap in Hq... subst a b x.
      apply restrI... rewrite <- Heq3.
      apply func_correct...
Qed.

Ltac ω_strong_induction C := cut (C = 0); [
  intros ?H0; eapply EmptyE in H0; apply H0;
  apply SepI; eauto |
  apply ω_ind_strong_0; [
    intros ?c ?Hc; apply SepE in Hc as []; auto |
    intros ?c ?Hc; apply SepE in Hc as [?Hc ?IH]
  ]
].

Example ex4_28: trans ω.
Proof with auto.
  apply trans_sub. intros n Hn.
  contra.
  set {n ∊ ω | n ⊈ ω} as C.
  ω_strong_induction C.
  ω_destruct c.
  - exfalso. apply IH. intros x Hx. exfalso0.
  - exists c. split; revgoals. apply BUnionI2...
    apply SepI... intros Hsub. apply IH.
    intros x Hx. apply BUnionE in Hx as [].
    apply Hsub... apply SingE in H0. subst...
Qed.

Example ex4_32: ∀n ∈ ω, ⋃{n,}⁺ = n⁺.
Proof with nauto.
  intros n Hn.
  ext Hx.
  - apply UnionAx in Hx as [y [Hy Hx]].
    apply BUnionE in Hy as []; apply SingE in H; subst.
    apply BUnionI1... apply BUnionI2...
  - apply BUnionE in Hx as []; apply UnionAx.
    + exists n. split... apply BUnionI1...
    + exists {n,}. split...
Qed.

Definition count : set → set → Prop := λ S n,
  n ∈ ω ∧ ∃ f, f: n ⟺ S.

Lemma ex4_37_0: ∀ x m n ∈ ω, x ∈ m + n⁺ → x ∉ m →
  ∃b ∈ n⁺, x = m + b.
Proof with eauto.
  intros n Hn a Ha b Hb.
  ω_induction n; intros Hnab Hna.
  - ω_destruct a.
    + exists 0. split. apply suc_has_0... rewrite add_0_r...
    + exfalso. apply Hna. apply suc_has_0...
  - destruct (classic (m⁺ = a)).
    exists 0. split. apply suc_has_0... rewrite add_0_r...
    apply nat_connected in H as []; try apply ω_inductive...
    exfalso. apply Hna...
    assert (Hma: m ∉ a). {
      intros Hma. apply BUnionE in H as [].
      eapply nat_not_lt_gt; revgoals...
      apply SingE in H. eapply nat_not_lt_self; revgoals...
    }
    apply IH in Hma as [c [Hc Heq]]; revgoals.
    eapply nat_trans; revgoals. apply Hnab. apply BUnionI2...
    apply add_ran... apply ω_inductive...
    assert (Hcw: c ∈ ω). {
      eapply ω_trans. apply Hc. apply ω_inductive...
    }
    destruct (classic (c = b)). exfalso.
    rewrite <- H0, add_suc in Hnab...
    apply suc_preserve_lt in Hnab; try apply add_ran...
    eapply nat_irrefl. apply Hm. rewrite <- Heq in Hnab...
    apply nat_connected in H0 as []; revgoals... exfalso.
    apply le_iff_lt_suc in Hc... eapply nat_not_le_gt; revgoals...
    exists c⁺. split; revgoals. rewrite add_suc... congruence.
    apply suc_preserve_lt in H0...
Qed.

Example ex4_37_a: ∀ A B m n,
  count A m → count B n → disjoint A B →
  count (A ∪ B) (m + n).
Proof with eauto; try congruence.
  intros * [Hm [f [[Hff Hfs] [Hfd Hfr]]]]
           [Hn [g [[Hgf Hgs] [Hgd Hgr]]]] Hdj.
  split. apply add_ran...
  set (Rel (m + n) (A ∪ B) (λ a y,
    (a ∈ m ∧ y = f[a]) ∨
    (∃b ∈ n, a = m + b ∧ y = g[b])
  )) as h.
  assert (Hhf: is_function h). {
    split. apply rel_is_rel.
    intros x Hx. rewrite <- unique_existence.
    split. apply domE in Hx...
    intros y1 y2 H1 H2.
    apply SepE in H1 as [Hp [[Hxm1 H1]|[b1 [Hb1 [H11 H12]]]]];
    apply SepE in H2 as [_  [[Hxm2 H2]|[b2 [Hb2 [H21 H22]]]]];
    apply CPrdE2 in Hp as [Hxmn _]; zfc_simple.
    - rewrite H21 in Hxm1. exfalso.
      assert (Hbw: b2 ∈ ω) by (eapply ω_trans; eauto).
      eapply (le_iff_not_gt m Hm (m + b2))...
      apply add_ran... eapply add_enlarge_le...
    - rewrite H11 in Hxm2. exfalso.
      assert (Hbw: b1 ∈ ω) by (eapply ω_trans; eauto).
      eapply (le_iff_not_gt m Hm (m + b1))...
      apply add_ran... eapply add_enlarge_le...
    - assert (Hbw1: b1 ∈ ω) by (eapply ω_trans; eauto).
      assert (Hbw2: b2 ∈ ω) by (eapply ω_trans; eauto).
      rewrite add_comm in H11, H21... rewrite H11 in H21.
      apply add_cancel in H21...
  }
  exists h. split; split...
  - (* single_rooted h *)
    intros y Hy. rewrite <- unique_existence.
    split. apply ranE in Hy...
    intros x1 x2 H1 H2.
    apply SepE in H1 as [Hp1 [[Hxm1 H1]|[b1 [Hb1 [H11 H12]]]]];
    apply SepE in H2 as [Hp2 [[Hxm2 H2]|[b2 [Hb2 [H21 H22]]]]];
    apply CPrdE2 in Hp1 as [Hxmn1 _];
    apply CPrdE2 in Hp2 as [Hxmn2 _]; zfc_simple.
    + rewrite <- Hfd in Hxm1, Hxm2.
      eapply injectiveE; revgoals... split...
    + exfalso. rewrite <- Hfd in Hxm1. rewrite <- Hgd in Hb2.
      apply func_correct in Hxm1... apply ranI in Hxm1.
      apply func_correct in Hb2... apply ranI in Hb2.
      rewrite Hfr in Hxm1. rewrite Hgr in Hb2.
      eapply (disjointE A B)...
    + exfalso. rewrite <- Hfd in Hxm2. rewrite <- Hgd in Hb1.
      apply func_correct in Hxm2... apply ranI in Hxm2.
      apply func_correct in Hb1... apply ranI in Hb1.
      rewrite Hfr in Hxm2. rewrite Hgr in Hb1.
      eapply (disjointE A B)...
    + cut (b1 = b2)... rewrite <- Hgd in Hb1, Hb2.
      eapply injectiveE; revgoals... split...
  - ext Hx.
    (* dom h ⊆ m + n *)
    apply domE in Hx as [y Hp]. apply SepE in Hp as [Hp _].
    apply CPrdE2 in Hp as []...
    (* dom h ⊇ m + n *)
    destruct (classic (x ∈ m)) as [Hxm|Hxm].
    + assert (Hxd := Hxm). rewrite <- Hfd in Hxd.
      apply domE in Hxd as [y Hp].
      eapply domI. apply SepI; zfc_simple.
      * apply CPrdI... apply BUnionI1.
        rewrite <- Hfr. eapply ranI. apply Hp.
      * left. split... apply func_ap in Hp...
    + assert (Hxmn := Hx). ω_destruct n.
      rewrite H, add_0_r in Hx...
      rewrite Heq in Hx.
      eapply ex4_37_0 in Hx as [b [Hb Hx]]; revgoals...
      eapply ω_trans... apply add_ran...
      assert (Hbw: b ∈ ω). {
        eapply ω_trans. apply Hb. apply ω_inductive...
      }
      assert (b ∈ n⁺)... rewrite <- Heq in Hb. clear Hp.
      apply domE in Hb as [c Hp].
      eapply domI. apply SepI; zfc_simple.
      * apply CPrdI... apply BUnionI2.
        rewrite <- Hgr. eapply ranI...
      * right. exists b. split... split... apply func_ap in Hp...
  - ext y Hy.
    (* ran h ⊆ A ∪ B *)
    apply ranE in Hy as [x Hp]. apply SepE in Hp as [Hp _].
    apply CPrdE2 in Hp as []...
    (* ran h ⊇ A ∪ B *)
    assert (Hy' := Hy). apply BUnionE in Hy' as [].
    + rewrite <- Hfr in H. apply ranE in H as [x Hp].
      eapply ranI. apply SepI; zfc_simple.
      * apply CPrdI... apply domI in Hp.
        rewrite Hfd in Hp. apply add_enlarge_lt...
      * left. split. apply domI in Hp... apply func_ap in Hp...
    + rewrite <- Hgr in H. apply ranE in H as [b Hp].
      apply domI in Hp as Hd. rewrite Hgd in Hd.
      assert (Hbw: b ∈ ω) by (eapply ω_trans; eauto).
      eapply ranI. apply SepI; zfc_simple.
      * apply CPrdI... rewrite add_comm...
        apply add_preserve_lt; revgoals...
      * right. exists b. split... split.
        rewrite add_comm... apply func_ap in Hp...
Qed.

Lemma ex4_37_1: ∀ m i1 i2 j1 j2 ∈ ω,
  m ⋅ j1 + i1 = m ⋅ j2 + i2 →
  i1 ∈ m → i2 ∈ m → j1 = j2.
Proof with eauto; try congruence.
  intros n Hn i1 Hi1 i2 Hi2 j1 Hj1 j2 Hj2.
  generalize dependent j2.
  ω_induction j1; intros j2 Hj2 Heq Hlt1 Hlt2.
  - ω_destruct j2... exfalso.
    rewrite mul_0_r, add_0_l in Heq... rewrite Heq in Hlt1.
    apply add_shrink_lt in Hlt1; try apply mul_ran...
    eapply nat_not_le_gt; revgoals. apply Hlt1.
    apply mul_enlarge_le...
    apply mul_ran... apply Hn.
  - ω_destruct j2.
    + exfalso. rewrite mul_0_r, add_0_l in Heq...
      rewrite <- Heq in Hlt2.
      apply add_shrink_lt in Hlt2;
        try apply mul_ran; try apply ω_inductive...
      eapply nat_not_le_gt; revgoals. apply Hlt2.
      apply mul_enlarge_le...
      apply mul_ran... apply ω_inductive... apply Hn.
    + cut (m = j2)... eapply IH...
      do 2 rewrite mul_suc in Heq...
      do 2 rewrite add_assoc in Heq; try apply mul_ran...
      rewrite add_comm, (add_comm n) in Heq;
        try apply add_ran; try apply mul_ran...
      apply add_cancel in Heq;
        try apply add_ran; try apply mul_ran...
Qed.

Lemma ex4_37_2_0 : ∀ a b ∈ ω, ∀x ∈ a + b,
  a ⋸ x → ∃c ∈ b, x = a + c.
Proof with neauto.
  intros a Ha b Hb.
  ω_induction b; intros x Hx Hlt.
  - exfalso. rewrite add_0_r in Hx...
    eapply nat_not_le_gt; revgoals... eapply ω_trans...
  - assert (Hxw: x ∈ ω). {
      eapply ω_trans. apply Hx.
      apply add_ran... apply ω_inductive...
    }
    rewrite add_suc in Hx...
    apply le_iff_lt_suc in Hx as []; try apply add_ran...
    apply IH in Hlt as [c [Hc Heq]]...
    exists c. split... apply BUnionI1...
Qed.

Lemma ex4_37_2: ∀ m n ∈ ω, ∀x ∈ m ⋅ n,
  ∃i ∈ m, ∃j ∈ n, x = m ⋅ j + i.
Proof with eauto.
  intros k Hk n Hn.
  ω_induction n; intros x Hx.
  - rewrite mul_0_r in Hx... exfalso0.
  - assert (Hxw: x ∈ ω). {
      eapply ω_trans... apply mul_ran...
      apply ω_inductive...
    }
    rewrite mul_suc in Hx; try apply mul_ran...
    destruct (classic (x ∈ k)).
    exists x. split... exists 0. split.
    apply suc_has_0... rewrite mul_0_r, add_0_l...
    apply le_iff_not_gt in H...
    apply ex4_37_2_0 in Hx as [c [Hc Hx]]; try apply mul_ran...
    apply IH in Hc as [i [Hi [j [Hj Hc]]]]. subst c.
    assert (Hiw: i ∈ ω) by (eapply ω_trans; eauto).
    assert (Hjw: j ∈ ω) by (eapply ω_trans; eauto).
    rewrite <- add_assoc, <- mul_suc in Hx; try apply mul_ran...
    exists i. split... exists j⁺. split...
    apply suc_preserve_lt in Hj; try apply ω_inductive...
Qed.

Lemma ex4_37_3: ∀ m n ∈ ω, ∀i ∈ m, ∀j ∈ n, 
  m ⋅ j + i ∈ m ⋅ n.
Proof with auto.
  intros k Hk n Hn i Hi.
  ω_induction n; intros j Hj. exfalso0.
  assert (Hiw: i ∈ ω) by (eapply ω_trans; eauto).
  assert (Hjw: j ∈ ω). {
    eapply ω_trans; eauto. apply ω_inductive...
  }
  rewrite mul_suc, (add_comm k); revgoals...
  apply mul_ran...
  apply le_iff_lt_suc in Hj as []...
  - apply IH in H. eapply add_enlarge_lt...
    apply mul_ran...
  - subst. rewrite add_comm, (add_comm (k⋅m))...
    apply add_preserve_lt... apply mul_ran...
    apply mul_ran... apply mul_ran...
Qed.

Example ex4_37_b: ∀ A B m n,
  count A m → count B n → disjoint A B →
  count (A × B) (m ⋅ n).
Proof with eauto; try congruence.
intros * [Hm [f [[Hff Hfs] [Hfd Hfr]]]]
         [Hn [g [[Hgf Hgs] [Hgd Hgr]]]] Hdj.
  split. apply mul_ran...
  set (Rel (m ⋅ n) (A × B) (λ x y,
    let u := π1 y in let v := π2 y in
    ∃i ∈ m, ∃j ∈ n, u = f[i] ∧ v = g[j] ∧
    x = m ⋅ j + i
  )) as h.
  assert (Hhf: is_function h). {
    split. apply rel_is_rel.
    intros x Hx. rewrite <- unique_existence.
    split. apply domE in Hx...
    intros y1 y2 H1 H2.
    apply SepE in H1 as
      [Hp1 [i1 [Hi1 [j1 [Hj1 [Hf1 [Hg1 Heq1]]]]]]].
    apply SepE in H2 as
      [Hp2 [i2 [Hi2 [j2 [Hj2 [Hf2 [Hg2 Heq2]]]]]]].
    apply CPrdE2 in Hp1 as [Hxmn Hy1].
    apply CPrdE2 in Hp2 as [_ Hy2].
    apply CPrdE1 in Hy1 as [u1 [Hu1 [v1 [Hv1 Hy1]]]].
    apply CPrdE1 in Hy2 as [u2 [Hu2 [v2 [Hv2 Hy2]]]].
    rewrite Hy1 in Hf1, Hg1. rewrite Hy2 in Hf2, Hg2.
    zfc_simple. rewrite Heq1 in Heq2.
    assert (Hi1w: i1 ∈ ω) by (eapply ω_trans; eauto).
    assert (Hi2w: i2 ∈ ω) by (eapply ω_trans; eauto).
    assert (Hj1w: j1 ∈ ω) by (eapply ω_trans; eauto).
    assert (Hj2w: j2 ∈ ω) by (eapply ω_trans; eauto).
    assert (j1 = j2) by (eapply ex4_37_1; swap 1 6; eauto).
    rewrite H, add_comm, (add_comm (m⋅j2)) in Heq2;
      try apply mul_ran... cut (i1 = i2)...
    eapply add_cancel; revgoals... apply mul_ran...
  }
  exists h. split; split...
  - (* single_rooted h *)
    intros y Hy. rewrite <- unique_existence.
    split. apply ranE in Hy...
    intros x1 x2 H1 H2.
    apply SepE in H1 as
      [Hp1 [i1 [Hi1 [j1 [Hj1 [Hf1 [Hg1 Heq1]]]]]]].
    apply SepE in H2 as
      [Hp2 [i2 [Hi2 [j2 [Hj2 [Hf2 [Hg2 Heq2]]]]]]].
    apply CPrdE2 in Hp1 as [Hxmn1 Hy1].
    apply CPrdE2 in Hp2 as [Hxmn2 Hy2].
    apply CPrdE1 in Hy1 as [u1 [Hu1 [v1 [Hv1 Hy1]]]].
    apply CPrdE1 in Hy2 as [u2 [Hu2 [v2 [Hv2 Hy2]]]].
    rewrite Hy1 in Hf1, Hg1. rewrite Hy2 in Hf2, Hg2.
    zfc_simple. rewrite Hy1 in Hy2.
    apply op_iff in Hy2 as [Hequ Heqv].
    assert (Heqfi: f[i1] = f[i2]) by congruence.
    assert (Heqfj: g[j1] = g[j2]) by congruence.
    apply injectiveE in Heqfi; revgoals... split...
    apply injectiveE in Heqfj; revgoals... split...
  - ext Hx.
    (* dom h ⊆ m ⋅ n *)
    apply domE in Hx as [y Hp]. apply SepE in Hp as [Hp _].
    apply CPrdE2 in Hp as []...
    (* dom h ⊇ m ⋅ n *)
    assert (Hxmn := Hx).
    apply ex4_37_2 in Hx as [i [Hi [j [Hj Heq]]]]...
    assert (Hid := Hi). assert (Hjd := Hj).
    rewrite <- Hfd in Hid. apply domE in Hid as [yf Hpf].
    rewrite <- Hgd in Hjd. apply domE in Hjd as [yg Hpg].
    eapply domI. apply SepI; zfc_simple.
    apply CPrdI... apply CPrdI.
    rewrite <- Hfr. eapply ranI...
    rewrite <- Hgr. eapply ranI... zfc_simple.
    exists i. split... exists j. split...
    apply func_ap in Hpf... apply func_ap in Hpg...
  - ext y Hy.
    (* ran h ⊆ A ∪ B *)
    apply ranE in Hy as [x Hp]. apply SepE in Hp as [Hp _].
    apply CPrdE2 in Hp as []...
    (* ran h ⊇ A ∪ B *)
    assert (Hy' := Hy).
    apply CPrdE1 in Hy' as [u [Hu [v [Hv H]]]]. subst y.
    rewrite <- Hfr in Hu. apply ranE in Hu as [i Hpf].
    rewrite <- Hgr in Hv. apply ranE in Hv as [j Hpg].
    apply domI in Hpf as Hi. rewrite Hfd in Hi.
    apply domI in Hpg as Hj. rewrite Hgd in Hj.
    eapply ranI. apply SepI; zfc_simple.
    apply CPrdI... apply ex4_37_3...
    exists i. split... exists j. split...
    apply func_ap in Hpf... apply func_ap in Hpg...
Qed.
