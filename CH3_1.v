(** Solutions to "Elements of Set Theory" Chapter 3 Part 1 **)
(** Coq coding by choukh, May 2020 **)

Require Export ZFC.CH2.

Example ch3_2_a: ∀ A B C, A × (B ∪ C) = (A × B) ∪ (A × C).
Proof.
  intros. apply ExtAx. split; intros.
  - apply CProd_correct in H as [a [Ha [b [Hb H]]]].
    apply BUnionE in Hb as [].
    + apply BUnionI1. subst x. apply CProdI; assumption.
    + apply BUnionI2. subst x. apply CProdI; assumption.
  - apply BUnionE in H as [];
      apply CProd_correct in H as [a [Ha [b [Hb H]]]];
      subst x; apply CProdI; try apply Ha.
    + apply BUnionI1. apply Hb.
    + apply BUnionI2. apply Hb.
Qed.

Example ch3_2_b: ∀ A B C, ⦿ A → A × B = A × C → B = C.
Proof.
  intros A B C [a Ha] H. apply ExtAx. split; intros.
  - assert (<a, x> ∈ A × B) by (apply CProdI; assumption).
    rewrite H in H1. rewrite CProd_correct in H1.
    destruct H1 as [a' [Ha' [c [Hc Heq]]]].
    apply op_correct in Heq as []. subst. apply Hc.
  - assert (<a, x> ∈ A × C) by (apply CProdI; assumption).
    rewrite <- H in H1. rewrite CProd_correct in H1.
    destruct H1 as [a' [Ha' [b [Hb Heq]]]].
    apply op_correct in Heq as []. subst. apply Hb.
Qed.

Example ch3_3: ∀ A ℬ, A × ⋃ℬ = ⋃{λ X, A × X | X ∊ ℬ}.
Proof.
  intros. apply ExtAx. split; intros.
  - apply CProd_correct in H as [a [Ha [b [Hb Heq]]]].
    apply UnionAx in Hb as [B [HB Hb]]. subst x.
    eapply FUnionI. apply HB. apply CProdI; assumption.
  - apply FUnionE in H as [B [HB Hx]].
    apply CProd_correct in Hx as [a [Ha [b [Hb Heq]]]]. subst x.
    apply CProdI. apply Ha. apply UnionAx.
    exists B. split. apply HB. apply Hb.
Qed.

(* 没有循环三链 *)
Lemma well_founded_3 : ∀ X Y Z, X ∈ Y → Y ∈ Z → Z ∉ X.
Proof.
  intros X Y Z H. pose proof (ε_ind (λ X, ∀ Y Z, X ∈ Y → Y ∈ Z → Z ∉ X)).
  apply H0; [|apply H]. clear X Y Z H H0. unfoldq.
  intros X H Y Z H1 H2 H3.
  pose proof (H Z H3 X Y H3 H1). auto.
Qed.

Example ch3_4: ¬ ∃ S, ∀ a b, <a, b> ∈ S.
Proof.
  intros [S H]. specialize H with S S.
  assert (<S, S> = ⎨⎨S⎬⎬). {
    apply ExtAx. split; intros.
    apply PairE in H0 as []; subst x; apply SingI. apply H0.
  }
  rewrite H0 in H.
  apply (well_founded_3 S ⎨S⎬ ⎨⎨S⎬⎬); try apply SingI. apply H.
Qed.

Example ch3_5_b: ∀ A B, A × B = ⋃{λ x, ⎨x⎬ × B | x ∊ A}.
Proof.
  intros. apply ExtAx. split; intros.
  - apply CProd_correct in H as [a [Ha [b [Hb Heq]]]].
    eapply FUnionI. apply Ha. subst x.
    apply CProdI. apply SingI. apply Hb.
  - apply FUnionE in H as [a [Ha Hx]].
    apply CProd_correct in Hx as [a' [Ha' [b [Hb Heq]]]].
    apply SingE in Ha'. subst a. subst x.
    apply CProdI; assumption.
Qed.

Example ch3_6: ∀ X, is_relation X ↔ X ⊆ dom X × ran X.
Proof.
  intros X. split.
  - intros Hr. unfold Sub. intros x Hx. assert (Heq := Hx).
    apply relE in Heq. rewrite Heq. rewrite Heq in Hx. apply CProdI.
    + eapply domI. apply Hx.
    + eapply ranI. apply Hx.
    + apply Hr.
  - unfold is_relation. intros Hsub x Hx. apply Hsub in Hx.
    apply CProd_correct in Hx as [a [Ha [b [Hb Heq]]]].
    exists a, b. apply Heq.
Qed.

Example ch3_7: ∀ R, is_relation R → fld R = ⋃⋃R.
Proof.
  intros. apply ExtAx. split; intros.
  - apply BUnionE in H0 as [].
    + apply SepE in H0 as [Hx _]. apply Hx.
    + apply SepE in H0 as [Hx _]. apply Hx.
  - apply UnionAx in H0 as [p [Hp Hxp]].
    apply UnionAx in Hp as [q [Hq Hpq]].
    destruct (H q Hq) as [a [b Heq]].
    subst q. apply PairE in Hpq as []; subst p.
    + apply SingE in Hxp. subst x.
      apply BUnionI1. eapply domI. apply Hq.
    + apply PairE in Hxp as []; subst x.
      * apply BUnionI1. eapply domI. apply Hq.
      * apply BUnionI2. eapply ranI. apply Hq.
Qed.

Example ch3_8_a: ∀ 𝒜, dom ⋃𝒜 = ⋃{λ R, dom R | R ∊ 𝒜}.
Proof.
  intros. apply ExtAx. split; intros.
  - apply domE in H as [y Hxy].
    apply UnionAx in Hxy as [A [HA Hxy]].
    eapply FUnionI. apply HA. eapply domI. apply Hxy.
  - apply FUnionE in H as [A [HA Hx]].
    apply domE in Hx as [y Hxy]. eapply domI.
    apply UnionAx. exists A. split; eassumption.
Qed.

Example ch3_8_b: ∀ 𝒜, ran ⋃𝒜 = ⋃{λ R, ran R | R ∊ 𝒜}.
Proof.
  intros. apply ExtAx. split; intros.
  - apply ranE in H as [y Hxy].
    apply UnionAx in Hxy as [A [HA Hxy]].
    eapply FUnionI. apply HA. eapply ranI. apply Hxy.
  - apply FUnionE in H as [A [HA Hx]].
    apply ranE in Hx as [y Hxy]. eapply ranI.
    apply UnionAx. exists A. split; eassumption.
Qed.

Example ch3_9_a: ∀ 𝒜, dom ⋂𝒜 ⊆ ⋂{λ R, dom R | R ∊ 𝒜}.
Proof.
  unfold Sub. introq.
  apply domE in H as [y Hxy].
  apply InterE in Hxy as [[A HA] Hxy]. apply InterI.
  exists (dom A). apply ReplI. apply HA.
  intros B HB. apply ReplE in HB as [C [HC Heq]].
  subst B. eapply domI. apply Hxy in HC. apply HC.
Qed.

Example ch3_9_b: ∀ 𝒜, ran ⋂𝒜 ⊆ ⋂{λ R, ran R | R ∊ 𝒜}.
Proof.
  unfold Sub. introq.
  apply ranE in H as [y Hxy].
  apply InterE in Hxy as [[A HA] Hxy]. apply InterI.
  exists (ran A). apply ReplI. apply HA.
  intros B HB. apply ReplE in HB as [C [HC Heq]].
  subst B. eapply ranI. apply Hxy in HC. apply HC.
Qed.

Example ex_3_10_3: ∀ a b c d,
  <<<a, b>, c>, d> = <<a, b>, c, d>.
Proof. reflexivity. Qed.

Example ex_3_10_2: ∀ a b c d,
  <<<a, b>, c>, d> = <<a, b, c>, d>.
Proof. reflexivity. Qed.

Example ex_3_10_1: ∀ a b c d,
  <<<a, b>, c>, d> = <a, b, c, d>.
Proof. reflexivity. Qed.

Example ch3_11: ∀ F G,
  is_function F → is_function G → dom F = dom G
  → (∀x ∈ dom F, F[x] = G[x]) → F = G.
Proof. exact func_ext. Qed.

Example ch3_12: ∀ f g,
  is_function f → is_function g →
  f ⊆ g ↔ dom f ⊆ dom g ∧ ∀x ∈ dom f, f[x] = g[x].
Proof with eauto.
  intros f g Hf Hg. split.
  - intros H. split; intros x Hx; apply domE in Hx as [y Hp].
    + apply H in Hp. eapply domI...
    + assert (Hp' := Hp). apply H in Hp'.
      apply apI in Hp... apply apI in Hp'... subst...
  - intros [Hsub H] p Hdf. apply funcE1 in Hdf as Heq...
    rewrite Heq in Hdf. apply apI in Hdf as Hapf... 
    apply domI in Hdf. apply Hsub in Hdf as Hdg.
    apply funcDomE2 in Hdf as Hpf... apply funcDomE2 in Hdg as Hpg...
    apply H in Hdf as Hapeq. congruence.
Qed.

Example ch3_13: ∀ f g,
  is_function f → is_function g → f ⊆ g → dom g ⊆ dom f → f = g.
Proof with eauto.
  intros f g Hf Hg Hs Hds. apply func_ext...
  - apply sub_asym... intros x Hx. apply domE in Hx as [y Hp].
    apply Hs in Hp. eapply domI...
  - intros x Hx. apply domE in Hx as [y Hp].
    apply apI in Hp as Heqf... apply Hs in Hp.
    apply apI in Hp as Heqg... subst...
Qed.

Example ch3_14_a:  ∀ f g,
  is_function f → is_function g → is_function (f ∩ g).
Proof with eauto.
  intros * Hf Hg. repeat split.
  - intros x Hx. apply BInterE in Hx as [Hx _].
    apply funcE1 in Hx... exists (π1 x), (π2 x)...
  - apply domE in H...
  - intros y y' Hy Hy'. apply BInterE in Hy as [Hy _].
    apply BInterE in Hy' as [Hy' _]. clear Hg. eapply funcE2...
Qed.

Example ch3_14_b:  ∀ f g,
  is_function f → is_function g →
  (∀x ∈ dom f ∩ dom g, f[x] = g[x]) ↔ is_function (f ∪ g).
Proof with eauto.
  intros * Hf Hg. split; intros.
  - repeat split.
    + intros p Hp. apply BUnionE in Hp as [Hp|Hp];
        apply funcE1 in Hp; eauto; exists (π1 p), (π2 p)...
    + apply domE in H0...
    + intros y y' Hy Hy'.
      apply BUnionE in Hy as []; apply BUnionE in Hy' as [].
      * clear Hg. eapply funcE2...
      * apply domI in H1 as Hdf. apply domI in H2 as Hdg.
        apply apI in H1... apply apI in H2...
        assert (x ∈ dom f ∩ dom g) by (apply BInterI; auto).
        apply H in H3. congruence.
      * apply domI in H1 as Hdf. apply domI in H2 as Hdg.
        apply apI in H1... apply apI in H2...
        assert (x ∈ dom f ∩ dom g) by (apply BInterI; auto).
        apply H in H3. congruence.
      * clear Hf. eapply funcE2...
  - intros x Hx. apply BInterE in Hx as [Hdf Hdg].
    apply funcDomE2 in Hdf... apply funcDomE2 in Hdg...
    eapply funcE2... apply BUnionI1... apply BUnionI2...
Qed.

Example ch3_15: ∀ 𝒜, (∀f ∈ 𝒜, is_function f) →
  (∀ f g ∈ 𝒜, f ⊆ g ∨ g ⊆ f) → is_function ⋃𝒜.
Proof with eauto.
  intros. repeat split.
  - intros p Hp. apply UnionAx in Hp as [f [Hf Hp]].
    apply H in Hf. apply funcE1 in Hf. apply Hf in Hp.
    exists (π1 p), (π2 p)...
  - apply domE in H1...
  - intros y y' Hy Hy'.
    apply UnionAx in Hy  as [f [Hf Hpf]].
    apply UnionAx in Hy' as [g [Hg Hpg]].
    destruct (H0 f Hf g Hg).
    + apply H2 in Hpf. eapply funcE2... apply H...
    + apply H2 in Hpg. eapply funcE2... apply H...
Qed.

Example ch3_16: ¬ ∃ F, ∀ f, is_function f → f ∈ F.
Proof with auto.
  intros [F H].
  set (λ f, ∀x ∈ dom f, ∀y ∈ dom f, x = y) as P1.
  set (λ f, ∀z ∈ dom f, <z, z> ∈ f) as P2.
  set {f ∊ F | λ f, P1 f ∧ P2 f } as C.
  apply ch2_8. exists (⋃⋃C). intros.
  apply UnionAx. exists (⎨⎨a⎬⎬). split; [|apply SingI].
  apply UnionAx. exists (⎨⎨⎨a⎬⎬⎬). split; [|apply SingI].
  assert (⎨⎨⎨a⎬⎬⎬ = ⎨<a, a>⎬) by reflexivity.
  assert (⎨<a, a>⎬ = Ident ⎨a⎬). {
    apply ExtAx. split; intros.
    - apply SingE in H1. subst x. apply ReplAx.
      exists a. split... apply SingI.
    - apply ReplE in H1 as [b [Ha Hp]]. apply SingE in Ha.
      subst b x. apply SingI.
  }
  rewrite H0, H1. apply SepI. apply H. apply ident_is_func.
  split. intros x Hx y Hy.
  apply domE in Hx as [x' Hx]. apply identE in Hx as [Hx _].
  apply domE in Hy as [y' Hy]. apply identE in Hy as [Hy _].
  apply SingE in Hx. apply SingE in Hy. subst...
  intros z Hz. apply domE in Hz as [z' Hz].
  apply identE in Hz as Heq. destruct Heq as [_ Heq]. subst...
Qed.

Example ch3_17_a: ∀ F G,
  single_rooted F → single_rooted G → single_rooted (F ∘ G).
Proof with eauto.
  intros * Hsf Hsg y Hy. split. apply ranE in Hy...
  intros x x' Hx Hx'.
  apply compoE in Hx  as [t [Htg Htf]].
  apply compoE in Hx' as [u [Hug Huf]].
  assert (t = u) by (clear Hsg; eapply singrE; eauto).
  subst. clear Hsf. eapply singrE...
Qed.

Example ch3_17_b: ∀ F G,
  injection F → injection G → injection (F ∘ G).
Proof with auto.
  intros * [Hff Hsf] [Hfg Hsg]. split.
  apply compo_func... apply ch3_17_a...
Qed.

Example ch3_20: ∀ F A, F ↾ A = F ∩ A × ran F.
Proof with eauto.
  intros. apply ExtAx. intros x. split; intros Hx.
  - apply restrE in Hx as [a [b [Ha [Hp Heq]]]].
    subst x. apply BInterI... apply CProdI... eapply ranI...
  - apply BInterE in Hx as [Hx Hcp].
    apply CProd_correct in Hcp as [a [Ha [b [Hb Heq]]]].
    subst x. apply restrI...
Qed.

Example ch3_21: ∀ R S T, (R ∘ S) ∘ T = R ∘ (S ∘ T).
Proof with eauto.
  intros. apply ExtAx. intros x. split; intros Hx.
  - pose proof (compo_rel (R ∘ S) T).
    apply relE in Hx as Heq... rewrite Heq in *.
    apply compoE in Hx as [t [Ht1 Ht2]].
    apply compoE in Ht2 as [u [Hu1 Hu2]].
    eapply compoI. split... eapply compoI...
  - pose proof (compo_rel R (S ∘ T)).
    apply relE in Hx as Heq... rewrite Heq in *.
    apply compoE in Hx as [t [Ht1 Ht2]].
    apply compoE in Ht1 as [u [Hu1 Hu2]].
    eapply compoI. split... eapply compoI...
Qed.

Example ch3_22_a: ∀ F A B, A ⊆ B → F⟦A⟧ ⊆ F⟦B⟧.
Proof.
  intros * H y Hy. apply imgE in Hy as [x [Hx Hp]].
  apply H in Hx. eapply imgI; eauto.
Qed.

Example ch3_22_b: ∀ F G A, (F ∘ G)⟦A⟧ = F⟦G⟦A⟧⟧.
Proof with eauto.
  intros. apply ExtAx. intros y. split; intros Hy.
  - apply imgE in Hy as [x [Hx Hp]].
    apply compoE in Hp as [t [Htg Htf]].
    eapply imgI... eapply imgI...
  - apply imgE in Hy as [x [Hx Hpf]].
    apply imgE in Hx as [w [Hw Hpg]].
    eapply imgI... eapply compoI. split...
Qed.

Example ch3_22_c: ∀ Q A B, Q ↾ (A ∪ B) = (Q ↾ A) ∪ (Q ↾ B).
Proof with auto.
  intros. apply ExtAx. intros x. split; intros Hx.
  - apply restrE in Hx as [a [b [Ha [Hp Heq]]]]. subst x.
    apply BUnionE in Ha as [].
    + apply BUnionI1. apply restrI...
    + apply BUnionI2. apply restrI...
  - apply BUnionE in Hx as [Hx|Hx];
    apply restrE in Hx as [a [b [Ha [Hp Heq]]]]; subst x.
    + apply restrI... apply BUnionI1...
    + apply restrI... apply BUnionI2...
Qed.

Example ch3_23_a: ∀ A B, B ∘ Ident A = B ↾ A.
Proof with eauto.
  intros. apply ExtAx. intros x. split; intros Hx.
  - pose proof (compo_rel B (Ident A)).
    apply relE in Hx as Heq... clear H. rewrite Heq in Hx.
    apply compoE in Hx as [t [Hta Htb]].
    apply identE in Hta as [Hp1 Ht].
    subst t. rewrite Heq. apply restrI...
  - apply restrE in Hx as [a [b [Ha [Hp Heq]]]]. subst x.
    eapply compoI. split... apply identI...
Qed.

Example ch3_23_b: ∀ A C, (Ident A)⟦C⟧ = A ∩ C.
Proof with eauto.
  intros. apply ExtAx. intros x. split; intros Hx.
  - apply imgE in Hx as [w [Hc Hp]].
    apply identE in Hp as [Ha Heq]. subst x. apply BInterI...
  - apply BInterE in Hx as [Ha Hc].
    eapply imgI... apply identI...
Qed.

Example ch3_24: ∀ F A,
  is_function F → F⁻¹⟦A⟧ = {x ∊ dom F | λ x, F[x] ∈ A}.
Proof with eauto.
  intros F A Hf. apply ExtAx. split; intros.
  - apply SepE in H as [_ [w Hp]]. apply SepE in Hp as [Hp [_ Hw]].
    rewrite π1_correct in Hw. apply SepE in Hp as [_ [_ Hq]].
    rewrite π1_correct, π2_correct in Hq.
    apply SepI. eapply domI... erewrite apI...
  - apply SepE in H as [Hd Hy].
    pose proof (ap_exists F Hf x Hd) as [y [_ [Hxy Heq]]].
    eapply ranI. apply SepI; try split.
    + rewrite inv_op in Hxy...
    + exists y, x...
    + rewrite π1_correct. rewrite Heq in Hy...
Qed.

Example ch3_25: ∀ G,
  is_function G → (G ∘ G⁻¹) = Ident (ran G).
Proof. exact compo_inv_ran_ident. Qed.

(* ch3_26: see EX7.v *) 

Example ch3_27: ∀ F G, dom (F ∘ G) = G⁻¹⟦dom F⟧.
Proof with eauto.
  intros. apply ExtAx. intros x. split; intros Hx.
  - apply domE in Hx as [y Hp].
    apply compoE in Hp as [t [Htg Htf]].
    eapply imgI. eapply domI... rewrite <- inv_op...
  - apply imgE in Hx as [w [Hw Hpf]].
    rewrite <- inv_op in Hpf. apply domE in Hw as [x' Hpg].
    eapply domI. eapply compoI...
Qed.

Example ch3_28: ∀ f A B G,
  injection f → f: A ⇒ B →
  is_function G → dom G = 𝒫 A → (∀x ∈ dom G, G[x] = f⟦x⟧) →
  G: 𝒫 A ⇒ 𝒫 B ∧ injection G.
Proof with eauto.
  intros * [Hff Hsf] [_ [Hdf Hrf]] Hfg Hdgeq Hapeq.
  split. split... split...
  - intros y Hy. apply ranE in Hy as [x Hp].
    apply domI in Hp as Hdg. apply Hapeq in Hdg.
    apply apI in Hp... subst y. rewrite Hdg.
    assert (f⟦x⟧ ⊆ ran f) by apply img_included.
    apply PowerAx. eapply sub_tran...
  - split... intros y Hy. split. apply ranE in Hy...
    intros X X' HX HX'. subst A.
    apply domI in HX as Hd. apply domI in HX' as Hd'.
    apply apI in HX... apply apI in HX'...
    rewrite Hapeq in HX... rewrite Hapeq in HX'... subst y.
    clear Hrf Hfg Hapeq Hy.
    apply ExtAx. intros x. split; intros Hx.
    + rewrite Hdgeq in Hd. rewrite PowerAx in Hd. 
      apply Hd in Hx as Hpx. apply funcDomE2 in Hpx...
      eapply imgI in Hpx as Himg... rewrite <- HX' in Himg.
      apply imgE in Himg as [x' [Hx' Hpx']].
      assert (x = x') by (eapply singrE; eauto). subst...
    + rewrite Hdgeq in Hd'. rewrite PowerAx in Hd'.
      apply Hd' in Hx as Hpx. apply funcDomE2 in Hpx...
      eapply imgI in Hpx as Himg... rewrite HX' in Himg.
      apply imgE in Himg as [x' [Hx' Hpx']].
      assert (x = x') by (eapply singrE; eauto). subst...
Qed.

Example ch3_29: ∀ f A B G,
  f: A ⇒ B → G: B ⇒ 𝒫 A → 
  (∀b ∈ dom G, G[b] = {x ∊ A | λ x, f[x] = b}) →
  ran f = B → injection G.
Proof with eauto.
  intros * [Hff [Hdf _]] [Hgf [Hdg _]] H Hrf. subst A B.
  split... intros y Hy. split. apply ranE in Hy... clear Hy.
  intros b b' Hb Hb'. 
  apply domI in Hb as Hd. apply domI in Hb' as Hd'.
  apply apI in Hb... apply apI in Hb'... subst y.
  apply H in Hd as Heq. apply H in Hd' as Heq'.
  rewrite <- Hb' in Heq. rewrite Heq' in Heq.
  rewrite <- Hrf in Hd. clear Hb' Hd' Heq'.
  apply ranE in Hd as [x Hp]. apply apI in Hp as Hap...
  assert (Hx: x ∈ Sep (dom f) (λ x, f [x] = b)). {
    apply SepI... apply domI in Hp...
  }
  rewrite <- Heq in Hx. apply SepE in Hx as [_ Hfb]. subst...
Qed.

(** 克纳斯特－塔斯基定理的引理 **)
(* 设L是完全格，F: L ⇒ L 是次序保持函数，则F在L中有最小不动点和最大不动点 *)
Example ch3_30: ∀ F A, F: 𝒫 A ⇒ 𝒫 A →
  (∀ X Y, X ⊆ Y ∧ Y ⊆ A → F[X] ⊆ F[Y]) →
  let ℬ := {X ∊ 𝒫 A | λ X, F[X] ⊆ X} in
  let 𝒞 := {X ∊ 𝒫 A | λ X, X ⊆ F[X]} in
  let B := ⋂ℬ in let C := ⋃𝒞 in
  F[B] = B ∧ F[C] = C ∧ ∀X ∈ dom F, F[X] = X → B ⊆ X ∧ X ⊆ C.
Proof with eauto.
  intros * [Hf [Hd Hr]] HM ℬ 𝒞 B C.
  assert (HAp: <A, F[A]> ∈ F). {
    eapply funcDomE2... rewrite Hd. apply all_in_its_power.
  }
  assert (HAaps: F[A] ⊆ A). {
    apply PowerAx. apply Hr. eapply ranI...
  }
  assert (HA: A ∈ ℬ). {
    apply SepI... apply all_in_its_power.
  }
  assert (HBs: B ⊆ A). {
    intros x Hx. apply InterE in Hx as [[y H1] H2]. apply H2...
  }
  assert (HBp: <B, F[B]> ∈ F). {
    eapply funcDomE2... rewrite Hd. apply PowerAx...
  }
  assert (HBaps: F[B] ⊆ B). {
    intros x Hx. apply InterI. exists A... intros X HX.
    cut (F[B] ⊆ X). intros. apply H...
    cut (F[B] ⊆ F[X] ∧ F[X] ⊆ X). intros []. eapply sub_tran...
    assert (HX':= HX). apply SepE in HX' as [HXP HXs].
    rewrite PowerAx in HXP. split... apply HM. split...
    intros b Hb. apply InterE in Hb as [_ Hb]. apply Hb...
  }
  assert (HCs: C ⊆ A). {
    intros x Hx. apply UnionAx in Hx as [X [HX Hx]].
    apply SepE in HX as [HX _]. rewrite PowerAx in HX. apply HX... 
  }
  assert (HCp: <C, F[C]> ∈ F). {
    eapply funcDomE2... rewrite Hd. apply PowerAx...
  }
  assert (HCaps: C ⊆ F[C]). {
    intros x Hx. apply UnionAx in Hx as [X [HX Hx]].
    cut (X ⊆ F[C]). intros. apply H...
    cut (X ⊆ F[X] ∧ F[X] ⊆ F[C]). intros []. eapply sub_tran...
    assert (HX':= HX). apply SepE in HX' as [_ HXs].
    split... apply HM. split...
    intros c Hc. apply UnionAx. exists X. split...
  }
  split; [|split].
  - (* F[B] = B *) apply sub_asym...
    intros x Hx. apply InterE in Hx as [_ Hx]. apply Hx.
    apply SepI. apply Hr. eapply ranI... apply HM. split...
  - (* F[C] = C *) apply sub_asym...
    intros x Hx. apply UnionAx. exists (F[C]). split...
    apply SepI. apply Hr. eapply ranI... apply HM. split...
    apply PowerAx. apply Hr. eapply ranI...
  - intros X HX Heq. split.
    + (* B ⊆ X *) intros b Hb.
      apply InterE in Hb as [_ Hb]. apply Hb.
      apply SepI. apply Hr. rewrite <- Heq. eapply ranI.
      apply funcDomE2... rewrite ExtAx in Heq.
      intros x Hx. apply Heq...
    + (* X ⊆ C *) intros c Hc.
      apply UnionAx. exists X. split...
      apply SepI. apply Hr. rewrite <- Heq. eapply ranI.
      apply funcDomE2... rewrite ExtAx in Heq.
      intros x Hx. apply Heq...
Qed.

(* ch3_31: see EX7.v Theorem AC_1_iff_2 *) 
