From CRIS.common Require Import Common ConcRA.
From iris.proofmode Require Import proofmode.

From CRIS.modules Require Import Mod.
From CRIS.simulations.gsim Require Import GSimAdequacy GSimMod.
From CRIS.simulations.lsim Require Import LSimAdequacy LSimMod.
From CRIS.simulations.msim Require Import MSimCommon ISim ISimAdequacy.
From CRIS.simulations.ctxrefine Require Import CtxRefine.

Section ADEQUACY.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Lemma Own_split'
    r P Q
    (Vr : ✓ r)
    (H : Own r ⊢ P ∗ Q)
    : ∃ x, ✓ x /\ (Own x ⊢ P) /\ (Own r ⊢ Own x ∗ Q).
  Proof.
    eapply Own_split in H; et. destruct H as [a [b [E [H1 H2]]]].
    exists a. splits.
    - eapply cmra_valid_op_l. rewrite <- E; et.
    - et.
    - rewrite E. rewrite Own_op. rewrite H2. et.
  Qed.

  Theorem gsim_closed_adequacy
    (Mt Ms : Mod.t)
    : gsim_mod Ms Mt ⊢ refines Mt Ms.
  Proof.
    eapply entails_pointwise. intros r Vr Hsim.
    rewrite gsim_mod_unseal in Hsim.
    eapply Own_general_soundness in Hsim; et.
    iIntros "R %WFT".
    specialize (Hsim WFT). destruct Hsim as [WFS SIM].
    iSplit. { iPureIntro. et. }
    iIntros "WINV %t TGT".
    iRevert "TGT R WINV"; iIntros "TGT R WINV". iStopProof.
    eapply entails_pointwise. intros rs Vrs Hrs.
    eapply Own_split' in Hrs; et. destruct Hrs as [rt [Vrt [Hrt Hrs]]].
    eapply Own_general_completeness. rewrite Beh_unseal.
    intros rs' Vrs' LE.
    assert (SPLIT : Own rs' ⊢ Own rt ∗ Own r ∗ winv (∅,∅)).
    { iIntros "H". iApply Hrs. iApply Own_extends; et. }
    specialize (SIM rt rs' Vrs' SPLIT).
    eapply gsim_adequacy with (x0 := t) in SIM.
    2:{
      eapply Own_general_soundness in Hrt; et.
      rewrite Beh_unseal in Hrt. eapply Hrt; et.
    }
    eapply SIM.
  Qed.

  Theorem lsim_closed_adequacy
    (Mt Ms : Mod.t)
    : lsim_mod Ms Mt ⊢ refines Mt Ms.
  Proof.
    eapply transitivity with (y := gsim_mod Ms Mt).
    - eapply entails_pointwise. intros r Vr Hsim.
      rewrite lsim_mod_unseal in Hsim.
      eapply Own_general_soundness in Hsim; et.
      eapply Own_general_completeness. rewrite gsim_mod_unseal.
      intros WFT. specialize (Hsim WFT).
      destruct Hsim as [WFS SIM]. split; et.
      intros rt rs Vrs Hrs. specialize (SIM rt rs Vrs Hrs). destruct SIM.
      eapply lsim_adequacy. et.
    - eapply gsim_closed_adequacy.
  Qed.

  Theorem ISim_closed_adequacy
    (Mt Ms : Mod.t)
    : ISim.t closed Ms Mt ⊢ refines Mt Ms.
  Proof.
    eapply transitivity with (y := lsim_mod Ms Mt).
    - eapply (ISim_adequacy closed).
    - eapply lsim_closed_adequacy.
  Qed.

End ADEQUACY.
