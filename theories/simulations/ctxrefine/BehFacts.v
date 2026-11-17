From CRIS.common Require Import Common ConcRA.
From CRIS.modules Require Import Mod LMod.
From CRIS.simulations.gsim Require Import GSimAdequacy.
From CRIS.simulations.lsim Require Import LSimAdequacy LSimMod.
From CRIS.simulations.msim Require Import MSimCommon ISimFacts ISimAdequacy.
From CRIS.simulations.ctxrefine Require Import CtxRefine.

Section MOD_BEHAVIOR.

  Context `{!crisG Γ Σ α β τ _S _I}.

  Lemma Beh_intro
    M t r
    (WF : Mod.wf M)
    (BEH : Beh.of_itree (LMod.compile (Mod.to_lmod M r) tt↑) t)
    : Own r ∗ winv (∅,∅) ⊢ Beh M t.
  Proof.
    eapply entails_pointwise. intros rt Vrt Hrt.
    eapply Own_general_completeness. rewrite Beh_unseal.
    intros rt' Vrt' LE.
    assert (REFL' : Own (ε : Σ) ⊢ lsim_mod M M).
    { iIntros "_". iApply (ISim_adequacy open). iApply ISim_refl. }
    rewrite lsim_mod_unseal in REFL'.
    eapply Own_general_soundness in REFL'.
    2: apply ucmra_unit_valid.
    specialize (REFL' WF). destruct REFL' as [_ REFL'].
    assert (SUB : Own rt' ⊢ Own r ∗ Own (ε : Σ) ∗ winv (∅,∅)).
    {
      iIntros "H".
      iPoseProof (Own_extends with "H") as "H"; et.
      iDestruct (Hrt with "H") as "[R WINV]".
      iFrame. iApply Own_unit.
    }
    specialize (REFL' r rt' Vrt' SUB). destruct REFL' as [lw REFL'].
    eapply (lsim_adequacy _ _ (tt↑)) in REFL'.
    eapply gsim_adequacy with (x0 := t) in REFL'; et.
  Qed.

  Lemma Beh_elim
    M t r
    (BEH : Own r ⊢ Beh M t)
    : forall r', ✓ r' -> r ≼ r' -> Beh.of_itree (LMod.compile (Mod.to_lmod M r') tt↑) t.
  Proof.
    intros r' Vr' LE.
    assert (Vr : ✓ r) by (eapply cmra_valid_included; et).
    eapply Own_general_soundness in BEH; et.
    rewrite Beh_unseal in BEH. eapply BEH; et.
  Qed.

End MOD_BEHAVIOR.
