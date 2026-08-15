From CRIS.simulations.gsim Require Import GSimMod GSimAux.
From CRIS.simulations.msim Require Import ISimRefl.
From CRIS.simulations.ctxrefine Require Import CtxRefine CtxRefineFacts ClosedAdequacy MainAdequacy.
From CRIS.cancellation Require Import MInline MInlineIntro MInlineElim.
From CRIS.cancellation Require Import CancelPrepare CancelMain.

Module Cancel.
  Section Cancel_Theorems.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Theorem prepare (spt sps: specmap) (md: SMod.t)
    (SP1: ∀ fn arg (msk: emask) p, md.(SMod.fnsems) !! fn = Some (Some (msk,p)) →
          ∀ (fc: string), spt.1 !! (funid fc) ≠ sps.1 !! (funid fc) →
          msk _ (subevent _ (Call fc arg)) = false ∧
          msk _ (subevent _ (Spawn fc arg)) = false)
    (SPS: sps.2 = true)
    (SP2: spt.2 = false →
          ∀ fn (msk: emask) p, md.(SMod.fnsems) !! fn = Some (Some (msk,p)) →
          ∀ T (e: callE T), msk_sys _ (subevent _ e) = true → msk _ (subevent _ e) = false)
    :
    ⊢ ctx_refines
      (SMod.to_mod spt md)
      (SMod.to_mod_cancel sps md).
  Proof.
    iApply (main_adequacy _ _ (IstEq (SMod.to_mod spt md))).
    iApply prepare_sim; et.
  Qed.

  Definition init_res : iProp Σ :=
    TID 0 ∗ YIELD 0 ∗ winv (⊤, ⊤) ∗ TIDAUTH 0 ∗ YIELDAUTH 1.

  Theorem cancel
    M P Q
    (CANCELLABLE : SMod.cancellable M)
    (ENTRY : fspec_flat ((SMod.sp_from M).1 !! entry) P Q)
    (POST : forall varg arg, Q varg arg ⊢ ⌜ varg = arg ⌝)
    : P tt↑ tt↑ ∗ TIDAUTH 0 ∗ YIELDAUTH 1
        ⊢ refines
        (SMod.to_mod_cancel (SMod.sp_from M) M)
        (SMod.to_mod ∅ (SMod.cancel M)).
  Proof.
    iIntros "[PRE INIT]".
    iApply refines_trans. iSplitR. { iApply ISim_closed_adequacy. iApply inline_intro. }
    iApply refines_trans. iSplitL. 2:{ iApply ISim_closed_adequacy. iApply inline_elim. }
    iStopProof.
    eapply transitivity with
      (y := gsim_mod
              (MInline.inline (SMod.to_mod ∅ (SMod.cancel M)))
              (MInline.inline (SMod.to_mod_cancel (SMod.sp_from M) M))).
    2: eapply gsim_closed_adequacy.
    eapply gsim_mod_intro.
    intros Hwfm.
    assert (Hwfc : Mod.wf (SMod.to_mod ∅ (SMod.cancel M))).
    { inv Hwfm; econs; ss.
      revert wf_fns; rewrite !map_Forall_lookup => Hwf i x; specialize (Hwf i).
      rewrite !lookup_fmap in Hwf; rewrite !lookup_fmap.
      destruct (SMod.fnsems M !! i) as [[[? ?]|]|]; s; i; clarify.
      specialize (Hwf None); ss; hexploit Hwf; eauto.
    }
    split.
    { inv Hwfm. econs; eauto. s.
      intros i ? Hl. ss. r in wf_fns. specialize (wf_fns i). ss.
      rewrite !lookup_fmap in Hl, wf_fns. destruct (SMod.fnsems M !! i); ss.
      destruct o; ss; cycle 1.
      { inv Hl. hexploit wf_fns; eauto. }
      inv Hl. destruct p as [msk [fspo bd]]. ss.
    }
    intros rt rs Vrs Hrs.
    eapply cancel_main; et.
    esplits; eauto. rewrite Hrs.
    iIntros "[$ [[INIT [$ $]] _]]". et.
  Qed.

  End Cancel_Theorems.
End Cancel.
