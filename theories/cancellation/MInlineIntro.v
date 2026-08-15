From CRIS.common Require Import Common ConcRA.
From CRIS.modules Require Import SModTr SMod Mod.
From CRIS.simulations.msim Require Import
  Tactics MSimCommon ISim ISimFacts.
From CRIS.cancellation Require Import MInline.
From iris.proofmode Require Import proofmode.
From stdpp Require Import base list.

Set Implicit Arguments.

Section INLINE.
Context `{_crisG: !crisG Γ Σ α β τ _S _I}.

Lemma inline_intro md :
  ⊢ ISim.t closed (MInline.inline md) md (IstEq md).
Proof using _I _S _crisG Γ Σ α β τ.
  cut (∀ STATE : stateGS Σ, ⊢ ∀ f : emask * fbody,
    ⌜(∀ k v, f.1 _ (subevent _ (SPut k v)) = true →
        k.1 ∈ Mod.scopes md) ∧
      (∀ k, f.1 _ (subevent _ (SGet k)) = true →
        k.1 ∈ Mod.scopes md)⌝ →
    isim_fsem
      (fmap (λ v : option (emask * fbody), SB.sandbox_body <$> v)
        (fmap (option_map (inline_fsem md)) (Mod.fnsems md)))
      (fmap (λ v : option (emask * fbody), SB.sandbox_body <$> v)
        (Mod.fnsems md))
      (IstEq md STATE) closed
      (SB.sandbox_body (inline_fsem md f)) (SB.sandbox_body f)).
  { intros FSIMS.
    rewrite /ISim.t. iSplit.
    { rewrite /ISim.init_ist. iIntros (WF). iSplit.
      { done. }
      iIntros (STATE) "SRC TGT".
      iApply (@state_eq_init_same Σ STATE
        (list_to_set (Mod.scopes md)) (Mod.initial_st md) with "SRC TGT"). }
    rewrite /ISim.sim_funs. iIntros (WF). iSplit.
    { iPureIntro.
      split.
      - eapply map_Forall_fmap, map_Forall_impl; first apply WF.
        intros ? [[??]|]; ss.
      - rewrite /MInline.inline /Mod.fnsems /= dom_fmap. done. }
    iIntros (fn) "%Hfn". rewrite /ISim.sim_fun.
    iIntros (STATE).
    iPoseProof (FSIMS STATE) as "#FSIMS".
    iIntros "%WFS %WFT" (fs) "%Hfs".
    rewrite /sandbox_fnsemmap !lookup_fmap in Hfs.
    destruct (Mod.fnsems md !! fn) as [[[msk body]|]|]
      eqn:FINDT; ss; clarify.
    iExists (SB.sandbox_body (msk, body)).
    iSplit.
    { iPureIntro.
      rewrite /sandbox_fnsemmap lookup_fmap FINDT //. }
    iApply ("FSIMS" $! (msk, body) with "[]").
    iPureIntro.
    hexploit (Mod.well_scoped_fns md fn (msk, body)).
    { rewrite lookup_omap FINDT //. }
    done.
  }

  intros STATE. iIntros (f) "%SCOPED". rewrite /isim_fsem.
  iIntros "!#" (arg) "IST I".
  destruct f as [msk bd].
  generalize false at 1 as ps. generalize false at 1 as pt.
  do 2 (rewrite /SB.sandbox_body; s). generalize (bd arg) as it. i; ss. clear bd arg.
  cCoind CIH g __ with ps pt it msk SCOPED. iIntros "[IST I]".
  destruct SCOPED as [HPUT HGET].

  assert (CASE := case_itrH it); des; subst.
  - rewrite SBRed.ret MIRed.ret. cStep. iFrame. done.
  - rewrite SBRed.tau MIRed.tau !SBRed.tau. cStepsS. cStepsT. cByCoind CIH; eauto; iFrame.
  - rewrite SBRed.bind SBRed.vis !vis_trigger. des_ifs; cycle 1.
    { s. rewrite bind_bind MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. cStepS; ss. }
    ired. rewrite -(bind_ret_r (trigger (Assume _))) MIRed.bind MIRed.ag bind_bind SBRed.bind SBRed.vis !vis_trigger. des_ifs.
    ired. cStepS. cStepS.
    rewrite MIRed.ret. cNormS. rewrite !SBRed.ret bind_ret_l.
    iforce_t. iFrame. cStepsT.
    cByCoind CIH; eauto; iFrame.
  - rewrite SBRed.bind SBRed.vis !vis_trigger. des_ifs; cycle 1.
    { s. rewrite bind_bind MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. cStepS; ss. }
    ired. rewrite -(bind_ret_r (trigger (AssumeRes _))) MIRed.bind MIRed.ag bind_bind SBRed.bind SBRed.vis !vis_trigger. des_ifs.
    ired. cStepS. cStepS.
    rewrite MIRed.ret. cNormS. rewrite !SBRed.ret bind_ret_l.
    iforce_t. iFrame. cStepsT.
    cByCoind CIH; eauto; iFrame.
  - rewrite SBRed.bind SBRed.vis !vis_trigger. des_ifs; cycle 1.
    { s. rewrite bind_bind MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. cStepS; ss. }
    ired. rewrite -(bind_ret_r (trigger (Guarantee _))) MIRed.bind MIRed.ag bind_bind SBRed.bind SBRed.vis !vis_trigger. des_ifs.
    ired. cStepT.
    iforce_s. iFrame. cStepsS.
    rewrite MIRed.ret. cNormS. rewrite !SBRed.ret bind_ret_l.
    cByCoind CIH; eauto; iFrame.
  - destruct c.
    {
      rewrite SBRed.bind SBRed.vis !vis_trigger. des_ifs; cycle 1.
      { ired. rewrite MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. cStepS; ss. }
      ired. rewrite MIRed.call. cStepS. rewrite {2}/sandboxed_prog.
      destruct ((Mod.fnsems md) !! funid fn) eqn:FIND; cycle 1.
      { rewrite lookup_omap FIND /=. ired. rewrite MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. cStepS; ss. }
      destruct o; cycle 1.
      { rewrite lookup_omap FIND /=. ired. rewrite MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. cStepS; ss. }
      destruct p as [msk0 bd0]. iApply isim_inline_tgt.
      { rewrite lookup_fmap FIND //. }
      rewrite lookup_omap FIND /=. ired. rewrite /SB.sandbox_body. s.

      rewrite MIRed.bind SBRed.bind.
      iPoseProof (winv_split_empty with "[I]") as "[I I']"; et.
      iApply isim_bind. iSplitL "IST I".
      - cByCoind CIH; et.
        { eapply (Mod.well_scoped_fns md (funid fn) (msk0, bd0)).
          rewrite lookup_omap FIND //. }
        iFrame.
      - iIntros (? ?) "[% IST]". subst.
        rewrite !MIRed.tau. ired. rewrite !SBRed.ret !bind_ret_l. do 2 cStepS. cStepT.
        cByCoind CIH; et; iFrame.
    }
    {
      rewrite !SBRed.bind !SBRed.vis !vis_trigger. des_ifs; cycle 1.
      { s. rewrite bind_bind MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. cStepS; ss. }
      ired. rewrite MIRed.spawn SBRed.bind SBRed.vis !vis_trigger. des_ifs. ired.
      iApply isim_spawn. iIntros (?). cStepS.
      rewrite !SBRed.ret !bind_ret_l. cByCoind CIH; et; iFrame.
    }
    {
      rewrite !SBRed.bind !SBRed.vis !vis_trigger. des_ifs; cycle 1.
      { s. rewrite bind_bind MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. cStepS; ss. }
      ired. rewrite MIRed.yield !SBRed.bind !SBRed.vis !vis_trigger. des_ifs.
      ired. iApply isim_yield. iSplitL "IST"; et. iIntros "IST".
      cStepS. rewrite !SBRed.ret bind_ret_l. cByCoind CIH; et; iFrame.
    }
    {
      rewrite !SBRed.bind !SBRed.vis !vis_trigger. des_ifs; cycle 1.
      { s. rewrite bind_bind MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. cStepS; ss. }
      ired. rewrite MIRed.gettid !SBRed.bind !SBRed.vis !vis_trigger. des_ifs.
      ired. iApply isim_gettid. iIntros (?).
      cStepS. rewrite !SBRed.ret bind_ret_l. cByCoind CIH; et; iFrame.
    }
  - depdes s.
    + rewrite !SBRed.bind !SBRed.vis !vis_trigger. des_ifs; cycle 1. 
      { s. rewrite bind_bind MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. cStepS; ss. }
      ired. rewrite MIRed.pg !SBRed.bind !SBRed.vis !vis_trigger. des_ifs; cycle 1.
      { s. ired. cStepS; ss. }
      ired. iApply (isim_sput_eq _ _ _ (S := list_to_set (Mod.scopes md))).
      { rewrite elem_of_list_to_set. eapply (HPUT k v).
        rewrite orb_false_r in Heq. exact Heq. }
      iFrame "IST". iIntros "IST".
      cStepS. rewrite !SBRed.ret bind_ret_l. cByCoind CIH; et; iFrame.
    + rewrite !SBRed.bind !SBRed.vis !vis_trigger. des_ifs; cycle 1. 
      { s. rewrite bind_bind MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. cStepS; ss. }
      ired. rewrite MIRed.pg !SBRed.bind !SBRed.vis !vis_trigger. des_ifs; cycle 1.
      { s. ired. cStepS; ss. }
      ired. iApply (isim_sget_eq _ _ _ (S := list_to_set (Mod.scopes md))).
      { rewrite elem_of_list_to_set. eapply (HGET k).
        rewrite orb_false_r in Heq. exact Heq. }
      iFrame "IST". iIntros (?) "IST".
      cStepS. rewrite !SBRed.ret bind_ret_l. cByCoind CIH; et; iFrame.
  - depdes e.
    + rewrite !SBRed.bind !SBRed.vis !vis_trigger. des_ifs; cycle 1.
      { s. rewrite bind_bind MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. cStepS; ss. }
      ired. rewrite MIRed.core SBRed.bind SBRed.vis vis_trigger. des_ifs.
      ired. cStepT. cForceS _q. cStepsS. rewrite !SBRed.ret !bind_ret_l.
      cByCoind CIH; et; iFrame.
    + rewrite !SBRed.bind !SBRed.vis !vis_trigger. des_ifs; cycle 1.
      { rewrite bind_bind MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. cStepS; ss. }
      ired. rewrite MIRed.core SBRed.bind SBRed.vis vis_trigger. des_ifs.
      ired. cStepsS. cForceT _q. ired. rewrite !SBRed.ret !bind_ret_l.
      cByCoind CIH; et; iFrame.
    + rewrite !SBRed.bind !SBRed.vis !vis_trigger. des_ifs; cycle 1.
      { rewrite bind_bind MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. cStepS; ss. }
      ired. rewrite MIRed.core SBRed.bind SBRed.vis vis_trigger. des_ifs.
      ired. cStep. cStepsS. rewrite !SBRed.ret !bind_ret_l.
      cByCoind CIH; et; iFrame.
(*SLOW*)Qed.

End INLINE.
