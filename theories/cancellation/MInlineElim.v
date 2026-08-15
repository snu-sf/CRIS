From CRIS.common Require Import Common ConcRA.
From CRIS.modules Require Import SModTr SMod Mod.
From CRIS.simulations.msim Require Import
  Tactics MSimCommon ISim ISimFacts.
From CRIS.cancellation Require Import MInline.
From stdpp Require Import base list.

Section INLINE.
Context `{!crisG Γ Σ α β τ _S _I}.

Lemma inline_elim md :
  ⊢ ISim.t closed md (MInline.inline md) (IstEq md).
Proof using _I _S crisG0 Γ Σ α β τ.
  cut (∀ STATE : stateGS Σ, ⊢ ∀ f : emask * fbody,
    ⌜∀ X (e : crisE X),
      f.1 _ (subevent _ e) →
      (msk_scp (Mod.scopes md) msk_true) _ (subevent _ e)⌝ →
    isim_fsem
      (fmap (λ v : option (emask * fbody), SB.sandbox_body <$> v)
        (Mod.fnsems md))
      (fmap (λ v : option (emask * fbody), SB.sandbox_body <$> v)
        (fmap (option_map (inline_fsem md)) (Mod.fnsems md)))
      (IstEq md STATE) closed
      (SB.sandbox_body f) (SB.sandbox_body (inline_fsem md f))).
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
      - destruct WF as [wf_fns wf_scopes].
        intros fn value Hlookup. destruct value; first ss.
        exfalso. exploit (wf_fns fn None); [|intros []; ss].
        rewrite /= lookup_fmap Hlookup //.
      - rewrite /MInline.inline /Mod.fnsems /= dom_fmap. done. }
    iIntros (fn) "%Hfn". rewrite /ISim.sim_fun.
    iIntros (STATE).
    iPoseProof (FSIMS STATE) as "#FSIMS".
    iIntros "%WFS %WFT" (fs) "%Hfs".
    rewrite /sandbox_fnsemmap lookup_fmap in Hfs.
    destruct (Mod.fnsems md !! fn) as [[[msk body]|]|]
      eqn:FINDT; ss; clarify.
    iExists (SB.sandbox_body (inline_fsem md (msk, body))).
    iSplit.
    { iPureIntro.
      rewrite /sandbox_fnsemmap /= !lookup_fmap FINDT //. }
    iApply ("FSIMS" $! (msk, body) with "[]").
    iPureIntro. intros X evt Hmask.
    hexploit (Mod.well_scoped_fns md fn (msk, body)).
    { rewrite lookup_omap FINDT //. }
    intros SCOPED; ss; des. depdes evt; ss; des_ifs.
    { case_bool_decide; eauto. }
    { case_bool_decide; eauto. }
  }

  intros STATE. iIntros (f) "%SCP". rewrite /isim_fsem.
  iIntros "!#" (arg) "IST I".
  generalize false at 1 as ps. generalize false at 1 as pt.
  destruct f as [msk bd].
  do 2 (rewrite /SB.sandbox_body; s).
  generalize (bd arg) as it. i; ss. clear bd arg.
  cCoind CIH g __ with ps pt it msk SCP. iIntros "[IST I]".

  assert (CASE := case_itrH it); des; subst.
  - rewrite SBRed.ret MIRed.ret. cStep. iFrame. done.
  - rewrite SBRed.tau MIRed.tau !SBRed.tau. cStepsS. cStepsT.
    cByCoind CIH; eauto; iFrame.
  - rewrite SBRed.bind SBRed.vis !vis_trigger. des_ifs; cycle 1.
    { s. rewrite bind_bind MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. cStepS; ss. }
    ired. rewrite -(bind_ret_r (trigger (Assume _))) MIRed.bind MIRed.ag bind_bind SBRed.bind SBRed.bind SBRed.vis !vis_trigger. des_ifs.
    ired. cStepS. iApply isim_assume_tgt. iFrame. cStepT.
    rewrite MIRed.ret !SBRed.ret bind_ret_l SBRed.ret bind_ret_l.
    cByCoind CIH; eauto; iFrame.
  - rewrite SBRed.bind SBRed.vis !vis_trigger. des_ifs; cycle 1.
    { s. rewrite bind_bind MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. cStepS; ss. }
    ired. rewrite -(bind_ret_r (trigger (AssumeRes _))) MIRed.bind MIRed.ag bind_bind !SBRed.bind SBRed.vis !vis_trigger. des_ifs.
    ired. cStepS. iApply isim_assume_res_tgt. iFrame. cStepT.
    rewrite MIRed.ret. cNormT. rewrite !SBRed.ret bind_ret_l.
    cByCoind CIH; eauto; iFrame.
  - rewrite SBRed.bind SBRed.vis !vis_trigger. des_ifs; cycle 1.
    { s. rewrite bind_bind MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. cStepS; ss. }
    ired. rewrite -(bind_ret_r (trigger (Guarantee _))) MIRed.bind MIRed.ag bind_bind !SBRed.bind SBRed.vis !vis_trigger. des_ifs.
    ired. cStepT. cStepT.
    iforce_s. iFrame. cStepsS.
    rewrite MIRed.ret. cNormT. rewrite !SBRed.ret bind_ret_l.
    cByCoind CIH; eauto; iFrame.
  - destruct c.
    {
      rewrite SBRed.bind SBRed.vis !vis_trigger. des_ifs; cycle 1.
      { ired. rewrite MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. cStepS; ss. }
      ired. rewrite MIRed.call. cStepT. rewrite {2}/sandboxed_prog.
      destruct ((Mod.fnsems md) !! funid fn) eqn:FIND; cycle 1.
      { iApply isim_call_none; eauto. rewrite lookup_fmap FIND //. }
      destruct o; cycle 1.
      { iApply isim_call_none; eauto. rewrite lookup_fmap FIND //. }
      destruct p as [msk0 bd0]. iApply isim_inline_src.
      { rewrite lookup_fmap FIND //. }
      rewrite lookup_omap FIND /=. ired. rewrite /SB.sandbox_body. s.

      rewrite MIRed.bind SBRed.bind.
      iPoseProof (winv_split_empty with "[I]") as "[I I']"; et.
      iApply isim_bind. iSplitL "IST I".
      - cByCoind CIH; et.
        hexploit (Mod.well_scoped_fns md (funid fn) (msk0, bd0)).
        { rewrite lookup_omap FIND //. }
        i; ss; des. depdes e; ss. des_ifs.
        { case_bool_decide; eauto. }
        { case_bool_decide; eauto. }
        iFrame.
      - iIntros (? ?) "[% IST]". subst.
        rewrite !MIRed.tau. ired. rewrite !SBRed.ret !bind_ret_l. do 2 cStepT. cStepS.
        cByCoind CIH; et; iFrame.
    }
    {
      rewrite !SBRed.bind !SBRed.vis !vis_trigger. des_ifs; cycle 1.
      { s. rewrite bind_bind MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. cStepS; ss. }
      ired. rewrite MIRed.spawn SBRed.bind SBRed.vis !vis_trigger. des_ifs. ired.
      iApply isim_spawn. iIntros (?). cStepT.
      rewrite !SBRed.ret !bind_ret_l. cByCoind CIH; et; iFrame.
    }
    {
      rewrite !SBRed.bind !SBRed.vis !vis_trigger. des_ifs; cycle 1.
      { s. rewrite bind_bind MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. cStepS; ss. }
      ired. rewrite MIRed.yield !SBRed.bind !SBRed.vis !vis_trigger. des_ifs.
      ired. iApply isim_yield. iSplitL "IST"; et. iIntros "IST".
      cStepT. rewrite !SBRed.ret bind_ret_l. cByCoind CIH; et; iFrame.
    }
    {
      rewrite !SBRed.bind !SBRed.vis !vis_trigger. des_ifs; cycle 1.
      { s. rewrite bind_bind MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. cStepS; ss. }
      ired. rewrite MIRed.gettid !SBRed.bind !SBRed.vis !vis_trigger. des_ifs.
      ired. iApply isim_gettid. iIntros (?).
      cStepT. rewrite !SBRed.ret bind_ret_l. cByCoind CIH; et; iFrame.
    }
  - depdes s.
    + rewrite !SBRed.bind !SBRed.vis !vis_trigger. des_ifs; bsimpl; cycle 1. 
      { s. rewrite bind_bind MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. cStepS; ss. }
      ired. rewrite MIRed.pg !SBRed.bind !SBRed.vis !vis_trigger. des_ifs; cycle 1.
      { hexploit SCP; eauto. i; ss. rewrite H in Heq0. ss. }
      ired. iApply (isim_sput_eq _ _ _ (S := list_to_set (Mod.scopes md))).
      { rewrite elem_of_list_to_set.
        hexploit (SCP _ (subevent _ (SPut k v))); eauto. intros HS.
        rewrite bool_decide_eq_true in HS. exact HS. }
      iFrame "IST". iIntros "IST".
      cStepT. rewrite !SBRed.ret bind_ret_l. cByCoind CIH; et; iFrame.
    + rewrite !SBRed.bind !SBRed.vis !vis_trigger. des_ifs; bsimpl; cycle 1. 
      { s. rewrite bind_bind MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. cStepS; ss. }
      ired. rewrite MIRed.pg !SBRed.bind !SBRed.vis !vis_trigger. des_ifs; cycle 1.
      { hexploit SCP; eauto. i; ss. rewrite H in Heq0. ss. }
      ired. iApply (isim_sget_eq _ _ _ (S := list_to_set (Mod.scopes md))).
      { rewrite elem_of_list_to_set.
        hexploit (SCP _ (subevent _ (SGet k))); eauto. intros HS.
        rewrite bool_decide_eq_true in HS. exact HS. }
      iFrame "IST". iIntros (?) "IST".
      cStepT. rewrite !SBRed.ret bind_ret_l. cByCoind CIH; et; iFrame.
  - depdes e.
    + rewrite !SBRed.bind !SBRed.vis !vis_trigger. des_ifs; bsimpl; ss.
      ired. rewrite MIRed.core SBRed.bind SBRed.vis vis_trigger. des_ifs.
      ired. cStepsT. cForceS _q. rewrite !SBRed.ret !bind_ret_l.
      cByCoind CIH; et; iFrame.
    + rewrite !SBRed.bind !SBRed.vis !vis_trigger. des_ifs; bsimpl; cycle 1.
      { rewrite bind_bind MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. cStepS; ss. }
      ired. rewrite MIRed.core SBRed.bind SBRed.vis vis_trigger. des_ifs.
      ired. cStepsS. cForceT _q. cStepsT. rewrite !SBRed.ret !bind_ret_l.
      cStepsT. cByCoind CIH; et; iFrame.
    + rewrite !SBRed.bind !SBRed.vis !vis_trigger. des_ifs; cycle 1.
      { s. rewrite bind_bind MIRed.core SBRed.bind SBRed.vis !vis_trigger. des_ifs. cStepS; ss. }
      ired. rewrite MIRed.core SBRed.bind SBRed.vis vis_trigger. des_ifs.
      ired. cStep. cStepsT. rewrite !SBRed.ret !bind_ret_l.
      cStepsT. cByCoind CIH; et; iFrame.
Qed.

End INLINE.
