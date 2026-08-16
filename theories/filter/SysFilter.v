From CRIS.common Require Import Common.
From CRIS.simulations.msim Require Import
  ISim ISimFacts WSim WSimFacts Tactics TacticsCommon TacticsInit.
From CRIS.simulations.gsim Require Import GSim GSimAdequacy GSimTactics GSimAux.
From CRIS.common Require Export ConcRA.
From CRIS.modules Require Export LMod Mod SMod.
From CRIS.simulations.ctxrefine Require Export CtxRefine CtxRefineFacts ClosedAdequacy MainAdequacy.
From stdpp Require Import base list.

Module SFilter. Section SFilter.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition msk_filter_out (msk : emask) : emask := λ X e,
    negb (msk_sys _ e) && msk X e.

  Program Definition filter (m : Mod.t) : Mod.t := {|
    Mod.scopes := m.(Mod.scopes);
    Mod.fnsems :=
      (λ (x : option _), map_fst (msk_filter_out) <$> x) <$> m.(Mod.fnsems);
    Mod.initial_st := m.(Mod.initial_st)
  |}.
  Next Obligation. i; eapply Mod.sorted_scopes. Qed.
  Next Obligation.
    rewrite /msk_filter_out.
    intros m i [msk x]; rewrite lookup_omap ?lookup_fmap /Mod.fnsems => ?.
    destruct m; ss.
    destruct (fnsems !! i) as [[[??]|]|] eqn : ?; ss; clarify; ss.
    eapply (well_scoped_fns i (_, _)); rewrite lookup_omap Heqo //=.
  Qed.
  Next Obligation. intros m; destruct m; ss. Qed.
  Next Obligation. intros m; destruct m; ss. Qed.

  Lemma sim_filter_intro (m : Mod.t) :
    ⊢ ISim.t open (filter m) m (IstEq m).
  Proof using.
    rewrite /ISim.t. iSplit.
    { rewrite /ISim.init_ist. iIntros (Hwf). iSplit.
      { done. }
      iIntros (STATE) "SRC TGT".
      iApply (state_eq_init_same with "SRC TGT"). }
    rewrite /ISim.sim_funs. iIntros (Hwf). iSplit.
    { iPureIntro. split.
      - ii. rr. destruct x; et.
        exfalso. rewrite lookup_fmap in H. destruct (_ !! _) eqn: mi; ss.
        eapply Hwf in mi. rr in mi. des; subst. ss.
      - rewrite /filter /Mod.fnsems /= dom_fmap. done. }
    iIntros (fn) "%Hfn".

    rewrite /ISim.sim_fun ?lookup_fmap.
    iIntros (STATE).
    iIntros "%WFS %WFT" (fs) "%Hfs".
    destruct (_ !! _) as [[[msk bd]|]|] eqn : Ht; ss.
    hexploit (Mod.well_scoped_fns m fn (msk, bd)).
    { rewrite lookup_omap Ht //. }
    intros [HPUT HGET].
    clear Ht.
    clarify. iExists _. iSplit; first done.
    rewrite /isim_fsem.
    iIntros "!#" (arg) "IST". iApply wsim_isim.
    generalize false at 1 as ps; i. generalize false at 1 as pt; i.
    rewrite /SB.sandbox_body /=. generalize (bd arg) as itr; i. clear arg.
    cCoind CIH g0 __ with itr ps pt. iIntros "IST".

    assert (CASE:= case_itrH itr). des; subst; s.
    - cStep. iSplit; first done. iFrame.
    - cStepsS. cStepsT. cByCoind CIH; try et.
      iFrame "IST WINV".
    - cStepsS; ss.
      case_match; cStepsS; ss.
      cStepsT; case_match; ss; cForceT; iFrame; cStepsT.
      cByCoind CIH; try et. iFrame.
    - cStepS. cForceT; iFrame. cNormT.
      cByCoind CIH; try et. iFrame.
    - cStepT. cForceS; iFrame. cNormS.
      cByCoind CIH; try et. iFrame.
    - destruct c; s; cStepsS; try case_match; try case_bool_decide; cStepsS; ss.
      cStepsT. rewrite H.
      cStepsT. cCall "IST" as (ret) "IST"; cStepsS; cStepsT.
      cByCoind CIH; try et. iFrame.
    - destruct s as [k v|k]; cStepsS; cStepsT;
        case_match; cStepsS; ss; cStepsT.
      { iApply (wsim_sput_eq _ _ (S := list_to_set (Mod.scopes m))).
        { rewrite elem_of_list_to_set. eapply HPUT. eapply H. }
        iFrame "IST". iIntros "IST".
        cNormS; cNormT; cByCoind CIH; try et. iFrame. }
      { iApply (wsim_sget_eq _ _ (S := list_to_set (Mod.scopes m))).
        { rewrite elem_of_list_to_set. eapply HGET. eapply H. }
        iFrame "IST". iIntros (?) "IST".
        cNormS; cNormT; cByCoind CIH; try et. iFrame. }
    - destruct e; cNormS; cNormT.
      { cStepT. cForceS _q. cByCoind CIH; et. iFrame. }
      { case_match; cStepsS; ss. cForceT _q. cByCoind CIH; et. iFrame. }
      { case_match; cStepsS; ss. cStep. cByCoind CIH; et. iFrame. }
  Qed.

  Theorem smod_filter_intro sp md:
    ⊢ ctx_refines
      (SMod.to_mod sp md)
      (SMod.to_mod sp (SMod.filter (msk_filter_out) md)).
  Proof.
    evar_at_last_1.
    unfold bi_emp_valid.
    etrans; [eapply sim_filter_intro|eapply main_adequacy].
    f_equal. eapply Mod.t_eq; et. destruct md.
    rewrite /filter /SMod.filter /SMod.to_mod /SMod.fnsems /Mod.fnsems //.
    rewrite -!map_fmap_compose. f_equal. extensionality x.
    destruct x as [[msk [fsp fbd]]|]; ss. f_equal. f_equal.
    extensionalities T e. rewrite /msk_filter_out /msk_and.
    destruct e; try rewrite andb_diag; ss.
    destruct s; try rewrite andb_diag; ss.
    destruct c; try rewrite andb_diag; ss; destruct (msk _ _); ss.
  Qed.

  Lemma filter_masked {T} (m: SMod.t) fn msk p (e: callE T)
    (LU: SMod.fnsems (SMod.filter SFilter.msk_filter_out m) !! fn = Some (Some (msk, p)))
    (SYS: msk_sys _ (subevent _ e) = true)
    :
    msk _ (subevent _ e) = false.
  Proof.
    eapply lookup_fmap_Some in LU. des. destruct x as [[msk0 p0]|]; ss.
    depdes LU. destruct e; ss; rewrite /msk_and //=; bsimpl; et.
  Qed.

  Lemma filter_cancellable (m: SMod.t)
    (CANCEL: SMod.cancellable m)
    :
    SMod.cancellable (SMod.filter msk_filter_out m).
  Proof.
    ii. rewrite lookup_fmap_Some in H. des. ss.
    destruct x0 as [[? [? ?]]|]; ss; subst; et.
    eapply CANCEL in H0. unfold img_msk, call_msk, msk_and, msk_filter_out in *.
    des; esplits; i; s.
    - rewrite H0; et.
    - rewrite H2; et.
    - rewrite H3; et.
    - rewrite H4; et.
    - rewrite H5; et.
    - hdes. rewrite !(H6 _ _ y) !(H7 _ _ y). et.
  Qed.
  
End SFilter. End SFilter.
