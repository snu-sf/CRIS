From CRIS.simulations.gsim Require Import GSimAux.
From CRIS.simulations.msim Require Import MSimCommon ISim ISimRefl WSim WSimFacts Tactics TacticsInit.

Section PREPARE_SIM.

  Context `{!crisG Γ Σ α β τ _S _I}.

  Theorem prepare_sim (spt sps: specmap) (md: SMod.t)
    (SP1: ∀ fn arg (msk: emask) p, md.(SMod.fnsems) !! fn = Some (Some (msk,p)) →
          ∀ (fc: string), spt.1 !! (funid fc) ≠ sps.1 !! (funid fc) →
          msk _ (subevent _ (Call fc arg)) = false ∧
          msk _ (subevent _ (Spawn fc arg)) = false)
    (SPS: sps.2 = true)
    (SP2: spt.2 = false →
          ∀ fn (msk: emask) p, md.(SMod.fnsems) !! fn = Some (Some (msk,p)) →
          ∀ T (e: callE T), msk_sys _ (subevent _ e) = true → msk _ (subevent _ e) = false)
    :
    ⊢ ISim.t open (SMod.to_mod_cancel sps md) (SMod.to_mod spt md) (IstEq (SMod.to_mod spt md)).
  Proof.
    cStartModSim; et.
    iApply (state_eq_init_same with "SRC TGT").

    { destruct Hwf as [Hwf _]. rewrite /Mod.fnsems in Hwf |- *; ss.
      ii. specialize (Hwf i x). revert Hwf H. rewrite !lookup_fmap. i.
      destruct (SMod.fnsems md !! i) eqn: Emd; ss. depdes H. destruct o; ss. et. }

    rewrite /ISim.sim_fun.
    iIntros (STATE).
    iIntros "%WFS %WFT" (fs) "%Hfs".
    simpl_map. des_ifs; ss.
    rewrite /SMod.to_mod_cancel /SMod.to_mod /Mod.fnsems
      /sandbox_fnsemmap !lookup_fmap in Hfs |- *.
    do 2 (rewrite fmap_Some in Hfs; des); subst.
    destruct x0 as [[msk [fspo fbd]]|]; ss.
    depdes Hfs0. rewrite Hfs. s. clarify.
    hexploit (SMod.well_scoped_fns md fn (msk, (fspo, fbd))).
    { rewrite lookup_omap Hfs //. }
    intros [HPUT HGET].
    iExists _. iSplit; first done.
    rewrite /isim_fsem.
    iIntros "!#" (arg) "IST"; iApply wsim_isim;
    rewrite /SB.sandbox_body;
    simpl fst; simpl snd; rewrite /SModTr.trans_fnsem /SModTr.HoareFun /cfunU /cfunN.
    iStopProof.
    match goal with
      |- ?P ⊢ wsim ?fe_s ?fe_t ?Ist ?E ?g _ _ ?rel _ _ _ _ =>
      assert (HYP: ∀ ps pt itr, P ⊢ wsim fe_s fe_t Ist E g _ _ rel ps pt
              (⇓sb(msk) (SModTr._trans sps (Some msk) itr))
              (⇓sb(msk) (SModTr._trans spt None itr)))
    end; cycle 1.
    {
      iIntros "IST". destruct fspo; cycle 1.
      { cStepsS. cStepsT. iStopProof. eapply HYP. }
      cStepsS. cStepsT. des_if; [| cStepsS; ss].
      cStepsS. case_match; [| cStepsS; ss].
      cStepsS. case_match; [| cStepsS; ss].
      cStepsS. cForceT _q. cStepsT. rewrite H. cStepsT.
      cForcesT. cStepsT. erewrite H0. cForcesT. iFrame.
      cStepsT. cBind _ "IST" as (??) "Q".
      { iStopProof. eapply HYP. }
      iDestruct "Q" as "[-> IST]".
      cStepsT. cStepsS. des_if; [| cStepsS; ss].
      cStepsT. bsimpl. cStepsT. cForceS. cStepsS. bsimpl. cForceS. iFrame.
      cStep. iSplit; first done. iFrame.
    }

    iIntros (???) "IST".
    cCoind CIH g __ with ps pt itr. iIntros "IST".
    assert (CASE := case_itrH itr); des; subst.
    - rewrite !SRed._ret. cStep. iSplit; first done. iFrame.
    - rewrite !SRed._tau. cStepsS. cStepsT.
      cByCoind CIH; try et. iFrame "IST WINV".
    - rewrite !SRed._bind !SRed._ag. cStepsS. cStepsT. des_if; [|cStepsS; ss].
      cStepsS. cForceT. iFrame. cStepsT.
      cByCoind CIH; try et. iFrame "IST WINV".
    - rewrite !SRed._bind !SRed._ag. cStepsS. cStepsT. des_if; [|cStepsS; ss].
      cStepsS. cForceT. iFrame. cStepsT.
      cByCoind CIH; try et. iFrame "IST WINV".
    - rewrite !SRed._bind !SRed._ag. cStepsS. cStepsT. des_if; [|cStepsS; ss].
      cStepsT. cForceS. iFrame. cStepsS.
      cByCoind CIH; try et. iFrame "IST WINV".
    - destruct c.
      + rewrite !SRed._bind !SRed._call. unfold SModTr.HoareCall. cStepsS. cStepsT.
        case_match eqn: Lsps; cycle 1.
        { case_match eqn: Lspt.
          { hexploit (SP1 fn args); et.
            { erewrite Lsps, Lspt. et. }
            intros [Lmsk _]. cStepsS. rewrite Lmsk. cStepsS. ss.
          }
          cStepsS. cStepsT. des_if; [|cStepsS; ss].
          cCall "IST" as (?) "IST". cStepsS. cStepsT.
          cByCoind CIH; try et. iFrame "IST WINV".
        }
        destruct (spt.1 !! funid fn0) eqn: Lspt; cycle 1.
        { hexploit (SP1 fn args); et.
          { erewrite Lsps, Lspt. et. }
          intros [Lmsk _]. rewrite Lmsk. cStepsS. bsimpl. cForceS (). cStepsS. bsimpl.
          cForcesS. cStepsS. bsimpl. cForcesS. iSplit; et. cStepsS. rewrite Lmsk. cStepsS. ss.
        }
        destruct (classic (f = f0)) eqn: Ef_f0; cycle 1.
        { hexploit (SP1 fn args); et.
          { erewrite Lsps, Lspt. ii. depdes H. et. }
          intros [Lmsk _]. rewrite Lmsk.
          cStepsS. bsimpl. cForceS (). cStepsS. bsimpl. cForcesS. cStepsS.
          bsimpl. cForcesS. iSplit; et. cStepsS. rewrite Lmsk. cStepsS. ss.
        }
        subst. case_match eqn: Lmsk; cycle 1.
        { cStepsS. bsimpl. cForceS (). cStepsS. bsimpl. cForcesS. cStepsS.
          bsimpl. cForcesS. iSplit; et. cStepsS. rewrite Lmsk. cStepsS. ss.
        }
        cNormS. cStepsT. bsimpl. cStepsT. cForceS _q. cStepsS. bsimpl.
        cStepsT. cForceS _q0. cStepsS. bsimpl.
        cStepsT. cForceS. iFrame. cStepsS. bsimpl. des_if; [|cStepsS; ss].
        cCall "IST" as (?) "IST". cStepsS. cStepsT. des_if; [|cStepsS; ss].
        cStepsS. cForceT _q1. cStepsT. des_if; [|cStepsS; ss].
        cStepsS. cForceT. iFrame. cStepsT.
        cByCoind CIH; try et. iFrame "IST WINV".
      + rewrite !SRed._bind !SRed._spawn. cStepsS. cStepsT.
        rewrite /SModTr.HoareSpawn !SPS.
        destruct (classic (spt.1 !! funid fn0 = sps.1 !! funid fn0)) eqn: EQf_f0; cycle 1.
        { hexploit (SP1 fn args); et.
          intros [_ Lmsk]. destruct spt.2.
          - cStepsS. bsimpl. cForceS args. cStepsS. rewrite Lmsk. cStepsS. ss.
          - cStepsS. bsimpl. cForceS args. cStepsS. erewrite SP2; et. cStepsS. ss.
        }
        destruct spt.2; cycle 1.
        { cStepsS. bsimpl. cForceS args. cStepsS. erewrite SP2; et. cStepsS. ss. }
        cStepsS. cStepsT. bsimpl. cStepsT. cForceS _q. cStepsS. des_if; [|cStepsS; ss].
        cStep. cStepsS. cStepsT. des_if; [|cStepsS; ss].
        cStepsS. cForceT. iFrame. cStepsT. bsimpl.
        cStepsT. rewrite -e. cForceS _q0. bsimpl.
        cStepsT. cForceS. iFrame. cStepsS.
        cByCoind CIH; try et. iFrame "IST WINV".
      + rewrite !SRed._bind !SRed._yield. cStepsS. cStepsT. rewrite /SModTr.HoareYield.
        rewrite SPS. s. destruct (msk _ _) eqn: Emsk; cycle 1.
        { cStepsS. bsimpl. cForceS tid. cStepsS. bsimpl.
          cForceS. iSplit; et. cStepsS. erewrite Emsk; et. cStepsS. ss.
        }
        destruct spt.2 eqn: Espt; cycle 1.
        { erewrite SP2 in Emsk; et; ss. }
        cStepsS. cStepsT. des_if; [|cStepsS; ss].
        cStepsT. cForceS _q. cStepsS. bsimpl.
        cStepsT. cForcesS. iFrame. cStepsS. des_if; [|cStepsS; ss].
        cYield "IST" "IST". cStepsS. cStepsT. des_if; [|cStepsS; ss].
        cStepsS. cForceT. iFrame. cStepsT.
        cByCoind CIH; try et. iFrame "IST WINV".
      + rewrite !SRed._bind !SRed._gettid. cStepsS. cStepsT. rewrite /SModTr.HoareGetTid.
        rewrite SPS. s. destruct (msk _ _) eqn: Emsk; cycle 1.
        { cStepsS. bsimpl. cForceS 0. cStepsS. bsimpl.
          cForceS. iSplit; et. cStepsS. erewrite Emsk; et. cStepsS. ss.
        }
        destruct spt.2 eqn: Espt; cycle 1.
        { erewrite SP2 in Emsk; et; ss. }
        cStepsS. cStepsT. bsimpl.
        cStepsT. cForceS _q. cStepsS. bsimpl.
        cStepsT. cForcesS. iFrame. cStepsS. des_if; [|cStepsS; ss].
        cStep. cStepsS. cStepsT. des_if; [|cStepsS; ss].
        cStepsS. cForceT. iFrame. cStepsT.
        cByCoind CIH; try et. iFrame "IST WINV".
    - rewrite !SRed._bind !SRed._pg. destruct s as [k v|k].
      + cStepsS. cStepsT. des_ifs; [|cStepsS; ss].
        cStepsS. cStepsT.
        iApply (wsim_sput_eq _ _
          (S := list_to_set (Mod.scopes (SMod.to_mod spt md)))).
        { rewrite elem_of_list_to_set /=. eapply HPUT.
          rewrite orb_false_r in Heq. exact Heq. }
        iFrame "IST". iIntros "IST".
        cStepsS. cStepsT.
        cByCoind CIH; try et. iFrame "IST WINV".
      + cStepsS. cStepsT. des_ifs; [|cStepsS; ss].
        cStepsS. cStepsT.
        iApply (wsim_sget_eq _ _
          (S := list_to_set (Mod.scopes (SMod.to_mod spt md)))).
        { rewrite elem_of_list_to_set /=. eapply HGET.
          rewrite orb_false_r in Heq. exact Heq. }
        iFrame "IST". iIntros (?) "IST".
        cStepsS. cStepsT.
        cByCoind CIH; try et. iFrame "IST WINV".
    - rewrite !SRed._bind !SRed._core. destruct e.
      + cStepsS. cStepsT. des_if; [|cStepsS; ss].
        cStepsT. cForceS _q. cStepsS.
        cByCoind CIH; try et. iFrame "IST WINV".
      + cStepsS. cStepsT. des_if; [|cStepsS; ss].
        cStepsS. cForceT _q. cStepsT.
        cByCoind CIH; try et. iFrame "IST WINV".
      + cStepsS. cStepsT. des_if; [|cStepsS; ss].
        cStep. cStepsS. cStepsT.
        cByCoind CIH; try et. iFrame "IST WINV".
  Qed.

End PREPARE_SIM.
