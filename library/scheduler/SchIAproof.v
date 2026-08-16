From CRIS.common Require Import CRIS.
From CRIS.scheduler Require Import SchHeader SchI SchA.
From iris.algebra Require Import gmap_view frac_auth.

Module SchIA. Section sim.
  Context `{!crisG Γ Σ α β τ _S _I, !schGS}.
  Import SchA.
  Local Transparent SCH.

  Context (sp sp_user : specmap).
  Context (SchInSp : SchA.sp sp_user ⊤ ⊆ sp).
  Context (FunInSp : sp_user ⊆ sp).
  Context (ConcInSp : sp.2).

  Definition Ist (STATE : stateGS Σ) : iProp Σ :=
    (∃ ths tid_cur stid_cur,
        @points_to_src Σ STATE SchA.v_ths
          (((λ '(n, rv, _), (n, fst <$> rv : option SAny.t))
            <$> ths : list (nat * option SAny.t))↑) ∗
        @points_to_src Σ STATE SchA.v_tid tid_cur↑ ∗
        @points_to_tgt Σ STATE SchI.v_ths
          (((λ '(n, rv, _), (n, snd <$> rv : option SAny.t))
            <$> ths : list (nat * option SAny.t))↑) ∗
        @points_to_tgt Σ STATE SchI.v_tid tid_cur↑ ∗
        ⌜∃ ro_cur post_cur,
          ths !! tid_cur = Some (stid_cur, ro_cur, post_cur)⌝ ∗
        JoinAuth (list_to_map (imap (λ i RR, (i, to_agree RR)) ths.*2)) ∗
        TidAuth (list_to_map (imap pair ths.*1.*1)) ∗
        ([∗ list] i ↦ e ∈ ths,
          match e.1.2 with
          | None => True
          | Some (vrv, rv) =>
              JoinFrag (3/4) i e.2 ∗ interp_cond (e.2 vrv rv) ∨
              JoinFrag 1 i e.2
          end) ∗
        ([∗ list] i ↦ e ∈ ths.*1.*1, if decide (i = tid_cur) then emp else YIELD e))%I.

  Local Definition SchAMod := SchA.t sp_user sp.
  Local Definition SchIMod := SchI.t.

  Lemma simF_inner_spawn :
    ⊢ ISim.sim_fun open SchAMod SchIMod Ist (fid SchHdr._spawn).
  Proof using FunInSp SchInSp.
    cStartFunSim. rewrite /inner_spawn /SchI.inner_spawn.
    cStepS. destruct _q.
    cStepsS.
    iDestruct "ASM" as "[%stid [%pre [%postS [%fvarg [%varg [%fn [%mtid [[-> ->] ASM]]]]]]]]".
    iDestruct "ASM" as "[Spawn [W [TidFrag [Pre JoinFrag]]]]".

    cStepsS. cStepsT.
    iDestruct "Spawn" as "[%fsp [%Hfind Spawn]]". simpl_sp.
    iDestruct ("Spawn" with "[] [-IST JoinFrag]") as "> [% [% [%Hfsp [Pre Post]]]]".
    { iPureIntro; exists (stid, mtid, tt); split; done. }
    { unfoldPrePost; iFrame; eauto. }
    cForceS (FSpec_mk _ _ Hfsp); eauto. cForcesS. iFrame.

    cStepsS. cCall "IST" as (ret) "IST".

    (* after cCall - prepare for termination *)
    cStepsS. rename _q into vret.
    iMod ("Post" $! vret with "[ASM]") as "[W [[TidF [TID YIELD]] [% [% [[-> ->] Q]]]]]"; iFrame.
    cStepsS.

    cStepsT.
    iDestruct "IST" as (ths tid_cur stid_cur)
      "(THSS & TIDS & THST & TIDT & %Hmtid & JoinA & TidA & RET & Ys)".
    iApply wsim_sget_src; iFrame "THSS"; iIntros "THSS".
    iApply wsim_sget_tgt; iFrame "THST"; iIntros "THST".
    cStepsT. cStepsS.

    destruct Hmtid as [? [? Hmtid]].

    rewrite ?list_lookup_fmap Hmtid /=.
    cStepsS. cStepsT.

    iCombine "TidA TidF"
      gives %(av' & _ & _ & Hav' & _ & Hincl)%gmap_view_both_dfrac_valid_discrete_total.
    rewrite lookup_fmap_Some ?imap_fmap in Hav'; destruct Hav' as [? [? Hav']].
    eapply elem_of_list_to_map_2, elem_of_lookup_imap in Hav'.
    destruct Hav' as [mtid2 [[[stid2 ?] ?] [EQ Hmtid2]]]; symmetry in EQ; inv EQ.
    apply to_agree_included in Hincl; symmetry in Hincl; inv Hincl; ss; clarify.

    destruct (decide (tid_cur = mtid)); subst; cycle 1.
    { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]".
      { erewrite ?list_lookup_fmap, Hmtid2; ss. }
      des_ifs; by iPoseProof (YieldToken_both with "YIELD YIELD2") as "%".
    }
    rewrite Hmtid2 in Hmtid; inv Hmtid. rename stid_cur into stid.

    iCombine "JoinA JoinFrag"
      gives %(av' & _ & _ & Hav' & _ & Hincl)%gmap_view_both_dfrac_valid_discrete_total.
    eapply elem_of_list_to_map_2, elem_of_lookup_imap in Hav'.
    destruct Hav' as [mtid3 [postS' [EQ Hmtid3]]]; symmetry in EQ; inv EQ.
    apply to_agree_included in Hincl; symmetry in Hincl.
    rewrite list_lookup_fmap Hmtid2 in Hmtid3; ss. clarify.

    (* IST construction *)
    cIst "IST" with "[THSS TIDS THST TIDT JoinFrag JoinA TidA RET Ys Q]".
    { iExists (<[mtid := (stid, Some (svret, sret), _)]> ths), mtid, stid.
      iSplitL "THSS"; first (rewrite list_fmap_insert /=; iFrame).
      iSplitL "TIDS"; first iFrame.
      iSplitL "THST"; first (rewrite list_fmap_insert /=; iFrame).
      iSplitL "TIDT"; first iFrame.
      iSplit.
      { rewrite list_lookup_insert //.
        { iPureIntro; esplits; eauto. }
        eapply lookup_lt_is_Some; rewrite Hmtid2 //.
      }
      eapply elem_of_list_split_length in Hmtid2 as [ths1 [ths2 [-> Hlen]]].
      iSplitL "JoinA".
      { rewrite Hlen; rewrite insert_app_r_alt; last done.
        rewrite Nat.sub_diag /= ?fmap_app ?imap_app //=.
      }
      iSplitL "TidA".
      { rewrite Hlen; rewrite insert_app_r_alt; last done.
        rewrite Nat.sub_diag /= ?fmap_app ?imap_app //=.
      }
      iSplitL "RET Q JoinFrag".
      { rewrite Hlen insert_app_r_alt; last done.
        iPoseProof (big_sepL_insert_acc _ _ mtid with "RET") as "[_ RET]"; ss.
        { rewrite Hlen lookup_app_Some; right; split; ss; rewrite Nat.sub_diag //=. }
        iPoseProof ("RET" $! (stid, Some (svret, sret), postS) with "[Q JoinFrag]") as "RET".
        { rewrite /JoinFrag Hlen /=; iLeft; iFrame. }
        rewrite Nat.sub_diag insert_app_r_alt Hlen // Nat.sub_diag //=.
        assert (postS' = postS); last subst postS'; auto.
        { extensionalities t1 t2; rewrite (Hincl t1 t2) //. }
      }
      rewrite Hlen insert_app_r_alt // Nat.sub_diag /=.
      rewrite ?fmap_app ?fmap_cons /=. iFrame.
    }

    (* Coinduction on yield loop *)
    rewrite !/Sch.terminate /ccallU. unseal SCH.
    clear Hmtid2.
    iApply wsim_reset.
    cCoind CIH g __ with stid. iIntros "[W [TidF [TID [YIELD IST]]]] /=".
    unfoldIterCS. unfoldIterCT.

    cStepsS. simpl_sp.
    cForceS (stid, mtid, tt). cForceS (tt↑). cStepsS.
    iApply wsim_guarantee_src; iFrame "W TidF TID YIELD"; iSplit; eauto.

    cStepsT. cCall "IST" as (ret) "IST". cStepsS.
    iDestruct "ASM" as "[TidF [-> ->]]".
    cStepsT.
    cByCoind CIH; eauto.
    iPoseProof (winv_split_empty with "WINV") as "[I E]".
    iFrame; iDestruct "TidF" as "[$ [$ $]]".
  (*SLOW*)Qed.

  Lemma simF_spawn :
    ⊢ ISim.sim_fun open SchAMod SchIMod Ist (fid SchHdr.spawn).
  Proof using FunInSp SchInSp ConcInSp.
    cStartFunSim. rewrite /spawn /SchI.spawn.

    (* preprocess source precondition *)
    cStepS. destruct _q as [user_pre user_post]. cStepsS.
    iDestruct "ASM" as "[% [% [% [[-> ->] [Spawn ASM]]]]]".
    cStepsS. cStepsT.

    iDestruct "IST" as (ths tid_cur stid_cur)
      "(THSS & TIDS & THST & TIDT & %Hmtid & JoinA & TidA & RET & Y)".
    iApply wsim_sget_src; iFrame "THSS"; iIntros "THSS".
    iApply wsim_sget_tgt; iFrame "THST"; iIntros "THST".
    cStepsS. cStepsT. simpl_sp.
    rewrite ConcInSp.

    (* System spawn precondition *)
    cForceS ((fn, farg)↑). cStepsS.
    cStepsT. cSpawn as (tid_new). cStepsT.
    cStepsS. rewrite ?length_fmap /=. set (mtid_new := length ths).
    cForceS (). cStepsS.

    iMod (own_update with "JoinA") as "[JoinA JoinF]".
    { etrans; first eapply (gmap_view_alloc _ mtid_new (DfracOwn 1) (to_agree user_post)); ss.
      { rewrite -not_elem_of_list_to_map fmap_imap; intros Hcont%elem_of_lookup_imap.
        subst mtid_new; destruct Hcont as [? [? [? Hcont]]]; ss; subst.
        eapply lookup_lt_Some in Hcont; rewrite length_fmap in Hcont; lia.
      }
      refl.
    }
    iMod (own_update with "TidA") as "[TidA TidF]".
    { etrans; first eapply (gmap_view_alloc _ mtid_new (DfracOwn 1) (to_agree tid_new)); ss.
      { apply not_elem_of_dom. rewrite dom_fmap. apply not_elem_of_dom.
        rewrite -not_elem_of_list_to_map ?imap_fmap fmap_imap; intros Hcont%elem_of_lookup_imap.
        subst mtid_new; destruct Hcont as [? [? [? Hcont]]]; ss; subst.
        eapply lookup_lt_Some in Hcont; lia.
      }
      refl.
    }
    rewrite -{3}Qp.three_quarter_quarter -dfrac_op_own -{2}(agree_idemp (to_agree _)).
    iDestruct "JoinF" as "[JoinF1 JoinF2]".
    cForceS. iSplitL "ASM JoinF1 TidF Spawn".
    { iIntros "???"; iFrame "JoinF1 Spawn TidF".
      iExists _, _; iFrame; iPureIntro; esplits; eauto.
    }
    cStepsS. cForceS (mtid_new↑). cForceS. iSplitL "JoinF2".
    { iExists _; iSplit; eauto. }
    cStep. iSplit; eauto.

    iExists (ths ++ [(tid_new, None, user_post)]), _, _.
    iSplitL "THSS"; first (rewrite fmap_app /=; iFrame).
    iSplitL "TIDS"; first iFrame.
    iSplitL "THST"; first (rewrite fmap_app /=; iFrame).
    iSplitL "TIDT"; first iFrame.
    iSplitR.
    { des. iPureIntro. rewrite ?fmap_app /=. esplits; eauto. rewrite lookup_app Hmtid //. }
    iSplitL "JoinA".
    { rewrite -list_to_map_snoc.
      { rewrite fmap_app imap_app /= Nat.add_0_r length_fmap; subst mtid_new; done. }
      subst mtid_new; rewrite fmap_imap.
      intros [? [? [Heq Hin]]]%elem_of_lookup_imap; ss; rewrite -Heq in Hin.
      eapply lookup_lt_Some in Hin; rewrite length_fmap in Hin; lia.
    }
    iSplitL "TidA".
    { rewrite /TidAuth ?fmap_app /= imap_app /= ?length_fmap Nat.add_0_r list_to_map_snoc.
      { rewrite fmap_insert //. }
      subst mtid_new; rewrite fmap_imap.
      intros [? [? [Heq Hin]]]%elem_of_lookup_imap; ss; rewrite -Heq in Hin.
      eapply lookup_lt_Some in Hin; rewrite ?length_fmap in Hin; lia.
    }
    iSplitL "RET".
    { rewrite big_sepL_app /=; iFrame; done. }
    by rewrite ?fmap_app big_sepL_app /=; des_ifs; iFrame.
  (*SLOW*)Qed.

  Lemma simF_yield :
    ⊢ ISim.sim_fun open SchAMod SchIMod Ist (fid SchHdr.yield).
  Proof using FunInSp SchInSp ConcInSp.
    cStartFunSim. rewrite /yield /SchI.yield /SchI.choose_index.

    cStepS. destruct _q as [[stid mtid] ?]. cStepsS.
    iDestruct "ASM" as "[[Tid [TID YIELD]] [-> ->]]".
    iDestruct "IST" as (ths tid_cur stid_cur)
      "(THSS & TIDS & THST & TIDT & %Htid_cur & JoinA & TidA & RET & Ys)".
    destruct Htid_cur as [ro_cur [post_cur Htid_cur]].
    cStepsT. cStepsS.
    rewrite ConcInSp.

    (* GetTid reasoning *)
    cForceS stid; cForceS; iFrame "TID". cStepsS. cStepsT.
    cStep. cStepsS. cStepsT. iDestruct "ASM" as "[-> TID]".
    iPoseProof (Tid_Auth_Tid with "[TidA Tid]") as "%Hmtid"; first iFrame.
    eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
    destruct Hmtid as [? [? [EQ Hmtid]]]; symmetry in EQ; inv EQ.
    destruct (decide (tid_cur = mtid)); subst; cycle 1.
    { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
      case_decide; clarify; by iPoseProof (YieldToken_both with "YIELD YIELD2") as "%".
    }
    rewrite ?list_lookup_fmap Htid_cur in Hmtid; inv Hmtid.

    rewrite ?list_lookup_fmap Htid_cur /=; case_decide; subst; clarify.

    (* Choose the next tid *)
    cStepsT. cStepsS.
    destruct _q as [[tidn stidn] Htidn]. unshelve cForceS (exist _ (tidn, stidn) _); last cStepS.
    { ss. revert Htidn; rewrite ?list_lookup_fmap; destruct (ths !! tidn) as [[[? ?] ?]|]; ss. }
    cStepsS. cStepsT.

    (* HoareYield *)
    rewrite ConcInSp. cStepsS.
    rewrite ?list_lookup_fmap /= in Htidn.
    iAssert (YIELD stidn ∗
        [∗ list] i ↦ e ∈ ths.*1.*1, if decide (i = tidn) then emp else YIELD e)%I
      with "[YIELD Ys]" as "[YIELD Ys]".
    { destruct (decide (mtid = tidn)).
      { subst; destruct (ths !! tidn) as [[[? ?] ?]|]; ss; clarify. iFrame. }
      iPoseProof (big_sepL_delete _ ths.*1.*1 mtid with "[Ys YIELD]") as "Ys"; eauto.
      { rewrite ?list_lookup_fmap Htid_cur //. }
      { ss. instantiate (1:=λ _ i, YIELD i). iFrame. }
      rewrite big_sepL_delete; try iFrame.
      rewrite ?list_lookup_fmap; destruct (ths !! tidn) as [[[? ?] ?]|]; ss.
    }
    iApply wsim_unfold; iIntros "W".
    cForcesS. iFrame "W TID YIELD". cStepsS.
    iApply wsim_yield; iFrame. iSplit.
    { destruct (ths !! tidn) as [[[? ?] ?]|] eqn : ?; ss; clarify.
      iExists _; iPureIntro; esplits; eauto.
    }
    iIntros "IST".

    cStepsS. iDestruct "ASM" as "[TID [YIELD WINV]]".
    cForcesS. iFrame. iSplit; eauto.
    cStep. iFrame. done.
  (*SLOW*)Qed.

  Lemma simF_join :
    ⊢ ISim.sim_fun open SchAMod SchIMod Ist (fid SchHdr.join).
  Proof using FunInSp SchInSp.
    cStartFunSim. rewrite /join /SchI.join.

    cStepS. destruct _q as [[stid mtid] post]. cStepsS.
    iDestruct "ASM" as "[TID [%tid [[-> ->] JoinF]]]".

    cStepsT. cStepsS. iApply wsim_reset.
    cCoind CIH g' __ with tid. iIntros "[IST [Tid JoinF]]".
    unfoldIterCS; unfoldIterCT.

    iDestruct "IST" as (ths tid_cur stid_cur)
      "(THSS & TIDS & THST & TIDT & %Hmtid & JoinA & TidA & RET & Ys)".
    cStepsS. cStepsT.

    rewrite ?list_lookup_fmap.
    destruct (ths !! tid) as [[[stid_join [[rv vrv]|]] post2]|] eqn : Htid.
    { cStepsS. cStepsT.
      iPoseProof (big_sepL_lookup_acc _ _ tid with "RET") as "[J RET]"; eauto; ss.
      iDestruct "J" as "[[JoinF2 Post] | JoinF2]"; cycle 1.
      { iExFalso; iCombine "JoinF" "JoinF2" gives %[WF _]%gmap_view_frag_op_valid.
        rewrite dfrac_op_own // in WF.
      }
      iCombine "JoinF" "JoinF2" gives %[_ WF%to_agree_op_valid]%gmap_view_frag_op_valid.
      iCombine "JoinF" "JoinF2" as "JoinF"; rewrite Qp.quarter_three_quarter.
      iEval (rewrite WF agree_idemp) in "JoinF".
      iPoseProof ("RET" with "[JoinF]") as "RET"; first (iRight; iFrame).
      cForcesS. iEval (rewrite -WF) in "Post". iFrame "Tid Post".
      iSplit; eauto.
      cStep. iSplit; eauto.
      iFrame. des; iExists _; iPureIntro; esplits; eauto.
    }
    { cStepsT. cStepsS. simpl_sp.
      cForceS (stid, mtid, tt). cStepsS. cForceS. cForceS. iFrame "Tid". iSplit; eauto.
      cStepsS.
      cCall "THSS TIDS THST TIDT JoinA TidA RET Ys" as (ret) "IST".
      { iFrame. des; iExists _; iPureIntro; esplits; eauto. }
      cStepsS. cStepsT.
      iDestruct "ASM" as "[Tid [-> ->]]".
      cStepsT. cStepsS.
      cByCoind CIH. iFrame.
    }
    { iExFalso; iCombine "JoinA" "JoinF" gives %WF%gmap_view_both_dfrac_valid_discrete_total.
      destruct WF as [? [_ [_ [[? [? [EQ Hcont]]]%elem_of_list_to_map_2%elem_of_lookup_imap _]]]].
      inv EQ. rewrite list_lookup_fmap Htid // in Hcont.
    }
  (*SLOW*)Qed.

  Lemma sim :
    SchA.init_cond ⊢ ISim.t open SchAMod SchIMod Ist.
  Proof using FunInSp SchInSp ConcInSp.
    cStartModSim.
    { rewrite /init_cond.
      iDestruct "INIT" as "[TidA JoinA]".
      iEval (rewrite /state_init_src /=) in "SRC".
      iEval (rewrite /state_init_tgt /=) in "TGT".
      assert (SL : state_slice ({["sch"]} : gset string)
          {[SchI.v_ths # ([(0, None)] : thpool)↑; SchI.v_tid # 0↑]} =
          {[SchI.v_ths := ([(0, None)] : thpool)↑; SchI.v_tid := 0↑]}).
      { apply map_eq. intros k. rewrite state_slice_lookup.
        destruct (decide (k = SchI.v_ths)); subst; simpl_map.
        - case_decide; done.
        - destruct (decide (k = SchI.v_tid)); subst; simpl_map.
          + case_decide; done.
          + repeat case_decide; done.
      }
      iEval (rewrite right_id_L SL) in "SRC".
      iEval (rewrite right_id_L SL) in "TGT".
      iDestruct "SRC" as "[SRC _]".
      iEval (rewrite big_sepM_insert) in "SRC"; last simpl_map.
      iDestruct "SRC" as "[THSS TIDS]".
      iDestruct "TGT" as "[TGT _]".
      iEval (rewrite big_sepM_insert) in "TGT"; last simpl_map.
      iDestruct "TGT" as "[THST TIDT]".
      iEval (rewrite big_sepM_singleton) in "TIDS".
      iEval (rewrite big_sepM_singleton) in "TIDT".
      iExists [(0, None, λ _ _, existT 0 emp%SAT)], 0, 0.
      iFrame.
      iSplit; first (iPureIntro; eexists None, (λ _ _, existT 0 emp%SAT); done).
      rewrite !big_sepL_singleton /=. iFrame. iSplit; done.
    }
    { iApply simF_inner_spawn. }
    { iApply simF_spawn. }
    { iApply simF_yield. }
    { iApply simF_join. }
  Qed.
End sim.

Section ctxr.
  Context `{!crisG Γ Σ α β τ _S _I, _SCH: !schGS}.

  Lemma ctxr sp sp_user
        (SchInGlobal : SchA.sp sp_user ⊤ ⊆ sp)
        (UserInGlobal : sp_user ⊆ sp)
        (ConcInGlobal : sp.2) :
    SchA.init_cond ⊢ ctx_refines SchI.t (SchA.t sp_user sp).
  Proof.
    etrans; first (eapply sim; eauto).
    eapply main_adequacy.
  Qed.
End ctxr.
End SchIA.
