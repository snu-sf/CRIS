From CRIS.modules Require Import LMod LModTr.
From CRIS.simulations.gsim
  Require Import GSim GSimAdequacy GSimTactics GSimAux GSimMod.
From CRIS.cancellation Require Import MInline ElimRel.
From CRIS.cancellation Require Import
  CancelCore
  CancelPG
  CancelAG
  CancelSpawn
  CancelPre
  CancelPost
  CancelYield
  CancelGetTid.

Section CANCEL_MAIN.

  Context `{!crisG Γ Σ α β τ _S _I}.

  Lemma cancel_elim md (r_i r_s r_t: Σ) rs_diff srcs tgts cid st ps pt
    (WFS: SMod.cancellable md)
    (REL: Forall3i (thread_rel (SMod.sp_from md) cid) rs_diff srcs tgts)
    (WFR: ✓ r_s) (WFST: map_Forall (const is_Some) st)
    (RS: Own r_s ⊢ |==> ([∗ list] i ∈ rs_diff, Own i) ∗ Own r_t ∗
          TIDAUTH cid ∗ YIELDAUTH (length rs_diff))
    :
    gsim cancel_eq ps pt
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
                (SMod.to_mod ∅ (SMod.cancel md))) r_i))) (cid, srcs))
        (st, r_s))
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
                (SMod.to_mod_cancel (SMod.sp_from md) md)) r_i))) (cid, tgts))
        (st, r_t)).
  Proof using.
    ginit. move WFS at top. (* move WF at top. *)
    revert_until r_i. gcofix CIH. i.
    destruct (decide (cid < length srcs)) as [Hcid|]; cycle 1.
    { giter_s. s. rewrite (proj2 (lookup_ge_None srcs cid)); last lia.
      gstep_s. gcNormS. gstep_s. i; ss.
    }
    inversion REL as [Hlenxy [Hlenyz Hrel]].
    exploit (@Forall3i_nth _ _ _ cid); eauto; try lia; clear REL.
    intros [r_diff [i_s [i_t [Hdiff [Hs [Ht Hcidrel]]]]]]; ss.

    assert (Hkey :
      ∀ itr_s itr_t st (r_s r_t: Σ) r_diff,
      ✓ r_s → map_Forall (const is_Some) st →
      (Own r_s ⊢ |==> ([∗ list] i ∈ <[cid := r_diff]> rs_diff, Own i) ∗ Own r_t ∗
        TIDAUTH cid ∗ YIELDAUTH (length (<[cid := r_diff]> rs_diff))) →
      cid < List.length srcs →
      thread_rel (SMod.sp_from md) cid cid r_diff itr_s itr_t →
      gpaco7 _gsim (cpn7 _gsim) bot7 r (lstateT Σ * Any.t)%type
        (lstateT Σ * Any.t)%type cancel_eq smj_top smj_top
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
            (SMod.to_mod ∅ (SMod.cancel md))) r_i)))
                (cid, <[cid:=itr_s]> srcs))
        (st, r_s))
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
                (SMod.to_mod_cancel (SMod.sp_from md) md)) r_i)))
                (cid, <[cid:=itr_t]> tgts))
        (st, r_t))).
    { i. zprogress.
      gbase. eapply CIH; et.
      split.
      { rewrite !length_insert //. }
      split.
      { rewrite !length_insert //. }
      i. destruct (decide (cid = i)); cycle 1.
      { rewrite list_lookup_insert_ne in H4; et.
        rewrite list_lookup_insert_ne in H5; et.
        rewrite list_lookup_insert_ne in H6; et.
      }
      subst. rewrite !list_lookup_insert in H4, H5, H6; et; try lia.
      clarify.
    }

    inversion_clear Hcidrel; subst; ss.

    punfold REL; depdes REL; ii; subst; pclearbot.
    - eapply gsim_Take_src; try apply Hs; ss.
    - eapply gsim_tau_src; try apply Hs; ss.
      eapply gsim_Take_src; [lookup_tac; s; do 2 f_equal|ss].
    - revert Ht; ired; i. eapply gsim_Choose_tgt; try apply Ht; ss.
    - destruct cid; cycle 1.
      { giter_s; rewrite /= Hs; gcNormS; gsteps_s; gstep_s; ss. }
      giter_s; rewrite /= Hs; gcNormS; gsteps_s; ss.
      destruct Qo as [Q|].
      { eapply gsim_Choose_tgt; [revert Ht; ired; intros Ht; eapply Ht|]. intros ret.
        eapply gsim_tau_tgt; first rewrite list_lookup_insert //; try lia.
        rewrite list_insert_insert.
        eapply gsim_Guarantee_tgt; first rewrite list_lookup_insert //; try lia.
        intros rt2 [? Hrt2]. rewrite list_insert_insert.
        eapply gsim_tau_tgt; first rewrite list_lookup_insert //; try lia.
        rewrite list_insert_insert.
        giter_t; rewrite /= list_lookup_insert; last lia; s; gsteps_t.
        gstep. econs. econs. r; esplits; cSimpl.
        apply (Own_pure_soundness r_s); first done.
        { rewrite RS Hrt2; iIntros "> [_ [> [? _] _]]"; iApply RET; eauto. }
      }
      ss.
      giter_t; rewrite /= Ht /=. gsteps_t.
      gstep. econs. econs.
      r. esplits; eauto; cSimpl.
    - giter_s; giter_t; rewrite /= Hs Ht /=.
      gsteps_s; gsteps_t.
      eapply Hkey; et.
      { rewrite list_insert_id //. }
      { econs; eauto. }
    - revert Ht; ired; i. eapply cancel_core; eauto.
    - revert Ht; ired; i. eapply cancel_pg; eauto.
    - revert Ht; ired; i. eapply cancel_ag; eauto.
    - eapply cancel_yield; eauto. rewrite bind_bind // in Ht.
    - eapply cancel_spawn; eauto. rewrite bind_bind // in Ht.
    - eapply cancel_pre; eauto. rewrite bind_bind // in Ht.
    - eapply cancel_post; eauto. rewrite bind_bind // in Ht.
    - eapply cancel_gettid; eauto. rewrite bind_bind // in Ht.
  (*SLOW*)Qed.

  Lemma cancel_main md rs rt
    (WFS: SMod.cancellable md)
    (WF: Mod.wf (SMod.to_mod ∅ (SMod.cancel md)))
    (VALID: ✓ rs)
    (MAIN : ∃ P Q, (fspec_flat ((SMod.sp_from md).1 !! entry)) P Q ∧
      (Own rs ⊢ |==> (P tt↑ tt↑ ∗ Own rt) ∗ TIDAUTH 0 ∗ YIELDAUTH 1) ∧
      ∀ varg arg, Q varg arg ⊢ ⌜varg = arg⌝)
    :
    gsim eq smj_bot smj_bot
      (LMod.compile
        (Mod.to_lmod (MInline.inline (SMod.to_mod ∅ (SMod.cancel md))) rs)
        tt↑)
      (LMod.compile
        (Mod.to_lmod
          (MInline.inline (SMod.to_mod_cancel (SMod.sp_from md) md)) rt)
        tt↑).
  Proof using.
    unfold LMod.compile. s. rewrite /ITree.map /LModTr.trans /LModTr.interp_callE.

    rewrite !lookup_fmap !lookup_omap !lookup_fmap.
    destruct ((SMod.fnsems md) !! entry) eqn: FIND; rewrite ?FIND; cycle 1.
    { s. ired. ginit. gstep_s. ss. }
    s. ired. destruct o; ss; cycle 1.
    { s. ired. ginit. gstep_s. ss. }
    destruct p as [msk [fspo bd]]. s. ired.
    rewrite /ModTr.trans_fnsem /SModTr.trans_fnsem.
    dup WFS; rewrite /SMod.cancellable map_Forall_lookup in WFS.
    hexploit (WFS entry (Some (msk, (fspo, bd)))); eauto; intros [? ?].
    hexploit (SMod.well_scoped_fns md entry (msk, (fspo, bd))); last (intros [? ?]).
    { rewrite lookup_omap FIND //. }
    erewrite !sandbox_inline_commute; et.
    ginit. guclo bindC_spec. econs; cycle 1.
    { instantiate (1:=λ vrs vrt, cancel_eq vrs vrt). i. gstep. econs. econs. destruct SIM. des. et. }

    dup FIND.
    assert (FIND1 : SMod.fnsems (SMod.cancel md) !! entry = Some (Some (msk, (None, bd)))).
    { ss; rewrite lookup_fmap FIND //. }
    eapply MIRed_HoareFun_cancel with (sp:=SMod.sp_from md) (arg:=()↑) in FIND; try by des.
    rewrite FIND.
    eapply MIRed_HoareFun with (fspo:=None) (sp:=∅) (arg:=()↑) in FIND1; try by des.
    rewrite FIND1 /=.

    eapply gsim_tau_src; ss; [do 2 f_equal; hnorm_itr|].
    eapply gsim_tau_src; ss; [do 2 f_equal; hnorm_itr|]. ghcNormS. rewrite bind_ret_r.

    destruct fspo as [fsp|]; ss.
    { assert (Hf : (SMod.sp_from md).1 !! entry = Some fsp).
      { rewrite !lookup_omap lookup_fmap lookup_omap FIND0 //. }
      rewrite Hf /= in MAIN. destruct MAIN as [P [Q [Hfsp [Hp Hq]]]].
      eapply gsim_Take_tgt; ss; [do 2 f_equal; hnorm_itr|]. exists (FSpec_mk _ _ Hfsp).
      eapply gsim_tau_tgt; [s; do 2 f_equal; hnorm_itr|]. ss.
      eapply gsim_Take_tgt; ss; [do 2 f_equal; hnorm_itr|]. exists (tt↑).
      eapply gsim_tau_tgt; [s; do 2 f_equal; hnorm_itr|]. ss.
      hexploit (Own_bupd_split); eauto using Hp.
      intros [rs1 [rs2 [Hrs [Hrs1 [Hrs2 Hrs_valid]]]]].

      eapply gsim_Assume_tgt; [s; do 2 f_equal; hnorm_itr|]. exists rs1; splits; eauto.
      { eapply (Own_wand_valid rs); eauto; rewrite Hrs; iIntros "> [$ ?] //". }
      { rewrite Hrs1; apply bupd_intro. }
      eapply gsim_tau_tgt; [s; do 2 f_equal; hnorm_itr|]. ss. rewrite bind_ret_l.

      gfinal. right.
      rewrite /LMod.prog /LMod.fnsems /Mod.to_lmod.
      eapply cancel_elim with (r_s:=rs) (r_t:=rs1) (rs_diff:=[ε]); eauto.
      { econs; [ss|split; [ss|ss]].
        intros ????; rewrite !list_lookup_singleton; case_match; ss; i; clarify.
        eapply (thread_rel_body (Some Q)); eauto.
        eapply elim_rel_cancel; eauto.
      }
      { hexploit (Mod.nodup_init (SMod.to_mod ∅ (SMod.cancel md))); eauto. inv WF; ss. }
      rewrite Hrs Hrs2; iIntros "> [? [? ?]] !>"; iFrame; s; iSplit; auto; iApply Own_unit.
    }

    eapply gsim_tau_tgt; [s; do 2 f_equal; hnorm_itr|]. ss.
    eapply gsim_tau_tgt; [s; do 2 f_equal; hnorm_itr|]. ss.

    gfinal. right.
    rewrite /LMod.prog /LMod.fnsems /Mod.to_lmod.
    eapply cancel_elim with (r_s:=rs) (r_t:=rt) (rs_diff:=[ε]); eauto.
    { econs; [ss|split; [ss|ss]].
      intros ????; rewrite !list_lookup_singleton; case_match; ss; i; clarify.
      eapply (thread_rel_body None); eauto.
      { eapply elim_rel_cancel; eauto. }
      f_equal; grind.
    }
    { hexploit (Mod.nodup_init (SMod.to_mod ∅ (SMod.cancel md))); eauto. inv WF; ss. }
    destruct MAIN as [? [? [? [-> _]]]].
    iIntros "> [[? ?] [? ?]] !>"; iFrame; s.
    iSplit; auto; iApply Own_unit.
    Unshelve. all: eauto.
  (*SLOW*)Qed.

End CANCEL_MAIN.
