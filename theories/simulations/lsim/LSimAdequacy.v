From CRIS.common Require Import Common.
From CRIS.simulations.lsim Require Import LSim LSimTactics.
From CRIS.simulations.gsim Require Import GSim GSimTactics.

Local Open Scope nat_scope.

(* Adequacy - Part 1. ( Divided to resolve the dependency issue. ) *)
Definition b2smj (b : bool) : smj := if b then smj_mid else smj_bot.

Lemma lsim_gsim
    {Σ}
    ms_src ms_tgt
    (lw : LWorld Σ)
    (MSIM : lsim_lmod ms_src ms_tgt lw)
    (* (WFS : LMod.wf ms_src) *)
    w ps pt my_tid itrs_src itrs_tgt st_src st_tgt
    (EQS : List.length w = List.length itrs_src)
    (EQT : List.length w = List.length itrs_tgt)
    (WLEN : my_tid < List.length w)
    (SIM : ∀ tid ps0 pt0 itr_src itr_tgt w0 st_src0 st_tgt0
      (INS : itrs_src !! tid = Some itr_src)
      (INT : itrs_tgt !! tid = Some itr_tgt)
      (TID : tid < List.length w0)
      (FLG : if decide (tid = my_tid) then ps0 = ps ∧ pt0 = pt else ps0 = true ∧ pt0 = true)
      (WLE : if decide (tid = my_tid) then w0 = w
             else le_mine lw tid w w0)
      (WF : if decide (tid = my_tid)
        then st_src0 = st_src ∧ st_tgt0 = st_tgt
        else wf lw w0 (st_src0, st_tgt0)),
      ∃ wany,
        lsim
          (LMod.fnsems ms_src) (LMod.fnsems ms_tgt)
          lw tid (fun _ _ => True) wany ps0 pt0 w0
          (st_src0, itr_src) (st_tgt0, itr_tgt)) :
  gsim (λ '(st_src, ret_src) '(st_tgt, ret_tgt), ret_src = ret_tgt) (b2smj ps) (b2smj pt)
    (LModTr.interp_stateE Any.t
       (iterV (LModTr.handle_callE (LMod.prog ms_src)) (my_tid, itrs_src)) st_src)
    (LModTr.interp_stateE Any.t
       (iterV (LModTr.handle_callE (LMod.prog ms_tgt)) (my_tid, itrs_tgt)) st_tgt).
Proof.
  unfold LModTr.interp_stateE.
  ginit. revert_until MSIM. gcofix CIH. i.
  destruct (itrs_src !! my_tid) eqn : LKS; cycle 1.
  { exfalso. exploit lookup_ge_None_1; eauto. i. nia. }
  destruct (itrs_tgt !! my_tid) eqn : LKT; cycle 1.
  { exfalso. exploit lookup_ge_None_1; eauto. i. nia. }
  hexploit (SIM my_tid ps pt); eauto; try by des_ifs.
  i. des.
  remember (st_src, i) as src. remember (st_tgt, i0) as tgt.
  move H before CIH. revert SIM. revert_until H.
  pattern ps, pt, w, src, tgt.
  eapply lsim_ind, H. clear H. i. subst.

  inv PR.

  - rewrite !unfold_iterV. s. rewrite LKS LKT. grind. des_ifs.
    + grind. zstep_s. zstep_t. zstep. rr in RET. des; subst; eauto.
    + unfold triggerUB, LModTr.pure_state. do 2 zstep_s.
  - rewrite !unfold_iterV. s. rewrite LKS LKT. grind.
    unfold LMod.prog, unwrapU at 1. des_ifs; cycle 1.
    { unfold triggerUB, LModTr.pure_state. grind. do 2 zstep_s. }
    unfold LMod.prog, unwrapU at 1. des_ifs; cycle 1.
    { eapply (LSim.sim_fnsems _ _ lw MSIM) in Heq. des.
      erewrite Heq0 in Heq. ss.
    }
    grind. rename Heq into FIND.
    zstep_s. zstep_t.

    zprogress.
    gbase. eapply (CIH w1 true true); eauto; try by inv WLE; zsimpl_len.

    i. guardH FLG. des_ifs; des; subst; cycle 1.
    { rewrite list_lookup_insert_ne in INS; try nia.
      rewrite list_lookup_insert_ne in INT; try nia.
      eapply SIM; eauto; des_ifs.
      eapply (le_mine_trans lw tid); [|eauto].
      rr in WLE. des. rr. split; try nia.
      intros wi Hwi; exists wi; rewrite -WLE1; ss.
      esplits; eauto. apply (wle_refl lw).
    }

    rewrite !list_lookup_insert in INS; try nia. inv INS.
    rewrite !list_lookup_insert in INT; try nia. inv INT.
    esplits. ginit.
    guclo (@lbindC_spec Σ). econs.
    { eapply (LSim.sim_fnsems _ _ lw MSIM) in FIND. des.
      rewrite FIND in Heq0. inv Heq0.
      eapply lsim_flag_down. gfinal. right.
      eapply FIND0; eauto.
    }

    i. rr in SIM0. des; subst.
    do 2 (guclo (@lsim_indC_spec Σ); econs). grind.
    gfinal. right. eapply K; eauto.
    (* rewrite length_insert in WF0. nia. *)

  - rewrite !unfold_iterV. s. rewrite LKS LKT. grind.
    unfold LModTr.pure_state. grind. zstep. zostep_s. zostep_t. subst.
    eapply K;
      try rewrite length_insert;
      try rewrite list_lookup_insert; eauto; try nia.
    i. des_ifs; des; subst.
    + rewrite !list_lookup_insert in INS; try nia. inv INS.
      rewrite !list_lookup_insert in INT; try nia. inv INT.
      eexists. eapply K.
    + rewrite list_lookup_insert_ne in INS; try nia. inv INS.
      rewrite list_lookup_insert_ne in INT; try nia. inv INT.
      eapply SIM; des_ifs; eauto.

  - rewrite unfold_iterV. s. rewrite LKS. grind.
    unfold LMod.prog, unwrapU at 1.
    rewrite FUN. grind. zostep_s.
    eapply K;
      try rewrite length_insert;
      try rewrite list_lookup_insert; eauto; try nia.
    { do 2 f_equal. extensionalities. grind. }
    i. des_ifs; des; subst.
    + rewrite !list_lookup_insert in INS; try nia. inv INS.
      eexists. ginit. guclo_lflagC. econs.
      { gfinal. right.
        erewrite equal_f; eauto. do 3 f_equal. extensionalities. grind.
      }
      { apply le_others_refl. }
      { eauto. }
      { eauto. }
    + rewrite !list_lookup_insert_ne in INS; try nia. inv INS.
      eapply SIM; eauto; des_ifs.

  - rewrite (unfold_iterV _ (_, itrs_tgt)). s. rewrite LKT. grind.
    unfold LMod.prog, unwrapU at 1.
    rewrite FUN. grind. zostep_t.
    eapply K;
      try rewrite length_insert;
      try rewrite list_lookup_insert; eauto; try nia.
    { do 2 f_equal. extensionalities. grind. }
    i. des_ifs; des; subst.
    + rewrite !list_lookup_insert in INT; try nia. inv INT.
      eexists. ginit. guclo_lflagC. econs.
      { gfinal. right.
        erewrite f_equal; eauto. do 2 f_equal. extensionalities. grind.
      }
      { apply le_others_refl. }
      { eauto. }
      { eauto. }
    + rewrite !list_lookup_insert_ne in INT; try nia. inv INT.
      eapply SIM; eauto; des_ifs.

  - rewrite unfold_iterV. s. rewrite LKS. grind. zostep_s.
    eapply K;
      try rewrite length_insert;
      try rewrite list_lookup_insert; eauto; try nia.
    i. des_ifs; des; subst.
    + rewrite !list_lookup_insert in INS; try nia. inv INS.
      eexists. ginit. guclo_lflagC. econs.
      { gfinal. right. eapply K. }
      { apply le_others_refl. }
      { eauto. }
      { eauto. }
    + rewrite !list_lookup_insert_ne in INS; try nia. inv INS.
      eapply SIM; eauto; des_ifs.

  - rewrite (unfold_iterV _ (_, itrs_tgt)). s. rewrite LKT. grind. zostep_t.
    eapply K;
      try rewrite length_insert;
      try rewrite list_lookup_insert; eauto; try nia.
    i. des_ifs; des; subst.
    + rewrite !list_lookup_insert in INT; try nia. inv INT.
      eexists. ginit. guclo_lflagC. econs.
      { gfinal. right. eapply K. }
      { apply le_others_refl. }
      { eauto. }
      { eauto. }
    + rewrite !list_lookup_insert_ne in INT; try nia. inv INT.
      eapply SIM; eauto; des_ifs.

  - rewrite unfold_iterV. s. rewrite LKS. grind.
    unfold LModTr.pure_state at 1.
    grind. zstep_s. esplits. zostep_s.
    eapply K;
      try rewrite length_insert;
      try rewrite list_lookup_insert; eauto; try nia.
    i. des_ifs; des; subst.
    + rewrite !list_lookup_insert in INS; try nia. inv INS.
      eexists. ginit. guclo_lflagC. econs.
      { gfinal. right. eapply K. }
      { apply le_others_refl. }
      { eauto. }
      { eauto. }
    + rewrite !list_lookup_insert_ne in INS; try nia. inv INS.
      eapply SIM; eauto; des_ifs.

  - rewrite (unfold_iterV _ (_, itrs_tgt)). s. rewrite LKT.
    grind. unfold LModTr.pure_state at 2.
    grind. zstep_t. zostep_t.
    eapply K;
      try rewrite length_insert;
      try rewrite list_lookup_insert; eauto; try nia.
    i. des_ifs; des; subst.
    + rewrite !list_lookup_insert in INT; try nia. inv INT.
      eexists. ginit. guclo_lflagC. econs.
      { gfinal. right. eapply K. }
      { apply le_others_refl. }
      { eauto. }
      { eauto. }
    + rewrite !list_lookup_insert_ne in INT; try nia. inv INT.
      eapply SIM; eauto; des_ifs.

  - rewrite unfold_iterV. s. rewrite LKS.
    grind. unfold LModTr.pure_state at 1.
    grind. zstep_s. zostep_s. grind.
    eapply K;
      try rewrite length_insert;
      try rewrite list_lookup_insert; eauto; try nia.
    i. des_ifs; des; subst.
    + rewrite !list_lookup_insert in INS; try nia. inv INS.
      eexists. ginit. guclo_lflagC. econs.
      { gfinal. right. eapply K. }
      { apply le_others_refl. }
      { eauto. }
      { eauto. }
    + rewrite !list_lookup_insert_ne in INS; try nia. inv INS.
      eapply SIM; eauto; des_ifs.

  - rewrite (unfold_iterV _ (_, itrs_tgt)). s. rewrite LKT.
    grind. unfold LModTr.pure_state at 2.
    grind. zstep_t. esplits. zostep_t.
    eapply K;
      try rewrite length_insert;
      try rewrite list_lookup_insert; eauto; try nia.
    i. des_ifs; des; subst.
    + rewrite !list_lookup_insert in INT; try nia. inv INT.
      eexists. ginit. guclo_lflagC. econs.
      { gfinal. right. eapply K. }
      { apply le_others_refl. }
      { eauto. }
      { eauto. }
    + rewrite !list_lookup_insert_ne in INT; try nia. inv INT.
      eapply SIM; eauto; des_ifs.

  - rewrite unfold_iterV. s. rewrite LKS. grind. zostep_s.
    eapply K;
      try rewrite length_insert;
      try rewrite list_lookup_insert; eauto; try nia.
    i. des_ifs; des; subst.
    + rewrite !list_lookup_insert in INS; try nia. inv INS.
      eexists. ginit. guclo_lflagC. econs.
      { gfinal. right. eapply K. }
      { apply le_others_refl. }
      { eauto. }
      { eauto. }
    + rewrite !list_lookup_insert_ne in INS; try nia. inv INS.
      eapply SIM; eauto; des_ifs.

  - rewrite (unfold_iterV _ (_, itrs_tgt)). s. rewrite LKT. grind. zostep_t.
    eapply K;
      try rewrite length_insert;
      try rewrite list_lookup_insert; eauto; try nia.
    i. des_ifs; des; subst.
    + rewrite !list_lookup_insert in INT; try nia. inv INT.
      eexists. ginit. guclo_lflagC. econs.
      { gfinal. right. eapply K. }
      { apply le_others_refl. }
      { eauto. }
      { eauto. }
    + rewrite !list_lookup_insert_ne in INT; try nia. inv INT.
      eapply SIM; eauto; des_ifs.

  - rewrite !unfold_iterV /= LKS LKT. grind.

    unfold LMod.prog, unwrapU at 1. des_ifs; cycle 1.
    { unfold triggerUB, LModTr.pure_state. grind. do 2 zstep_s. }
    unfold LMod.prog, unwrapU at 1. des_ifs; cycle 1.
    { eapply (LSim.sim_fnsems _ _ lw MSIM) in Heq.
      des. erewrite Heq0 in Heq. ss. }
    grind. rename Heq into FIND.

    zstep_s. zstep_t. zprogress.
    gbase. eapply (CIH _ true true).
    { instantiate (1:=x2++[LSim.winit lw]).
      rewrite !length_app !length_insert. eauto. }
    { rewrite !length_app /= !length_insert. nia. }
    { rewrite length_app. nia. }
    i. des_ifs; des; subst.
    + rewrite lookup_app_l in INS; cycle 1.
      { rewrite length_insert. nia. }
      rewrite !list_lookup_insert in INS; try nia. inv INS.
      rewrite lookup_app_l in INT; cycle 1.
      { rewrite length_insert. nia. }
      rewrite !list_lookup_insert in INT; try nia. inv INT.
      eexists. s.
      move: K; rewrite -EQT -EQS; intros K. eapply K.
    + assert (DEC : tid < List.length itrs_tgt \/ tid = List.length itrs_tgt).
      { apply lookup_lt_Some in INS. rewrite length_app in INS. ss.
        rewrite length_insert in INS. nia.
      }
      des.
      { rewrite lookup_app_l in INS; cycle 1.
        { rewrite length_insert. nia. }
        rewrite list_lookup_insert_ne in INS; try nia.
        rewrite lookup_app_l in INT; cycle 1.
        { rewrite length_insert. nia. }
        rewrite list_lookup_insert_ne in INT; try nia.
        eapply SIM; eauto; des_ifs. destruct WLE. split.
        { rewrite length_app in H. ss. nia. }
        ii. eapply H0. rewrite lookup_app_l; eauto using lookup_lt_Some.
      }
      subst.
      rewrite (list_lookup_middle _ []) in INS; cycle 1.
      { rewrite length_insert. nia. }
      inv INS.
      rewrite (list_lookup_middle _ []) in INT; cycle 1.
      { rewrite length_insert. eauto. }
      inv INT.

      esplits.
      eapply (LSim.sim_fnsems _ _ lw MSIM) in FIND.
      des. rewrite FIND in Heq0. inv Heq0.
      ginit. eapply lsim_flag_down. gfinal. right.
      eapply lsim_mon_rr, FIND0; et.

  - rewrite !unfold_iterV /= LKS LKT. grind.
    zstep_s. zstep_t. zprogress.
    assert (DEC : tid < List.length itrs_src \/ tid >= List.length itrs_src) by nia.
    des; cycle 1.
    { rewrite unfold_iterV. s.
      rewrite lookup_ge_None_2; try (rewrite length_insert; nia).
      s. grind. unfold triggerUB. grind. unfold LModTr.pure_state. grind.
      do 2 zstep_s. }

    gbase. eapply (CIH w1 true true); eauto.
    { rewrite !length_insert. inv WLE. nia. }
    { rewrite !length_insert. inv WLE. nia. }
    { inv WLE; nia. }

    i. des_ifs; des; subst.
    { assert (DEC' : tid = my_tid \/ tid ≠ my_tid) by nia; des; subst.
      - rewrite !list_lookup_insert in INS; try nia. inv INS.
        rewrite !list_lookup_insert in INT; try nia. inv INT.
        eexists. eapply K; eauto.
        apply (le_mine_refl lw my_tid).
      - rewrite list_lookup_insert_ne in INS; try nia.
        rewrite list_lookup_insert_ne in INT; try nia.
        eapply SIM; eauto; des_ifs; eauto.
        split.
        { inv WLE; try nia. }
        ii. esplits; eauto.
        { inv WLE; hexploit H1; eauto. intros <-; eauto. }
        { apply (LSim.wle_refl lw). }
    }
    { assert (DEC' : tid0 = my_tid \/ tid0 ≠ my_tid) by nia; des; subst.
      - rewrite !list_lookup_insert in INS; try nia. inv INS.
        rewrite !list_lookup_insert in INT; try nia. inv INT.
        eexists. eapply K; eauto.
      - rewrite list_lookup_insert_ne in INS; try nia.
        rewrite list_lookup_insert_ne in INT; try nia.
        eapply SIM; eauto; des_ifs; eauto.
        eapply (le_mine_trans lw tid0); [|eauto].
        destruct WLE. split; try nia.
        ii. rewrite <-H0. rewrite H1.
        esplits; eauto. apply (wle_refl lw). eauto.
    }

  - rewrite !unfold_iterV. s. rewrite LKS LKT. grind.
    unfold LModTr.pure_state. zostep_s. zostep_t.
    (* grind. zstep. zostep_s. zostep_t. subst. *)
    eapply K;
      try rewrite length_insert;
      try rewrite list_lookup_insert; eauto; try nia.
    i. des_ifs; des; subst.
    + rewrite !list_lookup_insert in INS; try nia. inv INS.
      rewrite !list_lookup_insert in INT; try nia. inv INT.
      eexists. eapply K.
    + rewrite list_lookup_insert_ne in INS; try nia. inv INS.
      rewrite list_lookup_insert_ne in INT; try nia. inv INT.
      eapply SIM; des_ifs; eauto.

  - rewrite unfold_iterV; s. rewrite LKS. grind.
    unfold LMod.prog, unwrapU at 1.
    rewrite FUN. grind. unfold triggerUB, LModTr.pure_state. grind.
    do 2 zstep_s.

  - rewrite unfold_iterV; s. rewrite LKS. grind.
    unfold LMod.prog, unwrapU at 1.
    rewrite FUN. grind. unfold triggerUB, LModTr.pure_state. grind.
    do 2 zstep_s.

  - zprogress with smj_bot smj_bot _ _.
    gbase. eapply (CIH _ false false); eauto.
    i. des_ifs; cycle 1; des; subst.
    { eapply SIM; eauto; des_ifs; eauto. }

    eexists. ginit. guclo_lflagC.
    econs; try eassumption; eauto with paco.

Unshelve. all : try exact smj_top.
Qed.

(* ADEQUACY *)
Lemma lsim_adequacy
  {Σ}
  ms_src ms_tgt arg (lw : LWorld Σ)
  (SIM : lsim_lmod ms_src ms_tgt lw)
  : gsim eq smj_bot smj_bot (LMod.compile ms_src arg) (LMod.compile ms_tgt arg).
Proof.
  rewrite /LMod.compile /LModTr.trans /LModTr.interp_callE.
  ginit.
  destruct (_ !! _) eqn: E; s; cycle 1.
  { zstep_s. }
  ired. hexploit (LSim.sim_fnsems _ _ lw SIM); et. i; des.
  rewrite H. s. ired.
  specialize (H0 0 [LSim.winit lw]
    (LMod.initial_st ms_src) (LMod.initial_st ms_tgt) arg).
  assert (WF : wf lw [LSim.winit lw]
    (LMod.initial_st ms_src, LMod.initial_st ms_tgt)).
  { change (wf lw ([] ++ [LSim.winit lw])
      (LMod.initial_st ms_src, LMod.initial_st ms_tgt)).
    eapply (LSim.wf_winit _ _ lw SIM).
    eapply (LSim.wf_nil _ _ lw SIM).
  }
  specialize (H0 ltac:(ss) WF).
  erewrite <-(bind_ret_r (ITree.map snd _)), (bind_map _ _ _).
  erewrite <-(bind_ret_r (ITree.map snd _)), (bind_map _ _ _).

  guclo bindC_spec. econs; i; s.
  { gfinal. right.
    eapply (lsim_gsim _ _ lw SIM) with
      (ps := false) (pt := false);
      cycle 3.
    - i. destruct tid; ss; inv INS. des; subst. eexists.
      instantiate (1:= [_]). eapply lsim_mon_rr, H0. ss.
    - et.
    - et.
    - et.
  }
  { zstep. destruct vret_src, vret_tgt; ss. }
Qed.
