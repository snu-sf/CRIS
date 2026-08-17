From CRIS.common Require Import StatePredicate.
From CRIS.modules Require Import Mod ModTr.
From CRIS.simulations.msim Require Import MSimCommon MSim.
From CRIS.simulations.lsim Require Import LSim LSimTactics.
From iris.proofmode Require Import proofmode.

Lemma own_upd_in_middle `{Σ: GRA} mr_src mr_tgt ctx fmr fmr0 state_res
    (UPD : Own mr_src ⊢ |==> Own (ctx ⋅ fmr ⋅ state_res ⋅ mr_tgt))
    (FMR : Own fmr ⊢ |==> Own fmr0) :
  Own mr_src ⊢ |==> Own (ctx ⋅ fmr0 ⋅ state_res ⋅ mr_tgt).
Proof.
  etrans; eauto. iIntros "> [[[CTX FMR] STATE] MRT]".
  iMod (FMR with "FMR") as "FMR".
  iModIntro. rewrite !Own_op. iFrame.
Qed.
Local Hint Resolve own_upd_in_middle : core.

Local Lemma map_Forall_is_Some_mjoin_None
    (m : gmap key (option Any.t)) k
    (WF : map_Forall (const is_Some) m)
    (NONE : mjoin (m !! k) = None) :
  m !! k = None.
Proof.
  destruct (m !! k) as [[v|]|] eqn:LOOK; ss.
  exfalso. specialize (WF k None LOOK). by apply is_Some_None in WF.
Qed.

Definition ctx_sem `{Σ: GRA} (ctx : list Σ) : Σ :=
  [^(⋅) list] r ∈ ctx, r.

Variant interp_inv `{!stateGS Σ} (Ist : iProp Σ) :
    list Σ → lstateT Σ * lstateT Σ → Prop :=
| interp_inv_intro
    (ctx : list Σ) (mr_src mr_tgt : Σ) st_src st_tgt mr state_res
    (WF : ✓ mr_src)
    (MRS : Own mr_src ⊢ |==>
      Own (ctx_sem ctx ⋅ mr ⋅ state_res ⋅ mr_tgt))
    (MR : Own mr ⊢ |==> Ist)
    (STATE : Own state_res ⊢ |==> SI_src st_src ∗ SI_tgt st_tgt)
    (NODUPS : map_Forall (const is_Some) st_src)
    (NODUPT : map_Forall (const is_Some) st_tgt)
    :
  interp_inv Ist ctx
    ((st_src, mr_src), (st_tgt, mr_tgt)).

Definition IstWorld `{!stateGS Σ} (Ist : iProp Σ) : LWorld Σ :=
  {|
    world := Σ;
    winit := ε;
    wf := interp_inv Ist;
    wle := eq;
    wle_refl := λ _, eq_refl;
    wle_trans := λ x y z, @eq_trans Σ x y z
  |}.

Definition ctx_set `{Σ: GRA} (my_tid : nat) (ctx : list Σ) (r : Σ) : list Σ :=
  <[my_tid := r]> ctx.

Definition ctx_add `{Σ: GRA} (my_tid : nat) (ctx : list Σ) (r : Σ) : list Σ :=
  ctx_set my_tid ctx ((or_else (ctx !! my_tid) ε) ⋅ r).

Lemma ctx_set_sem `{Σ: GRA} (my_tid : nat) ctx r r' (IN : my_tid < List.length ctx) :
  ctx_sem (ctx_set my_tid ctx (r ⋅ r')) ≡ ctx_sem (ctx_set my_tid ctx r) ⋅ r'.
Proof.
  unfold ctx_set. revert my_tid r r' IN.
  induction ctx; i; ss; try nia.
  destruct my_tid; s.
  { rewrite /ctx_sem; rewrite !big_opL_cons. rewrite -assoc (comm _ r') assoc; done. }
  { move: IHctx; rewrite /ctx_sem !big_opL_cons => IHctx; rewrite IHctx; last by lia.
    by rewrite assoc. }
Qed.

Lemma ctx_add_sem `{Σ: GRA} (my_tid : nat) ctx r (IN : my_tid < List.length ctx) :
  ctx_sem (ctx_add my_tid ctx r) ≡ ctx_sem ctx ⋅ r.
Proof.
  destruct (ctx !! my_tid) eqn:emy; cycle 1.
  { hexploit (lookup_lt_is_Some_2 ctx); eauto; rewrite emy; ss; intros []; clarify. }
  { by rewrite /ctx_add; rewrite emy; ss; rewrite ctx_set_sem //= /ctx_set list_insert_id; ss. }
Qed.

Lemma le_mine_in `{!stateGS Σ} {Ist : iProp Σ}
    (my_tid : nat) (ctx0 ctx : list Σ)
    (CTXLE : le_mine (IstWorld Ist) my_tid ctx0 ctx)
    (IN : my_tid < List.length ctx0) :
  my_tid < List.length ctx.
Proof.
  destruct CTXLE.
  eapply lookup_lt_is_Some_2 in IN. rdes IN.
  eapply H0 in IN. des. subst.
  eapply lookup_lt_is_Some_1. eauto.
Qed.

Lemma ctx_set_le_others `{!stateGS Σ} {Ist : iProp Σ}
    (my_tid : nat) ctx r :
  le_others (IstWorld Ist) my_tid ctx (ctx_set my_tid ctx r).
Proof.
  unfold ctx_set. r; esplits.
  - rewrite length_insert. eauto.
  - i. rewrite list_lookup_insert_ne; eauto.
Qed.

Lemma ctx_le_mine_sem `{!stateGS Σ} {Ist : iProp Σ}
    (my_tid : nat) (w0 w1 : list Σ)
    (IN : my_tid < List.length w0)
    (LE : le_mine (IstWorld Ist) my_tid w0 w1) :
  ctx_sem w1 = ctx_sem (ctx_set my_tid w1 (or_else (w0 !! my_tid) ε)).
Proof.
  unfold ctx_sem, ctx_set.
  move w1 before Σ. revert_until w1.
  induction w1; i; eauto.
  destruct w0; ss; try nia.
  destruct LE.
  destruct my_tid; ss.
  - exploit H0; ss. i; des. inv x0. eauto.
  - erewrite (IHw1 _ Ist my_tid w0); eauto; try nia.
    unfold le_mine; simpl.
    split; first nia.
    intros wi Hwi. eapply H0 in Hwi as [wi' [Hwi ->]].
    exists wi'. split; done.
Qed.

Lemma msim_adequacy
    `{!stateGS Σ}
    (contextual : contextuality)
    (fl_src fl_tgt : gmap fname (option (Any.t → itree crisE Any.t)))
    (Ist : iProp Σ)
    (my_tid : nat)
    (fl_src0 fl_tgt0 : gmap fname (Any.t → itree (lmodE Σ) Any.t))
    (FLS : fl_src0 = ModTr.trans_fnsem <$> (omap id fl_src))
    (FLT : fl_tgt0 = ModTr.trans_fnsem <$> (omap id fl_tgt))
    ps pt st_src st_tgt itr_src itr_tgt
    (RR : iProp Σ)
    (ctx0 ctx : list Σ) (mr_src mr_tgt fmr state_res : Σ)

    (NODUPFS : map_Forall (const is_Some) fl_src)
    (NODUPFT : map_Forall (const is_Some) fl_tgt)
    (NODUPS : map_Forall (const is_Some) st_src)
    (NODUPT : map_Forall (const is_Some) st_tgt)
    (CTXLE : le_mine (IstWorld Ist) my_tid ctx0 ctx)
    (TID : my_tid < List.length ctx0)
    (SIM : msim contextual fl_src fl_tgt Ist
      (λ r_src r_tgt, ⌜r_src = r_tgt⌝ ∗ RR)%I
      ps pt itr_src itr_tgt fmr)
    (WF : ✓ mr_src)
    (FMR : Own mr_src ⊢ |==>
      Own (ctx_sem ctx ⋅ fmr ⋅ state_res ⋅ mr_tgt))
    (STATE : Own state_res ⊢ |==> SI_src st_src ∗ SI_tgt st_tgt) :
  lsim fl_src0 fl_tgt0 (IstWorld Ist) my_tid
    (interp_inv RR) ctx0 ps pt ctx
    ((st_src, mr_src), ModTr.trans itr_src)
    ((st_tgt, mr_tgt), ModTr.trans itr_tgt).
Proof.
  revert_until FLT. ginit. gcofix CIH. i.
  move SIM before FLT. revert_until SIM. punfold SIM.
  pattern ps, pt, itr_src, itr_tgt, fmr.
  eapply _msim_tarski, SIM; i. clear SIM fmr. rename fmr0 into fmr.
  assert (wffmr : ✓ fmr).
  { assert (FMR_VALID : Own mr_src ⊢ |==>
        Own (ctx_sem ctx ⋅ fmr ⋅ state_res ⋅ mr_tgt)).
    { exact FMR. }
    hexploit (Own_wand_valid mr_src
      (ctx_sem ctx ⋅ fmr ⋅ state_res ⋅ mr_tgt)); eauto. intros wf.
    apply cmra_valid_op_l, cmra_valid_op_l, cmra_valid_op_r in wf; ss.
  }
  exploit IN; i; eauto.
  des; clear IN.
  assert (wffmr0 : ✓ fmr0).
  { by eapply Own_wand_valid. }
  assert (wffmrstate : ✓ (fmr0 ⋅ state_res)).
  { eapply Own_wand_valid; last exact WF.
    iIntros "MRS".
    iMod (FMR with "MRS") as "[[[CTX FMR] STATE] MRT]".
    iMod (x1 with "FMR") as "FMR".
    iModIntro. rewrite Own_op. iFrame. }

  destruct x0; i; des.

  - (* Ret *)
    clear CIH; clarify.
    assert (EQ : v_src = v_tgt).
    { eapply Own_pure_soundness with (a := fmr0); eauto.
      iIntros "H". iMod (RET with "H") as "[$ _]". }
    step.
    econs; eauto.
    esplits; et.
    eapply interp_inv_intro with
      (mr := fmr0) (state_res := state_res); eauto.
    { iIntros "H". iMod (RET with "H") as "[_ RR]".
      iModIntro. iExact "RR". }

  - (* Call *)
    clarify; ired.
    hexploit (Own_bupd_split fmr0); eauto.
    intros [ist [frame [UPD [Hist [Hframe VALID_IST_FRAME]]]]].
    guclo_lflagC; econs; try instantiate (1:=ctx_add my_tid ctx frame);
      eauto using ctx_set_le_others.
    step.
    { eapply interp_inv_intro with
        (mr := ist) (state_res := state_res); eauto.
      { iIntros "H".
        iMod (FMR with "H") as "[[[CTX FMR] STATE] MRT]".
        iMod (x1 with "FMR") as "FMR".
        iMod (UPD with "FMR") as "[IST FRAME]".
        rewrite ctx_add_sem; eauto using le_mine_in.
        iModIntro. rewrite !Own_op. iFrame.
      }
      { iIntros "H"; iModIntro; iApply Hist; done. }
    }
    ired. inv WF0.
    guclo_lflagC; econs; try instantiate (1:=ctx_set w1 (or_else (ctx !! my_tid) ε));
      eauto using ctx_set_le_others.
    assert (MRS' : Own mr_src0 ⊢ |==>
      Own (ctx_sem (ctx_set my_tid w1 (default ε (ctx !! my_tid))) ⋅
        (frame ⋅ mr) ⋅ state_res0 ⋅ mr_tgt0)).
    { iIntros "H".
      iMod (MRS with "H") as "[[[CTX FMR] STATE] MRT]".
      iModIntro. rewrite !Own_op. iFrame "FMR STATE MRT".
      rewrite -Own_op.
      erewrite (ctx_le_mine_sem my_tid (ctx_add my_tid ctx frame) w1);
        eauto using le_mine_in; cycle 1.
      { rewrite /ctx_add length_insert; eauto using le_mine_in. }
      rewrite -ctx_set_sem; cycle 1.
      { eapply le_mine_in; eauto; rewrite length_insert;
          eauto using le_mine_in. }
      rewrite /ctx_add /ctx_set list_lookup_insert;
        eauto using le_mine_in. }
    assert (VALID_FRAME_MR : ✓ (frame ⋅ mr)).
    { assert (VALID_ALL :
        ✓ (ctx_sem (ctx_set my_tid w1 (default ε (ctx !! my_tid))) ⋅
          (frame ⋅ mr) ⋅ state_res0 ⋅ mr_tgt0)).
      { eapply Own_wand_valid; eauto. }
      apply cmra_valid_op_l, cmra_valid_op_l, cmra_valid_op_r in VALID_ALL.
      exact VALID_ALL. }
    eapply (K vret (frame ⋅ mr) VALID_FRAME_MR); eauto; try nia.
    { iIntros "[F M]"; iMod (MR with "M") as "M"; iSplitL "M"; iModIntro; eauto. iApply Hframe; done. }
    { eapply (le_mine_trans (IstWorld Ist) my_tid).
      { apply CTXLE. }
      { split.
        { destruct WLE. unfold ctx_add, ctx_set in *.
          rewrite !length_insert in H |- *. nia. }
        intros ? Hlookup.
        rewrite Hlookup /=.
        rewrite /ctx_set list_lookup_insert; eauto.
        eapply le_mine_in; eauto; rewrite /ctx_add /ctx_set length_insert; eauto using le_mine_in.
      }
    }

  - (* IO *)
    clarify. step. ired. eapply K; eauto.

  - (* inline src *)
    clarify. step; eauto.
    { instantiate (1:= ModTr.trans_fnsem f).
      rewrite lookup_fmap /= lookup_omap FUN //.
    }

    rewrite /ModTr.trans_fnsem.
    exploit (K _ _ st_src st_tgt ctx0 ctx
      mr_src mr_tgt state_res); eauto.
    clear K CIH; intros K.

    match goal with [|- _ ?t _] => pattern t end.
    eapply eq_ind; eauto.
    rewrite ?Red.bind bind_bind.
    repeat f_equal. extensionalities x.
    grind. rewrite !Red.tau ?bind_tau. repeat f_equal. rewrite Red.ret; grind.

  - (* inline tgt *)
    clarify. step; eauto.
    { instantiate (1:= ModTr.trans_fnsem f).
      rewrite lookup_fmap /= lookup_omap FUN //.
    }

    rewrite /ModTr.trans_fnsem.
    exploit (K _ _ st_src st_tgt ctx0 ctx
      mr_src mr_tgt state_res); eauto.
    clear K CIH; intros K.

    eapply eq_ind; eauto.
    rewrite ?Red.bind bind_bind.
    repeat f_equal. extensionalities x.
    grind. rewrite !Red.tau ?bind_tau. repeat f_equal. rewrite Red.ret; grind.

  - (* Tau src *)
    clarify; steps; eapply K; eauto.
  - (* Tau tgt *)
    clarify; steps; eapply K; eauto.
  - (* Take src *)
    clarify; steps; eapply K; eauto.
  - (* Choose tgt *)
    clarify; steps; eapply K; eauto.
  - (* Choose src *)
    clarify; steps; eapply K; eauto.
  - (* Take tgt *)
    clarify; steps; eapply K; eauto.

  - (* SPut src *)
    assert (UPD_STATE :
      Own (fmr0 ⋅ state_res) ⊢ |==>
        (k ↦src v' ∗ FMR0) ∗
        (SI_src (<[k := Some v']> st_src) ∗ SI_tgt st_tgt)).
    { rewrite Own_op. iIntros "[FMR STATE]".
      iMod (CUR with "FMR") as "[PT FMR]".
      iMod (STATE with "STATE") as "[SIS SIT]".
      iMod (SI_src_update with "SIS PT") as "[SIS PT]".
      iModIntro. iFrame. }
    eapply Own_bupd_split in UPD_STATE as
      [fmr1 [state_res1 [UPD [HFMR [HSTATE VALID_FMR_STATE]]]]];
      eauto.
    clarify; steps; eapply (K fmr1); eauto using cmra_valid_op_l.
    { iIntros "FMR". iModIntro. iApply HFMR. done. }
    { apply map_Forall_insert_2; ss. }
    { instantiate (1 := state_res1).
      iIntros "MRS".
      iMod (FMR with "MRS") as "[[[CTX FMR] STATE] MRT]".
      iMod (x1 with "FMR") as "FMR".
      iMod (UPD with "[FMR STATE]") as "[FMR STATE]".
      { rewrite Own_op. iFrame. }
      iModIntro. rewrite !Own_op. iFrame. }
    { iIntros "STATE". iModIntro. iApply HSTATE. done. }

  - (* SPut tgt *)
    assert (UPD_STATE :
      Own (fmr0 ⋅ state_res) ⊢ |==>
        (k ↦tgt v' ∗ FMR0) ∗
        (SI_src st_src ∗ SI_tgt (<[k := Some v']> st_tgt))).
    { rewrite Own_op. iIntros "[FMR STATE]".
      iMod (CUR with "FMR") as "[PT FMR]".
      iMod (STATE with "STATE") as "[SIS SIT]".
      iMod (SI_tgt_update with "SIT PT") as "[SIT PT]".
      iModIntro. iFrame. }
    eapply Own_bupd_split in UPD_STATE as
      [fmr1 [state_res1 [UPD [HFMR [HSTATE VALID_FMR_STATE]]]]];
      eauto.
    clarify; steps; eapply (K fmr1); eauto using cmra_valid_op_l.
    { iIntros "FMR". iModIntro. iApply HFMR. done. }
    { apply map_Forall_insert_2; ss. }
    { instantiate (1 := state_res1).
      iIntros "MRS".
      iMod (FMR with "MRS") as "[[[CTX FMR] STATE] MRT]".
      iMod (x1 with "FMR") as "FMR".
      iMod (UPD with "[FMR STATE]") as "[FMR STATE]".
      { rewrite Own_op. iFrame. }
      iModIntro. rewrite !Own_op. iFrame. }
    { iIntros "STATE". iModIntro. iApply HSTATE. done. }

  - (* SGet src *)
    assert (LOOK : st_src !! k = Some (Some v)).
    { eapply Own_pure_soundness with (a := fmr0 ⋅ state_res); eauto.
      rewrite Own_op. iIntros "[FMR STATE]".
      iMod (CUR with "FMR") as "[PT _]".
      iMod (STATE with "STATE") as "[SIS _]".
      iDestruct (SI_src_lookup with "SIS PT") as "$". }
    clarify. step.
    lnorm_s. rewrite LOOK /=. eapply (K fmr0); eauto.

  - (* SGet tgt *)
    assert (LOOK : st_tgt !! k = Some (Some v)).
    { eapply Own_pure_soundness with (a := fmr0 ⋅ state_res); eauto.
      rewrite Own_op. iIntros "[FMR STATE]".
      iMod (CUR with "FMR") as "[PT _]".
      iMod (STATE with "STATE") as "[_ SIT]".
      iDestruct (SI_tgt_lookup with "SIT PT") as "$". }
    clarify. step.
    lnorm_t. rewrite LOOK /=. eapply (K fmr0); eauto.

  - (* SPut src, uninitialized *)
    assert (LOOK : st_src !! k = None).
    { apply map_Forall_is_Some_mjoin_None; first exact NODUPS.
      eapply Own_pure_soundness with (a := fmr0 ⋅ state_res); eauto.
      rewrite Own_op. iIntros "[FMR STATE]".
      iMod (CUR with "FMR") as "[UNINIT _]".
      iMod (STATE with "STATE") as "[SIS _]".
      iDestruct (SI_src_uninit_lookup with "SIS UNINIT") as "$". }
    assert (UPD_STATE :
      Own (fmr0 ⋅ state_res) ⊢ |==>
        (k ↦src v' ∗ FMR0) ∗
        (SI_src (<[k := Some v']> st_src) ∗ SI_tgt st_tgt)).
    { rewrite Own_op. iIntros "[FMR STATE]".
      iMod (CUR with "FMR") as "[UNINIT FMR]".
      iMod (STATE with "STATE") as "[SIS SIT]".
      iMod (SI_src_insert _ _ _ LOOK with "SIS UNINIT") as "[SIS PT]".
      iModIntro. iFrame. }
    eapply Own_bupd_split in UPD_STATE as
      [fmr1 [state_res1 [UPD [HFMR [HSTATE VALID_FMR_STATE]]]]];
      eauto.
    clarify; steps; eapply (K fmr1); eauto using cmra_valid_op_l.
    { iIntros "FMR". iModIntro. iApply HFMR. done. }
    { apply map_Forall_insert_2; ss. }
    { instantiate (1 := state_res1).
      iIntros "MRS".
      iMod (FMR with "MRS") as "[[[CTX FMR] STATE] MRT]".
      iMod (x1 with "FMR") as "FMR".
      iMod (UPD with "[FMR STATE]") as "[FMR STATE]".
      { rewrite Own_op. iFrame. }
      iModIntro. rewrite !Own_op. iFrame. }
    { iIntros "STATE". iModIntro. iApply HSTATE. done. }

  - (* SPut tgt, uninitialized *)
    assert (LOOK : st_tgt !! k = None).
    { apply map_Forall_is_Some_mjoin_None; first exact NODUPT.
      eapply Own_pure_soundness with (a := fmr0 ⋅ state_res); eauto.
      rewrite Own_op. iIntros "[FMR STATE]".
      iMod (CUR with "FMR") as "[UNINIT _]".
      iMod (STATE with "STATE") as "[_ SIT]".
      iDestruct (SI_tgt_uninit_lookup with "SIT UNINIT") as "$". }
    assert (UPD_STATE :
      Own (fmr0 ⋅ state_res) ⊢ |==>
        (k ↦tgt v' ∗ FMR0) ∗
        (SI_src st_src ∗ SI_tgt (<[k := Some v']> st_tgt))).
    { rewrite Own_op. iIntros "[FMR STATE]".
      iMod (CUR with "FMR") as "[UNINIT FMR]".
      iMod (STATE with "STATE") as "[SIS SIT]".
      iMod (SI_tgt_insert _ _ _ LOOK with "SIT UNINIT") as "[SIT PT]".
      iModIntro. iFrame. }
    eapply Own_bupd_split in UPD_STATE as
      [fmr1 [state_res1 [UPD [HFMR [HSTATE VALID_FMR_STATE]]]]];
      eauto.
    clarify; steps; eapply (K fmr1); eauto using cmra_valid_op_l.
    { iIntros "FMR". iModIntro. iApply HFMR. done. }
    { apply map_Forall_insert_2; ss. }
    { instantiate (1 := state_res1).
      iIntros "MRS".
      iMod (FMR with "MRS") as "[[[CTX FMR] STATE] MRT]".
      iMod (x1 with "FMR") as "FMR".
      iMod (UPD with "[FMR STATE]") as "[FMR STATE]".
      { rewrite Own_op. iFrame. }
      iModIntro. rewrite !Own_op. iFrame. }
    { iIntros "STATE". iModIntro. iApply HSTATE. done. }

  - (* SGet src, uninitialized *)
    assert (LOOK : st_src !! k = None).
    { apply map_Forall_is_Some_mjoin_None; first exact NODUPS.
      eapply Own_pure_soundness with (a := fmr0 ⋅ state_res); eauto.
      rewrite Own_op. iIntros "[FMR STATE]".
      iMod (CUR with "FMR") as "[UNINIT _]".
      iMod (STATE with "STATE") as "[SIS _]".
      iDestruct (SI_src_uninit_lookup with "SIS UNINIT") as "$". }
    clarify. step.
    lnorm_s. rewrite LOOK /=. eapply (K fmr0); eauto.

  - (* SGet tgt, uninitialized *)
    assert (LOOK : st_tgt !! k = None).
    { apply map_Forall_is_Some_mjoin_None; first exact NODUPT.
      eapply Own_pure_soundness with (a := fmr0 ⋅ state_res); eauto.
      rewrite Own_op. iIntros "[FMR STATE]".
      iMod (CUR with "FMR") as "[UNINIT _]".
      iMod (STATE with "STATE") as "[_ SIT]".
      iDestruct (SI_tgt_uninit_lookup with "SIT UNINIT") as "$". }
    clarify. step.
    lnorm_t. rewrite LOOK /=. eapply (K fmr0); eauto.

  - (* Assume src *)
    clarify; steps.
    rewrite /assume bind_bind; steps.
    rewrite /ModTr.put_res; steps. des.
    eapply Own_bupd_split in x2 as
      [rP [rMRS [SPLIT [HP [HMRS VALID_RP_MRS]]]]]; eauto.
    assert (MRS' : Own x ⊢ |==>
      Own (ctx_sem ctx ⋅ (fmr0 ⋅ rP) ⋅ state_res ⋅ mr_tgt)).
    { rewrite SPLIT.
      iIntros "> [P MRS]". iPoseProof (HMRS with "MRS") as "MRS".
      iMod (FMR with "MRS") as "[[[CTX FMR] STATE] MRT]".
      iMod (x1 with "FMR") as "FMR".
      iModIntro. rewrite !Own_op. iFrame. }
    assert (VALID_FMR_P : ✓ (fmr0 ⋅ rP)).
    { assert (VALID_ALL :
        ✓ (ctx_sem ctx ⋅ (fmr0 ⋅ rP) ⋅ state_res ⋅ mr_tgt)).
      { eapply Own_wand_valid; eauto. }
      apply cmra_valid_op_l, cmra_valid_op_l, cmra_valid_op_r in VALID_ALL.
      exact VALID_ALL. }
    eapply (K (fmr0 ⋅ rP) VALID_FMR_P); eauto.
    { iIntros "[FMR X]"; iMod (CUR with "FMR") as "FMR". iFrame.
      iModIntro. iApply HP. eauto. }

  - (* Assume tgt *)
    clarify.
    hexploit (Own_bupd_split fmr0); eauto.
    intros [rP [rFMR [SPLIT [HP [HFMR VALID_RP_FMR]]]]].
    steps. instantiate (1 := rP ⋅ mr_tgt).
    rewrite /assume bind_bind. steps.
    shelve. Unshelve.
    split.
    { eapply (Own_wand_valid mr_src); eauto.
      iIntros "MRS"; iMod (FMR with "MRS") as "[[[_ FMR] _] MRT]"; iMod (x1 with "FMR") as "FMR".
      iMod (SPLIT with "FMR") as "[RP _]"; iModIntro; iSplitL "RP"; iFrame.
    }
    { iIntros "(P & MRT)". iFrame. iApply HP. eauto. }
    assert (VALID_RFMR : ✓ rFMR) by
      eauto using cmra_valid_op_r.
    eapply (K rFMR VALID_RFMR); eauto.
    { iIntros "?"; iApply HFMR; eauto. }
    { iIntros "MRS"; iMod (FMR with "MRS") as "[[[CTX FMR] STATE] MRT]"; iMod (x1 with "FMR") as "FMR";
        iMod (SPLIT with "FMR") as "[P FMR]";
        iModIntro; rewrite !Own_op; iFrame.
    }

  - (* AssumeRes src *)
    clarify; steps.
    rewrite /assume bind_bind.
    move FMR at bottom. move CUR at bottom.
    steps.
    rewrite !Own_op in FMR.
    assert (MRS' : Own (r0 ⋅ mr_src) ⊢ |==>
      Own (ctx_sem ctx ⋅ (fmr0 ⋅ r0) ⋅ state_res ⋅ mr_tgt)).
    { iIntros "[R MRS]".
      iMod (FMR with "MRS") as "[[[CTX FMR] STATE] MRT]".
      iMod (x1 with "FMR") as "FMR".
      iModIntro. rewrite !Own_op. iFrame. }
    assert (VALID_FMR_R : ✓ (fmr0 ⋅ r0)).
    { assert (VALID_ALL :
        ✓ (ctx_sem ctx ⋅ (fmr0 ⋅ r0) ⋅ state_res ⋅ mr_tgt)).
      { eapply Own_wand_valid; eauto. }
      apply cmra_valid_op_l, cmra_valid_op_l, cmra_valid_op_r in VALID_ALL.
      exact VALID_ALL. }
    eapply (K (fmr0 ⋅ r0) VALID_FMR_R); eauto.
    { rewrite !Own_op CUR; iIntros "[> $ $] //". }

  - (* AssumeRes tgt *)
    clarify; steps.
    rewrite /assume bind_bind; steps.
    shelve. Unshelve.
    { eapply Own_wand_valid; [|apply WF].
      iIntros "MRS".
      iMod (FMR with "MRS") as "[[[_ FMR] _] MRT]".
      iMod (x1 with "FMR") as "FMR".
      iMod (CUR with "FMR") as "[R _]".
      iModIntro. rewrite Own_op. iFrame.
    }
    { hexploit Own_bupd_split; first apply CUR; eauto.
      intros [fmr1 [fmr2 [Hfmr [? [Hfmr2 VALID_FMR12]]]]].
      assert (VALID_FMR2 : ✓ fmr2) by
        eauto using cmra_valid_op_r.
      eapply (K fmr2 VALID_FMR2); eauto.
      { rewrite Hfmr2; iIntros "$ //". }
      { iIntros "MRS".
        iMod (FMR with "MRS") as "[[[CTX FMR] STATE] MRT]".
        iMod (x1 with "FMR") as "FMR".
        iMod (Hfmr with "FMR") as "[R FMR]".
        iPoseProof (H with "R") as "R".
        iModIntro. rewrite !Own_op. iFrame. }
    }

  - (* Guarantee src *)
    clarify.
    hexploit (Own_bupd_split fmr0); eauto.
    intros [rP [rFMR [SPLIT [HP [HFMR VALID_RP_FMR]]]]].
    steps.
    rewrite /guarantee bind_bind; steps.
    instantiate (1 := ctx_sem ctx ⋅ rFMR ⋅ state_res ⋅ mr_tgt).
    shelve. Unshelve.
    split.
    { eapply (Own_wand_valid mr_src); eauto.
      iIntros "MRS"; iMod (FMR with "MRS") as "[[[CTX FMR] STATE] MRT]"; iMod (x1 with "FMR") as "FMR".
      iMod (SPLIT with "FMR") as "[P FMR]".
      iModIntro. rewrite !Own_op. iFrame.
    }
    { iIntros "MRS"; iMod (FMR with "MRS") as "[[[CTX FMR] STATE] MRT]"; iMod (x1 with "FMR") as "FMR".
      iMod (SPLIT with "FMR") as "[P FMR]". iPoseProof (HP with "P") as "P".
      iSplitL "P"; eauto. rewrite !Own_op. iFrame. iModIntro. done.
    }
    assert (VALID_RFMR : ✓ rFMR) by
      eauto using cmra_valid_op_r.
    eapply (K rFMR VALID_RFMR); eauto.
    { iIntros "?"; iApply HFMR; eauto. }
    { eapply (Own_wand_valid mr_src); eauto.
      iIntros "MRS"; iMod (FMR with "MRS") as "[[[CTX FMR] STATE] MRT]"; iMod (x1 with "FMR") as "FMR";
        iMod (SPLIT with "FMR") as "[_ FMR]"; iModIntro; rewrite !Own_op; iFrame.
    }

  - (* Guarantee tgt *)
    clarify; steps.
    rewrite /guarantee bind_bind; steps. des.
    hexploit (Own_bupd_split); eauto.
    { hexploit (Own_wand_valid _ _ FMR); eauto using cmra_valid_op_r. }
    intros [rP [frt [UPD [HP [Hx VALID_RP_FRT]]]]].
    assert (MRS' : Own mr_src ⊢ |==>
      Own (ctx_sem ctx ⋅ (fmr0 ⋅ rP) ⋅ state_res ⋅ x)).
    { iIntros "MRS".
      iMod (FMR with "MRS") as "[[[CTX FMR] STATE] MRT]".
      iMod (UPD with "MRT") as "[P FRT]".
      iMod (x1 with "FMR") as "FMR".
      iPoseProof (Hx with "FRT") as "X".
      iModIntro. rewrite !Own_op. iFrame. }
    assert (VALID_FMR_P : ✓ (fmr0 ⋅ rP)).
    { assert (VALID_ALL :
        ✓ (ctx_sem ctx ⋅ (fmr0 ⋅ rP) ⋅ state_res ⋅ x)).
      { eapply Own_wand_valid; eauto. }
      apply cmra_valid_op_l, cmra_valid_op_l, cmra_valid_op_r in VALID_ALL.
      exact VALID_ALL. }
    eapply (K (fmr0 ⋅ rP) VALID_FMR_P); eauto.
    { iIntros "[FMR P]"; iPoseProof (HP with "P") as "P"; iMod (CUR with "FMR") as "FMR";
        iModIntro; iSplitL "P"; iFrame. }

  - (* Spawn *)
    clarify. step. ired. eapply K; eauto.
    { eapply (le_mine_trans (IstWorld Ist) my_tid); eauto; ss.
      split.
      { rewrite length_app. s. nia. }
      ii; esplits; ss; rewrite lookup_app_l; eauto using le_mine_in.
    }
    { iIntros "MRS"; iMod (FMR with "MRS") as "[[[CTX FMR] STATE] MRT]"; iMod (x1 with "FMR") as "FMR";
        iModIntro; rewrite !Own_op; iFrame.
      rewrite /ctx_sem big_opL_app /= ?right_id; eauto.
    }

  - (* Yield *)
    clarify.
    hexploit (Own_bupd_split fmr0); eauto.
    intros [ist [frame [UPD [Hist [Hframe VALID_IST_FRAME]]]]].
    guclo_lflagC; econs; try instantiate (1:=ctx_add my_tid ctx frame); eauto using ctx_set_le_others.
    step.
    { eapply interp_inv_intro with
        (mr := ist) (state_res := state_res); eauto.
      { iIntros "H"; iMod (FMR with "H") as "[[[CTX FMR] STATE] MRT]"; iMod (x1 with "FMR") as "FMR".
        iMod (UPD with "FMR") as "[IST FRAME]".
        rewrite ctx_add_sem; eauto using le_mine_in.
        iModIntro. rewrite !Own_op. iFrame.
      }
      iIntros "H"; iModIntro; iApply Hist; done.
    }
    ired. inv WF0.
    guclo_lflagC; econs; try instantiate (1:=ctx_set w1 (default ε (ctx !! my_tid)));
      eauto using ctx_set_le_others.
    assert (MRS' : Own mr_src0 ⊢ |==>
      Own (ctx_sem (ctx_set my_tid w1 (default ε (ctx !! my_tid))) ⋅
        (frame ⋅ mr) ⋅ state_res0 ⋅ mr_tgt0)).
    { iIntros "H".
      iMod (MRS with "H") as "[[[CTX FMR] STATE] MRT]".
      iModIntro. rewrite !Own_op. iFrame "FMR STATE MRT".
      rewrite -Own_op.
      erewrite (ctx_le_mine_sem my_tid (ctx_add my_tid ctx frame) w1);
        eauto using le_mine_in; cycle 1.
      { rewrite /ctx_add length_insert; eauto using le_mine_in. }
      rewrite -ctx_set_sem; cycle 1.
      { eapply le_mine_in; eauto; rewrite length_insert;
          eauto using le_mine_in. }
      rewrite /ctx_add /ctx_set list_lookup_insert;
        eauto using le_mine_in. }
    assert (VALID_FRAME_MR : ✓ (frame ⋅ mr)).
    { assert (VALID_ALL :
        ✓ (ctx_sem (ctx_set my_tid w1 (default ε (ctx !! my_tid))) ⋅
          (frame ⋅ mr) ⋅ state_res0 ⋅ mr_tgt0)).
      { eapply Own_wand_valid; eauto. }
      apply cmra_valid_op_l, cmra_valid_op_l, cmra_valid_op_r in VALID_ALL.
      exact VALID_ALL. }
    eapply (K (frame ⋅ mr) VALID_FRAME_MR); eauto; try nia.
    { iIntros "[F M]"; iMod (MR with "M") as "M"; iSplitL "M"; iModIntro; eauto. iApply Hframe; done. }
    { eapply (le_mine_trans (IstWorld Ist) my_tid).
      { apply CTXLE. }
      { split.
        { destruct WLE. unfold ctx_add, ctx_set in *.
          rewrite !length_insert in H |- *. nia. }
        intros ? Hlookup.
        rewrite Hlookup /=.
        rewrite /ctx_set list_lookup_insert; eauto.
        eapply le_mine_in; eauto; rewrite /ctx_add /ctx_set length_insert; eauto using le_mine_in.
      }
    }

  - (* GetTid *)
    clarify. step.
    lnorm_s. lnorm_t. eapply K; eauto.

  - (* Call none *)
    clarify. prep. guclo (@lsim_indC_spec Σ). econs 17.
    rewrite lookup_fmap lookup_omap; destruct (_ !! _); ss; clarify.

  - (* Spawn none *)
    clarify. prep. guclo (@lsim_indC_spec Σ). econs 18.
    rewrite lookup_fmap lookup_omap; destruct (_ !! _); ss; clarify.

  - (* progress *)
    clarify. pclearbot. gstep; econs; econs; eauto; cycle 1.
    { gfinal; left; eapply CIH; eauto. }
    by apply le_others_refl.
Qed.
