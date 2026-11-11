From CRIS.common Require Import Common ConcRA StatePredicate.
From CRIS.modules Require Import Mod LMod FSpec.
From CRIS.simulations.msim Require Import MSim MSimCommon TacticsCommon.
From CRIS.simulations.msim Require Import FnsemLookup.
From iris.proofmode Require Import environments proofmode.

Section SIM.
  Context `{!stateGS Σ}.
  Context (ctx : contextuality).
  Context (fl_src fl_tgt : gmap fname (option (Any.t → itree crisE Any.t))).
  Context (Ist : iProp Σ).

  Let _msim := _msim ctx fl_src fl_tgt Ist.
  Let rel : Type := ∀ Rs Rt,
    retr_type Σ Rs Rt → bool → bool → itree crisE Rs → itree crisE Rt → iProp Σ.

  Variant iunlift (r : rel) Rs Rt RR ps pt sti_src sti_tgt res : Prop :=
  | unlift_intro (WF : ✓ res) (REL : Own res ⊢ |==> r Rs Rt RR ps pt sti_src sti_tgt).

  Definition ibot : rel := λ _ _ _ _ _ _ _, False%I.

  Global Program Definition isim
      (g : rel) {Rs Rt} (RR : retr_type Σ Rs Rt) ps pt i_src i_tgt : iProp Σ :=
    UPred Σ (gpaco8 (_msim) (cpn8 _msim) bot8 (iunlift g) _ _ RR ps pt i_src i_tgt) _.
  Next Obligation. guclo msim_extendC_spec. econs; et. Defined.

  (***** isim lemmas *****)
  Lemma iunlift_ibot : iunlift ibot <8= bot8.
  Proof using.
    rewrite /ibot; i; inv PR.
    assert (CON : Own x7 ⊢ False).
    { iIntros "H". iPoseProof (REL with "H") as "F". iMod "F". done. }
    eapply Own_pure_soundness in CON; eauto.
  Qed.

  Lemma isim_init g g' ps pt {Rs Rt} RR sti_src sti_tgt iP fmr
      (ENTAIL : iP ⊢ (@isim g Rs Rt RR ps pt sti_src sti_tgt))
      (CUR : Own fmr ⊢ iP)
      (LEG: iunlift g <8= g') :
    gpaco8 _msim (cpn8 _msim) bot8 g' Rs Rt RR ps pt sti_src sti_tgt fmr.
  Proof using.
    guclo msim_wfC_spec; econs; ii; esplits; eauto.
    assert (SIM : Own fmr ⊢ isim g RR ps pt sti_src sti_tgt).
    { etrans; eauto. }
    eapply gpaco8_mon; et.
    hexploit (Own_general_soundness fmr); eauto.
  Qed.

  Lemma isim_final g ps pt {Rs Rt} RR sti_src sti_tgt fmr
      (SIM : gpaco8 _msim (cpn8 _msim) bot8 (iunlift g) Rs Rt RR ps pt
        sti_src sti_tgt fmr) :
    Own fmr ⊢ (@isim g Rs Rt RR ps pt sti_src sti_tgt).
  Proof using.
    rr. econs. i. rr in H0. rewrite /isim. rr.
    rewrite seal_eq /own.Own_def /uPred_ownM seal_eq in H0. ss.
    guclo msim_extendC_spec. econs; et.
  Qed.

  Lemma iunlift_mon r0 r1
      (MON : ∀ Rs Rt RR ps pt sti_src sti_tgt,
        @r0 Rs Rt RR ps pt sti_src sti_tgt ⊢ |==> @r1 Rs Rt RR ps pt sti_src sti_tgt) :
    iunlift r0 <8= iunlift r1.
  Proof using.
    i. destruct PR. econs; eauto.
    iIntros "H". iPoseProof (REL with "H") as "H".
    iMod "H". iPoseProof (MON with "H") as "H". eauto.
  Qed.

  Lemma isim_mono_knowledge g0 g1 {Rs Rt} RR ps pt sti_src sti_tgt
      (MON1 : ∀ Rs Rt RR ps pt sti_src sti_tgt,
        @g0 Rs Rt RR ps pt sti_src sti_tgt ⊢ |==> @g1 Rs Rt RR ps pt sti_src sti_tgt) :
    @isim g0 Rs Rt RR ps pt sti_src sti_tgt ⊢ @isim g1 Rs Rt RR ps pt sti_src sti_tgt.
  Proof using.
    split; intros x wfx SIM.
    eapply gpaco8_mon; first eapply SIM; eauto using iunlift_mon.
  Qed.

  Lemma isim_mono g ps pt {Rs Rt} RR0 RR1 i_src i_tgt
      (MONO : ∀ ret_src ret_tgt,
        RR0 ret_src ret_tgt ⊢ RR1 ret_src ret_tgt) :
    @isim g Rs Rt RR0 ps pt i_src i_tgt ⊢ @isim g Rs Rt RR1 ps pt i_src i_tgt.
  Proof using.
    split; intros x wfx H0.
    rewrite <-(bind_ret_r i_src); rewrite <-(bind_ret_r i_tgt).
    guclo msim_bindC_spec; econs; first apply H0.
    ii; gstep; econs; ii; esplits; eauto; econs; eauto.
    iIntros "H"; iMod (RET with "H") as "H"; iModIntro; iApply MONO; done.
  Qed.

  Lemma isim_upd g ps pt {Rs Rt} RR i_src i_tgt :
    ( |==> @isim g Rs Rt RR ps pt i_src i_tgt) ⊢ @isim g Rs Rt RR ps pt i_src i_tgt.
  Proof using.
    uPred.unseal; split; intros x wfx SIM; destruct SIM as [x' SIM].
    guclo msim_updateC_spec; econs; intros ?; exists x'; split.
    { by apply (SIM ε); rewrite right_id; done. }
    { by apply Own_Upd; rewrite cmra_discrete_total_update => z; apply (SIM z). }
  Qed.

  Global Instance isim_elim_upd g {Rs Rt} RR ps pt i_src i_tgt P p :
    ElimModal True p false ( |==> P)%I P
      (@isim g Rs Rt RR ps pt i_src i_tgt)
      (isim g RR ps pt i_src i_tgt).
  Proof using.
    unfold ElimModal. rewrite bi.intuitionistically_if_elim.
    i. iIntros "[H0 H1]".
    iApply isim_upd. iMod "H0". iModIntro.
    iApply "H1". iFrame.
  Qed.

  Lemma isim_wand g ps pt {Rs Rt} RR RR' i_src i_tgt :
    (∀ ret_src ret_tgt, RR' ret_src ret_tgt -∗ RR ret_src ret_tgt)
    ∗ @isim g Rs Rt RR' ps pt i_src i_tgt
    ⊢ isim g RR ps pt i_src i_tgt.
  Proof using.
    uPred.unseal; split; intros x wfx H; destruct H as [x1 [x2 [-> [HRR SIM]]]].
    rewrite <-(bind_ret_r i_src); rewrite <-(bind_ret_r i_tgt).
    guclo msim_frameC_spec; econs; cycle 1.
    { iIntros "H"; iDestruct "H" as "[H1 H2]"; iModIntro; iSplitL "H2"; iFrame; last by iApply "H1". }
    guclo msim_bindC_spec; econs; eauto; first by exact SIM.
    intros; gstep; econs; ii; esplits; eauto.
    econs; eauto.
    { iIntros "H1"; iPoseProof (RET with "H1") as "> HRR"; iModIntro; iIntros "H1".
      iRevert "HRR"; iStopProof; uPred.unseal; split; intros x' wfx'.
      rewrite ?own.Own_eq /own.Own_def; uPred.unseal; intros [x'' ->].
      eapply uPred_mono; last by eapply cmra_included_l.
      eapply HRR.
    }
  Qed.

  Lemma isim_frame g {Rs Rt} RR ps pt i_src i_tgt P :
    P ∗ @isim g Rs Rt RR ps pt i_src i_tgt
    ⊢ isim g (fun r_src r_tgt => P ∗ RR r_src r_tgt) ps pt i_src i_tgt.
  Proof using. iIntros "[H0 H1]". iApply isim_wand. iFrame. eauto. Qed.

  Lemma isim_bind g ps pt {Rs Rt Qs Qt} RR QQ i_src i_tgt k_src k_tgt :
    @isim g Qs Qt QQ ps pt i_src i_tgt
    ∗ (∀ ret_src ret_tgt,
        QQ ret_src ret_tgt
        -∗ isim g RR false false (k_src ret_src) (k_tgt ret_tgt))%I
    ⊢ (@isim g Rs Rt RR ps pt (i_src >>= k_src) (i_tgt >>= k_tgt)).
  Proof using.
    rewrite {3}/isim; split; intros x wfx BINDSIM; r.
    uPred.unseal_once_in BINDSIM; destruct BINDSIM as [x1 [x2 [Heq [RET BINDSIM]]]].
    eapply Own_general_completeness in RET, BINDSIM.
    guclo msim_bindC_spec; econs; eauto; ii.
    { instantiate (1:=(λ ss st, Own x2 ∗ QQ ss st)%I).
      eapply isim_init; et.
      rewrite Heq; iIntros "[H1 H2]"; iApply isim_wand; iSplitL "H2".
      - iIntros (??) "QQ"; iSplitL "H2"; iFrame. done.
      - iApply RET; done.
    }
    eapply isim_init; et.
    iIntros "FMR"; iMod (RET0 with "FMR") as "[H2 QQ]".
    iApply (BINDSIM with "H2"); iFrame.
  Qed.

  (* Simulation rules *)
  Lemma isim_ret g ps pt {Rs Rt} RR v_src v_tgt :
    RR v_src v_tgt
    ⊢ @isim g Rs Rt RR ps pt (Ret v_src) (Ret v_tgt).
  Proof using.
    split; intros x wfx RRx.
    guclo msimC_spec; econs; esplits; i; eauto; econs; eauto.
    split; intros x' wfx'; rewrite own.Own_eq /own.Own_def; uPred.unseal; intros xx'.
    exists x'; intros yf x'wf; split; eauto. eapply uPred_mono; eauto.
  Qed.

  Lemma isim_tau_src g ps pt {Rs Rt} RR i_src i_tgt :
    @isim g Rs Rt RR true pt i_src i_tgt
    ⊢ @isim g Rs Rt RR ps pt (tau;; i_src) i_tgt.
  Proof using.
    by split; intros x wfx sim; guclo msimC_spec; econs; esplits; eauto; econs; eauto.
  Qed.

  Lemma isim_tau_tgt g ps pt {Rs Rt} RR i_src i_tgt :
    @isim g Rs Rt RR ps true i_src i_tgt
    ⊢ @isim g Rs Rt RR ps pt i_src (tau;; i_tgt).
  Proof using.
    by split; intros x wfx sim; guclo msimC_spec; econs; esplits; eauto; econs; eauto.
  Qed.

  Lemma isim_io g ps pt {Rs Rt} RR I O k_src k_tgt fn (varg : I) :
    (∀ (vret : O), @isim g Rs Rt RR true true (k_src vret) (k_tgt vret))
    ⊢ isim g RR ps pt (trigger (IO fn varg) >>= k_src) (trigger (IO fn varg) >>= k_tgt).
  Proof using.
    split; intros x wfx SIM.
    guclo msimC_spec. econs; esplits; eauto. econs; eauto. intros vret.
    eapply Own_general_completeness in SIM; eauto.
    eapply isim_init; eauto.
    iIntros "H". iApply (SIM with "H"); eauto.
  Qed.

  Lemma isim_take_src X g ps pt {Rs Rt} RR k_src i_tgt :
    (∀ x, @isim g Rs Rt RR true pt (k_src x) i_tgt)
    ⊢ @isim g Rs Rt RR ps pt (trigger (Take X) >>= k_src) i_tgt.
  Proof using.
    split; intros x wfx SIM; guclo msimC_spec; econs; esplits; eauto; econs; eauto; i.
    eapply Own_general_completeness in SIM; eauto.
    eapply isim_init; eauto.
    iIntros "H". iApply (SIM with "H").
  Qed.

  Lemma isim_take_src_fspec fsp g ps pt {Rs Rt} RR k_src i_tgt :
    (∀ x, @isim g Rs Rt RR true pt (k_src (FSpec_mk _ _ (fspec_to_rel_satisfy fsp x))) i_tgt)
    ⊢ @isim g Rs Rt RR ps pt (trigger (Take (FSpec (fspec_to_rel fsp))) >>= k_src) i_tgt.
  Proof using.
    iIntros "H". iApply isim_take_src. iIntros (x). destruct x.
    rr in related. des; subst. iSpecialize ("H" $! x).
    erewrite (proof_irrelevance _ (fspec_to_rel_satisfy fsp x)); et.
  Qed.

  Lemma isim_take_tgt X g ps pt {Rs Rt} RR i_src k_tgt :
    (∃ x, @isim g Rs Rt RR ps true i_src (k_tgt x))
    ⊢ @isim g Rs Rt RR ps pt i_src (trigger (Take X) >>= k_tgt).
  Proof using.
    split; intros x wfx SIM.
    uPred.unseal_once_in SIM. destruct SIM as [k SIM].
    eapply Own_general_completeness in SIM; eauto.
    guclo msimC_spec; econs; esplits; eauto; econs; eauto; i.
    eapply isim_init; eauto.
  Qed.

  Lemma isim_take_tgt_fspec fsp g ps pt {Rs Rt} RR i_src k_tgt :
    (∃ x, @isim g Rs Rt RR ps true i_src (k_tgt (FSpec_mk _ _ (fspec_to_rel_satisfy fsp x))))
    ⊢ @isim g Rs Rt RR ps pt i_src (trigger (Take (FSpec (fspec_to_rel fsp))) >>= k_tgt).
  Proof using.
    iIntros "[%x H]". iApply isim_take_tgt. eauto.
  Qed.

  Lemma isim_choose_src X g ps pt {Rs Rt} RR k_src i_tgt :
    (∃ x, @isim g Rs Rt RR true pt (k_src x) i_tgt)
    ⊢ @isim g Rs Rt RR ps pt (trigger (Choose X) >>= k_src) i_tgt.
  Proof using.
    split; intros x wfx SIM.
    uPred.unseal_once_in SIM. destruct SIM as [k SIM].
    eapply Own_general_completeness in SIM; eauto.
    guclo msimC_spec; econs; esplits; eauto; econs; eauto; i.
    eapply isim_init; eauto.
  Qed.

  Lemma isim_choose_src_fspec fsp g ps pt {Rs Rt} RR k_src i_tgt :
    (∃ x, @isim g Rs Rt RR true pt (k_src (FSpec_mk _ _ (fspec_to_rel_satisfy fsp x))) i_tgt)
    ⊢ @isim g Rs Rt RR ps pt (trigger (Choose (FSpec (fspec_to_rel fsp))) >>= k_src) i_tgt.
  Proof using.
    iIntros "[%x H]". iApply isim_choose_src. eauto.
  Qed.

  Lemma isim_choose_tgt X g ps pt {Rs Rt} RR i_src k_tgt :
    (∀ x, @isim g Rs Rt RR ps true i_src (k_tgt x))
    ⊢ @isim g Rs Rt RR ps pt i_src (trigger (Choose X) >>= k_tgt).
  Proof using.
    split; intros x wfx SIM; guclo msimC_spec; econs; esplits; eauto; econs; eauto; i.
    eapply Own_general_completeness in SIM; eauto.
    eapply isim_init; eauto.
    iIntros "H". iApply (SIM with "H").
  Qed.

  Lemma isim_choose_tgt_fspec fsp g ps pt {Rs Rt} RR i_src k_tgt :
    (∀ x, @isim g Rs Rt RR ps true i_src (k_tgt (FSpec_mk _ _ (fspec_to_rel_satisfy fsp x))))
    ⊢ @isim g Rs Rt RR ps pt i_src (trigger (Choose (FSpec (fspec_to_rel fsp))) >>= k_tgt).
  Proof using.
    iIntros "H". iApply isim_choose_tgt. iIntros (x). destruct x.
    rr in related. des; subst. iSpecialize ("H" $! x).
    erewrite (proof_irrelevance _ (fspec_to_rel_satisfy fsp x)); et.
  Qed.

  Lemma isim_asm_src (P : Prop) g ps pt {Rs Rt} RR k_src i_tgt :
    (∀ (_ : P), @isim g Rs Rt RR true pt (k_src ()) i_tgt)
    ⊢ @isim g Rs Rt RR ps pt (assume P >>= k_src) i_tgt.
  Proof using.
    i. iIntros "H". unfold assume. rewrite bind_bind.
    iApply isim_take_src. rewrite bind_ret_l. eauto.
  Qed.

  Lemma isim_asm_tgt (P : Prop) g ps pt {Rs Rt} RR i_src k_tgt :
    P →
    @isim g Rs Rt RR ps true i_src (k_tgt ())
    ⊢ @isim g Rs Rt RR ps pt i_src (assume P >>= k_tgt).
  Proof using.
    i. iIntros "H". unfold assume. rewrite bind_bind.
    iApply isim_take_tgt. rewrite bind_ret_l. eauto.
    Unshelve. eauto.
  Qed.

  Lemma isim_guar_src (P : Prop) g ps pt {Rs Rt} RR k_src i_tgt :
    ⌜P⌝ ∗ @isim g Rs Rt RR true pt (k_src ()) i_tgt
    ⊢ @isim g Rs Rt RR ps pt (guarantee P >>= k_src) i_tgt.
  Proof using.
    iIntros "[% H]". unfold guarantee. rewrite bind_bind.
    iApply isim_choose_src. rewrite bind_ret_l. eauto.
    Unshelve. eauto.
  Qed.

  Lemma isim_guar_tgt (P : Prop) g ps pt {Rs Rt} RR i_src k_tgt :
    (∀ (_:P), @isim g Rs Rt RR ps true i_src (k_tgt ()))
    ⊢ @isim g Rs Rt RR ps pt i_src (guarantee P >>= k_tgt).
  Proof using.
    i. iIntros "H". unfold guarantee. rewrite bind_bind.
    iApply isim_choose_tgt. rewrite bind_ret_l. eauto.
  Qed.

  Lemma isim_sput_src g ps pt {Rs Rt} RR k v v' k_src i_tgt :
    k ↦src v ∗ (k ↦src v' -∗ @isim g Rs Rt RR true pt (k_src tt) i_tgt)
    ⊢ @isim g Rs Rt RR ps pt (trigger (SPut k v') >>= k_src) i_tgt.
  Proof using.
    iApply entails_pointwise. intros x Vx Hx. eapply Own_general_completeness.
    guclo msimC_spec. econs. split; et. econs; et.
    - iIntros "H". iModIntro. iApply Hx. et.
    - i. eapply isim_init; et. rewrite NEW.
      iIntros ">[H1 H2]". iApply "H2"; et.
  Qed.

  Lemma isim_sput_tgt g ps pt {Rs Rt} RR k v v' i_src k_tgt :
    k ↦tgt v ∗ (k ↦tgt v' -∗ @isim g Rs Rt RR ps true i_src (k_tgt tt))
    ⊢ @isim g Rs Rt RR ps pt i_src (trigger (SPut k v') >>= k_tgt).
  Proof using.
    iApply entails_pointwise. intros x Vx Hx. eapply Own_general_completeness.
    guclo msimC_spec. econs. split; et. econs; et.
    - iIntros "H". iModIntro. iApply Hx. et.
    - i. eapply isim_init; et. rewrite NEW.
      iIntros ">[H1 H2]". iApply "H2"; et.
  Qed.

  Lemma isim_sget_src g ps pt {Rs Rt : Type} RR k v k_src i_tgt :
    k ↦src v ∗ (k ↦src v -∗ @isim g Rs Rt RR true pt (k_src v) i_tgt)
    ⊢ @isim g Rs Rt RR ps pt (trigger (SGet k) >>= k_src) i_tgt.
  Proof using.
    iApply entails_pointwise. intros x Vx Hx. eapply Own_general_completeness.
    guclo msimC_spec. econs. split; et. econs; et.
    - iIntros "H". iModIntro. iApply Hx. et.
    - i. eapply isim_init; et. rewrite NEW.
      iIntros ">[H1 H2]". iApply "H2"; et.
  Qed.

  Lemma isim_sget_tgt g ps pt {Rs Rt} RR k v i_src k_tgt :
    k ↦tgt v ∗ (k ↦tgt v -∗ @isim g Rs Rt RR ps true i_src (k_tgt v))
    ⊢ @isim g Rs Rt RR ps pt i_src (trigger (SGet k) >>= k_tgt).
  Proof using.
    iApply entails_pointwise. intros x Vx Hx. eapply Own_general_completeness.
    guclo msimC_spec. econs. split; et. econs; et.
    - iIntros "H". iModIntro. iApply Hx. et.
    - i. eapply isim_init; et. rewrite NEW.
      iIntros ">[H1 H2]". iApply "H2"; et.
  Qed.

  Lemma isim_sput_src_uninit g ps pt {Rs Rt} RR k v' k_src i_tgt :
    uninit_src k ∗
      (k ↦src v' -∗ @isim g Rs Rt RR true pt (k_src tt) i_tgt)
    ⊢ @isim g Rs Rt RR ps pt (trigger (SPut k v') >>= k_src) i_tgt.
  Proof using.
    iApply entails_pointwise. intros x Vx Hx.
    eapply Own_general_completeness.
    guclo msimC_spec. econs. split; et.
    eapply msim_sput_src_uninit; et.
    - iIntros "H". iModIntro. iApply Hx. et.
    - i. eapply isim_init; et. rewrite NEW.
      iIntros ">[H1 H2]". iApply "H2"; et.
  Qed.

  Lemma isim_sput_tgt_uninit g ps pt {Rs Rt} RR k v' i_src k_tgt :
    uninit_tgt k ∗
      (k ↦tgt v' -∗ @isim g Rs Rt RR ps true i_src (k_tgt tt))
    ⊢ @isim g Rs Rt RR ps pt i_src (trigger (SPut k v') >>= k_tgt).
  Proof using.
    iApply entails_pointwise. intros x Vx Hx.
    eapply Own_general_completeness.
    guclo msimC_spec. econs. split; et.
    eapply msim_sput_tgt_uninit; et.
    - iIntros "H". iModIntro. iApply Hx. et.
    - i. eapply isim_init; et. rewrite NEW.
      iIntros ">[H1 H2]". iApply "H2"; et.
  Qed.

  Lemma isim_sget_src_uninit g ps pt {Rs Rt} RR k k_src i_tgt :
    uninit_src k ∗
      (uninit_src k -∗
        @isim g Rs Rt RR true pt (k_src (tt↑)) i_tgt)
    ⊢ @isim g Rs Rt RR ps pt (trigger (SGet k) >>= k_src) i_tgt.
  Proof using.
    iApply entails_pointwise. intros x Vx Hx.
    eapply Own_general_completeness.
    guclo msimC_spec. econs. split; et.
    eapply msim_sget_src_uninit; et.
    - iIntros "H". iModIntro. iApply Hx. et.
    - i. eapply isim_init; et. rewrite NEW.
      iIntros ">[H1 H2]". iApply "H2"; et.
  Qed.

  Lemma isim_sget_tgt_uninit g ps pt {Rs Rt} RR k i_src k_tgt :
    uninit_tgt k ∗
      (uninit_tgt k -∗
        @isim g Rs Rt RR ps true i_src (k_tgt (tt↑)))
    ⊢ @isim g Rs Rt RR ps pt i_src (trigger (SGet k) >>= k_tgt).
  Proof using.
    iApply entails_pointwise. intros x Vx Hx.
    eapply Own_general_completeness.
    guclo msimC_spec. econs. split; et.
    eapply msim_sget_tgt_uninit; et.
    - iIntros "H". iModIntro. iApply Hx. et.
    - i. eapply isim_init; et. rewrite NEW.
      iIntros ">[H1 H2]". iApply "H2"; et.
  Qed.

  Lemma isim_assume_src g ps pt {Rs Rt} RR iP k_src i_tgt :
    (iP -∗ (@isim g Rs Rt RR true pt (k_src tt) i_tgt))
    ⊢ @isim g Rs Rt RR ps pt (trigger (Assume iP) >>= k_src) i_tgt.
  Proof using.
    split; intros x wfx Hx.
    guclo msimC_spec; econs; esplits; i; eauto; econs; eauto.
    intros x' VALID Hx'.
    eapply Own_general_completeness in Hx.
    eapply isim_init; et.
    iIntros "X"; iMod (Hx' with "X") as "[P X]"; iPoseProof (Hx with "X P") as "I"; done.
  Qed.

  Lemma isim_assume_res_src g ps pt {Rs Rt} RR a k_src i_tgt :
    (Own a -∗ @isim g Rs Rt RR true pt (k_src ()) i_tgt)
    ⊢ @isim g Rs Rt RR ps pt (trigger (AssumeRes a) >>= k_src) i_tgt.
  Proof using.
    split; intros x wfx Hx. eapply Own_general_completeness in Hx.
    guclo msimC_spec; econs; esplits; i; eauto.
    econs; eauto.
    intros x' VALID Hx'.
    eapply isim_init; et.
    iIntros "X". iMod (Hx' with "X") as "[P X]". iPoseProof (Hx with "X P") as "SIM".
    iApply "SIM"; eauto.
  Qed.

  Lemma isim_assume_tgt g ps pt {Rs Rt} RR iP i_src k_tgt :
    (iP ∗ (@isim g Rs Rt RR ps true i_src (k_tgt tt)))
    ⊢ @isim g Rs Rt RR ps pt i_src (trigger (Assume iP) >>= k_tgt).
  Proof using.
    split; intros x wfx Hx.
    eapply Own_general_completeness in Hx.
    guclo msimC_spec; econs; esplits; i; eauto; econs; eauto.
    { iIntros "X"; iApply Hx; eauto. }
    { intros x' VALID Hx'; eapply isim_init; eauto.
      iIntros "X"; iMod (Hx' with "X") as "X"; done. }
  Qed.

  Lemma isim_assume_res_tgt g ps pt {Rs Rt} RR a i_src k_tgt :
    ((Own a ∗ @isim g Rs Rt RR ps true i_src (k_tgt ()))%I) ⊢
    @isim g Rs Rt RR ps pt i_src (trigger (AssumeRes a) >>= k_tgt).
  Proof using.
    split; intros x wfx Hx.
    eapply Own_general_completeness in Hx.
    guclo msimC_spec; econs; esplits; i; eauto. econs; eauto.
    { iIntros "A"; iPoseProof (Hx with "A") as "$"; ss. }
    intros x' VALID NEW. eapply isim_init; eauto.
    rewrite NEW. iIntros ">H". et.
  Qed.

  Lemma isim_guarantee_src g ps pt {Rs Rt} RR iP k_src i_tgt :
    (iP ∗ (@isim g Rs Rt RR true pt (k_src tt) i_tgt))
    ⊢ @isim g Rs Rt RR ps pt (trigger (Guarantee iP) >>= k_src) i_tgt.
  Proof using.
    split; intros x wfx Hx.
    eapply Own_general_completeness in Hx.
    guclo msimC_spec; econs; esplits; i; eauto; econs; eauto.
    { iIntros "X"; iApply Hx; eauto. }
    { intros x' VALID Hx'; eapply isim_init; eauto.
      iIntros "X"; iMod (Hx' with "X") as "X"; done. }
  Qed.

  Lemma isim_guarantee_tgt g ps pt {Rs Rt} RR iP i_src k_tgt :
    (iP -∗ (@isim g Rs Rt RR ps true i_src (k_tgt tt)))
    ⊢ @isim g Rs Rt RR ps pt i_src (trigger (Guarantee iP) >>= k_tgt).
  Proof using.
    split; intros x wfx Hx.
    guclo msimC_spec; econs; esplits; i; eauto; econs; eauto.
    intros x' VALID Hx'.
    eapply Own_general_completeness in Hx.
    eapply isim_init; et.
    iIntros "X"; iMod (Hx' with "X") as "[P X]".
    iPoseProof (Hx with "X P") as "I". et.
  Qed.

  Lemma isim_triggerUB_src g {Rs Rt} RR ps pt X (k_src : X -> _) i_tgt :
    ⊢ @isim g Rs Rt RR ps pt (triggerUB >>= k_src) i_tgt.
  Proof using.
    unfold triggerUB. ired. iApply isim_take_src.
    iIntros (x). destruct x.
  Qed.

  Lemma isim_triggerUB_src_trigger g {Rs Rt} RR ps pt i_tgt :
    ⊢ @isim g Rs Rt RR ps pt triggerUB i_tgt.
  Proof using.
    rewrite (@idK_spec _ _ (triggerUB)). iApply isim_triggerUB_src.
  Qed.

  Lemma isim_triggerNB_tgt g {Rs Rt} RR ps pt X i_src (k_tgt : X -> _) :
    ⊢ @isim g Rs Rt RR ps pt i_src (triggerNB >>= k_tgt).
  Proof using.
    unfold triggerNB. ired. iApply isim_choose_tgt. iIntros (x). destruct x.
  Qed.

  Lemma isim_triggerNB_trigger g {Rs Rt} RR ps pt i_src :
    ⊢ @isim g Rs Rt RR ps pt i_src triggerNB.
  Proof using.
    rewrite (@idK_spec _ _ (triggerNB)). iApply isim_triggerNB_tgt.
  Qed.

  Lemma isim_unwrapU_src g {Rs Rt} RR ps pt X (x : option X) k_src i_tgt :
    (∀ x', ⌜x = Some x'⌝ -∗ isim g RR ps pt (k_src x') i_tgt)
    ⊢ (@isim g Rs Rt RR ps pt (unwrapU x >>= k_src) i_tgt).
  Proof using.
    iIntros "H". unfold unwrapU. destruct x.
    { cNormS. iApply "H". auto. }
    { iApply isim_triggerUB_src. }
  Qed.

  Lemma isim_unwrapN_src g {Rs Rt} RR ps pt X (x : option X) k_src i_tgt :
    (∃ x', ⌜x = Some x'⌝ ∗ @isim g Rs Rt RR ps pt (k_src x') i_tgt)
    ⊢ isim g RR ps pt (unwrapN x >>= k_src) i_tgt.
  Proof using.
    iIntros "H". iDestruct "H" as (x') "[% H]". subst. cNormS. iApply "H". Qed.

  Lemma isim_unwrapU_tgt g {Rs Rt} RR ps pt X (x : option X) i_src k_tgt :
    (∃ x', ⌜x = Some x'⌝ ∗ @isim g Rs Rt RR ps pt i_src (k_tgt x'))
    ⊢ isim g RR ps pt i_src (unwrapU x >>= k_tgt).
  Proof using.
    iIntros "H". iDestruct "H" as (x') "[% H]". subst. cNormT. iApply "H".
  Qed.

  Lemma isim_unwrapN_tgt g {Rs Rt} RR ps pt X (x : option X) i_src k_tgt :
    (∀ x', ⌜x = Some x'⌝ -∗ @isim g Rs Rt RR ps pt i_src (k_tgt x'))
    ⊢ isim g RR ps pt i_src (unwrapN x >>= k_tgt).
  Proof using.
    iIntros "H". unfold unwrapN. destruct x.
    { cNormT. iApply "H". auto. }
    { iApply isim_triggerNB_tgt. }
  Qed.

  Lemma isim_call g ps pt {Rs Rt} RR k_src k_tgt fn varg :
    Ist ∗
    (∀ vret, Ist -∗ @isim g Rs Rt RR true true (k_src vret) (k_tgt vret)) ⊢
    isim g RR ps pt
      (trigger (Call fn varg) >>= k_src) (trigger (Call fn varg) >>= k_tgt).
  Proof using.
    split; intros x wfx Hx. uPred.unseal_once_in Hx. destruct Hx as [x1 [x2 [-> [Hx1 Hx2]]]].
    guclo msimC_spec. econs; esplits; eauto.
    econs; eauto; i; subst.
    { iIntros "[X1 X2]"; iSplitL "X1".
      { iModIntro; iStopProof; split. i; eapply uPred_mono; eauto.
        rewrite own.Own_eq /own.Own_def in H1.
        uPred.unseal_in H1; eauto.
      }
      { iPoseProof (Own_general_completeness with "X2") as "X2"; eauto. }
    }
    guclo msim_updateC_spec. econs; ii; esplits; eauto.
    eapply isim_init; eauto.
    iIntros "H". iPoseProof (INV with "H") as "H". iApply isim_upd.
    iMod "H". iDestruct "H" as "[X B]".
    iSpecialize ("B" $! vret).
    iApply "B"; eauto.
  Qed.

  Lemma isim_inline_src g ps pt {Rs Rt} RR k_src i_tgt f fn varg
      (FIND : fl_src !! (funid fn) = Some (Some f)) :
    @isim g Rs Rt RR true pt (ret <- f varg;; tau;; k_src ret) i_tgt
    ⊢ @isim g Rs Rt RR ps pt (trigger (Call fn varg) >>= k_src) i_tgt.
  Proof using.
    split. intros x wfx SIM. guclo msimC_spec. econs. esplits; eauto. econs; eauto.
    match goal with
    | |- gpaco8 _ _ _ _ _ _ _ _ _ ?i_src _ _ =>
        replace i_src with (ret <- f varg;; tau;; k_src ret)
    end.
    2:{
      rewrite bind_bind. f_equal. extensionalities ret.
      rewrite bind_tau. rewrite bind_ret_l. f_equal.
    }
    eapply SIM.
  Qed.

  Lemma isim_inline_tgt g ps pt {Rs Rt} RR i_src k_tgt f fn varg
      (FIND : fl_tgt !! (funid fn) = Some (Some f)) :
    @isim g Rs Rt RR ps true i_src (ret <- f varg;; tau;; k_tgt ret)
    ⊢ @isim g Rs Rt RR ps pt i_src (trigger (Call fn varg) >>= k_tgt).
  Proof using.
    split. intros x wfx SIM. guclo msimC_spec. econs. esplits; eauto. econs; eauto.
    match goal with
    | |- gpaco8 _ _ _ _ _ _ _ _ _ _ ?i_tgt _ =>
        replace i_tgt with (ret <- f varg;; tau;; k_tgt ret)
    end.
    2:{
      rewrite bind_bind. f_equal. extensionalities ret.
      rewrite bind_tau. rewrite bind_ret_l. f_equal.
    }
    eapply SIM.
  Qed.

  Lemma isim_spawn g ps pt {Rs Rt} RR k_src k_tgt fn arg :
    (∀ tid, @isim g Rs Rt RR true true (k_src tid) (k_tgt tid)) ⊢
    isim g RR ps pt
      (trigger (Spawn fn arg) >>= k_src) (trigger (Spawn fn arg) >>= k_tgt).
  Proof using.
    split; intros x wfx SIM%Own_general_completeness.
    guclo msimC_spec; econs; esplits; eauto; econs; eauto.
    i. eapply isim_init; eauto; iIntros "X"; iPoseProof (SIM with "X") as "X"; done.
  Qed.

  Lemma isim_yield g ps pt {Rs Rt} RR k_src k_tgt tid :
    Ist ∗ (Ist -∗ @isim g Rs Rt RR true true (k_src ()) (k_tgt ())) ⊢
    isim g RR ps pt
      (trigger (Yield tid) >>= k_src) (trigger (Yield tid) >>= k_tgt).
  Proof using.
    split; intros x wfx Hx. uPred.unseal_once_in Hx. destruct Hx as [x1 [x2 [-> [Hx1 Hx2]]]].
    guclo msimC_spec. econs; esplits; eauto.
    econs; eauto; i; subst.
    { iIntros "[X1 X2]"; iSplitL "X1".
      { iModIntro; iStopProof; split. i; eapply uPred_mono; eauto. rewrite own.Own_eq /own.Own_def in H1.
        uPred.unseal_in H1; eauto.
      }
      { iPoseProof (Own_general_completeness with "X2") as "X2"; eauto. }
    }
    guclo msim_updateC_spec. econs; ii; esplits; eauto.
    eapply isim_init; eauto.
    iIntros "H". iPoseProof (INV with "H") as "H". iApply isim_upd.
    iMod "H". iDestruct "H" as "[X B]".
    iApply "B"; eauto.
  Qed.

  Lemma isim_gettid g ps pt {Rs Rt} RR k_src k_tgt :
    (∀ tid, @isim g Rs Rt RR true true (k_src tid) (k_tgt tid)) ⊢
    isim g RR ps pt (trigger GetTid >>= k_src) (trigger GetTid >>= k_tgt).
  Proof.
    split; intros x wfx SIM.
    guclo msimC_spec. econs; esplits; eauto. econs; eauto. intros tid.
    eapply Own_general_completeness in SIM; eauto.
    eapply isim_init; eauto.
    iIntros "H". iApply (SIM with "H"); eauto.
  Qed.

  Lemma isim_call_none
      g ps pt {Rs Rt} RR k_src i_tgt fn varg
      (CLOSED: ctx = closed)
      (FIND: fl_src !! (funid fn) = None) :
    ⊢ (@isim g Rs Rt RR ps pt (trigger (Call fn varg) >>= k_src) i_tgt).
  Proof using.
    split; intros x wfx SIM; guclo msimC_spec. econs; esplits; eauto.
    eapply msim_call_none; et.
  Qed.

  Lemma isim_spawn_none
    g ps pt {Rs Rt} RR k_src i_tgt fn varg
    (CLOSED: ctx = closed)
    (FIND: fl_src !! (funid fn) = None)
  :
  ⊢ (@isim g Rs Rt RR ps pt (trigger (Spawn fn varg) >>= k_src) i_tgt).
  Proof using.
    split; intros x wfx SIM; guclo msimC_spec. econs; esplits; eauto.
    eapply msim_spawn_none; et.
  Qed.

  Lemma isim_reset g {Rs Rt} RR ps pt sti_src sti_tgt :
    @isim g Rs Rt RR false false sti_src sti_tgt
    ⊢ @isim g Rs Rt RR ps pt sti_src sti_tgt.
  Proof using.
    split; intros x wfx SIM. eapply msim_flag_down. eauto.
  Qed.

  Lemma isim_progress g {Rs Rt} RR sti_src sti_tgt:
    g Rs Rt RR false false sti_src sti_tgt
    ⊢ @isim g Rs Rt RR true true sti_src sti_tgt.
  Proof using.
    split; intros x wfx SIM; eapply msim_progress_flag.
    rr in SIM. eapply Own_general_completeness in SIM.
    gfinal. left. econstructor; eauto. rewrite SIM. eauto.
  Qed.

  Lemma isim_flag_mon g {Rs Rt} RR i_src i_tgt (ps pt ps' pt' : bool)
      (PSLE : ps' → ps) (PTLE : pt' → pt) :
    @isim g Rs Rt RR ps' pt' i_src i_tgt
    ⊢ @isim g Rs Rt RR ps pt i_src i_tgt.
  Proof using. split; intros x wfx SIM. guclo msim_flagC_spec. econs; eauto. eapply SIM. Qed.

  Lemma isim_coind (g : rel) A (P: A → _) RsA RtA RRA psA ptA srcA tgtA
    (COIND: ∀ (g0 : rel)
        (INC: ∀ Rs Rt RR ps pt src tgt, g Rs Rt RR ps pt src tgt ⊢ g0 Rs Rt RR ps pt src tgt)
        (CIH: ∀ a, P a ⊢ g0 (RsA a) (RtA a) (RRA a) (psA a) (ptA a) (srcA a) (tgtA a)),
      ∀ a, P a ⊢ @isim g0 (RsA a) (RtA a) (RRA a) (psA a) (ptA a) (srcA a) (tgtA a))
    :
    ∀ a, P a ⊢ @isim g (RsA a) (RtA a) (RRA a) (psA a) (ptA a) (srcA a) (tgtA a).
  Proof using.
    i. iIntros "H". iPoseProof (bupd_intro with "H") as "H". iStopProof.
    split; intros x wfx Px.
    revert_until COIND. gcofix CIH. i.
    pose (g' :=
      (λ Rs Rt RR ps pt src tgt,
        g Rs Rt RR ps pt src tgt
        ∨ ∃ a, P a
          ∗ ⌜@existT (Type*Type)%type (fun '(_,_) => _) (Rs, Rt) (RR,ps,pt,src,tgt)
            = existT (RsA a, RtA a) (RRA a,psA a,ptA a,srcA a,tgtA a)⌝)%I).
    specialize (COIND g').
    uPred.unseal_once_in Px; destruct Px as [x' Px].
    guclo msim_updateC_spec; econs; ii; exists x'; split; cycle 1.
    { apply Own_Upd; rewrite cmra_discrete_total_update; intros yf; eapply Px; eauto. }
    eapply gpaco8_mon.
    { eapply COIND; eauto.
      { iIntros (???????) "X". iLeft; eauto. }
      { iIntros (?) "P"; iRight; iExists a0; iSplitL "P"; iFrame.
        iPureIntro; eauto.
      }
      { specialize (Px ε); rewrite ?right_id in Px; eapply Px; eauto. }
      { eapply Own_general_soundness.
        { specialize (Px ε); rewrite ?right_id in Px; eapply Px; eauto. }
        iIntros "X".
        specialize (Px ε); rewrite ?right_id in Px; hexploit (Px); eauto.
        i; des. iPoseProof (Own_general_completeness with "X") as "X"; eauto.
      }
    }
    { ii; eauto. }
    { ii. inv PR.
      uPred.unseal_once_in REL. destruct REL as [REL]. hexploit REL; eauto.
      { rewrite own.Own_eq /own.Own_def; uPred.unseal; rr.
        exists ε; rewrite right_id; ss. }
      intros UPD. destruct UPD as [x7']. dup H0.
      specialize (H0 ε). rewrite ?right_id in H0. hexploit H0; eauto; i; des.
      rr in H3. rewrite seal_eq in H3; ss.
      destruct H3.
      { apply CIH0; econs; eauto.
        iIntros "X"; iMod (Own_Upd with "X") as "X"; cycle 1.
        { eapply Own_general_completeness in H3; iModIntro; iApply H3; done. }
        { rewrite cmra_discrete_total_update; intros frame wf7; eapply (H1 frame); eauto. }
      }
      { rr in H3. rewrite seal_eq in H3; ss. des.
        rr in H3. rewrite seal_eq in H3; ss. des.
        rr in H5. rewrite seal_eq in H5; ss. depdes H5.
        eapply CIH; eauto.
        uPred.unseal; exists x7'; split.
        { eapply (H1 yf); eauto. }
        { eapply Own_general_soundness; eauto.
          rewrite H3; iIntros "[X _]"; eapply Own_general_completeness in H4; eauto.
          iApply H4; eauto.
        }
      }
    }
  Qed.

End SIM.

Arguments isim {_ _} _ _ _ _ _ {_ _} _ _ _ _ _.
Global Opaque isim.

Section FancyReal.
  Context `{!stateGS Σ}.
  Context (ctx : contextuality).
  Context (fl_s fl_t : gmap fname (option (Any.t → itree crisE Any.t))).
  Context (Ist : iProp Σ).

  Local Notation isim := (isim ctx fl_s fl_t Ist).

  Context (R_s R_t : Type).
  Context (RR : retr_type Σ R_s R_t).
  Context (ps pt : bool).

  (* Precise Pre & Post conditions *)
  Lemma isim_ru_src_advanced_general (pp: _→_→Prop) g k_s i_t :
    (∃ (I P : iProp Σ),
      I ∗ precise P ∗
      (∀ pre post (VS: pp pre post), ∃ T, (I -∗ pre -∗ □ T) ∗ (□ T -∗ pre ==∗ P ∗ post)) ∗
      (I -∗ P -∗ isim g RR true pt (k_s ()) i_t)) ⊢
    isim g RR ps pt (RealUpdate pp >>= k_s) i_t.
  Proof using.
    iIntros "[%I [%P [I [#[%pr Pre] [Hsplit Hsim]]]]]".
    iRevert "Hsplit Hsim Pre"; iStopProof.
    eapply entails_pointwise; iIntros (res _ Hres) "I Hsplit Hsim #[Hpre1 Hpre2]".
    rewrite /RealUpdate; unseal CRIS_FancyReal.
    cNormS; iApply isim_choose_src; iExists (pr ⋅ res).
    cNormS; iApply isim_guarantee_src; iSplitL "I Hsplit".
    { iIntros (pre post VS) "Pre".
      iPoseProof ("Hsplit" $! pre post VS) as "[%T [HT Hsplit]]".
      iPoseProof ("HT" with "[I] Pre") as "#T".
      { rewrite Hres; iFrame. }
      iMod ("Hsplit" with "T Pre") as "[P $]".
      rewrite Own_op; iFrame "I". iApply "Hpre2"; done.
    }
    cNormS; iApply isim_assume_res_src; iIntros "[P R]"; rewrite Hres.
    iMod ("Hpre1" with "P") as "P".
    cNormS. iPoseProof ("Hsim" with "R P") as "$".
  Qed.

  Lemma isim_ru_src_advanced {X} (pre post: X → _) g k_s i_t:
    (∃ (I P : iProp Σ),
      I ∗ precise P ∗
      (∀ x, ∃ T, (I -∗ pre x -∗ □ T) ∗ (□ T -∗ pre x ==∗ P ∗ post x)) ∗
      (I -∗ P -∗ isim g RR true pt (k_s ()) i_t)) ⊢
    isim g RR ps pt (RealUpdate (idx_to_rel pre post) >>= k_s) i_t.
  Proof.
    iIntros "[%[% [I [P [A B]]]]]".
    iApply (isim_ru_src_advanced_general (idx_to_rel pre post)).
    iFrame. iIntros (???). rr in VS; des; subst. iApply "A".
  Qed.

  Lemma isim_ru_src_general (pp: _→_→Prop) g k_s i_t :
    (∃ (P : iProp Σ),
      precise P ∗
      (∀ pre post (VS: pp pre post), pre ==∗ P ∗ post) ∗
      (P -∗ isim g RR true pt (k_s ()) i_t)) ⊢
    isim g RR ps pt (RealUpdate pp >>= k_s) i_t.
  Proof using.
    iIntros "[%P [Hprecise [Hsplit Hsim]]]".
    iApply isim_ru_src_advanced_general.
    iExists True%I, P.
    iSplit; [done|iSplit; [done|]].
    iSplitL "Hsplit".
    { iIntros (? ? ?); iExists emp%I; iSplitR; [iIntros "_ _"; done|].
      by iIntros "_ Pre"; iApply "Hsplit".
    }
    by iIntros "_"; iApply "Hsim".
  Qed.

  Lemma isim_ru_src {X} (pre post: X → _) g k_s i_t:
    (∃ (P : iProp Σ),
      precise P ∗
      (∀ x, pre x ==∗ P ∗ post x) ∗
      (P -∗ isim g RR true pt (k_s ()) i_t)) ⊢
    isim g RR ps pt (RealUpdate (idx_to_rel pre post) >>= k_s) i_t.
  Proof.
    iIntros "[% [? [A ?]]]".
    iApply (isim_ru_src_general (idx_to_rel pre post)).
    iFrame. iIntros (???). rr in VS; des; subst. iApply "A".
  Qed.

  Lemma isim_ru_tgt_general
      (pp: _→_→Prop)
      g
      i_s k_t
    :
    (∀ pr,
     (∀ pre post (VS: pp pre post), pre ==∗ Own pr ∗ post) -∗
     isim g RR ps true i_s (trigger (AssumeRes pr);;; k_t ()))
    ⊢
    isim g RR ps pt
      i_s
      (RealUpdate pp >>= k_t).
  Proof.
    iIntros "H".
    rewrite /RealUpdate; unseal CRIS_FancyReal.
    cNormT; iApply isim_choose_tgt; iIntros (pr).
    cNormT; iApply isim_guarantee_tgt; iIntros "UPD".
    iPoseProof ("H" $! pr with "UPD") as "SIM". cNormT.
    replace (x <- trigger (AssumeRes pr);; x <- Ret x;; k_t x) with
      (trigger (AssumeRes pr);;; k_t ()); et.
    f_equal. extensionalities. ired. destruct H. et.
  Qed.

  Lemma isim_ru_tgt {X} (pre post: X → _)
      g
      i_s k_t
    :
    (∀ pr,
     (∀ x, pre x ==∗ Own pr ∗ post x) -∗
     isim g RR ps true i_s (trigger (AssumeRes pr);;; k_t ()))
    ⊢
    isim g RR ps pt
      i_s
      (RealUpdate (idx_to_rel pre post) >>= k_t).
  Proof.
    iIntros "H".
    iApply (isim_ru_tgt_general (idx_to_rel pre post)).
    iIntros (?) "A". iApply "H". iIntros (?) "H".
    assert (PF: ∃ x0, pre x = pre x0 ∧ post x = post x0); et.
    iSpecialize ("A" $! _ _ PF).
    iApply "A". et.
  Qed.

  Lemma isim_ru_tgt_simple_general (pp: _→_→Prop) g i_s k_t :
    (∃ pre post, ⌜pp pre post⌝ ∗ pre ∗ (post -∗ isim g RR ps true i_s (k_t ())))
    ⊢
    isim g RR ps pt i_s (RealUpdate pp >>= k_t).
  Proof using.
    iIntros "[%pre [%post [%VS [Hpre Hsim]]]]".
    iApply isim_ru_tgt_general.
    iIntros (?) "U".
    iPoseProof ("U" $! _ _ VS with "Hpre") as ">[P Hpost]".
    iApply isim_assume_res_tgt. iFrame.
    iApply "Hsim". et.
  Qed.

  Lemma isim_ru_tgt_simple {X} (pre post: X → _) g i_s k_t :
    (∃ x, pre x ∗ (post x -∗ isim g RR ps true i_s (k_t ())))
    ⊢
    isim g RR ps pt i_s (RealUpdate (idx_to_rel pre post) >>= k_t).
  Proof.
    iIntros "[% H]".
    iApply (isim_ru_tgt_simple_general (idx_to_rel pre post)).
    iFrame. iPureIntro. rr; esplits; eauto.
  Qed.

End FancyReal.

Section FSEM.

  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.
  Context `{!stateGS Σ}.

  Definition isim_fsem fl_src fl_tgt Ist ctx (fs ft : Any.t → itree crisE Any.t) : iProp Σ :=
    □ ∀ arg,
        Ist
        -∗ winv (∅,∅)
        -∗ @isim
           Σ _ ctx fl_src fl_tgt Ist ibot Any.t Any.t (ist_with_eq Ist)
           false false (fs arg) (ft arg).

End FSEM.

Definition sandbox_fnsemmap `{Σ : GRA} (fns : gmap fname (option (emask * fbody))) :=
  (λ v : option _, SB.sandbox_body <$> v) <$> fns.
Arguments sandbox_fnsemmap : simpl never.
Global Instance fnsem_lookup_result_sandbox `{Σ : GRA}
    (m : @Mod.t Σ) fn result
    `{Hlookup : !FnsemLookupResult (Mod.fnsems m) fn result} :
  FnsemLookupResult (sandbox_fnsemmap (Mod.fnsems m)) fn
    ((λ x : option (emask * fbody), SB.sandbox_body <$> x) <$> result).
Proof.
  constructor. rewrite /sandbox_fnsemmap lookup_fmap
    fnsem_lookup_result_eq //.
Qed.
Global Hint Extern 1
  (FnsemLookupResult (sandbox_fnsemmap (Mod.fnsems _)) _ _) =>
  lazymatch goal with
  | |- FnsemLookupResult (sandbox_fnsemmap (Mod.fnsems ?m)) ?fn _ =>
      let MT := type of (Mod.fnsems m) in
      lazymatch MT with
      | gmap _ ?A =>
          let r := open_constr:(_ : option A) in
          notypeclasses refine
            (@fnsem_lookup_result_sandbox _ m fn r _)
      end
  end : fnsem_lookup.
Global Hint Extern 80 (sandbox_fnsemmap _ !! _ = Some _) =>
  rewrite /sandbox_fnsemmap; simpl_map : simpl_map.

Module ISim.
  Section ISim.

    Context `{!crisG Γ Σ α β τ _S _I}.
    Open Scope bi_scope.

    Section Internal.
    Context `{!stateGS Σ}.

    Definition init_ist
      (Ms Mt : Mod.t)
      (Ist :  iProp Σ)
      : iProp Σ :=
      ⌜ Mod.wf Mt ⌝ →
      ⌜ Ms.(Mod.scopes) ⊆+ Mt.(Mod.scopes) ⌝
      ∧ 
      (state_init_src (list_to_set Ms.(Mod.scopes)) Ms.(Mod.initial_st) _ -∗
       state_init_tgt (list_to_set Mt.(Mod.scopes)) Mt.(Mod.initial_st) _ -∗
       Ist).

    Definition sim_fun
      (ctx : contextuality)
      (Ks Kt : Mod.t)
      (Ist : iProp Σ)
      (fn : fname)
      : iProp Σ :=
      let fl_src := sandbox_fnsemmap Ks.(Mod.fnsems) in
      let fl_tgt := sandbox_fnsemmap Kt.(Mod.fnsems) in
      ⌜ Mod.wf Ks ⌝ →
      ⌜ Mod.wf Kt ⌝ →
      ∀ fs, ⌜ fl_src !! fn = Some (Some fs) ⌝ →
      ∃ ft, ⌜ fl_tgt !! fn = Some (Some ft) ⌝ ∧
              isim_fsem fl_src fl_tgt Ist ctx fs ft.

    Definition sim_funs
      (ctx : contextuality)
      (Ks Kt : Mod.t)
      (Ist : iProp Σ)
      (Ms Mt : Mod.t)
      : iProp Σ :=
      ⌜ Mod.wf Mt ⌝ →
      ⌜ map_Forall (const is_Some) Ms.(Mod.fnsems) ∧
        dom Ms.(Mod.fnsems) ⊆ dom Mt.(Mod.fnsems) ⌝ ∧
        ∀ fn, ⌜ fn ∈ dom Ms.(Mod.fnsems) ⌝ → sim_fun ctx Ks Kt Ist fn.

    End Internal.

    Definition t
      (ctx : contextuality)
      (Ms Mt : Mod.t)
      : iProp Σ :=
      ∀ STATE: stateGS Σ,
      ∃ Ist: iProp Σ,
      init_ist Ms Mt Ist ∗ sim_funs ctx Ms Mt Ist Ms Mt.

  End ISim.
End ISim.

Section ISIM_WELLFORMEDNESS.

  Context `{!crisG Γ Σ α β τ _S _I, !stateGpreS Σ}.

  Lemma ISim_wf ctx ms mt :
    ISim.t ctx ms mt ⊢ ⌜Mod.wf mt -> Mod.wf ms⌝.
  Proof.
    iIntros "SIM %WFT".
    iDestruct ("SIM" $! (Build_stateGS _ _ 1%positive 1%positive)) as "[%Ist [INIT SIM]]".
    iDestruct ("INIT" $! WFT) as "[%SCP _]".
    iDestruct ("SIM" $! WFT) as "[%PURE _]".
    destruct PURE as [SOME _].
    iPureIntro. econs; et.
    eapply submseteq_NoDup; et. apply WFT.
  Qed.

  Lemma ISim_dom contextual ms mt :
    ISim.t contextual ms mt
      ⊢ ⌜ Mod.wf mt -> dom (Mod.fnsems ms) ⊆ dom (Mod.fnsems mt) ⌝.
  Proof.
    iIntros "SIM %WFT".
    iDestruct ("SIM" $! (Build_stateGS _ _ 1%positive 1%positive)) as "[%Ist [_ SIM]]".
    iDestruct ("SIM" $! WFT) as "[%PURE _]".
    destruct PURE as [_ DOM].
    iPureIntro. exact DOM.
  Qed.

End ISIM_WELLFORMEDNESS.

Notation "E1 '------------------------------------------------------------------□' E2 '------------------------------------------------------------------∗' g ps pt '-------------------------------isim-------------------------------' itr_src itr_tgt '{' RR '}'" :=
  (environments.envs_entails (Envs E1 E2 _)
    (isim _ _ _ _ g RR ps pt itr_src itr_tgt))
    (at level 50, only printing,
     format "E1 '------------------------------------------------------------------□' '//' E2 '------------------------------------------------------------------∗' '//' g  ps  pt '//' '-------------------------------isim-------------------------------' '//' itr_src '//' '//' itr_tgt '//' '{'  RR  '}'").

Notation "E1 '------------------------------------------------------------------□' g ps pt '-------------------------------isim-------------------------------' itr_src itr_tgt '{' RR '}'" :=
  (environments.envs_entails (Envs E1 Enil _)
    (isim _ _ _ _ g RR ps pt itr_src itr_tgt))
    (at level 50, only printing,
     format "E1 '------------------------------------------------------------------□' '//' g  ps  pt '//' '-------------------------------isim-------------------------------' '//' itr_src '//' '//' itr_tgt '//' '{'  RR  '}'").

Notation "E2 '------------------------------------------------------------------∗' g ps pt '-------------------------------isim-------------------------------' itr_src itr_tgt '{' RR '}'" :=
  (environments.envs_entails (Envs Enil E2 _)
    (isim _ _ _ _ g RR ps pt itr_src itr_tgt))
    (at level 50, only printing,
     format "E2 '------------------------------------------------------------------∗' '//' g  ps  pt '//' '-------------------------------isim-------------------------------' '//' itr_src '//' '//' itr_tgt '//' '{'  RR  '}'").

Notation "'------------------------------------------------------------------∗' g ps pt '-------------------------------isim-------------------------------' itr_src itr_tgt '{' RR '}'" :=
  (environments.envs_entails (Envs Enil Enil _)
    (isim _ _ _ _ g RR ps pt itr_src itr_tgt))
    (at level 50, only printing,
     format "'------------------------------------------------------------------∗' '//' g  ps  pt '//' '-------------------------------isim-------------------------------' '//' itr_src '//' '//' itr_tgt '//' '{'  RR  '}'").
