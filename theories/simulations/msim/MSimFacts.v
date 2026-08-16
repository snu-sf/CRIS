From CRIS.common Require Import StatePredicate.
From CRIS.modules Require Import Mod ModTr.
From CRIS.simulations.msim Require Import MSimCommon MSim.
From iris.proofmode Require Import proofmode.
From stdpp Require Import base.

Local Ltac msim_ist_frame_simple K FMR STEP :=
  econs; et; i; eapply K; et;
  rewrite FMR STEP; iIntros ">[? >?]"; iFrame; et.

Lemma msim_ist_frame `{!stateGS Σ} contextual fl_src fl_tgt Rs Rt RR P Q R ps pt
    (i_s : itree crisE Rs) (i_t : itree crisE Rt) fmr0 fmr
    (SIM : msim contextual fl_src fl_tgt P RR ps pt i_s i_t fmr0)
    (FMR : Own fmr ⊢
      |==> ((□ (Q ∗-∗ P ∗ R)) ∗ R) ∗ Own fmr0) :
  msim contextual fl_src fl_tgt Q
    (λ x y, R ∗ RR x y)%I ps pt i_s i_t fmr.
Proof.
  ginit. revert_until R. gcofix CIH. i.
  gstep.
  punfold SIM. move SIM before CIH. revert_until SIM.
  pattern ps, pt, i_s, i_t, fmr0.
  eapply _msim_tarski, SIM. i.
  econs. ii.
  exploit IN; et.
  { eapply Own_wand_valid, H. rewrite FMR. iIntros "[_ H]". et. }
  i; des. esplits; et.
  destruct x0.
  - (* Ret *)
    econs; et. rewrite FMR x1 RET.
    iIntros ">[[_ ?] >>?]". iFrame. et.
  - (* Call *)
    econs; et.
    { rewrite FMR x1 INV. iIntros ">[[#ACC R] >>[P FR]]".
      instantiate (1 := ((□ (Q ∗-∗ P ∗ R)) ∗ FR)%I).
      iSplitR "ACC FR".
      - iApply "ACC". iFrame. et.
      - iModIntro. iFrame "# ∗". }
    i.
    assert (INV' :
      Own fmr3 ⊢
        |==> ((□ (Q ∗-∗ P ∗ R)) ∗ R) ∗ (P ∗ FR)).
    { rewrite INV0. iIntros ">[Q [#ACC FR]]".
      iPoseProof ("ACC" with "Q") as "[P R]".
      iFrame "# ∗". et. }
    eapply Own_bupd_split in INV'; et. des.
    eapply (K vret a2); eauto using cmra_valid_op_r; cycle 1.
    + rewrite INV' INV'0. et.
    + rewrite INV'1. et.
  - (* IO *)
    msim_ist_frame_simple K FMR x1.
  - (* Inline src *)
    msim_ist_frame_simple K FMR x1.
  - (* Inline tgt *)
    msim_ist_frame_simple K FMR x1.
  - (* Tau src *)
    msim_ist_frame_simple K FMR x1.
  - (* Tau tgt *)
    msim_ist_frame_simple K FMR x1.
  - (* Choose src *)
    msim_ist_frame_simple K FMR x1.
  - (* Choose tgt *)
    msim_ist_frame_simple K FMR x1.
  - (* Take src *)
    msim_ist_frame_simple K FMR x1.
  - (* Take tgt *)
    msim_ist_frame_simple K FMR x1.
  - (* SPut src *)
    econs; et.
    { instantiate (1 :=
        (((□ (Q ∗-∗ P ∗ R)) ∗ R) ∗ FMR0)%I).
      instantiate (1 := v).
      rewrite FMR x1 CUR. iIntros ">[? >>[? ?]]". iFrame. et. }
    i.
    rewrite comm -assoc in NEW.
    eapply Own_bupd_split in NEW; et. des.
    eapply (K a2); eauto using cmra_valid_op_r; cycle 1.
    + rewrite NEW NEW0. et.
    + rewrite NEW1 comm. et.
  - (* SPut tgt *)
    econs; et.
    { instantiate (1 :=
        (((□ (Q ∗-∗ P ∗ R)) ∗ R) ∗ FMR0)%I).
      instantiate (1 := v).
      rewrite FMR x1 CUR. iIntros ">[? >>[? ?]]". iFrame. et. }
    i.
    rewrite comm -assoc in NEW.
    eapply Own_bupd_split in NEW; et. des.
    eapply (K a2); eauto using cmra_valid_op_r; cycle 1.
    + rewrite NEW NEW0. et.
    + rewrite NEW1 comm. et.
  - (* SGet src *)
    econs; et.
    { instantiate (1 :=
        (((□ (Q ∗-∗ P ∗ R)) ∗ R) ∗ FMR0)%I).
      rewrite FMR x1 CUR. iIntros ">[? >>[? ?]]". iFrame. et. }
    i.
    rewrite comm -assoc in NEW.
    eapply Own_bupd_split in NEW; et. des.
    eapply (K a2); eauto using cmra_valid_op_r; cycle 1.
    + rewrite NEW NEW0. et.
    + rewrite NEW1 comm. et.
  - (* SGet tgt *)
    econs; et.
    { instantiate (1 :=
        (((□ (Q ∗-∗ P ∗ R)) ∗ R) ∗ FMR0)%I).
      rewrite FMR x1 CUR. iIntros ">[? >>[? ?]]". iFrame. et. }
    i.
    rewrite comm -assoc in NEW.
    eapply Own_bupd_split in NEW; et. des.
    eapply (K a2); eauto using cmra_valid_op_r; cycle 1.
    + rewrite NEW NEW0. et.
    + rewrite NEW1 comm. et.
  - (* SPut src, uninitialized *)
    eapply msim_sput_src_uninit; et.
    { instantiate (1 :=
        (((□ (Q ∗-∗ P ∗ R)) ∗ R) ∗ FMR0)%I).
      rewrite FMR x1 CUR. iIntros ">[? >>[? ?]]". iFrame. et. }
    i.
    rewrite comm -assoc in NEW.
    eapply Own_bupd_split in NEW; et. des.
    eapply (K a2); eauto using cmra_valid_op_r; cycle 1.
    + rewrite NEW NEW0. et.
    + rewrite NEW1 comm. et.
  - (* SPut tgt, uninitialized *)
    eapply msim_sput_tgt_uninit; et.
    { instantiate (1 :=
        (((□ (Q ∗-∗ P ∗ R)) ∗ R) ∗ FMR0)%I).
      rewrite FMR x1 CUR. iIntros ">[? >>[? ?]]". iFrame. et. }
    i.
    rewrite comm -assoc in NEW.
    eapply Own_bupd_split in NEW; et. des.
    eapply (K a2); eauto using cmra_valid_op_r; cycle 1.
    + rewrite NEW NEW0. et.
    + rewrite NEW1 comm. et.
  - (* SGet src, uninitialized *)
    eapply msim_sget_src_uninit; et.
    { instantiate (1 :=
        (((□ (Q ∗-∗ P ∗ R)) ∗ R) ∗ FMR0)%I).
      rewrite FMR x1 CUR. iIntros ">[? >>[? ?]]". iFrame. et. }
    i.
    rewrite comm -assoc in NEW.
    eapply Own_bupd_split in NEW; et. des.
    eapply (K a2); eauto using cmra_valid_op_r; cycle 1.
    + rewrite NEW NEW0. et.
    + rewrite NEW1 comm. et.
  - (* SGet tgt, uninitialized *)
    eapply msim_sget_tgt_uninit; et.
    { instantiate (1 :=
        (((□ (Q ∗-∗ P ∗ R)) ∗ R) ∗ FMR0)%I).
      rewrite FMR x1 CUR. iIntros ">[? >>[? ?]]". iFrame. et. }
    i.
    rewrite comm -assoc in NEW.
    eapply Own_bupd_split in NEW; et. des.
    eapply (K a2); eauto using cmra_valid_op_r; cycle 1.
    + rewrite NEW NEW0. et.
    + rewrite NEW1 comm. et.
  - (* Assume src *)
    econs; et; i.
    rewrite comm -assoc in NEW.
    eapply Own_bupd_split in NEW; et. des.
    eapply (K a2); eauto using cmra_valid_op_r; cycle 1.
    + rewrite NEW NEW0. et.
    + rewrite NEW1 x1 CUR. iIntros "[>>? ?]". iFrame. et.
  - (* Assume tgt *)
    econs; et; i.
    { rewrite FMR x1 CUR. iIntros ">[? >>[? ?]]".
      instantiate (1 :=
        (((□ (Q ∗-∗ P ∗ R)) ∗ R) ∗ FMR0)%I).
      iFrame. et. }
    eapply Own_bupd_split in NEW; et. des.
    eapply (K a2); eauto using cmra_valid_op_r; cycle 1.
    + rewrite NEW NEW0. et.
    + rewrite NEW1. et.
  - (* AssumeRes src *)
    econs; et; i.
    (* { rewrite FMR x1 CUR. iIntros ">[? >>[? ?]]".
      instantiate (1:= (P ∗ FMR0)%I). iFrame. et. } *)
    rewrite comm -assoc in NEW.
    eapply Own_bupd_split in NEW; et. des.
    eapply (K a2); eauto using cmra_valid_op_r; cycle 1.
    + rewrite NEW NEW0. et.
    + rewrite NEW1 x1 CUR. iIntros "[> > ? ?]". iFrame. et.
  - (* AssumeRes tgt  *)
    econs; et; i.
    { rewrite FMR x1 CUR //. iIntros ">[? >>[? ?]]".
      instantiate (1 :=
        (((□ (Q ∗-∗ P ∗ R)) ∗ R) ∗ FMR0)%I).
      iFrame. et.
    }
    eapply Own_bupd_split in NEW; et. des.
    eapply (K a2); eauto using cmra_valid_op_r; cycle 1.
    + rewrite NEW NEW0. et.
    + rewrite NEW1; iIntros "$ //".
  - (* Guarantee src *)
    econs; et; i.
    { rewrite FMR x1 CUR. iIntros ">[? >>[? ?]]".
      instantiate (1 :=
        (((□ (Q ∗-∗ P ∗ R)) ∗ R) ∗ FMR0)%I).
      iFrame. et. }
    eapply Own_bupd_split in NEW; et. des.
    eapply (K a2); eauto using cmra_valid_op_r; cycle 1.
    + rewrite NEW NEW0. et.
    + rewrite NEW1. et.
  - (* Guarantee tgt *)
    econs; et; i.
    rewrite comm -assoc in NEW.
    eapply Own_bupd_split in NEW; et. des.
    eapply (K a2); eauto using cmra_valid_op_r; cycle 1.
    + rewrite NEW NEW0. et.
    + rewrite NEW1 x1 CUR. iIntros "[>>? ?]". iFrame. et.
  - (* Spawn *)
    msim_ist_frame_simple K FMR x1.
  - (* Yield *)
    econs; et; i.
    { rewrite FMR x1 INV. iIntros ">[[#ACC R] >>[P FR]]".
      instantiate (1 := ((□ (Q ∗-∗ P ∗ R)) ∗ FR)%I).
      iSplitR "ACC FR".
      - iApply "ACC". iFrame. et.
      - iModIntro. iFrame "# ∗". }
    assert (INV' :
      Own fmr3 ⊢
        |==> ((□ (Q ∗-∗ P ∗ R)) ∗ R) ∗ (P ∗ FR)).
    { rewrite INV0. iIntros ">[Q [#ACC FR]]".
      iPoseProof ("ACC" with "Q") as "[P R]".
      iFrame "# ∗". et. }
    eapply Own_bupd_split in INV'; et. des.
    eapply (K a2); eauto using cmra_valid_op_r; cycle 1.
    + rewrite INV' INV'0. et.
    + rewrite INV'1. et.
  - (* GetTid *)
    msim_ist_frame_simple K FMR x1.
  - (* Call none *)
    eapply msim_call_none; et.
  - (* Spawn none *)
    eapply msim_spawn_none; et.
  - (* progress *)
    pclearbot. econs; et; i.
    gbase. eapply CIH; et.
    rewrite FMR x1. iIntros ">[? >?]". iFrame. et.
Qed.
