From CRIS.common Require Import Common ConcRA StatePredicate.
From CRIS.modules Require Import LMod Mod.
From CRIS.simulations.msim Require Import MSim MSimFacts
  MSimCommon ISim TacticsCommon ITactics.
From iris.proofmode Require Import proofmode.

Section ISIM_FRAME.
  Context `{!crisG Γ Σ α β τ _S _I}.
  Context `{!stateGS Σ}.

  Lemma isim_ist_acc ctx P Q R Rs Rt RR fl_src fl_tgt
      ps pt (i_s : itree crisE Rs) (i_t : itree crisE Rt) :
    □ (Q ∗-∗ P ∗ R) ⊢
      isim ctx fl_src fl_tgt P ibot RR ps pt i_s i_t -∗
      R -∗
      isim ctx fl_src fl_tgt Q ibot
        (λ rs rt, R ∗ RR rs rt) ps pt i_s i_t.
  Proof using.
    iIntros "ACC SIM R".
    iCombine "ACC R" as "H". iCombine "H SIM" as "H".
    iStopProof.
    eapply entails_pointwise. intros res VALID H.
    eapply isim_final.
    eapply Own_split in H as [rAR [rSIM [EQ [HAR HSIM]]]]; eauto.
    eapply isim_init in HSIM; et.
    gfinal. right.
    eapply paco8_mon; [eapply msim_ist_frame|]; ss.
    - ginit. eapply gpaco8_mon; eauto using iunlift_ibot.
    - rewrite EQ Own_op HAR. et.
  Qed.

  Local Lemma isim_fsem_ist_acc ctx fl_src fl_tgt P Q fs ft :
    □ (Q -∗ P ∗ (P -∗ Q)) -∗
    isim_fsem fl_src fl_tgt P ctx fs ft -∗
    isim_fsem fl_src fl_tgt Q ctx fs ft.
  Proof.
    rewrite /isim_fsem. iIntros "#ACC #FSIM !#" (arg) "Q W".
    iPoseProof ("ACC" with "Q") as "[P CLOSE]".
    iPoseProof ("FSIM" $! arg with "P W") as "SIM".
    iApply (isim_mono ctx fl_src fl_tgt Q ibot false false
      (λ rs rt, ((P -∗ Q) ∗ ist_with_eq P rs rt)%I)
      (ist_with_eq Q) (fs arg) (ft arg)).
    - iIntros (rs rt) "[CLOSE [-> P]]".
      iSplit; first done. iApply ("CLOSE" with "P").
    - iApply (isim_ist_acc ctx P Q (P -∗ Q)%I with
        "[] SIM CLOSE").
      iModIntro. iSplit.
      + iApply "ACC".
      + iIntros "[P CLOSE]". iApply ("CLOSE" with "P").
  Qed.

End ISIM_FRAME.

Section ISIM_SIM_FUNS_FRAME.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Lemma ISim_sim_funs_ist_acc ctx Ks Kt
      (P Q : stateGS Σ → iProp Σ) Ms Mt :
    (□ ∀ STATE, Q STATE -∗ P STATE ∗ (P STATE -∗ Q STATE)) -∗
    ISim.sim_funs ctx Ks Kt P Ms Mt -∗
    ISim.sim_funs ctx Ks Kt Q Ms Mt.
  Proof.
    iIntros "#ACC SIM %WF".
    iDestruct ("SIM" $! WF) as "[%PURE SIM]".
    iSplit; first done.
    iIntros (fn) "%IN".
    iSpecialize ("SIM" $! fn with "[]"); first done.
    rewrite /ISim.sim_fun.
    iIntros (STATE).
    iIntros "%WFS %WFT" (fs) "%LOOK".
    iSpecialize ("SIM" $! STATE with "[] []"); [done|done|].
    iSpecialize ("SIM" $! fs with "[]"); first done.
    iDestruct "SIM" as (ft) "[%LOOKT FSIM]".
    iExists ft. iSplit; first done.
    iApply (@isim_fsem_ist_acc Γ Σ α β _S _I STATE).
    - iApply "ACC".
    - done.
  Qed.

End ISIM_SIM_FUNS_FRAME.
