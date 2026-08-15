From CRIS.common Require Import Common ConcRA StatePredicate.
From CRIS.modules Require Import LMod Mod.
From CRIS.simulations.msim Require Import MSim MSimFacts
  MSimCommon ISim TacticsCommon ITactics.
From iris.proofmode Require Import proofmode.

Section ISIM_FRAME.
  Context `{!crisG Γ Σ α β τ _S _I}.
  Context `{!stateGS Σ}.

  Lemma isim_ist_frame ctx Ist P Rs Rt RR fl_src fl_tgt
      ps pt (i_s : itree crisE Rs) (i_t : itree crisE Rt) :
    P ∗ isim ctx fl_src fl_tgt Ist ibot RR ps pt i_s i_t ⊢
    isim ctx fl_src fl_tgt
      (P ∗ Ist)%I ibot (λ x y, P ∗ RR x y) ps pt i_s i_t.
  Proof using.
    eapply entails_pointwise. intros res VALID H.
    eapply isim_final.
    eapply Own_split in H as
      [rP [rSIM [EQ [HP HSIM]]]]; eauto.
    eapply isim_init in HSIM; et.
    gfinal. right.
    eapply paco8_mon; [eapply msim_ist_frame|]; ss.
    - ginit. eapply gpaco8_mon; eauto using iunlift_ibot.
    - rewrite EQ Own_op HP. et.
  Qed.

  Local Lemma isim_fsem_frame ctx fl_src fl_tgt Ist P fs ft :
    isim_fsem fl_src fl_tgt Ist ctx fs ft ⊢
    isim_fsem fl_src fl_tgt (P ∗ Ist)%I ctx fs ft.
  Proof.
    rewrite /isim_fsem. iIntros "#FSIM !#" (arg) "[P IST] W".
    iPoseProof ("FSIM" $! arg with "IST W") as "SIM".
    iCombine "P SIM" as "SIM".
    iPoseProof (isim_ist_frame with "SIM") as "SIM".
    iApply (isim_mono ctx fl_src fl_tgt (P ∗ Ist)%I ibot false false
      (λ x y, (P ∗ ist_with_eq Ist x y)%I)
      (ist_with_eq (P ∗ Ist)%I) (fs arg) (ft arg)).
    - iIntros (vsrc vtgt) "[P [-> IST]]".
      iSplit; first done.
      iSplitL "P"; done.
    - done.
  Qed.

End ISIM_FRAME.

Section ISIM_SIM_FUNS_FRAME.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Lemma ISim_sim_funs_frame ctx Ks Kt Ist P Ms Mt :
    ISim.sim_funs ctx Ks Kt Ist Ms Mt ⊢
    ISim.sim_funs ctx Ks Kt
      (λ STATE, (P STATE ∗ Ist STATE)%I) Ms Mt.
  Proof.
    rewrite /ISim.sim_funs. iIntros "SIM %WF".
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
    iApply (@isim_fsem_frame Γ Σ α β _S _I STATE).
    done.
  Qed.

End ISIM_SIM_FUNS_FRAME.
