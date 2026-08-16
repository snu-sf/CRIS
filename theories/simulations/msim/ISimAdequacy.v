From CRIS.common Require Import Common ConcRA StatePredicate.
From CRIS.modules Require Import LMod Mod SMod Sp.
From CRIS.simulations.lsim Require Import LSim LSimMod.
From CRIS.simulations.msim Require Import MSimCommon MSim
  MSimAdequacy ISim ISimFrame TacticsCommon ITactics.
From iris.proofmode Require Import proofmode.
From stdpp Require Import base list.

Local Lemma Own_exists_extract `{Σ : GRA} {X : Type}
    (a : Σ) (P : X -> iProp Σ)
    (VALID : ✓ a) (DERIV : Own a ⊢ ∃ x, P x) :
  ∃ x, Own a ⊢ P x.
Proof.
  pose proof (Own_general_soundness a (∃ x, P x)%I VALID DERIV) as HOLDS.
  uPred.unseal_in HOLDS.
  destruct HOLDS as [x HOLDS].
  exists x. eapply Own_general_completeness. exact HOLDS.
Qed.

Local Lemma Own_bupd_exists_split `{Σ : GRA} {X : Type}
    (a : Σ) (P : X -> iProp Σ) Q
    (VALID : ✓ a) (DERIV : Own a ⊢ |==> (∃ x, P x) ∗ Q) :
  ∃ x a1 a2,
    (Own a ⊢ |==> Own a1 ∗ Own a2) ∧
    (Own a1 ⊢ P x) ∧
    (Own a2 ⊢ Q).
Proof.
  eapply Own_bupd_split in DERIV as
    [a1 [a2 [UPD [HP [HQ VALID12]]]]]; eauto.
  assert (VALID1 : ✓ a1) by eauto using cmra_valid_op_l.
  destruct (Own_exists_extract a1 P VALID1 HP) as [x HPx].
  exists x, a1, a2. eauto.
Qed.

Section ISIM_ADEQUACY.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.

  (* ISim.t implies lsim_mod *)
  Lemma ISim_adequacy
    (contextual : contextuality) (ms mt : Mod.t) Ist
    : ISim.t contextual ms mt Ist ⊢ lsim_mod ms mt.
  Proof.
    eapply entails_pointwise. intros r VALID SIM.
    rewrite lsim_mod_unseal.
    eapply Own_general_completeness. cbn.
    intros WFT.
    assert (WFS : Mod.wf ms).
    { eapply Own_pure_soundness; et.
      rewrite SIM. iIntros "SIM".
      iPoseProof (ISim_wf with "SIM") as "%WF".
      iPureIntro. apply WF. done. }
    split; first done.
    intros rt rs WF SUB.
    assert (NODUPS : map_Forall (const is_Some) (Mod.initial_st ms)).
    { exact (Mod.nodup_init ms (Mod.wf_scopes ms WFS)). }
    assert (NODUPT : map_Forall (const is_Some) (Mod.initial_st mt)).
    { exact (Mod.nodup_init mt (Mod.wf_scopes mt WFT)). }
    pose (FSIM :=
      (∀ fn, ⌜fn ∈ dom (Mod.fnsems ms)⌝ →
        @ISim.sim_fun Γ Σ α β _S _I contextual ms mt Ist fn)%I).
    assert (SUB' : Own rs ⊢ |==>
      (∃ STATE : stateGS Σ,
        ((@SI_src Σ STATE (Mod.initial_st ms) ∗
          @SI_tgt Σ STATE (Mod.initial_st mt)) ∗
         (FSIM ∗ winv (∅, ∅) ∗ Ist STATE))) ∗ Own rt).
    { rewrite SUB SIM /ISim.t.
      iIntros "(RT & [INIT FUNS] & WINV)".
      iSpecialize ("INIT" $! WFT).
      iDestruct "INIT" as "[_ INIT]".
      iSpecialize ("FUNS" $! WFT).
      iDestruct "FUNS" as "[_ FUNS]".
      iDestruct "WINV" as "(ADMIN & E & WSATS)".
      iPoseProof (state_alloc
        (list_to_set (Mod.scopes ms)) (list_to_set (Mod.scopes mt))
        (Mod.initial_st ms) (Mod.initial_st mt)
        NODUPS NODUPT) as "ALLOC".
      iEval (rewrite own_bupd_unseal /own_bupd) in "ALLOC".
      iMod ("ALLOC" with "ADMIN") as "[ADMIN1 ALLOC1]".
      iDestruct "ALLOC1" as (STATE) "(SIS & SIT & PTS & PTT)".
      iSpecialize ("INIT" $! STATE with "PTS PTT").
      iAssert (winv (∅, ∅)) with "[ADMIN1 E WSATS]" as "WINV".
      { iFrame. }
      iModIntro. iSplitR "RT"; last done.
      iExists STATE. cbn [FSIM]. iFrame. }
    eapply Own_bupd_exists_split in SUB' as
      [STATE [rinit [rrt [SUBOWN [HINIT HRT]]]]]; eauto.
    cbn [FSIM] in HINIT.
    assert (VALID_INIT : ✓ rinit).
    { assert (WAND : Own rs ⊢ |==> Own (rinit ⋅ rrt)).
      { rewrite Own_op. exact SUBOWN. }
      assert (VALID_BOTH : ✓ (rinit ⋅ rrt)).
      { eapply Own_wand_valid; eauto. }
      eauto using cmra_valid_op_l. }
    assert (HINIT' : Own rinit ⊢ |==>
      ((@SI_src Σ STATE (Mod.initial_st ms) ∗
        @SI_tgt Σ STATE (Mod.initial_st mt)) ∗
       (FSIM ∗
        winv (∅, ∅) ∗ Ist STATE))).
    { iIntros "H". iModIntro. iApply HINIT. done. }
    eapply Own_bupd_split in HINIT' as
      [state_res [fmr [INITOWN [HSTATE [HFMR VALID_STATE]]]]];
      eauto.
    exists (IstWorld
      (FSIM ∗
       winv (∅, ∅) ∗ Ist STATE)%I).
    dup WFS. dup WFT. destruct WFS0, WFT0.
    constructor; ss.
    - eapply interp_inv_intro with (mr := fmr) (state_res := state_res).
      + exact WF.
      + iIntros "H". iMod (SUBOWN with "H") as "[INIT RT]".
        iMod (INITOWN with "INIT") as "[STATE FMR]".
        rewrite /ctx_sem /= left_id !Own_op.
        iModIntro. iFrame "FMR STATE". iApply HRT. done.
      + iIntros "FMR". iModIntro. iApply HFMR. done.
      + iIntros "STATE". iModIntro. iApply HSTATE. done.
      + exact NODUPS.
      + exact NODUPT.
    - ii; inv WF0. econs; eauto.
      iIntros "H". iMod (MRS with "H") as "H". iModIntro.
      unfold ctx_sem. rewrite big_opL_app. s. rewrite ?right_id; eauto.
    - intros fn fs; rewrite ?lookup_fmap lookup_omap.
      destruct (_ ms !! fn) as [[[msks its]|]|] eqn : Hms; ss; i; clarify.
      assert (TGT :
        ∃ ft,
          sandbox_fnsemmap (Mod.fnsems mt) !! fn =
            Some (Some ft)).
      { eapply Own_pure_soundness with (a := r); et.
        rewrite SIM /ISim.t.
        iIntros "SIM".
        iDestruct "SIM" as "[_ SIM]".
        iSpecialize ("SIM" $! WFT).
        iDestruct "SIM" as "[_ SIM]".
        iSpecialize ("SIM" $! fn with "[]").
        { iPureIntro. eapply elem_of_dom. eauto. }
        rewrite /ISim.sim_fun.
        iSpecialize ("SIM" $! STATE with "[] []").
        { done. }
        { done. }
        iSpecialize ("SIM" $! (SB.sandbox_body (msks, its))
          with "[]").
        { iPureIntro.
          rewrite /sandbox_fnsemmap lookup_fmap Hms //. }
        iDestruct "SIM" as (ft) "[%Hft _]".
        iPureIntro. eauto. }
      destruct TGT as [ft Hft].
      rewrite /sandbox_fnsemmap lookup_fmap in Hft.
      destruct (_ mt !! fn) as [[[mskt itt]|]|] eqn : Hmt; ss;
        clarify.
      eexists (ModTr.trans_fnsem (SB.sandbox_body (mskt, itt))).
      split.
      { rewrite ?lookup_fmap lookup_omap Hmt //. }
      intros tid ??? arg ??. inv SIMMRS.
      eapply msim_adequacy; eauto; cycle 4.
      { apply le_mine_refl. }
      { ginit; cycle 2; i.
        eapply gpaco8_mon with (r := bot8) (rg:= iunlift ibot); eauto using iunlift_ibot.
        eapply isim_init; eauto.
        iIntros "H". iApply isim_upd.
        iMod (MR with "H") as "[FUNS [I H]]".
        iDestruct "FUNS" as "#FUNS".
        iPoseProof ("FUNS" $! fn with "[]") as "FSIM".
        { iPureIntro. eapply elem_of_dom. eauto. }
        iEval (rewrite /ISim.sim_fun) in "FSIM".
        iSpecialize ("FSIM" $! STATE with "[] []").
        { done. }
        { done. }
        iSpecialize ("FSIM" $! (SB.sandbox_body (msks, its))
          with "[]").
        { iPureIntro.
          rewrite /sandbox_fnsemmap lookup_fmap Hms //. }
        iDestruct "FSIM" as (ft') "[%Hft' Hsim]".
        rewrite /sandbox_fnsemmap lookup_fmap Hmt /= in Hft'.
        clarify.
        rewrite /isim_fsem.
        iPoseProof (winv_split_empty with "[I]") as "[I I']"; et.
        iPoseProof ("Hsim" $! arg with "H I") as "ISIM".
        iModIntro. iApply isim_mono; cycle 1; i.
        { iApply (isim_ist_acc _ _ _ (FSIM ∗ winv (∅,∅)) with "[] ISIM [I']").
          - iModIntro. iSplit.
            + iIntros "($ & $ & $)". 
            + iIntros "($ & $ & $)".
          - iFrame. done.
        }
        { s. iIntros "[[FUNS WINV] [EQ IST]]". iFrame. }
      }
      { f_equal. apply map_eq; intros i; rewrite ?lookup_omap ?lookup_fmap lookup_omap.
        destruct (_ ms !! i); ss.
      }
      { f_equal. apply map_eq; intros i; rewrite ?lookup_omap ?lookup_fmap lookup_omap.
        destruct (_ mt !! i); ss.
      }
      { eapply map_Forall_fmap, map_Forall_impl; eauto; intros ? [[??]|]; ss; intros H; inv H. }
      { eapply map_Forall_fmap, map_Forall_impl; eauto; intros ? [[??]|]; ss; intros H; inv H. }
  Qed.
End ISIM_ADEQUACY.
