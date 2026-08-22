From iris.proofmode Require Import proofmode.
From CRIS.common Require Import Common ConcRA.
From CRIS.modules Require Import Mod.
From CRIS.simulations.ctxrefine Require Import CtxRefine ClosedAdequacy MainAdequacy BehFacts.
From CRIS.simulations.msim Require Import Tactics TacticsInit MSimCommon ISimFacts.
From CRIS.proofmode Require Import BiEnrichedProset.

(** Properties of contextual refinement *)
Section CtxRefineFacts.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.

  Global Program Instance refines_mod_PreOrder :
    PreOrder (@refines_lmod Σ).
  Next Obligation. ii. ss. Qed.
  Next Obligation. ii. eapply H0. eapply H. ss. Qed.

  Lemma refines_refl M : ⊢ refines M M.
  Proof.
    iIntros "%WFT". iSplit; et.
  Qed.

  Lemma refines_trans M1 M2 M3 :
    refines M1 M2 ∗ refines M2 M3 ⊢ refines M1 M3.
  Proof.
    iIntros "[H1 H2] %WF1".
    iDestruct ("H1" $! WF1) as "[%WF2 H1]".
    iDestruct ("H2" $! WF2) as "[%WF3 H2]".
    iSplit; et. iIntros "WINV %t BEH1".
    iDestruct (winv_split_empty with "WINV") as "[WINV1 WINV2]".
    iApply ("H2" with "WINV2").
    iApply ("H1" with "WINV1").
    et.
  Qed.

  (*** vertical composition ***)
  Lemma ctxr_refl M : ⊢ ctx_refines M M.
  Proof.
    iIntros (Ctx). iApply refines_refl.
  Qed.

  Lemma ctxr_trans M1 M2 M3 :
    ctx_refines M1 M2 ∗ ctx_refines M2 M3 ⊢ ctx_refines M1 M3.
  Proof.
    iIntros "[H1 H2] %Ctx".
    iSpecialize ("H1" $! Ctx).
    iSpecialize ("H2" $! Ctx).
    iApply refines_trans. iFrame.
  Qed.

  Lemma ctxr_refines Mt Ms
    : ctx_refines Mt Ms ⊢ refines Mt Ms.
  Proof.
    iIntros "H". iSpecialize ("H" $! Mod.empty).
    rewrite !right_id. et.
  Qed.

  (*** algebraic equalities ***)
  Lemma ctxr_comm (M N : Mod.t)
    : ⊢ ctx_refines (M ★ N) (N ★ M).
  Proof.
    rewrite comm. eapply ctxr_refl.
  Qed.

  Lemma ctxr_assoc
    M1 M2 M3
    : ⊢ ctx_refines ((M1 ★ M2) ★ M3) (M1 ★ (M2 ★ M3)).
  Proof.
    rewrite assoc.
    eapply ctxr_refl.
  Qed.

  Lemma ctxr_swap
    M1 M2 M3
    : ⊢ ctx_refines (M1 ★ (M2 ★ M3)) ((M2 ★ M1) ★ M3).
  Proof.
    rewrite (comm _ M2 M1).
    rewrite assoc.
    eapply ctxr_refl.
  Qed.

  (*** elimination of a module ***)
  Lemma elim_module M
    : ⊢ ctx_refines M ⌽.
  Proof.
    iApply (main_adequacy _ _ (fun _ => emp%I)).
    iStopProof. cStartModSim; ss.
  Qed.

  (*** frame rules ***)
  Lemma ctxr_frameL Mt Ms C :
    ctx_refines Mt Ms ⊢ ctx_refines (C ★ Mt) (C ★ Ms).
  Proof.
    iIntros "H %Ctx".
    iSpecialize ("H" $! (C ★ Ctx)).
    rewrite (comm _ C Mt).
    rewrite (comm _ C Ms).
    rewrite !assoc; et.
  Qed.

  Lemma ctxr_frameR Mt Ms C :
    ctx_refines Mt Ms ⊢ ctx_refines (Mt ★ C) (Ms ★ C).
  Proof.
    iIntros "H %Ctx".
    iSpecialize ("H" $! (C ★ Ctx)).
    rewrite !assoc; et.
  Qed.

  (*** horizontal composition ***)
  Lemma ctxr_compose_hor
    Mt Ms Nt Ns :
    ctx_refines Mt Ms ∗ ctx_refines Nt Ns
      ⊢ ctx_refines (Mt ★ Nt) (Ms ★ Ns).
  Proof.
    iIntros "[H1 H2]".
    iPoseProof (ctxr_frameR _ _ Nt with "H1") as "H1".
    iPoseProof (ctxr_frameL _ _ Ms with "H2") as "H2".
    iApply ctxr_trans; iFrame.
  Qed.

  (*** mixed composition ***)
  Lemma ctxr_compose_mix
    Mt Ms Nt Ns C :
    ctx_refines (Mt ★ C) (Ms ★ C) ∗ ctx_refines (Nt ★ C) (Ns ★ C)
      ⊢ ctx_refines (Mt ★ Nt ★ C) (Ms ★ Ns ★ C).
  Proof.
    iIntros "[H1 H2]".
    iPoseProof (ctxr_frameL _ _ Nt with "H1") as "H1".
    iPoseProof (ctxr_frameL _ _ Ms with "H2") as "H2".
    replace (Nt ★ Mt ★ C) with (Mt ★ Nt ★ C).
    2:{
      rewrite !assoc.
      rewrite (comm _ Mt Nt).
      et.
    }
    replace (Nt ★ Ms ★ C) with (Ms ★ Nt ★ C).
    2:{
      rewrite !assoc.
      rewrite (comm _ Ms Nt).
      et.
    }
    iApply ctxr_trans; iFrame.
  Qed.

  Program Canonical ctx_refines_BiProset : BiProset (iProp Σ) :=
    {|
      proset_ob := Mod.t;
      proset_hom := ctx_refines;
      proset_unit := ⌽;
      proset_tensor := Mod.add;
    |}.
  Next Obligation.
    constructor.
    - eapply ctxr_refl.
    - eapply ctxr_trans.
  Qed.
  Next Obligation.
    constructor.
    - eapply ctxr_compose_hor.
    - intros. rewrite -assoc. eapply ctxr_refl.
    - intros. rewrite -assoc. eapply ctxr_refl.
    - intros. rewrite mod_add_empty_l. eapply ctxr_refl.
    - intros. rewrite mod_add_empty_l. eapply ctxr_refl.
    - intros. rewrite mod_add_empty_r. eapply ctxr_refl.
    - intros. rewrite mod_add_empty_r. eapply ctxr_refl.
  Qed.
  Next Obligation.
    constructor.
    - eapply ctxr_comm.
  Qed.

End CtxRefineFacts.

Section ADEQUACY.

  Context `{!crisG Γ Σ α β τ _S _I}.

  Lemma refines_adequacy
    Mt Ms
    (WF : Mod.wf Mt)
    : winv (∅,∅) ∗ refines Mt Ms
        ⊢ ⌜ ∃ rs, ✓ rs /\ refines_lmod (Mod.to_lmod Mt ε) (Mod.to_lmod Ms rs) ⌝.
  Proof.
    eapply entails_pointwise. intros rs Vrs Hrs.
    iIntros "_". iPureIntro. exists rs. split; et.
    intros t TGT.
    assert (winv (∅,∅) ⊢ Beh Mt t).
    { iIntros "WINV".
      iApply Beh_intro; et.
      iFrame. iApply Own_unit.
    }
    assert (SRC : Own rs ⊢ Beh Ms t).
    { rewrite Hrs.
      iIntros "[WINV REF]".
      iDestruct (winv_split_empty with "WINV") as "[WINV1 WINV2]".
      iDestruct ("REF" $! WF) as "[_ REF]".
      iApply ("REF" with "WINV1").
      iApply H; et.
    }
    clear - SRC Vrs.
    eapply Beh_elim in SRC; et.
  Qed.

End ADEQUACY.
