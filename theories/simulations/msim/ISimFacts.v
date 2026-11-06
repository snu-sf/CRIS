From CRIS.common Require Import Common ConcRA StatePredicate.
From CRIS.modules Require Import Mod.
From CRIS.simulations.msim Require Import MSimCommon ISim.
From CRIS.simulations.msim Require Export ISimExtendCtx ISimHorComp
  ISimFrame ISimRefl.
From iris.proofmode Require Import proofmode.

Section ISIM_MODULE_REFL_COMPOSITION.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Section SIM_FUNS.
    Context `{!stateGS Σ}.

    Lemma ISim_sim_funs_reflL
        (ctx : contextuality) (A B C : Mod.t)
        (Ist : iProp Σ) :
      ⊢ ISim.sim_funs ctx (C ★ A) (C ★ B) (IstEq C ∗ Ist) C C.
    Proof.
      iApply (ISim_sim_funs_ist_acc ctx (C ★ A) (C ★ B)
        (IstEq C) (IstEq C ∗ Ist) C C).
      - iIntros "!# [EQ IST]".
        iSplitL "EQ"; first done.
        iIntros "EQ". iSplitL "EQ"; done.
      - iApply (ISim_sim_funs_extend_ctx ctx C C A B (IstEq C) C C).
        + done.
        + iApply (ISim_sim_funs_refl open C).
    Qed.

    Lemma ISim_sim_funs_reflR
        (ctx : contextuality) (A B C : Mod.t)
        (Ist : iProp Σ) :
      ⊢ ISim.sim_funs ctx (A ★ C) (B ★ C) (Ist ∗ IstEq C) C C.
    Proof.
      rewrite (comm _ A C) (comm _ B C).
      iApply (ISim_sim_funs_ist_acc ctx (C ★ A) (C ★ B)
        (IstEq C) (Ist ∗ IstEq C) C C).
      - iIntros "!# [IST EQ]".
        iSplitR "IST"; first done.
        iIntros "EQ". iSplitL "IST"; done.
      - iApply (ISim_sim_funs_extend_ctx ctx C C A B (IstEq C) C C).
        + done.
        + iApply (ISim_sim_funs_refl open C).
    Qed.

  End SIM_FUNS.

  Lemma ISim_reflL
      (ctx : contextuality) (A B C : Mod.t)
      (Ist : stateGS Σ -> iProp Σ) :
    (∀ (STATE : stateGS Σ), ISim.init_ist A B (Ist STATE)) -∗
    (∀ (STATE : stateGS Σ), ISim.sim_funs ctx (C ★ A) (C ★ B) (IstEq C ∗ Ist STATE) A B) -∗
    ISim.t ctx (C ★ A) (C ★ B).
  Proof.
    iIntros "INIT SIM". rewrite /ISim.t.
    iIntros (STATE). iExists (IstEq C ∗ Ist STATE)%I.
    iSplit.
    - iApply add_init_ist. iSplitR "INIT".
      + iApply ISim_init_ist_refl.
      + done.
    - iApply add_sim_funs. iSplitR "SIM".
      + iApply ISim_sim_funs_reflL.
      + done.
  Qed.

  Lemma ISim_reflR
      (ctx : contextuality) (A B C : Mod.t)
      (Ist : stateGS Σ → iProp Σ) :
    (∀ (STATE : stateGS Σ), ISim.init_ist A B (Ist STATE)) -∗
    (∀ (STATE : stateGS Σ), ISim.sim_funs ctx (A ★ C) (B ★ C) (Ist STATE ∗ IstEq C) A B) -∗
    ISim.t ctx (A ★ C) (B ★ C).
  Proof.
    iIntros "INIT SIM". rewrite /ISim.t.
    iIntros (STATE). iExists (Ist STATE ∗ IstEq C)%I. iSplit.
    - iApply add_init_ist. iSplitL "INIT".
      + done.
      + iApply ISim_init_ist_refl.
    - iApply add_sim_funs. iSplitL "SIM".
      + done.
      + iApply ISim_sim_funs_reflR.
  Qed.

End ISIM_MODULE_REFL_COMPOSITION.

Section ISIM_CONTEXT_EXTENSION.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Lemma ISim_ctx (ms mt C : Mod.t) :
    ISim.t open ms mt ⊢
    ISim.t open (ms ★ C) (mt ★ C).
  Proof.
    rewrite -(comm _ C ms) -(comm _ C mt).
    rewrite /ISim.t.
    iIntros "SIM" (STATE). iSpecialize ("SIM" $! STATE).
    iDestruct "SIM" as "[%Ist SIM]". iExists (IstEq C ∗ Ist)%I.
    iDestruct "SIM" as "[INIT FUNS]". iSplitL "INIT".
    - iApply add_init_ist. iSplitR "INIT".
      + iApply ISim_init_ist_refl.
      + done.
    - iApply add_sim_funs. iSplitR "FUNS".
      + iApply ISim_sim_funs_reflL.
      + iApply (ISim_sim_funs_ist_acc _ _ _ Ist).
        { iIntros "!# [$ $] $". }
        rewrite (comm _ C ms) (comm _ C mt).
        iApply ISim_sim_funs_extend_ctx; done.
  Qed.

End ISIM_CONTEXT_EXTENSION.
