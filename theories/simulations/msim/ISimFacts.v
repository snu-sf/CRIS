From CRIS.common Require Import Common ConcRA StatePredicate.
From CRIS.modules Require Import Mod.
From CRIS.simulations.msim Require Import MSimCommon ISim.
From CRIS.simulations.msim Require Export ISimExtendCtx ISimHorComp
  ISimFrame ISimRefl.
From iris.proofmode Require Import proofmode.

Section ISIM_MODULE_REFL_COMPOSITION.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Lemma ISim_sim_funs_reflL
      (ctx : contextuality) (A B C : Mod.t)
      (Ist : stateGS Σ → iProp Σ) :
    ⊢ ISim.sim_funs ctx (C ★ A) (C ★ B)
        (λ STATE, (IstEq C STATE ∗ Ist STATE)%I) C C.
  Proof.
    iApply (ISim_sim_funs_ist_acc ctx (C ★ A) (C ★ B)
      (IstEq C) (λ STATE, (IstEq C STATE ∗ Ist STATE)%I) C C).
    - iIntros "!#" (STATE) "[EQ IST]".
      iSplitL "EQ"; first done.
      iIntros "EQ". iSplitL "EQ"; done.
    - iApply (ISim_sim_funs_extend_ctx ctx C C A B (IstEq C) C C).
      + done.
      + iApply (ISim_sim_funs_refl open C).
  Qed.

  Lemma ISim_sim_funs_reflR
      (ctx : contextuality) (A B C : Mod.t)
      (Ist : stateGS Σ → iProp Σ) :
    ⊢ ISim.sim_funs ctx (A ★ C) (B ★ C)
        (λ STATE, (Ist STATE ∗ IstEq C STATE)%I) C C.
  Proof.
    rewrite (comm _ A C) (comm _ B C).
    iApply (ISim_sim_funs_ist_acc ctx (C ★ A) (C ★ B)
      (IstEq C) (λ STATE, (Ist STATE ∗ IstEq C STATE)%I) C C).
    - iIntros "!#" (STATE) "[IST EQ]".
      iSplitR "IST"; first done.
      iIntros "EQ". iSplitL "IST"; done.
    - iApply (ISim_sim_funs_extend_ctx ctx C C A B (IstEq C) C C).
      + done.
      + iApply (ISim_sim_funs_refl open C).
  Qed.

  Lemma ISim_reflL
      (ctx : contextuality) (A B C : Mod.t)
      (Ist : stateGS Σ → iProp Σ) :
    ISim.init_ist A B Ist -∗
    ISim.sim_funs ctx (C ★ A) (C ★ B)
      (λ STATE, (IstEq C STATE ∗ Ist STATE)%I) A B -∗
    ISim.t ctx (C ★ A) (C ★ B)
      (λ STATE, (IstEq C STATE ∗ Ist STATE)%I).
  Proof.
    iIntros "INIT SIM". rewrite /ISim.t. iSplit.
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
    ISim.init_ist A B Ist -∗
    ISim.sim_funs ctx (A ★ C) (B ★ C)
      (λ STATE, (Ist STATE ∗ IstEq C STATE)%I) A B -∗
    ISim.t ctx (A ★ C) (B ★ C)
      (λ STATE, (Ist STATE ∗ IstEq C STATE)%I).
  Proof.
    iIntros "INIT SIM". rewrite /ISim.t. iSplit.
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

  Lemma ISim_ctx (ms mt C : Mod.t) Ist :
    ISim.t open ms mt Ist ⊢
    ISim.t open (ms ★ C) (mt ★ C)
      (λ STATE, (IstEq C STATE ∗ Ist STATE)%I).
  Proof.
    rewrite -(comm _ C ms) -(comm _ C mt).
    rewrite /ISim.t. iIntros "[INIT FUNS]".
    iSplitL "INIT".
    - iApply add_init_ist. iSplitR "INIT".
      + iApply ISim_init_ist_refl.
      + done.
    - iApply add_sim_funs. iSplitR "FUNS".
      + iApply ISim_sim_funs_reflL.
      + iApply (ISim_sim_funs_ist_acc _ _ _ Ist).
        { iIntros "!# %STATE [$ $] $". }
        rewrite (comm _ C ms) (comm _ C mt).
        iApply ISim_sim_funs_extend_ctx; done.
  Qed.

End ISIM_CONTEXT_EXTENSION.
