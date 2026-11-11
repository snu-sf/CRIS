From CRIS.common Require Import Common ConcRA StatePredicate.
From CRIS.modules Require Import Mod.
From CRIS.simulations.msim Require Import MSimCommon ISim.
From iris.proofmode Require Import proofmode.

Local Lemma sandbox_fnsemmap_add_l `{Σ : GRA} (K C : Mod.t)
    (WF : Mod.wf (K ★ C)) :
  sandbox_fnsemmap (Mod.fnsems K) ⊆
    sandbox_fnsemmap (Mod.fnsems (K ★ C)).
Proof.
  apply map_omap_mono, map_subseteq_spec. intros fn f LOOK.
  eapply lookup_fnsems_l; eauto.
Qed.

Section ISIM_EXTEND_CTX.
  Context `{!crisG Γ Σ α β τ _S _I, !stateGS Σ}.

  Lemma ISim_sim_fun_extend_ctx
      (ctx : contextuality) (Ks Kt Cs Ct : Mod.t)
      (Ist : iProp Σ) fn :
    ISim.sim_fun open Ks Kt Ist fn ⊢
    ISim.sim_fun ctx (Ks ★ Cs) (Kt ★ Ct) Ist fn.
  Proof.
    rewrite /ISim.sim_fun.
    iIntros "SIM" (WFS WFT fl_src EXTS fl_tgt EXTT).
    destruct (Mod.add_wf_inv Ks Cs WFS) as [WFKS _].
    destruct (Mod.add_wf_inv Kt Ct WFT) as [WFKT _].
    iSpecialize ("SIM" $! WFKS WFKT fl_src with "[]").
    { iPureIntro. apply ISim.fnsem_ext_open.
      etrans; first by apply sandbox_fnsemmap_add_l.
      exact (ISim.fnsem_ext_subseteq _ _ _ EXTS). }
    iApply ("SIM" $! fl_tgt with "[]").
    iPureIntro. apply ISim.fnsem_ext_open.
    etrans; first by apply sandbox_fnsemmap_add_l.
    exact (ISim.fnsem_ext_subseteq _ _ _ EXTT).
  Qed.

  Lemma ISim_sim_funs_extend_ctx
      (ctx : contextuality) (Ks Kt Cs Ct : Mod.t)
      (Ist : iProp Σ) (Ms Mt : Mod.t) :
    ISim.sim_funs open Ks Kt Ist Ms Mt ⊢
    ISim.sim_funs ctx (Ks ★ Cs) (Kt ★ Ct) Ist Ms Mt.
  Proof.
    rewrite /ISim.sim_funs. iIntros "SIM %WF".
    iDestruct ("SIM" $! WF) as "[$ SIM]".
    iIntros (fn) "%IN". iApply ISim_sim_fun_extend_ctx.
    by iApply "SIM".
  Qed.

End ISIM_EXTEND_CTX.
