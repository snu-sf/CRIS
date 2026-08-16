From CRIS.common Require Import CRIS.
From CRIS.apc Require Import APCHeader APC APCI APCA.

Module APCIA. Section APCIA.
  Import APCA.
  Context `{!crisG Γ Σ α β τ _S _I}.
  
  Context (SpA SpPure: specmap).

  Definition Ist (_ : stateGS Σ) : iProp Σ := True%I.

  Local Definition APCAMod := (APCA.t SpPure SpA).
  Local Definition APCIMod := (APCI.t).

  Local Transparent _APC.

  Lemma simF_apc :
    ⊢ ISim.sim_fun open APCAMod APCIMod Ist (fid APC.apc).
  Proof using.
    cStartFunSim. rewrite /apc_body.
    
    cStepsS. iDestruct "ASM" as "[-> ->]".
    cStepsT. cStepsS. rewrite /APC. cForceS. cStepsS.
    rewrite unfold_APC. cForceS true. cStepsS.
    cForcesS. iSplitR; first done. cStep. iFrame; eauto.
    Unshelve. all: ss.
  Qed.

  Lemma sim : ⊢ ISim.t open APCAMod APCIMod Ist.
  Proof using.
    cStartModSim.
    - done.
    - iApply simF_apc.
  Qed.
End APCIA.

Section ctxr.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Lemma ctxr (SpA SpPure : specmap) :
    ⊢ ctx_refines
      APCI.t
      (APCA.t SpPure SpA).
  Proof. iApply main_adequacy. iApply sim. Qed.
End ctxr. End APCIA.
