From CRIS.common Require Import Common ConcRA StatePredicate.
From CRIS.modules Require Import Mod.
From CRIS.simulations.msim Require Import MSimCommon ISim ISimFacts
  ISimAdequacy.
From CRIS.simulations.ctxrefine Require Import CtxRefine ClosedAdequacy.
From iris.proofmode Require Import proofmode.

(** This file contains the main lemma of CRIS, namely ISim.t implies
    ctx_refines. *)

Section ADEQUACY.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Theorem main_adequacy (Mt Ms : Mod.t) :
    ISim.t open Ms Mt ⊢ ctx_refines Mt Ms.
  Proof.
    iIntros "SIM" (Ctx).
    iApply lsim_closed_adequacy.
    iApply (ISim_adequacy open).
    iApply ISim_ctx. done.
  Qed.

End ADEQUACY.
