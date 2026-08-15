From CRIS.modules Require Import LMod LModTr.
From CRIS.simulations Require Import GSim GSimTactics GSimAux.
From CRIS.cancellation Require Import ElimRel.

Lemma cancel_core `{!crisG Γ Σ α β τ _S _I} md sp R (e : coreE R) :
  CANCEL_GOAL md sp (trigger e) (trigger e).
Proof.
  r; i. destruct e.
  { eapply gsim_Choose_tgt; try apply x1. intros x.
    eapply gsim_Choose_src; eauto. exists x.
    eapply KEY; et.
    { rewrite list_insert_id //. }
    { econs; eauto; ss. }
  }
  { eapply gsim_Take_src; eauto. intros x.
    eapply gsim_Take_tgt; try apply x1. exists x.
    eapply KEY; et.
    { rewrite list_insert_id //. }
    { econs; eauto; ss. }
  }
  { eapply gsim_IO; eauto; try apply x1. intros ret.
    eapply KEY; et.
    { rewrite list_insert_id //. }
    { econs; eauto; ss. }
  }
(*SLOW*)Qed.
