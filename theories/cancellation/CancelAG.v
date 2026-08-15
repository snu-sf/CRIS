From CRIS.modules Require Import LMod LModTr.
From CRIS.simulations.gsim Require Import GSim GSimTactics GSimAux.
From CRIS.cancellation Require Import ElimRel.

Lemma cancel_ag `{_crisG: !crisG Γ Σ α β τ _S _I} md sp  R (e : agE R) :
  CANCEL_GOAL md sp (trigger e) (trigger e).
Proof.
  r; i. destruct e.
  { eapply gsim_Assume_src; eauto. intros res2 [? Hres2].
    eapply Own_bupd_split in Hres2 as
      [res21 [res22 [Hres2 [Hres21 [Hres22 Hres_valid]]]]];
      eauto.
    eapply gsim_Assume_tgt; try apply x1.
    exists (r_t ⋅ res21); splits; try by des.
    { eapply (Own_wand_valid res2); auto; rewrite Own_op Hres2 Hres22 RS.
      by iIntros "> [$ > [? [$ ?]]]".
    }
    { rewrite Own_op comm Hres21; apply bupd_intro. }
    eapply KEY; eauto.
    { rewrite list_insert_id //=.
      rewrite Hres2 Hres22 RS Own_op.
      iIntros "> [$ > [$ [$ [$ $]]]] //".
    }
    { econs; eauto; eapply KTR. }
  }
  { eapply gsim_AssumeRes_src; eauto. intros ?.
    eapply gsim_AssumeRes_tgt; try apply x1; split.
    { eapply Own_wand_valid; last eauto; rewrite !Own_op RS; iIntros "[$ > [? [$ ?]]] //". }
    eapply KEY; eauto.
    { rewrite list_insert_id //=.
      rewrite !Own_op RS.
      iIntros "[$ > [$ [$ [$ $]]]] //".
    }
    { econs; eauto; eapply KTR. }
  }
  { eapply gsim_Guarantee_tgt; try apply x1; intros rt2 [? Hrt2].
    eassert (Hrs2 : Own r_s ⊢ |==> P ∗ _).
    { rewrite RS Hrt2; iIntros "> [A [> [P B] C]]"; iCombine "A B C" as "A"; iSplitR "A"; done. }
    eapply Own_bupd_split in Hrs2 as
      [rs1 [rs2 [Hrs [Hrs1 [Hrs2 Hrs_valid]]]]]; auto.
    assert (✓ rs2). { apply (Own_wand_valid r_s); auto; rewrite Hrs; iIntros "> [? $] //". }
    eapply gsim_Guarantee_src; eauto; exists rs2; splits; eauto.
    { rewrite Hrs Hrs1 //. }
    eapply KEY; eauto.
    { rewrite list_insert_id //= Hrs2; apply bupd_intro. }
    { econs; eauto; eapply KTR. }
  }
Qed.
