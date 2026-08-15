From CRIS.modules Require Import LMod LModTr.
From CRIS.simulations.gsim Require Import GSim GSimTactics GSimAux.
From CRIS.cancellation Require Import MInline ElimRel.

Local Ltac gnorm_itr :=
  match goal with
  | |- context [?A] =>
      match type of A with
      | itree crisE Any.t => pattern A; eapply eq_ind; [|symmetry; hnorm_itr]
      end
  end.

Lemma cancel_spawn `{!crisG Γ Σ α β τ _S _I} md sp fn args :
  CANCEL_GOAL md sp
    (HoareSpawnE None false fn args) 
    (HoareSpawnE ((SMod.sp_from md).1 !! (funid fn)) true fn args).
Proof.
  r; i. ss. subst.
  revert x1; gnorm_itr; intros x1. revert x0; gnorm_itr; intros x0.
  eapply gsim_Spawn_src; try apply x0.
  rewrite {1}/LMod.prog {1}Mod.to_lmod_fnsems /= !lookup_fmap.
  destruct ((SMod.fnsems md) !! (funid fn)) as [[[msk [fspo bd]]|]|] eqn : Hfn; ss; cycle 1.
  { gstep_s; ss. }
  { gstep_s; ss. }
  ired.
  eapply gsim_tau_src.
  { rewrite lookup_app list_lookup_insert // length_fmap //. }
  rewrite insert_app_l ?length_insert // !list_insert_insert.

  assert (Hfnsp : (SMod.sp_from md).1 !! (funid fn) = fspo).
  { rewrite lookup_omap !lookup_fmap !lookup_omap Hfn //. }
  rewrite Hfnsp /= in x1.
  revert x1; gnorm_itr; intros x1.
  eapply gsim_Choose_tgt; [eapply x1|]. intros varg; s. ghcNormT.
  eapply gsim_tau_tgt; [lookup_tac; do 2 f_equal|]; try lia.
  rewrite !list_insert_insert. ghcNormT.
  eapply gsim_Spawn_tgt; [lookup_tac; do 2 f_equal|]; try lia.
  rewrite !list_insert_insert. ghcNormT.
  rewrite !length_insert.
  rewrite {2}/LMod.prog {1}Mod.to_lmod_fnsems /= !lookup_fmap Hfn /=. ired.

  eapply gsim_tau_tgt.
  { rewrite lookup_app list_lookup_insert //; lia. }
  rewrite insert_app_l ?length_insert //; try lia; rewrite !list_insert_insert.

  rewrite YieldToken_gen in RS.
  hexploit (Own_bupd_split).
  { iIntros "S". iPoseProof (RS with "S") as ">(D & R & TA & [YA NY])".
    iModIntro. iCombine "D TA YA" as "P". iCombine "R NY" as "Q".
    iSplitL "P"; [iApply "P"|iApply "Q"]. }
  { eauto. }
  intros [r_t1 [r_t2 [Hr_t [Hr_t1 [Hr_t2 Hr_t_valid]]]]].
  assert (RES: ✓ r_t2 ∧ (Own r_t2 ⊢ |==> YIELD (length tgts) ∗ Own r_t)).
  { split; eauto.
    { eapply Own_wand_valid; [iIntros "S"; iMod (Hr_t with "S") as "[_ $]"; done|eauto]. }
    { rewrite Hr_t2 EQLEN2 EQLEN. iIntros "[$ $]"; done. }
  }

  eapply gsim_Assume_tgt.
  { rewrite lookup_app list_lookup_insert //; lia. }
  exists r_t2; splits; try by des.
  rewrite insert_app_l ?length_insert //; try lia; rewrite !list_insert_insert.

  eapply gsim_tau_tgt.
  { rewrite lookup_app list_lookup_insert //; lia. }
  rewrite insert_app_l ?length_insert //; try lia; rewrite !list_insert_insert.
  gstep; econs; econs; try exact smj_lt_mid_top.

  eapply gsim_Choose_tgt. { rewrite lookup_app list_lookup_insert //; lia. }
  intros Fsp. ghcNormT.
  eapply gsim_tau_tgt.
  { lookup_tac; et. rewrite length_app length_insert; s. lia. }
  rewrite !list_insert_insert. ghcNormT.

  eapply gsim_Guarantee_tgt.
  { lookup_tac; et. rewrite length_app length_insert; s. lia. }
  intros r_t3 [? Hr_t3].
  rewrite insert_app_l ?length_insert //; try lia; rewrite !list_insert_insert. ghcNormT.

  eapply gsim_tau_tgt.
  { lookup_tac; et. rewrite length_app length_insert; s. lia. }
  rewrite insert_app_l ?length_insert //; try lia; rewrite !list_insert_insert. ghcNormT.

  hexploit Own_bupd_split; try apply Hr_t3; try by des.
  intros [r_t21 [r_t22
    [Hr_t2' [Hr_t21 [Hr_t22 Hr_t2_valid]]]]].
  gbase.
  eapply (CIH); eauto.
  { instantiate (1:=<[cid:=ε]>(rs_diff ++ [r_t21])).
    econs; first (rewrite !length_insert !length_app /= !length_insert; lia).
    rewrite !length_insert !length_app !length_insert /=. split; first lia.
    intros i ???; destruct (decide (i = cid)); subst.
    { rewrite !lookup_app !list_lookup_insert; try (rewrite ?length_app ?length_insert /=; lia).
      do 3 (intros INV; inv INV).
      econs; eauto. rewrite EQLEN. eapply KTR.
    }
    rewrite !list_lookup_insert_ne //.
    destruct (decide (i < length srcs)).
    { rewrite !lookup_app_l ?length_insert; try lia.
      rewrite !list_lookup_insert_ne //.
      ii; eapply REL; eauto.
    }
    destruct (decide (i = length srcs)); cycle 1.
    { rewrite ?lookup_ge_None_2; ss; rewrite ?length_app /= ?length_insert; lia. }
    subst; rewrite !lookup_app_r ?length_insert ?list_lookup_singleton; des_ifs_safe; try lia.
    do 3 (intros INV; inv INV).

    exploit (Mod.well_scoped_fns (SMod.to_mod (SMod.sp_from md) md) (funid fn)); eauto.
    { rewrite lookup_omap lookup_fmap Hfn //. }
    dup WFS; r in WFS; rewrite map_Forall_lookup in WFS; specialize (WFS (funid fn)).
    eapply WFS in Hfn as ?.
    i; ss.
    rewrite /ModTr.trans_fnsem !sandbox_inline_commute /SB.sandbox_body; cycle 1; try by des.
    rewrite /SModTr.trans_fnsem.
    eapply MIRed_HoareFun_cancel with (sp:=SMod.sp_from md) (arg:=varg) in Hfn; try by des.
    rewrite Hfn.
    rewrite SBRed.tau MIRed.tau.
    eapply thread_rel_spawn; eauto; ss; first lia.
    { eexists _, _; split; first apply related.
      rewrite Hr_t21 EQLEN //.
    }
    { ss; eapply elim_rel_cancel; eauto; try by des. }
  }
  rewrite insert_app_l; last lia.
  rewrite Hr_t Hr_t1 Hr_t2' Hr_t22. iIntros "> [[? [$ ?]] ?]".
  rewrite list_insert_id // big_sepL_app /= !right_id.
  rewrite length_app /= Nat.add_comm /=.
  iFrame; auto.
(*SLOW*)Qed.
