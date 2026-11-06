From CRIS.common Require Import Common ConcRA StatePredicate.
From CRIS.modules Require Import Mod.
From CRIS.simulations.msim Require Import MSim MSimCommon ISim.
From iris.proofmode Require Import proofmode.

Local Ltac mstep_extend :=
  guclo msimC_spec; econs; econs; eauto; econs; eauto.

Local Lemma msim_extend_ctx
    `{Σ : GRA} `{!stateGS Σ} (contextual : contextuality)
    (Ks Kt Cs Ct : Mod.t) (Ist : iProp Σ) {Rs Rt}
    (RR : retr_type Σ Rs Rt) ps pt
    (itr_src : itree crisE Rs) (itr_tgt : itree crisE Rt) (fmr : Σ) :
  Mod.wf (Ks ★ Cs) →
  Mod.wf (Kt ★ Ct) →
  msim open
    (sandbox_fnsemmap (Mod.fnsems Ks))
    (sandbox_fnsemmap (Mod.fnsems Kt))
    Ist RR ps pt itr_src itr_tgt fmr →
  @msim _ _ contextual
    (sandbox_fnsemmap (Mod.fnsems (Ks ★ Cs)))
    (sandbox_fnsemmap (Mod.fnsems (Kt ★ Ct)))
    Ist Rs Rt RR ps pt itr_src itr_tgt fmr.
Proof.
  ginit.
  intros WFS WFT.
  move WFS at top. move WFT at top.
  revert_until RR. gcofix CIH.
  intros ps pt itr_src itr_tgt fmr SIM.
  move SIM before CIH. revert_until SIM. punfold SIM.
  pattern ps, pt, itr_src, itr_tgt, fmr.
  eapply _msim_tarski, SIM; clear SIM fmr.
  intros ps0 pt0 itr_src0 itr_tgt0 fmr IN.
  guclo msim_wfC_spec. econs. intros VALID.
  guclo msim_nodupC_spec. econs. intros NODUPS NODUPT.
  hexploit IN; ss.
  { move: NODUPS. rewrite ?map_Forall_lookup => H i x.
    move: H => /(_ i x) /=.
    rewrite ?lookup_fmap lookup_union_with.
    destruct (_ Ks !! i) as [[[? ?]|]|];
      destruct (_ Cs !! i); ss; intros; clarify. }
  { move: NODUPT. rewrite ?map_Forall_lookup => H i x.
    move: H => /(_ i x) /=.
    rewrite ?lookup_fmap lookup_union_with.
    destruct (_ Kt !! i) as [[[? ?]|]|];
      destruct (_ Ct !! i); ss; intros; clarify. }
  clear IN. intros IN.
  destruct IN as [fmr1 [STEP UPD]]; eauto.
  inv STEP; try by (mstep_extend; eauto).
  - mstep_extend.
    revert FUN.
    intros [[f2|] [? FUN]]%lookup_fmap_Some; ss; clarify.
    move: FUN => /(Mod.lookup_add_l).
    move /(_ Cs WFS) => /=. rewrite lookup_fmap => -> //=.
  - mstep_extend.
    revert FUN.
    intros [[f2|] [? FUN]]%lookup_fmap_Some; ss; clarify.
    move: FUN => /(Mod.lookup_add_l).
    move /(_ Ct WFT) => /=. rewrite lookup_fmap => -> //=.
  - gstep. econs. econs. econs; eauto. econs; eauto.
    gbase. pclearbot. eapply CIH; eauto.
Qed.

Local Lemma isim_extend_ctx
    `{Σ : GRA} `{!stateGS Σ} (contextual : contextuality)
    (Ks Kt Cs Ct : Mod.t) (Ist : iProp Σ) {Rs Rt}
    (RR : retr_type Σ Rs Rt) ps pt
    (itr_src : itree crisE Rs) (itr_tgt : itree crisE Rt) :
  Mod.wf (Ks ★ Cs) →
  Mod.wf (Kt ★ Ct) →
  isim open
    (sandbox_fnsemmap (Mod.fnsems Ks))
    (sandbox_fnsemmap (Mod.fnsems Kt))
    Ist ibot RR ps pt itr_src itr_tgt ⊢
  @isim _ _ contextual
    (sandbox_fnsemmap (Mod.fnsems (Ks ★ Cs)))
    (sandbox_fnsemmap (Mod.fnsems (Kt ★ Ct)))
    Ist ibot Rs Rt RR ps pt itr_src itr_tgt.
Proof.
  intros WFS WFT.
  apply entails_pointwise => r _ SIM.
  eapply isim_init in SIM; eauto.
  eapply gpaco8_mon in SIM; try apply iunlift_ibot; eauto.
  eapply gpaco8_init in SIM; eauto with paco.
  eapply isim_final, gpaco8_final; eauto with paco. right.
  assert (SIM' :
    @msim _ _ contextual
      (sandbox_fnsemmap (Mod.fnsems (Ks ★ Cs)))
      (sandbox_fnsemmap (Mod.fnsems (Kt ★ Ct))) Ist
      Rs Rt RR ps pt itr_src itr_tgt r).
  { eapply msim_extend_ctx; eauto. }
  eapply paco8_mon_bot.
  - exact SIM'.
  - intros; assumption.
Qed.

Local Lemma isim_fsem_extend_ctx
    `{!crisG Γ Σ α β τ _S _I} `{!stateGS Σ}
    (contextual : contextuality) (Ks Kt Cs Ct : Mod.t)
    (Ist : iProp Σ) fs ft :
  Mod.wf (Ks ★ Cs) →
  Mod.wf (Kt ★ Ct) →
  isim_fsem
    (sandbox_fnsemmap (Mod.fnsems Ks))
    (sandbox_fnsemmap (Mod.fnsems Kt)) Ist open fs ft ⊢
  isim_fsem
    (sandbox_fnsemmap (Mod.fnsems (Ks ★ Cs)))
    (sandbox_fnsemmap (Mod.fnsems (Kt ★ Ct))) Ist contextual fs ft.
Proof.
  intros WFS WFT. rewrite /isim_fsem.
  iIntros "#SIM !#" (arg) "IST WINV".
  iApply (isim_extend_ctx contextual Ks Kt Cs Ct); eauto.
  iApply ("SIM" $! arg with "IST WINV").
Qed.

Section ISIM_EXTEND_CTX.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Section SIM_FUNS.
    Context `{!stateGS Σ}.

    (** Transport open function simulations to larger ambient modules.  [DOM]
        ensures that extension does not introduce a new selected source
        function whose previous [sim_fun] obligation was vacuous. *)
    Lemma ISim_sim_funs_extend_ctx
        (contextual : contextuality) (Ks Kt Cs Ct : Mod.t)
        (Ist : iProp Σ) (Ms Mt : Mod.t)
        (DOM : dom (Mod.fnsems Ms) ⊆ dom (Mod.fnsems Ks)) :
      ISim.sim_funs open Ks Kt Ist Ms Mt ⊢
      ISim.sim_funs contextual (Ks ★ Cs) (Kt ★ Ct) Ist Ms Mt.
    Proof.
      rewrite /ISim.sim_funs. iIntros "SIM %WFMT".
      iDestruct ("SIM" $! WFMT) as "[%PURE SIM]".
      iSplit; first done.
      iIntros (fn) "%IN".
      iPoseProof ("SIM" $! fn with "[]") as "SIM"; first done.
      rewrite /ISim.sim_fun.
      iIntros "%WFS %WFT" (fs) "%LOOK".
      destruct (Mod.add_wf_inv Ks Cs WFS) as [WFKS _].
      destruct (Mod.add_wf_inv Kt Ct WFT) as [WFKT _].
      iEval (rewrite /ISim.sim_fun) in "SIM".
      iSpecialize ("SIM" with "[] []"); [done|done|].
      iSpecialize ("SIM" $! fs with "[]").
      { iPureIntro.
        rewrite /sandbox_fnsemmap !lookup_fmap in LOOK |- *.
        rewrite (lookup_fnsems_l_2 Ks Cs fn WFS (DOM fn IN)) in LOOK.
        exact LOOK. }
      iDestruct "SIM" as (ft) "[%LOOKT FSIM]".
      iExists ft. iSplit.
      { iPureIntro.
        rewrite /sandbox_fnsemmap !lookup_fmap in LOOKT |- *.
        destruct (Mod.fnsems Kt !! fn)
          as [[[msk body]|]|] eqn:HKT; ss; clarify.
        rewrite (Mod.lookup_add_l Kt Ct fn (msk, body) WFT HKT) //=. }
      iApply (isim_fsem_extend_ctx contextual Ks Kt Cs Ct); eauto.
    Qed.

  End SIM_FUNS.

End ISIM_EXTEND_CTX.
