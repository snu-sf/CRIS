From CRIS.common Require Import Common ConcRA StatePredicate.
From CRIS.modules Require Import Mod.
From CRIS.simulations.msim Require Import MSimCommon ISim TacticsCommon ITactics.
From iris.proofmode Require Import proofmode.
From stdpp Require Import base list.

Section STATE_EQ.
  Context {Σ : GRA}.

  Definition state_eq (S : gset string) (STATE : stateGS Σ) : iProp Σ :=
    ∃ st_src st_tgt : gmap key (option Any.t),
      ⌜state_slice S st_src = state_slice S st_tgt⌝ ∗
      state_init_src S st_src STATE ∗ state_init_tgt S st_tgt STATE.

  Definition IstEq (M : Mod.t) : stateGS Σ → iProp Σ :=
    state_eq (list_to_set (Mod.scopes M)).

  Lemma state_eq_acc `{STATE : !stateGS Σ} S k (IN : k.1 ∈ S) :
    state_eq S STATE ⊢
      ∃ ov, state_cell_src k ov ∗ state_cell_tgt k ov ∗
        (∀ ov', ⌜state_cell_transition ov ov'⌝ -∗
          state_cell_src k ov' ∗ state_cell_tgt k ov' -∗
          state_eq S STATE).
  Proof.
    rewrite /state_eq /=. iIntros "EQ".
    iDestruct "EQ" as (st_src st_tgt) "(%EQ & SRC & TGT)".
    iPoseProof (state_init_src_acc S st_src k IN with "SRC") as
      (ov_src) "(%Hsrc & SRC & CLOSESRC)".
    iPoseProof (state_init_tgt_acc S st_tgt k IN with "TGT") as
      (ov_tgt) "(%Htgt & TGT & CLOSETGT)".
    assert (Hov : ov_src = ov_tgt).
    { rewrite Hsrc Htgt.
      pose proof (f_equal (fun st => st !! k) EQ) as EQk.
      rewrite (state_slice_lookup_in S st_src k IN)
        (state_slice_lookup_in S st_tgt k IN) in EQk.
      exact EQk. }
    clear Htgt. subst ov_tgt.
    iExists ov_src. iFrame "SRC TGT".
    iIntros (ov') "%TRANS [SRC TGT]".
    iExists (set_state_cell k ov' st_src),
      (set_state_cell k ov' st_tgt).
    iSplit.
    { iPureIntro.
      by apply state_slice_set_state_cell_eq. }
    iSplitL "SRC CLOSESRC".
    - iApply ("CLOSESRC" $! ov' with "[] SRC"). done.
    - iApply ("CLOSETGT" $! ov' with "[] TGT"). done.
  Qed.

  Lemma state_eq_put `{STATE : !stateGS Σ} S k v' (IN : k.1 ∈ S) :
    state_eq S STATE ⊢
      ∃ ov, state_cell_src k ov ∗ state_cell_tgt k ov ∗
        ((k ↦src v' ∗ k ↦tgt v') -∗ state_eq S STATE).
  Proof.
    iIntros "EQ".
    iPoseProof (state_eq_acc S k IN with "EQ") as
      (ov) "(SRC & TGT & CLOSE)".
    iExists ov. iFrame "SRC TGT". iIntros "[SRC TGT]".
    iApply ("CLOSE" $! (Some v') with "[] [SRC TGT]").
    - iPureIntro. right. done.
    - rewrite /state_cell_src /state_cell_tgt /=. iFrame.
  Qed.

  Lemma state_eq_get `{STATE : !stateGS Σ} S k (IN : k.1 ∈ S) :
    state_eq S STATE ⊢
      ∃ ov, state_cell_src k ov ∗ state_cell_tgt k ov ∗
        ((state_cell_src k ov ∗ state_cell_tgt k ov) -∗
          state_eq S STATE).
  Proof.
    iIntros "EQ".
    iPoseProof (state_eq_acc S k IN with "EQ") as
      (ov) "(SRC & TGT & CLOSE)".
    iExists ov. iFrame "SRC TGT". iIntros "ST".
    iApply ("CLOSE" $! ov with "[] ST").
    iPureIntro. left. done.
  Qed.

  Lemma state_eq_init `{STATE : !stateGS Σ} S st_src st_tgt
      (EQ : state_slice S st_src = state_slice S st_tgt) :
    state_init_src S st_src STATE -∗
    state_init_tgt S st_tgt STATE -∗
    state_eq S STATE.
  Proof.
    iIntros "SRC TGT". iExists st_src, st_tgt. iFrame. done.
  Qed.

  Lemma state_eq_init_same `{STATE : !stateGS Σ} S st :
    state_init_src S st STATE -∗
    state_init_tgt S st STATE -∗
    state_eq S STATE.
  Proof.
    iApply state_eq_init. done.
  Qed.
End STATE_EQ.

Section ISIM_REFL.
  Context `{!crisG Γ Σ α β τ _S _I}.
  Context `{STATE : !stateGS Σ}.

  (* Reflexivity of the isim relation *)
  Lemma isim_refl g ctx (Ist : iProp Σ) fl_src fl_tgt msk ps pt {R}
      (it : itree crisE R) :
    (∀ k v', msk _ (subevent _ (SPut k v')) = true →
      Ist ⊢ ∃ ov, state_cell_src k ov ∗ state_cell_tgt k ov ∗
        ((k ↦src v' ∗ k ↦tgt v') -∗ Ist)) →
    (∀ k, msk _ (subevent _ (SGet k)) = true →
      Ist ⊢ ∃ ov, state_cell_src k ov ∗ state_cell_tgt k ov ∗
        ((state_cell_src k ov ∗ state_cell_tgt k ov) -∗ Ist)) →
    Ist ⊢
    isim ctx fl_src fl_tgt Ist g (ist_with_eq Ist) ps pt
      (SB.sandbox msk it) (SB.sandbox msk it).
  Proof using.
    intros Hset Hget.
    revert it. combine_quant ps. combine_quant pt.
    eapply isim_coind. intros g0 _ CIH [pt [ps it]].
    destruct_quant CIH. iIntros "IST /=".
    assert (CASE := case_itrH it); des; subst.
    - istep. iFrame. done.
    - istep_s. istep_t. iby_coind CIH; eauto.
    - cNormT; cNormS. des_if.
      { istep_s. iforce_t; iFrame "ASM". cNormT. iby_coind CIH. eauto. }
      { istep_s; ss. }
    - cNormT; cNormS.
      istep_s. iforce_t; iFrame "ASM". cNormT. iby_coind CIH. eauto.
    - cNormT; cNormS.
      istep_t. iforce_s; iFrame. cNormS. iby_coind CIH. eauto.
    - depdes c.
      { cNormT; cNormS. des_if.
        { icall "IST" as (?) "IST"; et. iby_coind CIH; eauto. }
        { isteps_s; ss. }
      }
      { cNormT; cNormS. des_if.
        { istep. iby_coind CIH; done. }
        { isteps_s. ss. }
      }
      { cNormS; cNormT. des_if.
        { iyield "IST" "IST". iby_coind CIH. eauto. }
        { isteps_s. ss. }
      }
      { cNormS; cNormT. des_if.
        { istep. iby_coind CIH. eauto. }
        { isteps_s. ss. }
      }
    - depdes s.
      { cNormT; cNormS.
        rewrite ?resum_to_subevent ?subevent_subevent.
        specialize (Hset k v); destruct (msk _ _) eqn:Hmsk;
          [cNormS; cNormT|istep_s; ss].
        iPoseProof (Hset eq_refl with "IST") as
          (ov) "(SRC & TGT & CLOSE)".
        destruct ov as [v0|].
        - iEval (rewrite /state_cell_src /state_cell_tgt /=) in "SRC TGT".
          iApply isim_sput_src. iFrame "SRC". iIntros "SRC".
          iApply isim_sput_tgt. iFrame "TGT". iIntros "TGT".
          iby_coind CIH. iApply ("CLOSE" with "[$SRC $TGT]").
        - iEval (rewrite /state_cell_src /state_cell_tgt /=) in "SRC TGT".
          iApply isim_sput_src_uninit. iFrame "SRC". iIntros "SRC".
          iApply isim_sput_tgt_uninit. iFrame "TGT". iIntros "TGT".
          iby_coind CIH. iApply ("CLOSE" with "[$SRC $TGT]").
      }
      { cNormT; cNormS.
        rewrite ?resum_to_subevent ?subevent_subevent.
        specialize (Hget k); destruct (msk _ _) eqn:Hmsk;
          [cNormS; cNormT|istep_s; ss].
        iPoseProof (Hget eq_refl with "IST") as
          (ov) "(SRC & TGT & CLOSE)".
        destruct ov as [v|].
        - iEval (rewrite /state_cell_src /state_cell_tgt /=) in "SRC TGT".
          iApply isim_sget_src. iFrame "SRC". iIntros "SRC".
          iApply isim_sget_tgt. iFrame "TGT". iIntros "TGT".
          iby_coind CIH.
          iApply ("CLOSE" with "[$SRC $TGT]").
        - iEval (rewrite /state_cell_src /state_cell_tgt /=) in "SRC TGT".
          iApply isim_sget_src_uninit. iFrame "SRC". iIntros "SRC".
          iApply isim_sget_tgt_uninit. iFrame "TGT". iIntros "TGT".
          iby_coind CIH.
          iApply ("CLOSE" with "[$SRC $TGT]").
      }
    - destruct e.
      + cNormT; cNormS.
        istep_t. iforce_s. cNormS; cNormT; iby_coind CIH; eauto.
      + cNormT; cNormS. des_if; [cNormS; cNormT|istep_s; ss].
        istep_s. iforce_t. cNormS; cNormT; iby_coind CIH; eauto.
      + cNormT; cNormS. des_if; [cNormS; cNormT|istep_s; ss].
        istep. cNormS; cNormT; iby_coind CIH; eauto.
  Qed.

  Lemma isim_reflL
      (ctx : contextuality) (fl_src fl_tgt : gmap fname (option fbody))
      (msk : emask) (EqL Ist : iProp Σ) itr :
    (∀ k v', msk _ (subevent _ (SPut k v')) = true →
      EqL ⊢ ∃ ov, state_cell_src k ov ∗ state_cell_tgt k ov ∗
        ((k ↦src v' ∗ k ↦tgt v') -∗ EqL)) →
    (∀ k, msk _ (subevent _ (SGet k)) = true →
      EqL ⊢ ∃ ov, state_cell_src k ov ∗ state_cell_tgt k ov ∗
        ((state_cell_src k ov ∗ state_cell_tgt k ov) -∗ EqL)) →
    ⊢ isim_fsem fl_src fl_tgt (EqL ∗ Ist)%I ctx
        (SB.sandbox_body (msk, itr)) (SB.sandbox_body (msk, itr)).
  Proof using.
    intros Hset Hget. rewrite /isim_fsem.
    iIntros "!#" (arg) "[E I] _".
    rewrite /SB.sandbox_body /=. iApply isim_refl.
    - intros k v' Hmsk. iIntros "[E I]".
      iPoseProof (Hset k v' Hmsk with "E") as
        (ov) "(SRC & TGT & CLOSE)".
      iExists ov. iFrame "SRC TGT". iIntros "[SRC TGT]".
      iSplitR "I"; last done. iApply ("CLOSE" with "[$SRC $TGT]").
    - intros k Hmsk. iIntros "[E I]".
      iPoseProof (Hget k Hmsk with "E") as
        (ov) "(SRC & TGT & CLOSE)".
      iExists ov. iFrame "SRC TGT". iIntros "[SRC TGT]".
      iSplitR "I"; last done. iApply ("CLOSE" with "[$SRC $TGT]").
    - iFrame.
  Qed.

  Lemma isim_reflR
      (ctx : contextuality) (fl_src fl_tgt : gmap fname (option fbody))
      (msk : emask) (Ist EqR : iProp Σ) itr :
    (∀ k v', msk _ (subevent _ (SPut k v')) = true →
      EqR ⊢ ∃ ov, state_cell_src k ov ∗ state_cell_tgt k ov ∗
        ((k ↦src v' ∗ k ↦tgt v') -∗ EqR)) →
    (∀ k, msk _ (subevent _ (SGet k)) = true →
      EqR ⊢ ∃ ov, state_cell_src k ov ∗ state_cell_tgt k ov ∗
        ((state_cell_src k ov ∗ state_cell_tgt k ov) -∗ EqR)) →
    ⊢ isim_fsem fl_src fl_tgt (Ist ∗ EqR)%I ctx
        (SB.sandbox_body (msk, itr)) (SB.sandbox_body (msk, itr)).
  Proof using.
    intros Hset Hget. rewrite /isim_fsem.
    iIntros "!#" (arg) "[I E] _".
    rewrite /SB.sandbox_body /=. iApply isim_refl.
    - intros k v' Hmsk. iIntros "[I E]".
      iPoseProof (Hset k v' Hmsk with "E") as
        (ov) "(SRC & TGT & CLOSE)".
      iExists ov. iFrame "SRC TGT". iIntros "[SRC TGT]".
      iSplitL "I"; first done. iApply ("CLOSE" with "[$SRC $TGT]").
    - intros k Hmsk. iIntros "[I E]".
      iPoseProof (Hget k Hmsk with "E") as
        (ov) "(SRC & TGT & CLOSE)".
      iExists ov. iFrame "SRC TGT". iIntros "[SRC TGT]".
      iSplitL "I"; first done. iApply ("CLOSE" with "[$SRC $TGT]").
    - iFrame.
  Qed.

End ISIM_REFL.

Section ISIM_MODULE_REFL.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Lemma ISim_init_ist_refl (M : Mod.t) :
    ⊢ ISim.init_ist M M (IstEq M).
  Proof.
    rewrite /ISim.init_ist. iIntros (WF). iSplit.
    { done. }
    iIntros (STATE) "SRC TGT".
    iApply (@state_eq_init_same Σ STATE (list_to_set (Mod.scopes M))
      (Mod.initial_st M) with "SRC TGT").
  Qed.

  Lemma ISim_sim_funs_refl (ctx : contextuality) (M : Mod.t) :
    ⊢ ISim.sim_funs ctx M M (IstEq M) M M.
  Proof.
    rewrite /ISim.sim_funs. iIntros (WF). iSplit.
    { iPureIntro. split.
      - apply WF.
      - done. }
    iIntros (fn) "%Hfn". rewrite /ISim.sim_fun.
    iIntros (STATE).
    iIntros "%WFS %WFT" (fs) "%Hfs".
    rewrite lookup_fmap in Hfs.
    destruct (Mod.fnsems M !! fn) as [[[fmsk fbdy]|]|] eqn:Hc; ss.
    hexploit (Mod.well_scoped_fns M fn (fmsk, fbdy)).
    { rewrite lookup_omap Hc //. }
    intros [HPUT HGET].
    clarify. iExists (SB.sandbox_body (fmsk, fbdy)).
    iSplit; first by rewrite /sandbox_fnsemmap lookup_fmap Hc.
    rewrite /isim_fsem. iIntros "!#" (arg) "IST _".
    rewrite /SB.sandbox_body /=. iApply (@isim_refl Σ STATE).
    - intros k v Hmsk. iApply (@state_eq_put Σ STATE).
      rewrite elem_of_list_to_set. eapply HPUT. exact Hmsk.
    - intros k Hmsk. iApply (@state_eq_get Σ STATE).
      rewrite elem_of_list_to_set. eapply HGET. exact Hmsk.
    - iFrame.
  Qed.

  Lemma ISim_refl (ctx : contextuality) (M : Mod.t) :
    ⊢ ISim.t ctx M M (IstEq M).
  Proof.
    rewrite /ISim.t. iSplit.
    - iApply ISim_init_ist_refl.
    - iApply ISim_sim_funs_refl.
  Qed.

End ISIM_MODULE_REFL.

Section STATE_EQ_RULES.

  Context `{!crisG Γ Σ α β τ _S _I}.
  Context `{STATE : !stateGS Σ}.

  #[local] Set Implicit Arguments.

  Lemma isim_sput_eq ctx fl_s fl_t S g {Rs Rt} RR ps pt k v' k_s k_t
      (IN : k.1 ∈ S) :
    state_eq S STATE ∗
      (state_eq S STATE -∗
        @isim Σ _ ctx fl_s fl_t (state_eq S STATE) g Rs Rt RR
          true true (k_s tt) (k_t tt)) ⊢
    @isim Σ _ ctx fl_s fl_t (state_eq S STATE) g Rs Rt RR ps pt
      (trigger (SPut k v') >>= k_s) (trigger (SPut k v') >>= k_t).
  Proof.
    iIntros "[EQ SIM]".
    iPoseProof (state_eq_put S k v' IN with "EQ") as
      (ov) "(SRC & TGT & CLOSE)".
    destruct ov as [v|].
    - iEval (rewrite /state_cell_src /state_cell_tgt /=) in "SRC TGT".
      iApply isim_sput_src. iFrame "SRC". iIntros "SRC".
      iApply isim_sput_tgt. iFrame "TGT". iIntros "TGT".
      iApply "SIM". iApply ("CLOSE" with "[$SRC $TGT]").
    - iEval (rewrite /state_cell_src /state_cell_tgt /=) in "SRC TGT".
      iApply isim_sput_src_uninit. iFrame "SRC". iIntros "SRC".
      iApply isim_sput_tgt_uninit. iFrame "TGT". iIntros "TGT".
      iApply "SIM". iApply ("CLOSE" with "[$SRC $TGT]").
  Qed.

  Lemma isim_sget_eq ctx fl_s fl_t S g {Rs Rt} RR ps pt k k_s k_t
      (IN : k.1 ∈ S) :
    state_eq S STATE ∗
      (∀ v, state_eq S STATE -∗
        @isim Σ _ ctx fl_s fl_t (state_eq S STATE) g Rs Rt RR
          true true (k_s v) (k_t v)) ⊢
    @isim Σ _ ctx fl_s fl_t (state_eq S STATE) g Rs Rt RR ps pt
      (trigger (SGet k) >>= k_s) (trigger (SGet k) >>= k_t).
  Proof.
    iIntros "[EQ SIM]".
    iPoseProof (state_eq_get S k IN with "EQ") as
      (ov) "(SRC & TGT & CLOSE)".
    destruct ov as [v|].
    - iEval (rewrite /state_cell_src /state_cell_tgt /=) in "SRC TGT".
      iApply isim_sget_src. iFrame "SRC". iIntros "SRC".
      iApply isim_sget_tgt. iFrame "TGT". iIntros "TGT".
      iApply ("SIM" $! v). iApply ("CLOSE" with "[$SRC $TGT]").
    - iEval (rewrite /state_cell_src /state_cell_tgt /=) in "SRC TGT".
      iApply isim_sget_src_uninit. iFrame "SRC". iIntros "SRC".
      iApply isim_sget_tgt_uninit. iFrame "TGT". iIntros "TGT".
      iApply ("SIM" $! (tt↑)). iApply ("CLOSE" with "[$SRC $TGT]").
  Qed.

End STATE_EQ_RULES.
