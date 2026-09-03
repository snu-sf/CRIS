From CRIS.common Require Import Common ConcRA StatePredicate.
From CRIS.modules Require Import Mod.
From CRIS.simulations.msim Require Import MSimCommon ISim.
From iris.proofmode Require Import proofmode.
From stdpp Require Import base list.

Local Lemma mod_add_scope_set `{Σ : GRA} (m1 m2 : Mod.t) :
  (list_to_set (Mod.scopes (m1 ★ m2)) : gset string) =
    list_to_set (Mod.scopes m1) ∪ list_to_set (Mod.scopes m2).
Proof.
  apply set_eq. intros scope.
  rewrite elem_of_list_to_set elem_of_union /=.
  rewrite sorting.merge_sort_Permutation elem_of_app.
  by rewrite !elem_of_list_to_set.
Qed.

Local Lemma mod_add_scope_disjoint `{Σ : GRA} (m1 m2 : Mod.t)
    (WF : Mod.wf (m1 ★ m2)) :
  (list_to_set (Mod.scopes m1) : gset string) ##
    list_to_set (Mod.scopes m2).
Proof.
  intros scope IN1 IN2.
  rewrite !elem_of_list_to_set in IN1, IN2.
  pose proof (Mod.wf_scopes _ WF) as ND.
  rewrite /= sorting.merge_sort_Permutation NoDup_app in ND.
  destruct ND as [_ [DISJ _]]. exact (DISJ scope IN1 IN2).
Qed.

Local Lemma state_slice_union_with_l
    (S1 S2 : gset string) (m1 m2 : gmap key (option Any.t))
    (SCOPED2 : set_map scope (dom m2) ⊆ S2) (DISJ : S1 ## S2) :
  state_slice S1 (union_with uwnd m1 m2) = state_slice S1 m1.
Proof.
  apply map_eq. intros k. rewrite !state_slice_lookup.
  destruct (decide (scope k ∈ S1)) as [IN|NIN]; last done.
  rewrite lookup_union_with.
  destruct (m2 !! k) eqn:LOOK2; last by destruct (m1 !! k).
  exfalso. apply elem_of_dom_2 in LOOK2.
  apply (DISJ (scope k) IN), SCOPED2.
  apply elem_of_map. exists k. done.
Qed.

Local Lemma state_slice_union_with_r
    (S1 S2 : gset string) (m1 m2 : gmap key (option Any.t))
    (SCOPED1 : set_map scope (dom m1) ⊆ S1) (DISJ : S1 ## S2) :
  state_slice S2 (union_with uwnd m1 m2) = state_slice S2 m2.
Proof.
  apply map_eq. intros k. rewrite !state_slice_lookup.
  destruct (decide (scope k ∈ S2)) as [IN|NIN]; last done.
  rewrite lookup_union_with.
  destruct (m1 !! k) eqn:LOOK1; last by destruct (m2 !! k).
  exfalso. apply elem_of_dom_2 in LOOK1.
  apply (DISJ (scope k)).
  - apply SCOPED1, elem_of_map. exists k. done.
  - exact IN.
Qed.

Section HORIZONTAL_COMPOSITION.

  Context `{!crisG Γ Σ α β τ _S _I}.

  Lemma add_init_ist
    (Ms Mt Ns Nt : Mod.t)
    (IstM IstN : stateGS Σ -> iProp Σ)
    : ISim.init_ist Ms Mt IstM
      ∗ ISim.init_ist Ns Nt IstN
      ⊢ ISim.init_ist (Ms ★ Ns) (Mt ★ Nt) (fun STATE => IstM STATE ∗ IstN STATE).
  Proof.
    iIntros "[HM HN]". rewrite /ISim.init_ist.
    iIntros (WF).
    destruct (Mod.add_wf_inv Mt Nt WF) as
      [WFMT [WFNT [FNSDISJ SCOPEND]]].
    iDestruct ("HM" $! WFMT) as "[%SCPM HM]".
    iDestruct ("HN" $! WFNT) as "[%SCPN HN]".
    pose (SMs := (list_to_set (Mod.scopes Ms) : gset string)).
    pose (SMt := (list_to_set (Mod.scopes Mt) : gset string)).
    pose (SNs := (list_to_set (Mod.scopes Ns) : gset string)).
    pose (SNt := (list_to_set (Mod.scopes Nt) : gset string)).
    assert (TGT_DISJ : SMt ## SNt).
    { subst SMt SNt. apply mod_add_scope_disjoint. exact WF. }
    assert (MS_SUB : SMs ⊆ SMt).
    { intros scope IN. rewrite /SMs elem_of_list_to_set in IN.
      rewrite /SMt elem_of_list_to_set.
      eapply elem_of_submseteq; eauto. }
    assert (NS_SUB : SNs ⊆ SNt).
    { intros scope IN. rewrite /SNs elem_of_list_to_set in IN.
      rewrite /SNt elem_of_list_to_set.
      eapply elem_of_submseteq; eauto. }
    assert (SRC_DISJ : SMs ## SNs) by set_solver.
    assert (SLICE_SRC_M :
      state_slice SMs (Mod.initial_st (Ms ★ Ns)) =
        state_slice SMs (Mod.initial_st Ms)).
    { apply state_slice_union_with_l with (S2 := SNs).
      - apply Mod.well_scoped_init.
      - exact SRC_DISJ. }
    assert (SLICE_SRC_N :
      state_slice SNs (Mod.initial_st (Ms ★ Ns)) =
        state_slice SNs (Mod.initial_st Ns)).
    { apply state_slice_union_with_r with (S1 := SMs).
      - apply Mod.well_scoped_init.
      - exact SRC_DISJ. }
    assert (SLICE_TGT_M :
      state_slice SMt (Mod.initial_st (Mt ★ Nt)) =
        state_slice SMt (Mod.initial_st Mt)).
    { apply state_slice_union_with_l with (S2 := SNt).
      - apply Mod.well_scoped_init.
      - exact TGT_DISJ. }
    assert (SLICE_TGT_N :
      state_slice SNt (Mod.initial_st (Mt ★ Nt)) =
        state_slice SNt (Mod.initial_st Nt)).
    { apply state_slice_union_with_r with (S1 := SMt).
      - apply Mod.well_scoped_init.
      - exact TGT_DISJ. }
    iSplit.
    { iPureIntro. simpl. rewrite !sorting.merge_sort_Permutation.
      eapply submseteq_app; eauto. }
    iIntros (STATE) "SRC TGT".
    iEval (rewrite (mod_add_scope_set Ms Ns)) in "SRC".
    iEval (rewrite (mod_add_scope_set Mt Nt)) in "TGT".
    iPoseProof (state_init_src_union SMs SNs
      (Mod.initial_st (Ms ★ Ns)) SRC_DISJ with "SRC") as "[SRCM SRCN]".
    iPoseProof (state_init_tgt_union SMt SNt
      (Mod.initial_st (Mt ★ Nt)) TGT_DISJ with "TGT") as "[TGTM TGTN]".
    iPoseProof (state_init_src_ext SMs (Mod.initial_st (Ms ★ Ns))
      (Mod.initial_st Ms) SLICE_SRC_M with "SRCM") as "SRCM".
    iPoseProof (state_init_src_ext SNs (Mod.initial_st (Ms ★ Ns))
      (Mod.initial_st Ns) SLICE_SRC_N with "SRCN") as "SRCN".
    iPoseProof (state_init_tgt_ext SMt (Mod.initial_st (Mt ★ Nt))
      (Mod.initial_st Mt) SLICE_TGT_M with "TGTM") as "TGTM".
    iPoseProof (state_init_tgt_ext SNt (Mod.initial_st (Mt ★ Nt))
      (Mod.initial_st Nt) SLICE_TGT_N with "TGTN") as "TGTN".
    iSplitL "HM SRCM TGTM".
    - iApply ("HM" $! STATE with "SRCM TGTM").
    - iApply ("HN" $! STATE with "SRCN TGTN").
  Qed.

  Lemma add_sim_funs
    (ctx : contextuality)
    (Ks Kt : Mod.t)
    (Ist : stateGS Σ -> iProp Σ)
    (Ms Mt Ns Nt : Mod.t)
    : ISim.sim_funs ctx Ks Kt Ist Ms Mt
      ∗ ISim.sim_funs ctx Ks Kt Ist Ns Nt
      ⊢ ISim.sim_funs ctx Ks Kt Ist (Ms ★ Ns) (Mt ★ Nt).
  Proof.
    iIntros "[HM HN]". rewrite /ISim.sim_funs.
    iIntros (WF).
    destruct (Mod.add_wf_inv Mt Nt WF) as
      [WFMT [WFNT [TGT_DISJ SCOPEND]]].
    iDestruct ("HM" $! WFMT) as "[%PUREM SIMM]".
    iDestruct ("HN" $! WFNT) as "[%PUREN SIMN]".
    destruct PUREM as [SOMEM SUBM].
    destruct PUREN as [SOMEN SUBN].
    assert (SRC_DISJ : dom (Mod.fnsems Ms) ## dom (Mod.fnsems Ns))
      by set_solver.
    iSplit.
    { iPureIntro.
      split.
      - eapply map_Forall_union_with; eauto.
      - rewrite !Mod.dom_fnsems_add. set_solver.
    }
    iIntros (fn) "%IN".
    rewrite Mod.dom_fnsems_add in IN.
    set_unfold in IN. destruct IN as [IN|IN].
    - iApply ("SIMM" $! fn). done.
    - iApply ("SIMN" $! fn). done.
  Qed.

End HORIZONTAL_COMPOSITION.
