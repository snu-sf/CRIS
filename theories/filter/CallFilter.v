From CRIS.common Require Import Common.
From CRIS.simulations.msim Require Import
  ISim ISimFacts WSim WSimFacts Tactics TacticsCommon TacticsInit.
From CRIS.simulations.msim Require Import FnsemLookup.
From CRIS.simulations.gsim Require Import
  GSim GSimAdequacy GSimMod GSimTactics GSimAux.
From CRIS.common Require Export ConcRA.
From CRIS.modules Require Export LMod Mod SMod.
From CRIS.proofmode Require Import HNormClasses.
From CRIS.simulations.ctxrefine Require Export CtxRefine CtxRefineFacts ClosedAdequacy MainAdequacy.
From stdpp Require Import base list.

Local Ltac gnorm_itr :=
  match goal with
  | |- context [?A] =>
      match type of A with
      | itree crisE Any.t => pattern A; eapply eq_ind; [|symmetry; hnorm_itr]
      end
  end.

Module CFilter. Section CFilter.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition msk_filter_in (s : gset string) (msk : emask) : emask := λ X e,
    match e with
    | inr1 (inl1 (Call fn _)) => bool_decide (fn ∈ s ∧ msk X e)
    | inr1 (inl1 (Spawn fn _)) => bool_decide (fn ∈ s ∧ msk X e)
    | _ => msk X e
    end.
  
  Definition msk_filter_out (s : gset string) (msk : emask) : emask := λ X e,
    match e with
    | inr1 (inl1 (Call fn _)) => bool_decide (fn ∉ s ∧ msk X e)
    | inr1 (inl1 (Spawn fn _)) => bool_decide (fn ∉ s ∧ msk X e)
    | _ => msk X e
    end.

  (* filters module m with bl, which means function cCall fn ∉ bl are undefined behaviors *)
  Program Definition filter (bl : gset string) (m : Mod.t) : Mod.t := {|
    Mod.scopes := m.(Mod.scopes);
    Mod.fnsems :=
      (λ (x : option _), map_fst (msk_filter_out bl) <$> x) <$> m.(Mod.fnsems);
    Mod.initial_st := m.(Mod.initial_st)
  |}.
  Next Obligation. i; eapply Mod.sorted_scopes. Qed.
  Next Obligation.
    intros ? ? i [msk x]; rewrite lookup_omap ?lookup_fmap /Mod.fnsems => ?.
    destruct m; ss.
    destruct (fnsems !! i) as [[[??]|]|] eqn : ?; ss; clarify; ss.
    eapply (well_scoped_fns i (_, _)); rewrite lookup_omap Heqo //=.
  Qed.
  Next Obligation. intros ? m; destruct m; ss. Qed.
  Next Obligation. intros ? m; destruct m; ss. Qed.

  Global Instance fnsem_lookup_result_filter
      bl (m : Mod.t) fn result
      `{Hlookup : !FnsemLookupResult (Mod.fnsems m) fn result} :
    FnsemLookupResult (Mod.fnsems (CFilter.filter bl m)) fn
      ((λ x : option (emask * fbody),
          map_fst (CFilter.msk_filter_out bl) <$> x) <$> result) | 20.
  Proof.
    constructor. rewrite /CFilter.filter /Mod.fnsems /= lookup_fmap
      fnsem_lookup_result_eq //.
  Qed.

  (* Lemmas *)

  Lemma filter_app m1 m2 msk :
    CFilter.filter msk (m1 ★ m2) = CFilter.filter msk m1 ★ CFilter.filter msk m2.
  Proof using.
    destruct m1, m2. eapply Mod.t_eq; ss.
    eapply map_eq; intros i; rewrite ?lookup_fmap ?lookup_union_with ?lookup_fmap.
    do 2 destruct (_ !! i); ss.
  Qed.

  Lemma filter_empty m : CFilter.filter ∅ m = m.
  Proof.
    apply Mod.t_eq; ss.
    rewrite /filter /Mod.fnsems; destruct m as [? fnsems ?]; clear.
    generalize fnsems; eapply map_ind; ss.
    intros i [[msk ?]|] m; rewrite fmap_insert /=; intros ? ->; ss.
    repeat f_equal.
    extensionalities X e; destruct e as [|[|[|]]]; auto.
    destruct c; ss; case_bool_decide as H2; destruct msk; ss; des; ss; exfalso; apply H2; split; ss.
  Qed.

  Lemma filter_union fns1 fns2 m:
    CFilter.filter (fns1 ∪ fns2) m = CFilter.filter fns1 (CFilter.filter fns2 m).
  Proof.
    destruct m. eapply Mod.t_eq; ss.
    eapply map_eq; intros i; rewrite ?lookup_fmap ?lookup_union_with ?lookup_fmap.
    destruct (_ !! i); ss. destruct o as [[e f]|]; ss. do 3 f_equal.
    extensionalities T evt. rewrite /msk_and /msk_filter_out.
    destruct evt; try done. destruct s; try done.
    destruct c; try done;
      apply bool_decide_ext; rewrite /is_true bool_decide_eq_true; set_solver.
  Qed.

  (* Key theorems *)
  Lemma sim_filter_intro (bl : gset string) (m : Mod.t) :
    ⊢ ISim.t open (filter bl m) m (IstEq m).
  Proof using.
    rewrite /ISim.t. iSplit.
    { rewrite /ISim.init_ist. iIntros (Hwf). iSplit.
      { done. }
      iIntros (STATE) "SRC TGT".
      iApply (state_eq_init_same with "SRC TGT"). }
    rewrite /ISim.sim_funs. iIntros (Hwf). iSplit.
    { iPureIntro. split.
      - ii. rr. destruct x; et.
        exfalso. rewrite lookup_fmap in H. destruct (_ !! _) eqn: mi; ss.
        eapply Hwf in mi. rr in mi. des; subst. ss.
      - rewrite /filter /Mod.fnsems /= dom_fmap. done. }
    iIntros (fn) "%Hfn".

    rewrite /ISim.sim_fun ?lookup_fmap.
    iIntros (STATE).
    iIntros "%WFS %WFT" (fs) "%Hfs".
    destruct (_ !! _) as [[[msk bd]|]|] eqn : Ht; ss.
    hexploit (Mod.well_scoped_fns m fn (msk, bd)).
    { rewrite lookup_omap Ht //. }
    intros [HPUT HGET].
    clear Ht.
    clarify. iExists _. iSplit; first done.
    rewrite /isim_fsem.
    iIntros "!#" (arg) "IST". iApply wsim_isim.
    generalize false at 1 as ps; i. generalize false at 1 as pt; i.
    rewrite /SB.sandbox_body /=. generalize (bd arg) as itr; i. clear arg.
    cCoind CIH g0 __ with itr ps pt. iIntros "IST".

    assert (CASE:= case_itrH itr). des; subst; s.
    - cStep. iSplit; first done. iFrame.
    - cStepsS. cStepsT. cByCoind CIH; try et.
      iFrame "IST WINV".
    - cStepsS; ss.
      case_match; cStepsS; ss.
      cStepsT; case_match; ss; cForceT; iFrame; cStepsT.
      cByCoind CIH; try et. iFrame.
    - cStepS. cForceT; iFrame. cNormT.
      cByCoind CIH; try et. iFrame.
    - cStepT. cForceS; iFrame. cNormS.
      cByCoind CIH; try et. iFrame.
    - destruct c; s; cStepsS; case_match; try case_bool_decide; cStepsS; ss.
      + cStepsT; bsimpl; des; case_match; des; ss.
        cStepsT. cCall "IST" as (ret) "IST"; cStepsS; cStepsT.
        cByCoind CIH; try et. iFrame.
      + cStepsT; bsimpl; des; case_match; des; ss.
        cStepsT. iApply (wsim_spawn).
        iIntros (tid); cStepsS; cStepsT; cByCoind CIH; try et. iFrame.
      + cStepsT; bsimpl; des; case_match; des; ss.
        cStepsT. iApply (wsim_yield); iSplitL "IST"; [eauto|].
        iIntros "IST"; cStepsS; cStepsT; cByCoind CIH; try et. iFrame.
      + cStepsT; bsimpl; des; case_match; des; ss.
        cStepsT. iApply (wsim_gettid); eauto.
        iIntros (?); cStepsS; cStepsT; cByCoind CIH; try et. iFrame.
    - destruct s as [k v|k]; cStepsS; cStepsT;
        case_match; cStepsS; ss; cStepsT.
      { iApply (wsim_sput_eq _ _ (S := list_to_set (Mod.scopes m))).
        { rewrite elem_of_list_to_set. eapply HPUT. eapply H. }
        iFrame "IST". iIntros "IST".
        cNormS; cNormT; cByCoind CIH; try et. iFrame. }
      { iApply (wsim_sget_eq _ _ (S := list_to_set (Mod.scopes m))).
        { rewrite elem_of_list_to_set. eapply HGET. eapply H. }
        iFrame "IST". iIntros (?) "IST".
        cNormS; cNormT; cByCoind CIH; try et. iFrame. }
    - destruct e; cNormS; cNormT.
      { cStepT. cForceS _q. cByCoind CIH; et. iFrame. }
      { case_match; cStepsS; ss. cForceT _q. cByCoind CIH; et. iFrame. }
      { case_match; cStepsS; ss. cStep. cByCoind CIH; et. iFrame. }
  Qed.

  Lemma sim_filter_elim (bl : gset string) (m : Mod.t)
      (SUB : get_fids (dom (m.(Mod.fnsems))) ## bl) :
    ⊢ ISim.t closed m (filter bl m) (IstEq m).
  Proof using.
    rewrite /ISim.t. iSplit.
    { rewrite /ISim.init_ist. iIntros (Hwf). iSplit.
      { done. }
      iIntros (STATE) "SRC TGT".
      iApply (@state_eq_init_same Σ STATE
        (list_to_set (Mod.scopes m)) (Mod.initial_st m) with "SRC TGT"). }
    rewrite /ISim.sim_funs. iIntros (Hwf). iSplit.
    { iPureIntro.
      split.
      - destruct Hwf as [wf_fns _].
        rewrite map_Forall_lookup in wf_fns |- *.
        intros i x Hix. specialize (wf_fns i).
        rewrite /filter /Mod.fnsems /= lookup_fmap Hix /= in wf_fns.
        destruct x as [[msk bd]|]; ss.
        eapply wf_fns. reflexivity.
      - rewrite /filter /Mod.fnsems /= dom_fmap. done. }
    iIntros (fn) "%Hfn".

    rewrite /ISim.sim_fun ?lookup_fmap.
    iIntros (STATE).
    iIntros "%WFS %WFT" (fs) "%Hfs".
    destruct (_ !! _) as [[[msk bd]|]|] eqn : Ht; ss.
    hexploit (Mod.well_scoped_fns m fn (msk, bd)).
    { rewrite lookup_omap Ht //. }
    intros [HPUT HGET].
    clear Ht.
    clarify. iExists _. iSplit; first done.
    rewrite /isim_fsem.
    iIntros "!#" (arg) "IST _".
    generalize false at 1 as ps. generalize false at 1 as pt. i.
    rewrite /SB.sandbox_body /=. generalize (bd arg) as itr. i. clear arg.
    cCoind CIH g0 __ with ps pt itr. iIntros "IST".

    assert (CASE:= case_itrH itr). des; subst; s.
    { cStep. iSplit; first done. iFrame. }
    { cStepS; cStepsT. cByCoind CIH; et. }
    { cNormS. case_match; cStepS; ss.
      cStepsT; case_match; ss; cForceT; iFrame; cNormS; cNormT;
        cByCoind CIH; et.
    }
    { cStepS. cForceT; iFrame. cNormT.
      cByCoind CIH; et.
    }
    { cStepT. cForceS; iFrame. cNormS.
      cByCoind CIH; et.
    }
    { destruct c; s; cStepsS; case_match; try case_bool_decide; cStepsS; ss.
      { cStepsT; bsimpl; des; case_bool_decide; des; ss.
        { cStepsT. iApply isim_call. iSplitL "IST"; first done.
          iIntros (ret) "IST"; cStepsS; cStepsT.
          cByCoind CIH; et.
        }
        { iApply isim_call_none; ss.
          rewrite ?lookup_fmap; destruct (_ !! _) eqn : Heq; ss.
          eapply elem_of_dom_2 in Heq.
          exfalso; eapply (SUB fn0).
          { rewrite elem_of_set_omap; esplits; eauto. }
          set_solver.
        }
      }
      { cStepsT; bsimpl; des; case_bool_decide; des; ss.
        { cStepsT.
          iApply isim_spawn; iIntros (tid). cNormS; cNormT.
          cByCoind CIH; et.
        }
        { iApply isim_spawn_none; ss.
          rewrite ?lookup_fmap; destruct (_ !! _) eqn : Heq; ss.
          eapply elem_of_dom_2 in Heq.
          exfalso; eapply (SUB fn0).
          { rewrite elem_of_set_omap; esplits; eauto. }
          set_solver.
        }
      }
      { cStepsT; bsimpl; des; case_match; des; ss. cStepsT.
        iApply isim_yield; iSplitL "IST"; [done|]; iIntros "IST".
        cNormS; cNormT. cByCoind CIH; et.
      }
      { cStepsT; bsimpl; des; case_match; des; ss. cStepsT.
        iApply isim_gettid; iIntros (tid).
        cNormS; cNormT. cByCoind CIH; et.
      }
    }
    { destruct s as [k v|k]; cStepsS; cStepsT;
        case_match; cStepsS; ss; cStepsT.
      { iApply (isim_sput_eq _ _ _ (S := list_to_set (Mod.scopes m))).
        { rewrite elem_of_list_to_set. eapply HPUT. eapply H. }
        iFrame "IST". iIntros "IST".
        cNormS; cNormT; cByCoind CIH; et. }
      { iApply (isim_sget_eq _ _ _ (S := list_to_set (Mod.scopes m))).
        { rewrite elem_of_list_to_set. eapply HGET. eapply H. }
        iFrame "IST". iIntros (?) "IST".
        cNormS; cNormT; cByCoind CIH; et. }
    }
    { destruct e; cNormS; cNormT.
      { cStepT. cForceS _q. cByCoind CIH; et. }
      { case_match; cStepsS; ss. cForceT _q. cByCoind CIH; et. }
      { case_match; cStepsS; ss. cStep. cByCoind CIH; et. }
    }
  Qed.

  (*** introduction of a module ***)
  Lemma intro_filter fns (m : Mod.t) :
    ⊢ ctx_refines m (filter fns m).
  Proof using _I _S crisG0 Γ Σ α β τ.
    iApply main_adequacy. iApply sim_filter_intro.
  Qed.

  (*** elimination of a module ***)
  Lemma elim_filter (bl : gset string) (m : Mod.t)
      (SUB : get_fids (dom (m.(Mod.fnsems))) ## bl) :
    ⊢ refines (filter bl m) m.
  Proof using _I _S crisG0 Γ Σ α β τ.
    iApply ISim_closed_adequacy. iApply sim_filter_elim. eauto.
  Qed.

  (*** introduction of a module ***)
  Theorem intro_module (bl : gset string) m mc
      (WF: Mod.wf mc)
      (DISJ: (m.(Mod.scopes) ## mc.(Mod.scopes)))
      (EXCL: get_fids (dom (m.(Mod.fnsems))) ## bl)
      (EXCL2: get_fids (dom (mc.(Mod.fnsems))) ⊆ bl)
      (EXCL3: entry ∉ dom (Mod.fnsems mc))
      (* (SUB: ∀ fn, In (Some fn) (m.(Mod.fnsems).*1) → bl fn)
      (FRESH: ∀ fn, In (Some fn) (mc.(Mod.fnsems).*1) → (~ bl fn))
      (FRESHI: ~ In None (mc.(Mod.fnsems)).*1)
       *)
      :
      ⊢ refines (filter bl m) (filter bl m ★ mc).
  Proof using.
    iApply gsim_closed_adequacy.
    iApply (gsim_mod_intro _ _ emp%I).
    2: done.
    intros WFM.
    assert (Hwfadd : Mod.wf (filter bl m ★ mc)).
    { apply Mod.add_wf; eauto.
      { intros [i|] Hi1 Hi2; last set_solver.
        apply (EXCL i).
        { apply elem_of_set_omap; exists (funid i); split; ss.
          rewrite /filter /= dom_fmap // in Hi1.
        }
        apply EXCL2.
        apply elem_of_set_omap; eexists; split; done.
      }
      inv WF; inv WFM; eapply NoDup_app; splits; eauto.
    }
    split; et.

    (* Simulation proof *)
    intros rt rs VALID_rs SPLIT.

    assert (Hr_own : Own rs ⊢ Own rt).
    { iIntros "H". iDestruct (SPLIT with "H") as "[$ _]". }
    clear SPLIT.
    assert (Hr : rt ≼ rs).
    { eapply Own_general_soundness in Hr_own; et.
      rewrite own.Own_eq in Hr_own. unfold own.Own_def in Hr_own.
      rewrite upred.uPred_ownM_unseal in Hr_own. unfold upred.uPred_ownM_def in Hr_own.
      apply Hr_own.
    }
    clear Hr_own.

    cut (∀ ps pt arg,
         gsim eq ps pt (LMod.compile (Mod.to_lmod (filter bl m ★ mc) rs) arg)
           (LMod.compile (Mod.to_lmod (filter bl m) rt) arg)); et.

    i. ginit. rewrite /LMod.compile. s.
    rewrite ?lookup_fmap ?lookup_omap ?lookup_union_with ?lookup_fmap.
    destruct (_ mc !! entry) eqn : Hmc; [eapply elem_of_dom_2 in Hmc; set_solver|ss; clear Hmc].
    destruct (_ m !! entry) as [[[msk bd]|]|] eqn : Hm; ss; [|gstep_s; ss|gstep_s; ss].

    rewrite /LModTr.trans /LModTr.interp_callE /ModTr.trans_fnsem /SB.sandbox_body /ITree.map. ired.
    guclo bindC_spec. econs; cycle 1.
    { instantiate (1:=λ r_s r_t, r_s.2 = r_t.2). ii; gstep; ss. subst; econs; econs; ss. }
    rewrite -(sandbox_sandbox (bd arg) _ (msk_filter_out bl (msk_scp (Mod.scopes m) msk_true))); cycle 1.
    { intros X e ?; destruct e as [e|[e|[e|e]]]; ss; destruct e; ss; repeat case_bool_decide; ss.
      { exfalso; naive_solver. }
      { exfalso; naive_solver. }
      { hexploit (Mod.well_scoped_fns m); rewrite map_Forall_lookup => /(_ entry (msk, bd)).
        rewrite lookup_omap Hm /= =>/(_ eq_refl); intros [Hput ?]; naive_solver.
      }
      { hexploit (Mod.well_scoped_fns m); rewrite map_Forall_lookup => /(_ entry (msk, bd)).
        rewrite lookup_omap Hm /= =>/(_ eq_refl); intros [? Hget]; naive_solver.
      }
    }
    
    match goal with
      [|-context [ModTr.trans ?t]] => remember [ModTr.trans t] as ths
    end.
    (* destruct p as [[[img msk] sc] bd]. *)
    assert (WFTHS:
      ∀ tid t (IN: ths !! tid = Some t),
      ∃ ht, t = ModTr.trans (SB.sandbox (msk_filter_out bl (msk_scp (Mod.scopes m) msk_true)) ht)).
    { i. subst. destruct tid; ss. inv IN. esplits; eauto. }
    clear Heqths.
    generalize 0 as cid.
    (* rename rs into rs0.
    generalize rs0 at 2 4 as rs. *)
    assert (SCP := m.(Mod.well_scoped_init)). revert SCP.
    assert (Hsts : map_Forall (const is_Some) (Mod.initial_st m)).
    { apply Mod.nodup_init; inv WFM; auto. }
    revert Hsts.
    assert (SCPc := mc.(Mod.well_scoped_init)). revert SCPc.
    set (st := Mod.initial_st m).
    assert (Hsts : map_Forall (const is_Some) (union_with uwnd st (Mod.initial_st mc))).
    { subst st. hexploit (Mod.nodup_init (filter bl m ★ mc)); ss. inv Hwfadd; auto. }
    revert Hsts.
    generalize st.
    generalize (Mod.initial_st mc) as stc; clear st.
    (* generalize (eq_refl ths) as Heqths. *)
    (* generalize ths at 1 3 as ths0. *)
    generalize dependent ths.
    clear dependent arg bd msk.
    revert_until Hwfadd.
    gcofix CIH. i.
    (* ziter_l. ziter_r. *)
    destruct (ths !! cid) eqn: EQ; cycle 1.
    { giter_s. rewrite /= EQ /triggerUB. gstep_s. gstep_s. ss. }
    assert (WFLEN := lookup_lt_Some _ _ _ EQ).

    eapply WFTHS in EQ as ?. des. subst.
    rewrite /ModTr.trans in EQ.
    ides ht.
    {
      giter_s; giter_t; rewrite /= EQ /=.
      des_ifs; cycle 1.
      { unfold triggerUB. do 2 gstep_s. ss. }
      gstep_s. gcNormS. gstep_t. gcNormT. gstep. econs; econs; eauto.
    }
    {
      revert EQ; gnorm_itr; i.
      eapply gsim_tau_src; eauto.
      eapply gsim_tau_tgt; eauto.
      zprogress.
      gbase. eapply CIH; et.
      i. eapply list_lookup_insert_Some in IN. des; subst; et.
    }

    rewrite ?SBRed.vis in EQ. des_ifs; cycle 1.
    { bsimpl; des. revert EQ; gnorm_itr; intros EQ. eapply gsim_Take_src; [eapply EQ|ss]. }
    destruct e; [destruct a | destruct s;
                              [destruct c|destruct s; [destruct p|destruct c]]];
    rewrite vis_trigger in EQ.
    { (* Assume *)
      eapply gsim_Assume_src; [apply EQ|]. intros rs2 [Vrs2 Hrs2].
      eapply gsim_Assume_tgt; [apply EQ|]. exists rs2; splits; try by des.
      { iIntros "H". iDestruct (Hrs2 with "H") as "> [$ H]". iModIntro.
        iApply Own_extends; et.
      }
      zprogress. gbase.
      unfold Mod.to_lmod, LMod.prog. s.
      eapply CIH; try by des.
      i. eapply list_lookup_insert_Some in IN. des; subst; et.
    }
    { (* AssumeRes *)
      eapply gsim_AssumeRes_src; [apply EQ|]. intros rs2.
      eapply gsim_AssumeRes_tgt; [apply EQ|]. splits; try by des.
      { eapply cmra_valid_included.
        - eapply rs2.
        - eapply cmra_mono_l. et.
      }
      zprogress. gbase.
      unfold Mod.to_lmod, LMod.prog. s.
      eapply CIH; try by des.
      { eapply cmra_mono_l. et. }
      i. eapply list_lookup_insert_Some in IN. des; subst; et.
    }
    { (* Guarantee *)
      eapply gsim_Guarantee_tgt; [apply EQ|]. intros rs2 [Vrs2 Hrs2].
      eapply gsim_Guarantee_src; [apply EQ|]. exists rs2; splits; try by des.
      { iIntros "H". iPoseProof (Own_extends with "H") as "H"; et.
        iApply Hrs2. et.
      }
      zprogress. gbase.
      unfold Mod.to_lmod, LMod.prog. s.
      eapply CIH; try by des.
      i. eapply list_lookup_insert_Some in IN. des; subst; et.
    }
    { (* Call *)
      bsimpl. simpl in Heq. case_bool_decide as Hfn; ss.
      eapply gsim_Call_src; [apply EQ|].
      eapply gsim_Call_tgt; [apply EQ|].
      rewrite {2 4}/LMod.prog !Mod.to_lmod_fnsems lookup_fnsems_None_r //; cycle 1.
      { rewrite -not_elem_of_dom; intros ?; apply Hfn, EXCL2.
        rewrite elem_of_set_omap; exists (funid fn); split; ss; auto.
      }
      rewrite /unwrapU; destruct (_ !! funid fn) as [[[cmsk cbd]|]|] eqn : Hfn'; cycle 1.
      { ired. giter_s. rewrite /= list_lookup_insert //=. gstep_s; ss. }
      { ired. giter_s. rewrite /= list_lookup_insert //=. gstep_s; ss. }
      ired.
      rewrite /ModTr.trans_fnsem /ModTr.trans /SB.sandbox_body -!interpV_bind /=.
      simpl; rewrite !lookup_fmap in Hfn'.
      destruct (_ !! funid fn) as [[[cmsk2 bd2]|]|] eqn : Hfn2; ss; clarify.

      zprogress. gbase. eapply CIH; et.
      i. eapply list_lookup_insert_Some in IN. des; subst; et.
      rewrite /ModTr.trans; esplits.
      f_equal; erewrite SBRed.bind, sandbox_sandbox.
      { f_equal. extensionalities a. rewrite -SBRed.tau //. }
      { intros X e ?; destruct e as [e|[e|[e|e]]]; ss; destruct e; ss; repeat case_bool_decide; ss.
        { exfalso; naive_solver. }
        { exfalso; naive_solver. }
        { hexploit (Mod.well_scoped_fns m); rewrite map_Forall_lookup => /(_ (funid fn) (cmsk2, cbd)).
          rewrite lookup_omap Hfn2 /= =>/(_ eq_refl); intros [Hput ?]; naive_solver.
        }
        { hexploit (Mod.well_scoped_fns m); rewrite map_Forall_lookup => /(_ (funid fn) (cmsk2, cbd)).
          rewrite lookup_omap Hfn2 /= =>/(_ eq_refl); intros [? Hget]; naive_solver.
        }
      }
    }
    { (* Spawn *)
      bsimpl. simpl in Heq. case_bool_decide as Hfn; ss.
      eapply gsim_Spawn_src; [apply EQ|].
      eapply gsim_Spawn_tgt; [apply EQ|].
      rewrite {1 3}/LMod.prog !Mod.to_lmod_fnsems lookup_fnsems_None_r //; cycle 1.
      { rewrite -not_elem_of_dom; intros ?; apply Hfn, EXCL2.
        rewrite elem_of_set_omap; eexists (funid _); split; ss; auto.
      }
      rewrite /unwrapU; destruct (_ !! funid fn) as [[[cmsk cbd]|]|] eqn : Hfn'; cycle 1.
      { ired. gstep_s; ss. }
      { ired. gstep_s; ss. }
      ired.
      rewrite /ModTr.trans_fnsem /ModTr.trans /SB.sandbox_body /=.
      simpl; rewrite !lookup_fmap in Hfn'.
      destruct (_ !! funid fn) as [[[cmsk2 bd2]|]|] eqn : Hfn2; ss; clarify.

      zprogress. gbase. eapply CIH; et.
      i. eapply lookup_snoc_Some in IN. des.
      { eapply list_lookup_insert_Some in IN0. des; subst; et. }
      rewrite /ModTr.trans; esplits; subst.
      f_equal; erewrite <-sandbox_sandbox; try refl.
      { intros X e ?; destruct e as [e|[e|[e|e]]]; ss; destruct e; ss; repeat case_bool_decide; ss.
        { exfalso; naive_solver. }
        { exfalso; naive_solver. }
        { hexploit (Mod.well_scoped_fns m); rewrite map_Forall_lookup => /(_ (funid fn) (cmsk2, cbd)).
          rewrite lookup_omap Hfn2 /= =>/(_ eq_refl); intros [Hput ?]; naive_solver.
        }
        { hexploit (Mod.well_scoped_fns m); rewrite map_Forall_lookup => /(_ (funid fn) (cmsk2, cbd)).
          rewrite lookup_omap Hfn2 /= =>/(_ eq_refl); intros [? Hget]; naive_solver.
        }
      }
    }
    { (* Yield *)
      eapply gsim_Yield_src; [apply EQ|].
      eapply gsim_Yield_tgt; [apply EQ|].
      zprogress.
      gbase. eapply CIH; et.
      i. eapply list_lookup_insert_Some in IN. des; subst; et.
    }
    { (* GetTid *)
      eapply gsim_GetTid_src; [apply EQ|].
      eapply gsim_GetTid_tgt; [apply EQ|].
      zprogress.
      gbase. eapply CIH; et.
      i. eapply list_lookup_insert_Some in IN. des; subst; et.
    }
    { (* Put *)
      destruct k0 as [scp0 key0]; ss; case_bool_decide; ss.
      assert ((scp0 ↯ key0) ∉ (dom stc)).
      { intros Hscp0; eapply (DISJ scp0); auto.
        rewrite elem_of_subseteq in SCPc; specialize (SCPc scp0);
          rewrite elem_of_list_to_set in SCPc; eapply SCPc.
        rewrite elem_of_map. exists (scp0 ↯ key0). eauto.
      }
      eapply gsim_SPut_src; [apply EQ|auto|].
      rewrite insert_union_with_l; [|rewrite -not_elem_of_dom //].
      eapply gsim_SPut_tgt; [apply EQ|auto|].
      zprogress.
      gbase. eapply CIH; et.
      { i. eapply list_lookup_insert_Some in IN. des; subst; et. }
      { eapply map_Forall_union_with; cycle 1.
        { split.
          { eapply map_Forall_insert_2; ss. }
          { eapply map_Forall_union_with_inv in Hsts as ?; des; eauto. }
        }
        eapply map_Forall_union_with_inv_gen in Hsts as ?.
        set_solver.
      }
      { eapply map_Forall_insert_2; ss. }
      { set_solver. }
    }
    { (* Get *)
      destruct k0 as [scp0 key0]. ss; case_bool_decide; ss.
      assert ((scp0 ↯ key0) ∉ (dom stc)).
      { intros Hscp0; eapply (DISJ scp0); auto.
        rewrite elem_of_subseteq in SCPc; specialize (SCPc scp0);
          rewrite elem_of_list_to_set in SCPc; eapply SCPc.
        rewrite elem_of_map. exists (scp0 ↯ key0). eauto.
      }
      eapply gsim_SGet_src; [apply EQ|auto|]; s.
      eapply gsim_SGet_tgt; [apply EQ|auto|]; s.
      rewrite lookup_union_with (not_elem_of_dom_1 stc); eauto.
      zprogress. gbase.
      destruct (st !! _); ss; eapply CIH; et.
      { i. eapply list_lookup_insert_Some in IN. des; subst; et. }
      { i. eapply list_lookup_insert_Some in IN. des; subst; et. }
    }
    { (* Choose *)
      eapply gsim_Choose_tgt; [apply EQ|]; intros x.
      eapply gsim_Choose_src; [apply EQ|]; exists x.
      zprogress.
      gbase. eapply CIH; et.
      i. eapply list_lookup_insert_Some in IN. des; subst; et.
    }
    { (* Take *)
      eapply gsim_Take_src; [apply EQ|]; intros x.
      eapply gsim_Take_tgt; [apply EQ|]; exists x.
      zprogress.
      gbase. eapply CIH; et.
      i. eapply list_lookup_insert_Some in IN. des; subst; et.
    }
    { (* IO *)
      eapply gsim_IO; [apply EQ|apply EQ|]; intros x.
      zprogress.
      gbase. eapply CIH; et.
      i. eapply list_lookup_insert_Some in IN. des; subst; et.
    }
  Unshelve. all: exact smj_top.
  (*SLOW*)Qed.

  Lemma real_mod (md : Mod.t) (msk : gset string) :
    real_mod md → real_mod (CFilter.filter msk md).
  Proof.
    rewrite /real_mod !map_Forall_lookup /CFilter.filter {2}/Mod.fnsems.
    intros Hix i x; rewrite lookup_fmap; specialize (Hix i); destruct lookup as [[[? ?]|]|];
      i; clarify; destruct x; ss; clarify.
    eapply (Hix (Some (e, f))); ss.
  Qed.

  Theorem smod_filter_intro bl sp md:
    ⊢ ctx_refines
      (SMod.to_mod sp md)
      (SMod.to_mod sp (SMod.filter (msk_filter_out bl) md)).
  Proof.
    evar_at_last_1.
    unfold bi_emp_valid.
    etrans; [eapply sim_filter_intro|eapply main_adequacy].
    f_equal. eapply Mod.t_eq; et. destruct md.
    rewrite /filter /SMod.filter /SMod.to_mod /SMod.fnsems /Mod.fnsems //.
    rewrite -!map_fmap_compose. f_equal. extensionality x.
    destruct x as [[msk [fsp fbd]]|]; ss. f_equal. f_equal.
    extensionalities T e. rewrite /msk_filter_out /msk_and.
    destruct e; try rewrite andb_diag; ss.
    destruct s; try rewrite andb_diag; ss.
    destruct c; try rewrite andb_diag; ss.
    - destruct (msk _ _); ss. apply bool_decide_eq_false_2. ii; des; clarify.
    - destruct (msk _ _); ss. apply bool_decide_eq_false_2. ii; des; clarify.
  Qed.

  Lemma filter_masked bl (m: SMod.t) fn msk p fc arg
    (LU: SMod.fnsems (SMod.filter (msk_filter_out bl) m) !! fn = Some (Some (msk, p)))
    (IN: fc ∈ bl)
    :
    msk Any.t (subevent Any.t (Call fc arg)) = false ∧
    msk nat (subevent nat (Spawn fc arg)) = false.
  Proof.
    eapply lookup_fmap_Some in LU. des. destruct x as [[msk0 p0]|]; ss.
    depdes LU. rewrite /msk_and //=; bsimpl; rewrite !bool_decide_eq_false. set_solver.
  Qed.

  Lemma filter_cancellable bl (m: SMod.t)
    (CANCEL: SMod.cancellable m)
    :
    SMod.cancellable (SMod.filter (msk_filter_out bl) m).
  Proof.
    ii. rewrite lookup_fmap_Some in H. des. ss.
    destruct x0 as [[? [? ?]]|]; ss; subst; et.
    eapply CANCEL in H0. unfold img_msk, call_msk, msk_and, msk_filter_out in *.
    des; esplits; i; s.
    - rewrite H0; et.
    - rewrite H2; et.
    - rewrite H3; et.
    - rewrite H4; et.
    - rewrite H5; et.
    - hdes. rewrite !(H6 _ _ y) !(H7 _ _ y). et.
  Qed.
  
End CFilter. End CFilter.

Global Hint Extern 20
  (FnsemLookupResult (Mod.fnsems (CFilter.filter _ _)) _ _) =>
  lazymatch goal with
  | |- FnsemLookupResult (Mod.fnsems (CFilter.filter ?bl ?m)) ?fn _ =>
      let MT := type of (Mod.fnsems m) in
      lazymatch MT with
      | gmap _ ?A =>
          let r := open_constr:(_ : option A) in
          notypeclasses refine
            (@CFilter.fnsem_lookup_result_filter _ bl m fn r _)
      end
  end : fnsem_lookup.

#[global] Hint Extern 0
  (HNormBool (CFilter.msk_filter_out _ _ _ _) _) =>
  simpl;
  let a := fresh in
  case_bool_decide as a;
  [tc_solve|exfalso; set_solver+a]
    : typeclass_instances.

Ltac cfilter_solver :=
  let X := fresh "X" in let e := fresh "e" in
  apply Mod.t_eq; ss;
  rewrite /CFilter.filter /Mod.fnsems /= !fmap_insert /=; repeat f_equal;
  extensionalities X e; destruct e as [|[[]|]]; ss;
  eapply bool_decide_ext; rewrite /is_true bool_decide_eq_true; set_solver.
