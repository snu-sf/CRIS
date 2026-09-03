From CRIS.common Require Import CRIS.
From CRIS.modules Require Import LMod SMod.
From CRIS.simulations.gsim Require Import
  GSim GSimAdequacy GSimTactics GSimAux GSimMod.
From CRIS.filter Require Import CallFilter.
From CRIS.scheduler Require Import SchHeader SchI SchA.
From CRIS.helping Require Export HelpingOn HelpingOff HelpingAux.
From CRIS.helping Require Import HelpingOnOffAux HelpingOnOffResource.

Ltac unfold_trans :=
  rewrite /ModTr.trans_fnsem /SB.sandbox_body
    /ModTr.trans /SModTr.trans_fnsem /SModTr.trans /=.

Section HelpingOnOff.
  Import HelpingOn.
  Context `{!crisG Γ Σ α β τ _S _I, !schGS, !helpingGS}.
  (* sp, module name for the helping module *)
  Context (mn : string) (msk : gset string).
  Context (jobs : SAny.t → itree crisE (SAny.t + SAny.t)).

  Local Notation mod_src := (HelpingOff.t mn jobs ★ CFilter.filter msk SchI.t).
  Local Notation mod_tgt := (HelpingOn.t mn jobs ★ CFilter.filter msk SchI.t).

  Local Lemma wf_src ctx : Mod.wf (mod_tgt ★ ctx) → Mod.wf (mod_src ★ ctx).
  Proof using.
    (* wf proof *)
    intros WF; ss.
    pose proof WF as WF1; eapply Mod.add_wf_inv in WF1 as [[? [? ?]]%Mod.add_wf_inv [? [Hdom Hnd]]].
    apply Mod.add_wf; eauto.
    { apply Mod.add_wf; eauto.
      { econs; ss; [mod_tac|prove_nodup]. }
      { rewrite /Mod.fnsems /HelpingOff.fnsems /= ?fmap_insert fmap_empty. set_solver. }
      { rewrite NoDup_app in Hnd; des; ss. }
    }
    { clear -Hdom.
      intros ? a ?; eapply Hdom; [|done]; move: a.
      rewrite ?dom_union_with /=. set_solver.
    }
  Qed.

  Definition msk_ctx (msk : emask) : Prop :=
    (∀ k, msk _ (subevent _ (SGet k)) = true →
      scope k ∉ SchI.scopes ++ HelpingOn.scopes mn) ∧
    (∀ k v, msk _ (subevent _ (SPut k v)) = true →
      scope k ∉ SchI.scopes ++ HelpingOn.scopes mn).

  Notation prog_s ctx rs := (LMod.prog
    (Mod.to_lmod
      ((SMod.to_mod ∅ (HelpingOff.Mod mn jobs)
      ★ CFilter.filter msk (SMod.to_mod ∅ SchI.smod)) ★ ctx) rs)).
  Notation prog_t ctx rs := (LMod.prog
    (Mod.to_lmod
      ((SMod.to_mod ∅ (HelpingOn.Mod mn jobs)
      ★ CFilter.filter msk (SMod.to_mod ∅ SchI.smod)) ★ ctx) rs)).

  Definition run_s : Any.t → itree (lmodE Σ) Any.t := λ x,
    ⇓cris (⇓sb(msk_scp (HelpingOff.scopes mn) msk_true)
      ((tau;; ⇓smod(∅) (HelpingOff.run jobs x)))).
  Definition run_t : Any.t → itree (lmodE Σ) Any.t := λ x,
    ⇓cris (⇓sb(msk_scp (HelpingOn.scopes mn) msk_true)
      ((tau;; ⇓smod(∅) (HelpingOn.run mn jobs x)))).

  Definition help_s : Any.t → itree (lmodE Σ) Any.t := λ x,
    ⇓cris (⇓sb(msk_scp (HelpingOff.scopes mn) msk_true)
      ((tau;; ⇓smod(∅) (HelpingOff.help x)))).
  Definition help_t : Any.t → itree (lmodE Σ) Any.t := λ x,
    ⇓cris (⇓sb(msk_scp (HelpingOff.scopes mn) msk_true)
      ((tau;; ⇓smod(∅) (HelpingOn.help mn jobs x)))).

  Definition yield : Any.t → itree (lmodE Σ) Any.t := λ x,
    ⇓cris (⇓sb(CFilter.msk_filter_out msk (msk_real (msk_scp SchI.scopes msk_true)))
      (tau;; ⇓smod(∅) (cfunU SchHdr.yield SchI.yield x))).
  Definition inner_spawn : Any.t → itree (lmodE Σ) Any.t := λ x,
    ⇓cris (⇓sb(CFilter.msk_filter_out msk (msk_real (msk_scp SchI.scopes msk_true)))
      (tau;; ⇓smod(∅) (cfunU SchHdr._spawn SchI.inner_spawn x))).
  Definition spawn : Any.t → itree (lmodE Σ) Any.t := λ x,
    ⇓cris (⇓sb(CFilter.msk_filter_out msk (msk_real (msk_scp SchI.scopes msk_true)))
      (tau;; ⇓smod(∅) (cfunU SchHdr.spawn SchI.spawn x))).
  Definition join : Any.t → itree (lmodE Σ) Any.t := λ x,
    ⇓cris (⇓sb(CFilter.msk_filter_out msk (msk_real (msk_scp SchI.scopes msk_true)))
      (tau;; ⇓smod(∅) (cfunU SchHdr.join SchI.join x))).

  Local Lemma dom_helping_on :
    dom (Mod.fnsems (HelpingOn.t mn jobs)) = set_map funid (Helping.exports mn).
  Proof. set_solver. Qed.

  Local Lemma dom_helping_off :
    dom (Mod.fnsems (HelpingOff.t mn jobs)) = set_map funid (Helping.exports mn).
  Proof. set_solver. Qed.

  Lemma prog_s_run ctx rs : Mod.wf (mod_src ★ ctx) → prog_s ctx rs (Helping.run mn) = Some run_s.
  Proof. intros ?. rewrite /LMod.prog Mod.to_lmod_fnsems. simpl_map; ss. Qed.

  Lemma prog_t_run ctx rs : Mod.wf (mod_tgt ★ ctx) → prog_t ctx rs (Helping.run mn) = Some run_t.
  Proof. intros ?. rewrite /LMod.prog Mod.to_lmod_fnsems. simpl_map; ss. Qed.

  Lemma prog_s_help ctx rs : Mod.wf (mod_src ★ ctx) → prog_s ctx rs (Helping.help mn) = Some help_s.
  Proof. intros ?. rewrite /LMod.prog Mod.to_lmod_fnsems. simpl_map; ss. Qed.

  Lemma prog_t_help ctx rs : Mod.wf (mod_tgt ★ ctx) → prog_t ctx rs (Helping.help mn) = Some help_t.
  Proof. intros ?. rewrite /LMod.prog Mod.to_lmod_fnsems. simpl_map; ss. Qed.

  Lemma prog_s_yield ctx rs : Mod.wf (mod_src ★ ctx) → prog_s ctx rs SchHdr.yield.1 = Some yield.
  Proof. intros ?. rewrite /LMod.prog Mod.to_lmod_fnsems. simpl_map; ss. Qed.

  Lemma prog_t_yield ctx rs : Mod.wf (mod_tgt ★ ctx) → prog_t ctx rs SchHdr.yield.1 = Some yield.
  Proof. intros ?. rewrite /LMod.prog Mod.to_lmod_fnsems. simpl_map; ss. Qed.

  Lemma prog_s_inner_spawn ctx rs :
    Mod.wf (mod_src ★ ctx) → prog_s ctx rs SchHdr._spawn.1 = Some inner_spawn.
  Proof. intros ?. rewrite /LMod.prog Mod.to_lmod_fnsems. simpl_map; ss. Qed.

  Lemma prog_t_inner_spawn ctx rs :
    Mod.wf (mod_tgt ★ ctx) → prog_t ctx rs SchHdr._spawn.1 = Some inner_spawn.
  Proof. intros ?. rewrite /LMod.prog Mod.to_lmod_fnsems. simpl_map; ss. Qed.

  Lemma prog_s_spawn ctx rs :
    Mod.wf (mod_src ★ ctx) → prog_s ctx rs SchHdr.spawn.1 = Some spawn.
  Proof. intros ?. rewrite /LMod.prog Mod.to_lmod_fnsems. simpl_map; ss. Qed.

  Lemma prog_t_spawn ctx rs :
    Mod.wf (mod_tgt ★ ctx) → prog_t ctx rs SchHdr.spawn.1 = Some spawn.
  Proof. intros ?. rewrite /LMod.prog Mod.to_lmod_fnsems. simpl_map; ss. Qed.

  Lemma prog_s_join ctx rs :
    Mod.wf (mod_src ★ ctx) → prog_s ctx rs SchHdr.join.1 = Some join.
  Proof. intros ?. rewrite /LMod.prog Mod.to_lmod_fnsems. simpl_map; ss. Qed.

  Lemma prog_t_join ctx rs :
    Mod.wf (mod_tgt ★ ctx) → prog_t ctx rs SchHdr.join.1 = Some join.
  Proof. intros ?. rewrite /LMod.prog Mod.to_lmod_fnsems. simpl_map; ss. Qed.

  Lemma prog_s_prog_t fn ctx rs_s rs_t :
    Mod.wf ((HelpingOn.t mn jobs ★ CFilter.filter msk SchI.t) ★ ctx) →
    (prog_s ctx rs_s fn = None ∧ prog_t ctx rs_t fn = None) ∨
    ((fn = Helping.run mn ∧ prog_s ctx rs_s fn = Some run_s ∧
      prog_t ctx rs_t fn = Some run_t) ∨
    (fn = Helping.help mn ∧ prog_s ctx rs_s fn = Some help_s ∧
      prog_t ctx rs_t fn = Some help_t)) ∨
    (funid fn ∈ dom (Mod.fnsems SchI.t) ∧
      (∃ bd, prog_s ctx rs_s fn = Some (ModTr.trans_fnsem (SB.sandbox_body
        (CFilter.msk_filter_out msk (msk_real (msk_scp SchI.scopes msk_true)), bd)))) ∧
      prog_t ctx rs_t fn = prog_s ctx rs_s fn) ∨
    (funid fn ∈ dom (Mod.fnsems ctx) ∧
      prog_t ctx rs_t fn = prog_s ctx rs_s fn ∧
      (∃ msk bd,
        prog_s ctx rs_s fn =
          Some (ModTr.trans_fnsem (SB.sandbox_body (msk, bd))) ∧
        msk_ctx msk)).
  Proof using H.
    intros Hwf; pose proof Hwf as Hwf2; apply Mod.add_wf_inv in Hwf2 as [Hwfl [Hwfctx [Hdisj ?]]].
    pose proof Hwfl as Hwftgt; apply Mod.add_wf_inv in Hwfl as [Hwfhelp [Hwfsch [Hdisj2 ?]]].
    apply wf_src in Hwf as Hwfsrc.
    destruct (decide (funid fn ∈ dom (Mod.fnsems (mod_tgt ★ ctx)))) as [Hfn|Hfn]; cycle 1.
    { left; split.
      { rewrite /LMod.prog Mod.to_lmod_fnsems not_elem_of_dom_1; first ss.
        revert Hfn; rewrite ?Mod.dom_fnsems_add dom_helping_off dom_helping_on //.
      }
      { rewrite /LMod.prog Mod.to_lmod_fnsems not_elem_of_dom_1; ss. }
    }
    right.
    rewrite ?Mod.dom_fnsems_add in Hfn; set_unfold in Hfn; destruct Hfn as [[Hfn|Hfn]|Hfn].
    { left; pose proof Hwfsrc as ?; apply Mod.add_wf_inv in Hwfsrc as [? [? ?]].
      des; clarify; [left|right]; split; auto; split;
        rewrite /LMod.prog Mod.to_lmod_fnsems; erewrite (lookup_fnsems_l); auto;
        try (erewrite lookup_fnsems_l; auto; s; rewrite /HelpingOff.fnsems /HelpingOn.fnsems;
          simpl_map; ss; fail); ss.
    }
    { pose proof Hwfsrc as ?; apply Mod.add_wf_inv in Hwfsrc as [? [? ?]].
      right; left; split; first by (des; clarify; set_solver).
      assert (Hfn2 : funid fn ∈ dom (Mod.fnsems (CFilter.filter msk SchI.t))).
      { des; clarify; set_solver. }
      clear Hfn.
      assert (Mod.fnsems ctx !! funid fn = None) by
        (rewrite not_elem_of_dom_1 //; intros ?; eapply Hdisj; eauto;
          rewrite Mod.dom_fnsems_add elem_of_union; right; done).
      assert (Mod.fnsems (HelpingOff.t mn jobs) !! funid fn = None).
      { rewrite not_elem_of_dom_1 //; intros ?; eapply Hdisj2; set_solver. }
      assert (Mod.fnsems (HelpingOn.t mn jobs) !! funid fn = None).
      { rewrite not_elem_of_dom_1 //; intros ?; eapply Hdisj2; eauto. }
      rewrite /LMod.prog ?Mod.to_lmod_fnsems !(lookup_fnsems_None_r _ ctx) //.
      rewrite ?(lookup_fnsems_None_l) //; split; [|refl].
      set_unfold in Hfn2; des; clarify; simpl_map; eauto.
    }
    { right; right; split; first done.
      apply elem_of_dom in Hfn as [[[msk' bd]|] Hfn]; cycle 1.
      { exfalso; inv Hwfctx; rewrite map_Forall_lookup in wf_fns;
          hexploit (wf_fns (funid fn) None); auto; by (intros []).
      }
      rewrite /LMod.prog ?Mod.to_lmod_fnsems; try repeat erewrite lookup_fnsems_r; eauto.
      esplits; eauto.
      eapply Mod.add_wf_inv in Hwf as [? [? [? [? [Hnd ?]]%NoDup_app]]].
      hexploit (Mod.well_scoped_fns ctx); rewrite map_Forall_lookup => /(_ (funid fn) (msk', bd)).
      rewrite lookup_omap Hfn => /(_ eq_refl) [Hput Hget]; split.
      { intros ? ?%Hget; rewrite elem_of_app; ss; ii; exfalso; eapply Hnd; eauto.
        rewrite sorting.merge_sort_Permutation; rewrite elem_of_cons; des; [right|left]; set_solver.
      }
      { intros ? ? ?%Hput; rewrite elem_of_app; ss; ii; exfalso; eapply Hnd; eauto.
        rewrite sorting.merge_sort_Permutation; rewrite elem_of_cons; des; [right|left]; set_solver.
      }
    }
  Qed.

  Definition requests
      (tl : list (itree (lmodE Σ) Any.t * itree (lmodE Σ) Any.t *
        option ((nat * help_state * option (SAny.t * option namespace)) + (nat * (SAny.t * option namespace)))))
      : list nat :=
    foldr
      (λ '(itrs, e) acc, match e with | Some (inl (req, _, _)) => req :: acc | _ => acc end)
      [] tl.

  Lemma requests_app l1 l2 : requests (l1 ++ l2) = requests l1 ++ requests l2.
  Proof. induction l1; ss; repeat case_match; ss; rewrite IHl1 //. Qed.

  Lemma requests_in rid l :
    rid ∈ requests l → ∃ stid st no, l.*2 !! stid = Some (Some (inl (rid, st, no))).
  Proof.
    induction l as [|[? [[[[rid2 ?] ?]|arg]|]] l]; first (intros; set_solver); ss.
    { intros [->|[stid ?]%IHl]%elem_of_cons.
      { exists 0; esplits; ss. }
      des; exists (S stid); esplits; ss; eauto.
    }
    { intros [stid ?]%IHl; des; exists (S stid); esplits; ss; eauto. }
    { intros [stid ?]%IHl; des; exists (S stid); esplits; ss; eauto. }
  Qed.

  Lemma requests_inr stid es0 es1 arg tl :
    (tl !! stid = Some (es0, None) ∨ ∃ arg0, tl !! stid = Some (es0, Some (inr arg0))) →
    requests (<[stid:=(es1, Some (inr arg))]> tl) = requests tl.
  Proof.
    intros [[tl1 [tl2 [-> ->]]]%elem_of_list_split_length|
      [? [tl1 [tl2 [-> ->]]]%elem_of_list_split_length]];
      rewrite insert_app_r_alt // Nat.sub_diag /= ?requests_app //=.
  Qed.

  Lemma requests_id stid es1 tl :
    NoDup (requests tl) → NoDup (requests (<[stid:=(es1, None)]> tl)).
  Proof.
    destruct (decide (stid < length tl)) as [Hstid|]; cycle 1.
    { rewrite list_insert_ge //; lia. }
    apply lookup_lt_is_Some_2 in Hstid as [e Hstid]; apply elem_of_list_split_length in Hstid.
    destruct Hstid as [tl1 [tl2 [-> ->]]].
    rewrite insert_app_r_alt // Nat.sub_diag /= !requests_app /=; repeat case_match; ss.
    rewrite cons_app Permutation_app_swap_app NoDup_cons; i; des; ss.
  Qed.

  Lemma requests_fmap_snd tl tl2 :
    tl.*2 = tl2.*2 →
    requests tl = requests tl2.
  Proof.
    revert tl2; induction tl as [|[p e] tl]; intros [|[p2 e2] tl2]; try done.
    rewrite !fmap_cons (cons_app (p, e)) (cons_app (p2, e2)) !requests_app.
    intros Heq; inv Heq; rewrite (IHtl tl2); ss.
  Qed.

  Definition reqmap_rel
      (tl : list (itree (lmodE Σ) Any.t * itree (lmodE Σ) Any.t *
        option ((nat * help_state * option (SAny.t * option namespace)) + (nat * (SAny.t * option namespace)))))
      (reqmap : gmap nat help_state) : Prop :=
    NoDup (requests tl) ∧
    (∃ (f : nat → option nat),
      Inj (=) (λ x y, ∃ z, x = Some z ∧ y = Some z) f ∧
      (∀ stid, is_Some (f stid) ↔ ∃ arg, tl.*2 !! stid = Some (Some (inr arg))) ∧
      (∀ stid stid2 reqid arg, f stid = Some stid2 →
        tl.*2 !! stid = Some (Some (inr (reqid, arg))) →
        tl.*2 !! stid2 = Some (Some (inl (reqid, InProgress, Some arg))))) ∧
    (∀ stid rid st no,
      (tl.*2 !! stid = Some (Some (inl (rid, st, no))) → reqmap !! rid = Some st)) ∧
    (∀ rid N arg, reqmap !! rid = Some (Pend N arg) →
      ∃ stid, tl.*2 !! stid = Some (Some (inl (rid, Pend N arg, None)))).

  Lemma reqmap_rel_id stid es0 es1 r tl reqmap :
    tl !! stid = Some (es0, r) →
    reqmap_rel tl reqmap →
    reqmap_rel (<[stid:=(es1, r)]> tl) reqmap.
  Proof using.
    intros [tl1 [tl2 [-> Hlen]]]%elem_of_list_split_length.
    rewrite -(Nat.add_0_r stid); subst stid; rewrite /reqmap_rel insert_app_r; cbn.
    rewrite !requests_app /= !fmap_app; cbn; destruct r; eauto.
  Qed.

  Lemma reqmap_rel_id_2
      tl reqmap stid_helper stid_helpee rid arg arg2 helper1 helpee1 :
    tl.*2 !! stid_helper = Some (Some (inr (rid, arg))) →
    tl.*2 !! stid_helpee = Some (Some (inl (rid, InProgress, Some arg))) →
    reqmap_rel tl reqmap →
    (∃ (f : nat → option nat),
      Inj (=) (λ x y, ∃ z, x = Some z ∧ y = Some z) f ∧
      (∀ stid, is_Some (f stid) ↔ ∃ arg, tl.*2 !! stid = Some (Some (inr arg))) ∧
      (∀ stid stid2 reqid arg, f stid = Some stid2 →
        tl.*2 !! stid = Some (Some (inr (reqid, arg))) →
        tl.*2 !! stid2 = Some (Some (inl (reqid, InProgress, Some arg)))) ∧
      f stid_helper = Some stid_helpee) →
    reqmap_rel
      (<[stid_helper := (helper1, Some (inr (rid, arg2)))]>
        (<[stid_helpee := (helpee1, Some (inl (rid, InProgress, Some arg2)))]> tl))
      (<[rid := InProgress]> reqmap).
  Proof using.
    intros Hhelper Hhelpee [Hnodup [_ [Hrel1 Hrel2]]] [f [Hinj [Hf1 [Hf2 Hfstid]]]].
    apply list_lookup_fmap_Some in Hhelper as [[? o] [Hhelper ?]]; ss; subst o.
    apply list_lookup_fmap_Some in Hhelpee as [[? o] [Hhelpee ?]]; ss; subst o.
    apply lookup_lt_Some in Hhelper as Hhelperlen. apply lookup_lt_Some in Hhelpee as Hhelpeelen.
    assert (stid_helpee ≠ stid_helper) by (ii; clarify).
    split.
    { erewrite (requests_inr stid_helper); [|rewrite list_lookup_insert_ne //; right; eauto].
      revert Hhelpee; intros [tl1 [tl2 [-> ->]]]%elem_of_list_split_length.
      rewrite insert_app_r_alt // Nat.sub_diag /= requests_app /=.
      rewrite requests_app //= in Hnodup.
    }
    splits.
    { exists f; splits; first done.
      { intros stid; rewrite Hf1; destruct (decide (stid = stid_helper)) as [->|?].
        { rewrite !list_lookup_fmap list_lookup_insert ?length_insert //= Hhelper /=.
          split; i; des; eauto.
        }
        rewrite !list_lookup_fmap list_lookup_insert_ne //.
        split; intros [arg0 Harg0].
        { rewrite list_lookup_insert_ne; eauto.
          ii; clarify; rewrite Hhelpee // in Harg0.
        }
        assert (stid ≠ stid_helpee); [ii; clarify; rewrite list_lookup_insert // in Harg0|].
        rewrite list_lookup_insert_ne in Harg0; eauto.
      }
      intros stid stid2 arg1 reqid Hstid.
      destruct (decide (stid = stid_helper)) as [->|?].
      { rewrite !list_lookup_fmap !list_lookup_insert ?length_insert //=. i; clarify.
        eapply Hf2 in Hstid as Hstid2; [|rewrite list_lookup_fmap Hhelper //].
        rewrite list_lookup_insert_ne // list_lookup_insert //; ss; eauto.
      }
      rewrite !list_lookup_fmap list_lookup_insert_ne //.
      destruct (decide (stid = stid_helpee)) as [->|?].
      { rewrite list_lookup_insert //. }
      rewrite list_lookup_insert_ne //.
      destruct (decide (stid2 = stid_helper)) as [->|?]; ss.
      { rewrite -list_lookup_fmap; intros Hstid2.
        eapply Hf2 in Hstid; [|eauto]; des.
        rewrite list_lookup_fmap //= Hhelper in Hstid; clarify.
      }
      rewrite !list_lookup_insert_ne //.
      { rewrite -?list_lookup_fmap; intros Hstidtl. eapply Hf2; eauto. }
      ii; clarify. hexploit (Hinj stid stid_helper); ss; esplits; eauto.
    }
    { intros stid reqid st no Hstid.
      rewrite list_lookup_fmap in Hstid.
      destruct (decide (stid_helper = stid)); subst.
      { rewrite list_lookup_insert //= in Hstid; clarify.
        rewrite length_insert //.
      }
      rewrite list_lookup_insert_ne // in Hstid.
      destruct (decide (stid_helpee = stid)); subst.
      { rewrite list_lookup_insert //= in Hstid; clarify.
        rewrite lookup_insert //.
      }
      rewrite list_lookup_insert_ne // in Hstid.
      rewrite lookup_insert_ne; [eapply Hrel1; rewrite list_lookup_fmap; eauto|].
      ii; clarify.
      revert Hhelpee; intros [tl1 [tl2 [-> ->]]]%elem_of_list_split_length.
      rewrite requests_app /= cons_app Permutation_app_swap_app in Hnodup.
      apply NoDup_cons in Hnodup; apply Hnodup.
      rewrite -list_lookup_fmap in Hstid.
      apply list_lookup_fmap_inv in Hstid as [[[? ?] ?] [? Hstid]]; ss; clarify.
      apply lookup_app_Some in Hstid as [Hstid|[? Hstid]].
      { apply elem_of_app; left.
        apply elem_of_list_split_length in Hstid as [? [? [-> ->]]].
        rewrite requests_app /=; set_solver-.
      }
      rewrite lookup_cons in Hstid; des_ifs; first lia.
      apply elem_of_list_split_length in Hstid as [? [? [-> ->]]].
      apply elem_of_app; right.
      rewrite requests_app //=; set_solver-.
    }
    intros rid1 N1 arg1; destruct (decide (rid1 = rid)).
    { subst; rewrite lookup_insert; i; clarify. }
    rewrite lookup_insert_ne //; intros [stid1 Hstid1]%Hrel2.
    exists stid1; rewrite !list_lookup_fmap !list_lookup_insert_ne // -?list_lookup_fmap //.
    { ii; clarify. rewrite list_lookup_fmap Hhelpee /= in Hstid1; clarify. }
    { ii; clarify. rewrite list_lookup_fmap Hhelper /= in Hstid1; clarify. }
  Qed.

  Lemma reqmap_rel_inprogress_done
      tl reqmap stid_helper stid_helpee reqid arg ret helper1 helpee1 :
    tl.*2 !! stid_helper = Some (Some (inr (reqid, arg))) →
    tl.*2 !! stid_helpee = Some (Some (inl (reqid, InProgress, Some arg))) →
    reqmap_rel tl reqmap →
    (∃ (f : nat → option nat),
      Inj (=) (λ x y, ∃ z, x = Some z ∧ y = Some z) f ∧
      (∀ stid, is_Some (f stid) ↔ ∃ arg, tl.*2 !! stid = Some (Some (inr arg))) ∧
      (∀ stid stid2 reqid arg, f stid = Some stid2 →
        tl.*2 !! stid = Some (Some (inr (reqid, arg))) →
        tl.*2 !! stid2 = Some (Some (inl (reqid, InProgress, Some arg)))) ∧
      f stid_helper = Some stid_helpee) →
    reqmap_rel
      (<[stid_helper := (helper1, None)]>
        (<[stid_helpee := (helpee1, Some (inl (reqid, Done ret, None)))]> tl))
      (<[reqid := Done ret]> reqmap).
  Proof using.
    intros Hhelper Hhelpee [Hnodup [_ [Hrel1 Hrel2]]] [f [Hinj [Hf1 [Hf2 Hfstid]]]].
    apply list_lookup_fmap_Some in Hhelper as [[? o] [Hhelper ?]]; ss; subst o.
    apply list_lookup_fmap_Some in Hhelpee as [[? o] [Hhelpee ?]]; ss; subst o.
    apply lookup_lt_Some in Hhelper as Hhelperlen. apply lookup_lt_Some in Hhelpee as Hhelpeelen.
    assert (stid_helpee ≠ stid_helper) by (ii; clarify).
    split.
    { apply requests_id; eauto.
      eapply elem_of_list_split_length in Hhelpee as [? [? [-> ->]]].
      revert Hnodup; rewrite insert_app_r_alt // Nat.sub_diag /= !requests_app //.
    }
    splits.
    { exists (λ x, if (decide (x = stid_helper)) then None else f x); splits.
      { intros x y; repeat case_decide; subst; auto; ii; des; ss. }
      { intros stid; case_decide; subst.
        { rewrite list_lookup_fmap list_lookup_insert ?length_insert //=.
          split; intros [? ?]; des; ss.
        }
        rewrite Hf1 !list_lookup_fmap list_lookup_insert_ne //.
        split; intros [arg0 Harg0].
        { rewrite list_lookup_insert_ne; eauto.
          ii; clarify; rewrite Hhelpee // in Harg0.
        }
        assert (stid ≠ stid_helpee); [ii; clarify; rewrite list_lookup_insert // in Harg0|].
        rewrite list_lookup_insert_ne in Harg0; eauto.
      }
      intros stid stid2 arg1 reqid2 Hstid.
      destruct (decide (stid = stid_helper)) as [->|?].
      { rewrite !list_lookup_fmap !list_lookup_insert ?length_insert //=. }
      rewrite !list_lookup_fmap list_lookup_insert_ne //.
      destruct (decide (stid = stid_helpee)) as [->|?].
      { rewrite list_lookup_insert //. }
      rewrite list_lookup_insert_ne //.
      destruct (decide (stid2 = stid_helper)) as [->|?]; ss.
      { rewrite -list_lookup_fmap; intros Hstid2.
        eapply Hf2 in Hstid; [|eauto]; des.
        rewrite list_lookup_fmap //= Hhelper in Hstid; clarify.
      }
      rewrite !list_lookup_insert_ne //.
      { rewrite -?list_lookup_fmap; intros Hstidtl. eapply Hf2; eauto. }
      ii; clarify. hexploit (Hinj stid stid_helper); ss; esplits; eauto.
    }
    { intros stid reqid2 st no Hstid.
      rewrite list_lookup_fmap in Hstid.
      destruct (decide (stid_helper = stid)); subst.
      { rewrite list_lookup_insert //= in Hstid; clarify.
        rewrite length_insert //.
      }
      rewrite list_lookup_insert_ne // in Hstid.
      destruct (decide (stid_helpee = stid)); subst.
      { rewrite list_lookup_insert //= in Hstid; clarify; rewrite lookup_insert //. }
      rewrite list_lookup_insert_ne // in Hstid.
      rewrite lookup_insert_ne; [eapply Hrel1; rewrite list_lookup_fmap; eauto|].
      ii; clarify.
      revert Hhelpee; intros [tl1 [tl2 [-> ->]]]%elem_of_list_split_length.
      rewrite requests_app /= cons_app Permutation_app_swap_app in Hnodup.
      apply NoDup_cons in Hnodup; apply Hnodup.
      rewrite -list_lookup_fmap in Hstid.
      apply list_lookup_fmap_inv in Hstid as [[[? ?] ?] [? Hstid]]; ss; clarify.
      apply lookup_app_Some in Hstid as [Hstid|[? Hstid]].
      { apply elem_of_app; left.
        apply elem_of_list_split_length in Hstid as [? [? [-> ->]]].
        rewrite requests_app /=; set_solver-.
      }
      rewrite lookup_cons in Hstid; des_ifs; first lia.
      apply elem_of_list_split_length in Hstid as [? [? [-> ->]]].
      apply elem_of_app; right.
      rewrite requests_app //=; set_solver-.
    }
    intros rid1 N1 arg1; destruct (decide (rid1 = reqid)).
    { subst; rewrite lookup_insert; i; clarify. }
    rewrite lookup_insert_ne //; intros [stid1 Hstid1]%Hrel2.
    exists stid1; rewrite !list_lookup_fmap !list_lookup_insert_ne // -?list_lookup_fmap //.
    { ii; clarify. rewrite list_lookup_fmap Hhelpee /= in Hstid1; clarify. }
    { ii; clarify. rewrite list_lookup_fmap Hhelper /= in Hstid1; clarify. }
  Qed.

  Lemma reqmap_rel_Some reqmap rid tl stid es st no :
    tl !! stid = Some (es, Some (inl (rid, st, no))) →
    reqmap_rel tl reqmap →
    reqmap !! rid = Some st.
  Proof using.
    rewrite /reqmap_rel; intros Hin [? [? [Hrel1 ?]]].
    apply (Hrel1 stid rid st no). rewrite list_lookup_fmap Hin; eauto.
  Qed.

  Lemma reqmap_rel_Some_2 tl reqmap rid N arg :
    reqmap_rel tl reqmap →
    reqmap !! rid = Some (Pend N arg) →
    ∃ stid i_s i_t, tl !! stid = Some (i_s, i_t, Some (inl (rid, Pend N arg, None))).
  Proof using.
    rewrite /reqmap_rel; intros [? [? Hsome]] [stid Hstid]%Hsome; exists stid.
    apply list_lookup_fmap_inv in Hstid as [[[? ?] [|]] [? ?]]; ss.
    clarify; esplits; eauto.
  Qed.

  Lemma reqmap_rel_pend_inprogress
      tl reqmap stid_helper stid_helpee rid N jid arg helper0 helper1 helpee0 helpee1 :
    tl !! stid_helper = Some (helper0, None) →
    tl !! stid_helpee = Some (helpee0, Some (inl (rid, Pend N jid, None))) →
    reqmap_rel tl reqmap →
    reqmap_rel
      (<[stid_helper := (helper1, Some (inr (rid, arg)))]>
        (<[stid_helpee := (helpee1, Some (inl (rid, InProgress, Some arg)))]> tl))
      (<[rid := InProgress]> reqmap).
  Proof using.
    intros Hhelper Hhelpee [Hnodup [[f [Hinj [Hf1 Hf2]]] [Hrel1 Hrel2]]].
    apply lookup_lt_Some in Hhelper as Hhelperlen. apply lookup_lt_Some in Hhelpee as Hhelpeelen.
    assert (stid_helpee ≠ stid_helper) by (ii; clarify).
    split.
    { erewrite (requests_inr stid_helper); [|rewrite list_lookup_insert_ne //; eauto].
      revert Hhelpee; intros [tl1 [tl2 [-> ->]]]%elem_of_list_split_length.
      rewrite insert_app_r_alt // Nat.sub_diag /= requests_app /=.
      rewrite requests_app //= in Hnodup.
    }
    splits.
    { exists (λ x, if (decide (x = stid_helper)) then (Some stid_helpee) else f x); splits.
      { intros x y; repeat case_decide; subst; auto.
        { intros [z [<-%Some_inj Hy]].
          destruct (Hf1 y) as [Hf3 _]; hexploit Hf3; eauto; clear Hf3; intros [[? ?] Hf3].
          eapply Hf2 in Hy as Hy; eauto.
          rewrite list_lookup_fmap Hhelpee // in Hy.
        }
        { intros [z [Hz <-%Some_inj]].
          destruct (Hf1 x) as [Hf3 _]; hexploit Hf3; eauto; clear Hf3; intros [[? ?] Hf3].
          eapply Hf2 in Hz as Hz; eauto.
          rewrite list_lookup_fmap Hhelpee // in Hz.
        }
      }
      { intros stid; case_decide; subst.
        { rewrite list_lookup_fmap list_lookup_insert ?length_insert // /=. split; eauto. }
        rewrite Hf1 !list_lookup_fmap list_lookup_insert_ne //.
        destruct (decide (stid = stid_helpee)) as [->|?].
        { rewrite list_lookup_insert // Hhelpee; split; i; des; clarify. }
        rewrite list_lookup_insert_ne //.
      }
      intros stid stid2; case_decide; subst.
      { intros ? [? ?] <-%Some_inj; rewrite list_lookup_fmap list_lookup_insert ?length_insert //.
        simpl; intros Heq; inv Heq.
        rewrite list_lookup_fmap list_lookup_insert_ne // list_lookup_insert ?length_insert //=.
      }
      intros argstid Hstid. rewrite !list_lookup_fmap list_lookup_insert_ne //.
      destruct (decide (stid = stid_helpee)) as [->|?].
      { rewrite !list_lookup_insert //. }
      rewrite list_lookup_insert_ne // -list_lookup_fmap; intros Hstid2 Hstid3.
      specialize (Hf2 stid stid2 argstid Hstid Hstid2 Hstid3) as Hf2.
      rewrite !list_lookup_insert_ne //= -?list_lookup_fmap //.
      { ii; clarify; rewrite list_lookup_fmap Hhelpee // in Hf2. }
      { ii; clarify; rewrite list_lookup_fmap Hhelper // in Hf2. }
    }
    { intros stid reqid st no Hstid.
      rewrite list_lookup_fmap in Hstid.
      destruct (decide (stid_helper = stid)); subst.
      { rewrite list_lookup_insert //= in Hstid; clarify.
        rewrite length_insert //.
      }
      rewrite list_lookup_insert_ne // in Hstid.
      destruct (decide (stid_helpee = stid)); subst.
      { rewrite list_lookup_insert //= in Hstid; clarify.
        rewrite lookup_insert //.
      }
      rewrite list_lookup_insert_ne // in Hstid.
      rewrite lookup_insert_ne; [eapply Hrel1; rewrite list_lookup_fmap; eauto|].
      ii; clarify.
      revert Hhelpee; intros [tl1 [tl2 [-> ->]]]%elem_of_list_split_length.
      rewrite requests_app /= cons_app Permutation_app_swap_app in Hnodup.
      apply NoDup_cons in Hnodup; apply Hnodup.
      rewrite -list_lookup_fmap in Hstid.
      apply list_lookup_fmap_inv in Hstid as [[[? ?] ?] [? Hstid]]; ss; clarify.
      apply lookup_app_Some in Hstid as [Hstid|[? Hstid]].
      { apply elem_of_app; left.
        apply elem_of_list_split_length in Hstid as [? [? [-> ->]]].
        rewrite requests_app /=; set_solver-.
      }
      rewrite lookup_cons in Hstid; des_ifs; first lia.
      apply elem_of_list_split_length in Hstid as [? [? [-> ->]]].
      apply elem_of_app; right.
      rewrite requests_app //=; set_solver-.
    }
    intros rid1 N1 arg1; destruct (decide (rid1 = rid)).
    { subst; rewrite lookup_insert; i; clarify. }
    rewrite lookup_insert_ne //; intros [stid1 Hstid1]%Hrel2.
    exists stid1; rewrite !list_lookup_fmap !list_lookup_insert_ne // -?list_lookup_fmap //.
    { ii; clarify. rewrite list_lookup_fmap Hhelpee /= in Hstid1; clarify. }
    { ii; clarify. rewrite list_lookup_fmap Hhelper /= in Hstid1; clarify. }
  Qed.

  Lemma reqmap_rel_done_2 tl stid rid st es0 es1 reqmap ret :
    tl !! stid = Some (es0, Some (inl (rid, st, None))) →
    reqmap_rel tl reqmap →
    reqmap_rel (<[stid := (es1, None)]> tl) (<[rid := Done ret]> reqmap).
  Proof using.
    intros Hin [Hnodup [Hrel0 [Hrel1 Hrel2]]]; eapply lookup_lt_Some in Hin as Hlen; split.
    { revert Hin; intros [tl1 [tl2 [-> ?]]]%elem_of_list_split_length.
      rewrite -(Nat.add_0_r stid); subst stid; rewrite insert_app_r /=.
      revert Hnodup; rewrite !requests_app /= cons_app Permutation_app_swap_app.
      rewrite NoDup_cons; by intros [??].
    }
    splits.
    { destruct Hrel0 as [f [Hinj Hrel0]]; exists f; splits; first done.
      { intros stid1; destruct Hrel0 as [Hrel0 _]; rewrite Hrel0.
        rewrite !list_lookup_fmap.
        destruct (decide (stid1 = stid)) as [->|].
        { rewrite !list_lookup_insert //= Hin /=; split; i; des; clarify. }
        rewrite !list_lookup_insert_ne //.
      }
      intros stid1 stid2 arg reqid Hstid1; assert (stid1 ≠ stid).
      { ii; clarify; destruct Hrel0 as [Hrel0 _]; destruct (Hrel0 stid) as [Hrel01 _].
        hexploit Hrel01; [rewrite Hstid1 //|rewrite list_lookup_fmap Hin //=; i; des; clarify].
      }
      rewrite list_lookup_fmap list_lookup_insert_ne // -list_lookup_fmap. intros Hstid12.
      destruct Hrel0 as [_ Hrel0]; hexploit Hrel0; eauto.
      intros Hstid2; rewrite list_lookup_fmap list_lookup_insert_ne -?list_lookup_fmap.
      { rewrite Hstid2; eauto. }
      ii; clarify; rewrite list_lookup_fmap Hin // in Hstid2.
    }
    { intros stid1 rid1 st1 no1 Hstid1.
      destruct (decide (stid = stid1)) as [->|Heq].
      { rewrite list_lookup_fmap list_lookup_insert //= in Hstid1; clarify. }
      rewrite list_lookup_fmap list_lookup_insert_ne // in Hstid1.
      rewrite lookup_insert_ne; [eapply Hrel1; rewrite list_lookup_fmap; eauto|].
      ii; clarify.
      clear -Hin Hstid1 Hnodup Heq.
      revert Hin; intros [tl1 [tl2 [-> ->]]]%elem_of_list_split_length.
      rewrite requests_app /= in Hnodup.
      apply fmap_Some in Hstid1 as [[? o] [Hstid1 ?]]; ss; subst o.
      apply lookup_app_Some in Hstid1 as [Hstid1|[? Hstid2]].
      { apply elem_of_list_split_length in Hstid1 as [? [? [-> ?]]].
        rewrite requests_app /= NoDup_app in Hnodup.
        destruct Hnodup as [? [Hnodup ?]]; specialize (Hnodup rid1); set_solver.
      }
      rewrite lookup_cons in Hstid2; des_ifs; first lia.
      apply elem_of_list_split_length in Hstid2 as [? [? [-> ?]]].
      rewrite requests_app /= NoDup_app in Hnodup.
      destruct Hnodup as [? [_ Hnodup]]. apply NoDup_cons in Hnodup; set_solver.
    }
    intros rid1 jid1; destruct (decide (rid1 = rid)).
    { subst; rewrite lookup_insert; i; clarify. }
    rewrite lookup_insert_ne //; intros ? [stid1 Hstid1]%Hrel2.
    exists stid1; rewrite list_fmap_insert /= list_lookup_insert_ne //.
    ii; clarify.
    rewrite list_lookup_fmap Hin /= in Hstid1; clarify.
  Qed.

  Lemma reqmap_rel_pend tl reqmap stid es0 es1 rid st N arg no :
    tl !! stid = Some (es0, Some (inl (rid, Pend N arg, no))) →
    reqmap_rel tl reqmap →
    reqmap_rel (<[stid := (es1, Some (inl (rid, st, None)))]> tl) (<[rid := st]> reqmap).
  Proof using.
    intros Hin [Hnodup [Hrel0 [Hrel1 Hrel2]]]; eapply lookup_lt_Some in Hin as Hlen; split.
    { revert Hin; intros [tl1 [tl2 [-> ?]]]%elem_of_list_split_length.
      rewrite -(Nat.add_0_r stid); subst stid; rewrite /reqmap_rel insert_app_r ?fmap_app; cbn.
      revert Hnodup; rewrite /requests ?foldr_app //.
    }
    splits.
    { destruct Hrel0 as [f [Hinj Hrel0]]; exists f; splits; first done.
      { intros stid1; destruct Hrel0 as [Hrel0 _]; rewrite Hrel0.
        rewrite !list_lookup_fmap.
        destruct (decide (stid1 = stid)) as [->|].
        { rewrite !list_lookup_insert //= Hin /=; split; i; des; clarify. }
        rewrite !list_lookup_insert_ne //.
      }
      intros stid1 stid2 ? ? Hstid1; assert (stid1 ≠ stid).
      { ii; clarify; destruct Hrel0 as [Hrel0 _]; destruct (Hrel0 stid) as [Hrel01 _].
        hexploit Hrel01; [rewrite Hstid1 //|rewrite list_lookup_fmap Hin //=; i; des; clarify].
      }
      rewrite list_lookup_fmap list_lookup_insert_ne // -list_lookup_fmap. intros Hstid12.
      destruct Hrel0 as [_ Hrel0]; hexploit Hrel0; eauto.
      intros Hstid2; rewrite list_lookup_fmap list_lookup_insert_ne -?list_lookup_fmap.
      { rewrite Hstid2; eauto. }
      ii; clarify; rewrite list_lookup_fmap Hin // in Hstid2.
    }
    { intros stid1 rid1 st1 no1 Hstid1.
      destruct (decide (stid = stid1)) as [->|Heq].
      { rewrite list_lookup_fmap list_lookup_insert //= in Hstid1; clarify.
        rewrite lookup_insert //.
      }
      rewrite list_lookup_fmap list_lookup_insert_ne // in Hstid1.
      rewrite lookup_insert_ne; [eapply Hrel1; rewrite list_lookup_fmap; eauto|].
      ii; clarify.
      clear -Hin Hstid1 Hnodup Heq.
      revert Hin; intros [tl1 [tl2 [-> ->]]]%elem_of_list_split_length.
      rewrite requests_app /= in Hnodup.
      apply fmap_Some in Hstid1 as [[? o] [Hstid1 ?]]; ss; subst o.
      apply lookup_app_Some in Hstid1 as [Hstid1|[? Hstid2]].
      { apply elem_of_list_split_length in Hstid1 as [? [? [-> ?]]].
        rewrite requests_app /= NoDup_app in Hnodup.
        destruct Hnodup as [? [Hnodup ?]]; specialize (Hnodup rid1); set_solver.
      }
      rewrite lookup_cons in Hstid2; des_ifs; first lia.
      apply elem_of_list_split_length in Hstid2 as [? [? [-> ?]]].
      rewrite requests_app /= NoDup_app in Hnodup.
      destruct Hnodup as [? [_ Hnodup]]. apply NoDup_cons in Hnodup; set_solver.
    }
    intros rid1 jid1; destruct (decide (rid1 = rid)).
    { subst; rewrite lookup_insert; i; clarify.
      exists stid; rewrite list_lookup_fmap list_lookup_insert //.
    }
    rewrite lookup_insert_ne //; intros ? [stid1 Hstid1]%Hrel2.
    exists stid1; rewrite list_fmap_insert /= list_lookup_insert_ne //.
    ii; clarify.
    rewrite list_lookup_fmap Hin /= in Hstid1; clarify.
  Qed.

  Lemma reqmap_rel_done tl stid rid es0 es1 reqmap ret :
    tl !! stid = Some (es0, Some (inl (rid, Done ret, None))) →
    reqmap_rel tl reqmap →
    reqmap_rel (<[stid := (es1, None)]> tl) (reqmap).
  Proof using.
    intros Hin [Hnodup [[f Hrel0] [Hrel1 Hrel2]]]. eapply lookup_lt_Some in Hin as Hlen.
    rewrite /reqmap_rel. splits.
    { revert Hin; intros [tl1 [tl2 [-> ?]]]%elem_of_list_split_length.
      rewrite -(Nat.add_0_r stid); subst stid; rewrite insert_app_r /=.
      revert Hnodup; rewrite !requests_app /= cons_app Permutation_app_swap_app.
      rewrite NoDup_cons; by intros [??].
    }
    { destruct Hrel0 as [Hinj Hrel0]; exists f; splits; first done.
      { intros stid1; destruct Hrel0 as [Hrel0 _]; rewrite Hrel0.
        rewrite !list_lookup_fmap.
        destruct (decide (stid1 = stid)) as [->|].
        { rewrite !list_lookup_insert //= Hin /=; split; i; des; clarify. }
        rewrite !list_lookup_insert_ne //.
      }
      intros stid1 stid2 ? ? Hstid1; assert (stid1 ≠ stid).
      { ii; clarify; destruct Hrel0 as [Hrel0 _]; destruct (Hrel0 stid) as [Hrel01 _].
        hexploit Hrel01; [rewrite Hstid1 //|rewrite list_lookup_fmap Hin //=; i; des; clarify].
      }
      rewrite list_lookup_fmap list_lookup_insert_ne // -list_lookup_fmap. intros Hstid12.
      destruct Hrel0 as [_ Hrel0]; hexploit Hrel0; eauto.
      intros Hstid2; rewrite list_lookup_fmap list_lookup_insert_ne -?list_lookup_fmap.
      { rewrite Hstid2; eauto. }
      ii; clarify; rewrite list_lookup_fmap Hin // in Hstid2.
    }
    { intros stid' ??? Hstid'.
      rewrite list_fmap_insert /= in Hstid'.
      apply lookup_lt_Some in Hstid' as Hlen'. rewrite length_insert in Hlen'.
      destruct (decide (stid = stid')); subst.
      { rewrite list_lookup_insert // in Hstid'; ss. }
      rewrite list_lookup_insert_ne // in Hstid'.
      eapply (Hrel1 stid'); eauto.
    }
    intros ??? [stid' Hlookup]%Hrel2; exists stid'.
    rewrite list_fmap_insert /= list_lookup_insert_ne ?Hlookup //.
    ii; clarify.
    rewrite list_lookup_fmap Hin //= in Hlookup.
  Qed.

  Lemma reqmap_rel_insert_false tl reqmap rid ret :
    rid ∉ (dom reqmap) →
    reqmap_rel tl reqmap →
    reqmap_rel tl (<[rid:=Done ret]> reqmap).
  Proof using.
    intros Hrid [? [? [Hrel1 Hrel2]]]; split; first done.
    splits; eauto.
    { intros ???? Hstid%Hrel1.
      rewrite lookup_insert_ne //.
      ii; clarify; apply elem_of_dom_2 in Hstid; eauto.
    }
    intros rid1.
    destruct (decide (rid = rid1)); subst; [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
    ii; clarify.
  Qed.

  Lemma reqmap_rel_insert_false_2 tl reqmap rid :
    rid ∉ (dom reqmap) →
    reqmap_rel tl reqmap →
    reqmap_rel tl (<[rid:=InProgress]> reqmap).
  Proof using.
    intros Hrid [? [? [Hrel1 Hrel2]]]; split; first done.
    splits; auto.
    { intros ???? Hstid%Hrel1.
      rewrite lookup_insert_ne //.
      ii; clarify; apply elem_of_dom_2 in Hstid; eauto.
    }
    intros rid1.
    destruct (decide (rid = rid1)); subst; [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
    ii; clarify.
  Qed.

  Lemma reqmap_rel_insert_true tl reqmap stid es0 es1 rid st :
    rid ∉ (dom reqmap) →
    tl !! stid = Some (es0, None) →
    reqmap_rel tl reqmap →
    reqmap_rel (<[stid:=(es1, Some (inl (rid, st, None)))]> tl) (<[rid:=st]> reqmap).
  Proof using Σ mn jobs.
    intros Hrid Hin [Hnodup [Hrel0 [Hrel1 Hrel2]]]; eapply lookup_lt_Some in Hin as Hlen; split.
    { rewrite insert_take_drop //.
      rewrite requests_app //= cons_app Permutation_app_swap_app.
      eapply take_drop_middle in Hin as Hmid; rewrite -Hmid in Hnodup; clear Hmid.
      revert Hnodup; rewrite requests_app /=.
      intros ?; apply NoDup_cons; split; eauto.
      intros [Hrid2|Hrid2]%elem_of_app; apply requests_in in Hrid2 as [stid2 [st2 [no2 Hstid2]]].
      { apply Hrid, elem_of_dom.
        apply list_lookup_fmap_inv in Hstid2 as [[? o] [? Hstid2]]; ss; subst o.
        rewrite (Hrel1 stid2 rid st2 no2); ss.
        rewrite list_lookup_fmap. apply lookup_take_Some in Hstid2 as [Hstid2 ?]; rewrite Hstid2 //.
      }
      { apply Hrid, elem_of_dom.
        apply list_lookup_fmap_inv in Hstid2 as [[? o] [? Hstid2]]; ss; subst o.
        rewrite lookup_drop in Hstid2.
        erewrite (Hrel1 (S (stid + stid2)) rid st2 no2); ss.
        rewrite list_lookup_fmap Hstid2 //.
      }
    }
    splits.
    { destruct Hrel0 as [f [Hinj Hrel0]]; exists f; splits; first done.
      { intros stid1; destruct Hrel0 as [Hrel0 _]; rewrite Hrel0.
        rewrite !list_lookup_fmap.
        destruct (decide (stid1 = stid)) as [->|].
        { rewrite !list_lookup_insert //= Hin /=; split; i; des; clarify. }
        rewrite !list_lookup_insert_ne //.
      }
      intros stid1 stid2 ? ? Hstid1; assert (stid1 ≠ stid).
      { ii; clarify; destruct Hrel0 as [Hrel0 _]; destruct (Hrel0 stid) as [Hrel01 _].
        hexploit Hrel01; [rewrite Hstid1 //|rewrite list_lookup_fmap Hin //=; i; des; clarify].
      }
      rewrite list_lookup_fmap list_lookup_insert_ne // -list_lookup_fmap. intros Hstid12.
      destruct Hrel0 as [_ Hrel0]; hexploit Hrel0; eauto.
      intros Hstid2; rewrite list_lookup_fmap list_lookup_insert_ne -?list_lookup_fmap.
      { rewrite Hstid2; eauto. }
      ii; clarify; rewrite list_lookup_fmap Hin // in Hstid2.
    }
    { intros stid1 ? ? ?; destruct (decide (stid1 = stid)); subst.
      { rewrite list_lookup_fmap list_lookup_insert /=; i; clarify; rewrite lookup_insert //. }
      rewrite list_fmap_insert list_lookup_insert_ne //; intros Hcont%Hrel1.
      rewrite lookup_insert_ne //.
      ii; clarify.
      apply Hrid, elem_of_dom; eauto.
    }
    intros rid1.
    destruct (decide (rid = rid1)); subst; [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
    { ii; clarify. exists stid; rewrite list_fmap_insert list_lookup_insert // ?length_fmap //=. }
    intros ?? [? Hstid]%Hrel2; exists x; rewrite list_fmap_insert list_lookup_insert_ne //.
    ii; clarify.
    rewrite list_lookup_fmap Hin /= in Hstid; clarify.
  Qed.

  Lemma reqmap_rel_append tl reqmap es :
    reqmap_rel tl reqmap →
    reqmap_rel (tl ++ [(es, None)]) reqmap.
  Proof using.
    rewrite /reqmap_rel requests_app /= app_nil_r !fmap_app /=.
    intros [? [Hrel0 [Hrel1 Hrel2]]]; split; first done.
    splits.
    { destruct Hrel0 as [f [? Hrel0]]; exists f; splits; first done.
      { intros stid; destruct Hrel0 as [Hrel0 _]; rewrite Hrel0.
        split; first (i; des; erewrite !lookup_app_l_Some; eauto).
        intros [arg [?|[? [??]%list_lookup_singleton_Some]]%lookup_app_Some]; clarify; eauto.
      }
      intros stid stid2 arg [? ?] Hstid Hstid2.
      destruct Hrel0 as [Hrel01 Hrel02]; destruct (Hrel01 stid) as [Hrel01' _];
        hexploit Hrel01'; eauto; intros [[? [? ?]] Hstidtl].
      eapply Hrel02 in Hstid as Hstid2'; eauto.
      erewrite !lookup_app_l_Some in Hstid2; eauto; clarify.
      erewrite !lookup_app_l_Some; eauto.
    }
    { intros ????; rewrite lookup_app_Some; intros [?%Hrel1|[??%list_lookup_singleton_Some]]; eauto.
      des; clarify.
    }
    { intros ??? [stid Hstid]%Hrel2; apply lookup_lt_Some in Hstid as Hlen.
      exists stid; rewrite lookup_app_l //.
    }
  Qed.

  Definition inner_spawn_pend (arg : Any.t) ktr : itree (lmodE Σ) Any.t :=
    ⇓cris (x <- ⇓sb(CFilter.msk_filter_out msk (msk_real (msk_scp SchI.scopes msk_true)))
      (tau;; ⇓smod(∅) (
        'arg : SAny.t <- (arg↓)?;;
        'x1 : thpool <- (cgetU SchI.v_ths);;
        'x2 : nat <- (cgetU SchI.v_tid);;
        r <-
          (match x1 !! x2 with
          | Some (stid, _) =>
              cput SchI.v_ths (<[x2 := (stid, Some arg)]> x1);;;
              Sch.terminate
          | None => triggerUB
          end);;
        Ret (r↑)));;
      ktr x).

  Definition join_pend (arg : Any.t) jtid ktr : itree (lmodE Σ) Any.t :=
    ⇓cris (x <- ⇓sb(CFilter.msk_filter_out msk (msk_real (msk_scp SchI.scopes msk_true)))
      (tau;; ⇓smod(∅) (
        'arg : () <- (arg↓)?;;
        x_3 <- iterC (λ _ : (),
          'x_1 : thpool <- cgetU SchI.v_ths;;
          match x_1 !! jtid with
          | Some (_, Some rv) => Ret (inr (Some rv))
          | Some (_, None) =>
              '() : _ <- ccallU SchHdr.yield tt;; Ret (inl ())
          | None => Ret (inr None)
          end
        ) ();;
        Ret (x_3↑)));; ktr x).

  (* Definition helpee_pend_s
      (j : SAny.t) k
      (fspo : option fspec_rel) x_fsp
      : itree (lmodE Σ) Any.t :=
    ⇓cris (tau;; r <- ⇓sb(msk_scp (HelpingOff.scopes mn) msk_true) (
      HoareCall_epilogue (sp.1 !! (fid SchHdr.yield)) x_fsp (()↑);;;
      ret <- ⇓smod(sp) (𝒴;;; r <- SB.sandbox (msk_pure) (jobs j);; 𝒴;;; Ret r↑);;
      Ret ret
    );; k r). *)

  Definition helpee_pend_t (N : option namespace) (reqid : nat) (arg : SAny.t) k
      : itree (lmodE Σ) Any.t :=
    ⇓cris (tau;; x_ <- ⇓sb(msk_scp (HelpingOff.scopes mn) msk_true) (
      option_Assume N;;;
      x <- ⇓smod(∅) (𝒴@{N};;; HelpingOn.try_run mn jobs reqid);;
      Ret x
    );; k x_).

  Definition helpee_inprogress_s (N : option namespace) (arg : SAny.t) ktr
      : itree (lmodE Σ) Any.t :=
    ⇓cris (tau;;
      ret <- ⇓sb(msk_scp (HelpingOff.scopes mn) msk_true) (
        option_Assume N;;;
        ⇓smod(∅) (𝒴@{N};;; ret <- SB.sandbox msk_pure (jobs arg);;
          ret <- match ret with
          | inl arg1 => tau;; ITree.iter (λ arg, 𝒴@{N};;; SB.sandbox msk_pure (jobs arg)) arg1
          | inr ret => Ret ret
          end;;
          𝒴@{N};;; Ret ret));;
      ktr (ret↑)).

  Definition helpee_inprogress_t (N : option namespace) (arg : SAny.t) reqid ktr
      : itree (lmodE Σ) Any.t :=
    ⇓cris (tau;;
      ret <- ⇓sb(msk_scp (HelpingOff.scopes mn) msk_true) (
        option_Assume N;;;
        ⇓smod(∅) (𝒴@{N};;; ret <- SB.sandbox msk_pure (jobs arg);;
          ret <- match ret with
          | inl arg1 => tau;; ITree.iter (λ arg, 𝒴@{N};;; SB.sandbox msk_pure (jobs arg)) arg1
          | inr ret => Ret ret
          end;;
          trigger (Assume (HelpDone reqid ret));;;
          Ret ret
        ));;
      ktr (ret↑)).

  Definition helper_inprogress_t (N_helper N_helpee : option namespace) (arg : SAny.t) reqid ktr
      : itree (lmodE Σ) Any.t :=
    ⇓cris (tau;;
      ⇓sb(msk_scp (HelpingOff.scopes mn) msk_true) (
        option_Assume N_helpee;;;
        ⇓smod(∅) (𝒴@{N_helpee};;; ret <- SB.sandbox msk_pure (jobs arg);;
          ret <- match ret with
          | inl arg1 => tau;; ITree.iter (λ arg, 𝒴@{N_helpee};;; SB.sandbox msk_pure (jobs arg)) arg1
          | inr ret => Ret ret
          end;;
          option_Guarantee N_helpee;;;
          option_Assume N_helper;;;
          trigger (Assume (HelpDone reqid ret))
        ));;;
      ktr (tt↑)).

  Inductive help_rel 
    : itree (lmodE Σ) Any.t →
      itree (lmodE Σ) Any.t →
      option ((nat * help_state * option (SAny.t * option namespace)) + (nat * (SAny.t * option namespace))) →
      Prop :=
  | help_rel_ret ret : help_rel (Ret ret) (Ret ret) None
  | help_rel_eq itr_s itr_t ktr_s ktr_t itr msk :
      itr_s = ⇓cris (x <- SB.sandbox msk itr;; ktr_s x) →
      itr_t = ⇓cris (x <- SB.sandbox msk itr;; ktr_t x) →
      msk_ctx msk →
      (∀ ret, itr ≠ Ret ret) →
      (∀ (ret : Any.t), help_rel (⇓cris (ktr_s ret)) (⇓cris (ktr_t ret)) None) →
      help_rel itr_s itr_t None
  | help_rel_job_loop arg N rid itr_s itr_t ktr_s ktr_t :
      itr_s = helpee_inprogress_s N arg ktr_s →
      itr_t = helpee_inprogress_t N arg rid ktr_t  →
      (∀ ret, help_rel (⇓cris (ktr_s ret)) (⇓cris (ktr_t ret)) None) →
      help_rel itr_s itr_t (Some (inl (rid, InProgress, None)))
  | help_rel_helpee_inprogress arg jobarg N rid itr_s itr_t ktr_s ktr_t :
      itr_s = helpee_inprogress_s N arg ktr_s →
      itr_t = helpee_pend_t N rid jobarg ktr_t →
      (∀ ret, help_rel (⇓cris (ktr_s ret)) (⇓cris (ktr_t ret)) None) →
      help_rel itr_s itr_t (Some (inl (rid, InProgress, Some (arg, N))))
  | help_rel_helper_inprogress arg N_helper N_helpee rid itr_s itr_t ktr_s ktr_t :
      itr_s = (⇓cris (tau;;
        x_ <- ⇓sb(msk_scp (HelpingOn.scopes mn) msk_true)
          (⇓smod(∅) (option_Assume N_helper;;; 𝒴@{N_helper};;; Ret tt↑));;
        ktr_s x_)) →
      itr_t = helper_inprogress_t N_helper N_helpee arg rid ktr_t →
      (∀ ret, help_rel (⇓cris (ktr_s ret)) (⇓cris (ktr_t ret)) None) →
      help_rel itr_s itr_t (Some (inr (rid, (arg, N_helpee))))
  | help_rel_helpee_done N rid arg itr_s itr_t ktr_s ktr_t ret :
      itr_t = helpee_pend_t N rid arg ktr_t →
      itr_s = (
        ⇓cris (tau;;
          x_ <- ⇓sb(msk_scp (HelpingOn.scopes mn) msk_true)
            (⇓smod(∅) (option_Assume N;;; 𝒴@{N});;;
            Ret ret↑);;
          ktr_s x_)) →
      (∀ ret, help_rel (⇓cris (ktr_s ret)) (⇓cris (ktr_t ret)) None) →
      help_rel itr_s itr_t (Some (inl (rid, Done ret, None)))
  | help_rel_helpee_pend N reqid arg itr_s itr_t k_s k_t :
      itr_s = helpee_inprogress_s N arg k_s →
      itr_t = helpee_pend_t N reqid arg k_t →
      (∀ ret, help_rel (⇓cris (k_s ret)) (⇓cris (k_t ret)) None) →
      help_rel itr_s itr_t (Some (inl (reqid, Pend N arg, None)))
  | help_rel_call itr_s itr_t ktr_t ktr_s ctx rs_s rs_t fn arg :
      funid fn ∈ dom (Mod.fnsems (HelpingOn.t mn jobs)) ∪ dom (Mod.fnsems SchI.t) →
      Mod.wf ((HelpingOn.t mn jobs ★ CFilter.filter msk SchI.t) ★ ctx) →
      itr_s = bd <- (prog_s ctx rs_s fn)?;; x <- bd arg;; ⇓cris (ktr_s x) →
      itr_t = bd <- (prog_t ctx rs_t fn)?;; x <- bd arg;; ⇓cris (ktr_t x) →
      (∀ ret, help_rel (⇓cris (ktr_s ret)) (⇓cris (ktr_t ret)) None) →
      help_rel itr_s itr_t None
  | help_rel_inner_spawn itr_s itr_t (arg : Any.t) ktr_s ktr_t :
      itr_t = inner_spawn_pend arg ktr_t →
      itr_s = inner_spawn_pend arg ktr_s →
      (∀ ret, help_rel (⇓cris (ktr_s ret)) (⇓cris (ktr_t ret)) None) →
      help_rel itr_s itr_t None
  | help_rel_join itr_s itr_t (arg : Any.t) ktr_s ktr_t tid :
      itr_t = join_pend arg tid ktr_t →
      itr_s = join_pend arg tid ktr_s →
      (∀ ret, help_rel (⇓cris (ktr_s ret)) (⇓cris (ktr_t ret)) None) →
      help_rel itr_s itr_t None
  | help_rel_terminate itr_s itr_t ktr_s ktr_t :
      itr_s =
        (⇓cris (x <- ⇓sb(CFilter.msk_filter_out msk (msk_real (msk_scp SchI.scopes msk_true)))
          (⇓smod(∅) (x_ <- Sch.terminate;; Ret x_↑));; ktr_s x)) →
      itr_t =
        (⇓cris (x <- ⇓sb(CFilter.msk_filter_out msk (msk_real (msk_scp SchI.scopes msk_true)))
          (⇓smod(∅) (x_ <- Sch.terminate;; Ret x_↑));; ktr_t x)) →
      (∀ ret, help_rel (⇓cris (ktr_s ret)) (⇓cris (ktr_t ret)) None) →
      help_rel itr_s itr_t None.


  Lemma gsim_Yield_tgt (Priv : iProp Σ) (N : option namespace)
      r g RR p_s p_t tid_s tid_t tp_s tp_t
      scp (k_s k_t : itree crisE _) ctx st_ctx rs_t rs_s
      (ths : list (nat * option SAny.t))
      (mtid_s mtid_t : nat)
      (res_t res_s : Σ) :
    Mod.wf (mod_src ★ ctx) →
    Mod.wf (mod_tgt ★ ctx) →
    let st_src (ths : list (nat * option SAny.t)) (mtid_s : nat) :=
      (union_with uwnd
        {[SchI.v_ths # ths↑; SchI.v_tid # mtid_s↑]}
          st_ctx) in
    let st_tgt (ths : list (nat * option SAny.t)) (mtid_t : nat) :=
      (union_with uwnd
        {[SchI.v_ths # ths↑; SchI.v_tid # mtid_t↑]}
        st_ctx) in
    map_Forall (const is_Some) (st_src ths mtid_s) →
    map_Forall (const is_Some) (st_tgt ths mtid_t) →
    ✓ res_s →
    (Own res_s ⊢ |==> Own res_t ∗ Priv) →
    tp_s !! tid_s = Some (⇓cris ((⇓sb(msk_scp scp msk_true) (⇓smod(∅) (𝒴@{N})));;; k_s)) →
    tp_t !! tid_t = Some (⇓cris ((⇓sb(msk_scp scp msk_true) (⇓smod(∅) (𝒴@{N})));;; k_t)) →
    gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR smj_top smj_top
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE (prog_s ctx rs_s))
          (tid_s, <[tid_s:=⇓cris (⇓sb( msk_scp scp msk_true) (⇓smod(∅) 𝒴@{N});;; k_s)]> tp_s))
        (st_src ths mtid_s, res_s))
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE (prog_t ctx rs_t))
          (tid_t, <[tid_t:=⇓cris k_t]> tp_t))
        (st_tgt ths mtid_t, res_t)) →
    (ths.*1 !! mtid_s = Some tid_s →
      ths.*1 !! mtid_t = Some tid_t ∧
      ∀ mtid_t1 stid_t1, ths.*1 !! mtid_t1 = Some stid_t1 →
        ∃ mtid_s1 stid_s1, ths.*1 !! mtid_s1 = Some stid_s1 ∧
        ∀ (res_t2 res_s2 : Σ),
        ✓ res_s2 →
        (Own res_s2 ⊢ |==> Own res_t2 ∗ Priv) →
        gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR smj_top smj_top
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE (prog_s ctx rs_s))
            (stid_s1, <[tid_s:=⇓cris (tau;;
              ⇓sb(msk_scp scp msk_true)
                (option_Assume N;;;
                 ⇓smod(∅) 𝒴@{N});;; k_s)]> tp_s))
          (st_src ths mtid_s1, res_s2))
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE (prog_t ctx rs_t))
            (stid_t1, <[tid_t:=⇓cris (tau;;
              ⇓sb(msk_scp scp msk_true)
                (option_Assume N;;;
                 ⇓smod(∅) 𝒴@{N});;; k_t)]> tp_t))
          (st_tgt ths mtid_t1, res_t2))) →
    gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE (prog_s ctx rs_s))
          (tid_s, tp_s))
        (st_src ths mtid_s, res_s))
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE (prog_t ctx rs_t))
          (tid_t, tp_t))
        (st_tgt ths mtid_t, res_t)).
  Proof using H.
    intros Hwfsrc Hwftgt. revert res_t res_s p_s p_t tp_s tp_t.
    gcofix CIH.
    intros res_t res_s p_s p_t tp_s tp_t Hst1 Hst2 Hres Hr
      Htids Htidt ? Hk2.
    eapply lookup_lt_Some in Htids as ?, Htidt as ?.
    revert Htids Htidt; rewrite yield_namespace_unfold; intros Htids Htidt.
    eapply gsim_tau_tgt; [rewrite Htidt; do 2 f_equal; hnorm_itr|].
    eapply gsim_tau_src; [rewrite Htids; do 2 f_equal; hnorm_itr|].
    eapply gsim_Choose_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
    intros [[|]|]; rewrite list_insert_insert; cycle 1.
    { ghcNormT.
      eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      exists (Some false). ghcNormS. rewrite list_insert_insert.
      zprogress. gbase.
      eapply CIH; (try by lookup_tac); auto; rewrite ?list_insert_insert //.
    }
    { ghcNormT.
      eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      exists (Some false). ghcNormS. rewrite list_insert_insert.
      eapply gpaco7_mon; eauto.
    }
    eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
    exists (Some true). rewrite list_insert_insert. ired.
    ghcNormS. ghcNormT.
    rewrite option_Guarantee_sred.
    eapply gsim_option_Guarantee_both_view;
      [lookup_tac; s; do 2 f_equal
      |lookup_tac; s; do 2 f_equal
      |auto|eauto|].
    intros res_t1 res_s1 Hres_s1 Hr1.
    simpl. rewrite ?list_insert_insert.

    ghcNormS; ghcNormT; rewrite lookup_empty.
    eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
    ghcNormS. rewrite list_insert_insert.
    eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
    ghcNormT. rewrite list_insert_insert.

    eapply gsim_Call_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
    rewrite list_insert_insert. ghcNormS.
    eapply gsim_Call_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
    rewrite list_insert_insert. ghcNormT.

    rewrite prog_s_yield // prog_t_yield //=.
    rewrite /yield /SchI.yield /cfunU; ired; rewrite -?interpV_bind.
    eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
    rewrite list_insert_insert.
    eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
    rewrite list_insert_insert.

    eapply gsim_SGet_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
    rewrite list_insert_insert.
    subst st_tgt; match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst2 end.
    eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
    rewrite list_insert_insert.

    ghcNormS.
    eapply gsim_SGet_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
    rewrite list_insert_insert.
    assert (Hths_src :
      (({[SchI.v_ths # ths↑; SchI.v_tid # mtid_s↑]}) +# st_ctx) !! SchI.v_ths =
        Some (Some (ths↑))).
    { eapply lookup_union_with_l; [exact Hst1|]. rewrite lookup_insert //. }
    rewrite Hths_src.
    eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
    rewrite list_insert_insert.

    eapply gsim_GetTid_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
    rewrite list_insert_insert. ghcNormS.
    eapply gsim_GetTid_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
    rewrite list_insert_insert. ghcNormT.

    eapply gsim_SGet_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
    rewrite list_insert_insert.
    match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst2 end.

    eapply gsim_SGet_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
    rewrite list_insert_insert.
    assert (Htid_src :
      (({[SchI.v_ths # ths↑; SchI.v_tid # mtid_s↑]}) +# st_ctx) !! SchI.v_tid =
        Some (Some (mtid_s↑))).
    { eapply lookup_union_with_l; [exact Hst1|]. solve_map_lookup_symbolic Hst1. }
    rewrite Htid_src.
    ghcNormS. ghcNormT.

    destruct (ths !! mtid_s) as [[? ?]|] eqn : HtcSimpl; rewrite HtcSimpl; cycle 1.
    { ghcNormS.
      eapply gsim_Take_src with (X := False);
        [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss.
    }
    ghcNormS. case_decide; subst; cycle 1.
    { ghcNormS.
      eapply gsim_Take_src with (X := False);
        [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss.
    }

    hexploit Hk2; [rewrite list_lookup_fmap HtcSimpl //|]; clear Hk2.
    intros [[[? ?] [Hthst ?]]%list_lookup_fmap_Some Hk2]; rewrite Hthst /=; clarify; s.
    ghcNormT. case_decide; ss. ghcNormT. rewrite /choose_index. ghcNormS.

    eapply gsim_Choose_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
    intros [[mtid_t1 stid_t1] Hmtid_t1]; rewrite list_insert_insert. ghcNormT; ss.

    hexploit (Hk2 mtid_t1 stid_t1); eauto. clear Hk2; intros [mtid_s1 [stid_s1 [Hmtid_s1 Hk2]]].
    eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
    eexists (exist _ (mtid_s1, stid_s1) Hmtid_s1); rewrite list_insert_insert. ghcNormS.

    eapply gsim_SPut_tgt; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
    rewrite list_insert_insert. ghcNormT.
    eapply gsim_SPut_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
    rewrite list_insert_insert. ghcNormS.
    eapply gsim_tau_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
    rewrite list_insert_insert. ghcNormS.
    eapply gsim_tau_tgt; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
    rewrite list_insert_insert. ghcNormT.

    eapply gsim_Yield_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
    rewrite list_insert_insert. ghcNormS.
    eapply gsim_Yield_tgt; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
    rewrite list_insert_insert. ghcNormT. ired.
    assert (Hvtid_src : is_Some
      (({[SchI.v_ths # ths↑; SchI.v_tid # mtid_s↑]}
        : gmap key (option Any.t)) !! SchI.v_tid)).
    { rewrite lookup_insert_ne ?lookup_insert //; ii; clarify. }
    assert (Hstate_src :
      <[SchI.v_tid := Some (mtid_s1↑)]> (st_src ths mtid_s) =
        st_src ths mtid_s1).
    { unfold st_src.
      rewrite (insert_union_with_l' _ _ _ _ Hst1 Hvtid_src).
      rewrite insert_commute; [rewrite insert_insert //|ii; clarify]. }
    assert (Hvtid_tgt : is_Some
      (({[SchI.v_ths # ths↑; SchI.v_tid # mtid_t↑]}
        : gmap key (option Any.t)) !! SchI.v_tid)).
    { rewrite lookup_insert_ne ?lookup_insert //; ii; clarify. }
    assert (Hstate_tgt :
      <[SchI.v_tid := Some (mtid_t1↑)]>
        (({[SchI.v_ths # ths↑; SchI.v_tid # mtid_t↑]}) +# st_ctx) =
        ({[SchI.v_ths # ths↑; SchI.v_tid # mtid_t1↑]}) +# st_ctx).
    { rewrite (insert_union_with_l' _ _ _ _ Hst2 Hvtid_tgt).
      rewrite (insert_commute _ SchI.v_tid SchI.v_ths).
      2: { ii; clarify. }
      rewrite insert_insert. reflexivity. }
    rewrite Hstate_src Hstate_tgt.
    eapply gpaco7_mon; [greplace_s; [|greplace_t]| | ]; cycle 2.
    { eapply (Hk2 res_t1 res_s1); eauto. }
    { eauto. }
    { eauto. }
    { repeat f_equal; ss. rewrite SRed.bind option_Assume_sred //. }
    { repeat f_equal; ss. rewrite SRed.bind option_Assume_sred //. }
  (*SLOW*)Qed.

  Lemma gsim_option_Assume_Guarantee_src (N : option namespace)
      r g RR p_s p_t st_s prog_s tid_s tp_s
      scp k_s (res : Σ) itr_t :
    tp_s !! tid_s =
      Some (⇓cris (x <- ⇓sb(msk_scp scp msk_true) (⇓smod(∅) (option_Assume N;;; 𝒴@{N}));; k_s x)) →
    (gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR smj_top p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s)
        (tid_s, <[tid_s := ⇓cris (
          trigger (Call SchHdr.yield.1 (tt↑));;;
          x <- ⇓sb(msk_scp scp msk_true) (option_Assume (N);;; ⇓smod(∅) 𝒴@{N});; k_s x)]> tp_s))
        (st_s, res))
      itr_t) →
    gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) (st_s, res))
      itr_t.
  Proof using.
    intros Htid_s Hk.
    eapply lookup_lt_Some in Htid_s as Hlen_s.
    destruct N as [N | ]; cycle 1.
    { rewrite SRed.bind SRed.ret SBRed.bind SBRed.ret bind_ret_l
        yield_namespace_unfold /= in Htid_s.
      eapply gsim_tau_src; [rewrite Htid_s; do 2 f_equal; hnorm_itr|].
      eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]. exists (Some true).
      rewrite list_insert_insert.
      eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      rewrite list_insert_insert. rewrite lookup_empty. ghcNormS.
      greplace_s; last (eapply Hk; eauto).
      repeat f_equal. extensionalities. grind.
    }
    rewrite yield_namespace_unfold in Htid_s.
    eapply gsim_Assume_src; [rewrite Htid_s; do 2 f_equal; s; hnorm_itr|].
    intros res2 [? Hres2]. ghcNormS.
    eapply gsim_tau_src; [lookup_tac; do 2 f_equal; hnorm_itr|]. rewrite list_insert_insert.
    eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
    exists (Some true). rewrite list_insert_insert. ghcNormS.
    eapply gsim_Guarantee_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
    exists res; splits; auto.
    { eapply (Own_wand_valid res2); [rewrite Hres2; iIntros "> [? $] //"|auto]. }
    clear dependent res2.
    rewrite list_insert_insert. ghcNormS. rewrite lookup_empty.
    eapply gsim_tau_src; [lookup_tac; do 2 f_equal; hnorm_itr|]. rewrite list_insert_insert.
    greplace_s; last (eapply Hk; eauto).
    repeat f_equal.
    repeat (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
  Qed.



  Lemma helping_onoff_correct :
    Helping.exports mn ⊆ msk →
    help_erasure_init_cond ⊢ ctx_refines mod_tgt mod_src.
  Proof using H.
    intros Hmsk. iIntros "Hauth %ctx".
    iApply (gsim_closed_adequacy (mod_tgt ★ ctx) (mod_src ★ ctx)).
    iApply (gsim_mod_intro (mod_src ★ ctx) (mod_tgt ★ ctx)
      help_erasure_init_cond); last done.
    intros WF; split; first by apply wf_src.

    intros rt rs VALID_rs SPLIT.
    assert (Hinit : Own rs ⊢ |==> Own rt ∗ help_erasure_init_cond).
    { iIntros "Hrs". iDestruct (SPLIT with "Hrs") as "[Hrt [Hauth _]]".
      iModIntro. iFrame. }
    pose proof (res_rel_init rt rs VALID_rs Hinit) as Hres0.
    clear SPLIT Hinit.
    rewrite /LMod.compile /ITree.map /LModTr.trans /LModTr.interp_callE /=.
    destruct (Mod.fnsems ctx !! entry) as [[[mskctx bd]|]|] eqn : FIND; cycle 1.
    { simpl_map. ginit. gstep_s. ss. }
    { rewrite {1}/Mod.fnsems {1}/Mod.add !lookup_fmap lookup_omap lookup_union_with FIND
        lookup_fnsems_None //.
      ginit. gstep_s. ss.
    }

    simpl_map; s. ired.
    rewrite /SB.sandbox_body /ModTr.trans_fnsem /ModTr.trans /=.
    ginit. guclo bindC_spec. econs; cycle 1.
    { instantiate (1:=λ r_s r_t, r_s.2 = r_t.2). ii; gstep; ss. subst; econs; econs; ss. }

    (* Start coinduction *)
    rewrite /HelpingOff.t /HelpingOn.t /SchI.t; ss.
    rewrite left_id_L.
    set (st_src := union_with _ _ _) at 1.
    set (st_tgt := union_with _ _ _).
    set (tp_src := (0, [_])) at 1.
    set (tp_tgt := (0, [_])).
    cut
      (∃ (tl : list (itree (lmodE Σ) Any.t * itree (lmodE Σ) Any.t *
            option ((nat * help_state * option (SAny.t * option namespace)) +
              (nat * (SAny.t * option namespace)))))
          (mtid stid : nat) (ths : list (nat * option SAny.t)) st_ctx
          (reqmap : gmap nat help_state),
        st_src = {[SchI.v_ths # ths↑; SchI.SchI.v_tid # mtid↑]} +# st_ctx ∧
        st_tgt = {[SchI.v_ths # ths↑; SchI.SchI.v_tid # mtid↑]} +# st_ctx ∧
        tp_src = (stid, (fst ∘ fst <$> tl)) ∧ tp_tgt = (stid, (snd ∘ fst <$> tl)) ∧
        reqmap_rel tl reqmap ∧
        (∀ i itr_s itr_t no, tl !! i = Some (itr_s, itr_t, no) →
          help_rel itr_s itr_t no ∧
          match no with
          | Some (inl (_, Pend _ _, _)) | Some (inl (_, InProgress, _)) =>
              ∃ mtid_i ro_i, ths !! mtid_i = Some (i, ro_i)
          | _ => True
          end) ∧
        map_Forall (const is_Some) st_src ∧ map_Forall (const is_Some) st_tgt ∧
        res_rel reqmap rt rs); cycle 1.
    { eexists [(_ ,_, None)], _, _, _, _, ∅.
      esplits; subst st_src st_tgt; ss; repeat f_equal; ss.
      { rr; ss; split; first econs.
        splits.
        { exists (const None); splits; [intros ?? [? [? ?]]|intros ?|intros ???]; ss.
          destruct stid; ss; split; intros []; ss.
        }
        { intros ????; rewrite list_lookup_singleton_Some; i; des; clarify. }
        { intros ???; clarify. }
      }
      { intros ???? [-> In]%list_lookup_singleton_Some; clarify; split; last done.
        { ides (bd ()↑).
          { by rewrite ?SBRed.ret ?interpV_ret; econs. }
          { eapply (help_rel_eq _ _ (λ x, Ret x) (λ x, Ret x)); eauto; try by grind.
            { eapply Mod.add_wf_inv in WF as [? [? [? [? [Hnd ?]]%NoDup_app]]].
              hexploit (Mod.well_scoped_fns ctx); rewrite map_Forall_lookup => /(_ entry (mskctx, bd)).
              rewrite lookup_omap FIND => /(_ eq_refl) [Hput Hget]; split.
              { intros ? ?%Hget; rewrite elem_of_app; ss; ii; exfalso; eapply Hnd; eauto.
                rewrite sorting.merge_sort_Permutation; rewrite elem_of_cons; des; [right|left]; set_solver. }
              { intros ? ? ?%Hput; rewrite elem_of_app; ss; ii; exfalso; eapply Hnd; eauto.
                rewrite sorting.merge_sort_Permutation; rewrite elem_of_cons; des; [right|left]; set_solver.
              }
            }
            { by i; rewrite ?interpV_ret; econs. }
          }
          { eapply (help_rel_eq _ _ (λ x, Ret x) (λ x, Ret x)); eauto; try by grind.
            { eapply Mod.add_wf_inv in WF as [? [? [? [? [Hnd ?]]%NoDup_app]]].
              hexploit (Mod.well_scoped_fns ctx); rewrite map_Forall_lookup => /(_ entry (mskctx, bd)).
              rewrite lookup_omap FIND => /(_ eq_refl) [Hput Hget]; split.
              { intros ? ?%Hget; rewrite elem_of_app; ss; ii; exfalso; eapply Hnd; eauto.
                rewrite sorting.merge_sort_Permutation; rewrite elem_of_cons; des; [right|left]; set_solver. }
              { intros ? ? ?%Hput; rewrite elem_of_app; ss; ii; exfalso; eapply Hnd; eauto.
                rewrite sorting.merge_sort_Permutation; rewrite elem_of_cons; des; [right|left]; set_solver.
              }
            }
            { by i; rewrite ?interpV_ret; econs. }
          }
        }
      }
      { apply wf_src in WF; inv WF; hexploit (Mod.nodup_init); eauto. }
      { inv WF; hexploit (Mod.nodup_init); eauto. }
    }
    clear VALID_rs Hres0.
    clearbody st_src st_tgt tp_src tp_tgt.
    generalize smj_bot at 1 as f_s. generalize smj_bot as f_t.
    clear FIND mskctx bd.
    revert_until WF.
    gcofix CIH.
    intros rt rs st_s st_t tp_s tp_t f_t f_s.
    intros [tl [mtid [stid [ths [st_ctx [reqmap temp]]]]]].
    destruct temp as [-> [-> [-> [-> [Hreqmap [Hlookup [Hst1 [Hst2 Hres]]]]]]]].
    pose proof Hres as [Hrs Hr].

    destruct ((fst ∘ fst <$> tl) !! stid) as [i|] eqn : Htid; cycle 1.
    { giter_s. s. rewrite Htid. gstep_s. gcNormS. gstep_s. ss. }

    apply list_lookup_fmap_inv in Htid as [[[itr_src itr_tgt] no] [-> Htid]]; s.
    destruct no as [[[[rid [N arg | | ret]] no]|no]|].

    { (* 1. pending client *)
      apply lookup_lt_Some in Htid as Hstid_cur_length.
      pose proof Htid as Htid'.
      apply Hlookup in Htid' as [Hcase _]. inv Hcase.
      eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].

      eapply gsim_option_Assume_both_view;
        [lookup_tac; do 2 f_equal; hnorm_itr
        |lookup_tac; do 2 f_equal; hnorm_itr
        |auto|eauto|].
      intros rt1 rs1 Hrs1 Hr1.
      rewrite !list_insert_insert. ghcNormT. ghcNormS.

      eapply gsim_Yield_tgt; (eauto using wf_src); (try by lookup_tac; s; do 2 f_equal; hnorm_itr).
      { (* 2.1. do the job *)
        rewrite !list_insert_insert. ghcNormT.

        (* Pend -> InProgress *)
        rewrite /HelpingOn.try_run.
        eapply gsim_Choose_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        intros [ret0|]; rewrite list_insert_insert; ghcNormT.
        { eapply gsim_Guarantee_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          intros rt2 [Hrt2 Hupd].
          pose proof (res_rel_observe reqmap rt1 rs1 rid ret0 rt2
            (conj Hrs1 Hr1) Hupd) as [Hdone _].
          eapply reqmap_rel_Some in Hreqmap as Hpend; eauto. congruence.
        }
        eapply gsim_Choose_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        intros N2; rewrite list_insert_insert; ghcNormT.
        eapply gsim_Choose_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        intros arg2; rewrite list_insert_insert; ghcNormT.
        eapply gsim_Guarantee_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        intros rt2 [Hrt2 Hupd].
        pose proof (res_rel_claim reqmap rt1 rs1 rid N2 arg2 rt2
          (conj Hrs1 Hr1) Hupd) as [Hpend Hres2].
        eapply reqmap_rel_Some in Hreqmap as Hpending; eauto.
        rewrite Hpending in Hpend.
        injection Hpend as HN Harg. subst N2. subst arg2.
        rewrite list_insert_insert. ghcNormT.
        pose proof Hres2 as [Hrs2 Hr2].

        generalize arg at 1 2.
        revert Hrs2 Hr2; generalize rt2 rs1. gcofix CIH2.
        clear dependent rt1 rt2 rs1.
        intros rt1 rs1 Hrs1 Hr1 arg1. zprogress.
        rewrite unfold_iter.
        eapply gsim_Yield_tgt; eauto using wf_src; (try by lookup_tac; s; do 2 f_equal; hnorm_itr).
        { (* direct job execution *)
          rewrite !list_insert_insert. ghcNormT.
          rewrite {1}yield_namespace_unfold.
          eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
          rewrite list_insert_insert.
          eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s. exists None.
          rewrite list_insert_insert. ghcNormS.
          zprogress with smj_bot smj_bot _ _.
          eapply gsim_jobs_both_view; rewrite ?length_fmap //.
          intros rt2 rs2 [j2|ret1] Hrs2 Hr2.
          { (* repeat *)
            eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
            eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
            rewrite !list_insert_insert.
            rewrite {1}unfold_iter. ghcNormS.
            greplace_s; cycle 1.
            { gbase. eapply (CIH2 rt2 rs2 Hrs2 Hr2 j2); eauto. }
            repeat f_equal; grind.
          }

          (* job done *)
          clear CIH2.
          rewrite {1}yield_namespace_unfold.
          eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
          rewrite list_insert_insert.
          eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s. exists None.
          rewrite list_insert_insert. ghcNormS.

          ghcNormT.
          assert (Hip : (<[rid:=InProgress]> reqmap) !! rid = Some InProgress)
            by apply lookup_insert.
          pose proof (res_rel_publish (<[rid:=InProgress]> reqmap) rt2 rs2 rid ret1
            Hip (conj Hrs2 Hr2)) as [rt3 [Hrt3 [Hupd3 Hres3]]].
          eapply gsim_Assume_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          exists rt3; splits; [done|exact Hupd3|].
          rewrite list_insert_insert. ghcNormT.

          gbase. eapply (CIH rt3 rs2); try by des; eauto.
          eexists (<[stid := (_, _, None)]> tl), _, _, _, _,
            (<[rid:=Done ret1]> reqmap); ss; esplits; eauto.
          { rewrite list_fmap_insert //=. }
          { rewrite list_fmap_insert //=. }
          { eapply reqmap_rel_done_2; eauto. }
          { intros i; destruct (decide (i = stid)); subst; cycle 1.
            { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
            { rewrite list_lookup_insert; ii; clarify. }
          }
          { rewrite insert_insert in Hres3. exact Hres3. }
        }

        (* freeze during job execution *)
        clear CIH2.
        intros Hmtid; split; first done.
        intros mtidn_t stidn_t Hmtidn_t; exists mtidn_t, stidn_t; split; first done.
        intros rt2 rs2 Hrs2 Hr2.
        rewrite !list_insert_insert. ghcNormS; ghcNormT.
        eapply map_Forall_insert_union_with with (k:=SchI.v_tid) in Hst1 as Hsts2; revert Hsts2.
        repeat match goal with
        | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
          state_insert_simpl k1 v1 H
        end.
        intros Hsts2.
        pose proof Hsts2 as Hstt2.
        zprogress. gbase. eapply (CIH rt2 rs2); eauto.
        eexists (<[stid := (_, _, Some (inl (rid, InProgress, None)))]> tl),
          _, _, _, _, (<[rid:=InProgress]> reqmap); esplits; eauto.
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { eapply reqmap_rel_pend; eauto. }
        { intros i; destruct (decide (i = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify. split.
            { eapply (help_rel_job_loop); eauto.
              { rewrite /helpee_inprogress_s. f_equal.
                repeat (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
              }
              { rewrite /helpee_inprogress_t. f_equal.
                repeat (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
              }
            }
            apply list_lookup_fmap_Some in Hmtid as [[? ?] [? ?]]; clarify.
            esplits; eauto.
          }
        }
        { exact (conj Hrs2 Hr2). }
      }
      (* 2.2. freeze *)
      intros Hmtid; split; first done.
      intros mtidn_t stidn_t Hmtidn_t; exists mtidn_t, stidn_t; split; first done.
      intros rt2 rs2 Hrs2 Hr2.
      rewrite !list_insert_insert.
      eapply map_Forall_insert_union_with with (k:=SchI.v_tid) in Hst1 as Hsts; revert Hsts.
      repeat match goal with
      | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
        state_insert_simpl k1 v1 H
      end.
      intros Hsts.
      pose proof Hsts as Hstt.
      zprogress. gbase. eapply (CIH rt2 rs2); eauto.
      eexists (<[stid := (_, _, Some (inl (rid, Pend N arg, None)))]> tl),
        _, _, _, _, reqmap; esplits; eauto.
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      { eapply reqmap_rel_id; eauto. }
      { intros i; destruct (decide (i = stid)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify. split.
          { eapply (help_rel_helpee_pend); eauto.
            { rewrite /helpee_inprogress_s. f_equal.
              repeat (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
            }
            { rewrite /helpee_pend_t. f_equal.
              repeat (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
            }
          }
          apply list_lookup_fmap_Some in Hmtid as [[? ?] [? ?]]; clarify.
          esplits; eauto.
        }
      }
      { exact (conj Hrs2 Hr2). }
    }

    { (* 2. InProgress client *)
      eapply Hlookup in Htid as Htid'; destruct Htid' as [Hrel Hex].
      eapply lookup_lt_Some in Htid as Htidlen.
      inv Hrel; ss.
      { (* 2.1. self job *)
        eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        eapply gsim_option_Assume_both_view;
          [lookup_tac; do 2 f_equal; hnorm_itr
          |lookup_tac; do 2 f_equal; hnorm_itr
          |auto|eauto|].
        intros rt1 rs1 Hrs1 Hr1.
        rewrite !list_insert_insert. ghcNormT. ghcNormS.

        generalize arg. revert Hrs1 Hr1. generalize rt1 rs1.
        gcofix CIH2.
        clear dependent rt1 rs1.
        intros rt1 rs1 Hrs1 Hr1 arg2.
        eapply gsim_Yield_tgt; (eauto using wf_src);
            (try by lookup_tac; s; do 2 f_equal; hnorm_itr); cycle 1.
        { (* 2.1.1. re-yield *)
          clear CIH2.
          intros; split; first done.
          intros mtidn_t stidn_t Hmtidn_t; exists mtidn_t, stidn_t; split; first done.
          intros rt2 rs2 Hrs2 Hr2.
          rewrite !list_insert_insert.
          eapply (map_Forall_insert_union_with _ _ SchI.v_tid) in Hst1 as Hst1'; revert Hst1'.
          repeat match goal with
          | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
            state_insert_simpl k1 v1 Hst1
          end.
          intros Hst1'; eauto.

          pose proof Hst1' as Hst2'.

          zprogress. gbase. eapply (CIH rt2 rs2); try by des.

          eexists (<[stid := (_, _, _)]> tl), _, _, _, _, reqmap;
            ss; esplits; eauto.
          { rewrite list_fmap_insert //=. }
          { rewrite list_fmap_insert //=. }
          { eapply reqmap_rel_id; eauto. }
          { intros i; destruct (decide (i = stid)); subst; cycle 1.
            { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
            { rewrite list_lookup_insert; ii; clarify.
              split; ss. esplits; eauto.
              eapply help_rel_job_loop; eauto.
              { rewrite /helpee_inprogress_s; repeat f_equal; grind.
                repeat (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
              }
              { rewrite /helpee_inprogress_t; repeat f_equal; grind.
                repeat (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
              }
            }
          }
          { exact (conj Hrs2 Hr2). }
        }

        (* 2.1.2. do some job *)
        rewrite !list_insert_insert.
        rewrite {1}yield_namespace_unfold.
        eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        rewrite list_insert_insert.
        eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        exists None. rewrite list_insert_insert. ghcNormS. ghcNormT.

        zprogress with smj_bot smj_bot _ _.
        eapply gsim_jobs_both_view;
          try by rewrite ?length_insert ?length_fmap.
        intros rt2 rs2 [arg1|ret1] Hrs2 Hr2.
        { (* repeat *)
          eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          rewrite !list_insert_insert.
          rewrite {1 2}unfold_iter. ghcNormS. ghcNormT.
          greplace_s; cycle 1.
          { greplace_t; cycle 1. 
            { gbase. eapply (CIH2 rt2 rs2 Hrs2 Hr2 arg1); eauto. }
            repeat f_equal; grind.
          }
          repeat f_equal; grind.
        }
        (* done *)
        clear CIH2.
        assert (Hip : reqmap !! rid = Some InProgress).
        { eapply reqmap_rel_Some; eauto. }
        pose proof (res_rel_publish reqmap rt2 rs2 rid ret1 Hip
          (conj Hrs2 Hr2)) as [rt3 [Hrt3 [Hupd3 Hres3]]].
        eapply gsim_Assume_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        exists rt3; splits; [done|exact Hupd3|].
        rewrite list_insert_insert. ghcNormT.

        rewrite {1}yield_namespace_unfold.
        eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        rewrite list_insert_insert.
        eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        exists None. rewrite list_insert_insert. ghcNormS.

        (* by coinduction *)
        zprogress. gbase. eapply (CIH rt3 rs2); eauto.
        eexists (<[stid := (⇓cris (ktr_s _), ⇓cris (ktr_t _), None)]> tl),
          _, _, _, _, (<[rid:=Done ret1]> reqmap).
        esplits; try match goal with | |- context[map_Forall _] => fail | |- _ => eauto end.
        { rewrite ?list_fmap_insert //=. }
        { rewrite ?list_fmap_insert //=. }
        { eapply reqmap_rel_done_2; eauto. }
        { intros i; destruct (decide (i = stid)).
          { subst; intros ??? Hin; rewrite list_lookup_insert in Hin; ss; clarify. }
          intros ??? Hin; rewrite ?list_lookup_insert_ne // in Hin; eapply Hlookup; eauto.
        }
      }

      (* 2.2. being helped *)
      eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      eapply gsim_option_Assume_both_view;
        [lookup_tac; do 2 f_equal; hnorm_itr
        |lookup_tac; do 2 f_equal; hnorm_itr
        |auto|eauto|].
      intros rt1 rs1 Hrs1 Hr1.
      rewrite !list_insert_insert. ghcNormT. ghcNormS.

      eapply gsim_Yield_tgt; (eauto using wf_src); (try by lookup_tac; s; do 2 f_equal; hnorm_itr);
        cycle 1.
      { (* 2.1.1. re-yield *)
        intros; split; first done.
        intros mtidn_t stidn_t Hmtidn_t; exists mtidn_t, stidn_t; split; first done.
        intros rt2 rs2 Hrs2 Hr2.
        rewrite !list_insert_insert.
        eapply (map_Forall_insert_union_with _ _ SchI.v_tid) in Hst1 as Hst1'; revert Hst1'.
        repeat match goal with
        | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
          state_insert_simpl k1 v1 Hst1
        end.
        intros Hst1'; eauto.

        pose proof Hst1' as Hst2'.

        zprogress. gbase. eapply (CIH rt2 rs2); try by des.

        eexists (<[stid := (_, _, _)]> tl), _, _, _, _, reqmap;
          ss; esplits; eauto.
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { eapply reqmap_rel_id; eauto. }
        { intros i; destruct (decide (i = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify.
            split; ss. esplits; eauto.
            eapply (help_rel_helpee_inprogress arg jobarg N); eauto.
            { rewrite /helpee_inprogress_s; repeat f_equal; grind.
              repeat (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
            }
            { rewrite /helpee_pend_t; repeat f_equal; grind.
              repeat (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
            }
          }
        }
        { exact (conj Hrs2 Hr2). }
      }
      (* 2.2.2. triggerNB *)
      rewrite !list_insert_insert. ghcNormT.
      rewrite /HelpingOn.try_run.
      assert (Hip : reqmap !! rid = Some InProgress).
      { eapply reqmap_rel_Some; eauto. }
      eapply gsim_Choose_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      intros [ret0|]; rewrite list_insert_insert; ghcNormT.
      { eapply gsim_Guarantee_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        intros rt2 [Hrt2 Hupd].
        pose proof (res_rel_observe reqmap rt1 rs1 rid ret0 rt2
          (conj Hrs1 Hr1) Hupd) as [Hdone _]. congruence.
      }
      eapply gsim_Choose_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      intros N2; rewrite list_insert_insert; ghcNormT.
      eapply gsim_Choose_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      intros arg2; rewrite list_insert_insert; ghcNormT.
      eapply gsim_Guarantee_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      intros rt2 [Hrt2 Hupd].
      pose proof (res_rel_claim reqmap rt1 rs1 rid N2 arg2 rt2
        (conj Hrs1 Hr1) Hupd) as [Hpend _]. congruence.
    }

    { (* 3. Done client *)
      apply lookup_lt_Some in Htid as Hstid_cur_length.
      pose proof Htid as Htid'.
      apply Hlookup in Htid' as [Hcase _]. inv Hcase.
      eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      ghcNormS; ghcNormT. rewrite option_Assume_sred.

      eapply gsim_option_Assume_both_view;
          [lookup_tac; do 2 f_equal
          |lookup_tac; do 2 f_equal
          |auto|eauto|].
      intros rt1 rs1 Hrs1 Hr1.
      rewrite !list_insert_insert. ghcNormT. ghcNormS.

      eapply gsim_Yield_tgt; (eauto using wf_src);
              (try by lookup_tac; s; do 2 f_equal; hnorm_itr).
      { (* 4.1. return *)
        rewrite !list_insert_insert. ghcNormT.
        rewrite /HelpingOn.try_run.
        assert (Hdone0 : reqmap !! rid = Some (Done ret)).
        { eapply reqmap_rel_Some; eauto. }
        eapply gsim_Choose_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        intros [ret0|]; rewrite list_insert_insert; ghcNormT.
        { eapply gsim_Guarantee_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          intros rt2 [Hrt2 Hupd].
          pose proof (res_rel_observe reqmap rt1 rs1 rid ret0 rt2
            (conj Hrs1 Hr1) Hupd) as [Hdone Hres2].
          rewrite Hdone0 in Hdone. inv Hdone.
          rewrite list_insert_insert. ghcNormT.

          rewrite {1}yield_namespace_unfold.
          eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
          rewrite list_insert_insert.
          eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s. exists None.
          rewrite list_insert_insert. ghcNormS.
          zprogress. gbase. eapply (CIH rt2 rs1); eauto.
          eexists (<[stid := (_, _, None)]> tl), _, _, _, _, reqmap;
            ss; esplits; eauto.
          { rewrite list_fmap_insert //=. }
          { rewrite list_fmap_insert //=. }
          { eapply reqmap_rel_done; eauto. }
          { intros i; destruct (decide (i = stid)); subst; cycle 1.
            { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
            { rewrite list_lookup_insert; ii; clarify. }
          }
        }
        eapply gsim_Choose_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        intros N2; rewrite list_insert_insert; ghcNormT.
        eapply gsim_Choose_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        intros arg2; rewrite list_insert_insert; ghcNormT.
        eapply gsim_Guarantee_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        intros rt2 [Hrt2 Hupd].
        pose proof (res_rel_claim reqmap rt1 rs1 rid N2 arg2 rt2
          (conj Hrs1 Hr1) Hupd) as [Hpend _]. congruence.
      }

      intros; split; first done.
      intros mtidn_t stidn_t Hmtidn_t; exists mtidn_t, stidn_t; split; first done.
      intros rt2 rs2 Hrs2 Hr2.
      rewrite !list_insert_insert.
      eapply (map_Forall_insert_union_with _ _ SchI.v_tid) in Hst1 as Hst1'; revert Hst1'.
      repeat match goal with
      | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
        state_insert_simpl k1 v1 Hst1
      end.
      intros Hst1'; eauto.

      pose proof Hst1' as Hst2'.

      zprogress. gbase. eapply (CIH rt2 rs2); try by des.

      eexists (<[stid := (_, _, _)]> tl), _, _, _, _, reqmap;
        ss; esplits; eauto.
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      { eapply reqmap_rel_id; eauto. }
      { intros i; destruct (decide (i = stid)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify.
          split; ss. esplits; eauto.
          eapply (help_rel_helpee_done N rid arg); eauto.
          { rewrite /helpee_pend_t; repeat f_equal; grind.
            repeat (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
          }
          { rewrite SRed.bind option_Assume_sred. repeat f_equal; grind.
            repeat (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
          }
        }
      }
      { exact (conj Hrs2 Hr2). }
    }

    { (* 4. InProgress helper thread *)
      eapply Hlookup in Htid as Htid'; destruct Htid' as [Hrel Hex].
      eapply lookup_lt_Some in Htid as Htidlen.
      inv Hrel; ss.

      eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].

      pose proof Hreqmap as Hreqmap';
        destruct Hreqmap' as [Hnodup [[f [Hf1 [Hf2 Hf3]]] [Hrel1 Hrel2]]].
      destruct (Hf2 stid) as [_ [stid2 Hfstid2]]; [rewrite list_lookup_fmap Htid; ss; eauto|].
      hexploit (Hf3 stid stid2 rid (arg, N_helpee)); eauto.
      { rewrite list_lookup_fmap Htid //. }
      intros [[[? ?] o] [? Hstid2]]%list_lookup_fmap_inv; ss; subst o.
      hexploit (Hlookup stid2 _ _ _ Hstid2); intros [Hstid2rel [mtid2 [? Hstid2ths]]].
      eapply lookup_lt_Some in Hstid2 as Hstid2len.

      eapply gsim_option_Assume_Guarantee_src; [lookup_tac; do 2 f_equal|].
      { repeat (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind). }

      eapply gsim_Call_src;
        [lookup_tac; s; do 2 f_equal; hnorm_itr|rewrite list_insert_insert].
      rewrite prog_s_yield; auto using wf_src.
      rewrite /yield /SchI.yield /cfunU /fbody_trivial; ired.
      rewrite -interpV_bind.
      eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|rewrite list_insert_insert].
      ghcNormS.

      eapply gsim_SGet_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
      rewrite list_insert_insert.
      match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst1 end.

      eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      rewrite list_insert_insert.
      eapply gsim_GetTid_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
      rewrite list_insert_insert.

      eapply gsim_SGet_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
      rewrite list_insert_insert.
      match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst1 end.
      ghcNormS.

      destruct (_ !! mtid) as [[? ?]|] eqn : Hmtid; ss; cycle 1.
      { ghcNormS.
        eapply gsim_Take_src with (X := False);
          [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss.
      }
      ghcNormS. case_decide; subst; cycle 1.
      { ghcNormS.
        eapply gsim_Take_src with (X := False);
          [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss.
      }
      ghcNormS.

      rewrite /choose_index.
      eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      unshelve eexists.
      { exists (mtid2, stid2). rewrite /= list_lookup_fmap Hstid2ths //. }
      rewrite list_insert_insert. ghcNormS.

      eapply gsim_SPut_src;
        [lookup_tac; s; do 2 f_equal; hnorm_itr|exact Hst1|]; s.
      rewrite list_insert_insert. ghcNormS.
      eapply (map_Forall_insert_union_with _ _ SchI.v_tid) in Hst1 as Hsts; revert Hsts.
      repeat match goal with
      | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
        state_insert_simpl k1 v1 H
      end. intros Hsts.
      eapply gsim_tau_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
      rewrite list_insert_insert. ghcNormS.

      eapply gsim_Yield_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
      rewrite list_insert_insert. ghcNormS.

      inv Hstid2rel.
      eapply gsim_tau_src; auto.
      { rewrite !list_lookup_insert_ne //=.
        { rewrite list_lookup_fmap Hstid2 //=. }
        { ii; clarify. }
        { ii; clarify. }
      }

      (* target proceed for helping *)
      ghcNormT. ghcNormS.
      eapply gsim_option_Assume_both_view;
        [lookup_tac; do 2 f_equal
        |lookup_tac; do 2 f_equal
        |auto|eauto|].
      intros rt1 rs1 Hrs1 Hr1.
      rewrite !list_insert_insert. ghcNormT. ghcNormS.

      generalize arg.
      revert Hrs1 Hr1; generalize rt1 rs1; gcofix CIH2.
      clear dependent rt1 rs1.
      intros rt1 rs1 Hrs1 Hr1 arg2.
      eapply (gsim_Yield_tgt (HelpAuth reqmap ∗ HelpRun reqmap) N_helpee);
        [by apply wf_src|exact WF|exact Hsts|exact Hst2|exact Hrs1|exact Hr1
        |by lookup_tac; s; do 2 f_equal; hnorm_itr
        |by lookup_tac; s; do 2 f_equal; hnorm_itr
        | |]; cycle 1.
      { (* freeze during job execution *)
        clear CIH2.
        intros Hmtid_helpee; split; [rewrite list_lookup_fmap Hmtid //|].
        intros mtidn_t stidn_t Hmtidn_t; exists mtidn_t, stidn_t; split; first done.
        intros rt2 rs2 Hrs2 Hr2.
        rewrite !list_insert_insert.
        assert (Hstn : map_Forall (const is_Some)
          ({[SchI.v_ths # ths↑; SchI.v_tid # mtidn_t↑]} +# st_ctx)).
        { eapply (map_Forall_insert_union_with _ _ SchI.v_tid) in Hsts as temp;
            revert temp.
          repeat match goal with
          | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
            state_insert_simpl k1 v1 Hsts
          end.
          i; eauto.
        }
        zprogress. gbase. eapply (CIH rt2 rs2); eauto; clear CIH.
        eexists (<[stid2 := (_, _, Some (inl (rid, InProgress, Some (arg2, N_helpee))))]>
          (<[stid := (_, _, Some (inr (rid, (arg2, N_helpee))))]> tl)),
          _, _, _, _, reqmap;
          esplits; try refl.
        { rewrite !list_fmap_insert //=. }
        { rewrite !list_fmap_insert //=; f_equal.
          rewrite list_insert_commute //; f_equal.
          rewrite list_insert_id // list_lookup_fmap Hstid2 //=.
          ii; clarify.
        }
        { rewrite list_insert_commute //; [|ii; clarify].
          rewrite -(insert_id reqmap rid InProgress).
          { eapply reqmap_rel_id_2; eauto; rewrite list_lookup_fmap ?Htid ?Hstid2 //=. }
          eapply (Hrel1 stid2); rewrite list_lookup_fmap Hstid2 //.
        }
        { rewrite list_insert_commute //.
          intros i; destruct (decide (i = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=.
            destruct (decide (i = stid2)); subst.
            { rewrite list_lookup_insert //; intros ?; clarify; split.
              { eapply (help_rel_helpee_inprogress arg2 jobarg N_helpee); eauto.
                rewrite /helpee_inprogress_s. f_equal.
                repeat (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
              }
              apply list_lookup_fmap_Some in Hmtid_helpee as [[? ?] [? ?]]; eauto.
            }
            rewrite list_lookup_insert_ne //; eauto.
          }
          intros ???; rewrite list_lookup_insert ?length_insert //=.
          intros ?%Some_inj; clarify; split; last done.
          eapply (help_rel_helper_inprogress arg2 N_helper N_helpee _ _ _ ktr_s); eauto.
          { f_equal. rewrite SRed.bind option_Assume_sred.
            repeat (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
          }
          { rewrite /helper_inprogress_t. f_equal.
            repeat (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
          }
          ii; clarify.
        }
        { exact Hstn. }
        { exact Hstn. }
        { exact (conj Hrs2 Hr2). }
      }

      (* direct job helping *)
      rewrite !list_insert_insert.
      rewrite {1}yield_namespace_unfold.
      eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      rewrite list_insert_insert.
      eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      exists None. rewrite list_insert_insert. ghcNormS. ghcNormT.

      zprogress with smj_bot smj_bot _ _.
      eapply gsim_jobs_both_view;
        try by rewrite ?length_insert ?length_fmap.
      intros rt2 rs2 [arg1|ret1] Hrs2 Hr2.
      { (* repeat *)
        eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        rewrite !list_insert_insert.
        rewrite {1 2}unfold_iter. ghcNormS. ghcNormT.
        greplace_s; cycle 1.
        { greplace_t; cycle 1. 
          { gbase. eapply (CIH2 rt2 rs2 Hrs2 Hr2 arg1); eauto. }
          repeat f_equal; grind.
        }
        repeat f_equal; grind.
      }

      (* done - get back to the helper *)
      clear CIH2. ghcNormS. ghcNormT.

      rewrite {1}yield_namespace_unfold.
      eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      rewrite list_insert_insert. ghcNormS.
      eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      exists (Some true). ghcNormS.
      rewrite list_insert_insert option_Guarantee_sred.

      eapply gsim_option_Guarantee_both_view;
        [lookup_tac; s; do 2 f_equal
        |lookup_tac; s; do 2 f_equal
        |auto|eauto|].
      intros rt3 rs3 Hrs3 Hr3.
      simpl. rewrite ?list_insert_insert.
      ghcNormS; rewrite lookup_empty.
      eapply gsim_tau_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
      rewrite list_insert_insert.

      eapply gsim_Call_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|rewrite list_insert_insert].
      rewrite prog_s_yield; auto using wf_src.
      rewrite /yield /SchI.yield /cfunU /fbody_trivial. rewrite /= bind_ret_l -interpV_bind.
      eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|rewrite list_insert_insert].
      ghcNormS.
      eapply gsim_SGet_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|apply Hsts|]; s.
      rewrite !list_insert_insert.
      match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hsts end.
      eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      rewrite list_insert_insert.
      eapply gsim_GetTid_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
      rewrite list_insert_insert.

      eapply gsim_SGet_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
      rewrite list_insert_insert.
      match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst1 end. ghcNormS.

      rewrite Hstid2ths. ghcNormS. des_ifs_safe; ss. ghcNormS. rewrite /choose_index.
      eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      unshelve eexists.
      { exists (mtid, stid). rewrite list_lookup_fmap Hmtid //=. }
      rewrite list_insert_insert.

      eapply gsim_SPut_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
      rewrite list_insert_insert. ghcNormS.
      eapply (map_Forall_insert_union_with _ _ SchI.v_tid) in Hsts as Hsts2; revert Hsts2.
      repeat match goal with
      | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
        state_insert_simpl k1 v1 H
      end.
      intros Hsts2.
      eapply gsim_tau_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
      rewrite list_insert_insert.
      eapply gsim_Yield_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
      rewrite list_insert_insert. ghcNormS. rewrite list_insert_commute //; [|ii; clarify].

      eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s. ghcNormS.
      ghcNormT. rewrite !option_Assume_sred.
      eapply gsim_option_Assume_both_view;
        [lookup_tac; do 2 f_equal
        |lookup_tac; do 2 f_equal
        |auto|eauto|].
      rewrite !list_insert_insert. intros rt4 rs4 Hrs4 Hr4.

      assert (Hip : reqmap !! rid = Some InProgress).
      { eapply (Hrel1 stid2); rewrite list_lookup_fmap Hstid2 //. }
      pose proof (res_rel_publish reqmap rt4 rs4 rid ret1 Hip
        (conj Hrs4 Hr4)) as [rt5 [Hrt5 [Hupd5 Hres5]]].
      eapply gsim_Assume_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      exists rt5; splits; [done|exact Hupd5|].
      rewrite list_insert_insert. ghcNormT.

      rewrite {1}yield_namespace_unfold.
      eapply gsim_tau_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
      rewrite list_insert_insert.
      eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      exists (None).
      rewrite list_insert_insert. ghcNormS.

      (* by coinduction *)
      zprogress. gbase. eapply (CIH rt5 rs4); eauto.
      set (i_helpee := ⇓cris (tau;; _)).
      eexists (<[stid := (⇓cris (ktr_s () ↑), ⇓cris (ktr_t () ↑), None)]>
        (<[stid2 := (i_helpee, _, Some (inl (rid, Done ret1, None)))]> tl)),
        _, _, _, _, (<[rid:=Done ret1]> reqmap).
      esplits; try match goal with | |- context[map_Forall _] => fail | |- _ => eauto end.
      { rewrite ?list_fmap_insert //=. }
      { rewrite ?list_fmap_insert //=.
        do 2 f_equal. rewrite list_insert_id //. rewrite list_lookup_fmap Hstid2 //.
      }
      { eapply reqmap_rel_inprogress_done; eauto.
        { rewrite list_lookup_fmap Htid //. }
        { rewrite list_lookup_fmap Hstid2 //. }
      }
      { intros i; destruct (decide (i = stid)).
        { subst; intros ??? Hin; rewrite list_lookup_insert in Hin; ss; clarify.
          rewrite length_insert //.
        }
        rewrite list_lookup_insert_ne //.
        destruct (decide (i = stid2)).
        { subst; intros ??? Hin; rewrite // list_lookup_insert // in Hin.
          clarify; split; last eauto.
          eapply help_rel_helpee_done; eauto.
          subst i_helpee.
          f_equal. grind.
          repeat (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
        }
        intros ??? Hin; rewrite ?list_lookup_insert_ne // in Hin; eapply Hlookup; eauto.
      }
    }

    (* 1. No client case *)
    apply lookup_lt_Some in Htid as Hstid_cur_length.
    pose proof Htid as Htid'.
    apply Hlookup in Htid' as [Hcase _].
    inv Hcase.

    { (* Return case *)
      giter_s; giter_t; rewrite /= ?list_lookup_fmap Htid /=.
      gstep_s; gstep_t; gcNormS; gcNormT.
      des_ifs; ss.
      { rewrite /LModTr.interp_stateE ?interp_state_ret; ired.
        gstep; econs; econs; ss.
      }
      rewrite /triggerUB; ss; gstep_s; ss.
    }

    
    { (* event from ctx *)
      rename itr into itr_c.
      ides itr_c.
      { (* ret *)
        congruence.
      }
      { (* tau *)
        eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        zprogress.
        gbase. eapply CIH; eauto.
        eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { eapply reqmap_rel_id; eauto. }
        { intros i; destruct (decide (i = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify. split; ss.
            ides t0; try by eapply help_rel_eq; eauto.
            by rewrite ?SBRed.ret; ired.
          }
        }
      }
      (* events *)
      rewrite SBRed.vis in Htid; des_ifs; cycle 1.
      { eapply gsim_Take_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|ss]. }
      rename Heq into Hmsk2.
      destruct e as [e|[e|[e|e]]]; rewrite vis_trigger in Htid.
      { (* agE *)
        destruct e as [P|x|Q].
        { (* Assume *)
          eapply gsim_Assume_both_view;
            [lookup_tac; s; do 2 f_equal; hnorm_itr
            |lookup_tac; s; do 2 f_equal; hnorm_itr
            |exact Hrs|exact Hr|].
          intros rt1 rs1 Hrs1 Hr1.
          zprogress.
          gbase. eapply (CIH rt1 rs1); try by des; et.
          eexists (<[stid := (_, _, None)]> tl), _, _, _, _, reqmap;
            ss; esplits; eauto.
          { rewrite list_fmap_insert //=. }
          { rewrite list_fmap_insert //=. }
          { eapply reqmap_rel_id; eauto. }
          { intros i; destruct (decide (i = stid)); subst; cycle 1.
            { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
            { rewrite list_lookup_insert; ii; clarify. split; ss.
              ired; ides (k ()); try by eapply help_rel_eq; eauto.
              by rewrite ?SBRed.ret; ired.
            }
          }
          { exact (conj Hrs1 Hr1). }
        }
        { (* AssumeRes *)
          eapply gsim_AssumeRes_both_view;
            [lookup_tac; s; do 2 f_equal; hnorm_itr
            |lookup_tac; s; do 2 f_equal; hnorm_itr
            |exact Hrs|exact Hr|].
          intros Hx Hrx.
          zprogress.
          gbase. eapply (CIH (x ⋅ rt) (x ⋅ rs)); try by des.
          eexists (<[stid := (_, _, None)]> tl), _, _, _, _, reqmap;
            ss; esplits; eauto.
          { rewrite list_fmap_insert //=. }
          { rewrite list_fmap_insert //=. }
          { eapply reqmap_rel_id; eauto. }
          { intros i; destruct (decide (i = stid)); subst; cycle 1.
            { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
            { rewrite list_lookup_insert; ii; clarify. split; ss.
              ired; ides (k ()); try by eapply help_rel_eq; eauto.
              by rewrite ?SBRed.ret; ired.
            }
          }
          { exact (conj Hx Hrx). }
        }
        { (* Guarantee *)
          eapply gsim_Guarantee_both_view;
            [lookup_tac; s; do 2 f_equal; hnorm_itr
            |lookup_tac; s; do 2 f_equal; hnorm_itr
            |exact Hrs|exact Hr|].
          intros rt1 rs1 Hrs1 Hr1.
          zprogress.
          gbase. eapply (CIH rt1 rs1); try by des; et.
          eexists (<[stid := (_, _, None)]> tl), _, _, _, _, reqmap;
            ss; esplits; eauto.
          { rewrite list_fmap_insert //=. }
          { rewrite list_fmap_insert //=. }
          { eapply reqmap_rel_id; eauto. }
          { intros i; destruct (decide (i = stid)); subst; cycle 1.
            { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
            { rewrite list_lookup_insert; ii; clarify. split; ss.
              ired; ides (k ()); try by eapply help_rel_eq; eauto.
              by rewrite ?SBRed.ret; ired.
            }
          }
          { exact (conj Hrs1 Hr1). }
        }
      }
      { (* callE *)
        destruct e as [fn args| | | ].
        { (* call *)
          eapply gsim_Call_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          eapply gsim_Call_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          zprogress.
          hexploit (prog_s_prog_t fn ctx rs rt); eauto;
            intros [[-> ->]|Hprog].
          { s; giter_s. ired. rewrite list_lookup_insert /=. gstep_s; done.
            rewrite length_fmap //.
          }
          gbase. eapply (CIH rt rs); try by des.
          eexists (<[stid := (_, _, None)]> tl); ss; esplits; auto.
          { rewrite list_fmap_insert //=. }
          { rewrite list_fmap_insert //=. }
          { eapply reqmap_rel_id; eauto. }
          { intros i; destruct (decide (i = stid)); subst; cycle 1.
            { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
            { rewrite list_lookup_insert; ii; clarify. split; ss.
              destruct Hprog as [Hprog|Hprog].
              { eapply help_rel_call; eauto.
                { des; subst; rewrite elem_of_union; left; set_unfold; [left|right]; done. }
                { i; ired; rewrite -?bind_tau -?SBRed.tau. eapply help_rel_eq; auto. }
              }
              destruct Hprog as [Hprog|Hprog].
              { eapply help_rel_call; eauto.
                { des; subst; rewrite elem_of_union; right; done. }
                { i; ired; rewrite -?bind_tau -?SBRed.tau. eapply help_rel_eq; auto. }
              }
              destruct Hprog as [? [-> [msk1 [bd1 [-> ?]]]]]; s; unfold_trans; ired.
              rewrite -?interpV_bind.
              ides (bd1 args).
              { rewrite ?SBRed.ret; ired. rewrite -?bind_tau -?SBRed.tau.
                eapply help_rel_eq; eauto.
              }
              { eapply help_rel_eq; eauto.
                ss. grind. rewrite -?bind_tau -!SBRed.tau; eapply help_rel_eq; eauto.
              }
              { eapply help_rel_eq; eauto.
                ss. grind. rewrite -?bind_tau -!SBRed.tau; eapply help_rel_eq; eauto.
              }
            }
          }
          { exact Hres. }
        }
        { (* spawn *)
          eapply gsim_Spawn_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          eapply gsim_Spawn_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          hexploit (prog_s_prog_t fn ctx rs rt); eauto;
            intros [[-> ?]|Hprog]; s.
          { s. gstep_s; done. }
          assert (Htemp : ∃ bds bdt, prog_s ctx rs fn = Some (λ x, ⇓cris (bds x)) ∧
            prog_t ctx rt fn = Some (λ x, ⇓cris (bdt x))).
          { des; esplits; eauto; rewrite ?Hprog1 ?Hprog0 //. }
          destruct Htemp as [bds [bdt [Hprog1 Hprog2]]]; rewrite Hprog1 Hprog2; s; ired.
          zprogress. gbase.
          eapply (CIH rt rs); try by des.
          eexists ((<[stid := (_, _, None)]> tl) ++ [(_, _, None)]); ss.
          esplits; eauto.
          { rewrite ?fmap_app list_fmap_insert //=. }
          { rewrite ?fmap_app list_fmap_insert //=. }
          { eapply reqmap_rel_append; eauto.
            eapply reqmap_rel_id; eauto.
          }
          { intros i; destruct (decide (i = length tl)); subst.
            { intros ???; rewrite lookup_app_r // ?length_insert; try lia.
              rewrite Nat.sub_diag /=; intros Heq; inv Heq.
              split; ss.
              destruct Hprog as [Hprog|Hprog].
              { eapply (help_rel_call _ _ (λ a, Ret a) (λ a, Ret a)
                  ctx rs rt fn args); eauto.
                { rewrite elem_of_union; left; des; subst; set_unfold; auto. }
                { rewrite Hprog1 /=; ired; etrans; first apply bind_ret_r_rev; grind;
                    auto using interpV_ret. }
                { rewrite Hprog2 /=; ired; etrans; first apply bind_ret_r_rev; grind;
                    auto using interpV_ret. }
                { i; rewrite ?interpV_ret; econs; auto. }
              }
              destruct Hprog as [[? Hprog]|Hprog].
              { eapply (help_rel_call _ _ (λ a, Ret a) (λ a, Ret a)
                  ctx rs rt fn args); eauto.
                { rewrite elem_of_union; right; set_unfold; auto. }
                { rewrite Hprog1 /=; ired; etrans; first apply bind_ret_r_rev; grind;
                    auto using interpV_ret. }
                { rewrite Hprog2 /=; ired; etrans; first apply bind_ret_r_rev; grind;
                    auto using interpV_ret. }
                { i; rewrite ?interpV_ret; econs; auto. }
              }
              revert Hprog1 Hprog2.
              destruct Hprog as [? [-> [? [bd1 [-> ?]]]]]; unfold_trans.
              intros temp1%Some_inj; rewrite -(func_ext_rev args temp1).
              intros temp2%Some_inj; rewrite -(func_ext_rev args temp2).
              ides (bd1 args).
              { rewrite !SBRed.ret !interpV_ret; econs; eauto. }
              { eapply (help_rel_eq); try by grind.
                i; s; rewrite ?interpV_ret; econs; eauto.
              }
              { eapply (help_rel_eq); try by grind.
                i; s; rewrite ?interpV_ret; econs; eauto.
              }
            }
            destruct (decide (i = stid)); subst.
            { intros ???; rewrite -insert_app_l // list_lookup_insert // ?length_app; try lia.
              intros EQ; clarify.
              split; ss.
              rewrite ?length_fmap.
              ides (k (length tl)).
              { rewrite ?SBRed.ret ?interpV_ret; ired; auto. }
              { eapply (help_rel_eq); eauto. }
              { eapply (help_rel_eq); eauto. }
            }
            rewrite -insert_app_l // list_lookup_insert_ne //.
            intros ??? [[Hilen Hi]|[??]]%lookup_snoc_Some; last clarify.
            apply Hlookup; eauto.
          }
        }
        { (* yield *)
          eapply gsim_Yield_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
          eapply GSimAux.gsim_Yield_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
          ghcNormS; ghcNormT.
          zprogress.
          gbase. eapply (CIH rt rs); try by des.
          eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
          { rewrite list_fmap_insert //=. }
          { rewrite list_fmap_insert //=. }
          { eapply reqmap_rel_id; eauto. }
          { intros i; destruct (decide (i = stid)); subst; cycle 1.
            { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
            { rewrite list_lookup_insert; ii; clarify. ired. split; ss.
              ides (k ()).
              { rewrite ?SBRed.ret ?interpV_ret; ired; eauto. }
              { eapply (help_rel_eq); eauto. }
              { eapply (help_rel_eq); eauto. }
            }
          }
        }
        { (* gettid *)
          eapply gsim_GetTid_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
          eapply gsim_GetTid_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.

          zprogress.
          gbase. eapply (CIH rt rs); try by des.
          eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
          { rewrite list_fmap_insert //=. }
          { rewrite list_fmap_insert //=. }
          { eapply reqmap_rel_id; eauto. }
          { intros i; destruct (decide (i = stid)); subst; cycle 1.
            { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
            { rewrite list_lookup_insert; ii; clarify. split; ss. ired.
              ides (k stid).
              { rewrite ?SBRed.ret ?interpV_ret; ired; eauto. }
              { eapply (help_rel_eq); eauto. }
              { eapply (help_rel_eq); eauto. }
            }
          }
        }
      }
      { (* pgE *)
        destruct e as [key val|key].
        { (* sPut *)
          eapply gsim_SPut_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
          eapply gsim_SPut_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.

          match goal with | A : msk_ctx ?a |- _ => rename A into Hmskctx end.
          bsimpl. apply Hmskctx in Hmsk2; set_unfold in Hmsk2.
          rewrite !insert_union_with_r; cycle 1.
          { rewrite ?lookup_insert_ne //; ii; clarify; ss; eauto. }

          ghcNormS; ghcNormT.
          zprogress. gbase.
          eapply (CIH rt rs); try by des.
          eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
          { rewrite list_fmap_insert //=. }
          { rewrite list_fmap_insert //=. }
          { eapply reqmap_rel_id; eauto. }
          { intros i; destruct (decide (i = stid)); subst; cycle 1.
            { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
            { rewrite list_lookup_insert; ii; clarify. split; ss. ired.
              ides (k ()).
              { rewrite ?SBRed.ret ?interpV_ret; ired; eauto. }
              { eapply (help_rel_eq); eauto. }
              { eapply (help_rel_eq); eauto. }
            }
          }
          { eapply map_Forall_union_with; cycle 1.
            { split.
              { eapply map_Forall_union_with_inv in Hst1 as ?; des; eauto. }
              { eapply map_Forall_insert_2; ss.
                eapply map_Forall_union_with_inv in Hst1 as ?; des; eauto.
              }
            }
            eapply map_Forall_union_with_inv_gen in Hst1.
            set_solver+Hmsk2 Hst1.
          }
          { eapply map_Forall_union_with; cycle 1.
            { split.
              { eapply map_Forall_union_with_inv in Hst2 as ?; des; eauto. }
              { eapply map_Forall_insert_2; ss.
                eapply map_Forall_union_with_inv in Hst2 as ?; des; eauto.
              }
            }
            eapply map_Forall_union_with_inv_gen in Hst2; revert Hst2.
            rewrite ?dom_union_with ?dom_insert ?dom_empty; i.
            set_solver+Hmsk2 Hst2.
          }
        }
        { (* sGet *)
          eapply gsim_SGet_tgt; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
          eapply gsim_SGet_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
          ghcNormS; ghcNormT.
          match goal with | A : msk_ctx ?a |- _ => rename A into Hmskctx end.
          bsimpl. apply Hmskctx in Hmsk2; set_unfold in Hmsk2.
          rewrite ?lookup_union_with ?lookup_insert_ne //; ii; clarify; ss; eauto.
          rewrite ?lookup_empty /=; ired.
          zprogress. gbase.
          eapply (CIH rt rs); try by des.
          eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
          { rewrite list_fmap_insert //=. }
          { rewrite list_fmap_insert //=. }
          { eapply reqmap_rel_id; eauto. }
          { intros i; destruct (decide (i = stid)); subst; cycle 1.
            { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
            { rewrite list_lookup_insert; ii; clarify. split; ss. ired.
              set (temp := default _ _); ides (k temp).
              { rewrite ?SBRed.ret ?interpV_ret; ired; eauto. }
              { eapply (help_rel_eq); eauto. }
              { eapply (help_rel_eq); eauto. }
            }
          }
        }
      }
      { (* coreE *)
        destruct e as [X|X|? ? fn args].
        { (* Choose *)
          eapply gsim_Choose_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|]. intros x.
          eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]. exists x.
          zprogress.
          gbase. eapply (CIH rt rs); try by des.
          eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
          { rewrite list_fmap_insert //=. }
          { rewrite list_fmap_insert //=. }
          { eapply reqmap_rel_id; eauto. }
          { intros i; destruct (decide (i = stid)); subst; cycle 1.
            { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
            { rewrite list_lookup_insert; ii; clarify. split; ss.
              ired; ides (k x); try by eapply help_rel_eq; eauto.
              by rewrite ?SBRed.ret; ired.
            }
          }
        }
        { (* Take *)
          eapply gsim_Take_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]. intros x.
          eapply gsim_Take_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|]. exists x.
          zprogress.
          gbase. eapply (CIH rt rs); try by des.
          eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
          { rewrite list_fmap_insert //=. }
          { rewrite list_fmap_insert //=. }
          { eapply reqmap_rel_id; eauto. }
          { intros i; destruct (decide (i = stid)); subst; cycle 1.
            { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
            { rewrite list_lookup_insert; ii; clarify. split; ss.
              ired; ides (k x); try by eapply help_rel_eq; eauto.
              by rewrite ?SBRed.ret; ired.
            }
          }
        }
        { (* IO *)
          eapply gsim_IO; (try by lookup_tac; s; do 2 f_equal; hnorm_itr). intros ret; s.
          ghcNormS; ghcNormT.
          zprogress. gbase. eapply (CIH rt rs); try by des.
          eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
          { rewrite list_fmap_insert //=. }
          { rewrite list_fmap_insert //=. }
          { eapply reqmap_rel_id; eauto. }
          { intros i; destruct (decide (i = stid)); subst; cycle 1.
            { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
            { rewrite list_lookup_insert; ii; clarify. split; ss.
              ired; ides (k ret); try by eapply help_rel_eq; eauto.
              by rewrite ?SBRed.ret; ired.
            }
          }
        }
      }
    }
    { (* call case *)
      match goal with | A : _ ∈ _ |- _ => rename A into Hfn end.
      set_unfold in Hfn; des; clarify.
      { (* Helping.run *)
        revert Htid; rewrite prog_s_run ?prog_t_run; eauto using wf_src; s; ired.
        rewrite /run_s /run_t -!interpV_bind; intros Htid.
        revert Htid; rewrite /HelpingOff.run /HelpingOn.run; intros Htid.
        eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        destruct (arg ↓) as [[Nhelpee j]|];
          [|eapply gsim_Take_src with (X := False);
             [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss]; s.
        ghcNormS. ghcNormT.

        (* The target allocates a fresh private-protocol ticket. *)
        set (rid := fresh (dom reqmap)).
        assert (Hfresh : reqmap !! rid = None).
        { apply not_elem_of_dom. subst rid. apply is_fresh. }
        eapply gsim_Take_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        exists rid. rewrite list_insert_insert. ghcNormT.
        pose proof (res_rel_issue reqmap rt rs rid Nhelpee j Hfresh Hres)
          as [rt1 [Hrt1 [Hissue Hres1]]].
        eapply gsim_Assume_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        exists rt1; splits; [exact Hrt1|exact Hissue|].
        rewrite list_insert_insert. ghcNormT.
        pose proof Hres1 as [Hrsp Hrp].

        rewrite unfold_iter; ghcNormS.
        eapply gsim_Yield_tgt; (eauto using wf_src);
          (try by lookup_tac; s; do 2 f_equal; hnorm_itr).
        { (* self-help *)
          rewrite ?list_insert_insert. ghcNormT. rewrite /try_run.

          (* Pend -> InProgress *)
          eapply gsim_Choose_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          intros [ret0|]; rewrite list_insert_insert; ghcNormT.
          { eapply gsim_Guarantee_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
            intros rt2 [Hrt2 Hupd].
            pose proof (res_rel_observe (<[rid:=Pend Nhelpee j]> reqmap)
              rt1 rs rid ret0 rt2 Hres1 Hupd) as [Hdone _].
            rewrite lookup_insert in Hdone. congruence.
          }
          eapply gsim_Choose_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          intros N2; rewrite list_insert_insert; ghcNormT.
          eapply gsim_Choose_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          intros arg2; rewrite list_insert_insert; ghcNormT.
          eapply gsim_Guarantee_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          intros rt2 [Hrt2 Hupd].
          pose proof (res_rel_claim (<[rid:=Pend Nhelpee j]> reqmap)
            rt1 rs rid N2 arg2 rt2 Hres1 Hupd) as [Hpend Hres2].
          rewrite lookup_insert in Hpend.
          injection Hpend as HN Harg. subst N2. subst arg2.
          rewrite insert_insert in Hres2.
          rewrite list_insert_insert. ghcNormT.
          pose proof Hres2 as [Hrs2 Hr2].

          generalize j at 1 2.
          revert Hrs2 Hr2; generalize rt2 rs.
          gcofix CIH2.
          clear dependent rt1 rt2.
          intros rt1 rs1 Hrs1 Hr1 j1. zprogress.
          rewrite unfold_iter.
          eapply gsim_Yield_tgt; eauto using wf_src; (try by lookup_tac; s; do 2 f_equal; hnorm_itr).
          { (* direct job execution *)
            rewrite !list_insert_insert. ghcNormT.
            rewrite {1}yield_namespace_unfold.
            eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
            rewrite list_insert_insert.
            eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s. exists None.
            rewrite list_insert_insert. ghcNormS.
            zprogress with smj_bot smj_bot _ _.
            eapply gsim_jobs_both_view; rewrite ?length_fmap //.
            intros rt2 rs2 [j2|ret1] Hrs2 Hr2.
            { (* repeat *)
              eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
              eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
              rewrite !list_insert_insert.
              rewrite {1}unfold_iter. ghcNormS. gbase.
              eapply (CIH2 rt2 rs2 Hrs2 Hr2 j2); eauto.
            }
            (* job done *)
            clear CIH2.
            rewrite {1}yield_namespace_unfold.
            eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
            rewrite list_insert_insert.
            eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s. exists None.
            rewrite list_insert_insert. ghcNormS.

            ghcNormT.
            assert (Hip : (<[rid:=InProgress]> reqmap) !! rid = Some InProgress)
              by apply lookup_insert.
            pose proof (res_rel_publish (<[rid:=InProgress]> reqmap)
              rt2 rs2 rid ret1 Hip (conj Hrs2 Hr2))
              as [rt3 [Hrt3 [Hupd3 Hres3]]].
            rewrite insert_insert in Hres3.
            eapply gsim_Assume_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
            exists rt3; splits; [exact Hrt3|exact Hupd3|].
            rewrite list_insert_insert. ghcNormT.

            gbase. eapply (CIH rt3 rs2); try by des; eauto.
            eexists (<[stid := (_, _, None)]> tl), _, _, _, _,
              (<[rid:=Done ret1]> reqmap); ss; esplits; eauto.
            { rewrite list_fmap_insert //=. }
            { rewrite list_fmap_insert //=. }
            { eapply reqmap_rel_insert_false; first apply is_fresh. eapply reqmap_rel_id; eauto. }
            { intros i; destruct (decide (i = stid)); subst; cycle 1.
              { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
              { rewrite list_lookup_insert; ii; clarify. }
            }
          }

          (* freeze during job execution *)
          intros Hmtid; split; first done.
          intros mtidn_t stidn_t Hmtidn_t; exists mtidn_t, stidn_t; split; first done.
          intros rtf rsf Hrsf Hrf.
          rewrite !list_insert_insert. ghcNormS; ghcNormT.
          eapply map_Forall_insert_union_with with (k:=SchI.v_tid) in Hst1 as Hsts2; revert Hsts2.
          repeat match goal with
          | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
            state_insert_simpl k1 v1 H
          end.
          intros Hsts2.
          pose proof Hsts2 as Hstt4.
          zprogress. gbase. eapply (CIH rtf rsf); eauto.
          eexists (<[stid := (_, _, Some (inl (rid, InProgress, None)))]> tl),
            _, _, _, _, (<[rid:=InProgress]> reqmap); esplits; eauto.
            { rewrite list_fmap_insert //=. }
            { rewrite list_fmap_insert //=. }
            { eapply reqmap_rel_insert_true; first apply is_fresh; eauto. }
          { intros i; destruct (decide (i = stid)); subst; cycle 1.
            { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
            { rewrite list_lookup_insert; ii; clarify. split.
              { eapply (help_rel_job_loop j1 Nhelpee); eauto.
                { rewrite /helpee_inprogress_s. f_equal.
                  repeat (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
                }
                { rewrite /helpee_inprogress_t. f_equal.
                  repeat (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
                }
              }
              apply list_lookup_fmap_Some in Hmtid as [[? ?] [? ?]]; clarify.
              esplits; eauto.
            }
          }
          { exact (conj Hrsf Hrf). }
        }

        (* freeze before job execution *)
        intros Hmtid; split; first done.
        intros mtidn_t stidn_t Hmtidn_t; exists mtidn_t, stidn_t; split; first done.
        intros rtp rsp Hrsfreeze Hrfreeze.
        rewrite !list_insert_insert. ghcNormS; ghcNormT.
        eapply map_Forall_insert_union_with with (k:=SchI.v_tid) in Hst1 as Hsts; revert Hsts.
        repeat match goal with
        | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
          state_insert_simpl k1 v1 H
        end.
        intros Hsts.
        pose proof Hsts as Hstt.
        zprogress. gbase. eapply (CIH rtp rsp); eauto.
        eexists (<[stid := (_, _, Some (inl (rid, Pend Nhelpee j, None)))]> tl),
          _, _, _, _, (<[rid:=Pend Nhelpee j]> reqmap); esplits; eauto.
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { eapply reqmap_rel_insert_true; first apply is_fresh; eauto. }
        { intros i; destruct (decide (i = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify.
            split.
            { eapply help_rel_helpee_pend; eauto.
              { rewrite /helpee_inprogress_s. f_equal.
                repeat (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
              }
              { rewrite /helpee_pend_t. f_equal.
                repeat (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
              }
            }
            apply list_lookup_fmap_Some in Hmtid as [[? ?] [? ?]]; clarify.
            esplits; eauto.
          }
        }
        { exact (conj Hrsfreeze Hrfreeze). }
      }
      { (* Helping.help *)
        revert Htid; rewrite prog_s_help ?prog_t_help; eauto using wf_src; s; ired.
        rewrite /help_s /help_t -!interpV_bind /HelpingOff.help /HelpingOn.help; intros Htid.
        eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].

        destruct Any.downcast as [Nhelper|]; s; ghcNormS; cycle 1.
        { eapply gsim_Take_src with (X := False);
          [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss. }
        eapply gsim_Choose_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|]. intros rid.
        rewrite list_insert_insert. ghcNormT.
        eapply gsim_Choose_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|]. intros Nhelpee.
        rewrite list_insert_insert. ghcNormT.
        eapply gsim_Choose_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|]. intros arghelp.
        rewrite list_insert_insert. ghcNormT.
        eapply gsim_Guarantee_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        intros rt0 [Hrt0 Hclaim].
        pose proof (res_rel_claim reqmap rt rs rid Nhelpee arghelp rt0 Hres Hclaim)
          as [Hrid Hres0].
        pose proof Hres0 as [Hrs0 Hr0].
        rewrite list_insert_insert. ghcNormT.

        (* go for help *)
        pose proof Hrid as Hrid'.
        eapply reqmap_rel_Some_2 in Hrid' as [stid_helpee [i_s [i_t Hhelpee]]]; eauto.
        eapply Hlookup in Hhelpee as Hhelpee'.
        destruct Hhelpee' as [Hhelpee' [mtid_helpee Hthshelpee]].
        inv Hhelpee'; des; clarify.
        eapply lookup_lt_Some in Hhelpee as Hhelpeelen.
        assert (Hneq : stid_helpee ≠ stid) by (ii; clarify).

        (* handle source yield *)
        rewrite yield_namespace_unfold.
        eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        rewrite list_insert_insert.
        eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        exists (Some true). rewrite list_insert_insert. ghcNormS.
        rewrite !option_Guarantee_sred.
        eapply gsim_option_Guarantee_both_view;
          [lookup_tac; do 2 f_equal
          |lookup_tac; do 2 f_equal
          |exact Hrs0|exact Hr0|].
        rewrite !list_insert_insert. intros rt1 rs1 Hrs1 Hr1.
        ghcNormS; rewrite lookup_empty.
        eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        rewrite list_insert_insert.

        eapply gsim_Call_src;
          [lookup_tac; s; do 2 f_equal; hnorm_itr|rewrite list_insert_insert].
        rewrite prog_s_yield; auto using wf_src.
        rewrite /yield /SchI.yield /cfunU /fbody_trivial; ired.
        rewrite -interpV_bind.
        eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|rewrite list_insert_insert].
        ghcNormS.

        eapply gsim_SGet_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
        rewrite list_insert_insert.
        match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst1 end.

        eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        rewrite list_insert_insert.
        eapply gsim_GetTid_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
        rewrite list_insert_insert.

        eapply gsim_SGet_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
        rewrite list_insert_insert.
        match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst1 end.
        ghcNormS.

        destruct (_ !! mtid) as [[? ?]|] eqn : Hmtid; ss; cycle 1.
        { ghcNormS.
          eapply gsim_Take_src with (X := False);
            [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss.
        }
        ghcNormS. case_decide; subst; cycle 1.
        { ghcNormS.
          eapply gsim_Take_src with (X := False);
            [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss.
        }
        rewrite /choose_index. ghcNormS.

        eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        unshelve eexists.
        { exists (mtid_helpee, stid_helpee). rewrite /= list_lookup_fmap Hthshelpee //. }
        rewrite list_insert_insert. ghcNormS.

        eapply gsim_SPut_src;
          [lookup_tac; s; do 2 f_equal; hnorm_itr|exact Hst1|]; s.
        rewrite list_insert_insert. ghcNormS.
        eapply (map_Forall_insert_union_with _ _ SchI.v_tid) in Hst1 as Hsts; revert Hsts.
        repeat match goal with
        | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
          state_insert_simpl k1 v1 H
        end. intros Hsts.
        eapply gsim_tau_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
        rewrite list_insert_insert. ghcNormS.

        eapply gsim_Yield_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
        rewrite list_insert_insert. ghcNormS.

        eapply gsim_tau_src; auto.
        { rewrite list_lookup_insert_ne //=.
          rewrite list_lookup_fmap Hhelpee /=.
          rewrite /helpee_inprogress_s; hnorm_itr.
        }

        (* target proceed for helping *)
        ghcNormT. ghcNormS. rewrite option_Assume_sred.
        eapply gsim_option_Assume_both_view;
          [lookup_tac; do 2 f_equal
          |lookup_tac; do 2 f_equal
          |auto|eauto|].
        intros rt2 rs2 Hrs2 Hr2.
        rewrite !list_insert_insert. ghcNormT. ghcNormS.

        generalize arghelp.
        revert Hrs2 Hr2; generalize rt2 rs2; gcofix CIH2.
        clear dependent rt2 rs2.
        intros rt2 rs2 Hrs2 Hr2 arghelp2.
        rewrite unfold_iter. ghcNormT.
        eapply (gsim_Yield_tgt
          (HelpAuth (<[rid:=InProgress]> reqmap) ∗
           HelpRun (<[rid:=InProgress]> reqmap)) Nhelpee);
          [by apply wf_src|exact WF|exact Hsts|exact Hst2|exact Hrs2|exact Hr2
          |by lookup_tac; s; do 2 f_equal; hnorm_itr
          |by lookup_tac; s; do 2 f_equal; hnorm_itr
          | |].
        { (* direct job helping *)
          rewrite !list_insert_insert.

          rewrite {1}yield_namespace_unfold.
          eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          rewrite list_insert_insert.
          eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          exists None. rewrite list_insert_insert. ghcNormS. ghcNormT.

          zprogress with smj_bot smj_bot _ _.
          eapply gsim_jobs_both_view;
            try by rewrite ?length_insert ?length_fmap.
          intros rt3 rs3 [arg1|ret1] Hrs3 Hr3.
          { (* repeat *)
            eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
            eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
            rewrite !list_insert_insert.
            rewrite {1}unfold_iter. ghcNormS. ghcNormT.
            greplace_s; cycle 1.
            { gbase. eapply (CIH2 rt3 rs3 Hrs3 Hr3 arg1); eauto. }
            repeat f_equal; grind.
          }

          (* done - get back to the helper *)
          clear CIH2. ghcNormS. ghcNormT.

          rewrite {1}yield_namespace_unfold.
          eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          rewrite list_insert_insert. ghcNormS.
          eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          exists (Some true). ghcNormS.
          rewrite list_insert_insert option_Guarantee_sred.

          eapply gsim_option_Guarantee_both_view;
            [lookup_tac; s; do 2 f_equal
            |lookup_tac; s; do 2 f_equal
            |auto|eauto|].
          intros rt4 rs4 Hrs4 Hr4. simpl. rewrite ?list_insert_insert.
          ghcNormS; rewrite lookup_empty.
          eapply gsim_tau_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
          rewrite list_insert_insert.

          eapply gsim_Call_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|rewrite list_insert_insert].
          rewrite prog_s_yield; auto using wf_src.
          rewrite /yield /SchI.yield /cfunU /fbody_trivial. rewrite /= bind_ret_l -interpV_bind.
          eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|rewrite list_insert_insert].
          ghcNormS.
          eapply gsim_SGet_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|apply Hsts|]; s.
          rewrite !list_insert_insert.
          match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hsts end.
          eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          rewrite list_insert_insert.
          eapply gsim_GetTid_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
          rewrite list_insert_insert.

          eapply gsim_SGet_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
          rewrite list_insert_insert.
          match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst1 end. ghcNormS.

          rewrite Hthshelpee. ghcNormS. des_ifs_safe; ss. ghcNormS. rewrite /choose_index.
          eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          unshelve eexists.
          { exists (mtid, stid). rewrite list_lookup_fmap Hmtid //=. }
          rewrite list_insert_insert.

          eapply gsim_SPut_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
          rewrite list_insert_insert. ghcNormS.
          eapply (map_Forall_insert_union_with _ _ SchI.v_tid) in Hsts as Hsts2; revert Hsts2.
          repeat match goal with
          | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
            state_insert_simpl k1 v1 H
          end.
          intros Hsts2.
          eapply gsim_tau_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
          rewrite list_insert_insert.
          eapply gsim_Yield_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
          rewrite list_insert_insert. ghcNormS. rewrite list_insert_commute //.

          eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s. ghcNormS.
          ghcNormT. rewrite !option_Assume_sred.
          eapply gsim_option_Assume_both_view;
            [lookup_tac; do 2 f_equal
            |lookup_tac; do 2 f_equal
            |auto|eauto|].
          rewrite !list_insert_insert. intros rt5 rs5 Hrs5 Hr5.

          assert (Hip : (<[rid:=InProgress]> reqmap) !! rid = Some InProgress)
            by apply lookup_insert.
          pose proof (res_rel_publish (<[rid:=InProgress]> reqmap)
            rt5 rs5 rid ret1 Hip (conj Hrs5 Hr5))
            as [rt6 [Hrt6 [Hdone6 Hres6]]].
          rewrite insert_insert in Hres6.
          eapply gsim_Assume_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          exists rt6; splits; [exact Hrt6|exact Hdone6|].
          rewrite list_insert_insert. ghcNormT.

          rewrite {1}yield_namespace_unfold.
          eapply gsim_tau_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
          rewrite list_insert_insert.

          eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          exists (None).
          rewrite list_insert_insert. ghcNormS.

          (* by coinduction *)
          zprogress. gbase. eapply (CIH rt6 rs5); eauto.
          set (i_helpee := ⇓cris (tau;; _)).
          eexists (<[stid := (⇓cris (ktr_s () ↑), ⇓cris (ktr_t () ↑), None)]>
            (<[stid_helpee := (i_helpee, _, Some (inl (rid, Done ret1, None)))]> tl)),
            _, _, _, _, (<[rid:=Done ret1]> reqmap).
          esplits; try match goal with | |- context[map_Forall _] => fail | |- _ => eauto end.
          { rewrite ?list_fmap_insert //=. }
          { rewrite ?list_fmap_insert //=.
            do 2 f_equal. rewrite list_insert_id //. rewrite list_lookup_fmap Hhelpee //.
          }
          { rewrite list_insert_commute //.
            eapply reqmap_rel_pend; eauto.
            { rewrite list_lookup_insert_ne //. }
            eapply reqmap_rel_id; eauto.
          }
          { intros i; destruct (decide (i = stid)).
            { subst; intros ??? Hin; rewrite list_lookup_insert in Hin; ss; clarify.
              rewrite length_insert //.
            }
            destruct (decide (i = stid_helpee)).
            { subst; intros ??? Hin; rewrite list_lookup_insert_ne // list_lookup_insert // in Hin.
              clarify; split; last eauto.
              eapply help_rel_helpee_done; eauto.
              subst i_helpee.
              f_equal. grind.
              repeat (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
            }
            intros ??? Hin; rewrite ?list_lookup_insert_ne // in Hin; eapply Hlookup; eauto.
          }
        }

        (* freeze during job execution *)
        clear CIH2.
        intros Hmtid_helpee; split; [rewrite list_lookup_fmap Hmtid //|].
        intros mtidn_t stidn_t Hmtidn_t; exists mtidn_t, stidn_t; split; first done.
        intros rt3 rs3 Hrs3 Hr3.
        rewrite !list_insert_insert.
        assert (Hstn : map_Forall (const is_Some)
          ({[SchI.v_ths # ths↑; SchI.v_tid # mtidn_t↑]} +# st_ctx)).
        { eapply (map_Forall_insert_union_with _ _ SchI.v_tid) in Hsts as temp;
            revert temp.
          repeat match goal with
          | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
            state_insert_simpl k1 v1 Hsts
          end.
          i; eauto.
        }
        zprogress. gbase. eapply (CIH rt3 rs3); eauto; clear CIH.
        eexists (<[stid_helpee := (_, _, Some (inl (_)))]>
          (<[stid := (_, _, Some (inr (_)))]> tl)),
          _, _, _, _, (<[rid:=InProgress]> reqmap);
          esplits; try refl.
        { rewrite !list_fmap_insert //=. }
        { rewrite !list_fmap_insert //=; f_equal.
          rewrite list_insert_commute //; f_equal.
          rewrite list_insert_id // list_lookup_fmap Hhelpee //=.
        }
        { rewrite list_insert_commute //. eapply reqmap_rel_pend_inprogress; eauto. }
        { rewrite list_insert_commute //.
          intros i; destruct (decide (i = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=.
            destruct (decide (i = stid_helpee)); subst.
            { rewrite list_lookup_insert //; intros ?; clarify; split.
              { eapply (help_rel_helpee_inprogress arghelp2 arghelp Nhelpee rid); eauto.
                rewrite /helpee_inprogress_s. f_equal.
                repeat (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
              }
              apply list_lookup_fmap_Some in Hmtid_helpee as [[? ?] [? ?]]; eauto.
            }
            rewrite list_lookup_insert_ne //; eauto.
          }
          intros ???; rewrite list_lookup_insert ?length_insert //=.
          intros ?%Some_inj; clarify; split; last done.
          eapply (help_rel_helper_inprogress arghelp2 Nhelper Nhelpee rid _ _ ktr_s); eauto.
          { f_equal. repeat (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind). }
          { rewrite /helper_inprogress_t. f_equal.
            repeat (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
          }
        }
        { exact Hstn. }
        { exact Hstn. }
        { exact (conj Hrs3 Hr3). }
      }
      { (* SchI.inner_spawn *)
        revert Htid; rewrite prog_s_inner_spawn; auto using wf_src; rewrite prog_t_inner_spawn //.
        rewrite /inner_spawn; ired; do 2 rewrite -interpV_bind; intros Htid.

        eapply gsim_tau_src; [rewrite list_lookup_fmap // Htid; s; do 2 f_equal; hnorm_itr|].
        eapply gsim_tau_tgt; [rewrite list_lookup_fmap // Htid; s; do 2 f_equal; hnorm_itr|].
        zprogress.

        rewrite /cfunU.
        destruct Any.downcast as [[]|]; s; ghcNormS; cycle 1.
        { eapply gsim_Take_src with (X := False);
          [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss.
        }
        eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          rewrite list_insert_insert.
        eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          rewrite list_insert_insert.
        rewrite !lookup_empty.

        ghcNormS; ghcNormT.
        case_bool_decide as Hs; ghcNormS;
          [|eapply gsim_Take_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss].

        eapply gsim_Call_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss.
          rewrite list_insert_insert.
        eapply gsim_Call_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss.
          rewrite list_insert_insert.
        hexploit (prog_s_prog_t s ctx rs rt); eauto;
          intros [[-> ->]|Hprog].
        { s; giter_s. ired. rewrite list_lookup_insert /=. gstep_s; done.
          rewrite length_fmap //.
        }
        zprogress.
        gbase.
        eapply (CIH rt rs); eauto.
        eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { eapply reqmap_rel_id; eauto. }
        { intros i1; destruct (decide (i1 = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify. split; ss.
            destruct Hprog as [Hprog|Hprog].
            { exfalso; des; subst s; apply Hs; set_solver+Hmsk. }
            destruct Hprog as [Hprog|Hprog].
            { eapply help_rel_call with (ctx:=ctx); eauto.
              { des; clarify; rewrite elem_of_union; right; done. }
              { i; ired; rewrite -?bind_tau -?SBRed.tau.
                eapply help_rel_inner_spawn; eauto.
                { rewrite /inner_spawn_pend; f_equal.
                  instantiate (1:=ret); grind.
                  repeat f_equal; extensionalities a; grind.
                }
                { rewrite /inner_spawn_pend.
                  repeat f_equal; extensionalities a; grind.
                }
              }
            }
            destruct Hprog as [? [-> [msk1 [bd1 [-> ?]]]]]; s; unfold_trans; ired.
            rewrite -?interpV_bind.
            ides (bd1 t0↑).
            { rewrite ?SBRed.ret; ired. rewrite -?bind_tau -?SBRed.tau.
              eapply help_rel_inner_spawn; eauto.
              { rewrite /inner_spawn_pend. f_equal.
                f_equal; grind.
                repeat f_equal; extensionalities a; grind.
              }
              { rewrite /inner_spawn_pend. f_equal.
                f_equal; grind.
                repeat f_equal; extensionalities a; grind.
              }
            }
            { eapply help_rel_eq; eauto.
              i; s.
              rewrite -?bind_tau -?SBRed.tau.
              eapply help_rel_inner_spawn; eauto.
              { rewrite /inner_spawn_pend. f_equal.
                f_equal; grind.
                repeat f_equal; extensionalities a; grind.
              }
              { rewrite /inner_spawn_pend. f_equal.
                f_equal; grind.
                repeat f_equal; extensionalities a; grind.
              }
            }
            { eapply help_rel_eq; eauto.
              i; s.
              rewrite -?bind_tau -?SBRed.tau.
              eapply help_rel_inner_spawn; eauto.
              { rewrite /inner_spawn_pend. f_equal.
                f_equal; grind.
                repeat f_equal; extensionalities a; grind.
              }
              { rewrite /inner_spawn_pend. f_equal.
                f_equal; grind.
                repeat f_equal; extensionalities a; grind.
              }
            }
          }
        }
      }
      { (* SchI.spawn *)
        revert Htid; rewrite prog_s_spawn; auto using wf_src; rewrite prog_t_spawn //.
        rewrite /spawn; ired; do 2 rewrite -interpV_bind; intros Htid.

        eapply gsim_tau_src; [rewrite list_lookup_fmap // Htid; s; do 2 f_equal; hnorm_itr|].
        eapply gsim_tau_tgt; [rewrite list_lookup_fmap // Htid; s; do 2 f_equal; hnorm_itr|].
        zprogress.

        rewrite /cfunU /SchI.spawn.
        destruct Any.downcast as [[]|]; s; ghcNormS; cycle 1.
        { eapply gsim_Take_src with (X := False);
          [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss.
        }
        ghcNormT.

        eapply gsim_SGet_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
        rewrite list_insert_insert.
        match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst1 end. ghcNormS.

        eapply gsim_SGet_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
        rewrite list_insert_insert.
        match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst2 end. ghcNormT.

        eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        rewrite !list_insert_insert.
        destruct (decide (fn_name SchHdr._spawn ∈ msk)) as [Hspawnmsk|Hspawnmsk].
        { ghcNormS. case_bool_decide as a; des; first set_solver+a Hspawnmsk.
          s. eapply gsim_Take_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          done.
        }
        eapply gsim_Spawn_src.
        { lookup_tac; s; do 2 f_equal. etrans; first hnorm_itr.
          case_bool_decide as a; des; last (exfalso; apply a; split; ss).
          s. hnorm_itr.
        }
        eapply gsim_Spawn_tgt.
        { lookup_tac; s; do 2 f_equal. etrans; first hnorm_itr.
          case_bool_decide as a; des; last (exfalso; apply a; split; ss).
          s. hnorm_itr.
        }
        rewrite !list_insert_insert.
        rewrite prog_s_inner_spawn; auto using wf_src; rewrite prog_t_inner_spawn //=.
        ired.
        ghcNormS; ghcNormT.

        eapply gsim_SPut_src.
        { rewrite lookup_app list_lookup_insert // length_fmap //. }
        { exact Hst1. }
        rewrite insert_app_l // ?length_insert ?length_fmap // list_insert_insert.
        eapply map_Forall_insert_union_with in Hst1 as Hst1'; revert Hst1'.
        repeat match goal with
        | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
          state_insert_simpl k1 v1 H
        end.
        intros Hst1'.
        ghcNormS.

        eapply gsim_SPut_tgt.
        { rewrite lookup_app list_lookup_insert // length_fmap //. }
        { exact Hst2. }
        rewrite insert_app_l // ?length_insert ?length_fmap // list_insert_insert.
        pose proof Hst1' as Hst2'.
        ghcNormT.

        zprogress. gbase.
        eapply (CIH rt rs); eauto.
        eexists ((<[stid := (_, _, None)]> tl) ++ [(inner_spawn (s, t0)↑, inner_spawn (s, t0)↑, None)]); ss.
        esplits; eauto.
        { assert (Hvths : is_Some
              (({[SchI.v_ths # ths↑; SchI.v_tid # mtid↑]}
                : gmap key (option Any.t)) !! SchI.v_ths)).
          { rewrite lookup_insert; eauto. }
          rewrite (insert_union_with_l' _ _ _ _ Hst1 Hvths) insert_insert //. }
        { rewrite ?fmap_app list_fmap_insert //=. }
        { rewrite ?fmap_app list_fmap_insert //=. }
        { eapply reqmap_rel_append; eauto.
          eapply reqmap_rel_id; eauto.
        }
        { intros i1; destruct (decide (i1 = length tl)); subst.
          { intros ???; rewrite lookup_app_r // ?length_insert; try lia.
            rewrite Nat.sub_diag /=; intros Heq; inv Heq.
            split; ss.
            eapply (help_rel_call _ _ (λ a, Ret a) (λ a, Ret a)
              ctx rs rt SchHdr._spawn.1); eauto.
            { rewrite /HelpingOn.t /SchI.t; ss; set_solver-. }
            { rewrite prog_s_inner_spawn; auto using wf_src; s; ired; rewrite -!interpV_bind. grind. }
            { rewrite prog_t_inner_spawn; auto; s; ired; rewrite -!interpV_bind. grind. }
            i; rewrite !interpV_ret; eapply help_rel_ret; eauto.
          }
          destruct (decide (i1 = stid)); subst.
          { intros ???; rewrite -insert_app_l // list_lookup_insert // ?length_app; try lia.
            intros EQ; clarify.
          }
          rewrite -insert_app_l // list_lookup_insert_ne //.
          intros ??? [[Hilen Hi]|[??]]%lookup_snoc_Some; last clarify.
          eapply Hlookup in Hi; des; split; eauto.
          destruct no as [[[[? [?| |?]] ?]|?]|]; eauto; des; eexists _, _; rewrite lookup_app_l //;
            eapply lookup_lt_Some; eauto.
        }
        { assert (Hvths : is_Some
              (({[SchI.v_ths # ths↑; SchI.v_tid # mtid↑]}
                : gmap key (option Any.t)) !! SchI.v_ths)).
          { rewrite lookup_insert; eauto. }
          rewrite (insert_union_with_l' _ _ _ _ Hst1 Hvths) insert_insert.
          exact Hst1'.
        }
      }
      { (* SchI.yield *)
        revert Htid; rewrite prog_s_yield; auto using wf_src; rewrite prog_t_yield //.
        rewrite /yield; ired; do 2 rewrite -interpV_bind; intros Htid.

        eapply gsim_tau_src; [rewrite list_lookup_fmap // Htid; s; do 2 f_equal; hnorm_itr|].
        eapply gsim_tau_tgt; [rewrite list_lookup_fmap // Htid; s; do 2 f_equal; hnorm_itr|].
        zprogress.

        rewrite /cfunU /SchI.yield /SchI.choose_index.
        destruct Any.downcast as [[]|]; s; ghcNormS; cycle 1.
        { eapply gsim_Take_src with (X := False);
          [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss.
        }
        ghcNormT.

        eapply gsim_SGet_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
        rewrite list_insert_insert.
        match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst1 end. ghcNormS.

        eapply gsim_SGet_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
        rewrite list_insert_insert.
        match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst2 end. ghcNormT.

        eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        rewrite !list_insert_insert.

        eapply gsim_GetTid_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
        rewrite list_insert_insert.
        eapply gsim_GetTid_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
        rewrite list_insert_insert.

        eapply gsim_SGet_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
        rewrite list_insert_insert.
        match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst1 end. ghcNormS.

        eapply gsim_SGet_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
        rewrite list_insert_insert.
        match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst2 end. ghcNormT.

        destruct (_ !! mtid) as [[? ?]|]; ghcNormS; ghcNormT; cycle 1.
        { eapply gsim_Take_src with (X := False);
          [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss.
        }
        case_decide; ghcNormS; ghcNormT; subst; cycle 1.
        { eapply gsim_Take_src with (X := False);
          [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss.
        }

        eapply gsim_Choose_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        intros [[mtid_t1 stid_t1] Hmtid_t1]; rewrite list_insert_insert. ghcNormT; ss.
        eapply gsim_Choose_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        exists (exist _ (mtid_t1, stid_t1) Hmtid_t1); rewrite list_insert_insert. ghcNormS; ss.

        eapply gsim_SPut_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
        rewrite list_insert_insert. ghcNormS.
        eapply map_Forall_insert_union_with with (k:=SchI.v_tid) in Hst1 as Hst1'; revert Hst1'.
        repeat match goal with
        | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
          state_insert_simpl k1 v1 H
        end.
        intros Hst1'.

        eapply gsim_SPut_tgt;
          [lookup_tac; s; do 2 f_equal; hnorm_itr|exact Hst2|]; s.
        rewrite list_insert_insert. ghcNormT.
        pose proof Hst1' as Hst2'.

        eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        rewrite !list_insert_insert.

        eapply gsim_Yield_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
        rewrite list_insert_insert. ghcNormS.
        eapply GSimAux.gsim_Yield_tgt; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
        rewrite list_insert_insert. ghcNormT. ired.

        zprogress. gbase. eapply (CIH rt rs); eauto.
        eexists (<[stid := (_, _, None)]> tl); esplits; eauto.
          { assert (Hvtid : is_Some
              (({[SchI.v_ths # ths↑; SchI.v_tid # mtid↑]}
                : gmap key (option Any.t)) !! SchI.v_tid)).
          { rewrite lookup_insert_ne ?lookup_insert //; ii; clarify. }
          rewrite (insert_union_with_l' _ _ _ _ Hst1 Hvtid).
          rewrite insert_commute; [rewrite insert_insert //|ii; clarify]. }
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { eapply reqmap_rel_id; eauto. }
        { intros i; destruct (decide (i = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify. }
        }
        { assert (Hvtid : is_Some
              (({[SchI.v_ths # ths↑; SchI.v_tid # mtid↑]}
                : gmap key (option Any.t)) !! SchI.v_tid)).
          { rewrite lookup_insert_ne ?lookup_insert //; ii; clarify. }
          rewrite (insert_union_with_l' _ _ _ _ Hst1 Hvtid).
          rewrite insert_commute; [rewrite insert_insert; exact Hst1'|ii; clarify].
        }
      }
      { (* SchI.join *)
        revert Htid; rewrite prog_s_join; auto using wf_src; rewrite prog_t_join //.
        rewrite /join; ired; do 2 rewrite -interpV_bind; intros Htid.

        eapply gsim_tau_src; [rewrite list_lookup_fmap // Htid; s; do 2 f_equal; hnorm_itr|].
        eapply gsim_tau_tgt; [rewrite list_lookup_fmap // Htid; s; do 2 f_equal; hnorm_itr|].
        zprogress.

        rewrite /cfunU /SchI.join.
        destruct Any.downcast as [n|]; s; ghcNormS; cycle 1.
        { eapply gsim_Take_src with (X := False);
          [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss.
        }
        ghcNormT.

        rewrite unfold_iterC; ired.
        eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        rewrite !list_insert_insert.

        eapply gsim_SGet_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
        rewrite list_insert_insert.
        match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst1 end. ghcNormS.

        eapply gsim_SGet_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
        rewrite list_insert_insert.
        match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst2 end. ghcNormT.

        destruct (ths !! n) as [[? [rv|]]|] eqn : Hret; rewrite Hret /=; ghcNormS; ghcNormT.
        { (* Join-return *)
          zprogress; gbase. eapply (CIH rt rs); eauto.
          eexists (<[stid := (_, _, None)]> tl); esplits; eauto.
          { rewrite list_fmap_insert //=. }
          { rewrite list_fmap_insert //=. }
          { eapply reqmap_rel_id; eauto. }
          { intros i; destruct (decide (i = stid)); subst; cycle 1.
            { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
            { rewrite list_lookup_insert; ii; clarify. }
          }
        }
        { (* Join-loop *)
          rewrite /ccallU !lookup_empty.
          eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          rewrite !list_insert_insert.

          ghcNormS. ghcNormT.
          destruct (decide (fn_name SchHdr.yield ∈ msk)) as [Hspawnmsk|Hspawnmsk].
          { ghcNormS. case_bool_decide as a; des; first set_solver+a Hspawnmsk.
            s. eapply gsim_Take_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
            done.
          }
          eapply gsim_Call_src.
          { lookup_tac; s; do 2 f_equal. etrans; first hnorm_itr.
            case_bool_decide as a; des; last (exfalso; apply a; split; ss).
            s. hnorm_itr.
          }
          eapply gsim_Call_tgt.
          { lookup_tac; s; do 2 f_equal. etrans; first hnorm_itr.
            case_bool_decide as a; des; last (exfalso; apply a; split; ss).
            s. hnorm_itr.
          }
          rewrite !list_insert_insert. ghcNormT.

          zprogress.
          gbase. eapply (CIH rt rs); eauto.
          eexists (<[stid := (_, _, None)]> tl); esplits; eauto.
          { rewrite list_fmap_insert //=. }
          { rewrite list_fmap_insert //=. }
          { eapply reqmap_rel_id; eauto. }
          { intros i1; destruct (decide (i1 = stid)); subst; cycle 1.
            { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
            { rewrite list_lookup_insert; ii; clarify.
              split; ss. eapply (help_rel_call _ _ _ _ ctx rs rt
                (SchHdr.yield.1)); eauto.
              { set_solver-. }
              intros ret; ss.
              eapply (help_rel_join _ _ ret _ _ n); eauto.
              { rewrite /join_pend /ccallU. f_equal.
                do 3 (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
                repeat f_equal; extensionalities a; destruct a; grind.
                repeat f_equal; extensionalities a; grind.
              }
              { rewrite /join_pend /ccallU. f_equal.
                do 3 (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
              }
            }
          }
        }

        (* join-None *)
        zprogress.
        gbase. eapply (CIH rt rs); eauto.
        eexists (<[stid := (_, _, None)]> tl); esplits; eauto.
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { eapply reqmap_rel_id; eauto. }
        { intros i; destruct (decide (i = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify. }
        }
      }
    }
    { (* inner spawn - continuation *)
      rewrite /inner_spawn_pend in Htid.
      eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].

      destruct Any.downcast as [n|]; s; ghcNormS; cycle 1.
      { eapply gsim_Take_src with (X := False);
        [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss.
      }
      ghcNormT.

      eapply gsim_SGet_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
      rewrite list_insert_insert.
      match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst1 end. ghcNormS.

      eapply gsim_SGet_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
      rewrite list_insert_insert.
      match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst1 end. ghcNormS.

      eapply gsim_SGet_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
      rewrite list_insert_insert.
      match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst2 end. ghcNormT.

      eapply gsim_SGet_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
      rewrite list_insert_insert.
      match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst2 end. ghcNormT.

      destruct (ths !! mtid) as [[? ?]|] eqn : Hmtid;
        rewrite Hmtid; ghcNormS; ghcNormT; cycle 1.
      { eapply gsim_Take_src with (X := False);
        [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss.
      }

      eapply gsim_SPut_src; auto; [lookup_tac; s; do 2 f_equal; hnorm_itr|]; s.
      rewrite list_insert_insert. ghcNormS.
      eapply map_Forall_insert_union_with in Hst1 as Hst1'; revert Hst1'.
      repeat match goal with
      | H : map_Forall _ ?a |- context [base.insert ?k1 (Some ?v1) ?a] =>
        state_insert_simpl k1 v1 H
      end.
      intros Hst1'.

      eapply gsim_SPut_tgt;
        [lookup_tac; s; do 2 f_equal; hnorm_itr|exact Hst2|]; s.
      rewrite list_insert_insert. ghcNormT.
      pose proof Hst1' as Hst2'.

      zprogress. gbase. eapply (CIH rt rs); eauto.
      eexists (<[stid := (_, _, None)]> tl); esplits; eauto.
      { assert (Hvths : is_Some
            (({[SchI.v_ths # ths↑; SchI.v_tid # mtid↑]}
              : gmap key (option Any.t)) !! SchI.v_ths)).
        { rewrite lookup_insert; eauto. }
        rewrite (insert_union_with_l' _ _ _ _ Hst1 Hvths) insert_insert //. }
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      { eapply reqmap_rel_id; eauto. }
      { intros stid2; destruct (decide (stid2 = stid)); subst; cycle 1.
        { intros itr_s2 itr_t2 no2; rewrite list_lookup_insert_ne //=.
          intros Hi; pose proof Hi as Hi'; revert Hi'; intros [Hi1 Hi2]%Hlookup; split; eauto.
          destruct no2 as [[[[tid2 [?| |?]] ?]|]|]; ss;
          destruct Hi2 as [mtid2 [ro2 Hi2]]; apply lookup_lt_Some in Hi2 as Hlen2;
            destruct (decide (mtid2 = mtid)); subst.
          { rewrite Hi2 in Hmtid; clarify. eexists mtid, (Some _); rewrite list_lookup_insert //. }
          { exists mtid2, ro2; rewrite list_lookup_insert_ne //. }
          { rewrite Hi2 in Hmtid; clarify. eexists mtid, (Some _); rewrite list_lookup_insert //. }
          { exists mtid2, ro2; rewrite list_lookup_insert_ne //. }
        }
        { rewrite list_lookup_insert; ii; clarify. split; ss.
          eapply help_rel_terminate; eauto.
          { f_equal; symmetry; hnorm_itr. }
          { f_equal; etrans; first hnorm_itr; symmetry; hnorm_itr. }
        }
      }
      { assert (Hvths : is_Some
            (({[SchI.v_ths # ths↑; SchI.v_tid # mtid↑]}
              : gmap key (option Any.t)) !! SchI.v_ths)).
        { rewrite lookup_insert; eauto. }
        rewrite (insert_union_with_l' _ _ _ _ Hst1 Hvths) insert_insert.
        exact Hst1'.
      }
    }
    { (* join - continuation *)
      rewrite /join_pend in Htid.
      eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].

      destruct Any.downcast as [n|]; s; ghcNormS; cycle 1.
      { eapply gsim_Take_src with (X := False);
        [lookup_tac; s; do 2 f_equal; hnorm_itr|]; ss.
      }
      ghcNormT.

      rewrite unfold_iterC; ired.
      eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      rewrite !list_insert_insert.

      eapply gsim_SGet_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
      rewrite list_insert_insert.
      match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst1 end. ghcNormS.

      eapply gsim_SGet_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|auto|]; s.
      rewrite list_insert_insert.
      match goal with | |- context[?st !! ?k] => state_lookup_simpl st k Hst2 end. ghcNormT.

      destruct (ths !! tid) as [[? [rv|]]|] eqn : Hret; rewrite Hret /=.
      { (* Join-return *)
        ghcNormS; ghcNormT.
        zprogress. gbase. eapply (CIH rt rs); eauto.
        eexists (<[stid := (_, _, None)]> tl); esplits; eauto.
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { eapply reqmap_rel_id; eauto. }
        { intros i; destruct (decide (i = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify. }
        }
      }
      { (* Join-loop *)
        rewrite /ccallU. ghcNormS; ghcNormT.
        rewrite !lookup_empty.
        eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        rewrite !list_insert_insert.

        ghcNormS; ghcNormT.
        destruct (decide (fn_name SchHdr.yield ∈ msk)) as [Hspawnmsk|Hspawnmsk].
        { ghcNormS. case_bool_decide as a; des; first set_solver+a Hspawnmsk.
          s. eapply gsim_Take_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
          done.
        }
        eapply gsim_Call_src.
        { lookup_tac; s; do 2 f_equal. etrans; first hnorm_itr.
          case_bool_decide as a; des; last (exfalso; apply a; split; ss).
          s. hnorm_itr.
        }
        eapply gsim_Call_tgt.
        { lookup_tac; s; do 2 f_equal. etrans; first hnorm_itr.
          case_bool_decide as a; des; last (exfalso; apply a; split; ss).
          s. hnorm_itr.
        }
        rewrite !list_insert_insert. ghcNormS. ghcNormT.

        zprogress. gbase. eapply (CIH rt rs); eauto.
        eexists (<[stid := (_, _, None)]> tl); esplits; eauto.
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { eapply reqmap_rel_id; eauto. }
        { intros i1; destruct (decide (i1 = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify.
            split; ss. eapply (help_rel_call _ _ _ _ ctx rs rt
              (SchHdr.yield.1)); eauto.
            { set_solver-. }
            intros ret; ss; eapply (help_rel_join _ _ ret _ _ tid); eauto.
            { rewrite /join_pend /ccallU. f_equal.
              do 3 (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
              repeat f_equal; extensionalities a; destruct a; grind.
              repeat f_equal; extensionalities a; grind.
            }
            { rewrite /join_pend /ccallU. f_equal.
              do 3 (etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr; grind).
              repeat f_equal; extensionalities a; destruct a; grind.
              repeat f_equal; extensionalities a; grind.
            }
          }
        }
      }

      (* join-None *)
      ghcNormS; ghcNormT.
      zprogress. gbase. eapply (CIH rt rs); eauto.
      eexists (<[stid := (_, _, None)]> tl); esplits; eauto.
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      { eapply reqmap_rel_id; eauto. }
      { intros i; destruct (decide (i = stid)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify. }
      }
    }
    { (* inner_spawn - continuation *)
      revert Htid; rewrite /Sch.terminate; unseal SCH; rewrite unfold_iterC; intros Htid.
      eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].

      ghcNormS; ghcNormT.
      rewrite !lookup_empty.
      eapply gsim_tau_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      eapply gsim_tau_tgt; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
      rewrite !list_insert_insert.

      ghcNormS; ghcNormT.
      destruct (decide (fn_name SchHdr.yield ∈ msk)) as [Hspawnmsk|Hspawnmsk].
      { ghcNormS. case_bool_decide as a; des; first set_solver+a Hspawnmsk.
        s. eapply gsim_Take_src; [lookup_tac; s; do 2 f_equal; hnorm_itr|].
        done.
      }
      eapply gsim_Call_src.
      { lookup_tac; s; do 2 f_equal. etrans; first hnorm_itr.
        case_bool_decide as a; des; last (exfalso; apply a; split; ss).
        s. hnorm_itr.
      }
      eapply gsim_Call_tgt.
      { lookup_tac; s; do 2 f_equal. etrans; first hnorm_itr.
        case_bool_decide as a; des; last (exfalso; apply a; split; ss).
        s. hnorm_itr.
      }
      ghcNormS. ghcNormT. rewrite !list_insert_insert.

      zprogress. gbase. eapply (CIH rt rs); eauto.
      eexists (<[stid := (_, _, None)]> tl); esplits; eauto.
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      { eapply reqmap_rel_id; eauto. }
      { intros i1; destruct (decide (i1 = stid)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify.
          split; last ss.
          eapply (help_rel_call _ _ _ _ ctx rs rt (SchHdr.yield.1));
            eauto.
          { set_solver-. }
          i; s.
          eapply help_rel_eq with (itr := tau;; Ret ()↑).
          { f_equal. symmetry. etrans; first hnorm_itr. do 2 f_equal.
            lazymatch goal with
            | |- _ = ?rhs => instantiate (1 := λ _, rhs)
            end.
            etrans; first hnorm_itr; symmetry; hnorm_itr.
          }
          { f_equal. symmetry. etrans; first hnorm_itr. do 2 f_equal.
            lazymatch goal with
            | |- _ = ?rhs => instantiate (1 := λ _, rhs)
            end.
            etrans; first hnorm_itr; symmetry; hnorm_itr.
          }
          { instantiate (1:=msk_scp [] msk_true); split; ii; ss. }
          { ii; clarify. }
          i; ss.
          eapply help_rel_terminate; eauto; rewrite /Sch.terminate; unseal SCH.
          { f_equal; etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr.
            repeat f_equal; extensionalities a; destruct a; grind.
          }
          { f_equal; etrans; first hnorm_itr; symmetry; etrans; first hnorm_itr.
            repeat f_equal; extensionalities a; destruct a; grind.
          }
        }
      }
    }
  (*SLOW*)Qed.
End HelpingOnOff.
