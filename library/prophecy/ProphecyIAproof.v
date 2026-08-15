From CRIS.common Require Import CRIS.
From CRIS.modules Require Import Mod LMod.
From CRIS.prophecy Require Export ProphecyHeader ProphecyI ProphecyA.
From CRIS.prophecy Require Import ExtendedBehavior SimGEx.
From CRIS.lib Require Import exco_stream.
From stdpp Require Import base strings.

Module ProphIA. Section ProphIA.
  Context `{_crisG : !crisG Γ Σ α β τ _I _S, _PROPH : !prophGS}.

  Variant _take_is_prop (coself : itree (lmodE Σ) Any.t -> Prop)
      : itree (lmodE Σ) Any.t -> Prop :=
  | take_is_prop_ret retv
  : _take_is_prop coself (Ret retv)

  | take_is_prop_tau itr
    (NEXT: coself itr)
  : _take_is_prop coself (tau;; itr)

  | take_is_prop_callE X (e : callE X) ktr
    (NEXT: forall x, coself (ktr x))
  : _take_is_prop coself (x <- trigger e;; ktr x)

  | take_is_prop_stateE X (e : lstateE Σ X) ktr
    (NEXT: forall x, coself (ktr x))
  : _take_is_prop coself (x <- trigger e;; ktr x)

  | take_is_prop_choose X ktr
    (NEXT: forall x, coself (ktr x))
  : _take_is_prop coself (x <- trigger (Choose X);; ktr x)

  | take_is_prop_take (X : Type) ktr
    (e : ∃ P : Prop, X = P)
    (NEXT: forall x : X, coself (ktr x))
  : _take_is_prop coself (p <- trigger (Take X);; ktr p)

  | take_is_prop_io I O fn (args : I) ktr
    (NEXT: forall o : O, coself (ktr o))
  : _take_is_prop coself (o <- trigger (IO fn args);; ktr o).

  Definition take_is_prop := paco1 _take_is_prop bot1.

  Lemma take_is_prop_mon : monotone1 _take_is_prop.
  Proof using.
    ii. destruct IN; des; eauto using _take_is_prop.
  Qed.

  Hint Unfold take_is_prop : core.
  Hint Constructors _take_is_prop : core.
  Hint Resolve take_is_prop_mon: paco.

  Definition thread_rel :
      itree (lmodE Σ) Any.t -> (bool * itree (lmodE Σ) Any.t) -> Prop :=
    fun itr_src '(b, itr_tgt) =>
      if b then
        (exists (fn : string) (arg : Any.t)
            (itr_cont : itree (lmodE Σ) Any.t),
          (itr_tgt = trigger (@IO Any.t () fn arg);;; tau;; tau;; itr_cont)
          /\ itr_src = tau;; tau;; itr_cont)
        \/
        exists (fn : string) (arg : Any.t),
          (itr_tgt = trigger (@IO Any.t () fn arg);;; tau;; Ret tt↑)
          /\ itr_src = tau;; Ret tt↑
      else itr_src = itr_tgt.

  Lemma thread_rel_load
      thl_src thl_tgt
      (WF : Forall2 thread_rel thl_src thl_tgt) :
    forall n itr_src, thl_src !! n = Some itr_src ->
      exists bitr_tgt, <<TGTITR : thl_tgt !! n = Some bitr_tgt>> /\<<WFITR : thread_rel itr_src bitr_tgt>>.
  Proof using Type.
    induction WF; i; ss. destruct n; ss; clarify; et.
  Qed.

  Lemma take_is_prop_load
      thl
      (WF : Forall take_is_prop thl) :
    forall n itr, thl !! n = Some itr -> <<WFITR : take_is_prop itr>>.
  Proof using Type.
    induction WF; i; ss. destruct n; ss; clarify; et.
  Qed.

  Lemma take_is_prop_bind itr ktr
      (F : take_is_prop itr)
      (S : forall x, take_is_prop (ktr x)) :
    take_is_prop (itr >>= ktr).
  Proof using Type.
    revert itr F. pcofix CIH. i. ides itr; grind.
    - eapply paco1_mon; try apply S. i. ss.
    - pfold. econs. right. apply CIH. punfold F. inv F; try itree_clarify H0.
      pclearbot. et.
    - destruct e; try destruct s.
      + rewrite vis_trigger bind_bind. pfold. econs. i. right.
        apply CIH. rewrite vis_trigger in F. punfold F. inv F; try itree_clarify H0.
        pclearbot. et.
      + rewrite vis_trigger bind_bind. pfold. econs. i. right.
        apply CIH. rewrite vis_trigger in F. punfold F. inv F; try itree_clarify H0.
        pclearbot. et.
      + destruct c.
        * rewrite vis_trigger bind_bind. pfold. econs. i. right.
          apply CIH. rewrite vis_trigger in F. punfold F. inv F; try itree_clarify H0.
          pclearbot. et.
        * rewrite vis_trigger bind_bind. pfold.
          rewrite vis_trigger in F. punfold F. inv F; try itree_clarify H0.
          econs; et. i. right. apply CIH. pclearbot. et.
        * rewrite vis_trigger bind_bind. pfold. econs. i. right.
          apply CIH. rewrite vis_trigger in F. punfold F. inv F; try itree_clarify H0.
          pclearbot. et.
  Qed.

  Context (md : Mod.t) (Hreal : real_mod md) (mn : string).

  Lemma mod_take_is_prop r fn i arg :
    (Mod.to_lmod (md ★ ProphecyI.t mn) r).(LMod.fnsems) !! fn = Some i →
    take_is_prop (i arg).
  Proof using Hreal.
    dup Hreal.
    rewrite /LMod.fnsems /Mod.to_lmod ?lookup_fmap lookup_omap.
    destruct (_ _ !! fn) as [[[msk bd]|]|] eqn : Hfn; ss.
    assert ((∀ P, msk _ (subevent _ (Assume P)) = false) ∧
      ∀ X, msk _ (subevent _ (Take X)) = true → ∃ (P : Prop), X = P).
    { rewrite lookup_union_with ?lookup_fmap in Hfn.
      destruct (_ !! fn) as [[[? ?]|]|] eqn : ?; ss; simplify_eq.
      { destruct (ProphecyI.fnsems mn !! fn); ss.
        rewrite /real_mod map_Forall_lookup in Hreal0; eapply Hreal0 in Heqo; ss.
        rewrite /SModTr.trans_fnsem in Hfn; clarify.
      }
      { repeat destruct (_ !! fn); ss. }
      { revert Hfn; rewrite /ProphecyI.fnsems.
        let rec go :=
        try match goal with
        | |- context [(<[?i := _]> _) !! ?k] =>
          destruct (decide (i = k)); [subst; rewrite lookup_insert; ss|rewrite lookup_insert_ne; go]
        | |- context [({[?i := _]}) !! ?k] =>
          destruct (decide (i = k)); [subst; rewrite lookup_insert; ss|rewrite lookup_insert_ne; go]
        end in go; i; clarify; ss; split; ss; intros ?;
        match goal with
        | |- context [excluded_middle_informative ?P] =>
          destruct (excluded_middle_informative P) as [?|?]; ss
        end.
      }
    }
    clear Hfn. i; clarify.
    rewrite /SB.sandbox_body /ModTr.trans_fnsem /= /ModTr.trans.
    generalize (bd arg). clear -H. pcofix CIH. i. ides i.
    - rewrite SBRed.ret interpV_ret. pfold. econs.
    - rewrite SBRed.tau interpV_tau. pfold. econs. right. et.
    - rewrite SBRed.vis; des_ifs; [|rewrite interpV_vis; ss; grind; pfold; econs; eauto; ss].
      destruct e; simpl.
      + destruct a; des_ifs; ss.
        * destruct H as [H ?]; rewrite H in Heq; ss.
        * rewrite interpV_vis; ss; grind.
          pfold. econs. i. left. grind.
          grind. unfold guarantee, assume.
          pfold. grind. econs.
          { esplits; eauto. }
          i. left. unfold ModTr.put_res. grind.
          pfold. econs. i. left. grind.
          grind. pfold. econs. i. right. grind.
        * rewrite interpV_vis; ss; grind.
          pfold. econs. i. left. grind.
          grind. pfold. econs. i. left.
          unfold guarantee, ModTr.put_res. grind. pfold. econs. i. left.
          grind. pfold. econs. i. left. grind.
          grind. pfold. econs. i.
          right. et.
      + destruct s; des_ifs; try destruct p; try destruct c; ss;
        try by (rewrite interpV_vis /=; grind; pfold; econs; i; grind; right; eauto).
        destruct s.
        * destruct p.
          { rewrite interpV_vis; grind; pfold; econs; i.
            grind. left; pfold; econs; i; right. eauto.
          }
          { rewrite interpV_vis; grind; pfold; econs; i.
            grind; eauto.
          }
        * destruct c.
          { rewrite interpV_vis /=; grind; pfold; econs; i; grind; right; eauto. }
          { rewrite interpV_vis /=; grind; pfold; econs; eauto.
            { destruct (excluded_middle_informative _); et.
              bsimpl. eapply H. et. }
            { i; grind; right; eauto. }
          }
          { rewrite interpV_vis /=; grind; pfold; econs; i; grind; right; eauto. }
  (*SLOW*)Qed.

  (* Lemma map_fst_snd {A B C: Type} (l : list (A * B)) (f: B -> C):
    List.map fst (List.map (map_snd f) l)
     = List.map fst l.
  Proof using Type. induction l; ss. destruct a. ss. rewrite IHl. ss. Qed. *)

  Lemma mod_proph_comp_sim
      (WF : Mod.wf (md ★ ProphecyI.t mn)) :
    forall arg r,
      comp_sim
        (LMod.compile (Mod.to_lmod (md ★ ProphecyI.t mn) r) arg)
        (proph_compile (Mod.to_lmod (md ★ ProphecyI.t mn) r) mn arg).
  Proof using Hreal.
    ii.
    unfold LMod.compile, proph_compile. ss.
    unfold ITree.map.
    unfold LModTr.trans, proph_trans.
    unfold unwrapU. des_ifs; cycle 1.
    { unfold triggerUB. grind. pfold. econs. clarify. }
    ired. unfold LModTr.interp_stateE, LModTr.interp_callE, proph_interp_callE.
    assert (Forall2 thread_rel [i arg] [(false, i arg)]).
    { econs; last econs. ss. }
    assert (Forall take_is_prop [i arg]).
    { econs; last econs. unshelve eapply mod_take_is_prop; et. }
    assert (Forall take_is_prop (snd <$> [(false, i arg)])%stdpp).
    { econs; last econs. ss. unshelve eapply mod_take_is_prop; et. }
    clear Heq.
    set (t := (_, r)).
    clearbody t. revert H H0 H1.
    generalize [i arg]. generalize [(false, i arg)].
    generalize 0. revert t. clear -WF Hreal.
    pcofix CIH. i. do 2 rewrite unfold_iterV. ss.
    destruct (l0 !! n) eqn:E; cycle 1.
    { ired. apply List.Forall2_length in H0.
      assert (l !! n = None).
      { apply lookup_ge_None_1 in E. rewrite H0 in E. apply lookup_ge_None_2 in E. ss. }
      rewrite H. unfold itreeV_itree. rewrite interp_state_tau. grind. pfold. econs.
      econs. pfold. unfold LModTr.pure_state. grind. econs. i; ss. }
    dup H0.
    eapply thread_rel_load in H0; et. des. rewrite TGTITR. destruct bitr_tgt.
    red in WFITR. destruct b. des.
    - clarify. ss. grind. pfold.
      rewrite /LModTr.pure_state. ired.
      under ( bind_extk (λ (_: unit), ITree.bind _ _) ) => m.
      { rewrite bind_ret_l. rewrite bind_tau. rewrite bind_ret_l.
        rewrite ! bind_ret_l. ss. rewrite unfold_iterV.
        ss. rewrite list_lookup_insert.
        2:{ apply lookup_lt_is_Some. et. }
        ss. rewrite bind_tau.
        rewrite interp_state_tau. rewrite bind_tau.
        over. }
      econs. ss. grind.
      rewrite list_insert_insert. right. eapply CIH; et.
      apply Forall2_insert. ss.
      ss.
      apply Forall_insert; ss.
      rewrite Forall_lookup in H2.
      specialize (H2 n).
      hexploit H2. { rewrite list_lookup_fmap_Some. et. } ss. i.
      punfold H. inv H; itree_clarify H4. specialize (NEXT tt).
      pclearbot. punfold NEXT. inv NEXT; try itree_clarify H0. pclearbot.
      apply NEXT0. rewrite list_fmap_insert. ss.
      apply Forall_insert; ss. rewrite Forall_lookup in H2.
      specialize (H2 n).
      hexploit H2. { rewrite list_lookup_fmap_Some. et. } ss. i.
      punfold H. inv H; itree_clarify H4. specialize (NEXT tt).
      pclearbot. punfold NEXT. inv NEXT; try itree_clarify H0. pclearbot.
      apply NEXT0.
    - clarify. ss. grind. pfold.
      rewrite /LModTr.pure_state. ired.
      under ( bind_extk (λ (_: unit), ITree.bind _ _) ) => m.
      { rewrite bind_ret_l. rewrite bind_tau. rewrite bind_ret_l.
        rewrite ! bind_ret_l. ss. rewrite unfold_iterV.
        ss. rewrite list_lookup_insert.
        2:{ apply lookup_lt_is_Some. et. }
        ss. rewrite bind_tau.
        rewrite interp_state_tau. rewrite bind_tau.
        over. }
      econs. grind. rewrite list_insert_insert. left. do 2 rewrite unfold_iterV.
      ss. rewrite -> list_lookup_insert by now apply lookup_lt_is_Some; et.
      rewrite -> list_lookup_insert by now apply lookup_lt_is_Some; et. ss. grind.
      pfold. econs. left.
      destruct (Nat.eq_dec n 0).
      + grind. pfold. econs.
      + grind. pfold. econs. i. clarify.
    - ides (i0); grind; pfold; try econs.
      + destruct (Nat.eq_dec). grind.
        (* Ret *) econs; pfold; econs.
        (* UB *) unfold triggerUB. rewrite interp_state_bind interp_state_trigger.
        grind. econs. rewrite /LModTr.pure_state.
        grind. pfold; econs. i; ss.
      + (* tau *)
        right. eapply CIH; et.
        apply Forall2_insert; et; ss.
        apply Forall_insert; et; ss.
        exploit Forall_lookup_1. apply H1. apply E.
        i. punfold x0. inv x0; et; try itree_clarify H0.
        pclearbot. eapply NEXT.
        rewrite list_fmap_insert; ss.
        apply Forall_insert; et; ss.
        rewrite Forall_lookup in H2.
        exploit (H2). rewrite list_lookup_fmap_Some. et.
        i. punfold x0. inv x0; et; try itree_clarify H0.
        pclearbot. eapply NEXT.
      + (* Vis *) destruct e; try destruct c; try destruct s; cycle 3; grind.
        3: destruct c.
        * (* GetTid *)
          econs. right. eapply CIH; et.
          apply Forall2_insert; et; ss.
          apply Forall_insert; et; ss.
          exploit Forall_lookup_1. apply H1. apply E.
          i. punfold x0. inv x0; et; try itree_clarify H0.
          pclearbot. ired.
          eapply NEXT.
          rewrite list_fmap_insert; ss.
          apply Forall_insert; et; ss.
          rewrite Forall_lookup in H2.
          exploit (H2). rewrite list_lookup_fmap_Some. et.
          i. punfold x0. inv x0; et; try itree_clarify H0.
          pclearbot. ired. eapply NEXT.
        *  (* StateE *)
          destruct l1.
          ired. econs. right. eapply CIH; et.
          apply Forall2_insert; et; ss.
          apply Forall_insert; et; ss.
          exploit Forall_lookup_1. apply H1. apply E.
          i. punfold x0. inv x0; et; try itree_clarify H0.
          pclearbot. ired.
          eapply NEXT.
          rewrite list_fmap_insert; ss.
          apply Forall_insert; et; ss.
          rewrite Forall_lookup in H2.
          exploit (H2). rewrite list_lookup_fmap_Some. et.
          i. punfold x0. inv x0; et; try itree_clarify H0.
          pclearbot. ired. eapply NEXT.
        * (* Choose *)
          ired. unfold LModTr.pure_state at 1 4.
          grind. econs. i. ired. econs. pfold; econs.
          right. eapply CIH.
          apply Forall2_insert; et; ss.
          apply Forall_insert; et; ss.
          exploit Forall_lookup_1. apply H1. apply E.
          i. punfold x1. inv x1; et; try itree_clarify H0.
          pclearbot. ired.
          eapply NEXT.
          rewrite list_fmap_insert; ss.
          apply Forall_insert; et; ss.
          rewrite Forall_lookup in H2.
          exploit (H2). rewrite list_lookup_fmap_Some. et.
          i. punfold x1. inv x1; et; try itree_clarify H0.
          pclearbot. ired. eapply NEXT.
        * (* Take *)
          unfold LModTr.pure_state at 1 4.
          grind. exploit Forall_lookup_1. apply H1. apply E. i.
          punfold x0. rewrite <- bind_trigger in x0.
          assert (∃ (P : Prop), X = P).
          { inv x0; try itree_clarify H0. et. }
          des; subst. econs. i.
          ired. econs; pfold; econs.
          right. eapply CIH.
          apply Forall2_insert; et; ss.
          apply Forall_insert; et; ss.
          exploit Forall_lookup_1. apply H1. apply E.
          i. punfold x2. inv x2; et; des; subst; try itree_clarify H0.
          pclearbot. ired.
          eapply inj_pair2 in H. clarify.
          rewrite list_fmap_insert; ss.
          apply Forall_insert; et; ss.
          rewrite Forall_lookup in H2.
          exploit (H2). rewrite list_lookup_fmap_Some. et.
          i. punfold x2. inv x2; et; des; subst; try itree_clarify H0.
          pclearbot. ired.
          eapply inj_pair2 in H. subst; ss.
        * (* IO *)
          unfold LModTr.pure_state at 1 4.
          grind. econs. i. ired.
          econs. pfold; econs; ss.
          right. eapply CIH.
          apply Forall2_insert; et; ss.
          apply Forall_insert; et; ss.
          exploit Forall_lookup_1. apply H1. apply E.
          i. punfold x1. inv x1; et; try itree_clarify H0.
          pclearbot. ired. eapply NEXT.
          rewrite list_fmap_insert; ss.
          apply Forall_insert; et; ss.
          rewrite Forall_lookup in H2.
          exploit (H2). rewrite list_lookup_fmap_Some. et.
          i. punfold x1. inv x1; et; try itree_clarify H0.
          pclearbot. ired. eapply NEXT.
        * (* Call *)
          econs.
          rewrite {1 3}/LMod.prog; destruct (_ !! (funid fn)) eqn: EE; ss; cycle 1.
          { unfold triggerUB.
            rewrite interp_state_bind.
            grind. unfold LModTr.pure_state. grind.
            econs. pfold. econs. i. ss. }
          grind. right. eapply CIH.
          { apply Forall2_insert; et; ss.
            unfold thread_rel. destruct decide; et.
            left. eapply lookup_fmap_Some in EE as [? [<- EE]].
            eapply lookup_fmap_Some in EE as [? [<- EE]].
            eapply lookup_omap_id_Some in EE.
            apply lookup_union_with_Some in EE as [[? EE] | [[? EE] | ]].
            { des; subst; rewrite /ProphecyI.fnsems in EE;
              rewrite !lookup_fmap in EE;
              repeat (rewrite lookup_insert in EE || rewrite lookup_insert_ne // in EE); ss.
            }
            { rewrite /Mod.fnsems /= /ProphecyI.fnsems in EE; des; subst;
              ss; simpl_map; ss; clarify;
              rewrite /ModTr.trans_fnsem /ModTr.trans /SB.sandbox_body /SModTr.trans_fnsem /=;
                esplits; rewrite /ProphecyI.new /ProphecyI.resolve /ProphecyI.close
                ?SBRed.tau ?interpV_tau ?SRed.ret ?SBRed.ret ?interpV_ret; grind.
            }
            { des; clarify. }
          }
          { apply Forall_insert; et. apply take_is_prop_bind.
            unshelve eapply mod_take_is_prop; et. i. pfold. econs. left.
            eapply Forall_lookup_1 in H2; cycle 1.
            { rewrite list_lookup_fmap. rewrite -> TGTITR. ss. }
            punfold H2. inv H2; try itree_clarify H0. grind.
            pclearbot. et. }
          { rewrite list_fmap_insert. apply Forall_insert; et.
            eapply Forall_lookup_1 in H1; [|et].
            punfold H1. inv H1; try itree_clarify H0. pclearbot.
            destruct decide; ss.
            - pfold. econs. i. left. apply take_is_prop_bind.
              unshelve eapply mod_take_is_prop; et. i. pfold. econs. left. grind.
            - apply take_is_prop_bind. unshelve eapply mod_take_is_prop; et.
              i. pfold. econs. left. grind. }
        * (* Spawn *)
          econs.
          rewrite {1 3}/LMod.prog; destruct (_ !! (funid fn)) eqn: EE; ss; cycle 1.
          { unfold triggerUB.
            rewrite interp_state_bind.
            grind. unfold LModTr.pure_state. grind.
            econs. pfold. econs. i. ss. }
          grind. right. eapply CIH.
          { apply Forall2_app.
            { apply Forall2_insert; et; ss. apply Forall2_length in H3. rewrite H3; ss. }
            econs; last econs. destruct decide; ss.
            right. eapply lookup_fmap_Some in EE as [? [<- EE]].
            eapply lookup_fmap_Some in EE as [? [<- EE]].
            eapply lookup_omap_id_Some in EE.
            apply lookup_union_with_Some in EE as [[? EE] | [[? EE] | ]].
            { des; subst; rewrite /ProphecyI.fnsems in EE; ss;
              rewrite !lookup_fmap in EE;
              repeat (rewrite lookup_insert in EE || rewrite lookup_insert_ne // in EE); ss. }
            { rewrite /Mod.fnsems /= /ProphecyI.fnsems /= in EE; des; subst; ss; simpl_map; ss; clarify;
              rewrite /ModTr.trans_fnsem /ModTr.trans /SB.sandbox_body /SModTr.trans_fnsem /=;
                esplits; rewrite /ProphecyI.new /ProphecyI.resolve /ProphecyI.close
                ?SBRed.tau ?interpV_tau SRed.ret SBRed.ret interpV_ret; grind.
            }
            { des; clarify. }
          }
          { eapply Forall_lookup_1 in E; et. punfold E.
            inv E; try itree_clarify H0. pclearbot. grind.
            apply Forall_app. split. apply Forall_insert; et.
            econs; last econs. eapply mod_take_is_prop; et. }
          { eapply Forall_lookup_1 in E; et. punfold E.
            inv E; try itree_clarify H0. pclearbot. grind.
            rewrite fmap_app. ss. apply Forall_app.
            rewrite list_fmap_insert. ss. split.
            apply Forall_insert; et. econs; last econs.
            destruct decide; ss.
            - pfold. econs. i. left. eapply mod_take_is_prop; et.
            - eapply mod_take_is_prop; et. }
          Unshelve. all : et.
        * (* Yield *)
          econs. right. eapply CIH; et.
          apply Forall2_insert; et; ss.
          apply Forall_insert; et; ss.
          exploit Forall_lookup_1. apply H1. apply E.
          i. punfold x0. inv x0; et; try itree_clarify H0.
          pclearbot. ired.
          eapply NEXT.
          rewrite list_fmap_insert; ss.
          apply Forall_insert; et; ss.
          rewrite Forall_lookup in H2.
          exploit (H2). rewrite list_lookup_fmap_Some. et.
          i. punfold x0. inv x0; et; try itree_clarify H0.
          pclearbot. ired. eapply NEXT.
  (*SLOW*)Qed.

  Lemma prophecy_tgt_exbeh_exists
      (WF : Mod.wf (md ★ ProphecyI.t mn)) :
    forall arg r tr
      (BEH: Beh.of_itree (LMod.compile (Mod.to_lmod (md ★ ProphecyI.t mn) r) arg) tr),
      exists extr, tr_extr_relation tr extr /\ ExBeh.of_itree (proph_compile (Mod.to_lmod (md ★ ProphecyI.t mn) r) mn arg) extr.
  Proof using Hreal. i. eapply comp_sim_tgt_extr_exists; et. apply mod_proph_comp_sim. et. Qed.

  Let proph_newI :=
    (ModTr.trans_fnsem ∘ SB.sandbox_body)
    (msk_real (msk_scp [] msk_true), (SModTr.trans_fnsem ∅ (None, ProphecyI.new))).
  Let proph_resolveI :=
    (ModTr.trans_fnsem ∘ SB.sandbox_body)
    (msk_real (msk_scp [] msk_true), (SModTr.trans_fnsem ∅ (None, ProphecyI.resolve))).
  Let proph_closeI :=
    (ModTr.trans_fnsem ∘ SB.sandbox_body)
    (msk_real (msk_scp [] msk_true), (SModTr.trans_fnsem ∅ (None, ProphecyI.close))).
  Let proph_newA sp :=
    (ModTr.trans_fnsem ∘ SB.sandbox_body)
    (msk_scp [] (CFilter.msk_filter_in ∅ msk_true), (SModTr.trans_fnsem sp (fsp_some ProphecyA.new_spec, fbody_trivial))).
  Let proph_resolveA sp :=
    (ModTr.trans_fnsem ∘ SB.sandbox_body)
    (msk_scp [] (CFilter.msk_filter_in ∅ msk_true), (SModTr.trans_fnsem sp (fsp_some ProphecyA.resolve_spec, fbody_trivial))).
  Let proph_closeA sp :=
    (ModTr.trans_fnsem ∘ SB.sandbox_body)
    (msk_scp [] (CFilter.msk_filter_in ∅ msk_true), (SModTr.trans_fnsem sp (fsp_some ProphecyA.close_spec, fbody_trivial))).

  Variant _wf_sim
      (coself : itree (lmodE Σ) Any.t ->
        (bool * itree (lmodE Σ) Any.t) -> Prop)
      : itree (lmodE Σ) Any.t ->
        (bool * itree (lmodE Σ) Any.t) -> Prop :=
  | wf_ret retv
  : _wf_sim coself (Ret retv) (false, Ret retv)

  | wf_tau itr_src itr_tgt
    (NEXT: coself itr_src (false, itr_tgt))
  : _wf_sim coself (tau;; itr_src) (false, tau;; itr_tgt)

  | wf_coreE X (e : coreE X) ktr_src ktr_tgt
    (NEXT: forall x, coself (ktr_src x) (false, ktr_tgt x))
  : _wf_sim coself (x <- trigger e;; ktr_src x) (false, x <- trigger e;; ktr_tgt x)

  | wf_callE X (e : callE X) ktr_src ktr_tgt
    (NEXT: forall x, coself (ktr_src x) (false, ktr_tgt x))
  : _wf_sim coself (x <- trigger e;; ktr_src x) (false, x <- trigger e;; ktr_tgt x)

  | wf_prophecy_new sp arg ktr_src ktr_tgt
    (NEXT: coself (ktr_src tt↑) (false, ktr_tgt tt↑))
    : _wf_sim coself (x <- proph_newA sp arg;; ktr_src x)
        (true, trigger (IO (I:=()) (Prophecy.new mn).1 arg);;;
         x <- proph_newI arg;; ktr_tgt x)

  | wf_prophecy_resolve sp arg ktr_src ktr_tgt
    (NEXT: coself (ktr_src tt↑) (false, ktr_tgt tt↑))
    : _wf_sim coself (x <- proph_resolveA sp arg;; ktr_src x)
        (true, trigger (IO (I:=()) (Prophecy.resolve mn).1 arg);;;
         x <- proph_resolveI arg;; ktr_tgt x)

  | wf_prophecy_close sp arg ktr_src ktr_tgt
    (NEXT: coself (ktr_src tt↑) (false, ktr_tgt tt↑))
    : _wf_sim coself (x <- proph_closeA sp arg;; ktr_src x)
        (true, trigger (IO (I:=()) (Prophecy.close mn).1 arg);;;
         x <- proph_closeI arg;; ktr_tgt x)

  | wf_sget key ktr_src ktr_tgt
    (NEXT: forall x, coself (ktr_src x) (false, ktr_tgt x))
  : _wf_sim coself (x <- (itreeV_itree (ModTr.handle_crisE _ (||SGet key|)%sum));; ktr_src x) (false, x <- (itreeV_itree (ModTr.handle_crisE _ (||SGet key|)%sum));; ktr_tgt x)

  | wf_sput key a ktr_src ktr_tgt
    (NEXT: coself (ktr_src tt) (false, ktr_tgt tt))
  : _wf_sim coself (x <- (itreeV_itree (ModTr.handle_crisE _ (||SPut key a|)%sum));; ktr_src x) (false, x <- (itreeV_itree (ModTr.handle_crisE _ (||SPut key a|)%sum));; ktr_tgt x)

  | wf_Guarantee iP ktr_src ktr_tgt
    (NEXT: coself (ktr_src tt) (false, ktr_tgt tt))
  : _wf_sim coself (x <- (itreeV_itree (ModTr.handle_crisE _ (Guarantee iP|)%sum));; ktr_src x) (false, x <- (itreeV_itree (ModTr.handle_crisE _ (Guarantee iP|)%sum));; ktr_tgt x)

  | wf_AssumePrecise r ktr_src ktr_tgt
    (NEXT: coself (ktr_src tt) (false, ktr_tgt tt))
  : _wf_sim coself (x <- (itreeV_itree (ModTr.handle_crisE _ (AssumeRes r|)%sum));; ktr_src x) (false, x <- (itreeV_itree (ModTr.handle_crisE _ (AssumeRes r|)%sum));; ktr_tgt x).

  Definition wf_sim := paco2 _wf_sim bot2.

  Lemma wf_sim_mon : monotone2 _wf_sim.
  Proof using. ii. destruct IN; des; eauto using _wf_sim. Qed.
  Hint Constructors _wf_sim : core.
  Hint Resolve wf_sim_mon: paco.

  Lemma thread_list_load_relation
      thl_src thl_tgt
      (WF : Forall2 wf_sim thl_src thl_tgt) :
    forall n itr_src, thl_src !! n = Some itr_src -> exists itr_tgt, <<TGTITR : thl_tgt !! n = Some itr_tgt>> /\ <<WFITR : wf_sim itr_src itr_tgt>>.
  Proof using. induction WF; i; ss. destruct n; ss; clarify; et. Qed.

  Lemma wf_sim_bind itrs itrt ktrs ktrt
      (L1 : wf_sim itrs (false, itrt))
      (L2 : forall x, wf_sim (ktrs x) (false, ktrt x)) :
    wf_sim (itrs >>= ktrs) (false, itrt >>= ktrt).
  Proof using.
    Local Opaque itreeV_itree.
    depgen itrs. depgen itrt. pcofix CIH. i. punfold L1. inv L1.
    - ired. eapply paco2_mon_bot; eauto. apply L2.
    - ired. pfold. econs. right. apply CIH. pclearbot. et.
    - ired. pfold. econs. right. apply CIH. pclearbot. apply NEXT.
    - ired. pfold. econs. right. apply CIH. pclearbot. apply NEXT.
    - ired. pfold. econs. right. apply CIH. pclearbot. apply NEXT.
    - ired. pfold. econs. right. apply CIH. pclearbot. apply NEXT.
    - ired. pfold. econs. right. apply CIH. pclearbot. apply NEXT.
    - rewrite 2! bind_bind. pfold. econs. i.
      right. apply CIH. pclearbot. apply NEXT.
    Local Transparent itreeV_itree.
  Qed.

  Lemma pmod_fun_wf_sim fn i args
    (FIND:
      (ModTr.trans_fnsem <$> (SB.sandbox_body <$> omap id (Mod.fnsems md))) !! fn = Some i)
    :
      wf_sim (i args) (false, i args).
  Proof using Hreal.
    revert i FIND; pcofix CIH; intros i; rewrite ?lookup_fmap lookup_omap.
    destruct (Mod.fnsems _ !! fn) as [[[msk ?]|]|] eqn : Hfn; ss; i; clarify.
    revert Hreal; rewrite /real_mod map_Forall_lookup => /(_ fn (Some (msk, f))).
    intros Hmsk; hexploit Hmsk; eauto; clear Hmsk; intros Hmsk.
    rewrite /SB.sandbox_body /= /ModTr.trans_fnsem /ModTr.trans.
    clear - Hmsk f. generalize (f args) as i; clear f args.
    pcofix CIH; intros i; ides i.
    { rewrite SBRed.ret interpV_ret. pfold. econs. }
    { rewrite SBRed.tau interpV_tau. pfold. econs. right. et. }
    { rewrite SBRed.vis; des_ifs; cycle 1.
      { rewrite interpV_vis /= bind_bind. pfold. econs. ss. }
      destruct e as [e|[e|[e|e]]]; simpl.
      { destruct e.
        { destruct Hmsk as [Hmsk _]; rewrite Hmsk in Heq; done. }
        { rewrite interpV_vis; pfold. eapply wf_AssumePrecise; eauto. }
        { rewrite interpV_vis; pfold. econs; eauto. }
      }
      { rewrite interpV_vis /= bind_ret_r. pfold; econs; eauto. }
      { destruct e; rewrite interpV_vis; pfold; econs; eauto. }
      { rewrite interpV_vis /= bind_ret_r; pfold; econs; eauto. }
    }
  Qed.

  Fixpoint stream_app {A} (prefix : list A) (s : stream A) : stream A :=
    match prefix with
    | [] => s
    | h :: t => sfold (scons h (stream_app t s))
    end.

  Fixpoint stream_firstn {A} (i : nat) (s : stream A) : list A :=
    match i with
    | O => []
    | S i' =>
        let '(sfold (scons h t)) := s in
        h :: (stream_firstn i' t)
    end.

  Fixpoint nth {A} (x : stream A) (i : nat) : A :=
    match x with
    | sfold (scons h x') =>
        match i with
        | O => h
        | S n => nth x' n
        end
    end.

  Lemma firstn_reverse {A} n (l : list A) x (LE : n ≤ List.length l) :
    Prophecy.firstn (λ i, nth (stream_app l x) i) n = reverse (firstn n l).
  Proof using Type.
    revert l x LE. induction n; ss. i.
    assert (nth_error l n <> None).
    { rewrite nth_error_Some. nia. }
    destruct nth_error eqn:E; ss.
    replace (take (S n) l) with (take n l ++ [a]).
    2:{ clear - E. revert l a E. induction n; ss; i; des_ifs.
        ss. f_equal. rewrite IHn; et. }
    rewrite reverse_app. ss. rewrite IHn; try nia. f_equal.
    clear - E. revert l x a E. induction n; ss; i.
    { des_ifs. ss. inv Heq. et. }
    des_ifs. ss. inv Heq. apply IHn. et.
  Qed.

  Lemma firstn_length {A} (l : list A) x :
    Prophecy.firstn (λ i, nth (stream_app l x) i) (List.length l) = reverse l.
  Proof using Type. rewrite firstn_reverse; try nia. rewrite firstn_all //. Qed.

  Lemma stream_app_cons {A} (l : list A) a x :
    stream_app l (sfold (scons a x)) = stream_app (l ++ [a]) x.
  Proof using Type. revert a x. induction l; ss. i. do 2 f_equal. et. Qed.

  Definition consistent_sany (Pr : Prophecy.t) (sl: list SAny.t) (p : Prophecy.Pro Pr) :=
    exists l : list (Prophecy.Obs Pr),
      sl = List.map SAny.upcast l /\ Prophecy.consistent Pr l p.

  CoFixpoint stream_map {A B} (f : A -> B) (x : stream A) : stream B :=
    match x with
    | sfold (scons hd tl) => sfold (scons (f hd) (stream_map f tl))
    end.

  Lemma consistent_sany_equiv t obs_seq p
    (COV : forall i, Prophecy.consistent t (Prophecy.firstn obs_seq i) p) :
    forall i,
    exists l,
      List.map SAny.upcast l = Prophecy.firstn (λ n, (obs_seq n)↑↑) i
      /\ Prophecy.consistent t l p.
  Proof using Type.
    i. exists (Prophecy.firstn obs_seq i). split; et.
    induction i; ss. f_equal. et.
  Qed.

  Hint Constructors _extrace_obs_stream_relation : core.
  Hint Resolve extrace_obs_stream_relation_mon : paco.

  Lemma src_mod_wf sp (WF : Mod.wf (md ★ ProphecyI.t mn)) : Mod.wf (md ★ (ProphecyA.t mn sp)).
  Proof using Hreal.
    apply Mod.add_wf_inv in WF as [? [? [? ?]]].
    eapply Mod.add_wf; eauto.
    { econs; [mod_tac | prove_nodup]. }
    set_solver.
  Qed.

  Local Existing Instances prophGS_prophGpreS proph_inG.
  Lemma adequacy_aux sp rs_src rs_tgt rs_proph rs_prog_tgt rs_prog_src proph_map free_ids extr thidx thl_src thl_tgt pstore
    (WFMODT : Mod.wf (md ★ ProphecyI.t mn))
    (VALID : ✓ rs_src)
    (REQ : rs_src ~~> rs_tgt ⋅ rs_proph)
    (RS : rs_proph ≡ (own.iRes_singleton proph_name (proph_auth_r free_ids proph_map)))
    (WF : Forall2 wf_sim thl_src thl_tgt)
    (INV :
      forall id (NOTFREE : ~(free_ids id)),
        exists obs_str,
        let p := proph_map id in
        extrace_obs_stream_relation mn id (projT1 p) extr obs_str
        /\ forall i', consistent_sany (projT1 p)
                       (Prophecy.firstn (λ i, nth (stream_app (reverse (List.map SAny.upcast (snd (projT2 p)))) (stream_map SAny.upcast obs_str)) i) i')
                       (fst (projT2 p)))
    (TBEH :
      paco2 ExBeh._of_itreeF bot2
        (x_ <-
           interp_state (case_ LModTr.handle_stateE LModTr.pure_state)
             (iterV
                (proph_handle_callE mn
                   (LMod.prog
                      (Mod.to_lmod (md ★ ProphecyI.t mn) rs_prog_tgt)))
                (thidx, thl_tgt)) (pstore, rs_tgt);; Ret x_.2) extr) :

    simg_ex false false extr
      (x <-
         LModTr.interp_stateE Any.t
           (iterV
              (LModTr.handle_callE
                 (LMod.prog (Mod.to_lmod (md ★ (ProphecyA.t mn sp)) rs_prog_src)))
              (thidx, thl_src)) (pstore, rs_src);; Ret x.2)
      (x <-
         LModTr.interp_stateE Any.t
           (iterV
              (proph_handle_callE mn
                 (LMod.prog (Mod.to_lmod (md ★ ProphecyI.t mn) rs_prog_tgt)))
              (thidx, thl_tgt)) (pstore, rs_tgt);; Ret x.2).
  Proof using Hreal.
    Local Opaque wsimg.
    hexploit src_mod_wf; et. intro WFMODS.
    move WFMODS at top. move WFMODT at top.
    move rs_proph at bottom. move rs_tgt at bottom. revert_until proph_closeA. pcofix CIH. i.
    revert TBEH. set (ITree.bind _ _). set (ITree.bind _ _).
    assert (wsimg r false false extr i0 i); et. unfold i0, i. clearbody i i0.
    rewrite /LModTr.interp_stateE unfold_iterV /itreeV_itree {1}/LModTr.handle_callE.
    destruct (thl_src !! thidx) as [itr_src|] eqn: SRCITR; [|grind; steps_s; clearub].
    hexploit thread_list_load_relation; et; i; des.
    assert (LEN : thidx < base.length thl_src).
    { apply lookup_lt_is_Some. et. }
    rewrite /LModTr.interp_stateE unfold_iterV /itreeV_itree {1}/proph_handle_callE TGTITR .
    punfold WFITR. inv WFITR; ss; pclearbot.
    (* case : return *)
    - grind. steps_t. steps_s. des_ifs; grind. { apply wsimg_ret. }
      clearub.
    (* case : tau *)
    - grind. steps_t. steps_s. endsim; cycle 1.
      + i. hexploit INV; et. i. des. esplits; et. punfold H0.
        inv H0. fclarify. pclearbot. et.
      + apply Forall2_insert; et.
    (* case : coreE *)
    - grind. destruct e; ss; grind; unfold LModTr.pure_state at 1 3; grind.
      + steps_t. steps_s. exists x. grind. steps_t. steps_s. endsim.
        * apply Forall2_insert; et. apply NEXT.
        * i. hexploit INV; et. i. des. esplits; et.
          punfold H0. inversion H0. clexteq. pclearbot.
          apply (f_equal (fun y => y 0%fin)) in H5. clarify.
          punfold STEP. inversion STEP. fclarify. pclearbot. et.
      + steps_s. steps_t. exists p. grind. steps_s. steps_t. endsim.
        * apply Forall2_insert; et. apply NEXT.
        * i. hexploit INV; et. i. des. esplits; et.
          punfold H0. inversion H0. fclarify. pclearbot.
          punfold STEP. inversion STEP. fclarify. pclearbot. et.
      + apply wsimg_io_normal. i. clarify. rename extr' into extr.
        grind. steps_t. steps_s. endsim.
        * apply Forall2_insert; et. apply NEXT.
        * i. hexploit INV; et. i. des. esplits; et.
          punfold H0. inversion H0.
          apply inj_pair2 in H6. apply inj_pair2 in H7.
          clarify. fclarify. pclearbot.
          punfold STEP. inversion STEP. fclarify. pclearbot. et.
    (* case : callE *)
    - grind. destruct e; ss; grind.
      + steps_s. steps_t. unfold unwrapU.
        destruct LMod.prog eqn:E; [|clearub]. grind. destruct decide.
        { assert (Hfn : Mod.fnsems md !! funid fn = None).
          { inv WFMODT; eapply map_Forall_union_with_inv_gen in wf_fns.
            eapply not_elem_of_dom_1; i; des; subst; set_solver.
          }
          des_ifs; cycle 1.
          { exfalso; rewrite /LMod.prog /= ?lookup_fmap lookup_omap lookup_union_with in Heq.
            rewrite Hfn in Heq; des; subst;
              rewrite !lookup_fmap in Heq;
              repeat (rewrite lookup_insert in Heq || rewrite lookup_insert_ne // in Heq); ss.
          }
          grind. endsim; cycle 1.
          { i. hexploit INV; et. i. clear o. des. esplits; et.
            punfold H0. inversion H0. fclarify. pclearbot. et.
          }
          apply Forall2_insert; et. pfold.
          clear -Heq E o NEXT WFMODS WFMODT Hfn.
          revert E Heq; rewrite /LMod.prog /= ?lookup_fmap ?lookup_omap ?lookup_union_with ?Hfn.
          rewrite /ProphecyA.fnsems /ProphecyI.fnsems.
          des; subst; simpl_map; ss; i; clarify; econs; left; pfold; econs; left; grind.
        }
        (* case : normal call *)
        * revert E; rewrite {1 3}/LMod.prog /= ?lookup_fmap ?lookup_omap ?lookup_union_with.
          rewrite ?lookup_fmap /ProphecyA.fnsems /ProphecyI.fnsems; rewrite ?lookup_insert_ne;
            try by (ii; clarify; exfalso; apply n; esplits; eauto).
          rewrite lookup_empty /=; ss.
          destruct (_ !! funid fn) as [[?|]|] eqn : Hfn; ss; i; clarify.
          grind. endsim.
          { apply Forall2_insert; et. apply wf_sim_bind.
            { eapply (pmod_fun_wf_sim (funid fn)); rewrite ?lookup_fmap lookup_omap Hfn //=. }
            i. pfold. econs. left. grind.
          }
          i. hexploit INV; et. i. des. esplits; et.
          punfold H0. inversion H0. fclarify. pclearbot. et.
      + steps_s. steps_t. unfold unwrapU.
        destruct LMod.prog eqn:E; [|clearub]. grind. destruct decide.
        { assert (Hfn : Mod.fnsems md !! funid fn = None).
          { inv WFMODT; eapply map_Forall_union_with_inv_gen in wf_fns.
            eapply not_elem_of_dom_1; i; des; subst; set_solver.
          }
          des_ifs; cycle 1.
          { exfalso; rewrite /LMod.prog /= ?lookup_fmap lookup_omap lookup_union_with in Heq.
            rewrite Hfn !lookup_fmap in Heq; des; subst;
              repeat (rewrite lookup_insert in Heq || rewrite lookup_insert_ne // in Heq); ss.
          }
          grind. endsim; cycle 1.
          { i. hexploit INV; et. i. clear o. des. esplits; et.
            punfold H0. inversion H0. fclarify. pclearbot. et.
          }
          apply Forall2_app.
          { apply Forall2_insert; et.
            erewrite Forall2_length; et. apply NEXT.
          }
          econs; last econs.
          rewrite -(bind_ret_r (i1 args)) -(bind_ret_r (trigger _;;;_)) bind_bind.
          clear -Heq E o NEXT WFMODS WFMODT Hfn.
          revert E Heq; rewrite /LMod.prog /= ?lookup_fmap ?lookup_omap ?lookup_union_with ?Hfn.
          rewrite /ProphecyA.fnsems /ProphecyI.fnsems.
          des; subst; simpl_map; ss; i; clarify; pfold; econs; left; pfold; econs; left; grind.
        }
        (* case : normal call *)
        * revert E; rewrite {1 3}/LMod.prog /= ?lookup_fmap ?lookup_omap ?lookup_union_with.
          rewrite ?lookup_fmap /ProphecyA.fnsems /ProphecyI.fnsems; rewrite ?lookup_insert_ne;
            try by (ii; clarify; exfalso; apply n; esplits; eauto).
          rewrite lookup_empty /=; ss.
          destruct (_ !! funid fn) as [[?|]|] eqn : Hfn; ss; i; clarify.
          grind. endsim.
          { apply Forall2_app; cycle 1.
            { econs; last econs.
              eapply (pmod_fun_wf_sim (funid fn)); rewrite ?lookup_fmap lookup_omap Hfn //=.
            }
            apply Forall2_insert; et. erewrite Forall2_length; et.
            apply NEXT.
          }
          i. hexploit INV; et. i. des. esplits; et.
          punfold H0. inversion H0. fclarify. pclearbot. et.
      + steps_s. steps_t. endsim.
        * apply Forall2_insert; et. apply NEXT.
        * i. hexploit INV; et. i. des. esplits; et.
          punfold H0. inv H0. fclarify. pclearbot. et.
      + steps_s. steps_t. endsim.
        * apply Forall2_insert; et. apply NEXT.
        * i. hexploit INV; et. i. des. esplits; et.
          punfold H0. inv H0. fclarify. pclearbot. et.
    - grind. unfold LModTr.pure_state at 1 3. grind.
      apply wsimg_io_proph. i. clarify. rename extr' into extr.
      steps_s. grind. steps_s. steps_t.
      unfold proph_newI, ProphecyI.new, ProphecyA.new_spec, fspec_simple.

      unfold precond, postcond. destruct p. ss.
      rr in related. des; subst. destruct x as [i1 t].
      unfold cfunU, SB.sandbox_body, SB.sandbox, ModTr.trans_fnsem, ModTr.trans, SModTr.trans.
      simpl. rewrite !interpV_bind !interpV_trigger. simpl.
      rewrite bind_ret_r interpV_trigger. simpl.
      rewrite bind_ret_r. grind. rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et.
      grind. unfold LModTr.pure_state at 1. grind. steps_s. grind.
      steps_s. rewrite !list_insert_insert.

      simpl. rewrite !interpV_bind !interpV_trigger. simpl.
      rewrite bind_ret_r interpV_trigger. simpl. grind.
      (* rewrite bind_ret_r. grind. *)
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et.
      grind.  grind. steps_s. grind.
      steps_s. rewrite !list_insert_insert.
      grind.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind.
      grind. unfold LModTr.pure_state at 1. grind. steps_s. grind. steps_s.
      rewrite !list_insert_insert.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et.
      grind. unfold LModTr.pure_state at 1. grind. steps_s. grind. steps_s.
      rewrite !list_insert_insert.
      des.
      assert (Own p0 ⊢ ⌜arg = i1↑⌝).
      { iIntros "A". iPoseProof (p2 with "A") as "> [[% [% ?]] ?]"; subst; auto. }
      apply Own_pure_soundness in H; et. clarify.
      assert (Own p0 ⊢ |==> ((⌜i1 ↑ = i1 ↑⌝ ∗ free_id (λ y : Prophecy.ID, y = i1)) ∗ ⌜p = i1 ↑⌝) ∗ Own (rs_tgt ⋅ rs_proph)).
      { iIntros "A". iPoseProof (p2 with "A") as ">[[% [% A]] B]". iFrame. iSplitR; eauto.
        iStopProof. apply Own_Upd. et.
      }
      clear p2. rename H into p2. rewrite /free_id in p2.
      assert (✓ (free_id_r (λ y : Prophecy.ID, y = i1) ⋅ proph_auth_r free_ids proph_map)).
      { eapply Own_pure_soundness; et.
        iIntros "A". iPoseProof (p2 with "A") as ">[[[A B] C] [D E]]".
        rewrite RS.
        rewrite own.own_eq /own.own_def own.Own_eq /own.Own_def.
        iCombine "B E" gives %HFREE. iPureIntro.
        rewrite -own.iRes_singleton_op in HFREE.
        by apply own.iRes_singleton_valid in HFREE.
      }
      assert (free_ids i1).
      { unfold proph_auth_r, free_id_r in H.
        specialize (H i1). discrete_fun_tac.
        destruct excluded_middle_informative; clarify.
        destruct excluded_middle_informative; clarify.
        rewrite comm auth_both_valid_discrete in H. des.
        apply Excl_included in H; inv H.
      }
      clear H. rename H0 into FREE.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind. steps_s.
      rewrite !list_insert_insert.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind. steps_s.
      rewrite !list_insert_insert. unfold fbody_trivial.
      rewrite /SModTr.trans /SModTr._trans interpV_trigger. simpl.
      rewrite bind_ret_r interpV_trigger. simpl.
      rewrite bind_ret_r. rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind.
      grind. unfold LModTr.pure_state at 1. grind. apply wsimg_choose_src.
      exists (tt↑). grind. rewrite !list_insert_insert. steps_s.
      rewrite interpV_ret. grind.
      rewrite !interpV_bind interpV_trigger. simpl.
      rewrite bind_ret_r interpV_trigger. simpl.
      rewrite bind_ret_r. grind.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind.
      grind. unfold LModTr.pure_state at 1. grind. apply wsimg_choose_src.
      exists (tt↑). grind. rewrite !list_insert_insert. steps_s.
      rewrite !interpV_bind interpV_trigger. simpl.
      rewrite bind_ret_r interpV_trigger. simpl. grind.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind. steps_s.
      rewrite !list_insert_insert.
      grind.
      destruct (extrace_has_obs_stream mn extr i1 t).
      pose proof (t.(Prophecy.coverage) (nth x)). des.
      set proph_map' :=
        λ i,
          if excluded_middle_informative (i = i1)
          then existT t (p3, [])
          else proph_map i.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind.
      grind. unfold LModTr.pure_state at 1. grind. apply wsimg_choose_src.
      exists (rs_tgt ⋅ (own.iRes_singleton proph_name (proph_auth_r (Ensembles.Subtract _ free_ids i1) proph_map')
                )).
      grind. steps_s. rewrite !list_insert_insert.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et.
      grind. unfold LModTr.pure_state at 1. grind. apply wsimg_choose_src.
      assert
        (Own p0 ⊢ |==>
           ((∃ p4 : Prophecy.Pro t, ⌜tt ↑ = tt ↑⌝ ∗
             proph i1 (existT t (p4, []))) ∗ ⌜
              tt ↑ = tt ↑⌝) ∗
           Own
           (rs_tgt ⋅ (own.iRes_singleton proph_name
              (proph_auth_r
                 (Ensembles.Subtract Prophecy.ID free_ids i1) proph_map')))).
      { iIntros "A". iPoseProof (p2 with "A") as ">[[[_ B] _] [D E]]".
        rewrite RS. rewrite Own_op; iFrame "D".
        iAssert (own proph_name (proph_auth_r free_ids proph_map)) with "[E]" as "E".
        { rewrite own.Own_eq own.own_eq /own.own_def /own.Own_def //=. }
        iMod (own_update_2 with "B E") as "[B E]"; cycle 1.
        { iModIntro; iSplitL "B".
          { iSplit; last done. iExists p3; iSplit; by iFrame. }
          rewrite own.Own_eq own.own_eq /own.own_def /own.Own_def //=.
        }
        rewrite /free_id_r /proph_r /proph_auth_r.
        apply discrete_fun_update; intros id.
        rewrite !discrete_fun_lookup_op.
        destruct excluded_middle_informative; clarify.
        { destruct excluded_middle_informative; clarify.
          rewrite discrete_fun_lookup_singleton.
          destruct excluded_middle_informative; clarify.
          { inv s. exfalso. apply H2. econs. }
          rewrite comm; etrans; first apply excl_auth_update; rewrite comm.
          rewrite /proph_map'; destruct excluded_middle_informative; ss; reflexivity.
        }
        rewrite !left_id discrete_fun_lookup_singleton_ne //.
        destruct excluded_middle_informative; ss.
        { rewrite left_id. destruct excluded_middle_informative; ss.
          exfalso. apply n0. econs; eauto.
          intros H1; inv H1.
        }
        rewrite left_id. destruct excluded_middle_informative; ss.
        { exfalso; inv s. }
        rewrite /proph_map'. destruct excluded_middle_informative; ss.
      }
      assert
        (✓ (rs_tgt ⋅ (own.iRes_singleton proph_name
              (proph_auth_r
                 (Ensembles.Subtract Prophecy.ID free_ids i1) proph_map')))).
      { assert
          (p0 ~~>
             (rs_tgt ⋅ (own.iRes_singleton proph_name
                (proph_auth_r
                   (Ensembles.Subtract Prophecy.ID free_ids i1) proph_map')))).
        { apply Own_bupd_update. iIntros "A".
          iPoseProof (H1 with "A") as ">[A B]". iModIntro. iFrame. }
        rewrite cmra_valid_validN. i.
        specialize (H2 n ε). ss. apply H2. clear H2. revert n.
        rewrite -cmra_valid_validN. et. }
      unshelve eexists (conj H2 _).
      { rewrite H1. iIntros "> [[[% [? $]] _] $]". iModIntro; iSplit; eauto. }
      grind. rewrite list_insert_insert. step_s.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind. steps_s.
      rewrite !list_insert_insert.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind. steps_s.
      rewrite !list_insert_insert. rewrite !interpV_ret. grind.
      (* rewrite !interpV_tau !interpV_ret. grind. *)
      rewrite (unfold_iterV (proph_handle_callE mn _)). simpl.
      rewrite !list_lookup_insert; [| erewrite <- Forall2_length; et].
      ss. grind. steps_t.
      rewrite !list_insert_insert.
      apply wsimg_endsim. i. eapply CIH. et.
      { apply Forall2_insert; et. rewrite SRed.ret ?interpV_ret /=. grind; eauto. }
      4:{ refl. }
      2:{ refl. }
      3:{ apply WFMODS. }
      2:{ et. }
      i. destruct (decide (id = i1)); cycle 1.
      { assert (~ free_ids id). { ii. apply NOTFREE. split; et. ii. inv H5. }
        apply INV in H4. des.
        replace (proph_map' id) with (proph_map id) by now unfold proph_map'; des_ifs.
        esplits; et.
        Local Arguments String.append /.
        punfold H4. inversion H4.
        Local Arguments String.append : simpl never.
        { subst. apply inj_pair2 in H9. rewrite H9 in H11.
          destruct r1, ret. apply inj_pair2 in H11.
          apply (f_equal (fun y => y 0%fin)) in H11; clarify. pclearbot.
          punfold STEP. inversion STEP. clexteq.
          apply (f_equal (fun y => y 0%fin)) in H7; clarify. pclearbot.
          punfold STEP0. inversion STEP0. clexteq.
          apply (f_equal (fun y => y 0%fin)) in H7; clarify. pclearbot.
          et. }
        { exfalso. apply NE. left. clexteq. split; et. }
        { exfalso. apply NE. et. }
        { exfalso. apply NE. et. } }
      subst. clear H1 H2 H3. unfold proph_map'.
      destruct excluded_middle_informative; clarify. ss.
      punfold H. inversion H. clarify. clexteq.
      apply (f_equal (fun y => y 0%fin)) in H2. clarify. pclearbot.
      esplits; et. i. red.
      eapply consistent_sany_equiv with (i:=i') in H0.
      des. esplits; et. rewrite H0.
      f_equal. extensionalities. clear. revert x.
      induction H2; ss; i; des_ifs.
    - grind. unfold LModTr.pure_state at 1 3. grind.
      apply wsimg_io_proph. i. clarify. rename extr' into extr.
      steps_s. grind. steps_s. steps_t.
      unfold proph_resolveI, ProphecyI.resolve, ProphecyA.resolve_spec, fspec_simple.

      unfold precond, postcond. destruct p. ss.
      rr in related. des; subst. destruct x.
      destruct s, p, p. ss.
      unfold cfunU, SB.sandbox_body, SB.sandbox, ModTr.trans_fnsem, ModTr.trans, SModTr.trans.
      simpl.

      rewrite !interpV_bind !interpV_trigger. simpl.
      rewrite bind_ret_r. grind. rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et.
      grind. unfold LModTr.pure_state at 1. grind. steps_s. grind.
      unfold cfunU, SB.sandbox_body, SB.sandbox, ModTr.trans_fnsem, ModTr.trans, SModTr.trans.
      steps_s. grind. rewrite list_insert_insert.
      rewrite interpV_ret; ired.
      rewrite !interpV_bind !interpV_trigger. simpl.
      rewrite bind_ret_r interpV_trigger. simpl.
      grind. rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind. steps_s. grind.
      rewrite !list_insert_insert.
      grind.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind.
      unfold LModTr.pure_state at 1. grind. steps_s. grind. steps_s.
      rewrite !list_insert_insert.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind.
      unfold LModTr.pure_state at 1. grind. steps_s. grind. steps_s.
      rewrite !list_insert_insert.
      des.
      assert (Own p1 ⊢ ⌜arg = (i1, o↑↑)↑⌝).
      { iIntros "A". iPoseProof (p3 with "A") as ">[[% [% ?]] ?]". subst; eauto. }
      apply Own_pure_soundness in H; et. clarify.
      assert (Own p1 ⊢ |==> ((⌜(i1, o ↑↑) ↑ = (i1, o ↑↑) ↑⌝ ∗ proph i1 (existT x (p, l))) ∗ ⌜p0 = (i1, o ↑↑) ↑⌝) ∗ Own (rs_tgt ⋅ rs_proph)).
      { iIntros "A". iPoseProof (p3 with "A") as ">[[% [% A]] B]". iFrame. iSplitR; eauto.
        iStopProof. apply Own_Upd. et. }
      clear p3. rename H into p3. rewrite RS /proph in p3.
      assert (✓ (proph_r i1 (existT x (p, l)) ⋅ proph_auth_r free_ids proph_map)).
      { eapply Own_pure_soundness; et.
        iIntros "A". iPoseProof (p3 with "A") as ">[[[A B] C] [D E]]".
        rewrite own.own_eq /own.own_def own.Own_eq /own.Own_def.
        iCombine "B E" gives %HFREE.
        rewrite -own.iRes_singleton_op in HFREE.
        by apply own.iRes_singleton_valid in HFREE.
      }
      assert (~ free_ids i1).
      { unfold proph_auth_r, proph_r in H.
        specialize (H i1). discrete_fun_tac.
        rewrite discrete_fun_lookup_singleton in H.
        destruct excluded_middle_informative; clarify.
        rewrite comm auth_both_valid_discrete in H. des.
        apply Excl_included in H; inv H.
      }
      assert (proph_map i1 = existT x (p, l)).
      { specialize (H i1).
        unfold proph_r, proph_auth_r in H.
        discrete_fun_tac. des_ifs.
        rewrite discrete_fun_lookup_singleton in H.
        rewrite comm auth_both_valid_discrete in H. des.
        apply Excl_included in H; inv H. done.
      }
      clear H. rename H0 into FREE. rename H1 into PROPH.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind. steps_s.
      rewrite !list_insert_insert.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind. steps_s.
      rewrite !list_insert_insert. unfold fbody_trivial.
      rewrite /SModTr.trans /SModTr._trans interpV_trigger. simpl.
      rewrite bind_ret_r interpV_trigger. simpl.
      rewrite bind_ret_r.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind.
      unfold LModTr.pure_state at 1. grind. steps_s. grind. steps_s.
      apply wsimg_choose_src.
      exists (tt↑). grind. rewrite !list_insert_insert. steps_s.
      rewrite interpV_ret. grind.
      rewrite !interpV_bind interpV_trigger. simpl.
      rewrite bind_ret_r interpV_trigger. simpl.
      rewrite bind_ret_r. grind.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind.
      unfold LModTr.pure_state at 1. grind. steps_s. grind. steps_s.
      exists (tt↑). grind. rewrite !list_insert_insert. steps_s.
      rewrite !interpV_bind interpV_trigger. simpl.
      rewrite bind_ret_r interpV_trigger. simpl. grind.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind. steps_s.
      rewrite !list_insert_insert.
      grind.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind.
      unfold LModTr.pure_state at 1. grind. steps_s.
      set proph_map' :=
        λ i,
          if excluded_middle_informative (i = i1)
          then existT x (p, o :: l)
          else proph_map i.
      exists
        (rs_tgt
           ⋅ (own.iRes_singleton proph_name (proph_auth_r free_ids proph_map'))).
      grind. step_s. rewrite list_insert_insert.
      hexploit INV; et. i. des.
      punfold H. inversion H.
      { exfalso. des; clarify. }
      all: cycle 1.
      { exfalso. apply inj_pair2 in H3. rewrite H3 in H5. destruct r1, ret.
        fclarify.
        apply (f_equal (@Any.downcast (Prophecy.ID * SAny.t))) in H3.
        rewrite !Any.upcast_downcast in H3. clarify. }
      { exfalso. apply NE. right. split; et.
        clexteq. exists i1, (o↑↑). rewrite PROPH. ss. et. }
      { exfalso. apply NE. et. }
      { exfalso. apply NE. et. }
      apply inj_pair2 in H3. rewrite H3 in H5. destruct r1, ret.
      apply (f_equal (@Any.downcast (Prophecy.ID * SAny.t))) in H3.
      rewrite !Any.upcast_downcast in H3. fclarify. pclearbot.
      replace (stream_map SAny.upcast (sfold (scons o0 obs))) with (sfold (scons (o0↑↑) (stream_map SAny.upcast obs))) in H0.
      2:{
        assert (forall {T} (s : stream T), s = match s with sfold (scons hd tl) => sfold (scons hd tl) end).
        { i. destruct s. destruct s. refl. }
        rewrite (H1 _ (stream_map SAny.upcast (sfold (scons o0 obs)))).
        ss. }
      rewrite H2 in H0. clear H2 H. clear o0. clear H4. pclearbot.
      rewrite stream_app_cons in H0. dup PROPH.
      apply (f_equal (projT1)) in PROPH0. ss. clarify.
      assert (projT2 (proph_map i1) = (p, l)).
      { destruct (proph_map i1). ss.
        apply inj_pair2 in PROPH. et. }
      rewrite H in H0. ss.
      clear H. replace (reverse (List.map SAny.upcast l) ++ [o↑↑]) with (reverse (List.map SAny.upcast (o :: l))) in H0; cycle 1.
      { ss. rewrite cons_app reverse_app. et. }
      dup H0. specialize (H0 (List.length (reverse (List.map SAny.upcast (o :: l))))).
      rewrite firstn_length reverse_involutive in H0.
      rename H1 into CONS. rename H0 into CCC. dup CCC.
      red in CCC0. des.
      assert (l0 = o :: l).
      { clear -CCC0. revert CCC0. generalize (o :: l).
        induction l0; ss; i. { destruct l0; ss. }
        destruct l1; ss. inv CCC0.
        apply (f_equal (@SAny.downcast (Prophecy.Obs (projT1 (proph_map i1))))) in H0.
        rewrite !SAny.upcast_downcast in H0. clarify. f_equal. et. }
      rewrite H in CCC1. clear CCC0 H l0.

      assert
        (Own p1 ⊢ |==>
           postcond ProphecyA.resolve_spec
                 (i1, existT (projT1 (proph_map i1)) (p, l, o)) 
                 () ↑ () ↑ ∗
           Own
           (rs_tgt ⋅
              (own.iRes_singleton proph_name (proph_auth_r free_ids proph_map')))).
      { iIntros "A". iPoseProof (p3 with "A") as ">[[[_ B] _] [D E]]".
        rewrite Own_op; iFrame "D".
        iAssert (own proph_name (proph_auth_r free_ids proph_map)) with "[E]" as "E".
        { rewrite own.Own_eq own.own_eq /own.own_def /own.Own_def //=. }
        rewrite /postcond /=.
        iMod (own_update_2 with "B E") as "[B E]"; cycle 1.
        { iModIntro; iSplitL "B".
          { repeat iSplit; ss. }
          rewrite own.Own_eq own.own_eq /own.own_def /own.Own_def //=.
        }
        rewrite /free_id_r /proph_r /proph_auth_r.
        apply discrete_fun_update; intros id.
        rewrite !discrete_fun_lookup_op.
        destruct (decide (id = i1)); cycle 1.
        { rewrite !discrete_fun_lookup_singleton_ne // !left_id.
          rewrite /proph_map'; repeat destruct excluded_middle_informative; ss.
        }
        subst; rewrite !discrete_fun_lookup_singleton.
        destruct (excluded_middle_informative); ss.
        rewrite comm; etrans; first apply excl_auth_update.
        rewrite /proph_map'; destruct excluded_middle_informative; ss.
        rewrite comm //.
      }
      assert
        (✓ (rs_tgt ⋅
              (own.iRes_singleton proph_name
                 (proph_auth_r free_ids proph_map')))).
      { assert
          (p1 ~~>
             (rs_tgt ⋅
                (own.iRes_singleton proph_name
                   (proph_auth_r free_ids proph_map')))).
        { apply Own_bupd_update. iIntros "A".
          iPoseProof (H with "A") as ">[[_ [_ A]] [? B]] /=". rewrite !Own_op. iFrame. done.
        }
        rewrite cmra_valid_validN. i.
        specialize (H0 n ε). ss. apply H0. clear H0. revert n.
        rewrite -cmra_valid_validN. et.
      }
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind.
      unfold LModTr.pure_state at 1. grind. steps_s.
      unshelve eexists (conj H0 _).
      { rewrite H; iIntros ">[$ $] !> //". }
      grind. steps_s. rewrite !list_insert_insert.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind. steps_s.
      rewrite !list_insert_insert.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind. steps_s.
      rewrite !list_insert_insert.
      rewrite !interpV_ret. grind.
      rewrite (unfold_iterV (proph_handle_callE mn _)). simpl.
      (* rewrite (unfold_iterV (proph_handle_callE _)). simpl. *)
      rewrite !list_lookup_insert; [| erewrite <- Forall2_length; et].
      ss. grind. steps_t.
      rewrite !list_insert_insert.
      rewrite !SRed.ret ?interpV_ret bind_ret_l.
      apply wsimg_endsim. i. eapply CIH. et.
      { apply Forall2_insert; et. }
      5:{ apply WFMODS. }
      4:{ refl. }
      3:{ et. }
      2:{ refl. }
      i. destruct (decide (id = i1)); cycle 1.
      { apply INV in NOTFREE. des.
        replace (proph_map' id) with (proph_map id) by now unfold proph_map'; des_ifs.
        esplits; et.
        punfold NOTFREE. inversion NOTFREE.
        { exfalso. des; clarify. }
        { exfalso. clexteq.
          apply (f_equal (@Any.downcast (Prophecy.ID * SAny.t))) in H4.
          rewrite !Any.upcast_downcast in H4. clarify. }
        { subst. apply inj_pair2 in H4.
          apply (f_equal (@Any.downcast (Prophecy.ID * SAny.t))) in H4.
          rewrite !Any.upcast_downcast in H4.
          inversion H4. subst. destruct r1. fclarify. pclearbot.
          punfold STEP0. inv STEP0. fclarify. pclearbot.
          punfold STEP1. inv STEP1. fclarify. pclearbot.
          et. }
        { subst. clexteq. exfalso. apply NE. right. split; et. }
        { exfalso. clexteq. }
        { exfalso. apply NE. et. } }
      subst. clear H H0 H1. unfold proph_map'.
      destruct excluded_middle_informative; clarify. ss.
      esplits; et. punfold STEP. inv STEP. fclarify. pclearbot.
      punfold STEP0. inv STEP0. fclarify. pclearbot. et.
    - grind. unfold LModTr.pure_state at 1 3. grind.
      apply wsimg_io_proph. i. clarify. rename extr' into extr.
      steps_s. grind. steps_s. steps_t.
      unfold proph_closeI, ProphecyI.close, ProphecyA.close_spec, fspec_simple.
      unfold precond, postcond. destruct p. ss.
      rr in related. des; subst. destruct x as [i1 s].
      unfold cfunU, SB.sandbox_body, SB.sandbox, ModTr.trans_fnsem, ModTr.trans, SModTr.trans.
      simpl. rewrite !interpV_bind !interpV_trigger. simpl.
      rewrite bind_ret_r interpV_trigger. simpl.
      rewrite bind_ret_r. grind. rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et.
      grind. unfold LModTr.pure_state at 1. grind. steps_s. grind.
      steps_s. rewrite !list_insert_insert.
      simpl. rewrite !interpV_bind !interpV_trigger. simpl.
      rewrite bind_ret_r interpV_trigger. simpl. grind.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind. steps_s. grind.
      rewrite !list_insert_insert.
      grind.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind.
      unfold LModTr.pure_state at 1. grind. steps_s. grind. steps_s.
      rewrite !list_insert_insert.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind.
      unfold LModTr.pure_state at 1. grind. steps_s. grind. steps_s.
      rewrite !list_insert_insert. des.

      assert (Own p0 ⊢ ⌜arg = i1↑⌝).
      { iIntros "A". destruct s as [? [? ?]].
        iPoseProof (p2 with "A") as "> [[-> [-> _]] _]". et.
      }
      apply Own_pure_soundness in H; et. clarify.
      destruct s as [x [p' l]].
      assert (Own p0 ⊢
        |==> ((⌜i1 ↑ = i1 ↑⌝ ∗ proph i1 (existT x (p', l))) ∗ ⌜p = i1 ↑⌝) ∗ Own (rs_tgt ⋅ rs_proph)).
      { iIntros "A". iPoseProof (p2 with "A") as ">[[-> A] B]". iFrame. iSplitL ""; et.
        iStopProof. apply Own_Upd. et. }
      clear p2. rename H into p3.
      assert (✓ (proph_r i1 (existT x (p', l)) ⋅ proph_auth_r free_ids proph_map)).
      { eapply Own_pure_soundness; et.
        iIntros "A". iPoseProof (p3 with "A") as ">[[[A B] C] [D E]]".
        rewrite RS.
        unfold proph.
        rewrite own.own_eq /own.own_def own.Own_eq /own.Own_def.
        iCombine "B E" gives %HFREE.
        rewrite -own.iRes_singleton_op in HFREE.
        by apply own.iRes_singleton_valid in HFREE.
      }
      assert (~ free_ids i1).
      { unfold proph_auth_r, proph_r in H.
        specialize (H i1). discrete_fun_tac.
        rewrite discrete_fun_lookup_singleton in H.
        destruct excluded_middle_informative; clarify.
        rewrite comm auth_both_valid_discrete in H. des.
        apply Excl_included in H; inv H.
      }
      assert (proph_map i1 = existT x (p', l)).
      { specialize (H i1).
        unfold proph_r, proph_auth_r in H.
        discrete_fun_tac. des_ifs.
        rewrite discrete_fun_lookup_singleton in H.
        rewrite comm auth_both_valid_discrete in H. des.
        apply Excl_included in H; inv H; eauto.
      }
      clear H. rename H0 into FREE. rename H1 into PROPH.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind. steps_s.
      rewrite !list_insert_insert.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind. steps_s.
      rewrite !list_insert_insert. unfold fbody_trivial.
      rewrite /SModTr.trans /SModTr._trans interpV_trigger. simpl.
      rewrite bind_ret_r interpV_trigger. simpl.
      rewrite bind_ret_r.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind.
      unfold LModTr.pure_state at 1. grind. steps_s. grind.
      eapply wsimg_choose_src.
      exists (tt↑). grind. rewrite !list_insert_insert. steps_s.
      rewrite interpV_ret. grind.
      rewrite !interpV_bind interpV_trigger. simpl.
      rewrite bind_ret_r interpV_trigger. simpl.
      rewrite bind_ret_r. grind.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind.
      unfold LModTr.pure_state at 1. grind. steps_s. grind. steps_s.
      exists (tt↑). grind. rewrite !list_insert_insert. steps_s.
      rewrite !interpV_bind interpV_trigger. simpl.
      rewrite bind_ret_r interpV_trigger. simpl. grind.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind. steps_s.
      rewrite !list_insert_insert.
      grind.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind.
      unfold LModTr.pure_state at 1. grind. steps_s.
      exists (rs_tgt ⋅ (own.iRes_singleton proph_name (proph_auth_r (Ensembles.Add _ free_ids i1) proph_map))).
      grind. steps_s. rewrite !list_insert_insert.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind.
      unfold LModTr.pure_state at 1. grind. steps_s.
      assert
        (Own p0 ⊢ |==>
           postcond ProphecyA.close_spec (i1, existT x (p', l)) () ↑ () ↑ ∗
           Own
           (rs_tgt ⋅ (own.iRes_singleton proph_name
              (proph_auth_r
                 (Ensembles.Add Prophecy.ID free_ids i1) proph_map)))).
      { iIntros "A". iPoseProof (p3 with "A") as ">[[[_ B] _] [D E]]".
        rewrite RS.
        rewrite Own_op; iFrame "D".
        iAssert (own proph_name (proph_auth_r free_ids proph_map)) with "[E]" as "E".
        { rewrite own.Own_eq own.own_eq /own.own_def /own.Own_def //=. }
        rewrite /postcond /=.
        iMod (own_update_2 with "B E") as "[B E]"; cycle 1.
        { iModIntro; iSplitL "B".
          { repeat iSplit; ss. }
          rewrite own.Own_eq own.own_eq /own.own_def /own.Own_def //=.
        }
        rewrite /free_id_r /proph_r /proph_auth_r.
        apply discrete_fun_update; intros id.
        rewrite !discrete_fun_lookup_op.
        destruct (decide (id = i1)); cycle 1.
        { rewrite !discrete_fun_lookup_singleton_ne // !left_id.
          destruct excluded_middle_informative; ss.
          { destruct excluded_middle_informative; ss. rewrite left_id.
            destruct excluded_middle_informative; ss.
            exfalso; apply n1; econs; ss.
          }
          destruct excluded_middle_informative; ss.
          destruct excluded_middle_informative; ss.
          inv a; inv H.
        }
        subst; rewrite !discrete_fun_lookup_singleton.
        destruct (excluded_middle_informative); ss.
        rewrite comm; etrans; first apply excl_auth_update.
        destruct excluded_middle_informative; ss.
        rewrite comm //; des_ifs; [refl|].
        exfalso; apply n0. right; ss.
      }
      assert
        (✓ (rs_tgt ⋅ (own.iRes_singleton proph_name
              (proph_auth_r
                 (Ensembles.Add Prophecy.ID free_ids i1) proph_map)))).
      { assert
          (p0 ~~>
             (rs_tgt ⋅ (own.iRes_singleton proph_name
                (proph_auth_r
                   (Ensembles.Add Prophecy.ID free_ids i1) proph_map)))).
        { apply Own_bupd_update. iIntros "A".
          iPoseProof (H with "A") as ">[A B]". iModIntro. iFrame. }
        rewrite cmra_valid_validN. i.
        specialize (H0 n ε). ss. apply H0. clear H0. revert n.
        rewrite -cmra_valid_validN. et. }
      exists (conj H0 H).
      grind. rewrite list_insert_insert. step_s.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind. steps_s.
      rewrite !list_insert_insert.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind. steps_s.
      rewrite !list_insert_insert. rewrite !interpV_ret. grind.
      rewrite (@unfold_iterV _ _ _ (proph_handle_callE mn _)). simpl.
      rewrite !list_lookup_insert; [| erewrite <- Forall2_length; et].
      ss. grind. steps_t.
      rewrite !list_insert_insert.
      rewrite SRed.ret !interpV_ret bind_ret_l.
      apply wsimg_endsim. i. eapply CIH. et.
      { apply Forall2_insert; et. }
      5:{ apply WFMODS. }
      4:{ refl. }
      3:{ et. }
      2:{ refl. }
      i. hexploit INV. { instantiate (1:=id). ii. apply NOTFREE. econs. et. }
      i. des. assert (NEQ: i1 <> id). { ii. apply NOTFREE. econs 2. clarify. }
      esplits; et.
      Local Arguments String.append /.
      punfold H2. inversion H2.
      Local Arguments String.append : simpl never.
      { subst. apply inj_pair2 in H7. rewrite H7 in H9.
        destruct r1, ret. fclarify. pclearbot.
        punfold STEP. inversion STEP. fclarify. pclearbot.
        punfold STEP0. inversion STEP0. fclarify. pclearbot. et. }
      { exfalso. apply NE. left. clexteq. split; et. }
      { exfalso. apply NE. et. }
      { exfalso. apply NE. et. }
    - grind. steps_t. steps_s.
      endsim. { apply Forall2_insert; et. apply NEXT. }
      i. hexploit INV; et. i. des. esplits; et. punfold H0. inv H0.
      fclarify. pclearbot. et.
    - grind. steps_t. steps_s.
      do 2 rewrite unfold_iterV. grind.
      rewrite !list_lookup_insert; et; cycle 1.
      { erewrite <- Forall2_length; et. }
      grind. steps_t. steps_s. rewrite !list_insert_insert.
      endsim. { apply Forall2_insert; et. }
      i. hexploit INV; et. i. des. esplits; et. punfold H0. inv H0.
      fclarify. pclearbot.
      punfold STEP. inv STEP. fclarify. pclearbot. et.
    - grind. steps_t. steps_s.
      grind.
      do 2 rewrite unfold_iterV. grind.
      rewrite !list_lookup_insert; et; cycle 1.
      { erewrite <- Forall2_length; et. }
      grind. unfold LModTr.pure_state at 1 4. grind.
      steps_t. steps_s. exists (x ⋅ rs_proph). grind.
      steps_t. steps_s. rewrite !list_insert_insert.
      do 2 rewrite unfold_iterV. grind.
      rewrite !list_lookup_insert; et; cycle 1.
      { erewrite <- Forall2_length; et. }
      grind. unfold LModTr.pure_state at 1 4. grind.
      steps_t. steps_s. move x0 at bottom.
      assert (Own (rs_tgt ⋅ rs_proph) ⊢ |==> iP ∗ Own (x ⋅ rs_proph)).
      { iIntros "[A B]". des. iPoseProof (x1 with "A") as ">[A C]".
        iCombine "C B" as "B". iModIntro. iFrame. }
      assert (Own (rs_tgt ⋅ rs_proph) ⊢ |==> Own (x ⋅ rs_proph)).
      { iIntros "A". iPoseProof (H with "A") as ">[B C]". iModIntro. et. }
      assert (✓ (x ⋅ rs_proph)).
      { apply Own_bupd_update in H0.
        assert (rs_src ~~> x ⋅ rs_proph). { etrans; et. }
        red in H1. rewrite cmra_valid_validN. i.
        specialize (H1 n ε). ss. apply H1. clear H1. revert n.
        rewrite -cmra_valid_validN //=. }
      esplits. Unshelve. all: et. all: cycle 1.
      { split; et. iIntros "A". eapply Own_Upd in REQ.
        iPoseProof (REQ with "A") as ">A". iApply H. et. }
      grind. steps_s. steps_t.
      rewrite !list_insert_insert.
      do 2 rewrite unfold_iterV. grind.
      rewrite !list_lookup_insert; et; cycle 1.
      { erewrite <- Forall2_length; et. }
      grind. steps_t. steps_s.
      rewrite !list_insert_insert.
      do 2 rewrite unfold_iterV. grind.
      rewrite !list_lookup_insert; et; cycle 1.
      { erewrite <- Forall2_length; et. }
      grind. steps_t. steps_s. rewrite !list_insert_insert.
      endsim. { apply Forall2_insert; et. }
      2:{ refl. }
      clear H H0 H1 H2.
      i. hexploit INV; et. i. des. esplits; et. punfold H. inv H.
      fclarify. pclearbot.
      punfold STEP. inversion STEP. clexteq.
      apply (f_equal (fun y => y 0%fin)) in H3; clarify. pclearbot.
      punfold STEP0. inversion STEP0. clexteq.
      apply (f_equal (fun y => y 0%fin)) in H1; clarify. pclearbot.
      punfold STEP1. inversion STEP1. clexteq.
      apply (f_equal (fun y => y 0%fin)) in H3; clarify. pclearbot.
      punfold STEP2. inv STEP2. fclarify. pclearbot.
      punfold STEP3. inv STEP3. fclarify. pclearbot.
      punfold STEP2. inv STEP2. fclarify. pclearbot. et.
    - grind. steps_t. steps_s.
      grind.
      do 2 rewrite unfold_iterV. grind.
      rewrite !list_lookup_insert; et; cycle 1.
      { erewrite <- Forall2_length; et. }
      grind. unfold LModTr.pure_state at 1 4. grind.
      steps_s. steps_t. unshelve eexists.
      { rewrite comm. eapply cmra_discrete_total_update.
        { etrans; last apply cmra_update_op_l; apply REQ. }
        rewrite comm //.
      }
      grind.
      steps_t. steps_s. rewrite !list_insert_insert.
      do 2 rewrite unfold_iterV. grind.
      rewrite !list_lookup_insert; et; cycle 1.
      { erewrite <- Forall2_length; et. }
      grind.
      steps_s; steps_t.
      rewrite !list_insert_insert.
      do 2 rewrite unfold_iterV. grind.
      rewrite !list_lookup_insert; et; cycle 1.
      { erewrite <- Forall2_length; et. }
      grind.
      steps_t. steps_s.
      rewrite !list_insert_insert.
      endsim. { apply Forall2_insert; et. }
      2:{ rewrite REQ assoc //. }
      i. hexploit INV; et. i. des. esplits; et. clear - H0.
      punfold H0. inv H0. fclarify. pclearbot.
      punfold STEP. inversion STEP. clexteq.
      apply (f_equal (fun y => y 0%fin)) in H1; clarify. pclearbot.
      punfold STEP0. inversion STEP0. clexteq.
      apply (f_equal (fun y => y 0%fin)) in H0; clarify. pclearbot.
      punfold STEP1. inversion STEP1. clexteq.
      apply (f_equal (fun y => y 0%fin)) in H0; clarify. pclearbot.
      punfold STEP2. inv STEP2. fclarify. pclearbot.
      punfold STEP3. pfold. eauto.
  (*SLOW*)Qed.

  (* we can't give an prophecy value in initial state *)
  (* prophecy's invariant is that prophecy value should consistent with full prophecy call behavior *)
  (* prophecy module can't expect full program's behavior locally *)
  (* If prophecy value is given in initial state, context module cannot be parameterized and should have expected behavior *)
  Lemma adequacy_refines_mod sp
      (r_src r_tgt r_proph : Σ)
      (WFMODT : Mod.wf (md ★ ProphecyI.t mn))
      (WFR : ✓ r_src)
      (REQ : r_src ~~> r_tgt ⋅ r_proph)
      (RS : r_proph ≡
        (own.iRes_singleton proph_name (proph_auth_r (Ensembles.Full_set _) (λ _, dummy_prophinst)))) :
    refines_lmod
      (Mod.to_lmod (md ★ ProphecyI.t mn) r_tgt)
      (Mod.to_lmod (md ★ (ProphecyA.t mn sp)) r_src).
  Proof using Hreal.
    ii. apply prophecy_tgt_exbeh_exists in PR; et. des.
    pose proof (extrace_has_obs_stream mn extr).
    revert PR0. unfold LMod.compile. unfold proph_compile.
    remember (_ !! entry). set (_ !! entry).
    assert (o = o0).
    { rewrite Heqo. unfold o0, Mod.to_lmod, LMod.prog. ss.
      rewrite ?lookup_fmap ?lookup_omap ?lookup_union_with.
      simpl_map; ss.
    }
    rewrite -H0. clear o0 H0. destruct o; simpl; cycle 1.
    { i. unfold triggerUB. rewrite bind_bind. pfold. econs. econs. i. clarify. }
    rewrite !bind_ret_l. unfold ITree.map. i.
    eapply simg_ex_adequacy; et.
    replace (Mod.initial_st (ProphecyI.t mn)) with (Mod.initial_st (ProphecyA.t mn sp)) in PR0 by reflexivity.
    eapply adequacy_aux; et; cycle 1.
    { i. exfalso. apply NOTFREE. ss. }
    econs; last econs. eapply pmod_fun_wf_sim.
    rewrite Heqo. unfold LMod.prog. ss.
    instantiate (1:= entry).
    rewrite ?lookup_fmap ?lookup_omap ?lookup_union_with ?lookup_fmap.
    rewrite /ProphecyI.fnsems ?fmap_insert ?lookup_insert_ne //= lookup_empty //=.
    destruct (Mod.fnsems _ !! entry); ss.
  Qed.

  Lemma adequacy_refines sp :
    ProphecyA.initial_cond ⊢
      refines (md ★ ProphecyI.t mn) (md ★ ProphecyA.t mn sp).
  Proof using Hreal.
    assert (PROPH :
      ProphecyA.initial_cond ⊢
        Own (own.iRes_singleton proph_name
          (proph_auth_r (Ensembles.Full_set Prophecy.ID)
            (λ _ : Prophecy.ID, dummy_prophinst)))).
    { rewrite /ProphecyA.initial_cond /proph_auth.
      rewrite own.own_eq /own.own_def own.Own_eq //. }
    iIntros "INIT %WFMODT".
    iSplit. { iPureIntro. apply src_mod_wf; et. }
    iIntros "WINV %t TGT".
    iRevert "TGT INIT WINV"; iIntros "TGT INIT WINV". iStopProof.
    eapply entails_pointwise. intros rs Vrs Hrs.
    eapply Own_split' in Hrs; et.
    destruct Hrs as [rt [Vrt [Hrt Hrs]]].
    eapply Own_general_completeness. rewrite Beh_unseal.
    intros rs' Vrs' LE.
    assert (REF :
      refines_lmod
        (Mod.to_lmod (md ★ ProphecyI.t mn) rt)
        (Mod.to_lmod (md ★ ProphecyA.t mn sp) rs')).
    { eapply adequacy_refines_mod; et.
      eapply Own_bupd_update.
      iIntros "S".
      iPoseProof (Own_extends with "S") as "S"; et.
      iDestruct (Hrs with "S") as "[T [INIT _]]".
      iModIntro. rewrite Own_op. iFrame "T".
      iApply PROPH. done.
    }
    eapply REF.
    eapply Own_general_soundness in Hrt; et.
    rewrite Beh_unseal in Hrt. eapply Hrt; et.
  Qed.
End ProphIA. End ProphIA.
