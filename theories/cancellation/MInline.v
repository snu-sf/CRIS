From CRIS.common Require Import Common ConcRA.
From CRIS.modules Require Import Mod FSpec.
From iris.proofmode Require Import proofmode.
From stdpp Require Import base.

(* Inlining every function call in HMod. *)
Section INTERP.
  Context `{Σ : GRA}.

  Definition handle_callE
      {R} (prog : string → fbody) (itr : itree crisE R)
      : itree crisE (itree crisE R + R) :=
    match observe itr with
    | RetF r => Ret (inr r)
    | TauF itr' => tau;; Ret (inl itr')
    | VisF (inr1 (inl1 c)) k =>
        match c in (callE T) return ((T → _) → _)
        with
        | Call fn args =>
            λ k, Ret (inl (x <- prog fn args;; (tau;; k x)))
        | Spawn fn args =>
            λ k, v <- trigger (Spawn fn args);; Ret (inl (k v))
        | Yield tid =>
            λ k, v <- trigger (Yield tid);; Ret (inl (k v))
        | GetTid =>
            λ k, v <- trigger GetTid;; Ret (inl (k v))
        end k
    | VisF e k =>
        v <- trigger e;; Ret (inl (k v))
    end.

  Definition sandboxed_prog (ms : Mod.t) (fn : string) (arg : Any.t) : itree crisE Any.t :=
    kb <- ((omap id ms.(Mod.fnsems)) !! (funid fn))?;;
    SB.sandbox_body kb arg.

  Definition inline_body {R} prog := ITree.iter (@handle_callE R prog).

  Definition inline_fsem ms (kb: emask * fbody) : emask * fbody :=
    (msk_scp (Mod.scopes ms) msk_true, inline_body (sandboxed_prog ms) ∘ (SB.sandbox_body kb)).
End INTERP.

Module MInline.
  Import Mod.

  Program Definition inline `{Σ : GRA} (ms : Mod.t) : Mod.t := {|
    scopes := ms.(scopes);
    fnsems := fmap (option_map (inline_fsem ms)) (ms.(fnsems));
    initial_st := ms.(initial_st);
  |}.
  Next Obligation. intros ? [? ? ?]; ss. Qed.
  Next Obligation.
    intros Σ ms fn [msk p].
    rewrite lookup_omap lookup_fmap.
    destruct ((fnsems ms) !! fn) eqn: Heq; ss; intros H.
    destruct o as [[msk0 p0]|]; ss. hexploit (ms.(well_scoped_fns) fn (msk0, p0)); eauto.
    { rewrite lookup_omap Heq //. }
    inv H. i; des; split; i; rewrite /msk_scp /msk_true in H1; des_ifs; inv Heq0; ss;
      case_bool_decide; ss.
  Qed.
  Next Obligation. ii. destruct ms. ss. eauto. Qed.
  Next Obligation.
    ii. destruct ms. ss.
    hexploit nodup_init0; eauto. i; ss. specialize (H1 i). ss.
    hexploit H1; eauto.
  Qed.
End MInline.

Module MIRed.

  Lemma ret `{Σ : GRA} {T} prog (x : T) :
    inline_body prog (Ret x) = Ret x.
  Proof using. rewrite/inline_body unfold_iter. grind. Qed.

  Lemma tau `{Σ : GRA} {T} prog (t : itree _ T) :
    inline_body prog (tau;; t) = tau;; tau;; inline_body prog t.
  Proof using. rewrite/inline_body unfold_iter. grind. Qed.

  Lemma bind `{Σ : GRA} {R T} prg i (k : R → itree _ T) :
    inline_body prg (i >>= k) = x <- inline_body prg i;; inline_body prg (k x).
  Proof using.
    rewrite /inline_body. eapply bisim_is_eq. ginit.
    revert i k. gcofix CIH. i.
    ides i.
    - grind. rewrite [_ _ (Ret _)]unfold_iter. grind.
      gfinal. right. eapply paco2_mon_bot; eauto.
      eapply eq_is_bisim. refl.
    - grind. rewrite !unfold_iter. grind.
      gstep. econs. gstep. econs. gbase. eapply CIH.
    - rewrite !unfold_iter.
      destruct e.
      { grind. rewrite! bind_trigger. gstep. econs. i.
        grind. gstep. econs. gbase. eauto.
      }
      destruct s; [destruct c|].
      { grind. gstep. econs.
        gbase. evar_at_last_2; eauto. f_equal. grind.
      } 
      { grind. rewrite! bind_trigger. gstep. econs. i.
        grind. gstep. econs. gbase. eauto.  
      }
      { grind. rewrite! bind_trigger. gstep. econs. i.
        grind. gstep. econs. gbase. eauto.
      }
      { grind. rewrite! bind_trigger. gstep. econs. i.
        grind. gstep. econs. gbase. eauto.
      }
      grind. rewrite! bind_trigger. gstep. econs. i.
      grind. gstep. econs. gbase. eauto.
  Qed.

  Lemma spawn `{Σ: GRA} {T} prog fn args (ktr: _ → itree _ T) :
    inline_body prog (x <- trigger (Spawn fn args);; ktr x)  =
    x <- trigger (Spawn fn args);; tau;; inline_body prog (ktr x).
  Proof using. rewrite/inline_body unfold_iter. grind. Qed.

  Lemma yield `{Σ: GRA} {T} prog tid (ktr: _ → itree _ T) :
    inline_body prog (x <- trigger (Yield tid);; ktr x) =
    x <- trigger (Yield tid);; tau;; inline_body prog (ktr x).
  Proof using. rewrite/inline_body unfold_iter. grind. Qed.
  
  Lemma gettid `{Σ : GRA} {T} prog (ktr: _ → itree _ T) :
    inline_body prog (x <- trigger GetTid;; ktr x) =
    x <- trigger GetTid;; tau;; inline_body prog (ktr x).
  Proof using. rewrite/inline_body unfold_iter. grind. Qed.

  Lemma core `{Σ: GRA} {T} X prog (e: coreE X) (ktr: _ → itree _ T) :
    inline_body prog (x <- trigger e;; ktr x) =
    x <- trigger e;; tau;; inline_body prog (ktr x).
  Proof using. rewrite /inline_body unfold_iter. grind. Qed.

  Lemma pg `{Σ : GRA} {T} X prog (e: pgE X) (ktr: _ → itree _ T) :
    inline_body prog (x <- trigger e;; ktr x) =
    x <- trigger e;; tau;; inline_body prog (ktr x).
  Proof using. rewrite/inline_body unfold_iter. grind. Qed.

  Lemma ag `{Σ: GRA} {T} X prog (e: agE X) (ktr: _ → itree _ T) :
    inline_body prog (x <- trigger e;; ktr x) =
    x <- trigger e;; tau;; inline_body prog (ktr x).
  Proof using. rewrite /inline_body unfold_iter. grind. Qed.

  Lemma call `{Σ: GRA} {T} prog (ktr: _ → itree _ T) (fn: string) arg  :
    inline_body prog (trigger (Call fn arg) >>= ktr) =
    tau;; inline_body prog (x <- prog fn arg;; tau;; ITree.subst ktr (Ret x)).
  Proof using. rewrite/inline_body unfold_iter. ired. refl. Qed.
End MIRed.

Lemma sandbox_inline_commute `{Σ: GRA}
  ms (msk: emask) (bd: fbody) arg
  (IMG: img_msk msk)
  (SCP: (∀ (k : key) (v : Any.t),
            msk _ (subevent _ (SPut k v)) = true →
            scope k ∈ (Mod.scopes ms))
        ∧ (∀ (k : key),
            msk _ (subevent _ (SGet k)) = true →
            scope k ∈ (Mod.scopes ms)))
  :
  SB.sandbox_body (inline_fsem ms (msk, bd)) arg
  =
  inline_body (sandboxed_prog ms) (SB.sandbox_body (msk, bd) arg).
Proof using.
  assert (SCPIMPL:
           ∀ (fn: string) (msk: emask) (bd: fbody),
             Mod.fnsems ms !! funid fn = Some (Some (msk, bd)) →
             ∀ (X: Type) (e : @crisE Σ X), msk X e → (msk_scp (Mod.scopes ms) msk_true) X e).
  { i. hexploit (Mod.well_scoped_fns ms); eauto.
    intros FA. specialize (FA (funid fn) (msk0, bd0)).
    rewrite lookup_omap H in FA. ss. specialize (FA eq_refl).
    rewrite /msk_scp. depdes e; ss.
    depdes s; ss. depdes s; ss. depdes p; ss.
    { case_bool_decide; ss. exfalso. des; eauto. }
    { case_bool_decide. ss. exfalso. des; eauto. }
  }
  assert (SCPIMPL0: ∀ (X : Type) (e : crisE X), msk X e → (msk_scp (Mod.scopes ms) msk_true) X e).
  { i; des. rewrite /msk_scp. depdes e; ss. depdes s; ss. depdes s; ss. depdes p; ss.
    { case_bool_decide; ss. exfalso. des; eauto. }
    { case_bool_decide; ss. exfalso. des; eauto. }
  }
  unfold inline_fsem, SB.sandbox_body. ss.
  apply bisim_is_eq.
  ginit. generalize (bd arg) as itr. clear bd arg.
  revert_until ms. gcofix CIH. i.
  ides itr.
  { rewrite !SBRed.ret MIRed.ret SBRed.ret. gstep. econs. reflexivity. }
  { rewrite !SBRed.tau MIRed.tau !SBRed.tau.
    gstep. econs. gstep. econs. gbase. eauto. }
  rewrite -bind_trigger !SBRed.bind.
  destruct e.
  { assert ((@ITree.trigger (@crisE Σ) X (inl1 a)) = trigger a) by grind.
    destruct a.
    - rewrite H !SBRed.vis. des_ifs.
      + rewrite !vis_trigger !bind_bind !MIRed.ag !SBRed.bind !SBRed.vis !bind_trigger.
        des_ifs. rewrite !bind_vis.
        gstep. econs. i. rewrite SBRed.ret bind_ret_l SBRed.tau SBRed.ret !bind_ret_l.
        gstep. econs. gbase. eauto.
      + ired. rewrite !vis_trigger !bind_bind !MIRed.core SBRed.bind SBRed.vis.
        des_ifs. rewrite !vis_trigger !bind_bind.
        gstep. r; s; econs. ss.
    - rewrite H !SBRed.vis. des_ifs; cycle 1.
      { r in IMG; des. rewrite IMG2 // in Heq. }
      rewrite !vis_trigger !bind_bind MIRed.ag SBRed.bind SBRed.vis !bind_trigger /=.
      des_ifs. rewrite ?vis_trigger ?bind_bind ?H.
      gstep. r; s; econs. i.
      rewrite bind_ret_l SBRed.ret !bind_ret_l.
      rewrite SBRed.tau. gstep. econs.
      rewrite SBRed.ret !bind_ret_l.
      gbase. eauto.
    - rewrite H !SBRed.vis. des_ifs; cycle 1.
      { r in IMG; des. rewrite IMG3 // in Heq. }
      rewrite !vis_trigger bind_bind MIRed.ag SBRed.bind SBRed.vis !bind_trigger !vis_trigger /=.
      rewrite bind_bind. gstep. r; s; econs. i.
      rewrite bind_ret_l SBRed.ret !bind_ret_l.
      rewrite SBRed.tau. gstep. econs.
      rewrite SBRed.ret !bind_ret_l.
      gbase. eauto.
  }
  destruct s; [destruct c|].
  { rewrite !SBRed.vis. des_ifs; cycle 1.
    { ired. rewrite !vis_trigger !bind_bind !MIRed.core !SBRed.bind SBRed.vis !bind_trigger.
      des_ifs. gstep. r; s; econs. ss. }

    rewrite !vis_trigger !bind_bind MIRed.call SBRed.tau. s.
    gstep. econs.
    destruct ((Mod.fnsems ms) !! (funid fn)) eqn: FIND; cycle 1.
    { ired. rewrite {2 4}/sandboxed_prog lookup_omap FIND. s. ired.
      rewrite !MIRed.core !SBRed.bind SBRed.vis !bind_trigger.
      gstep. r; s; econs. ss.
    }

    rewrite {2 4}/sandboxed_prog /SB.sandbox_body lookup_omap FIND. s. ired. destruct o; cycle 1.
    { ired. rewrite !MIRed.core !SBRed.bind SBRed.vis !bind_trigger.
      des_ifs. gstep. r; s; econs. ss. }
    ired.
    destruct p as [msk1 bd0]. s.
    match goal with
    [|- _ _ (_ _ ?itr)] => assert (EX: exists itr', itr = SB.sandbox (msk_scp ms.(Mod.scopes) msk_true) itr'); cycle 1
    end.
    { des. rewrite EX. gbase. eapply CIH; try refl; eauto; ss. split; i; case_bool_decide; ss. }

    eexists. instantiate (1:= _ >>= _).
    rewrite SBRed.bind. f_equal.
    { erewrite <-(@sandbox_sandbox _ _ _ _ _ (SCPIMPL fn msk1 bd0 FIND)); try refl; eauto. }
    extensionality x.
    rewrite subst_bind bind_ret_l.
    erewrite SBRed.tau.
    rewrite SBRed.ret bind_ret_l.
    erewrite <-(@sandbox_sandbox _ _ _ _ _ SCPIMPL0); eauto.
  }
  {
    rewrite !SBRed.vis. des_ifs.
    + rewrite !vis_trigger !bind_bind MIRed.spawn SBRed.bind SBRed.vis. s.
      gstep. r; s; econs. i.
      rewrite SBRed.ret !bind_ret_l SBRed.tau. gstep. econs.
      rewrite SBRed.ret bind_ret_l. gbase. eauto.
    + ired. rewrite !vis_trigger !bind_bind !MIRed.core !SBRed.bind SBRed.vis !bind_trigger.
      des_ifs. gstep. r; s; econs. i.
      rewrite SBRed.ret !bind_ret_l SBRed.tau. gstep. econs. gbase. eauto.
  }
  {
    rewrite !SBRed.vis. des_ifs.
    + rewrite !vis_trigger !bind_bind MIRed.yield SBRed.bind SBRed.vis. s.
      gstep. r; s; econs. i.
      rewrite SBRed.ret !bind_ret_l SBRed.tau. gstep. econs.
      rewrite SBRed.ret bind_ret_l. gbase. eauto.
    + ired. rewrite !vis_trigger !bind_bind !MIRed.core !SBRed.bind SBRed.vis !bind_trigger.
      des_ifs. gstep. r; s; econs. i.
      rewrite SBRed.ret !bind_ret_l SBRed.tau. gstep. econs. gbase. eauto.
  }
  {
    rewrite !SBRed.vis. des_ifs.
    + rewrite !vis_trigger !bind_bind MIRed.gettid SBRed.bind SBRed.vis. s.
      gstep. r; s; econs. i.
      rewrite SBRed.ret !bind_ret_l SBRed.tau. gstep. econs.
      rewrite SBRed.ret bind_ret_l. gbase. eauto.
    + ired. rewrite !vis_trigger !bind_bind !MIRed.core !SBRed.bind SBRed.vis !bind_trigger.
      des_ifs. gstep. r; s; econs. i.
      rewrite SBRed.ret !bind_ret_l SBRed.tau. gstep. econs. gbase. eauto.
  }
  destruct s; [destruct p|].
  {
    rewrite !SBRed.vis. des_ifs; cycle 1.
    { ired. rewrite !vis_trigger !bind_bind !MIRed.core !SBRed.bind SBRed.vis !bind_trigger.
      des_ifs. gstep. r; s; econs. ss.
    }

    rewrite !vis_trigger !bind_bind MIRed.pg SBRed.bind SBRed.vis. des_ifs; cycle 1.
    { exfalso. bsimpl. ss. case_bool_decide; ss. eapply H. des.
      eapply SCP; eauto. }
    rewrite !vis_trigger !bind_bind. gstep; r; s; econs; i.
    rewrite !bind_ret_l SBRed.ret bind_ret_l SBRed.tau. gstep; econs.
    rewrite SBRed.ret bind_ret_l. gbase; eauto.
  }
  {
    rewrite !SBRed.vis. des_ifs; cycle 1.
    { ired. rewrite !vis_trigger !bind_bind !MIRed.core !SBRed.bind SBRed.vis !bind_trigger.
      des_ifs. gstep. r; s; econs. ss. }

    rewrite !vis_trigger !bind_bind MIRed.pg SBRed.bind SBRed.vis. des_ifs; cycle 1.
    { exfalso. bsimpl. ss. case_bool_decide; ss. eapply H. des.
      eapply (SCP k0 tt↑). eauto. }
    rewrite !vis_trigger !bind_bind. gstep; r; s; econs; i.
    rewrite !bind_ret_l SBRed.ret bind_ret_l SBRed.tau. gstep; econs.
    rewrite SBRed.ret bind_ret_l. gbase; eauto.
  }
  {
    destruct c.
    - rewrite SBRed.vis. des_ifs; cycle 1.
      { r in IMG; des. rewrite IMG0 // in Heq. }
      rewrite !vis_trigger !bind_bind MIRed.core SBRed.bind SBRed.vis !bind_trigger.
      des_ifs. gstep. r; s; econs. i.
      rewrite SBRed.ret bind_ret_l SBRed.tau.  gstep; econs.
      rewrite SBRed.ret bind_ret_l. gbase; eauto.
    - rewrite SBRed.vis. des_ifs; cycle 1.
      { r in IMG; des. rewrite IMG // in Heq. }
      rewrite !vis_trigger !bind_bind MIRed.core SBRed.bind SBRed.vis !bind_trigger.
      gstep. r; s; econs. i.
      rewrite SBRed.ret bind_ret_l SBRed.tau.  gstep; econs.
      rewrite SBRed.ret bind_ret_l. gbase; eauto.
    - rewrite SBRed.vis. des_ifs.
      + rewrite !vis_trigger !bind_bind MIRed.core SBRed.bind SBRed.vis !bind_trigger.
        gstep. r; s; econs. i.
        rewrite SBRed.ret bind_ret_l SBRed.tau.  gstep; econs.
        rewrite SBRed.ret bind_ret_l. gbase; eauto.
      + rewrite !vis_trigger !bind_bind MIRed.core SBRed.bind SBRed.vis. des_ifs.
        gstep. r; s; econs. ss.
  }
(*SLOW*)Qed.
