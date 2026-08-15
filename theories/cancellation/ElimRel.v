From CRIS.common Require Import Common ConcRA.
From CRIS.modules Require Import Sp.
From CRIS.modules Require Import SMod Mod LMod SModTr ModTr LModTr.
From CRIS.cancellation Require Import MInline.
From CRIS.simulations.msim Require Import Tactics.
From CRIS.simulations.gsim Require Import GSim.
From iris.proofmode Require Export proofmode.

Set Implicit Arguments.

Section CancelLib.
  Definition Forall3i {X Y Z}
      (R : nat → X → Y → Z → Prop)
      (xs : list X) (ys : list Y) (zs : list Z) :=
    length xs = length ys ∧ length ys = length zs ∧
    ∀ i x y z,
      xs !! i = Some x → ys !! i = Some y → zs !! i = Some z →
      R i x y z.

  Lemma Forall3i_nth {X Y Z}
      (i : nat)
      (xs : list X) (ys : list Y) (zs : list Z)
      (R: nat → X → Y → Z → Prop) :
    Forall3i R xs ys zs →
    i < List.length xs →
    (∃ x y z,
      xs !! i = Some x ∧ ys !! i = Some y ∧ zs !! i = Some z ∧
      R i x y z).
  Proof using.
    intros Hrel Hlt; destruct Hrel as [? [? ?]]. revert_until xs. revert i.
    induction xs; i.
    - destruct ys; ss. destruct zs; des; ss. destruct i; try nia.
    - destruct ys; ss. destruct zs; des; ss. destruct i; s.
      { esplits; et. }
      eapply (IHxs i ys zs (λ i, R (S i))); et; nia.
  Qed.

  Lemma list_lookup_length {X} (x : X) l :
    (l ++ [x]) !! (base.length l) = Some x.
  Proof using. eapply lookup_snoc_Some; right; eauto. Qed.
End CancelLib.

Section ELIM_REL.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition HoareSpawnE (fspo : option fspec_rel) (sspo: bool) fn varg : itree crisE nat :=
    if sspo
    then
      arg <- trigger (Choose Any.t);; tau;;
      tid <- trigger (Spawn fn arg);; tau;;
      trigger (Assume (YIELD tid));;; tau;;
      PQ <- trigger (Choose (FSpec (or_else fspo fspec_trivial)));; tau;;
      trigger (Guarantee (YIELD tid -∗ TID tid -∗ winv (⊤, ⊤) -∗ Precond PQ varg arg));;; tau;;
      Ret tid
    else
      tid <- trigger (Spawn fn varg);; tau;;
      Ret tid.

  Definition HoareYieldE (sspo : bool) (* omsk *) ntid : itree crisE () :=
    if sspo
    then
        stid <- trigger (Choose nat);; tau;;
        trigger (Guarantee (TID stid ∗ YIELD ntid ∗ winv (⊤, ⊤)));;; tau;;
        trigger (Yield ntid);;; tau;;
        trigger (Assume (TID stid ∗ YIELD stid ∗ winv (⊤, ⊤)));;; tau;;
        Ret tt
    else
        trigger (Yield ntid);;; tau;; Ret tt.

  Definition HoareGetTidE (sspo : bool) (* omsk *) : itree crisE nat :=
    if sspo
    then
        stid <- trigger (Choose nat);; tau;;
        trigger (Guarantee (TID stid));;; tau;;
        tid <- trigger GetTid;; tau;;
        trigger (Assume (⌜tid = stid⌝ ∗ TID(stid)));;; tau;;
        Ret tid
    else
        tid <- trigger GetTid;; tau;; Ret tid.

  Definition elim_precond (msk_in: bool) (fspo fspo' : option fspec_rel) varg
      : itree crisE (option (Any.t→Any.t→iProp Σ) * option (Any.t→Any.t→iProp Σ) * Any.t) :=
    '(oQ, arg): _ <-
      match fspo with
      | Some fsp =>
        PQ <- trigger (Choose (FSpec (if msk_in then fsp else fspec_trivial)));; tau;;
        arg <- trigger (Choose Any.t);; tau;;
        trigger (Guarantee (PQ.(Precond) varg arg));;; tau;; tau;;
        Ret (Some (PQ.(Postcond)), arg)
      | None =>
        tau;; Ret (None, varg)
      end;;
    match fspo' with
    | Some fsp' =>
      PQ' <- trigger (Take (FSpec fsp'));; tau;;
      varg' <- trigger (Take Any.t);; tau;;
      trigger (Assume (PQ'.(Precond) varg' arg));;; tau;;
      Ret (oQ, Some (PQ'.(Postcond)), varg')
    | None =>
      tau;; tau;; Ret (oQ, None, arg)
    end.

  Definition elim_postcond Qo Qo' vret' : itree crisE Any.t :=
    ret <-
      match Qo' with
      | Some Q' =>
        ret <- trigger (Choose Any.t);; tau;;
        trigger (Guarantee (Q' vret' ret));;; tau;; tau;; tau;;
        Ret ret
      | None =>
        tau;; tau;; Ret vret'
      end;;
    match Qo with
    | Some Q =>
      vret <- trigger (Take Any.t);; tau;;
      trigger (Assume (Q vret ret));;; tau;;
      Ret vret
    | None =>
      Ret ret
    end.

  Definition elim_spawnee_precond (fspo : option fspec_rel) (arg : Any.t)
      : itree crisE (option (Any.t → Any.t → iProp Σ) * Any.t) :=
    match fspo with
    | Some fsp =>
      PQ <- trigger (Take (FSpec fsp));; tau;;
      varg <- trigger (Take Any.t);; tau;;
      trigger (Assume (PQ.(Precond) varg arg));;; tau;;
      Ret (Some PQ.(Postcond), varg)
    | None =>
      tau;; tau;; Ret (None, arg)
    end.

  Definition elim_spawnee_postcond Qo (vret : Any.t) : itree crisE Any.t :=
    match Qo with
    | Some Q =>
      ret <- trigger (Choose Any.t);; tau;;
      trigger (Guarantee (Q vret ret));;; tau;;
      Ret ret
    | None =>
      Ret vret
    end.

  Variant elim_rel_def
      (sp : specmap) (self : ∀ T, Σ → itree crisE T → itree crisE T → Prop) (T : Type)
    : Σ → itree crisE T → itree crisE T → Prop :=

  (* handling void cases *)
  | elim_take_false ktrS itrT :
    elim_rel_def sp self ε (trigger (Take False) >>= ktrS) itrT
  | elim_tau_take_false ktrS itrT :
    elim_rel_def sp self ε (tau;; trigger (Take False) >>= ktrS) itrT
  | elim_choose_false itrS ktrT :
    elim_rel_def sp self ε itrS (trigger (Choose False) >>= ktrT)
  (* handling normal cases *)
  | elim_rel_ret v :
    elim_rel_def sp self ε (Ret v) (Ret v)
  | elim_rel_tau itrS itrT :
    self _ ε itrS itrT →
    elim_rel_def sp self ε (tau;; itrS) (tau;; itrT)
  | elim_rel_core {R} (e : coreE R) ktrS ktrT :
    (∀ (x : R), self _ ε (ktrS x) (ktrT x)) →
    elim_rel_def sp self ε (trigger e >>= ktrS) (a <- trigger e;; ktrT a)
  | elim_rel_pg {R} (e : pgE R) ktrS ktrT :
    (∀ (x : R), self _ ε (ktrS x) (ktrT x)) →
    elim_rel_def sp self ε (trigger e >>= ktrS) (a <- trigger e;; ktrT a)
  | elim_rel_ag {R} (e : agE R) ktrS ktrT :
    (∀ (x : R), self _ ε (ktrS x) (ktrT x)) →
    elim_rel_def sp self ε (trigger e >>= ktrS) (a <- trigger e;; ktrT a)
  (* handling cancellation *)
  | elim_rel_yield ntid ktrS ktrT itrS itrT :
      itrS = HoareYieldE false ntid >>= ktrS →
      itrT = HoareYieldE true ntid >>= ktrT →
      (∀ x, self _ ε (ktrS x) (ktrT x)) →
      elim_rel_def sp self ε itrS itrT
  | elim_rel_spawn fn args ktrS ktrT itrS itrT :
    itrS = HoareSpawnE None false fn args >>= ktrS →
    itrT = HoareSpawnE (sp.1 !! (funid fn)) true fn args >>= ktrT →
    (∀ x, self _ ε (ktrS x) (ktrT x)) →
    elim_rel_def sp self ε itrS itrT
  | elim_rel_precond fspo fspo' varg itrS itrT ktrT :
    (∀ P Q (VS: fspec_flat fspo P Q), ∃ P' Q', fspec_flat fspo' P' Q' ∧
      (∀ arg, P varg arg ⊢ |==> P' varg arg)
      ∧ self _ ε itrS (ktrT (if fspo then Some Q else None, if fspo' then Some Q' else None, varg))) →
    itrT = elim_precond true fspo fspo' varg >>= ktrT →
    elim_rel_def sp self ε (tau;; tau;; tau;; itrS) itrT
  | elim_rel_postcond Qo Qo' vret itrS itrT ktrT :
    (∃ Q, (Qo = Some Q ∨ (Qo = None ∧ Q = λ varg arg, ⌜varg = arg⌝%I)) ∧
      ∃ Q', (Qo' = Some Q' ∨ (Qo' = None ∧ Q' = λ varg arg, ⌜varg = arg⌝%I)) ∧
      (∀ ret, Q' vret ret ⊢ |==> Q vret ret) ∧ self _ ε itrS (ktrT vret)) →
    itrT = elim_postcond Qo Qo' vret >>= ktrT →
    elim_rel_def sp self ε (tau;; tau;; itrS) itrT
  | elim_rel_gettid ktrS ktrT itrS itrT :
    itrS = HoareGetTidE false >>= ktrS ->
    itrT = HoareGetTidE true >>= ktrT ->
    (∀ x, self _ ε (ktrS x) (ktrT x)) ->
    elim_rel_def sp self ε itrS itrT.

  Definition elim_rel sp T r_diff itrS itrT :=
    paco4 (@elim_rel_def sp) bot4 T r_diff itrS itrT.

  Lemma elim_rel_def_mon sp r1 r2 :
    r1 <4= r2 →
    @elim_rel_def sp r1 <4= elim_rel_def sp r2.
  Proof using.
    intros ??????PR; destruct PR; eauto using @elim_rel_def.
    - eapply elim_rel_precond; eauto; des_safe.
      i. specialize (H0 _ _ VS). des_safe; esplits; eauto.
    - eapply elim_rel_postcond; eauto; des_safe. esplits; eauto.
  Qed.

  Hint Resolve cpn4_wcompat: paco.
  Hint Resolve elim_rel_def_mon: paco.

  Variant elim_rel_bindC
      (r : ∀ T, Σ → itree crisE T -> itree crisE T -> Prop) T
    : Σ → itree crisE T -> itree crisE T -> Prop :=
    | elim_rel_bindC_intro R r_diff itrS itrT ktrS ktrT :
      r R r_diff itrS itrT →
      (∀ v, r T ε (ktrS v) (ktrT v)) →
      elim_rel_bindC r r_diff (itrS >>= ktrS) (itrT >>= ktrT).

  Lemma elim_rel_bindC_mon : monotone4 elim_rel_bindC.
  Proof using. ii. destruct IN; econs; eauto. Qed.

  Lemma elim_rel_bindC_spec sp :
    elim_rel_bindC <5= gupaco4 (@elim_rel_def sp) (cpn4 (@elim_rel_def sp)).
  Proof using.
    eapply wrespect4_uclo; eauto with paco.
    econs; [apply elim_rel_bindC_mon|].
    i. inv PR. apply GF in H.
    inv H; grind; eauto 6 using rclo4, elim_rel_def, elim_rel_bindC with paco.
    - ired. eapply elim_rel_yield with (ktrS := λ z, (x <- ktrS0 z;; ktrS x)) (ktrT := λ z, (x <- ktrT0 z;; ktrT x)); eauto.
      { ired; ss. } { ired; ss. }
      eauto 7 using rclo4, elim_rel_def, elim_rel_bindC with paco.
    - eapply elim_rel_spawn with (ktrS := λ z, (x <- ktrS0 z;; ktrS x)) (ktrT := λ z, (x <- ktrT0 z;; ktrT x)); eauto.
      + ired; ss.
      + rewrite /HoareSpawnE. ired. et.
      + eauto 7 using rclo4, elim_rel_def, elim_rel_bindC with paco.
    - eapply elim_rel_precond; i; et.
      specialize (H1 _ _ VS). des_safe. esplits; et.
      eapply rclo4_clo'; cycle 1.
      + econs; [eapply H3|]; et.
      + eauto using rclo4.
    - eapply elim_rel_postcond; i; et.
      des_safe. esplits; et.
      eapply rclo4_clo'; cycle 1.
      + econs; [eapply H4|]; et.
      + eauto using rclo4.
    - eapply elim_rel_gettid; rewrite /HoareGetTidE; grind. i; et.
      des_safe. esplits; et.
      eapply rclo4_clo'; cycle 1.
      + econs; [eapply H3|]; et.
      + eauto using rclo4.
  Qed.

  Lemma SBRed_HoareSpawn (msk : emask) fn varg sspo fspo
    (MSK: ∀ x, msk _ (subevent _ (Spawn fn x)) = true)
    (IMG: img_msk msk)
    :
    SB.sandbox msk (SModTr.HoareSpawn fspo sspo fn varg) =
      SModTr.HoareSpawn fspo sspo fn varg.
  Proof using.
    r in IMG; des.
    rewrite /SModTr.HoareSpawn.
    destruct sspo; cycle 1.
    { etrans; first hnorm_itr; rewrite MSK vis_trigger; erewrite bind_ret_r_rev; grind; hnorm_itr. }
    etrans; first hnorm_itr; grind.
    etrans; first hnorm_itr; rewrite MSK vis_trigger; grind.
    etrans; first hnorm_itr; rewrite IMG1 vis_trigger; grind.
    etrans; first hnorm_itr; grind.
    etrans; first hnorm_itr; grind.
    hnorm_itr.
  Qed.

  Lemma MIRed_HoareSpawn prog fspo sspo fn varg :
    inline_body prog (SModTr.HoareSpawn fspo sspo fn varg) = HoareSpawnE fspo sspo fn varg.
  Proof using.
    destruct sspo; ss; cycle 1.
    { destruct fspo; ss; cycle 1.
      { rewrite -{1}(bind_ret_r (trigger (Spawn fn varg))). rewrite MIRed.spawn.
        f_equal. extensionalities. do 2 f_equal. by rewrite MIRed.ret. }
      { rewrite -{1}(bind_ret_r (trigger (Spawn fn varg))). rewrite MIRed.spawn.
        f_equal. extensionalities. do 2 f_equal. by rewrite MIRed.ret. }
    }
    rewrite MIRed.core. f_equal. extensionalities. do 2 f_equal.
    rewrite MIRed.spawn. f_equal. extensionalities. do 2 f_equal.
    rewrite MIRed.ag. f_equal. extensionalities. do 2 f_equal.
    rewrite MIRed.core. f_equal. extensionalities. do 2 f_equal.
    rewrite MIRed.ag. f_equal. extensionalities. do 2 f_equal.
    by rewrite MIRed.ret.
  Qed.

  Lemma SBRed_HoareYield (msk: emask) sspo omsk ntid
    (MSK: msk _ (subevent _ (Yield ntid)) = true)
    (IMG: img_msk msk) :
    SB.sandbox msk (SModTr.HoareYield sspo omsk ntid) =
      SModTr.HoareYield sspo omsk ntid.
  Proof using.
    r in IMG; des.
    rewrite /SModTr.HoareYield. destruct sspo; cycle 1.
    { rewrite SBRed.vis MSK vis_trigger. rewrite -{2}(bind_ret_r (trigger (Yield _))).
      f_equal. extensionalities. rewrite SBRed.ret //. }
    etrans; [hnorm_itr|]; grind.
    etrans; [hnorm_itr|]; grind.
    etrans; [hnorm_itr|]; rewrite MSK; etrans; [hnorm_itr|]; grind.
    etrans; [hnorm_itr|]; rewrite IMG1; etrans; [hnorm_itr|]; grind.
    rewrite -{2}(bind_ret_r (trigger (Assume _))). f_equal. extensionalities.
    rewrite SBRed.ret //.
  Qed.

  Lemma MIRed_HoareYield prog sspo omsk ntid
    (MSK: SModTr.omask_check omsk (subevent _ (Yield ntid)) = true)
    :
    inline_body prog (SModTr.HoareYield sspo omsk ntid) = HoareYieldE sspo ntid.
  Proof using.
    rewrite /SModTr.HoareYield /HoareYieldE. destruct sspo; cycle 1.
    { rewrite -{1}(bind_ret_r (trigger (Yield _))) MIRed.yield.
      f_equal. extensionalities. do 2 f_equal. rewrite MIRed.ret.
      by destruct H. }
    rewrite MSK MIRed.core. f_equal. extensionalities. do 2 f_equal.
    rewrite MIRed.ag. f_equal. extensionalities. do 2 f_equal.
    rewrite MIRed.yield. f_equal. extensionalities. do 2 f_equal.
    rewrite -{1}(bind_ret_r (trigger _)).
    rewrite MIRed.ag. f_equal. extensionalities. do 2 f_equal.
    destruct H2. by rewrite MIRed.ret.
  Qed.

  Lemma SBRed_HoareGetTid (msk : emask) sspo omsk
    (MSK: msk _ (subevent _ GetTid) = true)
    (IMG: img_msk msk) :
    SB.sandbox msk (SModTr.HoareGetTid sspo omsk) =
      SModTr.HoareGetTid sspo omsk.
  Proof using.
    r in IMG. des.
    rewrite /SModTr.HoareGetTid. destruct sspo; cycle 1.
    { rewrite SBRed.vis MSK vis_trigger. rewrite -{2}(bind_ret_r (trigger _)).
      f_equal. extensionalities. rewrite SBRed.ret //. }
    rewrite SBRed.bind SBRed.vis IMG0 vis_trigger bind_bind. f_equal. extensionalities.
    rewrite SBRed.ret bind_ret_l.
    rewrite SBRed.bind SBRed.vis IMG3 vis_trigger bind_bind. f_equal. extensionalities.
    rewrite SBRed.ret bind_ret_l.
    rewrite SBRed.bind SBRed.vis MSK vis_trigger bind_bind. f_equal. extensionalities.
    rewrite SBRed.ret bind_ret_l.
    rewrite SBRed.bind SBRed.vis IMG1 vis_trigger bind_bind. f_equal. extensionalities.
    rewrite SBRed.ret bind_ret_l.
    rewrite SBRed.ret //.
  Qed.

  Lemma MIRed_HoareGetTid prog sspo omsk
    (MSK: SModTr.omask_check omsk (subevent _ GetTid) = true)
    :
    inline_body prog (SModTr.HoareGetTid sspo omsk) = HoareGetTidE sspo.
  Proof using.
    rewrite /SModTr.HoareGetTid /HoareGetTidE. destruct sspo; cycle 1.
    { rewrite -{1}(bind_ret_r (trigger GetTid)) MIRed.gettid.
      f_equal. extensionalities. do 2 f_equal. rewrite MIRed.ret.
      by destruct H. }
    rewrite MSK MIRed.core. f_equal. extensionalities. do 2 f_equal.
    rewrite MIRed.ag. f_equal. extensionalities. do 2 f_equal.
    rewrite MIRed.gettid. f_equal. extensionalities. do 2 f_equal.
    rewrite MIRed.ag. f_equal. extensionalities. do 2 f_equal.
    by rewrite MIRed.ret.
  Qed.

  Lemma if_simpl X (b: bool) (x: X): (if b then x else x) = x.
  Proof using. destruct b; et. Qed.

  Lemma MIRed_HoareFun
      (md : SMod.t) (sp : specmap) (msk : emask)
      (bd : fbody) (fspo : option fspec_rel) (arg : Any.t)
      (fno : fname) :
    (SMod.fnsems md) !! fno = Some (Some (msk, (fspo, bd))) →
    img_msk msk →
    inline_body
      (sandboxed_prog (SMod.to_mod sp md))
      (SB.sandbox_body (msk, SModTr.HoareFun fspo (SModTr.trans sp ∘ bd)) arg) =
    '(x, varg) : _ <- elim_spawnee_precond fspo arg;;
    vret <-
      inline_body
        (sandboxed_prog (SMod.to_mod sp md))
        (SB.sandbox msk (SModTr.trans sp (bd varg)));;
    elim_spawnee_postcond x vret.
  Proof using.
    intros Hfind [H1 [H2 [H3 [H4 H5]]]].
    rewrite /SModTr.HoareFun /elim_spawnee_precond /elim_spawnee_postcond /= /SB.sandbox_body.
    destruct fspo; cycle 1.
    { ired. rewrite /= SBRed.tau MIRed.tau //. }
    rewrite SBRed.bind SBRed.vis /= H1 vis_trigger !bind_bind MIRed.core.
    ired; f_equal. extensionalities x; ired; do 2 f_equal.
    rewrite SBRed.ret bind_ret_l.
    rewrite SBRed.bind SBRed.vis /= H1 vis_trigger !bind_bind MIRed.core.
    ired; f_equal. extensionalities y; ired; do 2 f_equal.
    rewrite SBRed.ret bind_ret_l.
    rewrite SBRed.bind SBRed.vis /= H3 vis_trigger !bind_bind MIRed.ag.
    ired; f_equal. extensionalities P; ired; do 2 f_equal.
    rewrite SBRed.ret bind_ret_l /precond.

    rewrite SBRed.bind MIRed.bind; f_equal.
    extensionalities vret.
    rewrite SBRed.bind SBRed.vis /= H2 vis_trigger !bind_bind MIRed.core; f_equal.
    extensionalities ret; ired; do 2 f_equal.
    rewrite SBRed.ret bind_ret_l.
    rewrite SBRed.bind SBRed.vis /= H5 vis_trigger !bind_bind MIRed.ag; f_equal.
    extensionalities b; destruct b; do 2 f_equal.
    rewrite SBRed.ret bind_ret_l.
    rewrite SBRed.ret MIRed.ret //.
  Qed.

  Lemma MIRed_HoareFun_cancel
      (md : SMod.t) (sp : specmap) (msk : emask)
      (bd : fbody) (fspo : option fspec_rel) (arg : Any.t)
      (fno : fname) :
    (SMod.fnsems md) !! fno = Some (Some (msk, (fspo, bd))) →
    img_msk msk →
    inline_body
      (sandboxed_prog (SMod.to_mod_cancel sp md))
      (SB.sandbox_body (msk, SModTr.HoareFun fspo (SModTr._trans sp (Some msk) ∘ bd)) arg) =
    '(x, varg) : _ <- elim_spawnee_precond fspo arg;;
    vret <-
      inline_body
        (sandboxed_prog (SMod.to_mod_cancel sp md))
        (SB.sandbox msk (SModTr._trans sp (Some msk) (bd varg)));;
    elim_spawnee_postcond x vret.
  Proof using.
    intros Hfind [H1 [H2 [H3 [H4 H5]]]].
    rewrite /SModTr.HoareFun /elim_spawnee_precond /elim_spawnee_postcond /= /SB.sandbox_body.
    destruct fspo; cycle 1.
    { ired. rewrite /= SBRed.tau MIRed.tau //. }
    rewrite SBRed.bind SBRed.vis /= H1 vis_trigger !bind_bind MIRed.core.
    ired; f_equal. extensionalities x; ired; do 2 f_equal.
    rewrite SBRed.ret bind_ret_l.
    rewrite SBRed.bind SBRed.vis /= H1 vis_trigger !bind_bind MIRed.core.
    ired; f_equal. extensionalities y; ired; do 2 f_equal.
    rewrite SBRed.ret bind_ret_l.
    rewrite SBRed.bind SBRed.vis /= H3 vis_trigger !bind_bind MIRed.ag.
    ired; f_equal. extensionalities P; ired; do 2 f_equal.
    rewrite SBRed.ret bind_ret_l /precond.

    rewrite SBRed.bind MIRed.bind; f_equal.
    extensionalities vret.
    rewrite SBRed.bind SBRed.vis /= H2 vis_trigger !bind_bind MIRed.core; f_equal.
    extensionalities ret; ired; do 2 f_equal.
    rewrite SBRed.ret bind_ret_l.
    rewrite SBRed.bind SBRed.vis /= H5 vis_trigger !bind_bind MIRed.ag; f_equal.
    extensionalities b; destruct b; do 2 f_equal.
    rewrite SBRed.ret bind_ret_l.
    rewrite SBRed.ret MIRed.ret //.
  Qed.

  Lemma MIRed_HoareCall md sp fn varg (msk0 msk1 : emask) fspo0 fspo1 bd1
    (WF: SMod.cancellable md)
    (IN: ∀ x, msk0 _ (subevent _ (Call fn x)) = true)
    (IMG: img_msk msk0)
    (SP: sp.1 !! (funid fn) = fspo0)
    (FIND: (SMod.fnsems md) !! (funid fn) = Some (Some (msk1, (fspo1, bd1))))
    :
    inline_body (sandboxed_prog (SMod.to_mod sp md)) (SB.sandbox msk0 (SModTr.HoareCall fspo0 (Some msk0) fn varg))
    = '(x, x0,arg):_ <- elim_precond (msk0 _ (subevent _ (Call fn varg))) fspo0 fspo1 varg;;
      vret0 <- inline_body (sandboxed_prog (SMod.to_mod sp md))
                          (SB.sandbox msk1 (SModTr.trans sp (bd1 arg)));;
      elim_postcond x x0 vret0.
  Proof using.
    destruct IMG as [H1 [H2 [H3 [H4 H5]]]].
    r in WF. hexploit WF; eauto.
    rewrite map_Forall_lookup => /(_ (funid fn) (Some (msk1, (fspo1, bd1))) FIND).
    intros [[H6 [H7 [H8 [H9 H10]]]] Hcall].
    rewrite /elim_precond /elim_postcond. ired.
    destruct fspo0 as [fsp0|]; destruct fspo1 as [fsp1|]; ss.
    { rewrite !SBRed.bind !SBRed.vis /= H2 vis_trigger !bind_bind MIRed.core. grind.
      rewrite !SBRed.ret bind_ret_l.
      rewrite !SBRed.bind !SBRed.vis /= H2 vis_trigger !bind_bind MIRed.core. grind.
      rewrite !SBRed.ret bind_ret_l.
      rewrite !SBRed.bind SBRed.vis /= H5 vis_trigger !bind_bind MIRed.ag. grind.
      rewrite !SBRed.ret bind_ret_l.

      rewrite SBRed.vis IN vis_trigger !bind_bind MIRed.call. grind.
      rewrite {2}/sandboxed_prog.
      rewrite lookup_omap {2}/SMod.to_mod /= lookup_fmap FIND /= bind_ret_l.
      rewrite /SB.sandbox_body /SModTr.trans /=.

      rewrite !SBRed.bind SBRed.vis /= H6 vis_trigger !bind_bind MIRed.core. grind.
      rewrite !SBRed.ret bind_ret_l.
      rewrite !SBRed.bind !SBRed.vis /= H6 vis_trigger !bind_bind MIRed.core. grind.
      rewrite !SBRed.ret bind_ret_l.
      rewrite !SBRed.bind !SBRed.vis /= H8 !vis_trigger !bind_bind MIRed.ag. grind.
      rewrite !SBRed.ret bind_ret_l MIRed.bind. f_equal. extensionalities.
      rewrite !SBRed.bind !SBRed.vis /= H7 !vis_trigger !bind_bind MIRed.core. grind.
      rewrite !SBRed.ret bind_ret_l.
      rewrite !SBRed.bind !SBRed.vis /= H10 !vis_trigger !bind_bind MIRed.ag. grind.
      rewrite !SBRed.ret bind_ret_l. grind.
      rewrite !SBRed.ret bind_ret_l MIRed.tau. grind.
      rewrite !SBRed.bind SBRed.vis /= H1 vis_trigger !bind_bind MIRed.core. grind.
      rewrite !SBRed.ret bind_ret_l.
      rewrite !SBRed.bind !SBRed.vis /= H3 !vis_trigger !bind_bind MIRed.ag. grind.
      rewrite !SBRed.ret bind_ret_l MIRed.ret //.
    }
    { rewrite !SBRed.bind !SBRed.vis /= H2 vis_trigger !bind_bind MIRed.core. grind.
      rewrite !SBRed.ret bind_ret_l.
      rewrite !SBRed.bind !SBRed.vis /= H2 vis_trigger !bind_bind MIRed.core. grind.
      rewrite !SBRed.ret bind_ret_l.
      rewrite !SBRed.bind SBRed.vis /= H5 vis_trigger !bind_bind MIRed.ag. grind.
      rewrite !SBRed.ret bind_ret_l.

      rewrite SBRed.vis IN vis_trigger !bind_bind MIRed.call. grind.
      rewrite {2}/sandboxed_prog.
      rewrite lookup_omap {2}/SMod.to_mod /= lookup_fmap FIND /= bind_ret_l.
      rewrite /SB.sandbox_body /SModTr.trans /=.
      rewrite !SBRed.tau; ired; rewrite MIRed.tau. grind.
      rewrite !MIRed.bind; grind.
      rewrite MIRed.tau. grind.

      rewrite !SBRed.ret bind_ret_l.
      rewrite !SBRed.bind SBRed.vis /= H1 vis_trigger !bind_bind MIRed.core. grind.
      rewrite !SBRed.ret bind_ret_l.
      rewrite !SBRed.bind !SBRed.vis /= H3 !vis_trigger !bind_bind MIRed.ag. grind.
      rewrite !SBRed.ret bind_ret_l MIRed.ret //.
    }
    { rewrite SBRed.vis IN vis_trigger MIRed.call. grind.
      rewrite {2}/sandboxed_prog.
      rewrite lookup_omap {2}/SMod.to_mod /= lookup_fmap FIND /= bind_ret_l.
      rewrite /SB.sandbox_body /SModTr.trans /=.

      rewrite !SBRed.bind SBRed.vis /= H6 vis_trigger !bind_bind MIRed.core. grind. 
      rewrite !SBRed.ret bind_ret_l.
      rewrite !SBRed.bind !SBRed.vis /= H6 !vis_trigger !bind_bind MIRed.core. grind.
      rewrite !SBRed.ret bind_ret_l.
      rewrite !SBRed.bind !SBRed.vis /= H8 !vis_trigger !bind_bind MIRed.ag. grind.
      rewrite !SBRed.ret bind_ret_l.
      rewrite !MIRed.bind; grind.
      rewrite !SBRed.bind !SBRed.vis /= H7 !vis_trigger !bind_bind MIRed.core. grind.
      rewrite !SBRed.ret bind_ret_l.
      rewrite !SBRed.bind !SBRed.vis /= H10 !vis_trigger !bind_bind MIRed.ag. grind.
      rewrite !SBRed.ret bind_ret_l. grind.
      rewrite MIRed.tau. grind.
      rewrite !SBRed.ret MIRed.ret //.
    }
    grind.
    rewrite SBRed.vis IN vis_trigger MIRed.call. grind.
    rewrite {2}/sandboxed_prog.
    rewrite lookup_omap {2}/SMod.to_mod /= lookup_fmap FIND /= bind_ret_l.
    rewrite /SB.sandbox_body /SModTr.trans /=.

    rewrite SBRed.tau; grind. rewrite MIRed.tau; grind.
    rewrite !MIRed.bind; grind.
    rewrite MIRed.tau. grind.
    rewrite !SBRed.ret MIRed.ret //.
  (*SLOW*)Qed.

  Lemma MIRed_HoareCall_cancel md sp fn varg (msk0 msk1 : emask) fspo0 fspo1 bd1
    (WF: SMod.cancellable md)
    (IN: ∀ x, msk0 _ (subevent _ (Call fn x)) = true)
    (IMG: img_msk msk0)
    (SP: sp.1 !! (funid fn) = fspo0)
    (FIND: (SMod.fnsems md) !! (funid fn) = Some (Some (msk1, (fspo1, bd1))))
    :
    inline_body (sandboxed_prog (SMod.to_mod_cancel sp md)) (SB.sandbox msk0 (SModTr.HoareCall fspo0 (Some msk0) fn varg))
    = '(x, x0,arg):_ <- elim_precond (msk0 _ (subevent _ (Call fn varg))) fspo0 fspo1 varg;;
      vret0 <- inline_body (sandboxed_prog (SMod.to_mod_cancel sp md))
                          (SB.sandbox msk1 (SModTr._trans sp (Some msk1) (bd1 arg)));;
      elim_postcond x x0 vret0.
  Proof using.
    destruct IMG as [H1 [H2 [H3 [H4 H5]]]].
    r in WF. hexploit WF; eauto.
    rewrite map_Forall_lookup => /(_ (funid fn) (Some (msk1, (fspo1, bd1))) FIND).
    intros [[H6 [H7 [H8 [H9 H10]]]] Hcall].
    rewrite /elim_precond /elim_postcond. ired.
    destruct fspo0 as [fsp0|]; destruct fspo1 as [fsp1|]; ss.
    { rewrite !SBRed.bind !SBRed.vis /= H2 vis_trigger !bind_bind MIRed.core. grind.
      rewrite !SBRed.ret bind_ret_l.
      rewrite !SBRed.bind !SBRed.vis /= H2 vis_trigger !bind_bind MIRed.core. grind.
      rewrite !SBRed.ret bind_ret_l.
      rewrite !SBRed.bind SBRed.vis /= H5 vis_trigger !bind_bind MIRed.ag. grind.
      rewrite !SBRed.ret bind_ret_l.

      rewrite SBRed.vis IN vis_trigger !bind_bind MIRed.call. grind.
      rewrite {2}/sandboxed_prog.
      rewrite lookup_omap {2}/SMod.to_mod_cancel /= lookup_fmap FIND /= bind_ret_l.
      rewrite /SB.sandbox_body /SModTr.trans_cancel /=.

      rewrite !SBRed.bind SBRed.vis /= H6 vis_trigger !bind_bind MIRed.core. grind.
      rewrite !SBRed.ret bind_ret_l.
      rewrite !SBRed.bind !SBRed.vis /= H6 vis_trigger !bind_bind MIRed.core. grind.
      rewrite !SBRed.ret bind_ret_l.
      rewrite !SBRed.bind !SBRed.vis /= H8 !vis_trigger !bind_bind MIRed.ag. grind.
      rewrite !SBRed.ret bind_ret_l MIRed.bind. f_equal. extensionalities.
      rewrite !SBRed.bind !SBRed.vis /= H7 !vis_trigger !bind_bind MIRed.core. grind.
      rewrite !SBRed.ret bind_ret_l.
      rewrite !SBRed.bind !SBRed.vis /= H10 !vis_trigger !bind_bind MIRed.ag. grind.
      rewrite !SBRed.ret bind_ret_l. grind.
      rewrite !SBRed.ret bind_ret_l MIRed.tau. grind.
      rewrite !SBRed.bind SBRed.vis /= H1 vis_trigger !bind_bind MIRed.core. grind.
      rewrite !SBRed.ret bind_ret_l.
      rewrite !SBRed.bind !SBRed.vis /= H3 !vis_trigger !bind_bind MIRed.ag. grind.
      rewrite !SBRed.ret bind_ret_l MIRed.ret //.
    }
    { rewrite !SBRed.bind !SBRed.vis /= H2 vis_trigger !bind_bind MIRed.core. grind.
      rewrite !SBRed.ret bind_ret_l.
      rewrite !SBRed.bind !SBRed.vis /= H2 vis_trigger !bind_bind MIRed.core. grind.
      rewrite !SBRed.ret bind_ret_l.
      rewrite !SBRed.bind SBRed.vis /= H5 vis_trigger !bind_bind MIRed.ag. grind.
      rewrite !SBRed.ret bind_ret_l.

      rewrite SBRed.vis IN vis_trigger !bind_bind MIRed.call. grind.
      rewrite {2}/sandboxed_prog.
      rewrite lookup_omap {2}/SMod.to_mod_cancel /= lookup_fmap FIND /= bind_ret_l.
      rewrite /SB.sandbox_body /SModTr.trans_cancel /=.
      rewrite !SBRed.tau; ired; rewrite MIRed.tau. grind.
      rewrite !MIRed.bind; grind.
      rewrite MIRed.tau. grind.

      rewrite !SBRed.ret bind_ret_l.
      rewrite !SBRed.bind SBRed.vis /= H1 vis_trigger !bind_bind MIRed.core. grind.
      rewrite !SBRed.ret bind_ret_l.
      rewrite !SBRed.bind !SBRed.vis /= H3 !vis_trigger !bind_bind MIRed.ag. grind.
      rewrite !SBRed.ret bind_ret_l MIRed.ret //.
    }
    { rewrite SBRed.vis IN vis_trigger MIRed.call. grind.
      rewrite {2}/sandboxed_prog.
      rewrite lookup_omap {2}/SMod.to_mod_cancel /= lookup_fmap FIND /= bind_ret_l.
      rewrite /SB.sandbox_body /SModTr.trans_cancel /=.

      rewrite !SBRed.bind SBRed.vis /= H6 vis_trigger !bind_bind MIRed.core. grind. 
      rewrite !SBRed.ret bind_ret_l.
      rewrite !SBRed.bind !SBRed.vis /= H6 !vis_trigger !bind_bind MIRed.core. grind.
      rewrite !SBRed.ret bind_ret_l.
      rewrite !SBRed.bind !SBRed.vis /= H8 !vis_trigger !bind_bind MIRed.ag. grind.
      rewrite !SBRed.ret bind_ret_l.
      rewrite !MIRed.bind; grind.
      rewrite !SBRed.bind !SBRed.vis /= H7 !vis_trigger !bind_bind MIRed.core. grind.
      rewrite !SBRed.ret bind_ret_l.
      rewrite !SBRed.bind !SBRed.vis /= H10 !vis_trigger !bind_bind MIRed.ag. grind.
      rewrite !SBRed.ret bind_ret_l. grind.
      rewrite MIRed.tau. grind.
      rewrite !SBRed.ret MIRed.ret //.
    }
    grind.
    rewrite SBRed.vis IN vis_trigger MIRed.call. grind.
    rewrite {2}/sandboxed_prog.
    rewrite lookup_omap {2}/SMod.to_mod_cancel /= lookup_fmap FIND /= bind_ret_l.
    rewrite /SB.sandbox_body /SModTr.trans_cancel /=.

    rewrite SBRed.tau; grind. rewrite MIRed.tau; grind.
    rewrite !MIRed.bind; grind.
    rewrite MIRed.tau. grind.
    rewrite !SBRed.ret MIRed.ret //.
  (*SLOW*)Qed.

Local Tactic Notation "estep" integer(n) := do n (gstep; econs; i).
Local Ltac edone := eauto 6 with paco.

Lemma elim_rel_cancel (md: SMod.t) T msk (itr: itree _ T)
  (WF: SMod.cancellable md)
  (IMG: img_msk msk)
  (CALL: call_msk msk)
  :
  @elim_rel (SMod.sp_from md) T ε
    (inline_body (sandboxed_prog (SMod.to_mod ∅ (SMod.cancel md)))
      (SB.sandbox msk (SModTr.trans ∅ itr)))
    (inline_body (sandboxed_prog (SMod.to_mod_cancel (SMod.sp_from md) md))
      (SB.sandbox msk (SModTr._trans (SMod.sp_from md) (Some msk) itr))).
Proof using.
  ginit. revert IMG CALL. revert T itr msk. gcofix CIH. i.
  dup WF. red in WF. dup IMG. red in IMG. des.
  assert (CASE:= case_itrH itr). des; subst.
  - rewrite !SRed.ret !SRed._ret !SBRed.ret !MIRed.ret. estep 1.
  - rewrite !SRed.tau !SRed._tau !SBRed.tau !MIRed.tau. estep 2. edone.
  - rewrite !SRed.bind !SRed.ag !SRed._bind !SRed._ag !SBRed.bind SBRed.vis IMG2 vis_trigger !bind_bind.
    rewrite !MIRed.ag. estep 2. rewrite !SBRed.ret !bind_ret_l. edone.
  - rewrite !SRed.bind !SRed.ag !SRed._bind !SRed._ag !SBRed.bind !SBRed.vis IMG3 vis_trigger !bind_bind.
    rewrite !MIRed.ag. estep 2. rewrite !SBRed.ret !bind_ret_l. edone.
  - rewrite !SRed.bind !SRed.ag !SRed._bind !SRed._ag !SBRed.bind !SBRed.vis IMG4 vis_trigger !bind_bind !MIRed.ag.
    estep 2. rewrite !SBRed.ret !bind_ret_l. edone.
  - depdes c; s.
    (* call case *)
    { rewrite !SRed.bind !SRed._bind !SBRed.bind !SRed.call !SRed._call !SBRed.tau !MIRed.bind !MIRed.tau.
      ired. estep 2. rewrite lookup_empty.
      destruct (msk _ (subevent _ (Call fn args))) eqn: E; cycle 1.
      { rewrite SBRed.vis E //= vis_trigger // MIRed.core. ired. estep 1. }
      destruct ((SMod.fnsems md) !! (funid fn)) eqn: E0; cycle 1.
      { rewrite SBRed.vis E vis_trigger -(bind_ret_r (trigger _)).
        rewrite (lookup_sp_from _ _ None) //.
        ired. rewrite SBRed.vis E vis_trigger !MIRed.bind. ired.
        rewrite -(bind_ret_r (trigger _)) !MIRed.call. ired.
        estep 1. rewrite !MIRed.bind. rewrite !lookup_omap /= !lookup_fmap E0 /=. ired.
        rewrite !MIRed.bind /=. rewrite -(bind_ret_r (trigger _)) MIRed.core. ired.
        estep 1. }
      destruct o; cycle 1.
      { rewrite SBRed.vis E vis_trigger -(bind_ret_r (trigger _)).
        rewrite (lookup_sp_from _ _ (Some None)) //.
        ired. rewrite SBRed.vis E vis_trigger !MIRed.bind. ired.
        rewrite -(bind_ret_r (trigger _)) !MIRed.call. ired.
        estep 1. rewrite !MIRed.bind. rewrite !lookup_omap /= !lookup_fmap E0 /=. ired.
        rewrite !MIRed.bind /=. rewrite -(bind_ret_r (trigger _)) MIRed.core. ired.
        estep 1.
      }
      destruct p as [img0 [fsp0 bd0]]; s.
      rewrite SBRed.vis E vis_trigger.
      rewrite MIRed.call MIRed.bind; ired.
      rewrite !MIRed.bind.
      erewrite (MIRed_HoareCall_cancel (md:=md)); eauto; cycle 1.
      { intros x; specialize (CALL fn x args) as [-> ?]; auto. }
      rewrite !lookup_omap !lookup_fmap lookup_omap E0 /=.
      rewrite /SB.sandbox_body /SModTr.trans_fnsem /= MIRed.ret; ired.
      rewrite SBRed.tau MIRed.tau; ired.

      gstep. rewrite E. eapply elim_rel_precond; last destruct fsp0; ss.
      intros P Q ?; exists P, Q; split; first done.
      split; first iIntros "% $ //".

      ired. guclo elim_rel_bindC_spec. econs.
      { gbase. rewrite map_Forall_lookup in WF; eapply WF in E0; des; eapply CIH; auto. }

      i. ired. rewrite !MIRed.tau SBRed.ret MIRed.ret. ired.
      gstep. eapply elim_rel_postcond; et.
      destruct fsp0; esplits; eauto; gbase; eapply CIH; eauto.
    }

    (* spawn case *)
    {
      rewrite !SRed.bind !SRed._bind !SBRed.bind !SRed.spawn !SRed._spawn !SBRed.tau !MIRed.bind !MIRed.tau.
      rewrite !bind_tau. estep 2.
      destruct (msk _ (subevent _ (Spawn fn args))) eqn: M; cycle 1.
      { rewrite SBRed.vis M /= vis_trigger MIRed.core. ired. estep 1. }
      rewrite !SBRed_HoareSpawn //; cycle 1.
      { i. r in CALL. hexploit (CALL fn x args). i; des; eauto. }
      { i. r in CALL. hexploit (CALL fn args x). i; des; eauto. }
      rewrite !MIRed_HoareSpawn.
      gstep. eapply elim_rel_spawn; eauto.
      i. ss. edone.
    }

    (* yield case *)
    {
      rewrite !SRed.bind !SRed.yield !SRed._bind !SRed._yield !SBRed.bind !SBRed.tau !bind_tau !MIRed.tau. estep 2.
      destruct (msk _ (subevent _ (Yield tid))) eqn:Y; cycle 1.
      { ss. rewrite SBRed.vis Y /= vis_trigger bind_bind MIRed.core. estep 1. }
      rewrite !MIRed.bind !SBRed_HoareYield // !MIRed_HoareYield; et.
      gstep. eapply elim_rel_yield; eauto.
      i; s. edone.
    }

    (* get tid case *)
    {
      rewrite !SRed.bind !SRed.gettid !SRed._bind !SRed._gettid !SBRed.bind !SBRed.tau !bind_tau !MIRed.tau. estep 2.
      destruct (msk _ (subevent _ GetTid)) eqn:Y; cycle 1.
      { ss. rewrite SBRed.vis Y /= vis_trigger bind_bind MIRed.core. estep 1. }
      rewrite !MIRed.bind !SBRed_HoareGetTid // !MIRed_HoareGetTid; et.
      gstep. eapply elim_rel_gettid; eauto.
      i; s. edone.
    }

  - rewrite !SRed.bind !SRed.pg !SRed._bind !SRed._pg !SBRed.bind. destruct s.
    + rewrite !SBRed.vis !vis_trigger. des_ifs; ired; cycle 1.
      { rewrite MIRed.core. estep 1. }
      rewrite !MIRed.pg. estep 2.
      rewrite !SBRed.ret !bind_ret_l. edone.
    + rewrite !SBRed.vis !vis_trigger. des_ifs; ired; cycle 1.
      { rewrite MIRed.core. estep 1. }
      rewrite !MIRed.pg. estep 2.
      rewrite !SBRed.ret !bind_ret_l. edone.
  - rewrite !SRed.bind !SRed.core !SRed._bind !SRed._core !SBRed.bind. destruct e.
    + rewrite !SBRed.vis !vis_trigger. des_ifs; ired; cycle 1.
      { rewrite MIRed.core. estep 1. }
      rewrite !MIRed.core. estep 2.
      rewrite !SBRed.ret !bind_ret_l. edone.
    + rewrite !SBRed.vis !vis_trigger. des_ifs; ired; cycle 1.
      { rewrite MIRed.core. estep 1. }
      rewrite !MIRed.core. estep 2.
      rewrite !SBRed.ret !bind_ret_l. edone.
    + rewrite !SBRed.vis !vis_trigger. des_ifs; ired; cycle 1.
      { rewrite MIRed.core. estep 1. }
      rewrite !MIRed.core. estep 2.
      rewrite !SBRed.ret !bind_ret_l. edone.
(*SLOW*)Qed.

End ELIM_REL.
Hint Resolve cpn4_wcompat: paco.
Hint Resolve elim_rel_def_mon: paco.

Section CancelDef.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Variant thread_rel sp cid :
      nat → Σ → itree (lmodE Σ) Any.t → itree (lmodE Σ) Any.t → Prop :=
  | thread_rel_body itrS itrT src tgt r_diff tid Qo
      (RET: tid = 0 → match Qo with | Some Q => ∀ varg arg, Q varg arg ⊢ ⌜varg = arg⌝ | _ => True end)
      (TEQ: cid = tid)
      (REL: elim_rel sp r_diff itrS itrT)
      (SRC: src = ModTr.trans itrS)
      (TGT: tgt = ModTr.trans (vret <- itrT;; elim_spawnee_postcond Qo vret)) :
     thread_rel sp cid tid r_diff src tgt
  | thread_rel_spawn src tgt r_diff tid itrS fspo varg arg bd :
     tid ≠ 0 →
     cid ≠ tid →
     src = ModTr.trans (tau;; tau;; itrS) →
     tgt = ModTr.trans (
       '(oQ, varg) : _ <- elim_spawnee_precond fspo arg;;
       vret <- bd varg;;
       elim_spawnee_postcond oQ vret) →
       (∃ P Q, (or_else fspo fspec_trivial) P Q ∧
        (Own r_diff ⊢ YIELD tid -∗ TID tid -∗ winv (⊤, ⊤) -∗ P varg arg)) →
     elim_rel sp ε itrS (bd varg) →
     thread_rel sp cid tid r_diff src tgt
  | thread_rel_yield src tgt r_diff tid itrS itrT Qo :
     cid ≠ tid →
     (tid = 0 → match Qo with | Some Q => ∀ varg arg, Q varg arg ⊢ ⌜varg = arg⌝ | _ => True end) →
     src = ModTr.trans (tau;; itrS) →
     tgt = ModTr.trans (
      tau;; trigger (Assume (TID(tid) ∗ YIELD(tid) ∗ winv(⊤, ⊤)));;;
      tau;; vret <- itrT;; elim_spawnee_postcond Qo vret) →
     elim_rel sp ε itrS itrT →
     thread_rel sp cid tid r_diff src tgt.

  Definition cancel_eq (x y : lstateT Σ * Any.t) : Prop :=
    ∃ st r_s r_t,
      x.1 = (st,r_s) ∧ y.1 = (st,r_t) ∧
      x.2 = y.2.

  Definition CANCEL_GOAL md sp R (it_src it_tgt: itree crisE R) :=
    ∀ (r_i r_s r_t : Σ)
      (rs_diff : list Σ) (srcs tgts : list (itree (lmodE Σ) Any.t))
      (cid : nat)
      (st : gmap key (option Any.t))
      (ps pt : smj)
      ktrS ktrT Qo
      (r : ∀ x x0, (x → x0 → Prop) → smj → smj → itree coreE x → itree coreE x0 → Prop)
      (WFS: SMod.cancellable md)
      (VP: sp = SMod.sp_from md)
      (CIH :
        ∀ (r_s r_t : Σ) (rs_diff : list Σ)
          (srcs tgts : list (itree (lmodE Σ) Any.t))
          (cid : nat) (st : gmap key (option Any.t)) (ps pt : smj)
          (REL : Forall3i (thread_rel sp cid) rs_diff srcs tgts)
          (WFR: ✓ r_s) (WFST: map_Forall (const is_Some) st)
          (RS: Own r_s ⊢ |==> ([∗ list] i ∈ rs_diff, Own i) ∗ Own r_t ∗
                 TIDAUTH cid ∗ YIELDAUTH (length rs_diff)),
        r (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type cancel_eq ps pt
          (LModTr.interp_stateE Any.t
              (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
                    (SMod.to_mod ∅ (SMod.cancel md))) r_i))) (cid, srcs))
              (st, r_s))
          (LModTr.interp_stateE Any.t
              (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
                    (SMod.to_mod_cancel sp md)) r_i))) (cid, tgts))
              (st, r_t)))
      (KEY: ∀ itr_s itr_t st (r_s r_t r_diff : Σ)
              (WFR: ✓ r_s) (WFST: map_Forall (const is_Some) st)
              (RS: Own r_s ⊢ |==> ([∗ list] i ∈ <[cid:=r_diff]> rs_diff, Own i) ∗ Own r_t ∗
                     TIDAUTH cid ∗ YIELDAUTH (length (<[cid:=r_diff]> rs_diff)))
              (LEN: cid < List.length srcs)
              (REL: thread_rel sp cid cid r_diff itr_s itr_t),
        gpaco7 _gsim (cpn7 _gsim) bot7 r (lstateT Σ * Any.t)%type
          (lstateT Σ * Any.t)%type cancel_eq smj_top smj_top
          (LModTr.interp_stateE Any.t
              (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
                    (SMod.to_mod ∅ (SMod.cancel md))) r_i)))
                    (cid, <[cid:=itr_s]> srcs))
              (st, r_s))
          (LModTr.interp_stateE Any.t
              (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
                    (SMod.to_mod_cancel sp md)) r_i)))
                    (cid, <[cid:=itr_t]> tgts))
              (st, r_t)))
      (EQLEN : length srcs = length tgts)
      (EQLEN2 : length rs_diff = length srcs)
      (REL : ∀ i x y z, srcs !! i = Some x → tgts !! i = Some y → rs_diff !! i = Some z →
        thread_rel sp cid i z x y)
      (WFR : ✓ r_s)
      (WFST: map_Forall (const is_Some) st)
      (RS : Own r_s ⊢
              |==> ([∗ list] i ∈ rs_diff, Own i) ∗ Own r_t ∗
              TIDAUTH cid ∗ YIELDAUTH (length rs_diff))
      (LEN : cid < length srcs)
      (x0 : srcs !! cid = Some (ModTr.trans (x <- it_src;; ktrS x)))
      (x1 : tgts !! cid = Some (ModTr.trans (x <- it_tgt;; vret <- ktrT x;; elim_spawnee_postcond Qo vret)))
      (x2 : rs_diff !! cid = Some ε)
      (RET: cid = 0 → match Qo with | Some Q => ∀ varg arg, Q varg arg ⊢ ⌜varg = arg⌝ | _ => True end)
      (KTR : ∀ x, paco4 (elim_rel_def sp) bot4 Any.t ε (ktrS x) (ktrT x)),

  gpaco7 _gsim (cpn7 _gsim) bot7 r (lstateT Σ * Any.t)%type
    (lstateT Σ * Any.t)%type cancel_eq ps pt
    (LModTr.interp_stateE Any.t
       (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
              (SMod.to_mod ∅ (SMod.cancel md))) r_i))) (cid, srcs))
       (st, r_s))
    (LModTr.interp_stateE Any.t
       (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
              (SMod.to_mod_cancel sp md)) r_i))) (cid, tgts))
       (st, r_t)).

End CancelDef.
