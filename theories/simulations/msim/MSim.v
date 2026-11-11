(* Msim is an intermediate simulation relation that stands for 'module simulation' *)
From CRIS.common Require Import Common ConcRA StatePredicate.
From iris.proofmode Require Import proofmode.
From CRIS.modules Require Import Sandbox Mod.
From CRIS.simulations.msim Require Import MSimCommon.

Section msim.
  Context {Σ : GRA} `{!stateGS Σ}.
  Context (fl_src fl_tgt : gmap fname (option (Any.t → itree crisE Any.t))).
  Context (Ist : iProp Σ).

  (** hsupd properties **)
  (* Note : iProp-style definition of hsupd (λ fmr, Own fmr ⊢ ∃ fmr0, |==> ⌜P fmr0⌝)
      incurs positivity problem when defining _msim. *)
  Definition hsupd (P : Σ → Prop) : Σ → Prop :=
    λ fmr, ✓ fmr → ∃ fmr0, P fmr0 ∧ (Own fmr ⊢ |==> Own fmr0).

  Lemma hsupd_mon P Q r (IN : hsupd P r) (LE : P <1= Q) : hsupd Q r.
  Proof using. by intros wf; specialize (IN wf); inv IN; exists x; split; des; eauto. Qed.
  Lemma hsupd_incl P : P <1= hsupd P.
  Proof using. ii; esplits; eauto. Qed.

  Lemma hsupd_merge P r (REL : hsupd (hsupd P) r) : hsupd P r.
  Proof using.
    intros wf; specialize (REL wf); destruct REL as [r1 [??]].
    hexploit Own_wand_valid; eauto.
    intros wf1; hexploit (H wf1); intros [fmr0 [??]]; exists fmr0; esplits; eauto.
    iIntros "R"; iPoseProof (H0 with "R") as "> R1"; iApply H2; done.
  Qed.

  Lemma hsupd_update P r r' (IN : hsupd P r) (UPD : r' ~~> r) :
    hsupd P r'.
  Proof using.
    dup UPD; rewrite cmra_discrete_update in UPD; specialize (UPD (Some ε)); ss; rewrite ?right_id in UPD.
    intros wfr'; hexploit (IN (UPD wfr')); i; des; eexists; split; eauto.
    iIntros "H"; iPoseProof (Own_Upd with "H") as "> H"; first eauto.
    iApply H0; done.
  Qed.

  Lemma hsupd_extends P r r' (IN : hsupd P r) (UPD : r ≼ r') :
    hsupd P r'.
  Proof using. eapply hsupd_update; eauto; eapply cmra_update_included; eauto. Qed.

  Lemma hsupd_wf P r (IN : ✓ r → hsupd P r) :
    hsupd P r.
  Proof using. intros wf; hexploit (IN wf wf); i; des; clarify; esplits; eauto. Qed.

  Variant _msim'
      (msimc : ∀ Rs Rt (RR : retr_type Σ Rs Rt), msim_type Σ Rs Rt)
      {Rs Rt} {RR : retr_type Σ Rs Rt}
      (msimi : msim_type Σ Rs Rt) : msim_type Σ Rs Rt :=

  | msim_ret
      (MSIM_RET : True)
      ps pt fmr
      v_src v_tgt
      (RET : Own fmr ⊢ |==> RR v_src v_tgt) :
    _msim' msimc msimi ps pt (Ret v_src) (Ret v_tgt) fmr

  | msim_call
      (MSIM_CALL : True)
      ps pt fmr
      fn varg k_src k_tgt FR
      (INV : Own fmr ⊢ |==> (Ist ∗ FR))
      (K : ∀ vret fmr0
            (VALID : ✓ fmr0)
            (INV : Own fmr0 ⊢ |==> (Ist ∗ FR)),
        msimi true true (k_src vret) (k_tgt vret) fmr0) :
    _msim' msimc msimi ps pt
      (trigger (Call fn varg) >>= k_src) (trigger (Call fn varg) >>= k_tgt) fmr

  | msim_io
      (MSIM_IO : True)
      ps pt fmr
      I O fn (varg : I) k_src k_tgt
      (K : ∀ (vret : O), msimi true true (k_src vret) (k_tgt vret) fmr) :
    _msim' msimc msimi ps pt
      (trigger (IO fn varg) >>= k_src) (trigger (IO fn varg) >>= k_tgt) fmr

  | msim_inline_src
      (MSIM_INLINE_SRC : True)
      ps pt fmr
      fn f varg k_src i_tgt
      (FUN : fl_src !! (funid fn) = Some (Some f))
      (K : msimi true pt (f varg >>= (λ ret, tau;; Ret ret) >>= k_src) i_tgt fmr) :
    _msim' msimc msimi ps pt (trigger (Call fn varg) >>= k_src) i_tgt fmr

  | msim_inline_tgt
      (MSIM_INLINE_TGT : True)
      ps pt fmr
      fn f varg i_src k_tgt
      (FUN : fl_tgt !! (funid fn) = Some (Some f))
      (K : msimi ps true i_src (f varg >>= (λ ret, tau;; Ret ret) >>= k_tgt) fmr) :
    _msim' msimc msimi ps pt i_src (trigger (Call fn varg) >>= k_tgt) fmr

  | msim_tau_src
      (MSIM_TAU_SRC : True)
      ps pt fmr
      i_src i_tgt
      (K : msimi true pt i_src i_tgt fmr)
    :
    _msim' msimc msimi ps pt (tau;; i_src) i_tgt fmr

  | msim_tau_tgt
      (MSIM_TAU_TGT : True)
      ps pt fmr
      i_src i_tgt
      (K : msimi ps true i_src i_tgt fmr)
    :
    _msim' msimc msimi ps pt i_src (tau;; i_tgt) fmr

  | msim_choose_src
      (MSIM_CHOOSE_SRC : True)
      ps pt fmr
      X x k_src i_tgt
      (K : msimi true pt (k_src x) i_tgt fmr)
    :
    _msim' msimc msimi ps pt (trigger (Choose X) >>= k_src) i_tgt fmr

  | msim_choose_tgt
      (MSIM_CHOOSE_TGT : True)
      ps pt fmr
      X i_src k_tgt
      (K : ∀ (x : X), msimi ps true i_src (k_tgt x) fmr)
    :
    _msim' msimc msimi ps pt i_src (trigger (Choose X) >>= k_tgt) fmr

  | msim_take_src
      (MSIM_TAKE_SRC : True)
      ps pt fmr
      X k_src i_tgt
      (K : ∀ (x : X), msimi true pt (k_src x) i_tgt fmr)
    :
    _msim' msimc msimi ps pt (trigger (Take X) >>= k_src) i_tgt fmr

  | msim_take_tgt
      (MSIM_TAKE_TGT : True)
      ps pt fmr
      X x i_src k_tgt
      (K : msimi ps true i_src (k_tgt x) fmr)
    :
    _msim' msimc msimi ps pt i_src (trigger (Take X) >>= k_tgt) fmr

  | msim_sput_src
      (MSIM_SPUT_SRC : True)
      ps pt fmr FMR
      k_src i_tgt
      k v v'
      (CUR : Own fmr ⊢ |==> k ↦src v ∗ FMR)
      (K : forall fmr0 (VALID : ✓ fmr0)
          (NEW : Own fmr0 ⊢ |==> k ↦src v' ∗ FMR),
          msimi true pt (k_src tt) i_tgt fmr0)
    :
    _msim' msimc msimi ps pt (trigger (SPut k v') >>= k_src) i_tgt fmr

  | msim_sput_tgt
      (MSIM_SPUT_TGT : True)
      ps pt fmr FMR
      i_src k_tgt
      k v v'
      (CUR : Own fmr ⊢ |==> k ↦tgt v ∗ FMR)
      (K : forall fmr0 (VALID : ✓ fmr0)
          (NEW : Own fmr0 ⊢ |==> k ↦tgt v' ∗ FMR),
          msimi ps true i_src (k_tgt tt) fmr0)
    :
    _msim' msimc msimi ps pt i_src (trigger (SPut k v') >>= k_tgt) fmr

  | msim_sget_src
      (MSIM_SGET_SRC : True)
      ps pt fmr FMR
      k_src i_tgt
      k v
      (CUR : Own fmr ⊢ |==> k ↦src v ∗ FMR)
      (K : forall fmr0 (VALID : ✓ fmr0)
          (NEW : Own fmr0 ⊢ |==> k ↦src v ∗ FMR),
          msimi true pt (k_src v) i_tgt fmr0)
    :
    _msim' msimc msimi ps pt (trigger (SGet k) >>= k_src) i_tgt fmr

  | msim_sget_tgt
      (MSIM_SGET_TGT : True)
      ps pt fmr FMR
      i_src k_tgt
      k v
      (CUR : Own fmr ⊢ |==> k ↦tgt v ∗ FMR)
      (K : forall fmr0 (VALID : ✓ fmr0)
          (NEW : Own fmr0 ⊢ |==> k ↦tgt v ∗ FMR),
          msimi ps true i_src (k_tgt v) fmr0)
    :
    _msim' msimc msimi ps pt i_src (trigger (SGet k) >>= k_tgt) fmr

  | msim_sput_src_uninit
      (MSIM_SPUT_SRC_UNINIT : True)
      ps pt fmr FMR
      k_src i_tgt
      k v'
      (CUR : Own fmr ⊢ |==> uninit_src k ∗ FMR)
      (K : forall fmr0
          (VALID : ✓ fmr0)
          (NEW : Own fmr0 ⊢ |==> k ↦src v' ∗ FMR),
          msimi true pt (k_src tt) i_tgt fmr0)
    :
    _msim' msimc msimi ps pt
      (trigger (SPut k v') >>= k_src) i_tgt fmr

  | msim_sput_tgt_uninit
      (MSIM_SPUT_TGT_UNINIT : True)
      ps pt fmr FMR
      i_src k_tgt
      k v'
      (CUR : Own fmr ⊢ |==> uninit_tgt k ∗ FMR)
      (K : forall fmr0
          (VALID : ✓ fmr0)
          (NEW : Own fmr0 ⊢ |==> k ↦tgt v' ∗ FMR),
          msimi ps true i_src (k_tgt tt) fmr0)
    :
    _msim' msimc msimi ps pt
      i_src (trigger (SPut k v') >>= k_tgt) fmr

  | msim_sget_src_uninit
      (MSIM_SGET_SRC_UNINIT : True)
      ps pt fmr FMR
      k_src i_tgt
      k
      (CUR : Own fmr ⊢ |==> uninit_src k ∗ FMR)
      (K : forall fmr0
          (VALID : ✓ fmr0)
          (NEW : Own fmr0 ⊢ |==> uninit_src k ∗ FMR),
          msimi true pt (k_src (tt↑)) i_tgt fmr0)
    :
    _msim' msimc msimi ps pt
      (trigger (SGet k) >>= k_src) i_tgt fmr

  | msim_sget_tgt_uninit
      (MSIM_SGET_TGT_UNINIT : True)
      ps pt fmr FMR
      i_src k_tgt
      k
      (CUR : Own fmr ⊢ |==> uninit_tgt k ∗ FMR)
      (K : forall fmr0
          (VALID : ✓ fmr0)
          (NEW : Own fmr0 ⊢ |==> uninit_tgt k ∗ FMR),
          msimi ps true i_src (k_tgt (tt↑)) fmr0)
    :
    _msim' msimc msimi ps pt
      i_src (trigger (SGet k) >>= k_tgt) fmr

  | msim_assume_src
      (MSIM_ASSUME_SRC : True)
      ps pt fmr
      iP k_src i_tgt FMR
      (CUR : Own fmr ⊢ |==> FMR)
      (K : ∀ fmr0 (VALID : ✓ fmr0)
          (NEW : Own fmr0 ⊢ |==> (iP ∗ FMR)),
          msimi true pt (k_src tt) i_tgt fmr0)
    :
    _msim' msimc msimi ps pt (trigger (Assume iP) >>= k_src) i_tgt fmr

  | msim_assume_tgt
      (MSIM_ASSUME_TGT : True)
      ps pt fmr
      iP i_src k_tgt FMR
      (CUR : Own fmr ⊢ |==> (iP ∗ FMR))
      (K : ∀ fmr0 (VALID : ✓ fmr0)
          (NEW : Own fmr0 ⊢ |==> FMR),
          msimi ps true i_src (k_tgt tt) fmr0)
    :
    _msim' msimc msimi ps pt i_src (trigger (Assume iP) >>= k_tgt) fmr

  | msim_assume_res_src
      (MSIM_ASSUME_RES_SRC : True)
      ps pt fmr
      r k_src i_tgt FMR
      (CUR : Own fmr ⊢ |==> FMR)
      (K : ∀ fmr0 (VALID : ✓ fmr0)
          (NEW : Own fmr0 ⊢ |==> Own r ∗ FMR),
          msimi true pt (k_src tt) i_tgt fmr0)
    :
    _msim' msimc msimi ps pt (trigger (AssumeRes r) >>= k_src) i_tgt fmr

  | msim_assume_res_tgt
      (MSIM_ASSUME_PRECISE_TGT : True)
      ps pt fmr
      r i_src k_tgt FMR
      (CUR : Own fmr ⊢ |==> Own r ∗ FMR)
      (K : ∀ fmr0 (VALID : ✓ fmr0)
          (NEW : Own fmr0 ⊢ |==> FMR),
          msimi ps true i_src (k_tgt tt) fmr0)
    :
    _msim' msimc msimi ps pt i_src (trigger (AssumeRes r) >>= k_tgt) fmr

  | msim_guarantee_src
      (MSIM_GUARANTEE_SRC : True)
      ps pt fmr
      iP k_src i_tgt FMR
      (CUR : Own fmr ⊢ |==> (iP ∗ FMR))
      (K : ∀ fmr0 (VALID : ✓ fmr0)
          (NEW : Own fmr0 ⊢ |==> FMR),
          msimi true pt (k_src tt) i_tgt fmr0)
    :
    _msim' msimc msimi ps pt (trigger (Guarantee iP) >>= k_src) i_tgt fmr

  | msim_guarantee_tgt
      (MSIM_GUARANTEE_TGT : True)
      ps pt fmr
      iP i_src k_tgt FMR
      (CUR : Own fmr ⊢ |==> FMR)
      (K : ∀ fmr0 (VALID : ✓ fmr0)
          (NEW : Own fmr0 ⊢ |==> (iP ∗ FMR)),
          msimi ps true i_src (k_tgt tt) fmr0)
    :
    _msim' msimc msimi ps pt i_src (trigger (Guarantee iP) >>= k_tgt) fmr

  | msim_spawn
      (MSIM_SPAWN : True)
      ps pt fmr
      fn arg k_src k_tgt
      (K : ∀ tid, msimi true true (k_src tid) (k_tgt tid) fmr)
    :
    _msim' msimc msimi ps pt
      (trigger (Spawn fn arg) >>= k_src) (trigger (Spawn fn arg) >>= k_tgt) fmr

  | msim_yield
      (MSIM_YIELD : True)
      ps pt fmr
      tid k_src k_tgt FR
      (INV : Own fmr ⊢ |==> (Ist ∗ FR))
      (K : ∀ fmr0
          (VALID : ✓ fmr0)
          (INV : Own fmr0 ⊢ |==> (Ist ∗ FR)),
        msimi true true (k_src ()) (k_tgt ()) fmr0)
    :
    _msim' msimc msimi ps pt (trigger (Yield tid) >>= k_src) (trigger (Yield tid) >>= k_tgt) fmr

  | msim_gettid
      (MSIM_GETTID : True)
      ps pt fmr
      k_src k_tgt
      (K : ∀ tid, msimi true true (k_src tid) (k_tgt tid) fmr)
    :
    _msim' msimc msimi ps pt
      (trigger GetTid >>= k_src) (trigger GetTid >>= k_tgt) fmr

  | msim_call_none
      (MSIM_CALL_NONE: True)
      ps pt fmr
      fn varg k_src i_tgt
      (FUN: fl_src !! (funid fn) = None)
    :
    _msim' msimc msimi ps pt (trigger (Call fn varg) >>= k_src) i_tgt fmr

  | msim_spawn_none
      (MSIM_SPAWN_NONE: True)
      ps pt fmr
      fn varg k_src i_tgt
      (FUN: fl_src !! (funid fn) = None)
    :
    _msim' msimc msimi ps pt (trigger (Spawn fn varg) >>= k_src) i_tgt fmr

  | msim_progress
      (MSIM_PROGRESS : True)
      i_src i_tgt fmr
      (SIM : msimc Rs Rt RR false false i_src i_tgt fmr)
    :
    _msim' msimc msimi true true i_src i_tgt fmr
  .
  Global Arguments _msim' msimc {Rs Rt} RR msimi.

  Inductive _msim msim Rs Rt RR ps pt i_src i_tgt fmr : Prop :=
  | msim_intro
      (IN : ∀ (NODFS : map_Forall (const is_Some) (fl_src))
               (NODFT : map_Forall (const is_Some) (fl_tgt)),
        hsupd (@_msim' msim Rs Rt RR (@_msim msim Rs Rt RR) ps pt i_src i_tgt) fmr).

  Definition msim {Rs Rt} RR := paco8 _msim bot8 Rs Rt RR.

  Lemma _msim_tarski msim Rs Rt RR rel
      (FIX : ∀ ps pt i_src i_tgt fmr
             (IN : ∀ (NODFS : map_Forall (const is_Some) (fl_src))
                (NODFT : map_Forall (const is_Some) (fl_tgt)),
                hsupd (@_msim' msim Rs Rt RR rel ps pt i_src i_tgt) fmr),
        rel ps pt i_src i_tgt fmr) :
    _msim msim Rs Rt RR <5= rel.
  Proof using.
    fix self 6. i.
    destruct PR. apply FIX. i. intros wf.
    specialize (IN NODFS NODFT wf); des.
    exists fmr0; split; eauto.
    destruct IN;
      try by econs; et; i; hexploit K; et; i; des; esplits;
      eauto using @_msim' with paco.
  Qed.

  Lemma _msim'_mon r r' Rs Rt RR s s'
      ps pt sti_src sti_tgt fmr
      (REL : @_msim' r Rs Rt RR s ps pt sti_src sti_tgt fmr)
      (LEr : r <8= r')
      (LEs : s <5= s') :
    @_msim' r' Rs Rt RR s' ps pt sti_src sti_tgt fmr.
  Proof using.
    ii. destruct REL. all: try by econs; et; i; hexploit K; et; i; des; esplits; eauto using _msim'.
  Qed.

  Lemma _msim_mon : monotone8 _msim.
  Proof using. ii. eapply _msim_tarski, IN. i. econs. eauto using hsupd_mon, _msim'_mon. Qed.

  Lemma _msim_mon_auto r r' Rs Rt RR
      ps pt sti_src sti_tgt fmr
      (REL : _msim r Rs Rt RR ps pt sti_src sti_tgt fmr)
      (LEr : r <8= r') :
    _msim r' Rs Rt RR ps pt sti_src sti_tgt fmr.
  Proof using. eapply _msim_mon; eauto. Qed.

  Hint Constructors _msim' _msim : core.
  Hint Unfold msim : core.
  Hint Resolve _msim_mon : paco.
  Hint Resolve hsupd_mon _msim'_mon _msim_mon_auto : paco.
  Hint Resolve cpn8_wcompat : paco.

  (* Definition msim_body ps pt sti_src sti_tgt fmr :=
    @msim _ _ (@ist_with_eq _ Ist Any.t) ps pt sti_src sti_tgt fmr. *)

  Lemma _msim_flag_mon r Rs Rt RR (ps pt ps' pt' : bool) st_src st_tgt fmr
      (SIM : _msim r Rs Rt RR ps pt st_src st_tgt fmr)
      (LES : ps → ps')
      (LET : pt → pt') :
    _msim r Rs Rt RR ps' pt' st_src st_tgt fmr.
  Proof using.
    move SIM before r. revert_until SIM.
    pattern ps, pt, st_src, st_tgt, fmr.
    eapply _msim_tarski, SIM. i. econs.
    ii. specialize (IN NODFS NODFT H). des.
    destruct IN; try by esplits; et; econs; et; i; hexploit K; et; i; des; esplits; et.

    hexploit LES; eauto; intros Hps'.
    hexploit LET; eauto; intros Hpt'.
    assert (ps' = true) as ->.
    { destruct ps'; [done|exact Hps']. }
    assert (pt' = true) as ->.
    { destruct pt'; [done|exact Hpt']. }
    exists fmr1. split; last exact IN0.
    eapply msim_progress; [done|exact SIM0].
  Qed.

  Lemma msim_flag_mon Rs Rt RR (ps pt ps' pt' : bool) st_src st_tgt fmr
      (SIM : @msim Rs Rt RR ps pt st_src st_tgt fmr)
      (LES : ps → ps')
      (LET : pt → pt') :
    msim RR ps' pt' st_src st_tgt fmr.
  Proof using.
    move SIM before RR. revert_until SIM. pcofix CIH. i.
    pstep. eapply _msim_flag_mon; eauto.
    eapply paco8_mon_bot in SIM; eauto. punfold SIM.
  Qed.

  Lemma msim_progress_flag Rs Rt RR r g st_src st_tgt fmr
      (SIM : gpaco8 _msim (cpn8 _msim) g g Rs Rt RR false false st_src st_tgt fmr) :
    gpaco8 _msim (cpn8 _msim) r g Rs Rt RR true true st_src st_tgt fmr.
  Proof using. gstep. econs. r; esplits; eauto. Qed.

  (** msimC **)
  Definition msimC msim Rs Rt RR ps pt sti_src sti_tgt fmr :=
    hsupd (@_msim' msim Rs Rt RR (msim Rs Rt RR) ps pt sti_src sti_tgt) fmr.

  Lemma msimC_mon : monotone8 msimC.
  Proof using.
    ii. specialize (IN H). des.
    destruct IN;
      try by econs; esplits; et; econs; et; i; hexploit K; et; i; des; eauto.
  Qed.

  Lemma msimC_spec : msimC <9= gupaco8 _msim (cpn8 _msim).
  Proof using.
    eapply wrespect8_uclo; eauto with paco.
    econs; eauto using msimC_mon; i.
    econs. ii. destruct PR; eauto. des. esplits; eauto.
    eapply _msim'_mon; eauto using rclo8, _msim_mon_auto; i.
  Qed.

  (** msim_flagC**)
  Variant msim_flagC
      (r : ∀ (Rs Rt : Type) (RR : retr_type Σ Rs Rt), msim_type Σ Rs Rt)
      Rs Rt RR ps1 pt1 st_src st_tgt fmr : Prop :=
  | msim_flagC_intro ps0 pt0
    (SIM : r Rs Rt RR ps0 pt0 st_src st_tgt fmr)
    (SRC : ps0 = true → ps1 = true)
    (TGT : pt0 = true → pt1 = true).

  Lemma msim_flagC_mon r1 r2 (LE : r1 <8= r2) :
    msim_flagC r1 <8= msim_flagC r2.
  Proof using. ii. destruct PR; econs; et. Qed.

  Hint Resolve msim_flagC_mon : paco.

  Lemma msim_flagC_spec : msim_flagC <9= gupaco8 _msim (cpn8 _msim).
  Proof using.
    eapply wrespect8_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR.
    eauto using _msim_flag_mon, _msim_mon_auto, rclo8.
  Qed.

  Lemma msim_flag_down Rs Rt RR r g ps pt st_src st_tgt fmr
      (SIM : gpaco8 _msim (cpn8 _msim) r g Rs Rt RR false false st_src st_tgt fmr) :
    gpaco8 _msim (cpn8 _msim) r g Rs Rt RR ps pt st_src st_tgt fmr.
  Proof using. guclo msim_flagC_spec. econs; et. Qed.

  (** msim_bindC **)
  Variant msim_bindC
      (r : ∀ Rs Rt (RR : retr_type Σ Rs Rt), msim_type Σ Rs Rt)
    : ∀ Rs Rt (RR : retr_type Σ Rs Rt), msim_type Σ Rs Rt :=
  | msim_bindC_intro
      ps pt Qs Qt QQ i_src i_tgt fmr
      Rs Rt RR k_src k_tgt
      (SIM : r Qs Qt QQ ps pt i_src i_tgt fmr)
      (SIMK : ∀ vret_src vret_tgt fmr0
          (RET : Own fmr0 ⊢ |==> QQ vret_src vret_tgt),
        r Rs Rt RR false false (k_src vret_src) (k_tgt vret_tgt) fmr0) :
    msim_bindC r Rs Rt RR ps pt (i_src >>= k_src) (i_tgt >>= k_tgt) fmr.

  Lemma msim_bindC_mon r1 r2 (LEr : r1 <8= r2) : msim_bindC r1 <8= msim_bindC r2.
  Proof using. ii. destruct PR; econs; et. Qed.

  Lemma msim_bindC_wrespectful : wrespectful8 _msim msim_bindC.
  Proof using.
    econs; eauto using msim_bindC_mon; i.
    destruct PR. apply GF in SIM.
    move SIM before GF. revert_until SIM.
    pattern ps, pt, i_src, i_tgt, fmr.
    eapply _msim_tarski, SIM. econs. i. apply hsupd_merge.
    econs; esplits; eauto.
    subst. specialize (IN NODFS NODFT H). des.
    depdes IN; grind;
      try (by rr; i; esplits; eauto with paco arith);
      try (by do 2 (econs; esplits; eauto with paco arith);
              repeat rewrite <-bind_bind;
              eauto 6 using rclo8, msim_bindC).
    - exploit SIMK; eauto.
      i. apply GF in x0. eapply (_msim_flag_mon _ _ _ _ _  _ ps0 pt0) in x0; try by i; clarify.
      destruct x0. eapply hsupd_update in IN; eauto.
      eapply _msim_mon_auto; eauto using rclo8.
      eapply Own_bupd_update; eauto.
    (* - esplits; et. econs; et. i. hexploit K; et; i; des. esplits; et. *)
  Qed.

  Lemma msim_bindC_spec : msim_bindC <9= gupaco8 _msim (cpn8 _msim).
  Proof using. intros. eapply wrespect8_uclo; eauto with paco. apply msim_bindC_wrespectful. Qed.

  (** msim_extendC *)
  Variant msim_extendC
    (r : ∀ Rs Rt (RR : retr_type Σ Rs Rt), msim_type Σ Rs Rt) :
    ∀ Rs Rt (RR : retr_type Σ Rs Rt), msim_type Σ Rs Rt :=
  | msim_extendC_intro
      ps pt Rs Rt RR sti_src sti_tgt fmr fmr'
      (SIM : r Rs Rt RR ps pt sti_src sti_tgt fmr)
      (EXT : fmr ≼ fmr') :
    msim_extendC r Rs Rt RR ps pt sti_src sti_tgt fmr'.

  Lemma msim_extendC_mon r1 r2 (LEr : r1 <8= r2) : msim_extendC r1 <8= msim_extendC r2.
  Proof using. ii. destruct PR; econs; et. Qed.

  Lemma msim_extendC_compatible : compatible8 _msim msim_extendC.
  Proof using.
    econs; eauto using msim_extendC_mon.
    intros. destruct PR. destruct SIM. econs. i.
    eapply hsupd_extends; eauto.
    eapply _msim_mon_auto; eauto.
    i. econs; eauto; refl.
  Qed.

  Lemma msim_extendC_spec : msim_extendC <9= gupaco8 _msim (cpn8 _msim).
  Proof using.
    intros. gclo. econs; eauto using msim_extendC_compatible.
    eapply msim_extendC_mon, PR; eauto with paco.
  Qed.

  (** msim_wfC *)
  Variant msim_wfC (r : ∀ Rs Rt (RR : retr_type Σ Rs Rt), msim_type Σ Rs Rt):
    ∀ Rs Rt (RR : retr_type Σ Rs Rt), msim_type Σ Rs Rt :=
  | msim_wfC_intro
      ps pt Rs Rt RR sti_src sti_tgt fmr
      (SIM : ✓ fmr → r Rs Rt RR ps pt sti_src sti_tgt fmr) :
    msim_wfC r Rs Rt RR ps pt sti_src sti_tgt fmr.

  Lemma msim_wfC_mon r1 r2 (LEr : r1 <8= r2) : msim_wfC r1 <8= msim_wfC r2 .
  Proof using. ii. destruct PR. econs; eauto using hsupd_mon. Qed.

  Lemma msim_wfC_compatible : compatible8 _msim msim_wfC.
  Proof using.
    econs; eauto using msim_wfC_mon.
    i. destruct PR. econs. i. eapply hsupd_wf. i.
    eapply _msim_mon_auto; eauto 10 using msim_wfC, hsupd_incl with paco.
  Qed.

  Lemma msim_wfC_spec : msim_wfC <9= gupaco8 _msim (cpn8 _msim).
  Proof using.
    intros. gclo. econs; eauto using msim_wfC_compatible.
    eapply msim_wfC_mon, PR; eauto with paco.
  Qed.

  (** msim_updateC **)
  Variant msim_updateC (r : ∀ Rs Rt (RR : retr_type Σ Rs Rt), msim_type Σ Rs Rt):
    ∀ Rs Rt (RR : retr_type Σ Rs Rt), msim_type Σ Rs Rt :=
  | msim_updateC_intro
      ps pt Rs Rt RR sti_src sti_tgt fmr
      (SIM : hsupd (r Rs Rt RR ps pt sti_src sti_tgt) fmr) :
    msim_updateC r Rs Rt RR ps pt sti_src sti_tgt fmr.

  Lemma msim_updateC_mon r1 r2 (LEr : r1 <8= r2) : msim_updateC r1 <8= msim_updateC r2.
  Proof using. ii. destruct PR. econs; eauto using hsupd_mon. Qed.

  Lemma msim_updateC_compatible : compatible8 _msim msim_updateC.
  Proof using.
    econs; eauto using msim_updateC_mon.
    i. destruct PR. econs. i. eapply hsupd_merge.
    eapply hsupd_mon; eauto.
    i. destruct PR.
    eauto 10 using msim_updateC, hsupd_incl with paco.
  Qed.

  Lemma msim_updateC_spec : msim_updateC <9= gupaco8 _msim (cpn8 _msim).
  Proof using.
    intros. gclo. econs; eauto using msim_updateC_compatible.
    eapply msim_updateC_mon, PR; eauto with paco.
  Qed.

  (** msim_frameC *)
  Variant msim_frameC
      (r : ∀ Rs Rt (RR : retr_type Σ Rs Rt), msim_type Σ Rs Rt) :
    ∀ Rs Rt (RR : retr_type Σ Rs Rt), msim_type Σ Rs Rt :=
  | msim_frameC_intro
      ps pt Rs Rt RR sti_src sti_tgt fmr fmrc (CTX : iProp Σ)
      (SIM : r Rs Rt (λ s t, CTX -∗ RR s t)%I ps pt sti_src sti_tgt fmr)
      (UPD : Own fmrc ⊢ |==> (Own fmr ∗ CTX)) :
    msim_frameC r Rs Rt RR ps pt sti_src sti_tgt fmrc.

  Lemma msim_frameC_mon r1 r2 (LEr : r1 <8= r2) : msim_frameC r1 <8= msim_frameC r2.
  Proof using. ii. destruct PR. econs; eauto using hsupd_mon. Qed.

  Lemma msim_frameC_compatible : compatible8 _msim msim_frameC.
  Proof using.
    econs; first by eauto using msim_frameC_mon. ii.
    destruct PR. move SIM before r. revert_until SIM.
    pattern ps, pt, sti_src, sti_tgt, fmr.
    eapply _msim_tarski, SIM. i. econs. i.
    econs; esplits; eauto.
    exploit IN; eauto.
    { eapply Own_wand_valid; last by eauto. iIntros "O"; iMod (UPD with "O") as "[O1 O2]"; done. }
    i. des.
    assert (Own fmrc ⊢ |==> (Own fmr1 ∗ CTX)).
    { iIntros "H". iPoseProof (UPD with "H") as "H". iMod "H" as "[F C]".
      iFrame. iApply Own_Upd; eauto.
      by eapply Own_bupd_update; eauto.
    }

    depdes x0; grind; try by econs; eauto.
    - (* Ret *)
      econs; eauto.
      iIntros "H"; iMod (H0 with "H") as "[H C]"; by iMod (RET with "H C") as "$".
    - (* Call *)
      econs; eauto.
      + instantiate (1:= (FR ∗ CTX)%I).
        rewrite H0; iIntros "> [H $]"; iApply INV; done.
      + i. econs. i. apply hsupd_merge. ii. esplits; eauto.
        rewrite assoc in INV0. hexploit (Own_bupd_split fmr2); eauto; i; des.
        eapply (K _ a1); eauto using cmra_valid_op_l.
        { iIntros "?"; iApply H3; iFrame; done. }
        { rewrite H2 H4; iIntros "> [$ $] //". }

    - (* SPut src *)
      econs; eauto.
      { instantiate (1 := (FMR ∗ CTX)%I). instantiate (1 := v).
        iIntros "H".
        iPoseProof (H0 with "H") as ">[H $]".
        iPoseProof (CUR with "H") as "H"; et.
      }
      i. econs. i. apply hsupd_merge. ii. esplits; eauto.
      rewrite assoc in NEW.
      hexploit (Own_bupd_split fmr2); eauto; i; des.
      eapply (K a1); eauto using cmra_valid_op_l.
      { rewrite H3. et. }
      { rewrite H2 H4. et. }

    - (* SPut tgt *)
      econs; eauto.
      { instantiate (1 := (FMR ∗ CTX)%I). instantiate (1 := v).
        iIntros "H".
        iPoseProof (H0 with "H") as ">[H $]".
        iPoseProof (CUR with "H") as "H"; et.
      }
      i. econs. i. apply hsupd_merge. ii. esplits; eauto.
      rewrite assoc in NEW.
      hexploit (Own_bupd_split fmr2); eauto; i; des.
      eapply (K a1); eauto using cmra_valid_op_l.
      { rewrite H3. et. }
      { rewrite H2 H4. et. }

    - (* SGet src *)
      econs; eauto.
      { instantiate (1 := (FMR ∗ CTX)%I). instantiate (1 := v).
        iIntros "H".
        iPoseProof (H0 with "H") as ">[H $]".
        iPoseProof (CUR with "H") as "H"; et.
      }
      i. econs. i. apply hsupd_merge. ii. esplits; eauto.
      rewrite assoc in NEW.
      hexploit (Own_bupd_split fmr2); eauto; i; des.
      eapply (K a1); eauto using cmra_valid_op_l.
      { rewrite H3. et. }
      { rewrite H2 H4. et. }

    - (* SGet tgt *)
      econs; eauto.
      { instantiate (1 := (FMR ∗ CTX)%I). instantiate (1 := v).
        iIntros "H".
        iPoseProof (H0 with "H") as ">[H $]".
        iPoseProof (CUR with "H") as "H"; et.
      }
      i. econs. i. apply hsupd_merge. ii. esplits; eauto.
      rewrite assoc in NEW.
      hexploit (Own_bupd_split fmr2); eauto; i; des.
      eapply (K a1); eauto using cmra_valid_op_l.
      { rewrite H3. et. }
      { rewrite H2 H4. et. }

    - (* SPut src, uninitialized *)
      eapply msim_sput_src_uninit; eauto.
      { instantiate (1 := (FMR ∗ CTX)%I).
        iIntros "H".
        iPoseProof (H0 with "H") as ">[H $]".
        iPoseProof (CUR with "H") as "H"; et.
      }
      i. econs. i. apply hsupd_merge. ii. esplits; eauto.
      rewrite assoc in NEW.
      hexploit (Own_bupd_split fmr2); eauto; i; des.
      eapply (K a1); eauto using cmra_valid_op_l.
      { rewrite H3. et. }
      { rewrite H2 H4. et. }

    - (* SPut tgt, uninitialized *)
      eapply msim_sput_tgt_uninit; eauto.
      { instantiate (1 := (FMR ∗ CTX)%I).
        iIntros "H".
        iPoseProof (H0 with "H") as ">[H $]".
        iPoseProof (CUR with "H") as "H"; et.
      }
      i. econs. i. apply hsupd_merge. ii. esplits; eauto.
      rewrite assoc in NEW.
      hexploit (Own_bupd_split fmr2); eauto; i; des.
      eapply (K a1); eauto using cmra_valid_op_l.
      { rewrite H3. et. }
      { rewrite H2 H4. et. }

    - (* SGet src, uninitialized *)
      eapply msim_sget_src_uninit; eauto.
      { instantiate (1 := (FMR ∗ CTX)%I).
        iIntros "H".
        iPoseProof (H0 with "H") as ">[H $]".
        iPoseProof (CUR with "H") as "H"; et.
      }
      i. econs. i. apply hsupd_merge. ii. esplits; eauto.
      rewrite assoc in NEW.
      hexploit (Own_bupd_split fmr2); eauto; i; des.
      eapply (K a1); eauto using cmra_valid_op_l.
      { rewrite H3. et. }
      { rewrite H2 H4. et. }

    - (* SGet tgt, uninitialized *)
      eapply msim_sget_tgt_uninit; eauto.
      { instantiate (1 := (FMR ∗ CTX)%I).
        iIntros "H".
        iPoseProof (H0 with "H") as ">[H $]".
        iPoseProof (CUR with "H") as "H"; et.
      }
      i. econs. i. apply hsupd_merge. ii. esplits; eauto.
      rewrite assoc in NEW.
      hexploit (Own_bupd_split fmr2); eauto; i; des.
      eapply (K a1); eauto using cmra_valid_op_l.
      { rewrite H3. et. }
      { rewrite H2 H4. et. }

    - (* Assume src *)
      econs; eauto. i.
      econs. i. apply hsupd_merge. ii. esplits; eauto.
      rewrite assoc in NEW. hexploit (Own_bupd_split fmr2); eauto. i; des.
      eapply (K a1); eauto using cmra_valid_op_l.
      { iIntros "H1"; iPoseProof (H3 with "H1") as "[P H1]". iMod (CUR with "H1") as "?"; iModIntro; iFrame. }
      { iIntros "H2"; iPoseProof (H2 with "H2") as "> [H1 H2]"; iPoseProof (H4 with "H2") as "?"; iModIntro; iFrame. }

    - (* Assume tgt *)
      econs; eauto.
      { instantiate (1:= (FMR ∗ CTX)%I).
        iIntros "H". iPoseProof (H0 with "H") as "H". iMod "H" as "[F C]".
        iFrame. iStopProof; eauto. }
      i. econs. i. apply hsupd_merge. ii. esplits; eauto.
      hexploit (Own_bupd_split fmr2); eauto; i; des.
      eapply (K a1); eauto using cmra_valid_op_l.
      { iIntros "H". iModIntro; iApply H3; done. }
      { iIntros "H". iPoseProof (H2 with "H") as "H". iMod "H" as "[HP HQ]".
        iFrame. iModIntro; iApply H4; done.
      }

    - (* AssumeRes src *)
      econs; eauto; intros r2 Hvr2 Hr2.
      econs; ii; apply hsupd_merge; intros Hrv2; esplits; eauto.
      revert Hr2; rewrite assoc.
      intros [r21 [r22 [Hr2 [Hr21 [Hr22 Hvr21r22]]]]]
        %Own_bupd_split; eauto.
      eapply (K r21); eauto using cmra_valid_op_l.
      { rewrite Hr21 CUR; iIntros "[$ > $] //". }
      { rewrite Hr2 Hr22 //. }

    - (* AssumeRes tgt *)
      econs; et.
      { rewrite H0 CUR; iIntros "> [> [$ A] B]"; iCombine "A" "B" as "A"; iExact "A". }
      (* { ii; eapply K; eauto. }
      { intros PRE; rewrite H0 CUR //; iIntros "> [> [$ F] C]"; iCombine "C" "F" as "C"; iApply "C". } *)
      intros r2 Hvr2
        [r21 [r22 [Hr2 [Hr21 [Hr22 Hvr21r22]]]]]
        %Own_bupd_split; eauto.
      eapply (K r21); eauto using cmra_valid_op_l.
      { rewrite Hr21; iIntros "$ //". }
      { rewrite Hr2 Hr22 comm //. }

    - (* Guarantee src *)
      econs; eauto.
      { instantiate (1:= (FMR ∗ CTX)%I).
        iIntros "H". iPoseProof (H0 with "H") as "H". iMod "H" as "[F C]".
        iFrame. iStopProof; eauto. }
      i. econs. i. apply hsupd_merge. ii. esplits; eauto.
      hexploit (Own_bupd_split fmr2); eauto; i; des.
      eapply (K a1); eauto using cmra_valid_op_l.
      { iIntros "H". iModIntro; iApply H3; done. }
      { iIntros "H". iPoseProof (H2 with "H") as "H". iMod "H" as "[HP HQ]".
        iFrame. iModIntro; iApply H4; done.
      }

    - (* Guarantee tgt *)
      econs; eauto. i.
      econs. i. apply hsupd_merge. ii. esplits; eauto.
      rewrite assoc in NEW. hexploit (Own_bupd_split fmr2); eauto. i; des.
      eapply (K a1); eauto using cmra_valid_op_l.
      { iIntros "H1"; iPoseProof (H3 with "H1") as "[P H1]". iMod (CUR with "H1") as "?"; iModIntro; iFrame. }
      { iIntros "H2"; iPoseProof (H2 with "H2") as "> [H1 H2]"; iPoseProof (H4 with "H2") as "?"; iModIntro; iFrame. }

    - (* Yield *)
      econs; eauto.
      + instantiate (1:= (FR ∗ CTX)%I).
        iIntros "C"; iPoseProof (H0 with "C") as "> [H1 CTX]"; iPoseProof (INV with "H1") as ">?".
        iModIntro; iFrame; done.
      + i. econs. i. apply hsupd_merge. ii. esplits; eauto.
        rewrite assoc in INV0. exploit (Own_bupd_split fmr2); eauto; i; des.
        eapply (K a1); eauto using cmra_valid_op_l.
        { iIntros "H2"; iModIntro; iApply x2; done. }
        { iIntros "H2"; iPoseProof (x0 with "H2") as "> [H1 H2]"; iPoseProof (x3 with "H2") as "?".
          iModIntro; iFrame.
        }

    - (* progress *)
      eauto using msim_frameC with paco.
  Qed.

  Lemma msim_frameC_spec : msim_frameC <9= gupaco8 _msim (cpn8 _msim).
  Proof using.
    intros. gclo. econs; eauto using msim_frameC_compatible.
    eapply msim_frameC_mon, PR; eauto with paco.
  Qed.

  (** msim_nodupC **)
  Variant msim_nodupC (r : ∀ Rs Rt (RR : retr_type Σ Rs Rt), msim_type Σ Rs Rt):
    ∀ Rs Rt (RR : retr_type Σ Rs Rt), msim_type Σ Rs Rt :=
  | msim_nodupC_intro
      ps pt Rs Rt RR i_src i_tgt fmr
      (SIM : ∀ (NODFS : map_Forall (const is_Some) (fl_src))
               (NODFT : map_Forall (const is_Some) (fl_tgt)),
             r Rs Rt RR ps pt i_src i_tgt fmr) :
    msim_nodupC r Rs Rt RR ps pt i_src i_tgt fmr.

  Lemma msim_nodupC_mon r1 r2 (LEr : r1 <8= r2) :
    msim_nodupC r1 <8= msim_nodupC r2.
  Proof using. ii. destruct PR. econs; eauto using hsupd_mon. Qed.

  Lemma msim_nodupC_compatible : compatible8 _msim msim_nodupC.
  Proof using.
    econs; eauto using msim_nodupC_mon.
    i. destruct PR. econs. ii.
    edestruct SIM; eauto. edestruct IN; des; eauto.
    esplits; eauto.
    eapply _msim'_mon; eauto using msim_nodupC, _msim_mon.
  Qed.

  Lemma msim_nodupC_spec : msim_nodupC <9= gupaco8 _msim (cpn8 _msim).
  Proof using.
    intros. gclo. econs; eauto using msim_nodupC_compatible.
    eapply msim_nodupC_mon, PR; eauto with paco.
  Qed.
End msim.

Hint Resolve _msim_mon : paco.
Hint Resolve cpn8_wcompat : paco.
