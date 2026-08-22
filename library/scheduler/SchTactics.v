From CRIS.common Require Import CRIS.
From CRIS.simulations.msim Require Import ITactics MSim WSim.
From CRIS.scheduler Require Export SchHeader SchA.
From CRIS.lib Require Import ltac2_lib.

Section wsim.
  Context `{!crisG Γ Σ α β τ _S _I, !stateGS Σ, !schGS}.

  Context (fl_s fl_t : gmap fname (option (Any.t → itree crisE Any.t))).
  Context (Ist : iProp Σ).
  Context (R_s R_t : Type).
  Context (RR : retr_type Σ R_s R_t).
  Context (ps pt : bool).
  Context (N : namespace).

  Lemma wsim_yield_tgt_rr
      (E : coPset) (g : WSim.rel)
      (k_s : () → itree crisE R_s) (k_t : () → itree crisE R_t)
      (msk_s msk_t : emask) (sp_s sp_t : specmap) :
    sp_s.1 !! (fid SchHdr.yield) = None →
    sp_t.1 !! (fid SchHdr.yield) = None →
    (msk_t _ (subevent _ (Call SchHdr.yield.1 ()↑))) →
    Ist ∗
    (Ist -∗
      wsim fl_s fl_t Ist (E, E) g R_s R_t RR true true
        ((SB.sandbox msk_s (SModTr.trans sp_s 𝒴)) >>= k_s)
        (k_t tt)) ⊢
    wsim fl_s fl_t Ist (E, E) g R_s R_t RR ps pt
      ((SB.sandbox msk_s (SModTr.trans sp_s 𝒴)) >>= k_s)
      ((SB.sandbox msk_t (SModTr.trans sp_t 𝒴)) >>= k_t).
  Proof using.
    intros Hsps Hspt Hcall. iIntros "?".
    cCoind CIH g' Hg with ps pt. iIntros "[IST SIM]".
    rewrite {2 3}yield_unfold.
    
    cStepsS. cNormS.
    cStepsT. cStepsT. destruct _q; cStepsT; cycle 1.
    { cForceS (Some false).
      iPoseProof ("SIM" with "IST") as "SIM".
      iPoseProof (wsim_mono_knowledge with "SIM") as "SIM"; cycle 1.
      { iApply "SIM". }
      { iIntros (???????) "P !>". iApply Hg; ss. }
    }
    destruct b; cycle 1.
    { cForceS (Some false).
      cByCoind CIH; try et. iFrame. }

    cForceS (Some true). cStepsT. cStepS.
    rewrite Hsps Hspt.
    cNormS. des_if; cStepsS; ss.
    cStepsT. rewrite Hcall; cStepsT.
    cCall "IST" as (ret) "IST".
    cStepsT.
    cByCoind CIH; try et. iFrame.
  (*SLOW*)Qed.

  Lemma wsim_yield_tgt_ir
      (Es : coPset) (g : WSim.rel)
      (k_s : () → itree crisE R_s)
      (k_t : () → itree crisE R_t)
      (msk_s msk_t : emask)
      (sp_s sp_t : specmap)
      (mtid stid : nat) :
    sp_s.1 !! fid SchHdr.yield = fsp_some (SchA.yield_spec Es) →
    sp_t.1 !! fid SchHdr.yield = None →
    (msk_t _ (subevent _ (Call SchHdr.yield.1 ()↑))) →
    Ist ∗ Tid mtid stid ∗
    (Ist -∗ Tid mtid stid -∗
      wsim fl_s fl_t Ist (Es, Es) g R_s R_t RR true true
        ((SB.sandbox msk_s (SModTr.trans sp_s 𝒴)) >>= k_s)
        (k_t tt)) ⊢
    wsim fl_s fl_t Ist (Es, Es) g R_s R_t RR ps pt
      ((SB.sandbox msk_s (SModTr.trans sp_s 𝒴)) >>= k_s)
      ((SB.sandbox msk_t (SModTr.trans sp_t 𝒴)) >>= k_t).
  Proof using.
    intros Hsps Hspt Hcall. iIntros "?".
    cCoind CIH g' Hg with ps pt. iIntros "[IST [TID SIM]]".
    rewrite {2 3}yield_unfold.

    cStepsS.
    cStepsT. cStepsT. destruct _q; cycle 1.
    { cForceS (Some false). cStepsT.
      iPoseProof ("SIM" with "IST TID") as "SIM".
      iPoseProof (wsim_mono_knowledge with "SIM") as "SIM"; cycle 1.
      { iApply "SIM". }
      { iIntros (???????) "P !>". iApply Hg; ss. }
    }
    destruct b; cycle 1.
    { cForceS (Some false).
      cByCoind CIH; try et. iFrame. }

    cForceS (Some true). cStepsT. cStepS. rewrite Hsps Hspt.
    cNormS. cForceS (stid, mtid, ()); ss.
    cNormS. cForceS (()↑); s.

    cForceS.
    iFrame; iSplitL ""; eauto.
    cNormS. des_if; cStepsS; ss. cStepsT. rewrite Hcall; cStepsT.
    cCall "IST" as (ret) "IST".
    cStepsT.
    des_if; cStepS; ss. des_if; cStepsS; ss.
    cByCoind CIH; try et. iFrame. iDestruct "ASM" as "[$ ?]".
  (*SLOW*)Qed.

  Lemma wsim_yield_i_i
      (E Es Et : coPset) (g : WSim.rel)
      (k_s : () → itree crisE R_s)
      (k_t : () → itree crisE R_t)
      (msk_s msk_t : emask)
      (sp_s sp_t : specmap) :
    sp_s.1 !! fid SchHdr.yield = fsp_some (SchA.yield_spec Es) →
    sp_t.1 !! fid SchHdr.yield = fsp_some (SchA.yield_spec Et) →
    img_msk msk_t →
    (msk_t _ (subevent _ (Call SchHdr.yield.1 ()↑))) →
    Et ⊆ Es →
    E = Es ∖ Et →
    Ist ∗
    (Ist -∗
      wsim fl_s fl_t Ist (E, E) g R_s R_t RR true true
        ((SB.sandbox msk_s (SModTr.trans sp_s 𝒴)) >>= k_s)
        (k_t tt)) ⊢
    wsim fl_s fl_t Ist (E, E) g R_s R_t RR ps pt
      ((SB.sandbox msk_s (SModTr.trans sp_s 𝒴)) >>= k_s)
      ((SB.sandbox msk_t (SModTr.trans sp_t 𝒴)) >>= k_t).
  Proof using.
    intros Hsps Hspt [Ht [Hc [Ha [Har Hg]]]] Hcall HE ->. iIntros "?".
    cCoind CIH g' Hg' with ps pt. iIntros "[IST SIM]".
    rewrite {2 3}yield_unfold.

    cStepsS.
    cStepsT. cStepsT. destruct _q; cycle 1.
    { cForceS (Some false). cStepsT.
      iPoseProof ("SIM" with "IST") as "SIM".
      iPoseProof (wsim_mono_knowledge with "SIM") as "SIM"; cycle 1.
      { iApply "SIM". }
      { iIntros (???????) "P !>". iApply Hg'; ss. }
    }
    destruct b; cycle 1.
    { cForceS (Some false).
      cByCoind CIH; try et. iFrame. }

    cForceS (Some true). cStepsT. cStepS. rewrite Hsps Hspt.
    cStepsT. destruct _q as [[stid mtid] []].
    iDestruct "GRT" as "[TID [-> _]]". rewrite Hcall. cStepsT.
    cNormS. cForceS (stid, mtid, ()); ss.
    cNormS. cForceS (()↑); s.

    cForceS. iFrame; iSplit; eauto.
    cNormS. des_if; cStepsS; ss.
    cCall "IST" as (ret) "IST".
    des_if; cStepsS; ss. des_if; cStepsS; ss.
    rewrite Ht. cForceT _q. cStepsT. rewrite Ha. cForceT. iFrame. cStepsT.
    cByCoind CIH; try et. iFrame.
  (*SLOW*)Qed.

  Lemma wsim_yield_src Ep g (msk_s : emask) sp_s k_s i_t :
    wsim fl_s fl_t Ist Ep g R_s R_t RR true pt (k_s tt) i_t ⊢
    wsim fl_s fl_t Ist Ep g R_s R_t RR ps pt
      ((SB.sandbox msk_s (SModTr.trans sp_s 𝒴)) >>= k_s) i_t.
  Proof using.
    iIntros "SIM".
    rewrite /Sch.yield /Sch.choose_optbool; unseal SCH.
    rewrite unfold_iterC; cStepsS.
    cForceS None. iApply "SIM".
  Qed.
End wsim.

Section yield_namespace.
  Context `{!crisG Γ Σ α β τ _S _I, !stateGS Σ, !schGS}.

  Context (fl_s fl_t : gmap fname (option (Any.t → itree crisE Any.t))).
  Context (Ist : iProp Σ).
  Context (R_s R_t : Type).
  Context (RR : retr_type Σ R_s R_t).
  Context (ps pt : bool).

  Lemma wsim_yield_namespace_src (N : option namespace) Ep g (msk_s : emask) sp_s k_s i_t :
    wsim fl_s fl_t Ist Ep g R_s R_t RR true pt (k_s tt) i_t ⊢
    wsim fl_s fl_t Ist Ep g R_s R_t RR ps pt
      ((SB.sandbox msk_s (SModTr.trans sp_s 𝒴@{N})) >>= k_s) i_t.
  Proof using.
    iIntros "SIM". rewrite yield_namespace_unfold. cStepsS.
    cForceS None. iApply "SIM".
  Qed.

  Lemma wsim_yield_namespace_ir
      (N : namespace)
      (g : WSim.rel)
      (k_s : () → itree crisE R_s) (k_t : () → itree crisE R_t)
      (msk_s msk_t : emask) (sp_s sp_t : specmap) :
    sp_s.1 !! (fid SchHdr.yield) = None →
    sp_t.1 !! (fid SchHdr.yield) = None →
    (msk_t _ (subevent _ (Call SchHdr.yield.1 ()↑))) →
    Ist ∗
    (Ist -∗
      wsim fl_s fl_t Ist (↑N, ↑N) g R_s R_t RR true true
        ((SB.sandbox msk_s (SModTr.trans sp_s 𝒴@{Some N})) >>= k_s)
        (k_t tt)) ⊢
    wsim fl_s fl_t Ist (↑N, ↑N) g R_s R_t RR ps pt
      ((SB.sandbox msk_s (SModTr.trans sp_s 𝒴@{Some N})) >>= k_s)
      ((SB.sandbox msk_t (SModTr.trans sp_t 𝒴)) >>= k_t).
  Proof using.
    intros Hsps Hspt Hcall. iIntros "[? ?]".
    cCoind CIH g' Hg with ps pt. iIntros "[IST SIM]".
    rewrite yield_unfold {2}yield_namespace_unfold.
    
    cStepsS.
    cStepsT. cStepsT. destruct _q; cStepsT; cycle 1.
    { cForceS (Some false).
      iPoseProof ("SIM" with "IST") as "SIM".
      iPoseProof (wsim_mono_knowledge with "SIM") as "SIM"; cycle 1.
      { iApply "SIM". }
      { iIntros (???????) "P !>". iApply Hg; ss. }
    }
    destruct b; cycle 1.
    { cForceS (Some false). cByCoind CIH; try et. iFrame. }

    cForceS (Some true). cStepsT. rewrite Hspt.
    cForceS; iSplit; [done|]. cStepsS. rewrite Hsps.
    cNormS. des_if; cStepsS; ss.
    cStepsT. rewrite Hcall; cStepsT.
    cCall "IST" as (ret) "IST".
    des_if; cStepsS; ss.
    cByCoind CIH; try et. iFrame.
  (*SLOW*)Qed.

  Lemma wsim_yield_namespace_N_N
      (N_s N_t : namespace) (E : coPset)
      (g : WSim.rel)
      (k_s : () → itree crisE R_s)
      (k_t : () → itree crisE R_t)
      (msk_s msk_t : emask) (sp_s sp_t : specmap) :
    sp_s.1 !! (fid SchHdr.yield) = None →
    sp_t.1 !! (fid SchHdr.yield) = None →
    img_msk msk_t →
    (msk_t _ (subevent _ (Call SchHdr.yield.1 ()↑))) →
    ↑N_t ⊆@{coPset} ↑N_s →
    E = ↑N_s∖↑N_t →
    Ist ∗
    (Ist -∗
      wsim fl_s fl_t Ist (E, E) g R_s R_t RR true true
        ((SB.sandbox msk_s (SModTr.trans sp_s 𝒴@{Some N_s})) >>= k_s)
        (k_t tt)) ⊢
    wsim fl_s fl_t Ist (E, E) g R_s R_t RR ps pt
      ((SB.sandbox msk_s (SModTr.trans sp_s 𝒴@{Some N_s})) >>= k_s)
      ((SB.sandbox msk_t (SModTr.trans sp_t 𝒴@{Some N_t})) >>= k_t).
  Proof using.
    intros Hsps Hspt [Ht [Hc [Ha [Har Hg]]]] Hcall ? ->. iIntros "[? ?]".
    cCoind CIH g' Hg' with ps pt. iIntros "[IST SIM]".
    rewrite {2}(yield_namespace_unfold (Some N_s)) {1}(yield_namespace_unfold (Some N_t)).

    cStepsS.
    cStepsT. cStepsT. destruct _q; cStepsT; cycle 1.
    { cForceS (Some false).
      iPoseProof ("SIM" with "IST") as "SIM".
      iPoseProof (wsim_mono_knowledge with "SIM") as "SIM"; cycle 1.
      { iApply "SIM". }
      { iIntros (???????) "P !>". iApply Hg'; ss. }
    }
    destruct b; cycle 1.
    { cForceS (Some false). cByCoind CIH; try et. iFrame. }

    cForceS (Some true).
    cStepsT. cStepsT. cForceS. iSplit; first done.
    cStepsS. rewrite Hsps Hspt.
    cNormS. des_if; cStepsS; ss.
    cStepsT. rewrite Hcall; cStepsT.
    cCall "IST" as (ret) "IST".
    des_if; cStepsS; ss. rewrite Ha /=. cForcesT. iSplit; first done. cStepsT.
    cByCoind CIH; try et. iFrame.
  (*SLOW*)Qed.

  Lemma wsim_yield_namespace_i_N
      (E_s : coPset)
      (N_t : namespace)
      (mtid stid : nat)
      (g : WSim.rel)
      (k_s : () → itree crisE R_s)
      (k_t : () → itree crisE R_t)
      (msk_s msk_t : emask) (sp_s sp_t : specmap) :
    sp_s.1 !! fid SchHdr.yield = fsp_some (SchA.yield_spec E_s) →
    sp_t.1 !! (fid SchHdr.yield) = None →
    img_msk msk_t →
    (msk_t _ (subevent _ (Call SchHdr.yield.1 ()↑))) →
    ↑N_t ⊆ E_s →
    Ist ∗
    Tid mtid stid ∗
    (Ist -∗
      Tid mtid stid -∗
      wsim fl_s fl_t Ist (E_s∖↑N_t, E_s∖↑N_t) g R_s R_t RR true true
        ((SB.sandbox msk_s (SModTr.trans sp_s 𝒴)) >>= k_s)
        (k_t tt)) ⊢
    wsim fl_s fl_t Ist (E_s∖↑N_t, E_s∖↑N_t) g R_s R_t RR ps pt
      ((SB.sandbox msk_s (SModTr.trans sp_s 𝒴)) >>= k_s)
      ((SB.sandbox msk_t (SModTr.trans sp_t 𝒴@{Some N_t})) >>= k_t).
  Proof using.
    intros Hsps Hspt [Ht [Hc [Ha [Har Hg]]]] Hcall ?. iIntros "?".
    cCoind CIH g' Hg' with ps pt. iIntros "[IST [TID SIM]]".
    rewrite {2}(yield_unfold) {1}(yield_namespace_unfold (Some N_t)).

    cStepsS.
    cStepsT. cStepsT. destruct _q; cStepsT; cycle 1.
    { cForceS (Some false).
      iPoseProof ("SIM" with "IST TID") as "SIM".
      iPoseProof (wsim_mono_knowledge with "SIM") as "SIM"; cycle 1.
      { iApply "SIM". }
      { iIntros (???????) "P !>". iApply Hg'; ss. }
    }
    destruct b; cycle 1.
    { cForceS (Some false). cByCoind CIH; try et. iFrame. }

    cForceS (Some true). cStepS. simpl_sp. cStepsS.
    cStepsT. cStepsT. simpl_sp. cStepsT. rewrite Hcall. cStepsT.
    cForceS (_, _, tt). cForcesS.
    iFrame. iSplit; first done.
    cNormS. des_if; cStepsS; ss.
    cCall "IST" as (ret) "IST".
    des_if; cStepsS; ss. rewrite Ha /=. des_if; cStepsS; ss.
    cForcesT. iSplit; first done. cStepsT.
    cByCoind CIH; try et. iFrame. iDestruct "ASM" as "[$ _]".
  (*SLOW*)Qed.
End yield_namespace.

Tactic Notation "solve_msk" :=
  first
  [ assumption
  | solve [clear; cbn; first [done | repeat case_bool_decide; set_solver]]
  | try (clear; by ss); ss; cbn;
    match goal with | |- context[bool_decide ?P] => try by msk_solve P end
  ].

Ltac sYieldRR IST :=
  cNormS; cNormT; iApply (wsim_yield_tgt_rr); [ss|ss|solve_msk|iFrame IST];
  last (iIntros IST; cStepsT).

Tactic Notation "sYieldIR" uconstr(H1) uconstr(H2) :=
  let H2' := eval compute in (H1 ++ " " ++ H2)%string in
  cNormS; cNormT; iApply (wsim_yield_tgt_ir);
    [simpl_map; simpl_sp; ss|simpl_map; simpl_sp; ss|solve_msk|iFrame H2'];
  last (iIntros H2'; cStepsT).

Tactic Notation "sYieldII" uconstr(IST) :=
  cNormS; cNormT; iApply (wsim_yield_i_i);
  [simpl_sp; simpl_map; ss|simpl_sp; simpl_map; ss
  |solve_msk|solve_msk|(solve_ndisj || set_solver)|(solve_ndisj || set_solver)
  |iFrame IST]; iIntros IST; cStepsT.

Section SREL.
  Context `{!crisG Γ Σ α β τ _S _I, !stateGS Σ, !schGS}.
  Import SchA.

  (* srel (progress_flag) (oneshot_flag) (i_rew) (i_org) *)
  Variant srel_def 
    (coself : forall R, bool -> itree crisE R -> itree crisE R -> Prop)
    {R}
    (self : bool -> itree crisE R -> itree crisE R -> Prop)
    : bool -> itree crisE R -> itree crisE R -> Prop :=
    | srel_def_ret p r
        (SRELEQ: True)
      : srel_def coself self p (Ret r) (Ret r)

    | srel_def_tau p itr_src itr_tgt
        (SRELTAU: True)
        (SELF: coself R false itr_src itr_tgt)
      : srel_def coself self p (tau;; itr_src) (tau;; itr_tgt)

    | srel_def_tau_r p itr_src itr_tgt
        (SRELTAUR: True)
        (SELF: self true itr_src itr_tgt)
      : srel_def coself self p itr_src (tau;; itr_tgt)

    | srel_def_choose_diff p (X: Type) ktr_src ktr_tgt
        (SRELCHOOSEDIFF: True)
        (SELF: forall x_src: X, exists x_tgt: X, coself R false (ktr_src x_src) (ktr_tgt x_tgt))
      : srel_def coself self p (x <- trigger (Choose X);; ktr_src x) (x <- trigger (Choose X);; ktr_tgt x)

    | srel_def_choose_r p X itr_src ktr_tgt
        (SRELCHOOSER: True)
        (SELF: exists x, self true (itr_src) (ktr_tgt x))
      : srel_def coself self p itr_src (x <- trigger (Choose X);; ktr_tgt x)

    | srel_def_choose p X ktr_src ktr_tgt
        (SRELCHOOSE: True)
        (SELF: forall x, coself R false (ktr_src x) (ktr_tgt x))
      : srel_def coself self p (x <- trigger (Choose X);; ktr_src x) (x <- trigger (Choose X);; ktr_tgt x)

    | srel_def_take p X ktr_src ktr_tgt
        (SRELTAKE: True)
        (SELF: forall x, coself R false (ktr_src x) (ktr_tgt x))
      : srel_def coself self p (x <- trigger (Take X);; ktr_src x) (x <- trigger (Take X);; ktr_tgt x)

    | srel_def_io p I O f i ktr_src ktr_tgt
        (SRELIO: True)
        (SELF: forall x, coself R false (ktr_src x) (ktr_tgt x))
      : srel_def coself self p (x <- trigger (@IO I O f i);; ktr_src x) (x <- trigger (@IO I O f i);; ktr_tgt x)

    | srel_def_assume p P ktr_src ktr_tgt
        (SRELASSUME: True)
        (SELF: coself R false (ktr_src tt) (ktr_tgt tt))
      : srel_def coself self p (x <- trigger (Assume P);; ktr_src x) (x <- trigger (Assume P);; ktr_tgt x)

    | srel_def_assumeres p r ktr_src ktr_tgt
        (SRELASSUMERES: True)
        (SELF: coself R false (ktr_src tt) (ktr_tgt tt))
      : srel_def coself self p (x <- trigger (AssumeRes r);; ktr_src x) (x <- trigger (AssumeRes r);; ktr_tgt x)

    | srel_def_guarantee p P ktr_src ktr_tgt
        (SRELGUARANTEE: True)
        (SELF: coself R false (ktr_src tt) (ktr_tgt tt))
      : srel_def coself self p (x <- trigger (Guarantee P);; ktr_src x) (x <- trigger (Guarantee P);; ktr_tgt x)

    | srel_def_call p fn args ktr_src ktr_tgt
        (SRELGUARANTEE: True)
        (SELF: forall x, coself R false (ktr_src x) (ktr_tgt x))
      : srel_def coself self p (x <- trigger (Call fn args);; ktr_src x) (x <- trigger (Call fn args);; ktr_tgt x)

    | srel_def_spawn p fn args ktr_src ktr_tgt
        (SRELSPAWN: True)
        (SELF: forall x, coself R false (ktr_src x) (ktr_tgt x))
      : srel_def coself self p (x <- trigger (Spawn fn args);; ktr_src x) (x <- trigger (Spawn fn args);; ktr_tgt x)

    | srel_def_yield p n ktr_src ktr_tgt
        (SRELYIELD: True)
        (SELF: forall x, coself R false (ktr_src x) (ktr_tgt x))
      : srel_def coself self p (x <- trigger (Yield n);; ktr_src x) (x <- trigger (Yield n);; ktr_tgt x)

    | srel_def_get_tid p ktr_src ktr_tgt
        (SRELGETTID: True)
        (SELF: forall x, coself R false (ktr_src x) (ktr_tgt x))
      : srel_def coself self p (x <- trigger GetTid;; ktr_src x) (x <- trigger GetTid;; ktr_tgt x)

    | srel_def_sput p k v ktr_src ktr_tgt
        (SRELSPUT: True)
        (SELF: forall x, coself R false (ktr_src x) (ktr_tgt x))
      : srel_def coself self p (x <- trigger (SPut k v);; ktr_src x) (x <- trigger (SPut k v);; ktr_tgt x)

    | srel_def_sget p k ktr_src ktr_tgt
        (SRELSGET: True)
        (SELF: forall x, coself R false (ktr_src x) (ktr_tgt x))
      : srel_def coself self p (x <- trigger (SGet k);; ktr_src x) (x <- trigger (SGet k);; ktr_tgt x)
  .

  Global Arguments srel_def coself {R} self.

  Inductive _srel srel R p itr_src itr_tgt : Prop :=
  | srel_intro (SELF: @srel_def srel R (@_srel srel R) p itr_src itr_tgt).

  Definition srel := paco4 _srel bot4.

  Lemma _srel_tarski srel R rel
    (FIX: forall p itr_src itr_tgt (IN: @srel_def srel R rel p itr_src itr_tgt), rel p itr_src itr_tgt) :
    @_srel srel R <3= rel.
  Proof using.
    fix self 4. i.
    destruct PR. apply FIX. i. destruct SELF; des; econs; eauto.
  Qed.

  Lemma srel_def_mon r r' R s s' p itr_src itr_tgt
    (REL: @srel_def r R s p itr_src itr_tgt)
    (LEr: r <4= r')
    (LEs: s <3= s') :
    @srel_def r' R s' p itr_src itr_tgt.
  Proof using.
    ii. destruct REL; econs; eauto.
    { i. specialize (SELF x_src). des. eauto. }
    { des. eauto. }
  Qed.

  Lemma _srel_mon : monotone4 _srel.
  Proof using.
    ii. eapply _srel_tarski, IN.
    i. econs. eauto using srel_def_mon.
  Qed.

  Hint Resolve _srel_mon : paco.

  (** useful lemmas **)

  Lemma _srel_mon_auto r r' R p i_src i_tgt
    (REL: _srel r R p i_src i_tgt)
    (LEr: r <4= r') :
    _srel r' R p i_src i_tgt.
  Proof using. eapply _srel_mon; eauto. Qed.

  Lemma _srel_flag_mon r R (p p': bool) i_src i_tgt
    (SIM: _srel r R p i_src i_tgt)
    (LES: p -> p') :
    _srel r R p' i_src i_tgt.
  Proof using.
    move SIM before r. revert_until SIM.
    pattern p, i_src, i_tgt.
    eapply _srel_tarski, SIM. i. econs.
    destruct IN; try by des; econs; eauto.
  Qed.

  Hint Constructors srel_def _srel : core.
  Hint Unfold srel : core.
  Hint Resolve _srel_mon : paco.
  Hint Resolve _srel_mon_auto : paco.
  Hint Resolve cpn4_wcompat : paco.

  (** srel closure **)

  Variant srel_flagC
    (r : ∀ R, bool -> itree crisE R -> itree crisE R -> Prop)
    R p1 i_src i_tgt : Prop :=
  | srel_flagC_intro p0
      (SIM: r R p0 i_src i_tgt)
      (FLAG: p0 = true -> p1 = true).

  Lemma srel_flagC_mon r1 r2 (LE : r1 <4= r2) :
    srel_flagC r1 <4= srel_flagC r2.
  Proof using.
    ii. destruct PR; econs; eauto.
  Qed.

  Hint Resolve srel_flagC_mon: core.

  Lemma srel_flagC_spec : srel_flagC <5= gupaco4 _srel (cpn4 _srel).
  Proof using.
    eapply wrespect4_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR.
    eauto using _srel_flag_mon, _srel_mon_auto, rclo4.
  Qed.

  Variant srel_eqC
    (r : ∀ R, bool -> itree crisE R -> itree crisE R -> Prop)
    R (p: bool) : itree crisE R -> itree crisE R -> Prop :=
  | srel_eqC_intro itr
    : srel_eqC r R p itr itr.

  Lemma srel_eqC_mon r1 r2 (LEr: r1 <4= r2) : srel_eqC r1 <4= srel_eqC r2.
  Proof using. ii. destruct PR; econs; eauto. Qed.

  Lemma srel_eqC_compatible : compatible4 _srel srel_eqC.
  Proof using.
    econs; eauto using srel_eqC_mon. i.
    destruct PR. ides itr.
    - econs; econs; eauto.
    - econs; econs; eauto. econs.
    - rewrite <-bind_trigger. depdes e; ss.
      { depdes a; ss; econs; econs; eauto; econs. }
      depdes s; ss.
      { depdes c; ss; econs; econs; eauto; econs. }
      depdes s; ss.
      { depdes p; ss; econs; econs; eauto; econs. }
      { depdes c; ss; econs.
        - eapply srel_def_choose; eauto; i; econs.
        - econs; eauto; i; econs.
        - econs; eauto; i; econs.
      }
  Qed.

  Lemma srel_eqC_spec: srel_eqC <5= gupaco4 _srel (cpn4 _srel).
  Proof using.
    intros. gclo. econs; eauto using srel_eqC_compatible.
    eapply srel_eqC_mon, PR; eauto with paco.
  Qed.

  Variant srel_bindC
      (r : ∀ R, bool -> itree crisE R -> itree crisE R -> Prop)
    : ∀ R, bool -> itree crisE R -> itree crisE R -> Prop :=
  | srel_bindC_intro
      p Q i_src i_tgt R k_src k_tgt
      (SIM : r Q p i_src i_tgt)
      (SIMK : ∀ vret, r R false (k_src vret) (k_tgt vret)) :
    srel_bindC r R p (i_src >>= k_src) (i_tgt >>= k_tgt).

  Lemma srel_bindC_mon r1 r2 (LEr : r1 <4= r2) : srel_bindC r1 <4= srel_bindC r2.
  Proof using. ii. destruct PR; econs; et. Qed.

  Lemma srel_bindC_wrespectful : wrespectful4 _srel srel_bindC.
  Proof using.
    econs; eauto using srel_bindC_mon; i.
    destruct PR. apply GF in SIM.
    move SIM before GF. revert_until SIM.
    pattern p, i_src, i_tgt.
    eapply _srel_tarski, SIM. econs. i.
    depdes IN; grind; try (by econs; repeat rewrite <-bind_bind; eauto 7 using rclo4, srel_bindC).
    - exploit SIMK; eauto. i. eapply GF in x0. inv x0. eauto.
      eapply _srel_flag_mon with (p:=false); eauto.
      eapply _srel_mon_auto; eauto using rclo4.
    - econs; eauto. i. specialize (SELF x_src). des. esplits; eauto 7 using rclo4, srel_bindC.
    - econs; eauto. des. esplits; eauto.
  Unshelve. all: eauto.
  Qed.

  Lemma srel_bindC_spec : srel_bindC <5= gupaco4 _srel (cpn4 _srel).
  Proof using. intros. eapply wrespect4_uclo; eauto with paco. apply srel_bindC_wrespectful. Qed.

  Lemma srel_upaco_bot {R} p i_src i_tgt
      (SIM : upaco4 _srel bot4 R p i_src i_tgt) :
    srel _ p i_src i_tgt.
  Proof using. pclearbot. exact SIM. Qed.

  Lemma srel_cont {X R} (k_src k_rew k_org : X → itree crisE R)
      (EQ : k_rew = k_src)
      (SIM : ∀ x, upaco4 _srel bot4 R false (k_rew x) (k_org x)) x :
    srel _ false (k_src x) (k_org x).
  Proof using. subst k_src. eapply srel_upaco_bot, SIM. Qed.

  Lemma srel_cont_at {X R} (k_src k_rew k_org : X → itree crisE R) x
      (EQ : k_rew = k_src)
      (SIM : upaco4 _srel bot4 R false (k_rew x) (k_org x)) :
    srel _ false (k_src x) (k_org x).
  Proof using. subst k_src. eapply srel_upaco_bot, SIM. Qed.

  Lemma srel_cont_left {X R} (k_src k_rew : X → itree crisE R)
      x itr_org (EQ : k_rew = k_src)
      (SIM : upaco4 _srel bot4 R false (k_rew x) itr_org) :
    srel _ false (k_src x) itr_org.
  Proof using. subst k_src. eapply srel_upaco_bot, SIM. Qed.

  Lemma srel_bind_cont {X R} (itr : itree crisE X)
      (k_src k_rew k_org : X → itree crisE R)
      (EQ : k_rew = k_src)
      (SIM : ∀ x, upaco4 _srel bot4 R false (k_rew x) (k_org x)) :
    srel _ false (itr >>= k_src) (itr >>= k_org).
  Proof using.
    ginit. guclo srel_bindC_spec. econs.
    - guclo srel_eqC_spec. econs.
    - intro x. gfinal. right. eapply srel_cont; eauto.
  Qed.

  Lemma srel_source_ind {R} (itr_src : itree crisE R)
      (P : bool → itree crisE R → Prop)
      (STEP : ∀ p itr_rew itr_org,
        @srel_def (upaco4 _srel bot4) R
          (fun p itr_rew itr_org => itr_rew = itr_src → P p itr_org)
          p itr_rew itr_org →
        itr_rew = itr_src → P p itr_org)
      itr_org (SIM : srel R false itr_src itr_org) :
    P false itr_org.
  Proof using.
    punfold SIM.
    pose proof (@_srel_tarski (upaco4 _srel bot4) R
      (fun p itr_rew itr_org => itr_rew = itr_src → P p itr_org)
      STEP false itr_src itr_org SIM) as FOLD.
    exact (FOLD eq_refl).
  Qed.

  (* msim closure *)
  
  Variable contextual: contextuality.
  Variable fl_src : gmap fname (option (Any.t → itree crisE Any.t)).
  Variable fl_tgt : gmap fname (option (Any.t → itree crisE Any.t)).
  Variable Ist : iProp Σ.

  Definition msim_srelD {Rs Rt} (q : msim_type Σ Rs Rt) :
      msim_type Σ Rs Rt :=
    fun ps pt itr_rew itr_tgt fmr =>
      ∀ itr_org, srel _ false itr_rew itr_org →
        q ps pt itr_org itr_tgt fmr.

  Variant msim_srelC (r: forall Rs Rt (RR: retr_type Σ Rs Rt), msim_type Σ Rs Rt) :
    forall Rs Rt (RR: retr_type Σ Rs Rt), msim_type Σ Rs Rt :=
    | msim_srelC_intro
        ps pt Rs Rt RR itr_rew itr_org itr_tgt fmr
        (SREL: @srel Rs false itr_rew itr_org)
        (SIM: r Rs Rt RR ps pt itr_rew itr_tgt fmr)
      : msim_srelC r Rs Rt RR ps pt itr_org itr_tgt fmr.

  Lemma msim_roll q Rs Rt (RR : retr_type Σ Rs Rt)
      ps pt itr_src itr_tgt fmr
      (STEP : _msim' contextual fl_src fl_tgt Ist q RR
        (_msim contextual fl_src fl_tgt Ist q Rs Rt RR)
        ps pt itr_src itr_tgt fmr) :
    _msim contextual fl_src fl_tgt Ist q Rs Rt RR
      ps pt itr_src itr_tgt fmr.
  Proof using.
    econs. intros NODFS NODFT. eapply hsupd_incl. exact STEP.
  Qed.

  Lemma msim_srelC_mon r1 r2 (LEr: r1 <8= r2) : msim_srelC r1 <8= msim_srelC r2.
  Proof using. ii; destruct PR; econs; eauto. Qed.

  Lemma msim_srelC_step r Rs Rt (RR : retr_type Σ Rs Rt) :
    _msim' contextual fl_src fl_tgt Ist r RR
      (msim_srelD
        (_msim contextual fl_src fl_tgt Ist (msim_srelC r) Rs Rt RR)) <5=
    msim_srelD
      (_msim' contextual fl_src fl_tgt Ist (msim_srelC r) RR
        (_msim contextual fl_src fl_tgt Ist (msim_srelC r) Rs Rt RR)).
  Proof using.
    intros ps pt itr_rew itr_tgt fmr STEP itr_org SREL.
    dependent destruction STEP.
    - (* ret *)
      eapply (srel_source_ind (Ret v_src)
        (fun p itr_org =>
          _msim' contextual fl_src fl_tgt Ist (msim_srelC r) RR
            (_msim contextual fl_src fl_tgt Ist
              (msim_srelC r) Rs Rt RR)
            (p || ps) pt itr_org (Ret v_tgt) fmr)); [|exact SREL].
      intros p itr_rew0 itr_org0 REL EQ.
      dependent destruction REL; rewrite ?bind_trigger in EQ; ss.
      + dependent destruction EQ.
        eapply msim_ret; [exact MSIM_RET|exact RET].
      + eapply msim_tau_src; [exact SRELTAUR|].
        eapply msim_roll. eapply SELF. exact EQ.
      + destruct SELF as [x SELF].
        eapply msim_choose_src with (x := x); [exact SRELCHOOSER|].
        eapply msim_roll. eapply SELF. exact EQ.
    - (* call *)
      eapply (srel_source_ind (trigger (Call fn varg) >>= k_src)
        (fun p itr_org =>
          _msim' contextual fl_src fl_tgt Ist (msim_srelC r) RR
            (_msim contextual fl_src fl_tgt Ist
              (msim_srelC r) Rs Rt RR)
            (p || ps) pt itr_org
            (trigger (Call fn varg) >>= k_tgt) fmr)); [|exact SREL].
      intros p itr_rew0 itr_org0 REL EQ.
      dependent destruction REL; rewrite ?bind_trigger in EQ; ss.
      + eapply msim_tau_src; [exact SRELTAUR|].
        eapply msim_roll. eapply SELF. rewrite bind_trigger. exact EQ.
      + destruct SELF as [x SELF].
        eapply msim_choose_src with (x := x); [exact SRELCHOOSER|].
        eapply msim_roll. eapply SELF. rewrite bind_trigger. exact EQ.
      + dependent destruction EQ.
        eapply msim_call; [exact MSIM_CALL|exact INV|].
        intros vret fmr0 VALID INV0.
        eapply K; [exact VALID|exact INV0|].
        eapply srel_cont; eauto.
    - (* io *)
      eapply (srel_source_ind (trigger (IO fn varg) >>= k_src)
        (fun p itr_org =>
          _msim' contextual fl_src fl_tgt Ist (msim_srelC r) RR
            (_msim contextual fl_src fl_tgt Ist
              (msim_srelC r) Rs Rt RR)
            (p || ps) pt itr_org
            (trigger (IO fn varg) >>= k_tgt) fmr)); [|exact SREL].
      intros p itr_rew0 itr_org0 REL EQ.
      dependent destruction REL; rewrite ?bind_trigger in EQ; ss.
      + eapply msim_tau_src; [exact SRELTAUR|].
        eapply msim_roll. eapply SELF. rewrite bind_trigger. exact EQ.
      + destruct SELF as [x SELF].
        eapply msim_choose_src with (x := x); [exact SRELCHOOSER|].
        eapply msim_roll. eapply SELF. rewrite bind_trigger. exact EQ.
      + dependent destruction EQ.
        eapply msim_io; [exact MSIM_IO|].
        intro vret. eapply K. eapply srel_cont; eauto.
    - (* inline_src *)
      eapply (srel_source_ind (trigger (Call fn varg) >>= k_src)
        (fun p itr_org =>
          _msim' contextual fl_src fl_tgt Ist (msim_srelC r) RR
            (_msim contextual fl_src fl_tgt Ist
              (msim_srelC r) Rs Rt RR)
            (p || ps) pt itr_org i_tgt fmr)); [|exact SREL].
      intros p itr_rew0 itr_org0 REL EQ.
      dependent destruction REL; rewrite ?bind_trigger in EQ; ss.
      + eapply msim_tau_src; [exact SRELTAUR|].
        eapply msim_roll. eapply SELF. rewrite bind_trigger. exact EQ.
      + destruct SELF as [x SELF].
        eapply msim_choose_src with (x := x); [exact SRELCHOOSER|].
        eapply msim_roll. eapply SELF. rewrite bind_trigger. exact EQ.
      + dependent destruction EQ.
        eapply msim_inline_src;
          [exact MSIM_INLINE_SRC|exact FUN|].
        eapply K. eapply srel_bind_cont; eauto.
    - (* inline_tgt *)
      eapply msim_inline_tgt; [exact MSIM_INLINE_TGT|exact FUN|].
      eapply K. exact SREL.
    - (* tau_src *)
      eapply (srel_source_ind (tau;; i_src)
        (fun p itr_org =>
          _msim' contextual fl_src fl_tgt Ist (msim_srelC r) RR
            (_msim contextual fl_src fl_tgt Ist
              (msim_srelC r) Rs Rt RR)
            (p || ps) pt itr_org i_tgt fmr)); [|exact SREL].
      intros p itr_rew0 itr_org0 REL EQ.
      dependent destruction REL; rewrite ?bind_trigger in EQ; ss.
      + dependent destruction EQ.
        eapply msim_tau_src; [exact MSIM_TAU_SRC|].
        eapply K, srel_upaco_bot. exact SELF.
      + eapply msim_tau_src; [exact SRELTAUR|].
        eapply msim_roll. eapply SELF. exact EQ.
      + destruct SELF as [x SELF].
        eapply msim_choose_src with (x := x); [exact SRELCHOOSER|].
        eapply msim_roll. eapply SELF. exact EQ.
    - (* tau_tgt *)
      eapply msim_tau_tgt; [exact MSIM_TAU_TGT|].
      eapply K. exact SREL.
    - (* choose_src *)
      eapply (srel_source_ind (trigger (Choose X) >>= k_src)
        (fun p itr_org =>
          _msim' contextual fl_src fl_tgt Ist (msim_srelC r) RR
            (_msim contextual fl_src fl_tgt Ist
              (msim_srelC r) Rs Rt RR)
            (p || ps) pt itr_org i_tgt fmr)); [|exact SREL].
      intros p itr_rew0 itr_org0 REL EQ.
      dependent destruction REL; rewrite ?bind_trigger in EQ; ss.
      + eapply msim_tau_src; [exact SRELTAUR|].
        eapply msim_roll. eapply SELF. rewrite bind_trigger. exact EQ.
      + dependent destruction EQ.
        destruct (SELF x0) as [x_tgt SIM].
        eapply msim_choose_src with (x := x_tgt);
          [exact MSIM_CHOOSE_SRC|].
        eapply K. eapply srel_cont_left; eauto.
      + destruct SELF as [x_tgt SELF].
        eapply msim_choose_src with (x := x_tgt); [exact SRELCHOOSER|].
        eapply msim_roll. eapply SELF. rewrite bind_trigger. exact EQ.
      + dependent destruction EQ.
        eapply msim_choose_src with (x := x0); [exact MSIM_CHOOSE_SRC|].
        eapply K. eapply srel_cont; eauto.
    - (* choose_tgt *)
      eapply msim_choose_tgt; [exact MSIM_CHOOSE_TGT|].
      intro x. eapply K. exact SREL.
    - (* take_src *)
      eapply (srel_source_ind (trigger (Take X) >>= k_src)
        (fun p itr_org =>
          _msim' contextual fl_src fl_tgt Ist (msim_srelC r) RR
            (_msim contextual fl_src fl_tgt Ist
              (msim_srelC r) Rs Rt RR)
            (p || ps) pt itr_org i_tgt fmr)); [|exact SREL].
      intros p itr_rew0 itr_org0 REL EQ.
      dependent destruction REL; rewrite ?bind_trigger in EQ; ss.
      + eapply msim_tau_src; [exact SRELTAUR|].
        eapply msim_roll. eapply SELF. rewrite bind_trigger. exact EQ.
      + destruct SELF as [x SELF].
        eapply msim_choose_src with (x := x); [exact SRELCHOOSER|].
        eapply msim_roll. eapply SELF. rewrite bind_trigger. exact EQ.
      + dependent destruction EQ.
        eapply msim_take_src; [exact MSIM_TAKE_SRC|].
        intro v. eapply K. eapply srel_cont; eauto.
    - (* take_tgt *)
      eapply msim_take_tgt; [exact MSIM_TAKE_TGT|].
      eapply K. exact SREL.
    - (* sput_src *)
      eapply (srel_source_ind (trigger (SPut k v') >>= k_src)
        (fun p itr_org =>
          _msim' contextual fl_src fl_tgt Ist (msim_srelC r) RR
            (_msim contextual fl_src fl_tgt Ist
              (msim_srelC r) Rs Rt RR)
            (p || ps) pt itr_org i_tgt fmr)); [|exact SREL].
      intros p itr_rew0 itr_org0 REL EQ.
      dependent destruction REL; rewrite ?bind_trigger in EQ; ss.
      + eapply msim_tau_src; [exact SRELTAUR|].
        eapply msim_roll. eapply SELF. rewrite bind_trigger. exact EQ.
      + destruct SELF as [x SELF].
        eapply msim_choose_src with (x := x); [exact SRELCHOOSER|].
        eapply msim_roll. eapply SELF. rewrite bind_trigger. exact EQ.
      + dependent destruction EQ.
        eapply msim_sput_src; [exact MSIM_SPUT_SRC|exact CUR|].
        intros fmr0 VALID NEW. eapply K; [exact VALID|exact NEW|].
        eapply srel_cont; eauto.
    - (* sput_tgt *)
      eapply msim_sput_tgt; [exact MSIM_SPUT_TGT|exact CUR|].
      intros fmr0 VALID NEW.
      eapply K; [exact VALID|exact NEW|exact SREL].
    - (* sget_src *)
      eapply (srel_source_ind (trigger (SGet k) >>= k_src)
        (fun p itr_org =>
          _msim' contextual fl_src fl_tgt Ist (msim_srelC r) RR
            (_msim contextual fl_src fl_tgt Ist
              (msim_srelC r) Rs Rt RR)
            (p || ps) pt itr_org i_tgt fmr)); [|exact SREL].
      intros p itr_rew0 itr_org0 REL EQ.
      dependent destruction REL; rewrite ?bind_trigger in EQ; ss.
      + eapply msim_tau_src; [exact SRELTAUR|].
        eapply msim_roll. eapply SELF. rewrite bind_trigger. exact EQ.
      + destruct SELF as [x SELF].
        eapply msim_choose_src with (x := x); [exact SRELCHOOSER|].
        eapply msim_roll. eapply SELF. rewrite bind_trigger. exact EQ.
      + dependent destruction EQ.
        eapply msim_sget_src; [exact MSIM_SGET_SRC|exact CUR|].
        intros fmr0 VALID NEW. eapply K; [exact VALID|exact NEW|].
        eapply srel_cont; eauto.
    - (* sget_tgt *)
      eapply msim_sget_tgt; [exact MSIM_SGET_TGT|exact CUR|].
      intros fmr0 VALID NEW.
      eapply K; [exact VALID|exact NEW|exact SREL].
    - (* sput_src_uninit *)
      eapply (srel_source_ind (trigger (SPut k v') >>= k_src)
        (fun p itr_org =>
          _msim' contextual fl_src fl_tgt Ist (msim_srelC r) RR
            (_msim contextual fl_src fl_tgt Ist
              (msim_srelC r) Rs Rt RR)
            (p || ps) pt itr_org i_tgt fmr)); [|exact SREL].
      intros p itr_rew0 itr_org0 REL EQ.
      dependent destruction REL; rewrite ?bind_trigger in EQ; ss.
      + eapply msim_tau_src; [exact SRELTAUR|].
        eapply msim_roll. eapply SELF. rewrite bind_trigger. exact EQ.
      + destruct SELF as [x SELF].
        eapply msim_choose_src with (x := x); [exact SRELCHOOSER|].
        eapply msim_roll. eapply SELF. rewrite bind_trigger. exact EQ.
      + dependent destruction EQ.
        eapply msim_sput_src_uninit;
          [exact MSIM_SPUT_SRC_UNINIT|exact CUR|].
        intros fmr0 VALID NEW. eapply K; [exact VALID|exact NEW|].
        eapply srel_cont; eauto.
    - (* sput_tgt_uninit *)
      eapply msim_sput_tgt_uninit;
        [exact MSIM_SPUT_TGT_UNINIT|exact CUR|].
      intros fmr0 VALID NEW.
      eapply K; [exact VALID|exact NEW|exact SREL].
    - (* sget_src_uninit *)
      eapply (srel_source_ind (trigger (SGet k) >>= k_src)
        (fun p itr_org =>
          _msim' contextual fl_src fl_tgt Ist (msim_srelC r) RR
            (_msim contextual fl_src fl_tgt Ist
              (msim_srelC r) Rs Rt RR)
            (p || ps) pt itr_org i_tgt fmr)); [|exact SREL].
      intros p itr_rew0 itr_org0 REL EQ.
      dependent destruction REL; rewrite ?bind_trigger in EQ; ss.
      + eapply msim_tau_src; [exact SRELTAUR|].
        eapply msim_roll. eapply SELF. rewrite bind_trigger. exact EQ.
      + destruct SELF as [x SELF].
        eapply msim_choose_src with (x := x); [exact SRELCHOOSER|].
        eapply msim_roll. eapply SELF. rewrite bind_trigger. exact EQ.
      + dependent destruction EQ.
        eapply msim_sget_src_uninit;
          [exact MSIM_SGET_SRC_UNINIT|exact CUR|].
        intros fmr0 VALID NEW. eapply K; [exact VALID|exact NEW|].
        eapply srel_cont; eauto.
    - (* sget_tgt_uninit *)
      eapply msim_sget_tgt_uninit;
        [exact MSIM_SGET_TGT_UNINIT|exact CUR|].
      intros fmr0 VALID NEW.
      eapply K; [exact VALID|exact NEW|exact SREL].
    - (* assume_src *)
      eapply (srel_source_ind (trigger (Assume iP) >>= k_src)
        (fun p itr_org =>
          _msim' contextual fl_src fl_tgt Ist (msim_srelC r) RR
            (_msim contextual fl_src fl_tgt Ist
              (msim_srelC r) Rs Rt RR)
            (p || ps) pt itr_org i_tgt fmr)); [|exact SREL].
      intros p itr_rew0 itr_org0 REL EQ.
      dependent destruction REL; rewrite ?bind_trigger in EQ; ss.
      + eapply msim_tau_src; [exact SRELTAUR|].
        eapply msim_roll. eapply SELF. rewrite bind_trigger. exact EQ.
      + destruct SELF as [x SELF].
        eapply msim_choose_src with (x := x); [exact SRELCHOOSER|].
        eapply msim_roll. eapply SELF. rewrite bind_trigger. exact EQ.
      + dependent destruction EQ.
        eapply msim_assume_src; [exact MSIM_ASSUME_SRC|exact CUR|].
        intros fmr0 VALID NEW. eapply K; [exact VALID|exact NEW|].
        eapply srel_cont_at; eauto.
    - (* assume_tgt *)
      eapply msim_assume_tgt; [exact MSIM_ASSUME_TGT|exact CUR|].
      intros fmr0 VALID NEW.
      eapply K; [exact VALID|exact NEW|exact SREL].
    - (* assume_res_src *)
      eapply (srel_source_ind (trigger (AssumeRes r0) >>= k_src)
        (fun p itr_org =>
          _msim' contextual fl_src fl_tgt Ist (msim_srelC r) RR
            (_msim contextual fl_src fl_tgt Ist
              (msim_srelC r) Rs Rt RR)
            (p || ps) pt itr_org i_tgt fmr)); [|exact SREL].
      intros p itr_rew0 itr_org0 REL EQ.
      dependent destruction REL; rewrite ?bind_trigger in EQ; ss.
      + eapply msim_tau_src; [exact SRELTAUR|].
        eapply msim_roll. eapply SELF. rewrite bind_trigger. exact EQ.
      + destruct SELF as [x SELF].
        eapply msim_choose_src with (x := x); [exact SRELCHOOSER|].
        eapply msim_roll. eapply SELF. rewrite bind_trigger. exact EQ.
      + dependent destruction EQ.
        eapply msim_assume_res_src;
          [exact MSIM_ASSUME_RES_SRC|exact CUR|].
        intros fmr0 VALID NEW. eapply K; [exact VALID|exact NEW|].
        eapply srel_cont_at; eauto.
    - (* assume_res_tgt *)
      eapply msim_assume_res_tgt;
        [exact MSIM_ASSUME_PRECISE_TGT|exact CUR|].
      intros fmr0 VALID NEW. eapply K; [exact VALID|exact NEW|exact SREL].
    - (* guarantee_src *)
      eapply (srel_source_ind (trigger (Guarantee iP) >>= k_src)
        (fun p itr_org =>
          _msim' contextual fl_src fl_tgt Ist (msim_srelC r) RR
            (_msim contextual fl_src fl_tgt Ist
              (msim_srelC r) Rs Rt RR)
            (p || ps) pt itr_org i_tgt fmr)); [|exact SREL].
      intros p itr_rew0 itr_org0 REL EQ.
      dependent destruction REL; rewrite ?bind_trigger in EQ; ss.
      + eapply msim_tau_src; [exact SRELTAUR|].
        eapply msim_roll. eapply SELF. rewrite bind_trigger. exact EQ.
      + destruct SELF as [x SELF].
        eapply msim_choose_src with (x := x); [exact SRELCHOOSER|].
        eapply msim_roll. eapply SELF. rewrite bind_trigger. exact EQ.
      + dependent destruction EQ.
        eapply msim_guarantee_src;
          [exact MSIM_GUARANTEE_SRC|exact CUR|].
        intros fmr0 VALID NEW. eapply K; [exact VALID|exact NEW|].
        eapply srel_cont_at; eauto.
    - (* guarantee_tgt *)
      eapply msim_guarantee_tgt; [exact MSIM_GUARANTEE_TGT|exact CUR|].
      intros fmr0 VALID NEW.
      eapply K; [exact VALID|exact NEW|exact SREL].
    - (* spawn *)
      eapply (srel_source_ind (trigger (Spawn fn arg) >>= k_src)
        (fun p itr_org =>
          _msim' contextual fl_src fl_tgt Ist (msim_srelC r) RR
            (_msim contextual fl_src fl_tgt Ist
              (msim_srelC r) Rs Rt RR)
            (p || ps) pt itr_org
            (trigger (Spawn fn arg) >>= k_tgt) fmr)); [|exact SREL].
      intros p itr_rew0 itr_org0 REL EQ.
      dependent destruction REL; rewrite ?bind_trigger in EQ; ss.
      + eapply msim_tau_src; [exact SRELTAUR|].
        eapply msim_roll. eapply SELF. rewrite bind_trigger. exact EQ.
      + destruct SELF as [x SELF].
        eapply msim_choose_src with (x := x); [exact SRELCHOOSER|].
        eapply msim_roll. eapply SELF. rewrite bind_trigger. exact EQ.
      + dependent destruction EQ.
        eapply msim_spawn; [exact MSIM_SPAWN|].
        intro tid. eapply K. eapply srel_cont; eauto.
    - (* yield *)
      eapply (srel_source_ind (trigger (Yield tid) >>= k_src)
        (fun p itr_org =>
          _msim' contextual fl_src fl_tgt Ist (msim_srelC r) RR
            (_msim contextual fl_src fl_tgt Ist
              (msim_srelC r) Rs Rt RR)
            (p || ps) pt itr_org
            (trigger (Yield tid) >>= k_tgt) fmr)); [|exact SREL].
      intros p itr_rew0 itr_org0 REL EQ.
      dependent destruction REL; rewrite ?bind_trigger in EQ; ss.
      + eapply msim_tau_src; [exact SRELTAUR|].
        eapply msim_roll. eapply SELF. rewrite bind_trigger. exact EQ.
      + destruct SELF as [x SELF].
        eapply msim_choose_src with (x := x); [exact SRELCHOOSER|].
        eapply msim_roll. eapply SELF. rewrite bind_trigger. exact EQ.
      + dependent destruction EQ.
        eapply msim_yield; [exact MSIM_YIELD|exact INV|].
        intros fmr0 VALID INV0. eapply K; [exact VALID|exact INV0|].
        eapply srel_cont; eauto.
    - (* gettid *)
      eapply (srel_source_ind (trigger GetTid >>= k_src)
        (fun p itr_org =>
          _msim' contextual fl_src fl_tgt Ist (msim_srelC r) RR
            (_msim contextual fl_src fl_tgt Ist
              (msim_srelC r) Rs Rt RR)
            (p || ps) pt itr_org
            (trigger GetTid >>= k_tgt) fmr)); [|exact SREL].
      intros p itr_rew0 itr_org0 REL EQ.
      dependent destruction REL; rewrite ?bind_trigger in EQ; ss.
      + eapply msim_tau_src; [exact SRELTAUR|].
        eapply msim_roll. eapply SELF. rewrite bind_trigger. exact EQ.
      + destruct SELF as [x SELF].
        eapply msim_choose_src with (x := x); [exact SRELCHOOSER|].
        eapply msim_roll. eapply SELF. rewrite bind_trigger. exact EQ.
      + dependent destruction EQ.
        eapply msim_gettid; [exact MSIM_GETTID|].
        intro tid. eapply K. eapply srel_cont; eauto.
    - (* call_none *)
      eapply (srel_source_ind (trigger (Call fn varg) >>= k_src)
        (fun p itr_org =>
          _msim' contextual fl_src fl_tgt Ist (msim_srelC r) RR
            (_msim contextual fl_src fl_tgt Ist
              (msim_srelC r) Rs Rt RR)
            (p || ps) pt itr_org i_tgt fmr)); [|exact SREL].
      intros p itr_rew0 itr_org0 REL EQ.
      dependent destruction REL; rewrite ?bind_trigger in EQ; ss.
      + eapply msim_tau_src; [exact SRELTAUR|].
        eapply msim_roll. eapply SELF. rewrite bind_trigger. exact EQ.
      + destruct SELF as [x SELF].
        eapply msim_choose_src with (x := x); [exact SRELCHOOSER|].
        eapply msim_roll. eapply SELF. rewrite bind_trigger. exact EQ.
      + dependent destruction EQ.
        eapply msim_call_none;
          [exact MSIM_CALL_NONE|exact CLOSED|exact FUN].
    - (* spawn_none *)
      eapply (srel_source_ind (trigger (Spawn fn varg) >>= k_src)
        (fun p itr_org =>
          _msim' contextual fl_src fl_tgt Ist (msim_srelC r) RR
            (_msim contextual fl_src fl_tgt Ist
              (msim_srelC r) Rs Rt RR)
            (p || ps) pt itr_org i_tgt fmr)); [|exact SREL].
      intros p itr_rew0 itr_org0 REL EQ.
      dependent destruction REL; rewrite ?bind_trigger in EQ; ss.
      + eapply msim_tau_src; [exact SRELTAUR|].
        eapply msim_roll. eapply SELF. rewrite bind_trigger. exact EQ.
      + destruct SELF as [x SELF].
        eapply msim_choose_src with (x := x); [exact SRELCHOOSER|].
        eapply msim_roll. eapply SELF. rewrite bind_trigger. exact EQ.
      + dependent destruction EQ.
        eapply msim_spawn_none;
          [exact MSIM_SPAWN_NONE|exact CLOSED|exact FUN].
    - (* progress *)
      eapply msim_progress; [exact MSIM_PROGRESS|].
      econs; [exact SREL|exact SIM].
  Qed.

  Hint Resolve msim_srelC_mon : paco.

  Lemma msim_srelC_compatible : compatible8 (_msim contextual fl_src fl_tgt Ist) msim_srelC.
  Proof using.
    econs.
    - intros Rs Rt RR ps pt itr_src itr_tgt fmr r1 r2 PR LE.
      eapply msim_srelC_mon; [exact LE|exact PR].
    - intros r Rs Rt RR ps pt itr_org itr_tgt fmr PR.
      destruct PR.
      move SIM before r. revert_until SIM.
      pattern ps, pt, itr_rew, itr_tgt, fmr.
      eapply _msim_tarski, SIM. intros.
      econs. intros NODFS NODFT.
      eapply hsupd_mon.
      + exact (IN NODFS NODFT).
      + intros fmr1 STEP.
        eapply msim_srelC_step; [exact STEP|exact SREL].
  Qed.

  Lemma msim_srelC_spec: msim_srelC <9= gupaco8 (_msim contextual fl_src fl_tgt Ist) (cpn8 (_msim contextual fl_src fl_tgt Ist)).
  Proof using.
    intros. gclo. econs; eauto using msim_srelC_compatible.
    eapply msim_srelC_mon, PR; eauto with paco.
  Qed.

  Lemma srel_yy_y {R} (itr: unit -> itree crisE R) msk_s sp_s :
    srel _ false
      ((SB.sandbox msk_s (SModTr.trans sp_s Sch.yield));;;
       (SB.sandbox msk_s (SModTr.trans sp_s Sch.yield)) >>= itr)
      (SB.sandbox msk_s (SModTr.trans sp_s Sch.yield) >>= itr).
  Proof using.
    set (ysnd := SB.sandbox msk_s (SModTr.trans sp_s Sch.yield)) at 2.

    ginit. gcofix CIH. rewrite yield_unfold.

    rewrite SRed.tau SBRed.tau. grind.
    gstep. econs. econs; eauto.

    rewrite !SRed.bind !SRed.core !SBRed.bind !SBRed.vis; case_match; rewrite vis_trigger; grind;
      gstep; econs; econs; eauto; ss; i.

    destruct x_src; [destruct b|].
    { exists (Some true).

      rewrite !SBRed.ret; ired.
      rewrite !SRed.bind !SRed.call. grind. rewrite !SBRed.tau. grind.
      gstep. econs; econs; eauto.

      unfold SModTr.HoareCall. des_ifs.
      { rewrite !SBRed.bind !SBRed.vis; case_match; rewrite vis_trigger; grind;
          gstep; econs; econs; eauto; ss; i; exists x_src.
        
        rewrite !SBRed.ret; ired.

        rewrite !SBRed.bind !SBRed.vis; case_match; rewrite vis_trigger; grind;
          gstep; econs; econs; eauto; ss; i; exists x_src0.
        rewrite !SBRed.ret; ired.

        rewrite !SBRed.bind !SBRed.vis; case_match; rewrite vis_trigger; grind;
          gstep; econs; econs; eauto; ss; i.
        rewrite !SBRed.ret; ired.

        case_match; rewrite vis_trigger; grind; gstep; econs; econs; eauto; ss; i.
        rewrite !SBRed.ret; ired.

        rewrite !SBRed.bind !SBRed.vis; case_match; rewrite vis_trigger; grind;
          gstep; econs; econs; eauto; ss; i.
        rewrite !SBRed.ret; ired.

        rewrite !SBRed.bind !SBRed.vis; case_match; rewrite vis_trigger; grind;
          gstep; econs; econs; eauto; ss; i.
        rewrite !SBRed.ret; ired.

        gfinal; eauto.
      }
      { rewrite !SBRed.bind !SBRed.vis; case_match; rewrite vis_trigger; grind;
          gstep; econs; econs; eauto; ss; i.
        rewrite !SBRed.ret; ired.

        gfinal; eauto.
      }
    }
    { exists (Some false). rewrite SBRed.ret; grind. gbase. grind. }
    { exists (Some false).
      subst ysnd. rewrite !SBRed.ret; ired.
      rewrite SRed.ret SBRed.ret; ired. guclo srel_eqC_spec. econs; eauto.
    }
  Qed.

  Lemma srel_yy_y_namespace (N : option namespace) {R} (itr: unit -> itree crisE R) msk_s sp_s :
    srel _ false
      ((SB.sandbox msk_s (SModTr.trans sp_s (Sch.yield_namespace N)));;;
       (SB.sandbox msk_s (SModTr.trans sp_s (Sch.yield_namespace N))) >>= itr)
      (SB.sandbox msk_s (SModTr.trans sp_s (Sch.yield_namespace N)) >>= itr).
  Proof using.
    destruct N as [N|]; [|rewrite /Sch.yield_namespace; apply srel_yy_y].
    set (ysnd := SB.sandbox msk_s (SModTr.trans sp_s (Sch.yield_namespace (Some N)))) at 2.

    ginit. gcofix CIH. rewrite yield_namespace_unfold.

    rewrite SRed.tau SBRed.tau. grind.
    gstep. econs. econs; eauto.

    rewrite !SRed.bind !SRed.core !SBRed.bind !SBRed.vis; case_match; rewrite vis_trigger; grind;
      gstep; econs; econs; eauto; ss; i.

    destruct x_src; [destruct b|].
    { exists (Some true).

      rewrite !SBRed.ret; ired.
      rewrite !SRed.bind !SRed.ag !trigger_vis !SBRed.bind !SBRed.vis; case_match;
        rewrite vis_trigger; grind; gstep; econs; econs; eauto; ss.
      rewrite !SBRed.ret; ired.

      rewrite !SRed.call. grind. rewrite !SBRed.tau. grind.
      gstep. econs; econs; eauto.

      unfold SModTr.HoareCall. destruct lookup.
      { rewrite !SBRed.bind !SBRed.vis; case_match; rewrite vis_trigger; grind;
          rewrite orb_true_r; grind;
          gstep; econs; econs; eauto; ss; i; exists x_src.
        
        rewrite !SBRed.ret; ired.

        rewrite !SBRed.bind !SBRed.vis; case_match; rewrite vis_trigger; grind;
          gstep; econs; econs; eauto; ss; i; exists x_src0.
        rewrite !SBRed.ret; ired.

        rewrite !SBRed.bind !SBRed.vis; case_match; rewrite vis_trigger; grind;
          gstep; econs; econs; eauto; ss; i.
        rewrite !SBRed.ret; ired.

        case_match; rewrite vis_trigger; grind; gstep; econs; econs; eauto; ss; i.
        rewrite !SBRed.ret; ired.

        rewrite !SBRed.bind !SBRed.vis; case_match; rewrite vis_trigger; grind;
          gstep; econs; econs; eauto; ss; i.
        rewrite !SBRed.ret; ired.

        rewrite !SBRed.bind !SBRed.vis; case_match; rewrite vis_trigger; grind;
          gstep; econs; econs; eauto; ss; i.
        rewrite !SBRed.ret; ired.

        des_ifs;
        rewrite vis_trigger; grind; gstep; econs; econs; eauto; ss.
        rewrite !SBRed.ret; ired.

        gfinal; eauto.
      }
      { rewrite !SBRed.vis; case_match; rewrite vis_trigger; grind;
          gstep; econs; econs; eauto; ss; i.
        rewrite !SBRed.ret; ired.
        des_ifs; rewrite vis_trigger; grind; gstep; econs; econs; eauto; ss.
        rewrite !SBRed.ret; ired.

        gfinal; eauto.
      }
    }
    { exists (Some false). rewrite SBRed.ret; grind. gbase. grind. }
    { exists (Some false).
      subst ysnd. rewrite !SBRed.ret; ired.
      rewrite SRed.ret SBRed.ret; ired. guclo srel_eqC_spec. econs; eauto.
    }
  Qed.
End SREL.

Section ISIM.
  Import SchA.
  Context `{!crisG Γ Σ α β τ _S _I, !stateGS Σ, !schGS}.
  Variable contextual : contextuality.
  Variable fl_src fl_tgt : gmap fname (option (Any.t → itree crisE Any.t)).
  Variable Ist : iProp Σ.

  Lemma isim_yy_y g ps pt {Rs Rt} (RR : retr_type Σ Rs Rt)
      k_src i_tgt msk_s sp_s :
    isim contextual fl_src fl_tgt Ist g RR ps pt
      ((SB.sandbox msk_s (SModTr.trans sp_s Sch.yield));;;
       (SB.sandbox msk_s (SModTr.trans sp_s Sch.yield)) >>= k_src) i_tgt
    ⊢ isim contextual fl_src fl_tgt Ist g RR ps pt
      ((SB.sandbox msk_s (SModTr.trans sp_s Sch.yield)) >>= k_src) i_tgt.
  Proof using.
    split. intros x wfx SIM.
    Local Transparent isim.
    guclo msim_srelC_spec. econs; eauto using srel_yy_y.
  Qed.

  Lemma wsim_yy_y ps pt {Rs Rt} (RR : retr_type Σ Rs Rt)
      E F g msk_s sp_s k_s i_t :
    wsim fl_src fl_tgt Ist (E, F) g Rs Rt RR ps pt
      ((SB.sandbox msk_s (SModTr.trans sp_s Sch.yield));;;
       (SB.sandbox msk_s (SModTr.trans sp_s Sch.yield)) >>= k_s)
      i_t
    ⊢ wsim fl_src fl_tgt Ist (E, F) g Rs Rt RR ps pt
      ((SB.sandbox msk_s (SModTr.trans sp_s Sch.yield)) >>= k_s) i_t.
  Proof using.
    Local Transparent isim.
    iIntros "SIM".
    iApply wsim_unfold; iIntros "W".
    iPoseProof (wsim_fold with "[W SIM]") as "SIM"; iFrame.
    iPoseProof (wsim_isim with "SIM") as "SIM".
    iApply isim_wsim. iIntros "W".
    iPoseProof ("SIM" with "W") as "SIM".
    iStopProof. split. intros x wfx H1.
    guclo msim_srelC_spec. econs; eauto using srel_yy_y.
  Qed.

  Lemma wsim_yy_y_namespace (N : option namespace)
      ps pt {Rs Rt} (RR : retr_type Σ Rs Rt) E F g msk_s sp_s k_s i_t :
    wsim fl_src fl_tgt Ist (E, F) g Rs Rt RR ps pt
      ((SB.sandbox msk_s (SModTr.trans sp_s (Sch.yield_namespace N)));;;
       (SB.sandbox msk_s (SModTr.trans sp_s (Sch.yield_namespace N))) >>= k_s)
      i_t
    ⊢ wsim fl_src fl_tgt Ist (E, F) g Rs Rt RR ps pt
      ((SB.sandbox msk_s (SModTr.trans sp_s (Sch.yield_namespace N))) >>= k_s)
      i_t.
  Proof using.
    Local Transparent isim.
    iIntros "SIM".
    iApply wsim_unfold; iIntros "W".
    iPoseProof (wsim_fold with "[W SIM]") as "SIM"; iFrame.
    iPoseProof (wsim_isim with "SIM") as "SIM".
    iApply isim_wsim. iIntros "W".
    iPoseProof ("SIM" with "W") as "SIM".
    iStopProof. split. intros x wfx H1.
    guclo msim_srelC_spec. econs; eauto using srel_yy_y_namespace.
  Qed.
End ISIM.

From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export proofmode.
From iris.bi Require Import derived_laws.
Import bi.

Section proofmode.
  Context `{!crisG Γ Σ α β τ _S _I, !stateGS Σ}.
  Lemma tac_wsim_yield_r_r `{!schGS} Δ i (Ist : iProp Σ) E
      fl_s fl_t g R_s R_t RR ps pt msk_s sp_s k_s (msk_t : emask) sp_t k_t :
    sp_s.1 !! (fid SchHdr.yield) = None →
    sp_t.1 !! (fid SchHdr.yield) = None →
    (msk_t _ (subevent _ (Call SchHdr.yield.1 ()↑))) →
    envs_lookup i Δ = Some (false, Ist)%I →
    (match envs_simple_replace i false (Esnoc Enil i Ist) Δ with
      | Some Δ' =>
        envs_entails Δ' (
          wsim fl_s fl_t Ist (E, E) g R_s R_t RR true true
            ((SB.sandbox msk_s (SModTr.trans sp_s 𝒴)) >>= k_s)
            (k_t tt)
        )
      | None => False
      end) →
    envs_entails Δ (
      wsim fl_s fl_t Ist (E, E) g R_s R_t RR ps pt
        ((SB.sandbox msk_s (SModTr.trans sp_s 𝒴)) >>= k_s)
        ((SB.sandbox msk_t (SModTr.trans sp_t 𝒴)) >>= k_t)
    ).
  Proof.
    rewrite envs_entails_unseal=> ???? Hi.
    rewrite envs_lookup_sound //; simpl.
    etransitivity; [|eapply wsim_yield_tgt_rr; eauto].
    rewrite sep_mono_r //.
    destruct (envs_simple_replace) as [Δ'|] eqn:HΔ'; [ | contradiction ].
    rewrite envs_simple_replace_sound' //= Hi.
    iIntros "P ?"; iApply "P"; by iFrame.
  Qed.

  Lemma tac_wsim_yield_N_r Δ i (Ist : iProp Σ) N
      fl_s fl_t g R_s R_t RR ps pt msk_s sp_s k_s (msk_t : emask) sp_t k_t :
    sp_s.1 !! (fid SchHdr.yield) = None →
    sp_t.1 !! (fid SchHdr.yield) = None →
    (msk_t _ (subevent _ (Call SchHdr.yield.1 ()↑))) →
    envs_lookup i Δ = Some (false, Ist)%I →
    (match envs_simple_replace i false (Esnoc Enil i Ist) Δ with
      | Some Δ' => 
        envs_entails Δ' (
          wsim fl_s fl_t Ist (↑N, ↑N) g R_s R_t RR true true
            ((SB.sandbox msk_s (SModTr.trans sp_s 𝒴@{Some N})) >>= k_s)
            (k_t tt)
        )
      | None => False
      end) →
    envs_entails Δ (
      wsim fl_s fl_t Ist (↑N, ↑N) g R_s R_t RR ps pt
        ((SB.sandbox msk_s (SModTr.trans sp_s 𝒴@{Some N})) >>= k_s)
        ((SB.sandbox msk_t (SModTr.trans sp_t 𝒴)) >>= k_t)
    ).
  Proof.
    rewrite envs_entails_unseal=> ???? Hi.
    rewrite envs_lookup_sound //; simpl.
    etransitivity; [|eapply wsim_yield_namespace_ir; eauto].
    rewrite sep_mono_r //.
    destruct (envs_simple_replace) as [Δ'|] eqn:HΔ'; [ | contradiction ].
    rewrite envs_simple_replace_sound' //= Hi.
    iIntros "P ?"; iApply "P"; by iFrame.
  Qed.

  Lemma tac_wsim_yield_i_r `{!schGS} Δ i (Ist : iProp Σ) j mtid stid E_s
      fl_s fl_t g R_s R_t RR ps pt msk_s sp_s k_s (msk_t : emask) sp_t k_t :
    sp_s.1 !! (fid SchHdr.yield) = fsp_some (SchA.yield_spec E_s) →
    sp_t.1 !! (fid SchHdr.yield) = None →
    (msk_t _ (subevent _ (Call SchHdr.yield.1 ()↑))) →
    envs_lookup i Δ = Some (false, Ist)%I →
    envs_lookup j Δ = Some (false, Tid mtid stid)%I →
    i ≠ j →
    (match envs_simple_replace i false (Esnoc Enil i Ist) Δ with
      | Some Δ' => 
        envs_entails Δ' (
          wsim fl_s fl_t Ist (E_s, E_s) g R_s R_t RR true true
            ((SB.sandbox msk_s (SModTr.trans sp_s 𝒴)) >>= k_s)
            (k_t tt)
        )
      | None => False
      end) →
    envs_entails Δ (
      wsim fl_s fl_t Ist (E_s, E_s) g R_s R_t RR ps pt
        ((SB.sandbox msk_s (SModTr.trans sp_s 𝒴)) >>= k_s)
        ((SB.sandbox msk_t (SModTr.trans sp_t 𝒴)) >>= k_t)
    ).
  Proof.
    rewrite envs_entails_unseal=> ??? Hi Hj ? Hij.
    rewrite envs_lookup_sound; last apply Hi. simpl.
    etransitivity; [|eapply wsim_yield_tgt_ir; eauto].
    rewrite envs_lookup_split; [|rewrite envs_lookup_envs_delete_ne; eauto]; simpl.
    rewrite sep_mono_r // sep_mono_r //.
    destruct (envs_simple_replace) as [Δ'|] eqn:HΔ'; [ | contradiction ].
    rewrite (envs_simple_replace_sound') //= Hij.
    iIntros "He ? ?"; iApply ("He" with "[$]"); ss; eauto with iFrame.
  Qed.

  Lemma tac_wsim_yield_N_N Δ i (Ist : iProp Σ) N_s N_t E
      fl_s fl_t g R_s R_t RR ps pt msk_s sp_s k_s (msk_t : emask) sp_t k_t :
    sp_s.1 !! (fid SchHdr.yield) = None →
    sp_t.1 !! (fid SchHdr.yield) = None →
    img_msk msk_t →
    (msk_t _ (subevent _ (Call SchHdr.yield.1 ()↑))) →
    ↑N_t ⊆@{coPset} ↑N_s →
    E = ↑N_s∖↑N_t →
    envs_lookup i Δ = Some (false, Ist)%I →
    (match envs_simple_replace i false (Esnoc Enil i Ist) Δ with
      | Some Δ' => 
        envs_entails Δ' (
          wsim fl_s fl_t Ist (E, E) g R_s R_t RR true true
            ((SB.sandbox msk_s (SModTr.trans sp_s 𝒴@{Some N_s})) >>= k_s)
            (k_t tt)
        )
      | None => False
      end) →
    envs_entails Δ (
      wsim fl_s fl_t Ist (E, E) g R_s R_t RR ps pt
        ((SB.sandbox msk_s (SModTr.trans sp_s 𝒴@{Some N_s})) >>= k_s)
        ((SB.sandbox msk_t (SModTr.trans sp_t 𝒴@{Some N_t})) >>= k_t)
    ).
  Proof.
    rewrite envs_entails_unseal=> ????? -> ? Hi.
    rewrite envs_lookup_sound //; simpl.
    etransitivity; [|eapply wsim_yield_namespace_N_N; eauto].
    rewrite sep_mono_r //.
    destruct (envs_simple_replace) as [Δ'|] eqn:HΔ'; [ | contradiction ].
    rewrite envs_simple_replace_sound' //= Hi.
    iIntros "P ?"; iApply "P"; by iFrame.
  Qed.

  Lemma tac_wsim_yield_i_N `{!schGS}
      Δ i (Ist : iProp Σ) j
      (E_s : coPset) (N_t : namespace)
      (mtid stid : nat)
      fl_s fl_t  (g : WSim.rel) {R_s R_t} RR ps pt
      (k_s : () → itree crisE R_s)
      (k_t : () → itree crisE R_t)
      (msk_s msk_t : emask)
      (sp_s sp_t : specmap) :
    sp_s.1 !! fid SchHdr.yield = fsp_some (SchA.yield_spec E_s) →
    sp_t.1 !! fid SchHdr.yield = None →
    img_msk msk_t →
    (msk_t _ (subevent _ (Call SchHdr.yield.1 ()↑))) →
    ↑N_t ⊆E_s →
    envs_lookup i Δ = Some (false, Ist)%I →
    envs_lookup j Δ = Some (false, Tid mtid stid)%I →
    i ≠ j →
    (match envs_simple_replace i false (Esnoc Enil i Ist) Δ with
      | Some Δ' => 
        envs_entails Δ' (
          wsim fl_s fl_t Ist (E_s∖↑N_t, E_s∖↑N_t) g R_s R_t RR true true
            ((SB.sandbox msk_s (SModTr.trans sp_s 𝒴)) >>= k_s)
            (k_t tt)
        )
      | None => False
      end) →
    envs_entails Δ (wsim fl_s fl_t Ist (E_s∖↑N_t, E_s∖↑N_t) g R_s R_t RR ps pt
      ((SB.sandbox msk_s (SModTr.trans sp_s 𝒴)) >>= k_s)
      ((SB.sandbox msk_t (SModTr.trans sp_t 𝒴@{Some N_t})) >>= k_t)
    ).
  Proof using.
    rewrite envs_entails_unseal=> ????? Hi Hj ? Hij.
    rewrite envs_lookup_sound; last apply Hi. simpl.
    etransitivity; [|eapply wsim_yield_namespace_i_N; eauto].
    rewrite envs_lookup_split; [|rewrite envs_lookup_envs_delete_ne; eauto]; simpl.
    rewrite sep_mono_r // sep_mono_r //.
    destruct (envs_simple_replace) as [Δ'|] eqn:HΔ'; [ | contradiction ].
    rewrite (envs_simple_replace_sound') //= Hij.
    iIntros "He ? ?"; iApply ("He" with "[$]"); ss; eauto with iFrame.
  Qed.

  Lemma tac_wsim_yield_i_i `{!schGS}
      Δ i (Ist : iProp Σ)
      fl_s fl_t
      (E E_s E_t : coPset) (g : WSim.rel)
      {R_s R_t} RR ps pt
      (k_s : () → itree crisE R_s)
      (k_t : () → itree crisE R_t)
      (msk_s msk_t : emask)
      (sp_s sp_t : specmap) :
    sp_s.1 !! fid SchHdr.yield = fsp_some (SchA.yield_spec E_s) →
    sp_t.1 !! fid SchHdr.yield = fsp_some (SchA.yield_spec E_t) →
    img_msk msk_t →
    (msk_t _ (subevent _ (Call SchHdr.yield.1 ()↑))) →
    E_t ⊆ E_s →
    E = E_s ∖ E_t →
    envs_lookup i Δ = Some (false, Ist)%I →
    (match envs_simple_replace i false (Esnoc Enil i Ist) Δ with
      | Some Δ' => 
        envs_entails Δ' (
          wsim fl_s fl_t Ist (E, E) g R_s R_t RR true true
            ((SB.sandbox msk_s (SModTr.trans sp_s 𝒴)) >>= k_s)
            (k_t tt)
        )
      | None => False
      end) →
    envs_entails Δ (wsim fl_s fl_t Ist (E, E) g R_s R_t RR ps pt
      ((SB.sandbox msk_s (SModTr.trans sp_s 𝒴)) >>= k_s)
      ((SB.sandbox msk_t (SModTr.trans sp_t 𝒴)) >>= k_t)).
  Proof using.
    rewrite envs_entails_unseal=> ????? -> ? Hi.
    etrans; last eapply (wsim_yield_i_i with "P"); eauto.
    rewrite envs_lookup_sound //; simpl. rewrite sep_mono_r //.
    destruct (envs_simple_replace) as [Δ'|] eqn:HΔ'; [ | contradiction ].
    rewrite envs_simple_replace_sound' //= Hi.
    iIntros "P ?"; iApply "P"; by iFrame.
  Qed.
End proofmode.

Tactic Notation "sYield" :=
  cNormS; cStepsT;
  lazymatch goal with
  | |- envs_entails _ (
      wsim ?fl_s ?fl_t ?Ist ?Es ?g ?R_s ?R_t ?RR ?p_s ?p_t 
        (SB.sandbox ?msk_s (SModTr.trans ?sp_s 𝒴) >>= _)
        (SB.sandbox ?msk_t (SModTr.trans ?sp_t 𝒴) >>= _)
    ) =>
      (eapply (tac_wsim_yield_r_r _ _ Ist _
        fl_s fl_t g R_s R_t RR p_s p_t msk_s sp_s _ msk_t sp_t _);
      [by simpl_sp
      |by simpl_sp
      |solve_msk
      |iAssumptionCore || fail "sYield: cannot find ist"
      |simpl]) ||
      (eapply (tac_wsim_yield_i_r _ _ Ist _ _ _ _
        fl_s fl_t g R_s R_t RR p_s p_t msk_s sp_s _ msk_t sp_t _);
      [by simpl_sp
      |by simpl_sp
      |solve_msk
      |iAssumptionCore || fail "sYield: cannot find ist"
      |iAssumptionCore || fail "sYield: cannot find tid"
      |eauto
      |simpl]) ||
      (eapply (tac_wsim_yield_i_i _ _ Ist
        fl_s fl_t _ _ _ g RR p_s p_t);
      [by simpl_sp
      |by simpl_sp
      |solve_msk
      |solve_msk
      |simpl_set; iSolveSideCondition
      |simpl_set; iSolveSideCondition
      |iAssumptionCore || fail "sYield: cannot find ist"
      |simpl])
  | |- envs_entails _ (
      wsim ?fl_s ?fl_t ?Ist ?Es ?g ?R_s ?R_t ?RR ?p_s ?p_t
        (SB.sandbox ?msk_s (SModTr.trans ?sp_s 𝒴@{?N}) >>= _)
        (SB.sandbox ?msk_t (SModTr.trans ?sp_t 𝒴) >>= _)
    ) =>
      eapply (tac_wsim_yield_N_r _ _ Ist _);
      [by simpl_sp
      |by simpl_sp
      |solve_msk
      |iAssumptionCore || fail "sYield: cannot find ist"
      |simpl]
  | |- environments.envs_entails _ (
      wsim ?fl_s ?fl_t ?Ist ?Es ?g ?R_s ?R_t ?RR ?p_s ?p_t 
        (SB.sandbox ?msk_s (SModTr.trans ?sp_s 𝒴) >>= _)
        (SB.sandbox ?msk_t (SModTr.trans ?sp_t 𝒴@{Some ?N}) >>= _)
      ) =>
      eapply (tac_wsim_yield_i_N _ _ Ist _ _ N);
      [ by simpl_sp
      | by simpl_sp
      | solve_msk
      | solve_msk
      | iSolveSideCondition
      | iAssumptionCore || fail "sYield: cannot find ist"
      | iAssumptionCore || fail "sYield: cannot find tid"
      | auto
      | simpl
      ]
  | |- envs_entails _ (
      wsim ?fl_s ?fl_t ?Ist ?Es ?g ?R_s ?R_t ?RR ?p_s ?p_t
        (SB.sandbox ?msk_s (SModTr.trans ?sp_s 𝒴@{Some ?N_s}) >>= _)
        (SB.sandbox ?msk_t (SModTr.trans ?sp_t 𝒴@{Some ?N_t}) >>= _)
    ) =>
      eapply (tac_wsim_yield_N_N _ _ Ist N_s N_t);
      [by simpl_sp
      |by simpl_sp
      |solve_msk
      |solve_msk
      |iSolveSideCondition
      |simpl_set; iSolveSideCondition
      |iAssumptionCore || fail "sYield: cannot find ist"
      |simpl]
  end; cNormT.

Tactic Notation "sYields" :=
  sYield; try cStepsT;
  repeat (sYield; try cStepsT).

Tactic Notation "sYieldS" := 
  cNormS;
  lazymatch goal with
  | |- environments.envs_entails _ (
      wsim ?fl_s ?fl_t ?Ist ?Es ?g ?R_s ?R_t ?RR ?p_s ?p_t 
        (SB.sandbox ?msk_s (SModTr.trans ?sp_s 𝒴) >>= _)
        _
    ) =>
      iApply wsim_yield_src
  | |- environments.envs_entails _ (
      wsim ?fl_s ?fl_t ?Ist ?Es ?g ?R_s ?R_t ?RR ?p_s ?p_t
        (SB.sandbox ?msk_s (SModTr.trans ?sp_s 𝒴@{?N}) >>= _)
        _
    ) =>
      iApply wsim_yield_namespace_src
  end.
