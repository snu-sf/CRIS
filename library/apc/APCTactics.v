From CRIS.common Require Import CRIS.
From CRIS.apc Require Import APCHeader APC APCA.

(* useful apc lemmas - require IST *)
Section LEMMAS.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.
  Context `{!stateGS Σ}.

  Local Definition rel : Type := ∀ R_s R_t : Type,
    retr_type Σ R_s R_t → bool → bool →
    itree crisE R_s → itree crisE R_t → iProp Σ.

  Context (fl_s fl_t : gmap fname (option (Any.t → itree crisE Any.t))).
  Context (Ist : iProp Σ).
  Context (R_s R_t : Type).
  Context (RR : retr_type Σ R_s R_t).
  Context (ps pt : bool).

  Lemma wsim_apc_src
    (E : coPset) (g : rel) (k_src : () -> itree crisE R_s) (i_tgt : itree crisE R_t)
    (msk_s : emask) (sp_s sp_pure : specmap) (ow od : Ord.t) :
    wsim fl_s fl_t Ist (E, E) g R_s R_t RR true pt (k_src ()) i_tgt ⊢
    wsim fl_s fl_t Ist (E, E) g R_s R_t RR ps pt
      ((SB.sandbox msk_s (SModTr.trans sp_s (_APC od sp_pure ow))) >>= k_src)
      i_tgt.
  Proof using.
    iIntros "ISIM". rewrite unfold_APC.
    cStepsS. cForceS true. cStepsS. iFrame.
  Qed.

  Lemma wsim_apc_src_call_tgt_weaker
    (E : coPset) (g : rel) (k_src : () → itree crisE R_s) (k_tgt: Any.t -> itree crisE R_t)
    (msk_s : emask) (sp_s sp_pure : specmap)
    (fn: string) args fsp' fsp X (spec_arg: X) o P Q
    (ow_src ow_fn od_src od_fn : Ord.t)
    (WIDTH: (ow_fn < ow_src)%ord)
    (DEPTH: (od_fn < od_src)%ord)
    (SpPureInSp: sp_pure ⊆ sp_s)
    (fnInSpPure: sp_pure.1 !! (funid fn) = Some fsp')
    (WEAK: ⊢ fspec_imply fsp' fsp)
    (fspIsfspecapc: fsp = (@fspec_apc Σ X o (λ x, (P x, Q x))))
    :
    (((P spec_arg args ∗ ⌜∃ vo : Ord.t, od_fn ↑ = vo ↑ ∧ (o spec_arg <= vo)%ord⌝) ∗ Ist) ∗
     (∀ (ret: Any.t),
        (Ist ∗ Q spec_arg ret)
        -∗ wsim fl_s fl_t Ist (E, E) g R_s R_t RR false false
             ((SB.sandbox msk_s (SModTr.trans sp_s (_APC od_src sp_pure ow_fn))) >>= k_src)
             (k_tgt ret)))
    ⊢
      wsim fl_s fl_t Ist (E, E) g R_s R_t RR ps pt
        ((SB.sandbox msk_s (SModTr.trans sp_s (_APC od_src sp_pure ow_src))) >>= k_src)
        ((trigger (Call fn args)) >>= k_tgt).
  Proof using.
    (* intros Hchoose Htake Hguarantee Hassume Hcall. *)
    iIntros "[[[PRE %] IST] ISIM]".
    des. set_marker m. hide_ihyps. rewrite unfold_APC. show_until m.
    cStepsS. cForceS false.
    cStepsS. cForceS ow_fn.
    cStepsS. cForceS WIDTH.
    cStepsS. cForceS fn.
    cStepsS. cForceS od_fn. cStepsS.
    cForceS. iSplit; et. cStepsS. simpl_sp.
    cStepsS.
    iPoseProof (WEAK with "") as "WEAK".
    iSpecialize ("WEAK" with "[] [PRE]").
    { instantiate (1 := (λ _ a, (Q spec_arg a)%I)).
      instantiate (1 := (λ x a, (P spec_arg a ∗ ⌜∃ vo0, x = vo0 ↑ ∧ (o spec_arg <= vo0)%ord⌝))%I).
      subst fsp. rewrite /fspec_apc. ss. iPureIntro. exists spec_arg. ss. }
    { ss; iFrame; eauto. }
    iDestruct "WEAK" as "> (%pre & %post & %Hfsp & [PRE POST])".
    cForceS (FSpec_mk _ _ Hfsp).
    cStepsS. cForceS args.
    cStepsS. cForceS; iSplitL "PRE"; eauto.
    cStepsS. case_match; last by cStepsS. cStepsT. cCall "IST" as (?) "IST".
    cStepsS. case_match; last by cStepsS. cStepsS. case_match; last by cStepsS.
    cStepsS. iPoseProof ("POST" with "ASM") as ">POST".
    iApply wsim_reset. iSpecialize ("ISIM" $! ret). cStepsT.
    iApply "ISIM"; iFrame.
  Qed.

  Lemma wsim_apc_src_call_tgt
    (E : coPset) (g : rel) (k_src : () → itree crisE R_s) (k_tgt: Any.t -> itree crisE R_t)
    (msk_s : emask) (sp_s sp_pure : specmap)
    (fn: string) args fsp X (spec_arg: X) o P Q
    (ow_src ow_fn od_src od_fn : Ord.t)
    (WIDTH: (ow_fn < ow_src)%ord)
    (DEPTH: (od_fn < od_src)%ord)
    (SpPureInSp: sp_pure ⊆ sp_s)
    (fnInSpPure: sp_pure.1 !! (funid fn) = Some fsp)
    (fspIsfspecapc: fsp = (@fspec_apc Σ X o (λ x, (P x, Q x))))
    :
    (((P spec_arg args ∗ ⌜∃ vo : Ord.t, od_fn ↑ = vo ↑ ∧ (o spec_arg <= vo)%ord⌝) ∗ Ist) ∗
     (∀ (ret: Any.t),
        (Ist ∗ Q spec_arg ret)
        -∗ wsim fl_s fl_t Ist (E, E) g R_s R_t RR false false
             ((SB.sandbox msk_s (SModTr.trans sp_s (_APC od_src sp_pure ow_fn))) >>= k_src)
             (k_tgt ret)))
    ⊢
      wsim fl_s fl_t Ist (E, E) g R_s R_t RR ps pt
        ((SB.sandbox msk_s (SModTr.trans sp_s (_APC od_src sp_pure ow_src))) >>= k_src)
        ((trigger (Call fn args)) >>= k_tgt).
  Proof using.
    eapply wsim_apc_src_call_tgt_weaker; et. 
    eapply fspec_imply_refl.
  Qed.

End LEMMAS.

Tactic Notation "apcS/" :=
  iApply wsim_apc_src; ss.
Ltac apcS := apcS/; cShowS; cNormS; cHideS.

Tactic Notation "apcCallWeak/" uconstr(hyps) "as" "(" simple_intropattern(vret) ")" uconstr(IST) :=
  cShowS; cShowT; cNormS; cNormT; iApply wsim_apc_src_call_tgt_weaker; [ | | |simpl_sp| | |iSplitL hyps; [try done|try clear vret; try iClear IST; iIntros (vret) IST; cNormS; cNormT]]; ss.
Tactic Notation "apcCallWeak" uconstr(hyps) "as" "(" simple_intropattern(vret) ")" uconstr(IST) :=
  apcCallWeak/ hyps as (vret) IST; cHideS; cHideT.

Tactic Notation "apcCall/" uconstr(hyps) "as" "(" simple_intropattern(vret) ")" uconstr(IST) :=
  cShowS; cShowT; cNormS; cNormT; iApply wsim_apc_src_call_tgt; [ | | |simpl_sp| |iSplitL hyps; [try done|try clear vret; try iClear IST; iIntros (vret) IST; ss; cNormS; cNormT]]; ss.
Tactic Notation "apcCall" uconstr(hyps) "as" "(" simple_intropattern(vret) ")" uconstr(IST) :=
  apcCall/ hyps as (vret) IST; cHideS; cHideT.
