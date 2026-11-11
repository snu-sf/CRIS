From CRIS.common Require Import CRIS.
From CRIS.helping Require Export HelpingOn HelpingOff HelpingResource.
From CRIS.scheduler Require Import SchHeader SchI SchA.
From iris.algebra Require Import coPset.

#[local] Existing Instance helpingG.
#[local] Existing Instance helping_inG.
#[local] Existing Instance tokenG.

Section resource.
  Context `{!crisG Γ Σ α β τ _S _I, !helpingGS}.

  Definition hinv_ownE (E : coPset) : iProp Σ := own help_name (Some (CoPset E), None).
  Definition syn_hinv_ownE {n : level} (E : coPset) : GTerm.t n :=
    sown help_name (Some (CoPset E), None).
  Global Instance SLRed_hinv_ownE n E :
    SLRed n (syn_hinv_ownE E) (hinv_ownE E).
  Proof. solve_sl_red. Qed.

  Lemma hinv_ownE_exploit (E1 E2 : coPset) : hinv_ownE E1 ∗ hinv_ownE E2 ⊢ ⌜E1 ## E2⌝.
  Proof.
    iIntros "[H1 H2]". iCombine "H1 H2" gives %[WF _]%pair_valid.
    by rewrite /= -Some_op Some_valid coPset_disj_valid_op in WF.
  Qed.
  Lemma hinv_ownE_op (E1 E2 : coPset) : E1 ## E2 →
    hinv_ownE (E1 ∪ E2) ⊣⊢ hinv_ownE E1 ∗ hinv_ownE E2.
  Proof using. intros dis; rewrite -own_op -pair_op -Some_op coPset_disj_union; ss. Qed.
  Lemma hinv_ownE_subset (E1 E2 : coPset) :
    E1 ⊆ E2 →
    hinv_ownE E2 ⊢ hinv_ownE E1 ∗ (hinv_ownE E1 -∗ hinv_ownE E2).
  Proof using.
    iIntros (SUB) "E".
    rewrite (union_difference_L E1 E2); [|done].
    iPoseProof (hinv_ownE_op with "E") as "[E1 E2]"; [set_solver|].
    iFrame. iIntros "E1".
    iApply hinv_ownE_op; [set_solver|iFrame].
  Qed.

  Section rules.
    Context `{!stateGS Σ}.

    Context (fl_s fl_t : gmap fname (Any.t → itree crisE Any.t)).
    Context (R_s R_t : Type) (RR : retr_type Σ R_s R_t).
    Context (jobs : SAny.t → itree crisE (SAny.t + SAny.t)).
    Context (mn : string) (sp : specmap).

    Lemma wsim_helping_run
        (Ist : iProp Σ)
        (ps pt : bool)
        (N : option namespace)
        (parg : SAny.t)
        k_s k_t E1 E2 g :
      fl_s !! funid (Helping.run mn) =
        Some (SB.sandbox_body
          (msk_scp (HelpingOn.scopes mn) msk_true,
            (SModTr.trans_fnsem sp (None, HelpingOn.run mn jobs)))) →
      (∀ reqid,
        HelpPend reqid N parg -∗
        wsim fl_s fl_t Ist (E1, E2) g R_s R_t RR true pt
          (x <- SB.sandbox (msk_scp (HelpingOn.scopes mn) msk_true)
            (SModTr.trans sp
              (𝒴@{N};;; HelpingOn.try_run mn jobs reqid));;
          tau;; k_s x)
          k_t) -∗
      wsim fl_s fl_t Ist (E1, E2) g R_s R_t RR ps pt
        (x <- trigger (Call (Helping.run mn) (N, parg)↑);; k_s x)
        k_t.
    Proof.
      iIntros (Hfind) "K".
      cInlineS. cStepsS. rewrite /HelpingOn.run. cStepsS.
      replace_s; last iApply ("K" with "ASM").
      symmetry; etrans; first hnorm_itr; grind.
    Qed.

    Lemma wsim_helping_pend_try_run
        (reqid : nat) (N : option namespace) (arg : SAny.t)
        (Ist : iProp Σ)
        (ps pt : bool)
        (ktr_s : Any.t → itree crisE R_s)
        {R} (itr_t : itree crisE R) (ktr_t : R → itree crisE R_t)
        E1 E2 g :
      HelpPend reqid N arg -∗
      wsim fl_s fl_t Ist (E1, E2) g SAny.t R
        (λ r_s r_t,
          winv (E1, E2) ∗
          (HelpDone reqid r_s -∗
            wsim fl_s fl_t Ist (E1, E2) g R_s R_t RR true false
              (ktr_s r_s↑) (ktr_t r_t)))
        true pt
          (⇓sbox(msk_scp (HelpingOn.scopes mn) msk_true)
            (⇓smod(sp)
              (ITree.iter (λ arg, 𝒴@{N};;; ⇓sbox(msk_pure) (jobs arg)) arg)))
          itr_t -∗
      wsim fl_s fl_t Ist (E1, E2) g R_s R_t RR ps pt
        (x_ <- ⇓sbox(msk_scp (HelpingOn.scopes mn) msk_true)
          (⇓smod(sp) (HelpingOn.try_run mn jobs reqid));;
        ktr_s x_)
        (itr_t >>= ktr_t).
    Proof.
      iIntros "Pend SIM".
      rewrite /HelpingOn.try_run. cForceS None. cForceS N. cForceS arg.
      cForceS. iFrame "Pend". cStepsS.
      cBind _ "SIM" as (??) "Q".
      iDestruct "Q" as "[W K]".
      iApply wsim_fold; iFrame "W". cStepsS.
      iApply ("K" with "ASM").
    Qed.

    Lemma wsim_HelpDone_try_run
        (reqid : nat) (ret : SAny.t)
        (Ist : iProp Σ)
        (ps pt : bool)
        k_s k_t E1 E2 g :
      HelpDone reqid ret -∗
      wsim fl_s fl_t Ist (E1, E2) g R_s R_t RR true pt
        (k_s ret↑) k_t -∗
      wsim fl_s fl_t Ist (E1, E2) g R_s R_t RR ps pt
        (x_ <- ⇓sbox(msk_scp (HelpingOn.scopes mn) msk_true)
          (⇓smod(sp) (HelpingOn.try_run mn jobs reqid));;
        k_s x_)
        k_t.
    Proof.
      iIntros "#Done K".
      rewrite /HelpingOn.try_run. cForceS (Some ret). cForceS. iFrame "Done". cStepsS.
      iApply "K".
    Qed.

    Lemma wsim_helping_help
        (reqid : nat) (N N2 : namespace) (E : coPset) (arg : SAny.t)
        (Ist : iProp Σ)
        (g : WSim.rel)
        (ps pt : bool)
        (ktr_s : Any.t → itree crisE R_s)
        {R} (itr_t : itree crisE R) (ktr_t : R → itree crisE R_t) :
      HelpPend reqid (Some N2) arg -∗
      (∃ n, =|n, ↑N|={E, ↑N}=>
        wsim fl_s fl_t Ist (↑N2, ↑N2) g SAny.t R
          (λ r_s r_t,
            winv (↑N2, ↑N2) ∗
            (HelpDone reqid r_s -∗
              wsim fl_s fl_t Ist (↑N, ↑N) g R_s R_t RR true false
                (ktr_s ()↑) (ktr_t r_t)))
          true pt
            (⇓sbox(msk_scp (HelpingOn.scopes mn) msk_true)
              (⇓smod(sp)
                (ITree.iter
                  (λ arg, 𝒴@{Some N2};;; ⇓sbox(msk_pure) (jobs arg)) arg)))
            itr_t) -∗
      wsim fl_s fl_t Ist (↑N, E) g R_s R_t RR ps pt
        (x_ <- ⇓sbox(msk_scp (HelpingOn.scopes mn) msk_true)
          (⇓smod(sp) (HelpingOn.help mn jobs (Some N)↑));;
        ktr_s x_)
        (itr_t >>= ktr_t).
    Proof.
      iIntros "Tkn [%n SIM]".
      rewrite /HelpingOn.help. cStepsS.
      cForceS reqid. cForceS (Some N2). cForceS arg.
      cForceS. iFrame "Tkn". cStepsS.
      iMod "SIM" as "SIM".
      cForceS; iSplitL ""; first done. cStepsS.
      cBind _ "SIM" as (??) "Q".
      iDestruct "Q" as "[W K]".
      iApply wsim_fold; iFrame "W".
      cForceS; iSplitL ""; first done. cStepsS.
      iApply ("K" with "ASM''").
    Qed.
  End rules.

  (* Add cancellable-invariant namespace ownership to a client state invariant. *)
  Definition IstHelp (Ist : iProp Σ) (E : coPset) : iProp Σ :=
    (hinv_ownE E ∗ Ist)%I.

  Lemma IstHelp_nested_equiv
      (Ist IstR : iProp Σ) (E : coPset) :
    IstHelp Ist E ∗ IstR ⊣⊢ IstHelp (Ist ∗ IstR) E.
  Proof.
    rewrite /IstHelp. iSplit.
    - iIntros "[[HE HI] HR]". iFrame.
    - iIntros "[HE [HI HR]]". iFrame.
  Qed.

  (* a variant of cancellable invariants to streamline invariant opening/closing in helping *)
  Definition hinv {n : level} (N : namespace) (γ : gname) (P : GTerm.t n) : iProp Σ :=
    inv n N (sown γ (Excl ()) ∗ P ∨ syn_hinv_ownE (↑N))%SAT.
  Definition syn_hinv {n : level} (N : namespace) (γ : gname) (P : GTerm.t n) : GTerm.t n :=
    syn_inv N (sown γ (Excl ()) ∗ P ∨ syn_hinv_ownE (↑N))%SAT.
  Global Instance SLRed_hinv n N γ P :
    SLRed n (syn_hinv N γ P) (hinv N γ P).
  Proof. solve_sl_red. Qed.

  Global Instance hinv_persistent {n : level} N γ (P : GTerm.t n) : Persistent (hinv N γ P).
  Proof. rewrite /hinv; apply _. Qed.

  Lemma hinv_excl_alloc : ⊢ o=> ∃ γ, own γ (Excl ()).
  Proof. iApply own_alloc; ss. Qed.

  Lemma hinv_alloc `(P : GTerm.t n) Ew E N :
    ↑N ⊆ Ew →
    ⟦P⟧ =|S n, Ew|={E}=∗ ∃ γ, hinv N γ P.
  Proof.
    iIntros (?) "HP". iMod hinv_excl_alloc as "[%γ Hexcl]"; iExists γ.
    iApply inv_alloc; ss.
    rewrite SPropBi.or_red_base; iLeft. rewrite SPropBi.sep_red_base SPropiProp.own_red; iFrame.
  Qed.

  (* If we own the namespace of the invariant, then we can open the invariant atomically. *)
  Lemma hinv_acc {n : level} Ew E F N γ (P : GTerm.t n) :
    ↑N ⊆ E → ↑N ⊆ F → E ⊆ Ew →
    hinv N γ P -∗
    hinv_ownE F =|S n, Ew|={E, E∖↑N}=∗ ⟦P⟧ ∗ hinv_ownE (F∖↑N) ∗
      (⟦P⟧ -∗ hinv_ownE (F∖↑N) =|S n, Ew|={E∖↑N,E}=∗ hinv_ownE F) ∧
      (=|S n, Ew|={E∖↑N, E}=> (⟦P⟧ -∗ hinv_ownE (F∖↑N) =|S n, Ew|={E}=∗ hinv_ownE F)).
  Proof.
    iIntros (???) "#Hinv HE".
    iInv "Hinv" as "[[Hexcl $]|HE2]" "close"; cycle 1.
    { iPoseProof (hinv_ownE_exploit with "[HE HE2]") as "%Hcont"; iFrame.
      pose proof (nclose_infinite N) as HN; rewrite -coPset_infinite_finite in HN.
      specialize (HN []) as [i [Hi _]]; set_solver.
    }
    rewrite [F as X in hinv_ownE X](union_difference_L (↑N) F) //.
    rewrite (hinv_ownE_op (↑N)); last set_solver. 
    iDestruct "HE" as "[HN $]".
    iModIntro; iSplit.
    { iIntros "P $"; iFrame. iMod ("close" with "[-]") as "_"; eauto with iFrame. }
    iMod ("close" with "[HN]") as "_"; first eauto with iFrame.
    iIntros "!> P HE2".
    iInv "Hinv" as "[[Hexcl' _] | HE]" "Hclose".
    { iCombine "Hexcl" "Hexcl'" gives %[]. }
    iFrame. iApply ("Hclose" with "[-]"); first eauto with iFrame.
  Qed.

  Global Instance into_inv_hinv N γ `{P : GTerm.t n} : IntoInv (hinv N γ P) N := {}.

  Global Instance into_acc_hinv Ist Ew E F N γ `{p : GTerm.t n}
      (P : iProp Σ) :
    SLRed n p P →
    IntoAcc (X:=unit) (hinv N γ p)
            (↑N ⊆ E ∧ E ⊆ Ew) (⌜↑N ⊆ F⌝ ∗ IstHelp Ist F)
            (fupd_ex (S n) Ew E (E∖↑N)) bupd
            (λ _, IstHelp Ist (F∖↑N) ∗ P)%I (λ _, emp)%I
            (λ _, Some
              ((P -∗ IstHelp Ist (F∖↑N) =|S n, Ew|={E∖↑N, E}=∗
                  IstHelp Ist F) ∧
              (=|S n, Ew|={E∖↑N, E}=>
                (P -∗ IstHelp Ist (F∖↑N) =|S n, Ew|={E}=∗
                  IstHelp Ist F))))%I.
  Proof.
    rewrite /IntoAcc /accessor bi.exist_unit /= /IstHelp.
    iIntros (<- [? ?]) "#Hinv [% [HE IST]]".
    iMod (hinv_acc with "Hinv HE") as "[$ [HE Close]]"; eauto. iFrame "HE IST".
    iIntros "!> _ !>"; iFrame.
    iSplit; [iDestruct "Close" as "[Close _]"|iDestruct "Close" as "[_ > Close]"].
    { iIntros "P [HE $]". iApply ("Close" with "[$] [$]"). }
    iIntros "!> P [HE $]". iApply ("Close" with "[$] [$]").
  Qed.

End resource.

Section help.
  Context `{!crisG Γ Σ α β τ _S _I, !helpingGS}.

  Local Notation state := (gmap key (option Any.t)).
  Local Notation post R_s R_t := (state * R_s → state * R_t → iProp Σ).

  Context (fl_s fl_t : gmap fname (Any.t → itree crisE Any.t)).
  Context (R_s R_t : Type) (RR : post R_s R_t).

  (* Helping related context *)
  Context (jobs : SAny.t → itree crisE (SAny.t + SAny.t)).
  Context (mn : string) (sp : specmap).

  (*
  Lemma wsim_helping_help2
      `{!schGS} (st_src st_tgt : state)
      (ps pt : bool) k_s k_t E g (req_id : nat) x arg (mtid stid : nat) :
    sp.1 !! (fid SchHdr.yield) = fsp_some (SchA.yield_spec E) →
    Tid mtid stid -∗
    HelpPend req_id x -∗
    (∃ n, =| n, E |={ E, ∅ }=> Ist st_src st_tgt ∗
      (wsim fl_s fl_t Ist (E, ∅) g SAny.t ()
        (λ '(st_s, r_s) '(st_t, r_t), ⌜st_s = st_src ∧ st_t = st_tgt⌝ ∗ winv (E, ∅) ∗
          (∀ st_src st_tgt,
            HelpDone req_id r_s -∗
            Ist st_src st_tgt =| n, E |={ ∅, E }=∗
            (Tid mtid stid -∗
            wsim fl_s fl_t Ist (E, E) g R_s R_t RR true false
              (st_src, k_s ()↑) (st_tgt, k_t))))
        true pt
          (st_src, SB.sandbox (msk_scp (HelpingOn.scopes mn) msk_true)
            (SModTr.trans sp (SB.sandbox msk_pure (jobs x))))
          (st_tgt, Ret ()))) -∗
    wsim fl_s fl_t Ist (E, E) g R_s R_t RR ps pt
      (st_src,
        x_ <- SB.sandbox (msk_scp (HelpingOn.scopes mn) msk_true)
          (SModTr.trans sp (HelpingOn.help mn jobs sp arg));; k_s x_)
      (st_tgt, k_t).
  Proof using Hist.
    iIntros (Hsp) "TID Tkn [%n SIM]".
    rewrite /HelpingOn.help Hsp.
    cForceS req_id. cForceS (stid, mtid, tt). cForcesS. iFrame. iSplit; eauto.
    cStepsS. destruct _q as [[stid1 mtid1] []]. iDestruct "ASM" as "[TID [_ ->]]".
    iMod ("SIM") as "[IST SIM]".
    iApply (wsim_helping_pend_try_run with "Tkn IST").
    appendRetS. appendRetT. cBind _ "SIM" as (sts1 stt1 rets []) "[[-> ->] [? SIM]]".
    iApply wsim_fold; iFrame.
    cStep; iFrame. iSplit; first auto.
    clear_st. iIntros (st_src st_tgt) "Tkn IST".
    iMod ("SIM" $! st_src st_tgt with "Tkn IST") as "SIM".
    cForcesS. iFrame. iSplit; eauto.
    cStepsS. iDestruct "ASM" as "[TID [_ ->]]". iApply ("SIM" with "[$]"); done.
  Qed. *)

  (* Lemma IstHelp_split (q : Qp) :
    (q < 1)%Qp →
    IstHelp Ist st_src st_tgt -∗
    (∃ reqmap, HelpAuth q reqmap ∗ (HelpAuth q reqmap -∗ IstHelp Ist st_src st_tgt)).
  Proof.
    iIntros (Hq) "[% [% [% [% [% [Help● IST]]]]]]".
    assert (Hr : (∃ r, 1 - q = Some r)%Qp).
    { destruct (1 - q)%Qp as [r'|] eqn : Hq'; first eauto.
      apply Qp.sub_None in Hq'. exfalso. apply (StrictOrder_Asymmetric _ q 1%Qp); eauto.
      apply Qp.le_lteq in Hq'; des; subst; eauto.
    }
    destruct Hr as [r Hr%Qp.sub_Some]; rewrite Hr {1}/HelpAuth.
    rewrite -dfrac_op_own.
    iExists reqmap; iDestruct "Help●" as "[$ H]".
    iIntros "H2"; iCombine "H" "H2" as "H"; rewrite comm -Hr; iFrame; iExists _; ss.
  Qed.

  Lemma IstHelp_done req_id job_id (reqmap : gmap nat help_state) (ret : SAny.t) :
    HelpPend req_id job_id -∗
    IstHelp Ist ((HelpingOn.v_reqs mn, reqmap↑) :: st_src) st_tgt ==∗
    HelpDone req_id ret ∗
    IstHelp Ist
      ((HelpingOn.v_reqs mn, (<[req_id := (Some ret, job_id)]> reqmap)↑) :: st_src) st_tgt.
  Proof.
    iIntros "Help [% [% [% [% [% [Help● IST]]]]]]".
    iMod (own_update_2 with "Help● Help") as "[Help● Help]".
    { eapply gmap_view_replace. instantiate (1:=(to_agree (Some ret, job_id))); done. }
    iMod (own_update with "Help") as "$".
    { eapply gmap_view_frag_persist. }
    iExists _, _, _, _; iModIntro; iSplit; first done.
    rewrite -fmap_insert; iFrame "Help●"; done.
  Qed.

  (* TODO : modify helping so that we do not see cput after job execution *)
  Lemma wsim_helping_try_run (req_id : nat) (parg : SAny.t) k_s k_t E1 E2 g img_t msk_t scp_t :
    HelpPend req_id parg -∗
    IstHelp Ist st_src st_tgt -∗
    (∀ (reqmap : gmap nat help_state) st_src0,
      HelpPend req_id parg -∗
      IstHelp Ist ((HelpingOn.v_reqs mn, reqmap↑) :: st_src0) st_tgt -∗
      wsim fl_s fl_t (IstHelp Ist) (E1, E2) g R_s R_t RR true pt
        ((HelpingOn.v_reqs mn, reqmap↑) :: st_src0,
          x_ <- SB.sandbox true wmask_all (HelpingOn.scopes mn) (SModTr.trans true sp
            (r <- Helping.trans (jobs parg);;
            (cput (HelpingOn.v_reqs mn) (<[req_id := (Some r, parg)]> reqmap));;;
            Ret (r)));;
          x_0 <- SB.sandbox true wmask_all (HelpingOn.scopes mn) (SModTr.trans true sp
            (𝒴;;; Ret (x_↑)));;
          x_1 <- (tau;; Ret x_0);;
          x_2 <- (SB.sandbox img_t msk_t scp_t (Ret x_1));; k_s x_2)
        (st_tgt, k_t)) -∗
    wsim fl_s fl_t (IstHelp Ist) (E1, E2) g R_s R_t RR ps pt
      (st_src,
        x_ <- SB.sandbox (msk_scp (HelpingOn.scopes mn) msk_true)
          (SModTr.trans sp (HelpingOn.help mn jobs sp arg));; k_s x_)
      (st_tgt, k_t).
  Proof.
    iIntros "Help IST K".
    iDestruct "IST" as "[% [% [% [% [[-> ->] [Help● IST]]]]]]".
    rewrite /HelpingOn.try_run.
    cStepsS. rename _q into reqmap.
    iCombine "Help●" "Help" gives %[v' [? [_ [WF [_ EQ]]]]]%gmap_view_both_dfrac_valid_discrete.
    apply lookup_fmap_Some in WF as [[ro parg'] [? Hlookup]]; clarify.
    rewrite Hlookup. apply Some_pair_included in EQ as [_ EQ].
    rewrite Some_included_total to_agree_included in EQ; inv EQ; clarify.
    iApply ("K" $! reqmap st_src1 with "Help"). iFrame. eauto.
  Qed. *)
End help.
