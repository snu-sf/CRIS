From CRIS.common Require Import CRIS.
From CRIS.scheduler Require Import SchHeader SchI.
From iris Require Export frac_auth dfrac_agree gmap_view.

Definition joinRA `{α : GAT.t} :=
  gmap_viewUR nat (agreeR (SAny.t -d> SAny.t -d> leibnizO {n & GTerm.t n}))%type.
Definition newtidRA := gmap_viewUR nat (agreeR nat).

Class schGpreS `{!crisG Γ Σ α β τ _S _I} := {
  #[local] inG_join :: inG joinRA Σ;
  #[local] inG_tid :: inG newtidRA Γ;
}.
Class schGS `{!crisG Γ Σ α β τ _S _I} := {
  #[local] schGS_schGpreS :: schGpreS;
  join_name : gname;
  tid_name : gname
}.

Definition newschΓ : HRA := #[newtidRA].
Definition newschΣ `{Γ : HRA, α : GAT.t} : GRA := #[joinRA].
Global Instance subG_schGpreS `{!crisG Γ Σ α β τ _S _I} :
  subG newschΓ Γ → subG newschΣ Σ → schGpreS.
Proof using. solve_inG. Defined.

Local Existing Instances schGS_schGpreS inG_join inG_tid.

Section SchRA.
  Context `{!crisG Γ Σ α β τ _S _I, !schGS}.

  (* Join-related predicates *)
  Definition JoinFrag dq mtid postS : iProp Σ :=
    own join_name (gmap_view_frag mtid (DfracOwn (dq)%Qp) (to_agree postS) : joinRA).
  Definition JoinHandle mtid postS : iProp Σ :=
    JoinFrag (1/4) mtid postS.
  Definition JoinAuth m : iProp Σ :=
    own join_name (gmap_view_auth (DfracOwn 1) m : joinRA).

  (* Thread-id-related predicates *)
  Definition TidFrag (mtid stid : nat) : iProp Σ :=
    own tid_name (gmap_view_frag mtid (DfracOwn 1) (to_agree stid)).
  Definition Tid (mtid stid : nat) : iProp Σ :=
    own tid_name (gmap_view_frag mtid (DfracOwn 1) (to_agree stid)) ∗
    TID stid ∗ YIELD stid.
  Definition TidAuth (m : gmap nat nat) : iProp Σ :=
    own tid_name (gmap_view_auth (DfracOwn 1) (to_agree <$> m)).

  Definition PYIP (x: nat * nat) : iProp Σ :=
    own tid_name (gmap_view_frag x.1 (DfracOwn 1) (to_agree x.2)).

  Lemma Tid_Auth_Tid (m : gmap nat nat) (mtid stid : nat) :
    TidAuth m ∗ TidFrag mtid stid -∗
    ⌜m !! mtid = Some stid⌝.
  Proof.
    iIntros "[A F]"; iCombine "A" "F" gives %WF%gmap_view_both_dfrac_valid_discrete_total.
    destruct WF as [? [_ [_ [Hlookup [_ Hin]]]]]; rewrite lookup_fmap in Hlookup.
    destruct (m !! mtid) as [stid2|]; ss; inv Hlookup.
    eapply to_agree_included in Hin; inv Hin; done.
  Qed.
End SchRA.

Definition fspec_sch `{!crisG Γ Σ α β τ _S _I, !schGS}
    (E : coPset) (fsp : fspec) : fspec :=
  fspec_winv E
    (fspec_mk
      (λ '(stid, mtid, x) varg arg, Tid mtid stid ∗ precond fsp x varg arg)
      (λ '(stid, mtid, x) vret ret, Tid mtid stid ∗ postcond fsp x vret ret))%I.

Module SchA. Section SchA.
  Context `{!crisG Γ Σ α β τ _S _I, !schGS}.
  Context (sp_user : specmap).

  Definition fspec_spawnable fsp
      (pre : SAny.t → SAny.t → iProp Σ)
      (postS : SAny.t → SAny.t → leibnizO {n & GTerm.t n}) : iProp Σ :=
    fspec_imply fsp
      (fspec_sch ⊤
        (fspec_mk (meta:=unit)
          (λ _ varg arg,
            ∃ (sarg svarg : SAny.t), ⌜varg = svarg↑ ∧ arg = sarg↑⌝ ∗ pre svarg sarg)
          (λ _ vret ret,
            ∃ (sret svret : SAny.t), ⌜vret = svret↑ ∧ ret = sret↑⌝ ∗
              interp_cond (postS svret sret))))%I.

  Definition fn_spawnable fn
      (pre : SAny.t -d> SAny.t -d> iProp Σ)
      (postS : SAny.t -d> SAny.t -d> leibnizO {n & GTerm.t n}) : iProp Σ :=
    ∃ fsp, ⌜sp_user.1 !! (funid fn) = Some fsp⌝ ∗ fspec_spawnable fsp pre postS.

  Lemma fspec_sch_spawnable E1 E2 (fsp1 fsp2 : fspec) :
    E1 ⊆ E2 →
    fspec_imply fsp1 fsp2 -∗ fspec_imply (fspec_sch E1 fsp1) (fspec_sch E2 fsp2).
  Proof.
    iIntros "% S %P2 %Q2 [%x2 [-> ->]] %varg %arg Pre". destruct x2 as [[stid mtid] x2].
    unfoldPrePost. iDestruct "Pre" as "[W [TID Pre]]".
    iPoseProof ("S" with "[] Pre") as "> [%P1 [%Q1 [[%x1 [-> ->]] [S1 S2]]]]"; first (iPureIntro).
    { exists x2; split; ss. }
    iExists _, _; iModIntro; iSplit; first iPureIntro.
    { exists (stid, mtid, x1); split; ss. }
    replace E2 with ((E2 ∖ E1) ∪ E1); last (rewrite difference_union_L //; set_solver).
    iPoseProof (winv_split with "W") as "[W $]"; [set_solver|set_solver|]. iFrame "S1 TID".
    iIntros (??) "[W2 [TID Post]]".
    iFrame "TID". iPoseProof ("S2" with "Post") as "> $".
    iMod (winv_merge with "[-]") as "[$ ?]"; iFrame; auto.
  Qed.

  Definition inner_spawn_spec : fspec := 
    fspec_mk
      (λ (_ : unit) varg arg,
        ∃ stid pre postS (fvarg farg : SAny.t) (fn : string) (mtid : nat),
          ⌜varg = (fn, fvarg)↑ ∧ arg = (fn, farg)↑⌝ ∗
          fn_spawnable fn pre postS ∗
          winv (⊤, ⊤) ∗ Tid mtid stid ∗
          pre fvarg farg ∗
          JoinFrag (3/4)%Qp mtid postS)%I
      (λ _ vret _, ∃ (vr : SAny.t), ⌜vret = vr↑⌝ ∗ False)%I.

  (* TODO : make spawn_spec incremental *)
  Definition spawn_spec : fspec :=
    fspec_mk
      (λ '(pre, postS) varg arg,
        ∃ fvarg farg fn,
          ⌜varg = ((fn, fvarg) : string * SAny.t)↑ ∧ arg = ((fn, farg) : string * SAny.t)↑⌝ ∗
          fn_spawnable fn pre postS ∗ pre fvarg farg)%I
      (λ '(pre, postS) vret ret,
        ∃ tid, ⌜vret = tid↑ ∧ ret = tid↑⌝ ∗ JoinHandle tid postS)%I.

  Definition yield_spec (E : coPset) : fspec :=
    fspec_sch E
      (fspec_mk
        (λ (_ : ()) varg arg, ⌜arg = varg ∧ varg = tt↑⌝)
        (λ _ vret ret, ⌜ret = vret ∧ vret = tt↑⌝))%I.

  Definition join_spec (E : coPset) : fspec :=
    fspec_sch E
      (fspec_mk
        (λ postS varg arg,
          ∃ tid, ⌜arg = tid↑ ∧ varg = tid↑⌝ ∗ JoinHandle tid postS)
        (λ postS vret ret, 
          (∃ vsret sret, ⌜vret = (Some vsret)↑ ∧ ret = (Some sret)↑⌝ ∗
          interp_cond (postS vsret sret))))%I.

  Definition sp (E : coPset) : specmap :=
    {[fid SchHdr._spawn  @ inner_spawn_spec;
      fid SchHdr.spawn   @ spawn_spec;
      fid SchHdr.yield   @ yield_spec E;
      fid SchHdr.join    @ join_spec E
    ]}.

  (* Module definition *)
  Definition scopes : list string := [SCH].

  Definition v_ths := SCH ↯ "ths".
  Definition v_tid := SCH ↯ "tid".

  Definition inner_spawn : string * SAny.t → itree crisE unit :=
    λ '(fn, arg),
      rv <- ccallN (fnsig fn (fntyp SAny.t SAny.t)) arg;; (* call the user function *)
      'ths : thpool <- cgetN v_ths;;
      'tid : nat <- cgetN v_tid;;
      match ths !! tid with
      | Some (stid, _) =>
          let ths2 := <[tid := (stid, Some rv)]> ths in
          cput v_ths ths2;;; (* save the return value *)
          Sch.terminate
      | _ => triggerNB
      end.

  Definition spawn : string * SAny.t → itree crisE nat :=
    λ '(fn, arg),
      'ths : thpool <- cgetN v_ths;;
      let new_tid : nat := length ths in
      new_stid <- trigger (Spawn SchHdr._spawn.1 (fn, arg)↑);;
      cput v_ths (ths ++ [(new_stid, None)]);;;
      Ret (length ths).

  Definition yield : unit → itree crisE unit :=
    λ _,
      (* sanity check *)
      'ths : thpool <- cgetN v_ths;;
      tid <- trigger GetTid;;
      'mtid : nat <- cgetN v_tid;;
      match ths !! mtid with
      | Some (stid, _) => if (decide (stid = tid)) then Ret () else triggerNB
      | None => triggerNB
      end;;;
      '(mtid, stid) : _ <- choose_index ths;;
      cput v_tid mtid;;;
      trigger (Yield stid).

  Definition join : nat → itree crisE (option SAny.t) :=
    λ tid,
      (* possibly infinite loop while waiting for the thread to terminate *)
      orv <- (iterC (λ _,
        'ths : thpool <- cgetN v_ths;;
        match ths !! tid with
        | None => Ret (inr None)
        | Some (_, Some rv) => Ret (inr (Some rv))
        | Some (_, None) => ccallN SchHdr.yield tt;;; Ret (inl tt)
        end
      ) tt);;
      Ret orv.

  Definition fnsems (E : coPset) : fnsemmap :=
    {[fid SchHdr._spawn #
        (msk_scp scopes msk_true, (fsp_some (inner_spawn_spec), cfunN SchHdr._spawn inner_spawn));
      fid SchHdr.spawn #
        (msk_scp scopes msk_true, (fsp_some (spawn_spec), cfunN SchHdr.spawn spawn));
      fid SchHdr.yield #
        (msk_scp scopes msk_true, (fsp_some (yield_spec E), cfunN SchHdr.yield yield));
      fid SchHdr.join #
        (msk_scp scopes msk_true, (fsp_some (join_spec E), cfunN SchHdr.join join))
    ]}.

  Program Definition smod (E : coPset) : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems E;
    SMod.initial_st := SchI.smod.(SMod.initial_st);
  |}.
  Solve All Obligations with mod_tac.

  Definition init_cond : iProp Σ :=
    TidAuth {[0 := 0]} ∗
    JoinAuth {[0 := to_agree (λ _ _ : SAny.t, existT 0 emp%SAT)]}.

  (* Scheduler module itself has fixed namespace to ⊤, with specmap namespaces variable *)
  Definition t sp : Mod.t := SMod.to_mod sp (smod ⊤).
End SchA. End SchA.

Lemma sch_alloc `{!crisG Γ Σ α β τ Hsub Hinv, !schGpreS} :
  ⊢ o=> ∃ (_ : schGS), SchA.init_cond ∗ TidFrag 0 0.
Proof.
  iMod (own_alloc
    (gmap_view_auth (DfracOwn 1) {[0 := to_agree 0]} ⋅
      gmap_view_frag 0 (DfracOwn 1) (to_agree 0))) as "[%γt T]".
  { apply gmap_view_both_dfrac_valid_discrete; esplits; ss. split; ss. }
  iMod (own_alloc
    (gmap_view_auth (DfracOwn 1) {[0 := to_agree (λ _ _ : SAny.t, existT 0 emp%SAT)]} : joinRA))
  as "[%γj J]".
  { apply gmap_view_auth_valid. }
  pose (Build_schGS _ _ _ _ _ _ _ _ _ γj γt) as Hsch.
  rewrite own_op; iExists Hsch; iDestruct "T" as "[$ $]"; iFrame.
  done.
Qed.

Section Sch.
  Context `{!crisG Γ Σ α β τ Hsub Hinv, !stateGS Σ, !schGS}.

  Definition spawn_f (fn : string) (arg : SAny.t) (fsp : fspec) : itree crisE nat :=
    (* '(mtid, stid) : _ <- trigger (Take (nat * nat));;
    trigger (Assume (winv (⊤, ⊤) ∗ Tid mtid stid));;;
     *)
    R <- trigger (Choose (_));;
    trigger (Guarantee (∀ mtid stid, winv (⊤, ⊤) -∗ Tid mtid stid -∗
      ∃ (PQ : FSpec fsp), PQ.(Precond) arg↑ arg↑ ∗
      ∀ ret vret, (PQ.(Postcond) ret vret) -∗
        ∃ sret svret, ⌜ret = sret↑ ∧ vret = svret↑⌝ ∗
          winv (⊤, ⊤) ∗ Tid mtid stid ∗ interp_cond (R sret svret)));;;
    'tid : nat <- ccallU SchHdr.spawn (fn, arg);;
    trigger (Assume (JoinHandle tid R));;; Ret tid.

  Lemma wsim_spawn_f_src
      (fn : string) (arg : SAny.t) (fsp : fspec) (Q : SAny.t → SAny.t → leibnizO {n & GTerm.t n})
      fl_s fl_t (Ist : iProp Σ) Es g {R_s R_t} RR p_s p_t
      msk_s sp_s k_s
      msk_t sp_t k_t :
    sp_s.1 !! (fid SchHdr.spawn) = None →
    sp_t.1 !! (fid SchHdr.spawn) = None →
    msk_t _ (subevent _ (Call "Sch.spawn" (fn, arg)↑)) = true →
    Ist -∗
    (∀ mtid stid, winv (⊤, ⊤) -∗ Tid mtid stid -∗
      ∃ x, (precond fsp) x arg↑ arg↑ ∗ ∀ (ret vret : Any.t), (postcond fsp) x ret vret -∗
        ∃ (sret svret : SAny.t), ⌜ret = sret↑ ∧ vret = svret↑⌝ ∗
          winv (⊤, ⊤) ∗ Tid mtid stid ∗ interp_cond (Q sret svret)) -∗
    (∀ tid, Ist -∗ JoinHandle tid Q -∗
      wsim fl_s fl_t Ist (Es, Es) g R_s R_t RR true true
        (k_s tid) (k_t tid)) -∗
    wsim fl_s fl_t Ist (Es, Es) g R_s R_t RR p_s p_t
      (SB.sandbox msk_s (SModTr.trans sp_s (spawn_f fn arg fsp)) >>= k_s)
      (SB.sandbox msk_t (SModTr.trans sp_t (Sch.spawn (fn, arg))) >>= k_t).
  Proof.
    iIntros "%Hsp_s %Hsp_t %Hmsk_t IST Hx K". rewrite /spawn_f /Sch.spawn.
    cStepsT. rewrite Hsp_t. cStepsT. rewrite Hmsk_t /=. cStepsT.
    cStepsS. cForceS Q. cStepsS.
    cForceS; iSplitL "Hx".
    { iIntros (??) "W T"; iPoseProof ("Hx" with "[$] [$]") as "[%x [Hx Hx2]]".
      iExists (FSpec_mk _ _ (fspec_to_rel_satisfy fsp x)); iFrame.
    }
    cStepsS; simpl_sp; cStepsS; ss.
    case_match; cStepsS; ss.
    cCall "IST" as (ret) "IST". destruct (Any.downcast); cStepsS; ss.
    case_match; cStepsS; ss. cStepsT. iApply ("K" with "[$] [$]").
  Qed.

  Lemma wsim_spawn_f_tgt
      (fn : string) (arg : SAny.t) (fsp : fspec) (sp_user : specmap)
      fl_s fl_t (Ist : iProp Σ) Es g {R_s R_t} RR p_s p_t
      msk_s sp_s k_s
      msk_t sp_t k_t :
    sp_s.1 !! (fid SchHdr.spawn) = fsp_some (SchA.spawn_spec sp_user) →
    sp_t.1 !! (fid SchHdr.spawn) = None →
    sp_user.1 !! (funid fn) = fsp_some fsp →
    msk_t _ (subevent _ (Call "Sch.spawn" (fn, arg)↑)) = true →
    img_msk msk_t →
    Ist -∗
    (∀ tid, Ist -∗
      wsim fl_s fl_t Ist (Es, Es) g R_s R_t RR true true
        (k_s tid) (k_t tid)) -∗
    wsim fl_s fl_t Ist (Es, Es) g R_s R_t RR p_s p_t
      (SB.sandbox msk_s (SModTr.trans sp_s (Sch.spawn (fn, arg))) >>= k_s)
      (SB.sandbox msk_t (SModTr.trans sp_t (spawn_f fn arg fsp)) >>= k_t).
  Proof.
    iIntros "%Hsp_s %Hsp_t %Hsp_user %Hmsk_t %Himg IST K".
    destruct Himg as [Ht [? [Ha [? ?]]]].
    rewrite /spawn_f /Sch.spawn.
    cStepsT. cStepsT. cStepsT. rewrite Hsp_t /=.
    cStepsT. rewrite Hmsk_t /=. cStepsT. cStepsS. rewrite Hsp_s. cStepsS.
    cForceS (_, _q).
    cForcesS.
    iSplitL "GRT".
    { iExists arg, arg, _; iSplitR; first eauto.
      iSplitR; cycle 1.
      { instantiate (1:=λ x y, (⌜x = y⌝ ∗ _)%I). s. iSplit; first auto. iApply "GRT". }
      iExists _; iSplit; first eauto.
      iIntros (??) "[%x [-> ->]] % % [W Pre]"; destruct x as [[mtid stid] []].
      unfoldPrePost. iDestruct "Pre" as "[TID [% [% [[-> ->] [-> Pre]]]]]".
      iPoseProof ("Pre" with "W TID") as "[% [Pre Post]]".
      destruct PQ as [P Q x]; iExists P, Q; iSplitR; eauto.
      ss; iFrame. iIntros "!> %ret %vret Q".
      iPoseProof ("Post" with "Q") as "[% [% [% [$ [$ $]]]]]". auto.
    }
    cStepsS. case_match; cStepsS; ss. cCall "IST" as (tid) "IST".
    case_match; cStepsS; ss.
    case_match; cStepsS; ss. iDestruct "ASM" as "[% [[-> ->] J]]".
    cStepsS; cStepsT. rewrite Ha. cForcesT; iFrame "J". cStepsT.
    iApply "K"; auto.
  Qed.
End Sch.
Notation "'𝒮@{' fn ',' arg ',' fsp '}'" := (spawn_f fn arg fsp) (format "'𝒮@{' fn ','  arg ','  fsp '}'").
