From CRIS.modules Require Export SModTr.
From CRIS.iris_system Require Export atomic.
From CRIS.scheduler Require Import SchTactics.

Program Global Instance fspec_winv `{!crisG Γ Σ α β τ _S _I} P E
  : WP (winv (E, E) ∗ P) := {| WP_space := E; WP_remainder := P |}.
Next Obligation. intros; iSplit; iIntros "[$ $]". Qed.

(* wrapper for atomic_fspec, similar to HoareFun in SModTr.v,
   but delivers the meta-variable to the body *)
Definition atomic_fun `{!crisG Γ Σ α β τ Hsub Hinv} {X X2 : Type}
    (P : namespace → X → iProp Σ)
    (body : namespace → X → itree crisE (Any.t * X2))
    (Q : namespace → X → X2 → Any.t → iProp Σ)
    : itree crisE Any.t :=
  '(N, x) : _ <- trigger (Take (namespace * X));;
  trigger (Assume (winv (↑N, ↑N) ∗ P N x));;; (* private precondition *)
  '(ret, x2) : _ <- body N x;;
  trigger (Guarantee (winv (↑N, ↑N) ∗ Q N x x2 ret));;; Ret ret. (* private postcondition *)
Typeclasses Opaque atomic_fun.

Notation "'{{{' ∀∀ x ',' P '}}}' body '{{{' ∀∀ x2 ',' 'RET' ret ',' Q '}}}' '@' N" :=
  (atomic_fun (λ N x, P) (λ N x, body) (λ N x x2 ret, Q))%I
  (at level 20, N, P, body, Q at level 200, x binder, x2 binder, ret binder,
   format "'{{{'  ∀∀  x ,  '/' P '}}}'  '/' body  '/' '{{{'  ∀∀  x2 ,  '/' 'RET'  ret ,  '/' Q  '}}}' '@'  N").
Notation "'{{{' P '}}}' body '{{{' ∀∀ x2 ',' 'RET' ret ',' Q '}}}' '@' N" :=
  (atomic_fun (λ N _, P) (λ N _, body) (λ N _ x2 ret, Q) )%I
  (at level 20, N, P, body, Q at level 200, x2 binder, ret binder,
   format "'{{{' P '}}}'  '/' body  '/' '{{{'  ∀∀  x2 ,  '/' 'RET'  ret ,  '/' Q  '}}}' '@'  N").
Notation "'{{{' ∀∀ x ',' P '}}}' body '{{{' 'RET' ret ',' Q '}}}' '@' N" :=
  (atomic_fun (λ N x, P) (λ N x, body) (λ N x _ ret, Q))%I
  (at level 20, N, P, body, Q at level 200, x binder, ret binder,
   format "'{{{'  ∀∀  x ,  '/' P '}}}'  '/' body  '/' '{{{'  'RET'  ret ,  '/' Q  '}}}' '@'  N").
Notation "'{{{' ∀∀ x ',' P '}}}' body '{{{' ∀∀ x2 ',' Q '}}}' '@' N" :=
  (atomic_fun (λ N x, P) (λ N x, body) (λ N x x2 _, Q))%I
  (at level 20, N, P, body, Q at level 200, x binder, x2 binder,
   format "'{{{'  ∀∀  x ,  '/' P '}}}'  '/' body  '/' '{{{'  ∀∀  x2 ,  '/' Q  '}}}' '@'  N").
Notation "'{{{' ∀∀ x ',' P '}}}' body '{{{' Q '}}}' '@' N" :=
  (atomic_fun (λ N x, P) (λ N x, body) (λ N x _ _, Q))%I
  (at level 20, N, P, body, Q at level 200, x binder,
   format "'{{{'  ∀∀  x ,  '/' P '}}}'  '/' body  '/' '{{{'  Q  '}}}' '@'  N").
Notation "'{{{' P '}}}' body '{{{' ∀∀ x2 ',' Q '}}}' '@' N" :=
  (atomic_fun (λ N _, P) (λ N _, body) (λ N _ x2 _, Q))%I
  (at level 20, N, P, body, Q at level 200, x2 binder,
   format "'{{{' P '}}}'  '/' body  '/' '{{{'  ∀∀  x2 ,  '/' Q  '}}}' '@'  N").
Notation "'{{{' P '}}}' body '{{{' 'RET' ret ',' Q '}}}' '@' N" :=
  (atomic_fun (λ N _, P) (λ N _, body) (λ N _ _ ret, Q) )%I
  (at level 20, N, P, body, Q at level 200, ret binder,
   format "'{{{' P '}}}'  '/' body  '/' '{{{'  'RET'  ret ,  '/' Q  '}}}' '@'  N").
Notation "'{{{' P '}}}' body '{{{' Q '}}}' '@' N" :=
  (atomic_fun (λ N _, P) (λ N _, body) (λ N _ _ _, Q) )%I
  (at level 20, N, P, body, Q at level 200,
   format "'{{{' P '}}}'  '/' body  '/' '{{{'  Q  '}}}' '@'  N").

(* core atomic update point, which has the 'abort' facility as in Iris *)
Definition atomic_try `{Σ : GRA} {X : Type}
    (αP : X → iProp Σ)
    (αQ : X → Any.t → iProp Σ)
    : itree crisE (() + Any.t * X) :=
  x2 <- trigger (Take X);;
  trigger (Assume (αP x2));;; (* public precondition *)
  ret <- trigger (Choose (() + Any.t));;
  match ret with
  | inl _ =>
    trigger (Guarantee (αP x2));;; Ret (inl tt) (* public precondition - abort *)
  | inr ret =>
    trigger (Guarantee (αQ x2 ret));;; Ret (inr (ret, x2)) (* public postcondition *)
  end.

Definition atomic_update_sem `{!crisG Γ Σ α β τ Hinv Hsub} {X2 : Type}
    (N : namespace)
    (αP : X2 → iProp Σ)
    (αQ : X2 → Any.t → iProp Σ)
    : itree crisE (Any.t * X2) :=
  yield_namespace_iter (Some N) (λ _, atomic_try αP αQ) tt.

Notation "'<<{' ∀∀ x , αP , ∃∃ ret , αQ '}>>' @ N" :=
  (atomic_update_sem N (λ x, αP) (λ x ret, αQ))
  (at level 20, αP, αQ at level 200, x binder, ret binder).
Notation "'<<{' ∀∀ x , αP , αQ '}>>' @ N" :=
  (atomic_update_sem N (λ x, αP) (λ x _, αQ))
  (at level 20, αP, αQ at level 200, x binder).
Notation "'<<{' αP , ∃∃ ret , αQ '}>>' @ N" :=
  (atomic_update_sem N (λ _, αP) (λ _ ret, αQ))
  (at level 20, αP, αQ at level 200, ret binder).
Notation "'<<{' αP , αQ '}>>' @ N" :=
  (atomic_update_sem N (λ _, αP) (λ _ _, αQ))
  (at level 20, αP, αQ at level 200).

Lemma unfold_atomic_update_sem `{!crisG Γ Σ α β τ Hinv Hsub} {X2 : Type}
    (N : namespace)
    (αP : X2 → iProp Σ)
    (αQ : X2 → Any.t → iProp Σ) :
  atomic_update_sem N αP αQ =
    𝒴@{Some N};;;
    x2 <- trigger (Take X2);;
    trigger (Assume (αP x2));;;
    ret <- trigger (Choose (() + Any.t));;
    match ret with
    | inl _ => trigger (Guarantee (αP x2));;; tau;; atomic_update_sem N αP αQ
    | inr ret => trigger (Guarantee (αQ x2 ret));;; 𝒴@{Some N};;; Ret (ret, x2)
    end.
Proof.
  rewrite {1}/atomic_update_sem unfold_yield_namespace_iter /atomic_try; grind. case_match; grind.
Qed.

Ltac aUnfoldS :=
  replace_s; [
    match goal with
    | |- context[iterC ?body ?arg] => 
      rewrite {1}(unfold_iterC body arg); reflexivity
    | |- context[yield_iter ?body ?arg] =>
      rewrite {1}(unfold_yield_iter body arg); reflexivity
    | |- context[yield_namespace_iter ?No ?body ?arg] => 
      rewrite {1}(unfold_yield_namespace_iter No body arg); reflexivity
    | |- context[ITree.iter ?body ?arg] =>
      rewrite {1}(unfold_iter body arg); reflexivity
    | |- context[atomic_update_sem ?αP ?αQ] =>
      rewrite {1}(unfold_atomic_update_sem αP αQ); reflexivity
    end
  |].

Ltac aUnfoldT :=
  replace_t; [
    match goal with
    | |- context[iterC ?body ?arg] => 
      rewrite {1}(unfold_iterC body arg); reflexivity
    | |- context[yield_iter ?body ?arg] =>
      rewrite {1}(unfold_yield_iter body arg); reflexivity
    | |- context[yield_namespace_iter ?No ?body ?arg] => 
      rewrite {1}(unfold_yield_namespace_iter No body arg); reflexivity
    | |- context[ITree.iter ?body ?arg] =>
      rewrite {1}(unfold_iter body arg); reflexivity
    | |- context[atomic_update_sem ?αP ?αQ] =>
      rewrite {1}(unfold_atomic_update_sem αP αQ); reflexivity
    end
  |].

Lemma atomic_fun_src `{!crisG Γ Σ α β τ Hinv Hsub, !stateGS Σ}
    {X X2 : Type}
    (P : namespace → X → iProp Σ)
    (body : _ → _ → itree crisE (Any.t * X2))
    (Q : namespace → X → X2 → Any.t → iProp Σ)
    (fls flt : gmap fname (option fbody))
    (Ist : iProp Σ)
    (E1 E2 : coPset)
    g R_t RR ps pt
    (msk_s : emask) (sp_s : specmap) itt :
  (∀ N x,
    P N x -∗
    wsim fls flt Ist (E1 ∪ ↑N, E2 ∪ ↑N) g _ R_t
      (λ rets rett,
        o=> winv (E1 ∪ ↑N, E2 ∪ ↑N) ∗
          Q N x rets.2 rets.1 ∗ RR rets.1 rett)
      true pt
      (⇓sbox(msk_s) (⇓smod(sp_s) (body N x))) itt) -∗
  wsim fls flt Ist (E1, E2) g Any.t R_t RR ps pt
    (⇓sbox(msk_s) (⇓smod(sp_s)
      ({{{ ∀∀ x, P N x }}} body N x
       {{{ ∀∀ x2, RET ret, Q N x x2 ret }}} @ N)))
    itt.
Proof.
  iIntros "SIM".
  rewrite /atomic_fun.
  cNormS. case_match; cStepsS; ss. case_match; cStepsS; ss.
  cStepsS; case_match; cStepsS; ss.
  iPoseProof ("SIM" with "ASM") as "SIM".
  appendRetT. wbind _ "SIM" as ([ret_s x2_s] ret_t) ">[W [Q RR]]".
  iApply wsim_fold; iFrame. cForceS. iFrame.
  cStep; iFrame.
Qed.

Lemma atomic_fun_tgt `{!crisG Γ Σ α β τ Hinv Hsub, !stateGS Σ}
    {X X2 : Type}
    (x_t : X)
    (N : namespace)
    (P : namespace → X → iProp Σ)
    (body : namespace → X → itree crisE (Any.t * X2))
    (Q : namespace → X → X2 → Any.t → iProp Σ)
    (fls flt : gmap fname (option fbody))
    (Ist : iProp Σ)
    (E : coPset)
    g R_s R_t RR ps pt
    (its : itree crisE R_s)
    (msk_t : emask) (sp_t : specmap) ktr_t :
  (∀ X, msk_t _ (subevent _ (Take X))) →
  (∀ P, msk_t _ (subevent _ (Assume P))) →
  ↑N ⊆ E →
  P N x_t -∗
  wsim fls flt Ist (E∖↑N, E∖↑N) g R_s _ RR ps true
    its
    ('(ret_t, x2_t) : _ <- ⇓sbox(msk_t) (⇓smod(sp_t) (body N x_t));;
      trigger (Guarantee (winv (↑N, ↑N) ∗ Q N x_t x2_t ret_t));;;
      ktr_t ret_t) -∗
  wsim fls flt Ist (E, E) g R_s R_t RR ps pt
    its
    (⇓sbox(msk_t) (⇓smod(sp_t)
      (({{{ ∀∀ x, P N x }}} body N x
        {{{ ∀∀ x2, RET ret, Q N x x2 ret }}} @ N))) >>= ktr_t).
Proof.
  iIntros (Ht Ha) "%HN P Sim".
  rewrite /atomic_fun.
  cNormT. rewrite Ht /=. cForceT (N, x_t).
  rewrite Ha. cStepsT. cForceT; iFrame "P".
  replace_t; [|iFrame].
  symmetry; etrans; first hnorm_itr; grind.
  symmetry; etrans; first hnorm_itr; grind.
  all: try rewrite orb_true_r.
  rewrite SRed.bind SRed.ag SRed.ret.
  rewrite SBRed.bind SBRed.vis /= orb_true_r !SBRed.ret.
  rewrite !trigger_vis !bind_bind !bind_vis.
  repeat f_equal; extensionalities.
  rewrite SBRed.ret !bind_ret_l.
  reflexivity.
Qed.

Lemma lais_triple_tgt_sem
    `{!crisG Γ Σ α β τ Hinv Hsub, !stateGS Σ} {X X2 : Type}
    (N : namespace)
    (P : namespace → X → iProp Σ)
    (body : namespace → X → itree crisE (Any.t * X2))
    (Q : namespace → X → X2 → Any.t → iProp Σ)
    (fls flt : gmap fname (option fbody))
    (Ist : iProp Σ)
    (E : coPset)
    g R_s RR ps pt
    (its : itree crisE R_s)
    (msk_t : emask) (sp_t : specmap) :
  (∀ X, msk_t _ (subevent _ (Take X))) →
  (∀ P, msk_t _ (subevent _ (Assume P))) →
  ↑N ⊆ E →
  (∃ x_t, P N x_t ∗
    wsim fls flt Ist (E∖↑N, E∖↑N) g R_s (Any.t * X2)
      (λ ret_s ret_t, Q N x_t ret_t.2 ret_t.1 -∗ RR ret_s ret_t.1)
      ps true
      its
      (⇓sbox(msk_t) (⇓smod(sp_t) (body N x_t)))) -∗
  wsim fls flt Ist (E, E) g R_s Any.t RR ps pt
    its
    (⇓sbox(msk_t) (⇓smod(sp_t) (atomic_fun P body Q))).
Proof.
  iIntros (Ht Ha HN) "[%x_t [P Sim]]".
  appendRetT.
  iApply (atomic_fun_tgt with "P [-]"); eauto.
  appendRetS.
  iApply (wsim_bind with "[Sim]").
  iSplitL "Sim"; first iFrame.
  iIntros (ret_src [ret_t x2_t]) "HQ".
  cStepsT.
  iSpecialize ("HQ" with "GRT").
  cStep; iFrame.
Qed.

Lemma atomic_i_funsem
    `{!crisG Γ Σ α β τ Hinv Hsub, !stateGS Σ, !schGS}
    {X X2 : Type}
    (P : namespace → X → iProp Σ)
    (αP : namespace → X → X2 → iProp Σ)
    (αQ : namespace → X → X2 → Any.t → iProp Σ)
    (Q : namespace → X → X2 → Any.t → iProp Σ)
    (N : namespace)
    (x_t : X)
    (fl_s fl_t : gmap fname (option (Any.t → itree crisE Any.t)))
    (Ist : iProp Σ)
    (ps pt : bool)
    (E : coPset) (mtid stid : nat)
    g {R_s R_t} RR
    (ktr_s : _ → itree crisE R_s) (ktr_t : _ → itree crisE R_t)
    (msk_s msk_t : emask)
    (sp_s sp_t : specmap) :
  sp_s.1 !! fid SchHdr.yield = fsp_some (SchA.yield_spec E) →
  sp_t.1 !! fid SchHdr.yield = None →
  img_msk msk_t →
  (msk_t _ (subevent _ (Call SchHdr.yield.1 ()↑))) →
  ↑N ⊆ E →
  Ist ∗
  Tid mtid stid ∗
  P N x_t ∗
  (∃ n,
    AU <{ ∃∃ (x2_t : X2), αP N x_t x2_t }>
      @ n, E ∖ ↑N, E ∖ ↑N, ∅
      <{ ∀∀ ret, αQ N x_t x2_t ret,
        COMM
          Ist -∗
          Tid mtid stid -∗
          Q N x_t x2_t ret -∗
          wsim fl_s fl_t Ist (E, E) g R_s R_t RR true true
            (⇓sbox(msk_s) (⇓smod(sp_s) 𝒴) >>= ktr_s)
            (ktr_t ret) }>)%I ⊢
  wsim fl_s fl_t Ist (E, E) g R_s R_t RR ps pt
    (⇓sbox(msk_s) (⇓smod(sp_s) 𝒴) >>= ktr_s)
    (⇓sbox(msk_t) (⇓smod(sp_t) ((
      {{{ ∀∀ x, P N x }}}
        <<{ ∀∀ x2, αP N x x2, ∃∃ ret, αQ N x x2 ret }>> @ N
      {{{ ∀∀ x2, RET ret, Q N x x2 ret }}} @ N))) >>= ktr_t).
Proof using.
  iIntros (? ? [Ht [Hc [Ha [? ?]]]] ? ?) "[IST [TID [Pre [%n AU]]]]".
  iApply (atomic_fun_tgt with "[Pre]"); eauto with iFrame.
  iApply wsim_reset. cCoind CIH g2 Hg2 with n.
  iIntros "[TID [IST AU]]".
  rewrite /atomic_update_sem unfold_yield_namespace_iter. cNormT.
  iApply (wsim_yield_namespace_i_N); ss; iFrame.
  iIntros "IST TID".
  rewrite /atomic_try. cStepsT. rewrite Ht /=.
  iMod ("AU") as "AU"; iMod ("AU" $! tt with "[$]") as "[%x2_t [Pre AU]]".
  cForceT x2_t. rewrite Ha /=.
  cForceT; iFrame "Pre". cStepsT. rewrite ?orb_true_r. cStepsT. case_match.
  { cNormT. try rewrite orb_true_r. cStepsT.
    iMod ("AU" with "GRT") as "[_ AU]". cByCoind CIH. iFrame. }
  cStepsT. try rewrite orb_true_r. cStepsT.
  iMod ("AU" with "GRT") as "[% [_ > AU]]".
  iApply (wsim_yield_namespace_i_N); ss; iFrame.
  iIntros "IST TID".
  cStepsT. iApply wsim_mono_knowledge; last first.
  { iApply ("AU" with "IST TID GRT"). }
  { iIntros (???????) "?"; iApply Hg2; done. }
Qed.

Lemma atomic_i_sem
    `{!crisG Γ Σ α β τ Hinv Hsub, !stateGS Σ, !schGS} {X : Type}
    (αP : X → iProp Σ)
    (αQ : X → Any.t → iProp Σ)
    (N : namespace)
    (fl_s fl_t : gmap fname (option (Any.t → itree crisE Any.t)))
    (Ist : iProp Σ)
    (ps pt : bool)
    (E : coPset) (mtid stid : nat)
    g {R_s R_t} RR
    (ktr_s : _ → itree crisE R_s) (ktr_t : _ → itree crisE R_t)
    (msk_s msk_t : emask)
    (sp_s sp_t : specmap) :
  sp_s.1 !! fid SchHdr.yield = fsp_some (SchA.yield_spec E) →
  sp_t.1 !! fid SchHdr.yield = None →
  img_msk msk_t →
  (msk_t _ (subevent _ (Call SchHdr.yield.1 ()↑))) →
  ↑N ⊆ E →
  Ist ∗
  Tid mtid stid ∗
  (∃ n,
    AU <{ ∃∃ (x2_t : X), αP x2_t }>
      @ n, E∖↑N, E∖↑N, ∅
      <{ ∀∀ ret, αQ x2_t ret,
        COMM
          Ist -∗
          Tid mtid stid -∗
          wsim fl_s fl_t Ist (E∖↑N, E∖↑N) g R_s R_t RR true true
            (⇓sbox(msk_s) (⇓smod(sp_s) 𝒴) >>= ktr_s)
            (ktr_t (ret, x2_t)) }>)%I ⊢
  wsim fl_s fl_t Ist (E∖↑N, E∖↑N) g R_s R_t RR ps pt
    (⇓sbox(msk_s) (⇓smod(sp_s) 𝒴) >>= ktr_s)
    (⇓sbox(msk_t) (⇓smod(sp_t) (
      <<{ ∀∀ x, αP x, ∃∃ ret, αQ x ret }>> @ N)) >>= ktr_t).
Proof using.
  iIntros (? ? [Ht [Hc [Ha [? ?]]]] ? ?) "[IST [TID [%n AU]]]".
  iApply wsim_reset. cCoind CIH g2 Hg2 with n.
  iIntros "[IST [TID AU]]".
  rewrite /atomic_update_sem unfold_yield_namespace_iter. cStepsT. sYields.
  rewrite /atomic_try. cStepsT. rewrite Ht /=.
  iMod ("AU") as "AU"; iMod ("AU" $! tt with "[$]") as "[%x2_t [Pre AU]]".
  cForceT x2_t. rewrite Ha /=.
  cForceT; iFrame "Pre". cStepsT. rewrite ?orb_true_r. cStepsT. case_match.
  { cNormT. try rewrite orb_true_r. cStepsT.
    iMod ("AU" with "GRT") as "[_ AU]". cByCoind CIH. iFrame. }
  cStepsT. try rewrite orb_true_r. cStepsT.
  iMod ("AU" with "GRT") as "[% [_ > AU]]". sYields.
  iApply wsim_mono_knowledge; last first.
  { iApply ("AU" with "IST TID"). }
  { iIntros (???????) "?"; iApply Hg2; done. }
Qed.

Lemma atomic_N_funsem
    `{!crisG Γ Σ α β τ Hinv Hsub, !stateGS Σ} {X X2 : Type}
    (P : namespace → X → iProp Σ)
    (αP : namespace → X → X2 → iProp Σ)
    (αQ : namespace → X → X2 → Any.t → iProp Σ)
    (Q : namespace → X → X2 → Any.t → iProp Σ)
    (N N_t : namespace)
    (fl_s fl_t : gmap fname (option (Any.t → itree crisE Any.t)))
    (Ist : iProp Σ)
    (ps pt : bool)
    g {R_s R_t} RR
    (ktr_s : _ → itree crisE R_s) (ktr_t : _ → itree crisE R_t)
    (msk_s msk_t : emask)
    (sp_s sp_t : specmap) :
  sp_s.1 !! fid SchHdr.yield = None →
  sp_t.1 !! fid SchHdr.yield = None →
  img_msk msk_t →
  (msk_t _ (subevent _ (Call SchHdr.yield.1 ()↑))) →
  ↑N_t ⊆@{coPset} ↑N →
  Ist ∗
  (∃ x_t, P N_t x_t ∗
  (∃ n,
    AU <{ ∃∃ (x2_t : X2), αP N_t x_t x2_t }>
      @ n, ↑N∖↑N_t, ↑N∖↑N_t, ∅
      <{ ∀∀ ret, αQ N_t x_t x2_t ret,
        COMM
          Ist -∗
          Q N_t x_t x2_t ret -∗
          wsim fl_s fl_t Ist (↑N, ↑N) g R_s R_t RR true true
            (⇓sbox(msk_s) (⇓smod(sp_s) 𝒴@{Some N}) >>= ktr_s)
            (ktr_t ret) }>))%I ⊢
  wsim fl_s fl_t Ist (↑N, ↑N) g R_s R_t RR ps pt
    (⇓sbox(msk_s) (⇓smod(sp_s) 𝒴@{Some N}) >>= ktr_s)
    (⇓sbox(msk_t) (⇓smod(sp_t) ((
      {{{ ∀∀ x, P N x }}}
        <<{ ∀∀ x2, αP N x x2, ∃∃ ret, αQ N x x2 ret }>> @ N
      {{{ ∀∀ x2, RET ret, Q N x x2 ret }}} @ N))) >>= ktr_t).
Proof using.
  iIntros (? ? [Ht [Hc [Ha [? ?]]]] ? ?) "[IST [%x_t [Pre [%n AU]]]]".
  iApply (atomic_fun_tgt with "[Pre]"); eauto with iFrame.
  iApply wsim_reset. cCoind CIH g2 Hg2 with n. iIntros "[IST AU]".
  rewrite /atomic_update_sem unfold_yield_namespace_iter. sYields.
  rewrite /atomic_try. cStepsT. rewrite Ht /=.
  iMod ("AU") as "AU"; iMod ("AU" $! tt with "[$]") as "[%x2_t [Pre AU]]".
  cForceT x2_t. rewrite Ha /=.
  cForceT; iFrame "Pre". cStepsT. rewrite ?orb_true_r. cStepsT. case_match.
  { cNormT. try rewrite orb_true_r. cStepsT.
    iMod ("AU" with "GRT") as "[_ AU]". cByCoind CIH. iFrame. }
  cStepsT. try rewrite orb_true_r. cStepsT.
  iMod ("AU" with "GRT") as "[% [_ > AU]]".
  sYields. iApply wsim_mono_knowledge; last first.
  { iApply ("AU" with "IST GRT"). }
  { iIntros (???????) "?"; iApply Hg2; done. }
Qed.

Lemma atomic_N_sem
    `{!crisG Γ Σ α β τ Hinv Hsub, !stateGS Σ} {X : Type}
    (αP : X → iProp Σ)
    (αQ : X → Any.t → iProp Σ)
    (N N_s : namespace)
    (fl_s fl_t : gmap fname (option (Any.t → itree crisE Any.t)))
    (Ist : iProp Σ)
    (ps pt : bool)
    g {R_s R_t} RR
    (ktr_s : _ → itree crisE R_s) (ktr_t : _ → itree crisE R_t)
    (msk_s msk_t : emask)
    (sp_s sp_t : specmap) :
  sp_s.1 !! fid SchHdr.yield = None →
  sp_t.1 !! fid SchHdr.yield = None →
  img_msk msk_t →
  (msk_t _ (subevent _ (Call SchHdr.yield.1 ()↑))) →
  ↑N ⊆@{coPset} ↑N_s →
  Ist ∗
  (∃ n,
    AU <{ ∃∃ (x2_t : X), αP x2_t }>
      @ n, ↑N_s ∖ ↑N, ↑N_s ∖ ↑N, ∅
      <{ ∀∀ ret, αQ x2_t ret,
        COMM
          Ist -∗
          wsim fl_s fl_t Ist (↑N_s ∖ ↑N, ↑N_s ∖ ↑N) g R_s R_t RR true true
            (⇓sbox(msk_s) (⇓smod(sp_s) 𝒴@{Some N_s}) >>= ktr_s)
            (ktr_t (ret, x2_t)) }>)%I ⊢
  wsim fl_s fl_t Ist (↑N_s ∖ ↑N, ↑N_s ∖ ↑N) g R_s R_t RR ps pt
    (⇓sbox(msk_s) (⇓smod(sp_s) 𝒴@{Some N_s}) >>= ktr_s)
    (⇓sbox(msk_t) (⇓smod(sp_t) (
      <<{ ∀∀ x, αP x, ∃∃ ret, αQ x ret }>> @ N)) >>= ktr_t).
Proof using.
  iIntros (? ? [Ht [Hc [Ha [? ?]]]] ? ?) "[IST [%n AU]]".
  iApply wsim_reset. cCoind CIH g2 Hg2 with n. iIntros "[IST AU]".
  rewrite /atomic_update_sem unfold_yield_namespace_iter. cNormT.
  iApply (wsim_yield_namespace_N_N); ss; iFrame.
  iIntros "IST".
  rewrite /atomic_try. cStepsT. rewrite Ht /=.
  iMod ("AU") as "AU"; iMod ("AU" $! tt with "[$]") as "[%x2_t [Pre AU]]".
  cForceT x2_t. rewrite Ha /=.
  cForceT; iFrame "Pre". cStepsT. rewrite ?orb_true_r. cStepsT. case_match.
  { cNormT. try rewrite orb_true_r. cStepsT.
    iMod ("AU" with "GRT") as "[_ AU]". cByCoind CIH. iFrame. }
  cStepsT. try rewrite orb_true_r. cStepsT.
  iMod ("AU" with "GRT") as "[% [_ > AU]]".
  iApply (wsim_yield_namespace_N_N); ss; iFrame.
  iIntros "IST".
  cStepsT. iApply wsim_mono_knowledge; last first.
  { iApply ("AU" with "IST"). }
  { iIntros (???????) "?"; iApply Hg2; done. }
Qed.

Lemma atomic_N_inv_sem
    `{!crisG Γ Σ α β τ Hinv Hsub, !stateGS Σ}
    {X : Type} {n : level}
    (I : GTerm.t n)
    (αP αQ : X → iProp Σ)
    (N N_s N_inv : namespace)
    (fl_s fl_t : gmap fname (option (Any.t → itree crisE Any.t)))
    (Ist : iProp Σ)
    (ps pt : bool)
    g {R_s R_t} RR
    (ktr_s : _ → itree crisE R_s) (ktr_t : _ → itree crisE R_t)
    (msk_s msk_t : emask)
    (sp_s sp_t : specmap) :
  sp_s.1 !! fid SchHdr.yield = None →
  sp_t.1 !! fid SchHdr.yield = None →
  img_msk msk_t →
  (msk_t _ (subevent _ (Call SchHdr.yield.1 ()↑))) →
  ↑N ⊆@{coPset} ↑N_s →
  ↑N_inv ⊆@{coPset} ↑N_s ∖ ↑N →
  inv n N_inv I ∗
  Ist ∗
  (∃ x_t, αP x_t ∗
    (∀ ret,
      αQ x_t -∗
        Ist -∗
        wsim fl_s fl_t Ist (↑N_s ∖ ↑N, ↑N_s ∖ ↑N)
          g R_s R_t RR true true
          (⇓sbox(msk_s) (⇓smod(sp_s) 𝒴@{Some N_s}) >>= ktr_s)
          (ktr_t (ret, x_t)))) ⊢
  wsim fl_s fl_t Ist (↑N_s ∖ ↑N, ↑N_s ∖ ↑N) g R_s R_t RR ps pt
    (⇓sbox(msk_s) (⇓smod(sp_s) 𝒴@{Some N_s}) >>= ktr_s)
    (⇓sbox(msk_t) (⇓smod(sp_t) (
      <<{ ∀∀ x, ⟦I⟧ ∗ αP x, ∃∃ ret, ⟦I⟧ ∗ αQ x }>> @ N)) >>= ktr_t).
Proof using.
  iIntros (? ? ? ? ? ?) "[#Hinv [IST [%x_t [HP Hcont]]]]".
  iApply (atomic_N_sem with "[-]"); eauto.
  iFrame "IST". iExists (S n). iAuIntro.
  iInv "Hinv" as "HI".
  iAaccIntro with "HI HP".
  iSplit.
  - iIntros "[HI HP]".
    iModIntro. iFrame.
  - iIntros (ret) "[HI HQ]".
    iModIntro. iExists (tt↑). iFrame. iModIntro. iFrame.
    iIntros "IST".
    iApply ("Hcont" with "HQ IST").
Qed.

Lemma atomic_sem_funsem
    `{!crisG Γ Σ α β τ Hinv Hsub, !stateGS Σ}
    {X_s X X2 : Type}
    (αP_s : X_s → iProp Σ)
    (αQ_s : X_s → Any.t → iProp Σ)
    (P : namespace → X → iProp Σ)
    (αP : namespace → X → X2 → iProp Σ)
    (αQ : namespace → X → X2 → Any.t → iProp Σ)
    (Q : namespace → X → X2 → Any.t → iProp Σ)
    (N N_s : namespace)
    (fl_s fl_t : gmap fname (option (Any.t → itree crisE Any.t)))
    (Ist : iProp Σ)
    (ps pt : bool)
    g {R_s R_t} RR
    (ktr_s : _ → itree crisE R_s)
    (ktr_t : _ → itree crisE R_t)
    (msk_s msk_t : emask)
    (sp_s sp_t : specmap) :
  sp_s.1 !! fid SchHdr.yield = None →
  sp_t.1 !! fid SchHdr.yield = None →
  img_msk msk_t →
  (msk_t _ (subevent _ (Call SchHdr.yield.1 ()↑))) →
  ↑N ⊆@{coPset} ↑N_s →
  Ist -∗
  (∃ x_t, P N x_t ∗
    ∃ n,
      AU <{ ∀∀ x_s, αP_s x_s, ∃∃ (x2_t : X2), αP N x_t x2_t }>
        @ n, ↑N_s ∖ ↑N, ↑N_s ∖ ↑N, ∅
        <{ ∀∀ ret, αQ N x_t x2_t ret,
          ∃∃ ret_s, αQ_s x_s ret_s,
          COMM
            Ist -∗
            Q N x_t x2_t ret -∗
            wsim fl_s fl_t Ist (↑N_s, ↑N_s) g R_s R_t RR true true
              (⇓sbox(msk_s) (⇓smod(sp_s) 𝒴@{Some N_s});;;
               ktr_s (ret_s, x_s))
              (ktr_t ret) }>)%I -∗
  wsim fl_s fl_t Ist (↑N_s, ↑N_s) g R_s R_t RR ps pt
    (⇓sbox(msk_s) (⇓smod(sp_s)
      (<<{ ∀∀ x2, αP_s x2, ∃∃ ret, αQ_s x2 ret }>> @ N_s)) >>= ktr_s)
    (⇓sbox(msk_t) (⇓smod(sp_t)
      ({{{ ∀∀ x, P N x }}} <<{ ∀∀ x2, αP N x x2, ∃∃ ret, αQ N x x2 ret }>> @ N
      {{{ ∀∀ x2, RET ret, Q N x x2 ret }}} @ N)) >>= ktr_t).
Proof.
  iIntros (? ? [Ht [Hc [Ha [? ?]]]] ? ?) "IST [%x_t [Pre [%n AU]]]".
  iApply (atomic_fun_tgt with "[Pre]"); eauto.
  iApply wsim_reset. cCoind CIH g2 Hg2 with n. iIntros "[IST AU]".
  rewrite /atomic_update_sem unfold_yield_namespace_iter.
  replace_t; [rewrite unfold_yield_namespace_iter //|].
  cNormS; cNormT. sYield. sYieldS.
  rewrite /atomic_try.
  cNormS. case_match; cStepsS; ss. case_match; cStepsS; ss.
  iMod ("AU") as "AU"; iMod ("AU" with "[$]") as "[%x2_t [Pre AU]]".
  cStepsT. rewrite Ht /=. cForceT x2_t. cStepsT. rewrite Ha /=. cForceT; iFrame "Pre".
  cStepsT. rewrite ?orb_true_r. cStepsT. case_match.
  { cNormT. try rewrite orb_true_r. cStepsT. iMod ("AU" with "GRT") as "[Post AU]".
    cForceS (inl tt); cStepsS. cForceS; iFrame. cStepsS.
    cByCoind CIH. iFrame.
  }
  cStepsT. try rewrite orb_true_r. cStepsT.
  iMod ("AU" with "GRT") as "[%ret_s [Post > AU]]".
  cForceS (inr ret_s). cStepsS. cForceS; iFrame; cStepsS.
  sYields.
  cStepsT. iApply wsim_mono_knowledge; last first.
  { cShowS. eapply eq_ind; first iApply ("AU" with "IST GRT"). repeat f_equal.
    extensionalities; symmetry; etransitivity; first hnorm_itr; reflexivity.
  }
  { iIntros (???????) "?"; iApply Hg2; done. }
Qed.

Lemma atomic_sem_sem
    `{!crisG Γ Σ α β τ Hinv Hsub, !stateGS Σ}
    {X_s X_t : Type}
    (N_s N_t : namespace)
    (αP_s : X_s → iProp Σ)
    (αQ_s : X_s → Any.t → iProp Σ)
    (αP : X_t → iProp Σ)
    (αQ : X_t → Any.t → iProp Σ)
    (fl_s fl_t : gmap fname (option (Any.t → itree crisE Any.t)))
    (Ist : iProp Σ)
    (ps pt : bool)
    (E : coPset)
    g {R_s R_t} RR
    (ktr_s : _ → itree crisE R_s)
    (ktr_t : _ → itree crisE R_t)
    (msk_s msk_t : emask)
    (sp_s sp_t : specmap) :
  sp_s.1 !! fid SchHdr.yield = None →
  sp_t.1 !! fid SchHdr.yield = None →
  img_msk msk_t →
  (msk_t _ (subevent _ (Call SchHdr.yield.1 ()↑))) →
  ↑N_t ⊆@{coPset} ↑N_s →
  E = ↑N_s ∖ ↑N_t →
  Ist ∗
  (∃ n,
    AU <{ ∀∀ x_s, αP_s x_s, ∃∃ (x2_t : X_t), αP x2_t }>
      @ n, E, E, ∅
      <{ ∀∀ ret, αQ x2_t ret,
        ∃∃ ret_s, αQ_s x_s ret_s,
        COMM
          Ist -∗
          wsim fl_s fl_t Ist (E, E) g R_s R_t RR true true
            (⇓sbox(msk_s) (⇓smod(sp_s) 𝒴@{Some N_s});;;
             ktr_s (ret_s, x_s))
            (ktr_t (ret, x2_t)) }>)%I ⊢
  wsim fl_s fl_t Ist (E, E) g R_s R_t RR ps pt
    (⇓sbox(msk_s) (⇓smod(sp_s)
      (<<{ ∀∀ x2, αP_s x2, ∃∃ ret, αQ_s x2 ret }>> @ N_s)) >>= ktr_s)
    (⇓sbox(msk_t) (⇓smod(sp_t)
      (<<{ ∀∀ x2, αP x2, ∃∃ ret, αQ x2 ret }>> @ N_t)) >>= ktr_t).
Proof.
  iIntros (? ? [Ht [Hc [Ha [? ?]]]] ? ? ?) "[IST [%n AU]]".
  iApply wsim_reset. cCoind CIH g2 Hg2 with n. iIntros "[IST AU]".
  aUnfoldS. aUnfoldT. sYields. sYieldS.
  cNormS. case_match; cStepsS; ss. case_match; cStepsS; ss.
  iMod ("AU") as "AU"; iMod ("AU" with "[$]") as "[%x2_t [Pre AU]]".
  rewrite Ht /=. cForceT x2_t. rewrite Ha /=. cForceT; iFrame "Pre".
  cStepsT. rewrite ?orb_true_r. cStepsT. case_match.
  { cNormT. try rewrite orb_true_r. cStepsT. iMod ("AU" with "GRT") as "[Post AU]".
    cForceS (inl tt); cStepsS. cForceS; iFrame. cStepsS.
    cByCoind CIH. iFrame.
  }
  clear dependent CIH. cStepsT. try rewrite orb_true_r. cStepsT.
  iMod ("AU" with "GRT") as "[%ret_s [Post > AU]]".
  cForceS (inr ret_s). cStepsS. cForceS; iFrame; cStepsS.
  sYields. iApply wsim_mono_knowledge; last first.
  { cShowS. eapply eq_ind; first iApply ("AU" with "[$]"). repeat f_equal.
    extensionalities; symmetry; etransitivity; first hnorm_itr; reflexivity.
  }
  { iIntros (???????) "?"; iApply Hg2; done. }
Qed.

Lemma atomic_update_src_sem
    `{!crisG Γ Σ α β τ Hinv Hsub, !stateGS Σ}
    {X R_mid : Type}
    (N : namespace)
    (αP : X → iProp Σ)
    (αQ : X → Any.t → iProp Σ)
    (fl_s fl_t : gmap fname (option (Any.t → itree crisE Any.t)))
    (Ist : iProp Σ)
    (ps pt : bool)
    (E : coPset)
    g {R_s R_t} RR
    (ktr_s : _ → itree crisE R_s)
    (itr_t : itree crisE R_mid)
    (ktr_t : R_mid → itree crisE R_t)
    (msk_s : emask)
    (sp_s : specmap) :
  (∀ x_s,
    αP x_s -∗
    wsim fl_s fl_t Ist (E, E) g unit R_mid
      (λ _ ret_t,
        ∃ ret_s, αQ x_s ret_s ∗
          wsim fl_s fl_t Ist (∅, ∅) g R_s R_t RR true false
            (⇓sbox(msk_s) (⇓smod(sp_s) 𝒴@{Some N});;;
             ktr_s (ret_s, x_s))
            (ktr_t ret_t))
      true pt
      (Ret tt)
      itr_t) -∗
  wsim fl_s fl_t Ist (E, E) g R_s R_t RR ps pt
    (⇓sbox(msk_s) (⇓smod(sp_s)
      (<<{ ∀∀ x, αP x, ∃∃ ret, αQ x ret }>> @ N)) >>= ktr_s)
    (itr_t >>= ktr_t).
Proof using.
  iIntros "SIM".
  rewrite /atomic_update_sem unfold_yield_namespace_iter.
  cNormS. iApply wsim_yield_namespace_src.
  rewrite /atomic_try. cStepsS.
  case_match; cStepsS; ss. case_match; cStepsS; ss.
  iPoseProof ("SIM" with "ASM") as "SIM".
  prependRetS tt. iApply (wsim_bind with "[SIM]").
  iSplitL "SIM"; first iFrame.
  iIntros ([] ret_t) "[%ret_s [AQ SIM]]".
  try rewrite orb_true_r. cForceS (inr ret_s). cStepsS.
  cForceS; iFrame "AQ". cStepsS.
  eapply eq_ind; first iApply "SIM".
  repeat f_equal; extensionalities; symmetry; etrans; first hnorm_itr; reflexivity.
Qed.

Lemma yield_iter_prepend_yield_src
    `{!crisG Γ Σ α β τ Hinv Hsub, !stateGS Σ}
    {I R : Type} (body : I → itree _ (I + R)) (arg : I)
    (fl_s fl_t : gmap fname (option (Any.t → itree crisE Any.t)))
    (Ist : iProp Σ)
    (ps pt : bool)
    (Es : coPset) g
    {R_t R_s} RR
    (msk_s : emask)
    (sp_s : specmap)
    (ktr_s : _ → itree crisE R_s)
    (itr_t : itree crisE R_t) :
  wsim fl_s fl_t Ist (Es, Es) g R_s R_t RR ps pt
    (⇓sbox(msk_s) (⇓smod(sp_s) Sch.yield);;;
     ⇓sbox(msk_s) (⇓smod(sp_s) (yield_iter body arg)) >>= ktr_s)
    itr_t ⊢
  wsim fl_s fl_t Ist (Es, Es) g R_s R_t RR ps pt
    (⇓sbox(msk_s) (⇓smod(sp_s) (yield_iter body arg)) >>= ktr_s)
    itr_t.
Proof using.
  iIntros "SIM". rewrite unfold_yield_iter. cNormS. iApply wsim_yy_y.
  eapply eq_ind; first iApply "SIM".
  repeat f_equal; extensionalities; etrans; first hnorm_itr; auto.
Qed.

Lemma yield_namespace_iter_prepend_yield_src
    `{!crisG Γ Σ α β τ Hinv Hsub, !stateGS Σ}
    (N : option namespace)
    {I R : Type} (body : I → itree _ (I + R)) (arg : I)
    (fl_s fl_t : gmap fname (option (Any.t → itree crisE Any.t)))
    (Ist : iProp Σ)
    (ps pt : bool)
    (Es : coPset) g
    {R_s R_t} RR
    (msk_s : emask)
    (sp_s : specmap)
    (ktr_s : _ → itree crisE R_s)
    (itr_t : itree crisE R_t) :
  wsim fl_s fl_t Ist (Es, Es) g _ R_t RR ps pt
    (⇓sbox(msk_s) (⇓smod(sp_s) 𝒴@{N});;;
     ⇓sbox(msk_s) (⇓smod(sp_s) (yield_namespace_iter N body arg)) >>= ktr_s)
    itr_t ⊢
  wsim fl_s fl_t Ist (Es, Es) g _ R_t RR ps pt
    (⇓sbox(msk_s) (⇓smod(sp_s) (yield_namespace_iter N body arg)) >>= ktr_s)
    itr_t.
Proof using.
  iIntros "SIM". rewrite unfold_yield_namespace_iter. cNormS. iApply wsim_yy_y_namespace.
  eapply eq_ind; first iApply "SIM".
  repeat f_equal; extensionalities; etrans; first hnorm_itr; auto.
Qed.

Lemma atomic_update_sem_prepend_yield_src
    `{!crisG Γ Σ α β τ Hinv Hsub, !stateGS Σ} {X2 : Type}
    (N : namespace)
    (αP : X2 → iProp Σ)
    (αQ : X2 → Any.t → iProp Σ)
    (fl_s fl_t : gmap fname (option (Any.t → itree crisE Any.t)))
    (Ist : iProp Σ)
    (ps pt : bool)
    (Es : coPset) g
    {R_t R_s} RR
    (msk_s : emask)
    (sp_s : specmap)
    (ktr_s : _ → itree crisE R_s)
    (itr_t : itree crisE R_t) :
  wsim fl_s fl_t Ist (Es, Es) g _ R_t RR ps pt
    (⇓sbox(msk_s) (⇓smod(sp_s) 𝒴@{Some N});;;
     ⇓sbox(msk_s) (⇓smod(sp_s) (atomic_update_sem N αP αQ)) >>= ktr_s)
    itr_t ⊢
  wsim fl_s fl_t Ist (Es, Es) g _ R_t RR ps pt
    (⇓sbox(msk_s) (⇓smod(sp_s) (atomic_update_sem N αP αQ)) >>= ktr_s)
    itr_t.
Proof using.
  iIntros "SIM". rewrite /atomic_update_sem. iApply yield_namespace_iter_prepend_yield_src. auto.
Qed.

From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export proofmode.
From iris.bi Require Import derived_laws.
Import bi.
Section proofmode.
  Context `{!crisG Γ Σ α β τ Hsub Hinv, !stateGS Σ}.

  Lemma tac_wsim_yield_i_r `{!schGS} {X X2 : Type}
      (x_t : X) (N : namespace)
      Δ i Ist j mtid stid E_s Δ2 Δ3
      (P : namespace → X → iProp Σ)
      (αP : namespace → X → X2 → iProp Σ)
      (αQ : namespace → X → X2 → Any.t → iProp Σ)
      (Q : namespace → X → X2 → Any.t → iProp Σ)
      fl_s fl_t g R_s R_t RR ps pt msk_s sp_s ktr_s (msk_t : emask) sp_t ktr_t :
    sp_s.1 !! (fid SchHdr.yield) = fsp_some (SchA.yield_spec E_s) →
    sp_t.1 !! (fid SchHdr.yield) = None →
    img_msk msk_t →
    (msk_t _ (subevent _ (Call SchHdr.yield.1 ()↑))) →
    envs_lookup_delete true i Δ = Some (false, Ist, Δ2) →
    envs_lookup_delete true j Δ2 = Some (false, Tid mtid stid, Δ3) →
    ↑N ⊆ E_s →
    envs_entails Δ3 (
      P N x_t ∗
      (∃ n,
        AU <{ ∃∃ (x2_t : X2), αP N x_t x2_t }>
          @ n, E_s ∖ ↑N, E_s ∖ ↑N, ∅
          <{ ∀∀ ret, αQ N x_t x2_t ret,
            COMM
              Ist -∗
              Tid mtid stid -∗
              Q N x_t x2_t ret -∗
              wsim fl_s fl_t Ist (E_s, E_s) g R_s R_t RR true true
                (⇓sbox(msk_s) (⇓smod(sp_s) 𝒴) >>= ktr_s)
                (ktr_t ret) }>)
    ) →
    envs_entails Δ (
      wsim fl_s fl_t Ist (E_s, E_s) g R_s R_t RR ps pt
        (⇓sbox(msk_s) (⇓smod(sp_s) 𝒴) >>= ktr_s)
        (⇓sbox(msk_t) (⇓smod(sp_t) ((
          {{{ ∀∀ x, P N x }}}
            <<{ ∀∀ x2, αP N x x2, ∃∃ ret, αQ N x x2 ret }>> @ N
          {{{ ∀∀ x2, RET ret, Q N x x2 ret }}} @ N))) >>= ktr_t)
    ).
  Proof.
    rewrite envs_entails_unseal=> ????.
    rewrite /envs_lookup_delete_Some => ? ? ? Hij.
    rewrite envs_lookup_delete_sound //= envs_lookup_delete_sound //= Hij.
    etransitivity; [|eapply atomic_i_funsem; eauto]. simpl. eauto.
  Qed.

  Lemma tac_atomic_N_funsem {X X2 : Type}
      Δ i Ist Δ2
      (N N_t : namespace)
      (P : namespace → X → iProp Σ)
      (αP : namespace → X → X2 → iProp Σ)
      (αQ : namespace → X → X2 → Any.t → iProp Σ)
      (Q : namespace → X → X2 → Any.t → iProp Σ)
      fl_s fl_t g R_s R_t RR ps pt msk_s sp_s ktr_s (msk_t : emask) sp_t ktr_t :
    sp_s.1 !! (fid SchHdr.yield) = None →
    sp_t.1 !! (fid SchHdr.yield) = None →
    img_msk msk_t →
    (msk_t _ (subevent _ (Call SchHdr.yield.1 ()↑))) →
    ↑N_t ⊆@{coPset} ↑N →
    envs_lookup_delete true i Δ = Some (false, Ist, Δ2) →
    envs_entails Δ2 (
      ∃ x_t, P N_t x_t ∗
      (∃ n,
        AU <{ ∃∃ (x2_t : X2), αP N_t x_t x2_t }>
          @ n, ↑N∖↑N_t, ↑N∖↑N_t, ∅
          <{ ∀∀ ret, αQ N_t x_t x2_t ret,
            COMM
              Ist -∗
              Q N_t x_t x2_t ret -∗
              wsim fl_s fl_t Ist (↑N, ↑N) g R_s R_t RR true true
                (⇓sbox(msk_s) (⇓smod(sp_s) 𝒴@{Some N}) >>= ktr_s)
                (ktr_t ret) }>)
    ) →
    envs_entails Δ (
      wsim fl_s fl_t Ist (↑N, ↑N) g R_s R_t RR ps pt
        (⇓sbox(msk_s) (⇓smod(sp_s) 𝒴@{Some N}) >>= ktr_s)
        (⇓sbox(msk_t) (⇓smod(sp_t) ((
          {{{ ∀∀ x, P N x }}}
            <<{ ∀∀ x2, αP N x x2, ∃∃ ret, αQ N x x2 ret }>> @ N
          {{{ ∀∀ x2, RET ret, Q N x x2 ret }}} @ N))) >>= ktr_t)
    ).
  Proof.
    rewrite envs_entails_unseal=> ?????? Hij.
    rewrite envs_lookup_delete_sound //= Hij.
    etransitivity; [|eapply atomic_N_funsem; eauto]. simpl. eauto.
  Qed.

  Lemma tac_atomic_fun_tgt {X X2 : Type}
      (Δ : envs _)
      (x_t : X)
      (N : namespace)
      (P : namespace → X → iProp Σ)
      (body : namespace → X → itree crisE (Any.t * X2))
      (Q : namespace → X → X2 → Any.t → iProp Σ)
      (fls flt : gmap fname (option fbody))
      (Ist : iProp Σ)
      (E_s : coPset)
      g R_s R_t RR ps pt
      (its : itree crisE R_s)
      (msk_t : emask) (sp_t : specmap) ktr_t :
    (∀ X, msk_t _ (subevent _ (Take X))) →
    (∀ P, msk_t _ (subevent _ (Assume P))) →
    ↑N ⊆ E_s →
    envs_entails Δ (
      P N x_t ∗
      wsim fls flt Ist (E_s∖↑N, E_s∖↑N) g R_s _ RR ps true
        its
        ('(ret_t, x2_t) : _ <- ⇓sbox(msk_t) (⇓smod(sp_t) (body N x_t));;
          trigger (Guarantee (winv (↑N, ↑N) ∗ Q N x_t x2_t ret_t));;;
          ktr_t ret_t)
    ) →
    envs_entails Δ (
      wsim fls flt Ist (E_s, E_s) g R_s R_t RR ps pt
      its
      (⇓sbox(msk_t) (⇓smod(sp_t)
        (({{{ ∀∀ x, P N x }}} body N x
          {{{ ∀∀ x2, RET ret, Q N x x2 ret }}} @ N))) >>= ktr_t)
    ).
  Proof.
    rewrite envs_entails_unseal=> ???->.
    iIntros "[P ?]". iApply (atomic_fun_tgt with "P"); eauto.
  Qed.

  Lemma tac_atomic_sem_funsem {X_s X_t : Type}
      Δ i Ist Δ2
      (N_s N_t : namespace)
      (αP_s : X_s → iProp Σ)
      (αQ_s : X_s → Any.t → iProp Σ)
      (αP : X_t → iProp Σ)
      (αQ : X_t → Any.t → iProp Σ)
      (fl_s fl_t : gmap fname (option (Any.t → itree crisE Any.t)))
      (ps pt : bool)
      (E : coPset)
      g {R_s R_t} RR
      (ktr_s : _ → itree crisE R_s)
      (ktr_t : _ → itree crisE R_t)
      (msk_s msk_t : emask)
      (sp_s sp_t : specmap) :
    sp_s.1 !! fid SchHdr.yield = None →
    sp_t.1 !! fid SchHdr.yield = None →
    img_msk msk_t →
    (msk_t _ (subevent _ (Call SchHdr.yield.1 ()↑))) →
    ↑N_t ⊆@{coPset} ↑N_s →
    E = ↑N_s ∖ ↑N_t →
    envs_lookup_delete true i Δ = Some (false, Ist, Δ2) →
    envs_entails Δ2 (
      (∃ n,
        AU <{ ∀∀ x_s, αP_s x_s, ∃∃ (x2_t : X_t), αP x2_t }>
          @ n, E, E, ∅
          <{ ∀∀ ret, αQ x2_t ret,
            ∃∃ ret_s, αQ_s x_s ret_s,
            COMM
              Ist -∗
              wsim fl_s fl_t Ist (E, E) g R_s R_t RR true true
                (⇓sbox(msk_s) (⇓smod(sp_s) 𝒴@{Some N_s});;;
                 ktr_s (ret_s, x_s))
                (ktr_t (ret, x2_t)) }>)
    ) →
    envs_entails Δ (
      wsim fl_s fl_t Ist (E, E) g R_s R_t RR ps pt
        (⇓sbox(msk_s) (⇓smod(sp_s)
          (<<{ ∀∀ x2, αP_s x2, ∃∃ ret, αQ_s x2 ret }>> @ N_s)) >>= ktr_s)
        (⇓sbox(msk_t) (⇓smod(sp_t)
          (<<{ ∀∀ x2, αP x2, ∃∃ ret, αQ x2 ret }>> @ N_t)) >>= ktr_t)
    ).
  Proof.
    rewrite envs_entails_unseal=> ????.
    rewrite /envs_lookup_delete_Some => ? ? ? Hij.
    rewrite envs_lookup_delete_sound //= Hij.
    etransitivity; [|eapply atomic_sem_sem]; eauto.
  Qed.
End proofmode.

Tactic Notation "aStep" :=
  lazymatch goal with
  | |- environments.envs_entails _
      (wsim _ _ _ _ _ _ _ _ _ _
        (ITree.bind (SB.sandbox ?msk (SModTr.trans ?sp
          (atomic_update_sem ?N_s ?αP ?αQ)
          )) ?ktr)
        (ITree.bind (SB.sandbox ?msk_t (SModTr.trans ?sp_t
          (atomic_update_sem ?N_t ?αP_t ?αQ_t)
          )) ?ktr_t)) =>
    eapply tac_atomic_sem_funsem;
    [ by simpl_sp
    | by simpl_sp
    | solve_msk
    | solve_msk
    | iSolveSideCondition
    | simpl_set; iSolveSideCondition
    |(by iAssumptionCore || fail "aStep: ist not found")
    | .. ]
  | |- environments.envs_entails _
      (wsim _ _ _ _ _ _ _ _ _ _
        (SB.sandbox ?msk (SModTr.trans ?sp (atomic_update_sem ?N_s ?αP ?αQ)))
        (ITree.bind (SB.sandbox ?msk_t (SModTr.trans ?sp_t
          (atomic_update_sem ?N_t ?αP_t ?αQ_t)
          )) ?ktr_t)) =>
    appendRetS;
    eapply tac_atomic_sem_funsem;
    [ by simpl_sp
    | by simpl_sp
    | solve_msk
    | solve_msk
    | iSolveSideCondition
    | simpl_set; iSolveSideCondition
    |(by iAssumptionCore || fail "aStep: ist not found")
    | .. ]
  end.

Tactic Notation "aStepS" "(" ne_simple_intropattern_list(x) ")" uconstr(H) :=
  match goal with
  | |- environments.envs_entails _
      (wsim _ _ _ _ _ _ _ _ _ _
        (SB.sandbox ?msk (SModTr.trans ?sp (atomic_fun ?P ?body ?Q))) _) =>
    iApply (atomic_fun_src P body Q); last (_iIntros x H; simpl_set)
  end.

Tactic Notation "aForceT" constr(N) "with" constr (H) :=
  lazymatch goal with
  | |- envs_entails _ (
      wsim ?fl_s ?fl_t ?Ist ?Es ?g ?R_s ?R_t ?RR ?p_s ?p_t 
        (SB.sandbox ?msk_s (SModTr.trans ?sp_s 𝒴) >>= _)
        (SB.sandbox ?msk_t (SModTr.trans ?sp_t
          (atomic_fun ?P (λ N x, atomic_update_sem N ?αP ?αQ) ?Q)
        ) >>= _)
    ) =>
    eapply (tac_wsim_yield_i_r _ N);
      [by simpl_sp
      |by simpl_sp
      |solve_msk
      |solve_msk
      |(by iAssumptionCore || fail "aForceT: ist not found")
      |(by iAssumptionCore || fail "aForceT: tid not found")
      |solve_ndisj
      |iSplitL H]
  | |- environments.envs_entails _ (
      wsim ?fl_s ?fl_t ?Ist ?Es ?g ?R_s ?R_t ?RR ?p_s ?p_t 
        (SB.sandbox ?msk_s (SModTr.trans ?sp_s 𝒴@{Some ?N_s}) >>= _)
        (SB.sandbox ?msk_t (SModTr.trans ?sp_t
          (atomic_fun ?P (λ N x, atomic_update_sem N ?αP ?αQ) ?Q)
        ) >>= _)
    ) =>
    eapply (tac_atomic_N_funsem _ _ Ist _ N_s N);
    [ by simpl_sp
    | by simpl_sp
    | solve_msk
    | solve_msk
    | iSolveSideCondition
    |(by iAssumptionCore || fail "aForceT: ist not found")
    | ]
  | |- environments.envs_entails _ (
        wsim ?fl_s ?fl_t ?Ist ?Es ?g ?R_s ?R_t ?RR ?p_s ?p_t 
          _
          (SB.sandbox ?msk_t (SModTr.trans ?sp_t
            (atomic_fun ?P ?body ?Q)
          ) >>= _)
    ) =>
      eapply (tac_atomic_fun_tgt _ _ N);
        [solve_msk
        |solve_msk
        |solve_ndisj
        |iSplitL H; [|simpl_set]]
  | |- environments.envs_entails _ (
        wsim ?fl_s ?fl_t ?Ist ?Es ?g ?R_s ?R_t ?RR ?p_s ?p_t 
          _
          (SB.sandbox ?msk_t (SModTr.trans ?sp_t (atomic_fun ?P ?body ?Q)))
    ) =>
      appendRetT;
      eapply (tac_atomic_fun_tgt _ _ N);
        [solve_msk
        |solve_msk
        |solve_ndisj
        |iSplitL H; [|simpl_set]]
  end.

Ltac aAddY :=
  lazymatch goal with
  | |- environments.envs_entails _
      (wsim _ _ _ _ _ _ _ _ _ _
        (ITree.bind (SB.sandbox ?msk (SModTr.trans ?sp Sch.yield)) _) _) =>
    iApply wsim_yy_y
  | |- environments.envs_entails _
      (wsim _ _ _ _ _ _ _ _ _ _
        (SB.sandbox ?msk (SModTr.trans ?sp (atomic_update_sem ?N ?αP ?αQ))) _) =>
    appendRetS; iApply (atomic_update_sem_prepend_yield_src N αP αQ); rewrite bind_ret_r
  | |- environments.envs_entails _
      (wsim _ _ _ _ _ _ _ _ _ _
        (ITree.bind (SB.sandbox ?msk
          (SModTr.trans ?sp (atomic_update_sem ?N ?αP ?αQ))) _) _) =>
    iApply (atomic_update_sem_prepend_yield_src N αP αQ)
  | |- environments.envs_entails _
      (wsim _ _ _ _ _ _ _ _ _ _
        (SB.sandbox ?msk (SModTr.trans ?sp (yield_namespace_iter _ _ _))) _) =>
    appendRetS; iApply yield_namespace_iter_prepend_yield_src; rewrite bind_ret_r
  | |- environments.envs_entails _
      (wsim _ _ _ _ _ _ _ _ _ _
        (ITree.bind (SB.sandbox ?msk
          (SModTr.trans ?sp (yield_namespace_iter _ _ _))) _) _) =>
    iApply yield_namespace_iter_prepend_yield_src
  | |- environments.envs_entails _
      (wsim _ _ _ _ _ _ _ _ _ _
        (SB.sandbox ?msk (SModTr.trans ?sp (yield_iter _ _))) _) =>
    appendRetS; iApply yield_iter_prepend_yield_src; rewrite bind_ret_r
  | |- environments.envs_entails _
      (wsim _ _ _ _ _ _ _ _ _ _
        (ITree.bind (SB.sandbox ?msk
          (SModTr.trans ?sp (yield_iter _ _))) _) _) =>
    iApply yield_iter_prepend_yield_src
  end.
