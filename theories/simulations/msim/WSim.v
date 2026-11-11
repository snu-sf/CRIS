From CRIS.common Require Import Common ConcRA StatePredicate.
From iris.proofmode Require Import environments proofmode.
From stdpp Require Import coPset.
From CRIS.simulations.msim Require Import ISim.
From CRIS.modules Require Import SMod SModTr Mod.
From CRIS.simulations.msim Require Import TacticsCommon.
From CRIS.simulations.msim Require Export MSimCommon.

(* Typeclass definition to streamline assume/guarantee processing *)
Class WP `{!crisG Γ Σ α β τ _S _I} (P : iProp Σ) := mk_WP {
  WP_space : coPset;
  WP_remainder : iProp Σ;
  WP_iff : P ∗-∗ winv (WP_space, WP_space) ∗ WP_remainder
}.
Arguments mk_WP {_ _ _ _ _ _ _ _ _} _ _ _.
Arguments WP_remainder {_ _ _ _ _ _ _ _} [_] _.
Arguments WP_space {_ _ _ _ _ _ _ _} [_] _.
Arguments WP_iff {_ _ _ _ _ _ _ _} [_] _.

Program Global Instance WP_refl E `{!crisG Γ Σ α β τ _S _I}
  : WP (winv (E, E)) := mk_WP E True _.
Next Obligation. ii; iSplit; first iIntros "$"; iIntros "[$ _]". Qed.

Program Global Instance fspec_winv_precond `{!crisG Γ Σ α β τ _S _I} (fsp : fspec) E m arg varg :
  WP (precond (fspec_winv E fsp) m arg varg) :=
  {| WP_space := E; WP_remainder := (precond fsp m arg varg) |}.
Next Obligation. intros; iSplit; iIntros "[$ $]". Qed.

Program Global Instance fspec_winv_postcond `{!crisG Γ Σ α β τ _S _I} (fsp : fspec) E m arg varg :
  WP (postcond (fspec_winv E fsp) m arg varg) :=
  {| WP_space := E; WP_remainder := (postcond fsp m arg varg) |}.
Next Obligation. intros; iSplit; iIntros "[$ $]". Qed.

Section wsim.
  Context `{!crisG Γ Σ α β τ _S _I}.
  Context `{!stateGS Σ}.

  Local Definition rel : Type := ∀ R_s R_t : Type,
      retr_type Σ R_s R_t → bool → bool → itree crisE R_s → itree crisE R_t → iProp Σ.

  Local Definition wsim_def fl_s fl_t Ist Ep g R_s R_t RR ps pt i_s i_t :
      iProp Σ :=
    winv Ep -∗ @isim Σ _ fl_s fl_t Ist g R_s R_t RR ps pt i_s i_t.
  Local Definition wsim_aux : seal (@wsim_def). Proof using. by eexists. Qed.
  Definition wsim := wsim_aux.(unseal).
  Local Definition wsim_eq : @wsim = @wsim_def := wsim_aux.(seal_eq).
  Local Ltac unseal := rewrite wsim_eq /wsim_def.

  Context (fl_s fl_t : gmap fname (option (Any.t → itree crisE Any.t))).
  Context (Ist : iProp Σ).
  Context (R_s R_t : Type).

  Local Notation sim Ep g := (wsim fl_s fl_t Ist Ep g R_s R_t).

  Context (Ep : coPset * coPset).
  Context (g : rel).
  Context (RR : retr_type Σ R_s R_t).
  Context (ps pt : bool).

  (* Basic simulation rules *)
  Lemma wsim_ret rs rt :
    RR rs rt ⊢ sim Ep g RR ps pt (Ret rs) (Ret rt).
  Proof using. unseal; iIntros "RR I". by iApply isim_ret. Qed.

  Lemma wsim_call fn arg k_s k_t :
    Ist ∗
    (∀ ret, Ist -∗ sim Ep g RR true true (k_s ret) (k_t ret)) ⊢
    sim Ep g RR ps pt
      (trigger (Call fn arg) >>= k_s) (trigger (Call fn arg) >>= k_t).
  Proof using.
    unseal; iIntros "[IST CONT] I".
    rewrite -isim_call; iFrame.
    iIntros (?) "IST". iApply ("CONT" with "[IST]"); et; iFrame.
  Qed.

  Lemma wsim_io fn I O (arg : I) k_s k_t :
    (∀ (ret : O),
      sim Ep g RR true true (k_s ret) (k_t ret)) ⊢
    sim Ep g RR ps pt
      (trigger (IO fn arg) >>= k_s)
      (trigger (IO fn arg) >>= k_t).
  Proof using. unseal; iIntros "RR I". iApply isim_io. iIntros (ret); iApply "RR"; iFrame. Qed.

  Lemma wsim_tau_src i_s i_t :
    sim Ep g RR true pt i_s i_t ⊢
    sim Ep g RR ps pt (tau;; i_s) i_t.
  Proof using. unseal; iIntros "RR I". iApply isim_tau_src; iApply "RR"; iFrame. Qed.

  Lemma wsim_tau_tgt i_s i_t :
    sim Ep g RR ps true i_s i_t ⊢
    sim Ep g RR ps pt i_s (tau;; i_t).
  Proof using. unseal; iIntros "RR I". iApply isim_tau_tgt; iApply "RR"; iFrame. Qed.

  Lemma wsim_inline_src fn arg f_s k_s i_t :
    fl_s !! (funid fn) = Some (Some f_s) →
    sim Ep g RR true pt
      (ret <- f_s arg;; tau;; k_s ret)
      i_t ⊢
    sim Ep g RR ps pt (trigger (Call fn arg) >>= k_s) i_t.
  Proof using. i; unseal; iIntros "RR I". iApply isim_inline_src; eauto. iApply "RR"; iFrame. Qed.

  Lemma wsim_inline_tgt fn arg i_s f_t k_t :
    fl_t !! (funid fn) = Some (Some f_t) →
    sim Ep g RR ps true
      i_s
      (ret <- f_t arg;; tau;; k_t ret) ⊢
    sim Ep g RR ps pt i_s (trigger (Call fn arg) >>= k_t).
  Proof using. i; unseal; iIntros "RR I". iApply isim_inline_tgt; eauto. iApply "RR"; iFrame. Qed.
  
  Lemma wsim_take_src X k_s i_t :
    (∀ x, sim Ep g RR true pt (k_s x) i_t) ⊢
    sim Ep g RR ps pt (trigger (Take X) >>= k_s) i_t.
  Proof using.
    unseal; iIntros "RR I". iApply isim_take_src; eauto. iIntros (x); iApply "RR"; iFrame.
  Qed.

  Lemma wsim_take_src_fspec fsp k_s i_t :
    (∀ x, sim Ep g RR true pt (k_s (FSpec_mk _ _ (fspec_to_rel_satisfy fsp x))) i_t) ⊢
    sim Ep g RR ps pt (trigger (Take (FSpec (fspec_to_rel fsp))) >>= k_s) i_t.
  Proof using.
    unseal; iIntros "RR I". iApply isim_take_src_fspec; eauto. iIntros (x); iApply "RR"; iFrame.
  Qed.

  Lemma wsim_take_tgt X i_s k_t :
    (∃ x, sim Ep g RR ps true i_s (k_t x)) ⊢
    sim Ep g RR ps pt i_s (trigger (Take X) >>= k_t).
  Proof using.
    unseal; iIntros "[%x RR] I". iApply isim_take_tgt; eauto. iExists _; iApply "RR"; iFrame.
  Qed.

  Lemma wsim_take_tgt_fspec fsp i_s k_t :
    (∃ x, sim Ep g RR ps true i_s
      (k_t (FSpec_mk _ _ (fspec_to_rel_satisfy fsp x)))) ⊢
    sim Ep g RR ps pt i_s
      (trigger (Take (FSpec (fspec_to_rel fsp))) >>= k_t).
  Proof using.
    unseal; iIntros "[%x RR] I". iApply isim_take_tgt_fspec; eauto. iExists _; iApply "RR"; iFrame.
  Qed.

  Lemma wsim_choose_src X k_s i_t :
    (∃ x, sim Ep g RR true pt (k_s x) i_t) ⊢
    sim Ep g RR ps pt (trigger (Choose X) >>= k_s) i_t.
  Proof using.
    unseal; iIntros "[%x RR] I". iApply isim_choose_src; eauto. iExists _; iApply "RR"; iFrame.
  Qed.

  Lemma wsim_choose_src_fspec fsp k_s i_t :
    (∃ x, sim Ep g RR true pt
      (k_s (FSpec_mk _ _ (fspec_to_rel_satisfy fsp x))) i_t) ⊢
    sim Ep g RR ps pt
      (trigger (Choose (FSpec (fspec_to_rel fsp))) >>= k_s) i_t.
  Proof using.
    unseal; iIntros "[%x RR] I". iApply isim_choose_src_fspec; eauto. iExists _; iApply "RR"; iFrame.
  Qed.

  Lemma wsim_choose_tgt X i_s k_t :
    (∀ x, sim Ep g RR ps true i_s (k_t x)) ⊢
    sim Ep g RR ps pt i_s (trigger (Choose X) >>= k_t).
  Proof using.
    unseal; iIntros "RR I". iApply isim_choose_tgt; eauto. iIntros (x); iApply "RR"; iFrame.
  Qed.

  Lemma wsim_choose_tgt_fspec fsp i_s k_t :
    (∀ x, sim Ep g RR ps true i_s
      (k_t (FSpec_mk _ _ (fspec_to_rel_satisfy fsp x)))) ⊢
    sim Ep g RR ps pt i_s
      (trigger (Choose (FSpec (fspec_to_rel fsp))) >>= k_t).
  Proof using.
    unseal; iIntros "RR I". iApply isim_choose_tgt_fspec; eauto. iIntros (x); iApply "RR"; iFrame.
  Qed.

  Lemma wsim_sput_src k v v' k_s i_t :
    k ↦src v ∗ (k ↦src v' -∗ sim Ep g RR true pt (k_s tt) i_t) ⊢
      sim Ep g RR ps pt (trigger (SPut k v') >>= k_s) i_t.
  Proof using.
    unseal; iIntros "[PT SIM] I".
    iApply isim_sput_src. iSplitL "PT"; et. iIntros "PT".
    iApply ("SIM" with "PT"). et.
  Qed.

  Lemma wsim_sput_tgt k v v' i_s k_t :
    k ↦tgt v ∗ (k ↦tgt v' -∗ sim Ep g RR ps true i_s (k_t tt)) ⊢
    sim Ep g RR ps pt i_s (trigger (SPut k v') >>= k_t).
  Proof using.
    unseal; iIntros "[PT SIM] I".
    iApply isim_sput_tgt. iSplitL "PT"; et. iIntros "PT".
    iApply ("SIM" with "PT"). et.
  Qed.

  Lemma wsim_sput_src_uninit k v' k_s i_t :
    uninit_src k ∗ (k ↦src v' -∗ sim Ep g RR true pt (k_s tt) i_t) ⊢
      sim Ep g RR ps pt (trigger (SPut k v') >>= k_s) i_t.
  Proof using.
    unseal; iIntros "[PT SIM] I".
    iApply isim_sput_src_uninit. iSplitL "PT"; et. iIntros "PT".
    iApply ("SIM" with "PT"). et.
  Qed.

  Lemma wsim_sput_tgt_uninit k v' i_s k_t :
    uninit_tgt k ∗ (k ↦tgt v' -∗ sim Ep g RR ps true i_s (k_t tt)) ⊢
      sim Ep g RR ps pt i_s (trigger (SPut k v') >>= k_t).
  Proof using.
    unseal; iIntros "[PT SIM] I".
    iApply isim_sput_tgt_uninit. iSplitL "PT"; et. iIntros "PT".
    iApply ("SIM" with "PT"). et.
  Qed.

  Lemma wsim_sget_src k v k_s i_t :
    k ↦src v ∗ (k ↦src v -∗ sim Ep g RR true pt (k_s v) i_t) ⊢
    sim Ep g RR ps pt (trigger (SGet k) >>= k_s) i_t.
  Proof using.
    unseal; iIntros "[PT SIM] I".
    iApply isim_sget_src. iSplitL "PT"; et. iIntros "PT".
    iApply ("SIM" with "PT"). et.
  Qed.

  Lemma wsim_sget_tgt k v i_s k_t :
    k ↦tgt v ∗ (k ↦tgt v -∗ sim Ep g RR ps true i_s (k_t v)) ⊢
    sim Ep g RR ps pt i_s (trigger (SGet k) >>= k_t).
  Proof using.
    unseal; iIntros "[PT SIM] I".
    iApply isim_sget_tgt. iSplitL "PT"; et. iIntros "PT".
    iApply ("SIM" with "PT"). et.
  Qed.

  Lemma wsim_sget_src_uninit k k_s i_t :
    uninit_src k ∗ (uninit_src k -∗
      sim Ep g RR true pt (k_s (tt↑)) i_t) ⊢
    sim Ep g RR ps pt (trigger (SGet k) >>= k_s) i_t.
  Proof using.
    unseal; iIntros "[PT SIM] I".
    iApply isim_sget_src_uninit. iSplitL "PT"; et. iIntros "PT".
    iApply ("SIM" with "PT"). et.
  Qed.

  Lemma wsim_sget_tgt_uninit k i_s k_t :
    uninit_tgt k ∗ (uninit_tgt k -∗
      sim Ep g RR ps true i_s (k_t (tt↑))) ⊢
    sim Ep g RR ps pt i_s (trigger (SGet k) >>= k_t).
  Proof using.
    unseal; iIntros "[PT SIM] I".
    iApply isim_sget_tgt_uninit. iSplitL "PT"; et. iIntros "PT".
    iApply ("SIM" with "PT"). et.
  Qed.

  Lemma wsim_assume_src P k_s i_t :
    (P -∗ sim Ep g RR true pt (k_s tt) i_t) ⊢
    sim Ep g RR ps pt (trigger (Assume P) >>= k_s) i_t.
  Proof using.
    unseal; iIntros "RR I". iApply isim_assume_src; eauto. iIntros "P".
    iApply ("RR" with "P"); iFrame.
  Qed.

  Lemma wsim_assume_res_src a k_s i_t :
    (Own a -∗ sim Ep g RR true pt (k_s tt) i_t) ⊢
    sim Ep g RR ps pt (trigger (AssumeRes a) >>= k_s) i_t.
  Proof using.
    unseal. iIntros "H I". iApply isim_assume_res_src; eauto.
    iFrame. iIntros "P". iApply ("H" with "P I").
  Qed.

  Lemma wsim_assume_tgt P i_s k_t :
    P ∗ sim Ep g RR ps true i_s (k_t tt) ⊢
    sim Ep g RR ps pt i_s (trigger (Assume P) >>= k_t).
  Proof using.
    unseal; iIntros "[P RR] I". iApply isim_assume_tgt; eauto. iFrame. iApply "RR". ss.
  Qed.

  Lemma wsim_assume_res_tgt a i_s k_t :
    (Own a ∗ sim Ep g RR ps true i_s (k_t tt)) ⊢
    sim Ep g RR ps pt i_s (trigger (AssumeRes a) >>= k_t).
  Proof using.
    unseal; iIntros "[A H] I". iApply isim_assume_res_tgt; eauto.
    iPoseProof ("H" with "I") as "$". iFrame.
  Qed.

  Lemma wsim_guarantee_src (P : iProp Σ) k_s i_t :
    P ∗ sim Ep g RR true pt (k_s tt) i_t ⊢
    sim Ep g RR ps pt (trigger (Guarantee P) >>= k_s) i_t.
  Proof using.
    unseal; iIntros "[P RR] I". iApply isim_guarantee_src; eauto. iFrame. iApply "RR"; ss.
  Qed.

  Lemma wsim_guarantee_tgt (P : iProp Σ) i_s k_t :
    (P -∗ sim Ep g RR ps true i_s (k_t tt)) ⊢
    sim Ep g RR ps pt i_s (trigger (Guarantee P) >>= k_t).
  Proof using.
    unseal; iIntros "RR I". iApply isim_guarantee_tgt; eauto.
    iIntros "P"; iApply ("RR" with "P"); done.
  Qed.

  Lemma wsim_spawn fn args k_s k_t :
    (∀ tid, sim Ep g RR true true (k_s tid) (k_t tid)) ⊢
    sim Ep g RR ps pt
      (trigger (Spawn fn args) >>= k_s)
      (trigger (Spawn fn args) >>= k_t).
  Proof using. unseal; iIntros "C I". iApply isim_spawn; eauto. iIntros "%"; iApply "C". ss. Qed.

  Lemma wsim_yield tid k_s k_t :
    Ist ∗
    (Ist -∗ sim Ep g RR true true (k_s ()) (k_t ())) ⊢
    sim Ep g RR ps pt
      (trigger (Yield tid) >>= k_s)
      (trigger (Yield tid) >>= k_t).
  Proof using.
    unseal; iIntros "[IST C] I". iApply isim_yield; eauto. iFrame.
    iIntros "IST"; iApply ("C" with "[IST] [I]"); iFrame; et.
  Qed.

  Lemma wsim_gettid k_s k_t :
    (∀ tid, sim Ep g RR true true (k_s tid) (k_t tid)) ⊢
    sim Ep g RR ps pt
      (trigger GetTid >>= k_s)
      (trigger GetTid >>= k_t).
  Proof using.
    unseal; iIntros "C I". iApply isim_gettid; eauto.
    iIntros (?); iApply ("C" with "I"); iFrame; et.
  Qed.

  Lemma wsim_reset i_s i_t :
    sim Ep g RR false false i_s i_t ⊢
    sim Ep g RR ps pt i_s i_t.
  Proof using. unseal; iIntros "RR I". iApply isim_reset; iApply "RR"; iFrame. Qed.

  Lemma wsim_progress i_s i_t :
    (winv Ep -∗ g R_s R_t RR false false i_s i_t)
      ⊢ sim Ep g RR true true i_s i_t.
  Proof using.
    unseal; iIntros "RR I". iApply isim_progress.
    iApply "RR". eauto.
  Qed.

  Lemma wsim_flag_mon i_s i_t (ps0 pt0 : bool)
      (PSLE : ps0 → ps) (PTLE : pt0 → pt) :
    sim Ep g RR ps0 pt0 i_s i_t
    ⊢ sim Ep g RR ps pt i_s i_t.
  Proof using.
    unseal. iIntros "SIM I". iApply isim_flag_mon; [| |iApply "SIM"]; eauto.
  Qed.

  Lemma wsim_coind A (P: A → _) RsA RtA RRA psA ptA srcA tgtA
    (COIND: ∀ (g0 : rel)
        (INC: ∀ Rs Rt RR ps pt src tgt, g Rs Rt RR ps pt src tgt ⊢ g0 Rs Rt RR ps pt src tgt)
        (CIH: ∀ a, P a ∗ winv Ep ⊢ g0 (RsA a) (RtA a) (RRA a) (psA a) (ptA a) (srcA a) (tgtA a)),
      ∀ a, P a ⊢ wsim fl_s fl_t Ist Ep g0 (RsA a) (RtA a) (RRA a) (psA a) (ptA a) (srcA a) (tgtA a))
    :
    ∀ a, P a ⊢ wsim fl_s fl_t Ist Ep g (RsA a) (RtA a) (RRA a) (psA a) (ptA a) (srcA a) (tgtA a).
  Proof using.
    revert COIND. unseal. intros COIND a.
    iIntros "P I"; iCombine "P I" as "P". iStopProof.
    revert a. eapply isim_coind.
    intros g0 INC CIH a. iIntros "[P I]".
    iPoseProof ((COIND _ INC CIH a) with "P I") as "H"; et.
  Qed.

  Lemma wsim_frame
    P i_s i_t
    : P ∗ sim Ep g RR ps pt i_s i_t
        ⊢ sim Ep g (fun r_s r_t => P ∗ RR r_s r_t) ps pt i_s i_t.
  Proof.
    unseal.
    iIntros "[H SIM] WINV".
    iApply isim_frame.
    iSplitL "H"; et. iApply "SIM"; et.
  Qed.

  Lemma wsim_bind {Qs Qt} QQ i_s i_t k_s k_t :
    wsim fl_s fl_t Ist Ep g Qs Qt QQ ps pt i_s i_t
    ∗ (∀ r_s r_t,
        QQ r_s r_t
        -∗ sim (∅,∅) g RR false false (k_s r_s) (k_t r_t))%I
    ⊢ (sim Ep g RR ps pt (i_s >>= k_s) (i_t >>= k_t)).
  Proof using.
    rewrite wsim.wsim_eq /wsim.wsim_def.
    iIntros "[W SIM] INV".
    iPoseProof (winv_split_empty with "[INV]") as "[INV INV']"; et.
    iApply isim_bind.
    iSplitL "W INV". { iApply "W"; eauto. }
    iIntros (? ?) "Q". iSpecialize ("SIM" $! _ _).
    iApply ("SIM" with "Q"); et.
  Qed.

  (* Lemmas that use WP typeclasses *)
  Lemma wsim_guarantee_src_WP `{i : !WP P} k_s i_t Ew E :
    let EP := WP_space i in
    EP ⊆ Ew → EP ⊆ E →
    (WP_remainder i ∗
    sim (Ew ∖ EP, E ∖ EP) g RR true pt (k_s tt) i_t) ⊢
    sim (Ew, E) g RR ps pt (trigger (Guarantee P) >>= k_s) i_t.
  Proof using.
    unseal; iIntros (??) "[P SIM] I".
    iPoseProof (winv_split (WP_space i) (Ew ∖ WP_space i) (WP_space i) (E ∖ WP_space i)
      with "[I]") as "[I1 I2]".
    { set_solver. }
    { set_solver. }
    { rewrite -?union_difference_L //. }
    iApply isim_guarantee_src; eauto.
    iSplitR "SIM I2".
    { iApply WP_iff; iFrame. }
    { iApply "SIM"; iFrame. }
  Qed.

  Lemma wsim_assume_src_WP `{i : !WP P} k_s i_t :
    let EP := WP_space i in
    let Ep' := match Ep with (Ew, E) => (Ew ∪ EP, E ∪ EP) end in
    (WP_remainder i -∗ sim Ep' g RR true pt (k_s tt) i_t) ⊢
    sim Ep g RR ps pt (trigger (Assume P) >>= k_s) i_t.
  Proof using.
    unseal; iIntros "SIM I1". iApply isim_assume_src; eauto. iIntros "P".
    destruct Ep as [??]; iPoseProof (WP_iff with "P") as "[I Q]".
    iMod (winv_merge with "[I I1]") as "[I _]"; iFrame.
    iApply ("SIM" with "Q"); iFrame.
  Qed.

  Lemma wsim_assume_tgt_WP `{i : !WP P} i_s k_t Ew E :
    let EP := WP_space i in
    EP ⊆ Ew → EP ⊆ E →
    (WP_remainder i ∗ sim (Ew ∖ EP, E ∖ EP) g RR ps true i_s (k_t tt)) ⊢
    sim (Ew, E) g RR ps pt i_s (trigger (Assume P) >>= k_t).
  Proof using.
    unseal; iIntros (??) "[P SIM] [O [E [%n W]]]".
    iPoseProof (own_admin_split with "O") as "[O1 O2]". iApply isim_assume_tgt; eauto.
    rewrite /winv {2}(union_difference_L (WP_space i) Ew) // wsats_split; last set_solver.
    rewrite {2}(union_difference_L (WP_space i) E) // ownE_op; last set_solver.
    iDestruct "W" as "[W1 W2]"; iDestruct "E" as "[E1 E2]".
    iSplitR "SIM E2 W2 O2".
    { iApply WP_iff; iFrame. }
    { iApply "SIM"; iFrame. }
  Qed.

  Lemma wsim_guarantee_tgt_WP `{i : !WP P} i_s k_t :
    let EP := WP_space i in
    let Ep' := match Ep with (Ew, E) => (Ew ∪ EP, E ∪ EP) end in
    (WP_remainder i -∗ sim Ep' g RR ps true i_s (k_t tt)) ⊢
    sim Ep g RR ps pt i_s (trigger (Guarantee P) >>= k_t).
  Proof using.
    s; iIntros "SIM"; iApply wsim_guarantee_tgt; iIntros "P".
    iPoseProof (WP_iff i with "P") as "[P1 P2]".
    unseal; iIntros "I".
    iAssert ( |==> winv
      (match Ep with (Ew, E) => (Ew ∪ WP_space i, E ∪ WP_space i) end))%I
    with "[I P1]" as "> I".
    { destruct Ep as [??]; ss; iPoseProof (winv_merge with "[I P1]") as "[$ _]"; iFrame. }
    iApply ("SIM" with "P2"); ss.
  Qed.

  (* Derived lemmas *)
  Lemma wsim_unwrapU_src X (x : option X) k_s i_t :
    (∀ x', ⌜x = Some x'⌝ -∗ sim Ep g RR ps pt (k_s x') i_t) ⊢
    sim Ep g RR ps pt (unwrapU x >>= k_s) i_t.
  Proof using.
    iIntros "H". unfold unwrapU. destruct x.
    { ired. iApply "H". auto. }
    { unseal; iIntros "P". iApply isim_triggerUB_src. }
  Qed.

  Lemma wsim_unwrapN_src X (x : option X) k_s i_t :
    (∃ x', ⌜x = Some x'⌝ ∗ sim Ep g RR ps pt (k_s x') i_t) ⊢
    sim Ep g RR ps pt (unwrapN x >>= k_s) i_t.
  Proof using. iIntros "H". iDestruct "H" as (x') "[% H]". subst. ired. iApply "H". Qed.

  Lemma wsim_asm_src (P : Prop) k_s i_t :
    (⌜P⌝ -∗ (sim Ep g RR true pt (k_s tt) i_t)) ⊢
    sim Ep g RR ps pt (assume P >>= k_s) i_t.
  Proof using.
    unseal; iIntros "RR I". iApply isim_asm_src; eauto.
    iIntros "%H"; iApply ("RR" $! H with "I"); iFrame.
  Qed.

  Lemma wsim_asm_tgt (P : Prop) i_s k_t :
    ⌜P⌝ ∗ sim Ep g RR ps true i_s (k_t tt) ⊢
    sim Ep g RR ps pt i_s (assume P >>= k_t).
  Proof using.
    unseal; iIntros "[%HP SIM] I". iApply isim_asm_tgt; eauto. iApply ("SIM" with "I").
  Qed.

  Lemma wsim_guar_src (P : Prop) k_s i_t :
    ⌜P⌝ ∗ sim Ep g RR true pt (k_s tt) i_t ⊢
    sim Ep g RR ps pt (guarantee P >>= k_s) i_t.
  Proof using.
    unseal; iIntros "[P H] I". iApply isim_guar_src; eauto. iFrame.
    iApply ("H" with "I").
  Qed.

  Lemma wsim_guar_tgt (P : Prop) i_s k_t :
    (⌜P⌝ -∗ sim Ep g RR ps true i_s (k_t tt)) ⊢
    sim Ep g RR ps pt i_s (guarantee P >>= k_t).
  Proof using.
    unseal; iIntros "RR I". iApply isim_guar_tgt; eauto.
    iIntros "%H"; iApply ("RR" $! H with "I"); iFrame.
  Qed.

  Lemma wsim_mono_knowledge g0 i_s i_t
      (MON1 : ∀ Rs Rt RR ps pt i_src i_tgt,
        @g0 Rs Rt RR ps pt i_src i_tgt ⊢ |==> @g Rs Rt RR ps pt i_src i_tgt) :
    sim Ep g0 RR ps pt i_s i_t ⊢ sim Ep g RR ps pt i_s i_t.
  Proof using. unseal. iIntros "SIM I". iApply isim_mono_knowledge; et. iApply "SIM". et. Qed.

  Lemma wsim_mono RR0 i_s i_t
      (MONO : ∀ ret_src ret_tgt,
        RR0 ret_src ret_tgt ⊢ RR ret_src ret_tgt) :
    sim Ep g RR0 ps pt i_s i_t ⊢ sim Ep g RR ps pt i_s i_t.
  Proof using. unseal. iIntros "SIM I". iApply isim_mono; et. iApply "SIM". et. Qed.
  
  Lemma wsim_init_winv i_s i_t Ew E Ew' E':
    (winv (Ew', E') ∗ sim (Ew ∪ Ew', E ∪ E') g RR ps pt i_s i_t) ⊢
    sim (Ew, E) g RR ps pt i_s i_t.
  Proof using.
    unseal; iIntros "[P SIM] I".
    iApply isim_upd. iApply "SIM".
    iPoseProof (winv_merge with "[P I]") as "[I _]"; iFrame.
  Qed.

  Lemma wsim_fupd m Ew E1 E2 i_s i_t :
    =|m, Ew|={E2, E1}=> sim (Ew, E1) g RR ps pt i_s i_t ⊢
    sim (Ew, E2) g RR ps pt i_s i_t.
  Proof using.
    unseal; iIntros "SIM [O [E [%n [WA W]]]]".
    set (nm := n `max` m).
    iPoseProof (fupd_mon _ nm with "SIM") as "SIM"; first lia.
    iMod (wsatl_mon n nm with "[WA W]") as "[WA W]"; first lia; iFrame.
    rewrite invariants.uPred_fupd_unseal /invariants.uPred_fupd_def own_bupd_unseal /own_bupd.
    iMod ("SIM" with "[W E] O") as "[O [W [E SIM]]]"; iFrame.
    iApply "SIM"; iFrame.
  Qed.

  Lemma wsim_own_upd i_s i_t:
    (o=> sim Ep g RR ps pt i_s i_t)
    ⊢ sim Ep g RR ps pt i_s i_t.
  Proof using.
    destruct Ep as [Ew E2]; iIntros "SIM".
    iApply (wsim_fupd 0 _ E2). by iMod "SIM" as "$".
  Qed.

  Lemma wsim_upd i_s i_t:
    ( |==> sim Ep g RR ps pt i_s i_t)
    ⊢ sim Ep g RR ps pt i_s i_t.
  Proof using.
    iIntros "SIM".
    iApply wsim_own_upd. by iMod "SIM" as "$".
  Qed.

  (* Proofmode instances *)
  Global Instance wsim_elim_own_upd P p i_s i_t :
    ElimModal True p false (o=> P)%I P
      (sim Ep g RR ps pt i_s i_t)
      (sim Ep g RR ps pt i_s i_t).
  Proof using.
    rewrite /ElimModal bi.intuitionistically_if_elim /=.
    iIntros (_) "[HP SIM]".
    iApply wsim_own_upd. iMod "HP".
    by iApply ("SIM" with "HP").
  Qed.

  Global Instance wsim_elim_upd P p i_s i_t :
    ElimModal True p false ( |==> P)%I P
      (sim Ep g RR ps pt i_s i_t)
      (sim Ep g RR ps pt i_s i_t).
  Proof using.
    rewrite /ElimModal bi.intuitionistically_if_elim /=.
    iIntros (_) "[HP SIM]".
    iApply wsim_upd. iMod "HP".
    by iApply ("SIM" with "HP").
  Qed.

  Global Instance wsim_elim_fupd_gen Ew Ew' E0 E1 E2 n P p i_s i_t :
    ElimModal
      (E0 ⊆ E2 ∧ Ew' ⊆ Ew) p false
      (=|n, Ew'|={E0, E1}=> P)
      P
      (sim (Ew, E2) g RR ps pt i_s i_t)
      (sim (Ew, E1 ∪ (E2 ∖ E0)) g RR ps pt i_s i_t) | 10.
  Proof using.
    rewrite /ElimModal bi.intuitionistically_if_elim /=.
    iIntros ([??]) "[P SIM]".
    iApply (wsim_fupd n Ew (E1 ∪ E2 ∖ E0)). iMod "P".
    iModIntro. iApply ("SIM" with "P").
  Qed.

  Global Instance elim_fupd_wsim_same_mask Ew Ew' E1 E2 n p P i_s i_t :
    ElimModal
      (E1 ⊆ E2 ∧ Ew' ⊆ Ew) p false
      (=|n, Ew|={E1}=> P)
      P
      (sim (Ew, E2) g RR ps pt i_s i_t)
      (sim (Ew, E2) g RR ps pt i_s i_t).
  Proof using.
    rewrite /ElimModal bi.intuitionistically_if_elim.
    iIntros ([??]) "[> P SIM]"; rewrite -union_difference_L //; iApply ("SIM" with "P").
  Qed.

  Global Instance elim_fupd_wsim_simple Ew Ew' E0 E1 n P p i_s i_t :
    ElimModal
      (Ew' ⊆ Ew) p false
      (=|n, Ew'|={E0, E1}=> P)
      P
      (sim (Ew, E0) g RR ps pt i_s i_t)
      (sim (Ew, E1) g RR ps pt i_s i_t).
  Proof using.
    rewrite /ElimModal bi.intuitionistically_if_elim.
    iIntros (?) "[> P SIM]". rewrite difference_diag_L right_id_L; iApply "SIM"; done.
  Qed.

  Global Instance wpsim_add_modal_FUpd Ew E n P i_s i_t :
    AddModal (=|n, Ew|={E}=> P) P
             (sim (Ew, E) g RR ps pt i_s i_t).
  Proof using.
    unfold AddModal. iIntros "[H0 H1]". iMod "H0". iApply ("H1" with "H0").
  Qed.

  (* Primitive simulation rules *)
  Lemma wsim_isim i_s i_t :
    sim (∅,∅) g RR ps pt i_s i_t ⊢
    (winv (∅,∅) -∗ @isim Σ _ fl_s fl_t Ist g R_s R_t RR ps pt i_s i_t).
  Proof using.
    unseal; et.
  Qed.

  Lemma isim_wsim i_s i_t :
    (winv (∅,∅) -∗ @isim Σ _ fl_s fl_t Ist g R_s R_t RR ps pt i_s i_t)
    ⊢
    sim (∅,∅) g RR ps pt i_s i_t.
  Proof using.
    unseal. et.
  Qed.

  Lemma wsim_unfold Ew E i_s i_t :
    (winv (Ew, E) -∗ sim (∅,∅) g RR ps pt i_s i_t) ⊢
    sim (Ew, E) g RR ps pt i_s i_t.
  Proof using.
    unseal. iIntros "SIM PRE".
    iPoseProof (winv_split_empty with "[PRE]") as "[PRE PRE']"; et.
    iApply ("SIM" with "PRE"). done.
  Qed.

  Lemma wsim_fold Ew E i_s i_t :
    winv (Ew, E) ∗ sim (Ew, E) g RR ps pt i_s i_t ⊢
    sim (∅,∅) g RR ps pt i_s i_t.
  Proof using.
    unseal. iIntros "[PRE SIM] _". iApply ("SIM" with "PRE").
  Qed.

End wsim.

Lemma wsim_consequence
  `{!crisG Γ Σ α β τ _S _I}
  `{!stateGS Σ}
  fl_s fl_t Ist
  Ep g {Rs Rt} PP QQ ps pt i_s i_t
  : (∀ r_src r_tgt, PP r_src r_tgt -∗ QQ r_src r_tgt)
      ∗ wsim fl_s fl_t Ist Ep g Rs Rt PP ps pt i_s i_t
      ⊢ wsim fl_s fl_t Ist Ep g Rs Rt QQ ps pt i_s i_t.
Proof.
  iIntros "[LE SIM]".
  iApply wsim_mono; cycle 1.
  - iApply wsim_frame. iSplitL "LE".
    + iApply "LE".
    + iApply "SIM".
  - iIntros (r_s r_t) "[LE H]".
    iApply "LE"; et.
Qed.

Lemma wsim_bind_strong `{!crisG Γ Σ α β τ _S _I} `{!stateGS Σ}
    fl_s fl_t Ist {R_s R_t Qs Qt} E1 E2 g RR ps pt i_s i_t k_s k_t :
  wsim fl_s fl_t Ist (E1, E2) g Qs Qt
    (λ ret_src ret_tgt,
      winv (E1, E2) ∗
      wsim fl_s fl_t Ist (E1, E2) g R_s R_t RR false false
        (k_s ret_src) (k_t ret_tgt))
    ps pt i_s i_t
  ⊢ wsim fl_s fl_t Ist (E1, E2) g R_s R_t RR ps pt
      (i_s >>= k_s) (i_t >>= k_t).
Proof using.
  iIntros "SIM". iApply wsim_bind; iSplitL; iFrame.
  iIntros (? ?) "[W SIM]". iApply wsim_fold; iFrame.
Qed.

(* Lemmas for prophecies *)
Section FancyReal.
  Context `{!crisG Γ Σ α β τ _S _I}.
  Context `{!stateGS Σ}.

  Context (fl_s fl_t : gmap fname (option (Any.t → itree crisE Any.t))).
  Context (Ist : iProp Σ).
  Context (R_s R_t : Type).

  Context (Ep : coPset * coPset).
  Context (g : rel).
  Context (RR : retr_type Σ R_s R_t).
  Context (ps pt : bool).

  Local Notation sim Ep g := (wsim fl_s fl_t Ist Ep g R_s R_t).

  (* Precise Pre & Post conditions *)
  Lemma wsim_ru_src_advanced_general (pp: _→_→Prop) k_s i_t :
    (∃ (I P : iProp Σ),
      I ∗ precise P ∗
      (∀ pre post (VS: pp pre post), ∃ T, (I -∗ winv Ep -∗ pre -∗ □ T) ∗ (□ T -∗ pre ==∗ P ∗ post)) ∗
      (I -∗ P -∗ sim Ep g RR true pt (k_s ()) i_t)) ⊢
    sim Ep g RR ps pt (RealUpdate pp >>= k_s) i_t.
  Proof.
    rewrite wsim_eq /wsim_def.
    iIntros "[%I [%P [I [#Pre [Hsplit Hsim]]]]] W".
    iApply isim_ru_src_advanced_general. iExists _, _.
    iFrame "Pre". iSplitL "I W".
    { iCombine "I W" as "I". iApply "I". }
    iSplitL "Hsplit".
    { iIntros (? ? ?). iDestruct ("Hsplit" $! _ _ VS) as "[% [H ?]]"; iFrame.
      iIntros "[I W]". iApply ("H" with "I W"). }
    iIntros "[I W] P". iApply ("Hsim" with "I P W").
  Qed.

  Lemma wsim_ru_src_advanced {X} (pre post: X → _) k_s i_t :
    (∃ (I P : iProp Σ),
      I ∗ precise P ∗
      (∀ x, ∃ T, (I -∗ winv Ep -∗ pre x -∗ □ T) ∗ (□ T -∗ pre x ==∗ P ∗ post x)) ∗
      (I -∗ P -∗ sim Ep g RR true pt (k_s ()) i_t)) ⊢
    sim Ep g RR ps pt (RealUpdate (idx_to_rel pre post) >>= k_s) i_t.
  Proof.
    iIntros "[%[% [I [P [A B]]]]]".
    iApply (wsim_ru_src_advanced_general (idx_to_rel pre post)).
    iFrame. iIntros (???). rr in VS; des; subst. iApply "A".
  Qed.
  
  Lemma wsim_ru_src_general (pp: _→_→Prop) k_s i_t :
    (∃ (P : iProp Σ),
      precise P ∗
      (∀ pre post (VS: pp pre post), pre ==∗ P ∗ post) ∗
      (P -∗ sim Ep g RR true pt (k_s()) i_t)) ⊢
    sim Ep g RR ps pt (RealUpdate pp >>= k_s) i_t.
  Proof using.
    rewrite wsim_eq /wsim_def.
    iIntros "[%P [Hprecise [Hsplit Hsim]]] W".
    iApply isim_ru_src_general.
    iExists P; iFrame.
    by iIntros "P"; iPoseProof ("Hsim" with "P") as "SIM"; iApply "SIM".
  Qed.

  Lemma wsim_ru_src {X} (pre post: X → _) k_s i_t :
    (∃ (P : iProp Σ),
      precise P ∗
      (∀ x, pre x ==∗ P ∗ post x) ∗
      (P -∗ sim Ep g RR true pt (k_s()) i_t)) ⊢
    sim Ep g RR ps pt (RealUpdate (idx_to_rel pre post) >>= k_s) i_t.
  Proof using.
    iIntros "[% [? [A ?]]]".
    iApply (wsim_ru_src_general (idx_to_rel pre post)).
    iFrame. iIntros (???). rr in VS; des; subst. iApply "A".
  Qed.
  
  Lemma wsim_ru_tgt_general
      (pp: _→_→Prop)
      i_s k_t :
    (∀ pr,
     (∀ pre post (VS: pp pre post), pre ==∗ Own pr ∗ post) -∗
     sim Ep g RR ps true i_s (trigger (AssumeRes pr);;; k_t ()))
    ⊢
    sim Ep g RR ps pt
      i_s
      (RealUpdate pp >>= k_t).
  Proof.
    rewrite wsim_eq /wsim_def.
    iIntros "H W".
    iApply isim_ru_tgt_general.
    iIntros "% U". iPoseProof ("H" with "U W") as "H". et.
  Qed.

  Lemma wsim_ru_tgt {X} (pre post: X → _)
      i_s k_t :
    (∀ pr,
     (∀ x, pre x ==∗ Own pr ∗ post x) -∗
     sim Ep g RR ps true i_s (trigger (AssumeRes pr);;; k_t ()))
    ⊢
    sim Ep g RR ps pt
      i_s
      (RealUpdate (idx_to_rel pre post) >>= k_t).
  Proof.
    iIntros "H".
    iApply (wsim_ru_tgt_general (idx_to_rel pre post)).
    iIntros (?) "A". iApply "H". iIntros (?) "H".
    assert (PF: ∃ x0, pre x = pre x0 ∧ post x = post x0); et.
    iSpecialize ("A" $! _ _ PF).
    iApply "A". et.
  Qed.
  
  Lemma wsim_ru_tgt_simple_general (pp: _→_→Prop) i_s k_t :
    (∃ pre post, ⌜pp pre post⌝ ∗ pre ∗
      (post -∗ sim Ep g RR ps true i_s (k_t ())))
    ⊢
    sim Ep g RR ps pt i_s (RealUpdate pp >>= k_t).
  Proof using.
    rewrite wsim_eq /wsim_def.
    iIntros "[%pre [%post [%VS [Hpre Hsim]]]] W".
    iApply isim_ru_tgt_simple_general; repeat (iExists _); iSplit; et.
    iFrame "Hpre"; iIntros "?"; iApply ("Hsim" with "[$] [$]").
  Qed.

  Lemma wsim_ru_tgt_simple {X} (pre post: X → _) i_s k_t :
    (∃ x, pre x ∗ (post x -∗ sim Ep g RR ps true i_s (k_t ())))
    ⊢
    sim Ep g RR ps pt i_s (RealUpdate (idx_to_rel pre post) >>= k_t).
  Proof using.
    iIntros "[% H]".
    iApply (wsim_ru_tgt_simple_general (idx_to_rel pre post)).
    iFrame. iPureIntro. rr; esplits; eauto.
  Qed.
End FancyReal.

Notation "E1 '------------------------------------------------------------------□' E2 '------------------------------------------------------------------∗' Ew E g ps pt '-------------------------------wsim-------------------------------' itr_src itr_tgt '{' RR '}'" :=
  (environments.envs_entails (Envs E1 E2 _)
    (wsim _ _ _ (Ew, E) g _ _ RR ps pt itr_src itr_tgt))
    (at level 50, only printing,
     format "E1 '------------------------------------------------------------------□' '//' E2 '------------------------------------------------------------------∗' '//' Ew  E  g  ps  pt '//' '-------------------------------wsim-------------------------------' '//' itr_src '//' '//' itr_tgt '//' '{'  RR  '}' ").

Notation "E1 '------------------------------------------------------------------□' Ew E g ps pt '-------------------------------wsim-------------------------------' itr_src itr_tgt '{' RR '}'" :=
  (environments.envs_entails (Envs E1 Enil _)
    (wsim _ _ _ (Ew, E) g _ _ RR ps pt itr_src itr_tgt))
    (at level 50, only printing,
     format "E1 '------------------------------------------------------------------□' '//' Ew  E  g  ps  pt '//' '-------------------------------wsim-------------------------------' '//' itr_src '//' '//' itr_tgt '//' '{'  RR  '}' ").

Notation "E2 '------------------------------------------------------------------∗' Ew E g ps pt '-------------------------------wsim-------------------------------' itr_src itr_tgt '{' RR '}'" :=
  (environments.envs_entails (Envs Enil E2 _)
    (wsim _ _ _ (Ew, E) g _ _ RR ps pt itr_src itr_tgt))
    (at level 50, only printing,
     format "E2 '------------------------------------------------------------------∗' '//' Ew  E  g  ps  pt '//' '-------------------------------wsim-------------------------------' '//' itr_src '//' '//' itr_tgt '//' '{'  RR  '}' ").

Notation "'------------------------------------------------------------------∗' Ew E g ps pt '-------------------------------wsim-------------------------------' itr_src itr_tgt '{' RR '}'" :=
  (environments.envs_entails (Envs Enil Enil _)
    (wsim _ _ _ (Ew, E) g _ _ RR ps pt itr_src itr_tgt))
    (at level 50, only printing,
     format "'------------------------------------------------------------------∗' '//' Ew  E  g  ps  pt  '//' '-------------------------------wsim-------------------------------' '//' itr_src '//' '//' itr_tgt '//' '{'  RR  '}' ").
