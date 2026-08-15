From CRIS.modules Require Import LMod LModTr.
From CRIS.simulations.gsim Require Import GSim GSimTactics GSimAux.
From CRIS.cancellation Require Import MInline ElimRel.

Local Ltac gnorm_itr :=
  match goal with
  | |- context [?A] =>
      match type of A with
      | itree crisE Any.t => pattern A; eapply eq_ind; [|symmetry; hnorm_itr]
      end
  end.

Lemma cancel_post `{!crisG Γ Σ α β τ _S _I} md sp :
  ∀ (rs0 : Σ) r_s r_t srcs tgts cid st ps pt vret Qo Qo' Qo'' itrS ktrT rs_diff
    (r : ∀ x x0, (x→x0→Prop)→smj→smj→itree coreE x→itree coreE x0→Prop)
    (WFS: SMod.cancellable md)
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
                 (SMod.to_mod ∅ (SMod.cancel md))) rs0)))
                 (cid, <[cid:=itr_s]> srcs))
          (st, r_s))
       (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
                 (SMod.to_mod_cancel sp md)) rs0)))
                 (cid, <[cid:=itr_t]> tgts))
          (st, r_t)))
    (EQLEN2 : length rs_diff = length srcs)
    (EQLEN : length srcs = length tgts)
    (REL : ∀ i x y z, rs_diff !! i = Some z →
      srcs !! i = Some x → tgts !! i = Some y → thread_rel sp cid i z x y)
    (WFR : ✓ r_s)
    (WFST: map_Forall (const is_Some) st)
    (RS : Own r_s ⊢ |==> ([∗ list] i ∈ rs_diff, Own i) ∗ Own r_t ∗
              TIDAUTH cid ∗ YIELDAUTH (length rs_diff))
    (LEN : cid < length srcs)
    (x2 : rs_diff !! cid = Some ε)
    (x0 : srcs !! cid = Some (ModTr.trans (tau;; tau;; itrS)))
    (x1 : tgts !! cid = Some (ModTr.trans ((x <- elim_postcond Qo Qo' vret;; vret' <- ktrT x;; elim_spawnee_postcond Qo'' vret'))))
    (RET: cid = 0 → match Qo'' with | Some Q => ∀ varg arg, Q varg arg ⊢ ⌜varg = arg⌝ | _ => True end)
    (KTR :
      (∃ Q, (Qo = Some Q ∨ (Qo = None ∧ Q = λ varg arg, ⌜varg = arg⌝%I)) ∧
        ∃ Q', (Qo' = Some Q' ∨ (Qo' = None ∧ Q' = λ varg arg, ⌜varg = arg⌝%I)) ∧
        (∀ ret, Q' vret ret ⊢ |==> Q vret ret) ∧
          upaco4 (elim_rel_def sp) bot4 Any.t ε itrS (ktrT vret))),

  gpaco7 _gsim (cpn7 _gsim) bot7 r (lstateT Σ * Any.t)%type
    (lstateT Σ * Any.t)%type cancel_eq ps pt
    (LModTr.interp_stateE Any.t
       (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
              (SMod.to_mod ∅ (SMod.cancel md))) rs0))) (cid, srcs))
       (st, r_s))
    (LModTr.interp_stateE Any.t
       (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
              (SMod.to_mod_cancel sp md)) rs0))) (cid, tgts))
       (st, r_t)).
Proof.
  i. eapply gsim_tau_src; eauto.
  eapply gsim_tau_src; [lookup_tac; do 2 f_equal|].
  rewrite !list_insert_insert.

  destruct KTR as [Q [[->|[-> ?]] [Q' [[-> |[-> ?]] ?]]]].
  { revert x1; rewrite /elim_postcond; gnorm_itr; intros x1.
    eapply gsim_Choose_tgt; [eapply x1|]. intros Fsp; s. ghcNormT.
    eapply gsim_tau_tgt; [lookup_tac; do 2 f_equal|]; try lia.
    rewrite !list_insert_insert. ghcNormT.
    eapply gsim_Guarantee_tgt; [lookup_tac; do 2 f_equal|]; try lia. intros rt2 [? Hrt2]; s.
    rewrite !list_insert_insert. ghcNormT.
    eapply gsim_tau_tgt; [lookup_tac; do 2 f_equal|]; try lia. ghcNormT.
    rewrite !list_insert_insert.
    eapply gsim_tau_tgt; [lookup_tac; do 2 f_equal|]; try lia. ghcNormT.
    rewrite !list_insert_insert.
    eapply gsim_tau_tgt; [lookup_tac; do 2 f_equal|]; try lia. ghcNormT.
    rewrite !list_insert_insert.
    eapply gsim_Take_tgt; [lookup_tac; do 2 f_equal|]; try lia.
    exists vret.
    rewrite !list_insert_insert. ghcNormT.
    eapply gsim_tau_tgt; [lookup_tac; do 2 f_equal|]; try lia.
    rewrite !list_insert_insert. ghcNormT.
    eapply gsim_Assume_tgt; [lookup_tac; do 2 f_equal|]; try lia.
    exists r_t; splits; auto.
    { apply (Own_wand_valid r_s); auto; iIntros "S"; iMod (RS with "S") as "[? [$ ?]]"; auto. }
    { rewrite Hrt2 (proj1 H); iIntros "> [>$ $] //". }
    rewrite !list_insert_insert. ghcNormT.
    eapply gsim_tau_tgt; [lookup_tac; do 2 f_equal|]; try lia.
    rewrite !list_insert_insert. ghcNormT.

    des; pclearbot. eapply KEY; et.
    { rewrite list_insert_id //. }
    { econs; eauto; f_equal; eauto. }
  }
  { ss; clarify.
    revert x1; rewrite /elim_postcond; gnorm_itr; intros x1.
    eapply gsim_tau_tgt; [eapply x1|]. ghcNormT.
    eapply gsim_tau_tgt; [lookup_tac; do 2 f_equal|]; try lia.
    rewrite !list_insert_insert. ghcNormT.
    eapply gsim_Take_tgt; [lookup_tac; do 2 f_equal|]; try lia.
    exists vret.
    rewrite !list_insert_insert. ghcNormT.
    eapply gsim_tau_tgt; [lookup_tac; do 2 f_equal|]; try lia.
    rewrite !list_insert_insert. ghcNormT.
    eapply gsim_Assume_tgt; [lookup_tac; do 2 f_equal|]; try lia.
    exists r_t; splits; auto.
    { apply (Own_wand_valid r_s); auto; iIntros "S"; iMod (RS with "S") as "[? [$ ?]]"; auto. }
    { des; clarify. iIntros "$"; iApply H0; auto. }
    rewrite !list_insert_insert. ghcNormT.
    eapply gsim_tau_tgt; [lookup_tac; do 2 f_equal|]; try lia.
    rewrite !list_insert_insert. ghcNormT.

    des; pclearbot. eapply KEY; et.
    { rewrite list_insert_id //. }
    { eapply thread_rel_body; cycle 1; eauto; i; clarify; auto. }
  }
  { revert x1; rewrite /elim_postcond; gnorm_itr; intros x1.
    eapply gsim_Choose_tgt; [eapply x1|]. intros ret; s. ghcNormT.
    eapply gsim_tau_tgt; [lookup_tac; do 2 f_equal|]; try lia.
    rewrite !list_insert_insert. ghcNormT.
    eapply gsim_Guarantee_tgt; [lookup_tac; do 2 f_equal|]; try lia. intros rt2 [? Hrt2]; s.
    rewrite !list_insert_insert. ghcNormT.
    eapply gsim_tau_tgt; [lookup_tac; do 2 f_equal|]; try lia. ghcNormT.
    rewrite !list_insert_insert.
    eapply gsim_tau_tgt; [lookup_tac; do 2 f_equal|]; try lia. ghcNormT.
    rewrite !list_insert_insert.
    eapply gsim_tau_tgt; [lookup_tac; do 2 f_equal|]; try lia. ghcNormT.
    rewrite !list_insert_insert.

    assert (vret = ret).
    { eapply (Own_pure_soundness r_t).
      { apply (Own_wand_valid r_s); auto; iIntros "S"; iMod (RS with "S") as "[? [$ ?]]"; auto. }
      des; clarify. rewrite Hrt2 H0; iIntros "> [>-> ?] //".
    }
    des; pclearbot. eapply KEY; et.
    { rewrite list_insert_id // RS Hrt2. iIntros "> [$ [> [? $] $]] //". }
    { econs; eauto; subst; ss; f_equal; rewrite bind_ret_r //. }
  }
  revert x1; rewrite /elim_postcond; gnorm_itr; intros x1.
  eapply gsim_tau_tgt; [eapply x1|]. ghcNormT.
  eapply gsim_tau_tgt; [lookup_tac; do 2 f_equal|]; try lia.
  rewrite !list_insert_insert. ghcNormT.

  des; pclearbot. eapply KEY; et.
  { rewrite list_insert_id //. }
  { econs; eauto; f_equal; rewrite bind_ret_r //. }
(*SLOW*)Qed.
