From CRIS.modules Require Import LMod LModTr.
From CRIS.simulations.gsim Require Import GSim GSimTactics GSimAux.
From CRIS.cancellation Require Import ElimRel.

Local Ltac gnorm_itr :=
  match goal with
  | |- context [?A] =>
      match type of A with
      | itree crisE Any.t => pattern A; eapply eq_ind; [|symmetry; hnorm_itr]
      end
  end.

Lemma list_lookup_exists {A} (l: list A) n (LT: n < length l) :
  ∃ x, l !! n = Some x.
Proof.
  gen n. induction l; ss; [nia|]; i.
  destruct n; [esplits; eauto|].
  eapply Nat.succ_lt_mono in LT. hexploit IHl; eauto.
Qed.

Lemma cancel_yield `{!crisG Γ Σ α β τ _S _I} md sp ntid :
  CANCEL_GOAL md sp (HoareYieldE false ntid) (HoareYieldE true ntid).
Proof.
  r; i. subst. ss.
  revert x1; gnorm_itr; intros x1. revert x0; gnorm_itr; intros x0.

  eapply gsim_Choose_tgt; try apply x1. intros stid; s. ghcNormT.
  eapply gsim_tau_tgt; [lookup_tac; do 2 f_equal|]; try lia.
  rewrite !list_insert_insert. ghcNormT.
  eapply gsim_Guarantee_tgt; [lookup_tac; do 2 f_equal|]; try lia. intros rt2 [? Hrt2]; s.
  rewrite !list_insert_insert. ghcNormT.
  eapply gsim_tau_tgt; [lookup_tac; do 2 f_equal|]; try lia.
  rewrite !list_insert_insert. ghcNormT.
  eapply gsim_Yield_tgt; [lookup_tac; do 2 f_equal|]; try lia.
  rewrite !list_insert_insert. ghcNormT.
  eapply gsim_Yield_src; try apply x0. ghcNormS.

  assert (EQ : stid = cid).
  { eapply Own_pure_soundness with (a:=r_s); eauto.
    iIntros "S"; iPoseProof (RS with "S") as ">[_ [R [TA _]]]".
    iPoseProof (Hrt2 with "R") as ">[[T _] _]".
    iApply (TidToken_agree with "T"); iFrame.
  }
  subst.

  destruct (decide (ntid < length rs_diff)); cycle 1.
  { giter_s; s. destruct (<[cid:=_]> srcs !! ntid) eqn:FIND.
    { eapply lookup_lt_Some in FIND. rewrite length_insert in FIND. nia. }
    { gsteps_s. ss. }
  }
  
  assert (RS0: Own r_s ⊢
        |==> (([∗ list] i ∈ rs_diff, Own i) ∗ TIDAUTH ntid ∗ YIELDAUTH (length rs_diff)) ∗
        ((TID ntid ∗ YIELD ntid ∗ winv (⊤, ⊤)) ∗ Own rt2)).
  { rewrite RS Hrt2. iIntros ">[$ [>[[T [$ $]] $] [TA $]]]".
    iApply (TidToken_upd with "[TA T]"); iFrame.
  }
  hexploit (Own_bupd_split); eauto.
  intros [r_t1 [r_t2 [Hr_t1 [Hr_t2 [Hr_t3 Hr_t_valid]]]]].

  assert (TVALID: ✓ r_t2).
  { eapply Own_wand_valid with (a1:=r_s); eauto.
    rewrite Hr_t1. iIntros ">[_ $]"; eauto. }
  destruct (decide (ntid = cid)); subst.
  { eapply gsim_tau_tgt; [lookup_tac; do 2 f_equal|]; try lia.
    rewrite !list_insert_insert. ghcNormT.
    eapply gsim_Assume_tgt; [lookup_tac; do 2 f_equal|]; try lia.
    exists r_t2; splits; auto.
    { rewrite Hr_t3; apply bupd_intro. }
    rewrite !list_insert_insert. ghcNormT.
    eapply gsim_tau_tgt; [lookup_tac; do 2 f_equal|]; try lia.
    rewrite !list_insert_insert. ghcNormT.
    eapply gsim_tau_src; [lookup_tac; do 2 f_equal|].
    rewrite !list_insert_insert. ghcNormS.

    eapply KEY with (r_diff:=ε); eauto.
    { rewrite length_insert list_insert_id //.
      iIntros "S". iPoseProof (Hr_t1 with "S") as ">[S $]"; iStopProof.
      rewrite Hr_t2. eapply bupd_intro. }
    { eapply thread_rel_body; eauto. eapply KTR. }
  }
  {
    revert n; clear_until l; intros n.
    assert (Hntid : is_Some (rs_diff !! ntid)).
    { rewrite lookup_lt_is_Some //. }
    destruct Hntid as [rsntid Hntid].
    assert (RS0: Own r_s ⊢
                  |==> (([∗ list] i ∈ <[ntid:=ε]> rs_diff, Own i) ∗ TIDAUTH ntid ∗ YIELDAUTH (length rs_diff)) ∗
                  ((TID ntid ∗ YIELD ntid ∗ winv (⊤, ⊤)) ∗ Own (rsntid) ∗ Own rt2)).
    { rewrite RS Hrt2. iIntros ">[A [>[[T [$ $]] $] [TA $]]]".
      iPoseProof (TidToken_upd with "[TA T]") as "> [$ $]"; iFrame.
      iPoseProof (big_sepL_insert_acc with "A") as "[$ A]"; auto using Hntid.
      iApply "A"; iApply Own_unit.
    }
    hexploit (Own_bupd_split); eauto.
    intros [r_t1 [r_t2 [Hr_t1 [Hr_t2 [Hr_t3 Hr_t_valid]]]]].

    assert (TVALID: ✓ r_t2).
    { eapply Own_wand_valid with (a1:=r_s); eauto.
      rewrite Hr_t1. iIntros ">[_ $]"; eauto. }

    do 2 dup l. rename l into SRC, l0 into TGT, l1 into RES.
    rewrite EQLEN2 in SRC. rewrite EQLEN2 EQLEN in TGT.
    dup SRC; dup TGT; dup RES.
    eapply list_lookup_exists in SRC, TGT, RES; des.
    hexploit REL; eauto; intros RELTID. inv RELTID.
    { (* first execution *)
      destruct fspo as [fsp|].
      { ss.
        eapply gsim_Take_tgt.
        { rewrite !list_lookup_insert_ne // TGT /=; do 2 f_equal; hnorm_itr. }
        des; eexists (FSpec_mk P Q _); eauto; ghcNormT.
        eapply gsim_tau_tgt; [lookup_tac; do 2 f_equal|]; try lia.
        rewrite !list_insert_insert. ghcNormT.
        eapply gsim_Take_tgt; [lookup_tac; do 2 f_equal|]; try lia. exists varg.
        rewrite !list_insert_insert. ghcNormT.
        eapply gsim_tau_tgt; [lookup_tac; do 2 f_equal|]; try lia.
        rewrite !list_insert_insert. ghcNormT.
        eapply gsim_Assume_tgt; [lookup_tac; do 2 f_equal|]; try lia.
        exists r_t2; splits; auto.
        { rewrite Hr_t3 H2.
          iIntros "[[? [? ?]] [A $]] //". iApply ("A" with "[$] [$] [$]").
        }
        rewrite !list_insert_insert. ghcNormT.
        eapply gsim_tau_tgt; [lookup_tac; do 2 f_equal|]; try lia.
        rewrite !list_insert_insert. rewrite !bind_ret_l.
        eapply gsim_tau_src.
        { rewrite !list_lookup_insert_ne // SRC /=; do 2 f_equal; hnorm_itr. }
        eapply gsim_tau_src; [lookup_tac; do 2 f_equal|]; try lia.
        rewrite !list_insert_insert. ghcNormS.
        zprogress. gbase.
        eapply CIH with (rs_diff:=<[ntid:=ε]>rs_diff); eauto.
        { r. esplits; try rewrite !length_insert //.
          ii. destruct (decide (ntid = i)); subst.
          { rewrite list_lookup_insert ?length_insert // in H3.
            rewrite list_lookup_insert ?length_insert // in H6.
            rewrite list_lookup_insert ?length_insert // in H7.
            clarify.
            eapply thread_rel_body; cycle 1; eauto.
            { instantiate (1:=Some Q); f_equal; grind. }
            i; subst; lia.
          }
          { destruct (decide (cid = i)); subst.
            { rewrite list_lookup_insert_ne // ?length_insert // in H3.
              rewrite list_lookup_insert_ne // list_lookup_insert ?length_insert // in H6.
              rewrite list_lookup_insert_ne // list_lookup_insert ?length_insert // -?EQLEN // in H7.
              clarify. ired. eapply thread_rel_yield; eauto. eapply KTR.
            }
            rewrite !list_lookup_insert_ne // ?length_insert // in H3.
            rewrite !list_lookup_insert_ne // ?length_insert // in H6.
            rewrite !list_lookup_insert_ne // ?length_insert // in H7.
            hexploit REL; eauto; i. inv H8.
            { eapply thread_rel_spawn; cycle 4; eauto. }
            { eapply thread_rel_yield; eauto. }
          }
        }
        { rewrite Hr_t1 Hr_t2 length_insert. iIntros ">[[$ $] $] //". }
      }
      { ss; subst.
        eapply gsim_tau_tgt.
        { rewrite !list_lookup_insert_ne // TGT /=; do 2 f_equal; hnorm_itr. }
        ghcNormT.
        eapply gsim_tau_tgt; [lookup_tac; do 2 f_equal|].
        rewrite !list_insert_insert. ghcNormT.
        eapply gsim_tau_src.
        { rewrite !list_lookup_insert_ne // SRC /=; do 2 f_equal; hnorm_itr. }
        ghcNormS.
        eapply gsim_tau_src; [lookup_tac; do 2 f_equal|]; try lia.
        rewrite !list_insert_insert. ghcNormS.
        zprogress. gbase.
        eapply CIH with (rs_diff:=<[ntid:=ε]>rs_diff); eauto.
        { r. esplits; try rewrite !length_insert //.
          ii. destruct (decide (ntid = i)); subst.
          { rewrite list_lookup_insert ?length_insert // in H2.
            rewrite list_lookup_insert ?length_insert // in H3.
            rewrite list_lookup_insert ?length_insert // in H6.
            clarify.
            eapply thread_rel_body; cycle 1; eauto; try instantiate (1:=None); ss.

            des. depdes H4. des; subst.
            assert (Own r_s ⊢ ⌜varg = arg⌝).
            { rewrite RS0 H2. iIntros "> [_ [[T [Y W]] [P _]]]".
              iSpecialize ("P" with "Y T W"); et.
            }
            eapply Own_pure_soundness in H0; subst; et.
          }
          { destruct (decide (cid = i)); subst.
            { rewrite list_lookup_insert_ne // ?length_insert // in H2.
              rewrite list_lookup_insert_ne // list_lookup_insert ?length_insert // in H3.
              rewrite list_lookup_insert_ne // list_lookup_insert ?length_insert // -?EQLEN // in H6.
              clarify. ired. eapply thread_rel_yield; eauto. eapply KTR.
            }
            rewrite !list_lookup_insert_ne // ?length_insert // in H2.
            rewrite !list_lookup_insert_ne // ?length_insert // in H3.
            rewrite !list_lookup_insert_ne // ?length_insert // in H6.
            hexploit REL; eauto; i. inv H7.
            { eapply thread_rel_spawn; cycle 4; eauto. }
            { eapply thread_rel_yield; eauto. }
          }
        }
        { rewrite Hr_t1 Hr_t2 length_insert. iIntros ">[[$ $] A] //".
          by rewrite Hr_t3; iDestruct "A" as "[? [? $]]".
        }
      }
    }
    (* middle of execution *)
    eapply gsim_tau_tgt.
    { rewrite !list_lookup_insert_ne // TGT /=; do 2 f_equal; hnorm_itr. }
    ghcNormT.
    eapply gsim_Assume_tgt; [lookup_tac; do 2 f_equal|]; try lia.
    exists r_t2; splits; auto.
    { rewrite Hr_t3. iIntros "[[? [? ?]] [A $]]"; iFrame; auto. }
    ghcNormT.
    eapply gsim_tau_tgt; [lookup_tac; do 2 f_equal|]; try lia.
    rewrite !list_insert_insert. ghcNormT.
    eapply gsim_tau_src.
    { rewrite !list_lookup_insert_ne // SRC /=; do 2 f_equal; hnorm_itr. }

    zprogress.
    gbase. eapply CIH with (rs_diff:=<[ntid:=ε]>rs_diff); eauto.
    { r; esplits; try rewrite !length_insert //.
      ii. destruct (decide (ntid = i)); subst.
      { rewrite list_lookup_insert ?length_insert // in H2.
        rewrite list_lookup_insert ?length_insert // in H3.
        rewrite list_lookup_insert ?length_insert // in H5.
        clarify. eapply thread_rel_body; cycle 1; eauto.
      }
      {
        destruct (decide (cid = i)); subst.
        {
          rewrite list_lookup_insert_ne // ?length_insert // in H2.
          rewrite list_lookup_insert_ne // list_lookup_insert ?length_insert // in H3.
          rewrite list_lookup_insert_ne // list_lookup_insert ?length_insert // -?EQLEN // in H5.
          clarify. ired. eapply thread_rel_yield; eauto. eapply KTR.
        }
        rewrite !list_lookup_insert_ne // ?length_insert // in H2.
        rewrite !list_lookup_insert_ne // ?length_insert // in H3.
        rewrite !list_lookup_insert_ne // ?length_insert // in H5.
        hexploit REL; eauto; i. inv H6.
        { eapply thread_rel_spawn; cycle 4; eauto. }
        { eapply thread_rel_yield; eauto. }
      }
    }
    { rewrite Hr_t1 Hr_t2 -!assoc length_insert. iIntros ">($ & $ & $ & $) //". }
  }
  Unshelve. eauto.
(*SLOW*)Qed.
