From CRIS.common Require Import Common ConcRA StatePredicate.
From iris.proofmode Require Import proofmode.
From CRIS.modules Require Import LMod Mod SMod Sp.
From CRIS.simulations.lsim Require Import LSim LSimTactics.
From CRIS.simulations.msim Require Import MSim ISim TacticsCommon ITactics ISimFacts WSim.

Set Implicit Arguments.

Section STATE_EQ_RULES.

  Context `{!crisG Γ Σ α β τ _S _I}.
  Context `{STATE : !stateGS Σ}.

  Lemma wsim_sput_eq fl_s fl_t S Ep g {Rs Rt} RR ps pt k v' k_s k_t
      (IN : k.1 ∈ S) :
    state_eq S STATE ∗
      (state_eq S STATE -∗
        wsim fl_s fl_t (state_eq S STATE) Ep g
          Rs Rt RR true true (k_s tt) (k_t tt)) ⊢
    wsim fl_s fl_t (state_eq S STATE) Ep g
      Rs Rt RR ps pt
      (trigger (SPut k v') >>= k_s) (trigger (SPut k v') >>= k_t).
  Proof.
    iIntros "[EQ SIM]".
    iPoseProof (state_eq_put S k v' IN with "EQ") as
      (ov) "(SRC & TGT & CLOSE)".
    destruct ov as [v|].
    - iEval (rewrite /state_cell_src /state_cell_tgt /=) in "SRC TGT".
      iApply wsim_sput_src. iFrame "SRC". iIntros "SRC".
      iApply wsim_sput_tgt. iFrame "TGT". iIntros "TGT".
      iApply "SIM". iApply ("CLOSE" with "[$SRC $TGT]").
    - iEval (rewrite /state_cell_src /state_cell_tgt /=) in "SRC TGT".
      iApply wsim_sput_src_uninit. iFrame "SRC". iIntros "SRC".
      iApply wsim_sput_tgt_uninit. iFrame "TGT". iIntros "TGT".
      iApply "SIM". iApply ("CLOSE" with "[$SRC $TGT]").
  Qed.

  Lemma wsim_sget_eq fl_s fl_t S Ep g {Rs Rt} RR ps pt k k_s k_t
      (IN : k.1 ∈ S) :
    state_eq S STATE ∗
      (∀ v, state_eq S STATE -∗
        wsim fl_s fl_t (state_eq S STATE) Ep g
          Rs Rt RR true true (k_s v) (k_t v)) ⊢
    wsim fl_s fl_t (state_eq S STATE) Ep g
      Rs Rt RR ps pt
      (trigger (SGet k) >>= k_s) (trigger (SGet k) >>= k_t).
  Proof.
    iIntros "[EQ SIM]".
    iPoseProof (state_eq_get S k IN with "EQ") as
      (ov) "(SRC & TGT & CLOSE)".
    destruct ov as [v|].
    - iEval (rewrite /state_cell_src /state_cell_tgt /=) in "SRC TGT".
      iApply wsim_sget_src. iFrame "SRC". iIntros "SRC".
      iApply wsim_sget_tgt. iFrame "TGT". iIntros "TGT".
      iApply ("SIM" $! v). iApply ("CLOSE" with "[$SRC $TGT]").
    - iEval (rewrite /state_cell_src /state_cell_tgt /=) in "SRC TGT".
      iApply wsim_sget_src_uninit. iFrame "SRC". iIntros "SRC".
      iApply wsim_sget_tgt_uninit. iFrame "TGT". iIntros "TGT".
      iApply ("SIM" $! (tt↑)). iApply ("CLOSE" with "[$SRC $TGT]").
  Qed.
End STATE_EQ_RULES.
