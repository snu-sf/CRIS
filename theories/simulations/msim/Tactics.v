From iris.proofmode Require Import proofmode.
From CRIS.common Require Import Common ConcRA.
From CRIS.modules Require Import FSpec.
From CRIS.simulations Require Import ISim WSim.
From CRIS.simulations.msim Require Export TacticsCommon ITactics WTactics.

Tactic Notation "iwcase" tactic0(itac) tactic0(wtac) :=
  match goal with
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _) ] => itac
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _) ] => wtac
  end.

(** cSimpl: simplify various expressions **)

Lemma copset_diff_union (E E': coPset)
  (SUB: E' ⊆ E)
  :
  (E ∖ E') ∪ E' = E.
Proof.
  eapply leibniz_equiv.
  rewrite difference_union comm subseteq_union_1; et.
Qed.

Lemma copset_union_diff (E E': coPset)
  (SUB: E ## E')
  :
  (E ∪ E') ∖ E'  = E.
Proof.
  eapply leibniz_equiv.
  rewrite difference_union_distr_l difference_diag right_id.
  rewrite difference_disjoint_L; et.
Qed.

Ltac cSimpl_copset :=
  match goal with
  | |- context[(@union coPset coPset_union (@difference coPset coPset_difference ?E ?E') ?E')] =>
    replace ((E ∖ E') ∪ E') with E by (rewrite copset_diff_union; et; set_solver)
  | |- context[(@difference coPset coPset_difference (@union coPset coPset_union ?E ?E') ?E')] =>
    replace ((E ∪ E') ∖ E') with E by (rewrite copset_union_diff; et; set_solver)
  | |- context[(@difference coPset coPset_difference ?E ?E)] =>
    replace (E ∖ E) with (∅ : coPset) by set_solver
  | |- context[(@union coPset coPset_union ∅ ?E)] =>
    replace (∅ ∪ E) with E by set_solver
  | |- context[(@union coPset coPset_union ?E ∅)] =>
    replace (E ∪ ∅) with E by set_solver
  end.

Ltac cSimpl_des :=
  ss; des_safe; subst;
  (hrepeat do 1 match goal with
    | [v: () |- _] => destruct v
    | [H: (_,_) = (_,_) |- _] => inv H
    end);
  ss.

Ltac cSimpl :=
  (hrepeat do 1 match goal with
     | [|- context[environments.Esnoc _ ?H (True%I)]] => iClear H
     | [|- context[environments.Esnoc _ ?H (emp%I)]] => iClear H
     end);
  cSimpl_des;
  try (rewrite -> !Any.pair_split in * );
  try (rewrite -> !Any.upcast_downcast in * );
  try (rewrite -> !SAny.pair_split in * );
  try (rewrite -> !SAny.upcast_downcast in * );
  (hrepeat do 1 match goal with [G: Any.downcast _ = Some _ |-_] =>
    apply Any.downcast_upcast in G; inv G; ss
   end);
  (hrepeat do 1 match goal with [G: Any.upcast _ = Any.upcast _ |-_] =>
    apply Any.upcast_inj in G; destruct G as [_ G]; red in G; depdes G; ss
   end);
  (hrepeat do 1 match goal with [G: SAny.downcast _ = Some _ |-_] =>
    apply SAny.downcast_upcast in G; inv G; ss
   end);
  (hrepeat do 1 match goal with [G: SAny.upcast _ = SAny.upcast _ |-_] =>
    apply SAny.upcast_inj in G; destruct G as [_ G]; red in G; depdes G; ss
   end);
  (hrepeat do 1 match goal with [G: Some _ = Some _ |- _] =>
    depdes G; ss
   end);
  try (rewrite -> !Any.pair_split in * );
  try (rewrite -> !Any.upcast_downcast in * );
  try (rewrite -> !SAny.pair_split in * );
  try (rewrite -> !SAny.upcast_downcast in * );
  cSimpl_des;
  (hrepeat do 1 cSimpl_copset);
  simpl_sp;
  move_aux.

(** prependRetS r :  turn "t" to "_ <- ret r;; t" in the source **)

Tactic Notation "prependRetS" uconstr(r) :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  only_itree_s;
  match goal with [|-_ _ (_ ?t _)] =>
    rewrite -(bind_ret_l r (fun _ => t))
  end;
  show_until marker.

(** prependRetT r :  turn "t" to "_ <- ret r; t" in the target **)

Tactic Notation "prependRetT" uconstr(r) :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  only_itree_t;
  match goal with [|-_ _ (_ _ ?t)] =>
    rewrite -(bind_ret_l r (fun _ => t))
  end;
  show_until marker.

(** appendRetS :  turn "t" to "r <- t; ret r" in the source **)

Tactic Notation "appendRetS" :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  only_itree_s;
  match goal with [|-_ _ (_ ?t _)] =>
    rewrite -(bind_ret_r t)
  end;
  show_until marker.

(** appendRetT :  turn "t" to "r <- t; ret r" in the target **)

Tactic Notation "appendRetT" :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  only_itree_t;
  match goal with [|-_ _ (_ _ ?t)] =>
    rewrite -(bind_ret_r t)
  end;
  show_until marker.

(* unfold tactics *)

Ltac unfoldIterS :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  only_itree_s;
  rewrite unfold_iter;
  show_until marker.

Ltac unfoldIterT :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  only_itree_t;
  rewrite unfold_iter;
  show_until marker.

Ltac unfoldIterCS :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  only_itree_s;
  rewrite unfold_iterC;
  show_until marker.

Ltac unfoldIterCT :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  only_itree_t;
  rewrite unfold_iterC;
  show_until marker.

(** cHideR/cShowR: hide/show the return relation **)

Definition cris_r {A} (K: A) := K.

Lemma abstract_ret_rel `{Σ: GRA} (H: environments.envs _) Rs Rt
  (sim: retr_type Σ Rs Rt → bool → bool → retr_type Σ (itree crisE Rs) (itree crisE Rt))
  rr ps pt src tgt
  :
  (let RR := cris_r rr in
   environments.envs_entails H (sim RR ps pt src tgt))
  -> environments.envs_entails H (sim rr ps pt src tgt).
Proof. et. Qed.

Lemma abstract_ret_rel_gen `{Σ: GRA} (H: environments.envs _) Rs Rt
  (sim: retr_type Σ Rs Rt → bool → bool → retr_type Σ (itree crisE Rs) (itree crisE Rt))
  (f: iProp Σ → iProp Σ) rr ps pt src tgt
  :
  (let RR := cris_r rr in
   environments.envs_entails H (f (sim RR ps pt src tgt)))
  -> environments.envs_entails H (f (sim rr ps pt src tgt)).
Proof. et. Qed.

Ltac _cShowR :=
  match goal with
  H := cris_r _ |- _ => unfold cris_r in H; subst H
  end.

Ltac cShowR := try _cShowR.

Ltac _cHideR :=
  let RR := fresh "RR__" in
  first[eapply abstract_ret_rel|eapply abstract_ret_rel_gen]; intros RR; move RR at top.
                                                                              
Ltac cHideR :=
  try (cShowR; _cHideR).
    
(** cHideS/cShowS: hide/show continuation in src **)

Definition cris_s {A} (K: A) := K.

Lemma abstract_cont_src `{Σ: GRA} (H: environments.envs _) Rs Rt
  (sim: retr_type Σ (itree crisE Rs) (itree crisE Rt))
  T (itrs: itree _ T) K itrt
  :
  (let CONT := cris_s K in
   environments.envs_entails H (sim (itrs >>= CONT) itrt))
  -> environments.envs_entails H (sim (itrs >>= K) itrt).
Proof. et. Qed.

Lemma abstract_cont_src_gen `{Σ: GRA} (H: environments.envs _) Rs Rt
  (sim: retr_type Σ (itree crisE Rs) (itree crisE Rt))
  (f: iProp Σ → iProp Σ) T (itrs: itree _ T) K itrt
  :
  (let CONT := cris_s K in
   environments.envs_entails H (f (sim (itrs >>= CONT) itrt)))
  -> environments.envs_entails H (f (sim (itrs >>= K) itrt)).
Proof. et. Qed.

Lemma abstract_tau_src `{Σ: GRA} (H: environments.envs _) Rs Rt
  (sim: retr_type Σ (itree crisE Rs) (itree crisE Rt))
  itrs itrt
  :
  (let CONT := cris_s itrs in
   environments.envs_entails H (sim (tau;; CONT) itrt))
  -> environments.envs_entails H (sim (tau;; itrs) itrt).
Proof. et. Qed.

Lemma abstract_tau_src_gen `{Σ: GRA} (H: environments.envs _) Rs Rt
  (sim: retr_type Σ (itree crisE Rs) (itree crisE Rt))
  (f: iProp Σ → iProp Σ) itrs itrt
  :
  (let CONT := cris_s itrs in
   environments.envs_entails H (f (sim (tau;; CONT) itrt)))
  -> environments.envs_entails H (f (sim (tau;; itrs) itrt)).
Proof. et. Qed.

Ltac _cShowS :=
  match goal with
  H := cris_s _ |- _ => unfold cris_s in H; subst H
  end.

Ltac cShowS := try _cShowS.

Ltac cHideS := cShowS; cNormS;
  let CONT := fresh "CS__" in
  try (first [eapply abstract_cont_src|eapply abstract_tau_src|eapply abstract_cont_src_gen|eapply abstract_tau_src_gen]; intros CONT; move CONT at top).

(** cHideT/cShowT: hide/show continuation in tgt **)

Definition cris_t {A} (K: A) := K.

Lemma abstract_cont_tgt `{Σ: GRA} (H: environments.envs _) Rs Rt
  (sim: retr_type Σ (itree crisE Rs) (itree crisE Rt))
  itrs T (itrt: itree _ T) K
  :
  (let CONT := cris_t K in
   environments.envs_entails H (sim itrs (itrt >>= CONT)))
  -> environments.envs_entails H (sim itrs (itrt >>= K)).
Proof. et. Qed.

Lemma abstract_cont_tgt_gen `{Σ: GRA} (H: environments.envs _) Rs Rt
  (sim: retr_type Σ (itree crisE Rs) (itree crisE Rt))
  (f: iProp Σ → iProp Σ) itrs T (itrt: itree _ T) K
  :
  (let CONT := cris_t K in
   environments.envs_entails H (f (sim itrs (itrt >>= CONT))))
  -> environments.envs_entails H (f (sim itrs (itrt >>= K))).
Proof. et. Qed.

Lemma abstract_tau_tgt `{Σ: GRA} (H: environments.envs _) Rs Rt
  (sim: retr_type Σ (itree crisE Rs) (itree crisE Rt))
  itrs itrt
  :
  (let CONT := cris_t itrt in
   environments.envs_entails H (sim itrs (tau;; CONT)))
  -> environments.envs_entails H (sim itrs (tau;; itrt)).
Proof. et. Qed.

Lemma abstract_tau_tgt_gen `{Σ: GRA} (H: environments.envs _) Rs Rt
  (sim: retr_type Σ (itree crisE Rs) (itree crisE Rt))
  (f: iProp Σ → iProp Σ) itrs itrt
  :
  (let CONT := cris_t itrt in
   environments.envs_entails H (f (sim itrs (tau;; CONT))))
  -> environments.envs_entails H (f (sim itrs (tau;; itrt))).
Proof. et. Qed.

Ltac _cShowT :=
  match goal with
  H := cris_t _ |- _ => unfold cris_t in H; subst H
  end.

Ltac cShowT := try _cShowT.

Ltac cHideT := cShowT; cNormT;
  let CONT := fresh "CT__" in
  try (first[eapply abstract_cont_tgt|eapply abstract_tau_tgt|eapply abstract_cont_tgt_gen|eapply abstract_tau_tgt_gen]; intros CONT; move CONT at top).

(**
   Main tactics
 **)

Ltac _cShowTagS := try (_cShowS; let tag := fresh "TAGS_" in set (TAG_ := cris_s ())).
Ltac _cShowTagT := try (_cShowT; let tag := fresh "TAGT_" in set (TAG_ := cris_t ())).
Ltac _cShowTagR := try (_cShowR; let tag := fresh "TAGR_" in set (TAG_ := cris_r ())).

Ltac _cHideTagS := try (_cShowS; cHideS).
Ltac _cHideTagT := try (_cShowT; cHideT).
Ltac _cHideTagR := try (_cShowR; cHideR).

Ltac cStepS := _cShowTagS; iwcase (do 1 istep_s) (do 1 wstep_s); _cHideTagS.
Ltac cStepT := _cShowTagT; iwcase (do 1 istep_t) (do 1 wstep_t); _cHideTagT.

Ltac cStepsS := _cShowTagS; iwcase (do 1 isteps_s) (do 1 wsteps_s); _cHideTagS.
Ltac cStepsT := _cShowTagT; iwcase (do 1 isteps_t) (do 1 wsteps_t); _cHideTagT.

Ltac _cStateS irule wrule H :=
  _cShowTagS; cNormS;
  (iwcase (do 1 iApply irule) (do 1 iApply wrule));
  (iSplitL H; [iApply H|iIntros H]);
  cNormS; _cHideTagS.

Ltac _cStateT irule wrule H :=
  _cShowTagT; cNormT;
  (iwcase (do 1 iApply irule) (do 1 iApply wrule));
  (iSplitL H; [iApply H|iIntros H]);
  cNormT; _cHideTagT.

Tactic Notation "cGetS" constr(H) :=
  _cStateS isim_sget_src wsim_sget_src H.

Tactic Notation "cGetT" constr(H) :=
  _cStateT isim_sget_tgt wsim_sget_tgt H.

Tactic Notation "cPutS" constr(H) :=
  _cStateS isim_sput_src wsim_sput_src H.

Tactic Notation "cPutT" constr(H) :=
  _cStateT isim_sput_tgt wsim_sput_tgt H.

Tactic Notation "cStep" := _cShowTagS; _cShowTagT; _cShowTagR; iwcase (do 1 istep) (do 1 wstep); _cHideTagS; _cHideTagT; _cHideTagR.
Tactic Notation "cStep" "as" simple_intropattern(name) :=
  _cShowTagS; _cShowTagT; iwcase (do 1 istep as (name)) (do 1 wstep as (name)); _cHideTagS; _cHideTagT.

Tactic Notation "cForceS" := _cShowTagS; iwcase (do 1 iforce_s) (do 1 wforce_s); _cHideTagS.
Tactic Notation "cForceS" uconstr(p) :=
  _cShowTagS; iwcase (do 1 iforce_s p) (do 1 wforce_s p); _cHideTagS.

Tactic Notation "cForceT" := _cShowTagT; iwcase (do 1 iforce_t) (do 1 wforce_t); _cHideTagT.
Tactic Notation "cForceT" uconstr(p) :=
  _cShowTagT; iwcase (do 1 iforce_t p) (do 1 wforce_t p); _cHideTagT.

Ltac cForcesS := _cShowTagS; iwcase (do 1 iforces_s) (do 1 wforces_s); _cHideTagS.
Ltac cForcesT := _cShowTagT; iwcase (do 1 iforces_t) (do 1 wforces_t); _cHideTagT.

Ltac cInlineS := _cShowTagS; iwcase (do 1 iinline_s) (do 1 winline_s); _cHideTagS.
Ltac cInlineT := _cShowTagT; iwcase (do 1 iinline_t) (do 1 winline_t); _cHideTagT.

Tactic Notation "cCall" uconstr(hyps) "as" "(" simple_intropattern(vret) ")" uconstr(IST) :=
  _cShowTagS; _cShowTagT; iwcase (do 1 icall hyps as (vret) IST) (do 1 wcall hyps as (vret) IST); _cHideTagS; _cHideTagT.

Tactic Notation "cSpawn"  "as" "(" simple_intropattern(ntid) ")" :=
  _cShowTagS; _cShowTagT; iwcase (do 1 ispawn as (ntid)) (do 1 wspawn as (ntid)); _cHideTagS; _cHideTagT.

Tactic Notation "cYield" uconstr(hyps) uconstr(IST) :=
  _cShowTagS; _cShowTagT; iwcase (do 1 iyield hyps IST) (do 1 wyield hyps IST); _cHideTagS; _cHideTagT.

Tactic Notation "cBind" uconstr(RR) "as" "(" simple_intropattern(r_s) simple_intropattern(r_t) ")" uconstr(Q) :=
  _cShowTagS; _cShowTagT; iwcase (do 1 ibind RR as (r_s r_t) Q) (do 1 wbind RR as (r_s r_t) Q); _cHideTagS; _cHideTagT.

Tactic Notation "cBind" uconstr(RR) uconstr(hyps) "as" "(" simple_intropattern(r_s) simple_intropattern(r_t) ")" uconstr(Q) :=
  _cShowTagS; _cShowTagT; iwcase (do 1 ibind RR hyps as (r_s r_t) Q) (do 1 wbind RR hyps as (r_s r_t) Q); _cHideTagS; _cHideTagT.

Tactic Notation "cIst" constr(IST) "with" constr(H) :=
  iwcase (do 1 iIst IST with H) (do 1 wIst IST with H).

Ltac _clear_ibot H :=
  let ty := type of H in
  try match ty with context[ibot _ _ _ _ _ _ _ ⊢ _] => clear H end.

Ltac cByCoind CIH := iwcase (do 1 iby_coind CIH) (do 1 wby_coind CIH).

Tactic Notation "cCoind" ident(CIH) ident(g) ident(LEg) :=
  iStopProof;
  first [eapply wsim_coind | eapply isim_coind];
  intros g LEg CIH;
  s; destruct_quant CIH; _clear_ibot LEg.

Tactic Notation "cCoind" ident(CIH) ident(g) ident(LEg) "with" ident(id1) :=
  iStopProof;
  revert id1;
  first [eapply wsim_coind | eapply isim_coind];
  intros g LEg CIH id1;
  s; destruct_quant CIH; _clear_ibot LEg.

Tactic Notation "cCoind" ident(CIH) ident(g) ident(LEg) "with" ident(id2) ident(id1) :=
  iStopProof;
  revert id1; combine_quant id2;
  first [eapply wsim_coind | eapply isim_coind];
  intros g LEg CIH [id2 id1];
  s; destruct_quant CIH; _clear_ibot LEg.

Tactic Notation "cCoind" ident(CIH) ident(g) ident(LEg) "with" ident(id3) ident(id2) ident(id1) :=
  iStopProof;
  revert id1; combine_quant id2; combine_quant id3;
  first [eapply wsim_coind | eapply isim_coind];
  intros g LEg CIH [id3 [id2 id1]];
  s; destruct_quant CIH; _clear_ibot LEg.

Tactic Notation "cCoind" ident(CIH) ident(g) ident(LEg) "with" ident(id4) ident(id3) ident(id2) ident(id1) :=
  iStopProof;
  revert id1; combine_quant id2; combine_quant id3; combine_quant id4;
  first [eapply wsim_coind | eapply isim_coind];
  intros g LEg CIH [id4 [id3 [id2 id1]]];
  s; destruct_quant CIH; _clear_ibot LEg.

Tactic Notation "cCoind" ident(CIH) ident(g) ident(LEg) "with" ident(id5) ident(id4) ident(id3) ident(id2) ident(id1) :=
  iStopProof;
  revert id1; combine_quant id2; combine_quant id3; combine_quant id4; combine_quant id5;
  first [eapply wsim_coind | eapply isim_coind];
  intros g LEg CIH [id5 [id4 [id3 [id2 id1]]]];
  s; destruct_quant CIH; _clear_ibot LEg.

Tactic Notation "cCoind" ident(CIH) ident(g) ident(LEg) "with" ident(id6) ident(id5) ident(id4) ident(id3) ident(id2) ident(id1) :=
  iStopProof;
  revert id1; combine_quant id2; combine_quant id3; combine_quant id4; combine_quant id5; combine_quant id6;
  first [eapply wsim_coind | eapply isim_coind];
  intros g LEg CIH [id6 [id5 [id4 [id3 [id2 id1]]]]];
  s; destruct_quant CIH; _clear_ibot LEg.

Tactic Notation "cCoind" ident(CIH) ident(g) ident(LEg) "with" ident(id7) ident(id6) ident(id5) ident(id4) ident(id3) ident(id2) ident(id1) :=
  iStopProof;
  revert id1; combine_quant id2; combine_quant id3; combine_quant id4; combine_quant id5; combine_quant id6; combine_quant id7;
  first [eapply wsim_coind | eapply isim_coind];
  intros g LEg CIH [id7 [id6 [id5 [id4 [id3 [id2 id1]]]]]];
  s; destruct_quant CIH; _clear_ibot LEg.

Tactic Notation "cCoind" ident(CIH) ident(g) ident(LEg) "with" ident(id8) ident(id7) ident(id6) ident(id5) ident(id4) ident(id3) ident(id2) ident(id1) :=
  iStopProof;
  revert id1; combine_quant id2; combine_quant id3; combine_quant id4; combine_quant id5; combine_quant id6; combine_quant id7; combine_quant id8;
  first [eapply wsim_coind | eapply isim_coind];
  intros g LEg CIH [id8 [id7 [id6 [id5 [id4 [id3 [id2 id1]]]]]]];
  s; destruct_quant CIH; _clear_ibot LEg.

Tactic Notation "cCoind" ident(CIH) ident(g) ident(LEg) "with" ident(id9) ident(id8) ident(id7) ident(id6) ident(id5) ident(id4) ident(id3) ident(id2) ident(id1) :=
  iStopProof;
  revert id1; combine_quant id2; combine_quant id3; combine_quant id4; combine_quant id5; combine_quant id6; combine_quant id7; combine_quant id8; combine_quant id9;
  first [eapply wsim_coind | eapply isim_coind];
  intros g LEg CIH [id9 [id8 [id7 [id6 [id5 [id4 [id3 [id2 id1]]]]]]]];
  s; destruct_quant CIH; _clear_ibot LEg.

Tactic Notation "cCoind" ident(CIH) ident(g) ident(LEg) "with" ident(id10) ident(id9) ident(id8) ident(id7) ident(id6) ident(id5) ident(id4) ident(id3) ident(id2) ident(id1) :=
  iStopProof;
  revert id1; combine_quant id2; combine_quant id3; combine_quant id4; combine_quant id5; combine_quant id6; combine_quant id7; combine_quant id8; combine_quant id9; combine_quant id10;
  first [eapply wsim_coind | eapply isim_coind];
  intros g LEg CIH [id10 [id9 [id8 [id7 [id6 [id5 [id4 [id3 [id2 id1]]]]]]]]];
  s; destruct_quant CIH; _clear_ibot LEg.

Tactic Notation "cCoind" ident(CIH) ident(g) ident(LEg) "with" ident(id11) ident(id10) ident(id9) ident(id8) ident(id7) ident(id6) ident(id5) ident(id4) ident(id3) ident(id2) ident(id1) :=
  iStopProof;
  revert id1; combine_quant id2; combine_quant id3; combine_quant id4; combine_quant id5; combine_quant id6; combine_quant id7; combine_quant id8; combine_quant id9; combine_quant id10; combine_quant id11;
  first [eapply wsim_coind | eapply isim_coind];
  intros g LEg CIH [id11 [id10 [id9 [id8 [id7 [id6 [id5 [id4 [id3 [id2 id1]]]]]]]]]];
  s; destruct_quant CIH; _clear_ibot LEg.

Tactic Notation "cCoind" ident(CIH) ident(g) ident(LEg) "with" ident(id12) ident(id11) ident(id10) ident(id9) ident(id8) ident(id7) ident(id6) ident(id5) ident(id4) ident(id3) ident(id2) ident(id1) :=
  iStopProof;
  revert id1; combine_quant id2; combine_quant id3; combine_quant id4; combine_quant id5; combine_quant id6; combine_quant id7; combine_quant id8; combine_quant id9; combine_quant id10; combine_quant id11; combine_quant id12;
  first [eapply wsim_coind | eapply isim_coind];
  intros g LEg CIH [id12 [id11 [id10 [id9 [id8 [id7 [id6 [id5 [id4 [id3 [id2 id1]]]]]]]]]]];
  s; destruct_quant CIH; _clear_ibot LEg.

Tactic Notation "cCoind" ident(CIH) ident(g) ident(LEg) "with" ident(id13) ident(id12) ident(id11) ident(id10) ident(id9) ident(id8) ident(id7) ident(id6) ident(id5) ident(id4) ident(id3) ident(id2) ident(id1) :=
  iStopProof;
  revert id1; combine_quant id2; combine_quant id3; combine_quant id4; combine_quant id5; combine_quant id6; combine_quant id7; combine_quant id8; combine_quant id9; combine_quant id10; combine_quant id11; combine_quant id12; combine_quant id13;
  first [eapply wsim_coind | eapply isim_coind];
  intros g LEg CIH [id13 [id12 [id11 [id10 [id9 [id8 [id7 [id6 [id5 [id4 [id3 [id2 id1]]]]]]]]]]]];
  s; destruct_quant CIH; _clear_ibot LEg.

Tactic Notation "cCoind" ident(CIH) ident(g) ident(LEg) "with" ident(id14) ident(id13) ident(id12) ident(id11) ident(id10) ident(id9) ident(id8) ident(id7) ident(id6) ident(id5) ident(id4) ident(id3) ident(id2) ident(id1) :=
  iStopProof;
  revert id1; combine_quant id2; combine_quant id3; combine_quant id4; combine_quant id5; combine_quant id6; combine_quant id7; combine_quant id8; combine_quant id9; combine_quant id10; combine_quant id11; combine_quant id12; combine_quant id13; combine_quant id14;
  first [eapply wsim_coind | eapply isim_coind];
  intros g LEg CIH [id14 [id13 [id12 [id11 [id10 [id9 [id8 [id7 [id6 [id5 [id4 [id3 [id2 id1]]]]]]]]]]]]];
  s; destruct_quant CIH; _clear_ibot LEg.

Tactic Notation "cCoind" ident(CIH) ident(g) ident(LEg) "with" ident(id15) ident(id14) ident(id13) ident(id12) ident(id11) ident(id10) ident(id9) ident(id8) ident(id7) ident(id6) ident(id5) ident(id4) ident(id3) ident(id2) ident(id1) :=
  iStopProof;
  revert id1; combine_quant id2; combine_quant id3; combine_quant id4; combine_quant id5; combine_quant id6; combine_quant id7; combine_quant id8; combine_quant id9; combine_quant id10; combine_quant id11; combine_quant id12; combine_quant id13; combine_quant id14; combine_quant id15;
  first [eapply wsim_coind | eapply isim_coind];
  intros g LEg CIH [id15 [id14 [id13 [id12 [id11 [id10 [id9 [id8 [id7 [id6 [id5 [id4 [id3 [id2 id1]]]]]]]]]]]]]];
  s; destruct_quant CIH; _clear_ibot LEg.

Tactic Notation "cCoind" ident(CIH) ident(g) ident(LEg) "with" ident(id16) ident(id15) ident(id14) ident(id13) ident(id12) ident(id11) ident(id10) ident(id9) ident(id8) ident(id7) ident(id6) ident(id5) ident(id4) ident(id3) ident(id2) ident(id1) :=
  iStopProof;
  revert id1; combine_quant id2; combine_quant id3; combine_quant id4; combine_quant id5; combine_quant id6; combine_quant id7; combine_quant id8; combine_quant id9; combine_quant id10; combine_quant id11; combine_quant id12; combine_quant id13; combine_quant id14; combine_quant id15; combine_quant id16;
  first [eapply wsim_coind | eapply isim_coind];
  intros g LEg CIH [id16 [id15 [id14 [id13 [id12 [id11 [id10 [id9 [id8 [id7 [id6 [id5 [id4 [id3 [id2 id1]]]]]]]]]]]]]]];
  s; destruct_quant CIH; _clear_ibot LEg.

Tactic Notation "cCoind" ident(CIH) ident(g) ident(LEg) "with" ident(id17) ident(id16) ident(id15) ident(id14) ident(id13) ident(id12) ident(id11) ident(id10) ident(id9) ident(id8) ident(id7) ident(id6) ident(id5) ident(id4) ident(id3) ident(id2) ident(id1) :=
  iStopProof;
  revert id1; combine_quant id2; combine_quant id3; combine_quant id4; combine_quant id5; combine_quant id6; combine_quant id7; combine_quant id8; combine_quant id9; combine_quant id10; combine_quant id11; combine_quant id12; combine_quant id13; combine_quant id14; combine_quant id15; combine_quant id16; combine_quant id17;
  first [eapply wsim_coind | eapply isim_coind];
  intros g LEg CIH [id17 [id16 [id15 [id14 [id13 [id12 [id11 [id10 [id9 [id8 [id7 [id6 [id5 [id4 [id3 [id2 id1]]]]]]]]]]]]]]]];
  s; destruct_quant CIH; _clear_ibot LEg.

Tactic Notation "cCoind" ident(CIH) ident(g) ident(LEg) "with" ident(id18) ident(id17) ident(id16) ident(id15) ident(id14) ident(id13) ident(id12) ident(id11) ident(id10) ident(id9) ident(id8) ident(id7) ident(id6) ident(id5) ident(id4) ident(id3) ident(id2) ident(id1) :=
  iStopProof;
  revert id1; combine_quant id2; combine_quant id3; combine_quant id4; combine_quant id5; combine_quant id6; combine_quant id7; combine_quant id8; combine_quant id9; combine_quant id10; combine_quant id11; combine_quant id12; combine_quant id13; combine_quant id14; combine_quant id15; combine_quant id16; combine_quant id17; combine_quant id18;
  first [eapply wsim_coind | eapply isim_coind];
  intros g LEg CIH [id18 [id17 [id16 [id15 [id14 [id13 [id12 [id11 [id10 [id9 [id8 [id7 [id6 [id5 [id4 [id3 [id2 id1]]]]]]]]]]]]]]]]];
  s; destruct_quant CIH; _clear_ibot LEg.

Tactic Notation "cCoind" ident(CIH) ident(g) ident(LEg) "with" ident(id19) ident(id18) ident(id17) ident(id16) ident(id15) ident(id14) ident(id13) ident(id12) ident(id11) ident(id10) ident(id9) ident(id8) ident(id7) ident(id6) ident(id5) ident(id4) ident(id3) ident(id2) ident(id1) :=
  iStopProof;
  revert id1; combine_quant id2; combine_quant id3; combine_quant id4; combine_quant id5; combine_quant id6; combine_quant id7; combine_quant id8; combine_quant id9; combine_quant id10; combine_quant id11; combine_quant id12; combine_quant id13; combine_quant id14; combine_quant id15; combine_quant id16; combine_quant id17; combine_quant id18; combine_quant id19;
  first [eapply wsim_coind | eapply isim_coind];
  intros g LEg CIH [id19 [id18 [id17 [id16 [id15 [id14 [id13 [id12 [id11 [id10 [id9 [id8 [id7 [id6 [id5 [id4 [id3 [id2 id1]]]]]]]]]]]]]]]]]];
  s; destruct_quant CIH; _clear_ibot LEg.

(* (** Special Tactics for RealUpdate **) *)

(* (* Tactic Notation "ru_s_advanced" uconstr(P) := *) *)
(* (*   iwcase (do 1 iru_s_advanced P) (do 1 wru_s_advanced P). *) *)

(* Tactic Notation "ru_s" uconstr(P) := *)
(*   iwcase (do 1 iru_s P) (do 1 wru_s P). *)

(* Ltac ru_t := *)
(*   iwcase (do 1 iru_t) (do 1 wru_t). *)

(* (* *)
(*  unfold_lat *)
(* *) *)

(* Lemma unfold_lat_img `{Σ:GRA} peeking fsp lbody body arg:
  lat_img peeking fsp lbody body arg =
    r <- lat_img_body peeking fsp lbody body arg;;
    match r with
    | inl _ => tau;; lat_img peeking fsp lbody body arg
    | inr r => Ret r
    end.
Proof.
  rewrite /lat_img. erewrite -> (bisim_is_eq (unfold_iter _ _)) at 1.
  f_equal. extensionalities. destruct H; et.
  repeat f_equal. destruct u; et.
Qed.

Lemma unfold_lat_real `{Σ:GRA} peeking fsp lbody body arg:
  lat_real peeking fsp lbody body arg =
    r <- lat_real_body peeking fsp lbody body arg;;
    match r with
    | inl _ => tau;; lat_real peeking fsp lbody body arg
    | inr r => Ret r
    end.
Proof.
  rewrite /lat_real. erewrite -> (bisim_is_eq (unfold_iter _ _)) at 1.
  f_equal. extensionalities. destruct H; et.
  repeat f_equal. destruct u; et.
Qed.

Ltac unfold_lat_img_s :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  only_itree_s;
  rewrite {1}unfold_lat_img {1}/lat_img_body;
  show_until marker;
  steps_s.

Ltac unfold_lat_img_t :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  only_itree_t;
  rewrite {1}unfold_lat_img {1}/lat_img_body;
  show_until marker;
  steps_t.

Ltac unfold_lat_real_s :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  only_itree_s;
  rewrite {1}unfold_lat_real {1}/lat_real_body;
  show_until marker;
  steps_s.

Ltac unfold_lat_real_t :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  only_itree_t;
  rewrite {1}unfold_lat_real {1}/lat_real_body;
  show_until marker;
  steps_t. *)
