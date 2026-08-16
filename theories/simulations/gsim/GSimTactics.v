From CRIS.common Require Import Common.
From CRIS.modules Require Import LMod.
From CRIS.simulations.msim Require Import TacticsCommon.
From CRIS.modules Require Export Mod SMod.
From CRIS.simulations.gsim Require Export GSim.

Ltac greplace_s :=
  match goal with
  | |- gpaco7 _ _ _ _ _ _ _ _ _ ?itr _ =>
    pattern itr;
    match goal with
    | |- ?f ?a =>
      refine (eq_ind_r f _ _); cycle 1
    end
  end.

Ltac greplace_t :=
  match goal with
  | |- gpaco7 _ _ _ _ _ _ _ _ _ _ ?itr =>
    pattern itr;
    match goal with
    | |- ?f ?a =>
      refine (eq_ind_r f _ _); cycle 1
    end
  end.

Ltac gcNormS :=
  greplace_s; [s; hnorm_itr|].
Ltac gcNormT :=
  greplace_t; [s; hnorm_itr|].

Ltac giter_s :=
  greplace_s; [rewrite unfold_iterV /itreeV_itree //|].
Ltac giter_t :=
  greplace_t; [rewrite unfold_iterV /itreeV_itree //|].

Ltac gstep_t := gcNormT; guclo gsim_indC_spec; econs; instantiate (1:=smj_top).
Ltac gstep_s := gcNormS; guclo gsim_indC_spec; econs; instantiate (1:=smj_top).

Ltac gsteps_t :=
  gcNormT; hrepeat (do 1 (guclo gsim_indC_spec; econs; instantiate (1:=smj_top); try gcNormT)).
Ltac gsteps_s :=
  gcNormS; hrepeat (do 1 (guclo gsim_indC_spec; econs; instantiate (1:=smj_top); try gcNormS)).

Definition ztac_id {X: Type} (x: X) : X := x.
Global Opaque ztac_id.

Ltac zss :=
  try (rewrite -> !Any.pair_split in * );
  try (rewrite -> !Any.upcast_downcast in * );
  try (rewrite -> !SAny.pair_split in * );
  try (rewrite -> !SAny.upcast_downcast in * ).

Ltac zonly_s :=
  let ITREE := fresh "ITREE" in
  let GPACO := fresh "GPACO" in 
  match goal with
    [|- ?rel _ ?it] =>
      set (GPACO := rel); first [set (ITREE := it) at 2|set (ITREE := it) at 1]
  end;
  change ITREE with (ztac_id ITREE);
  move ITREE at top.

Ltac zonly_t :=
  let ITREE := fresh "ITREE" in
  let GPACO := fresh "GPACO" in 
  match goal with
    [|- ?rel ?it _] =>
      set (GPACO := rel); set (ITREE := it) at 1
  end;
  change ITREE with (ztac_id ITREE);
  move ITREE at top.

Ltac zshow :=
  match goal with
    [ITREE := ?t|-_] =>
      match type of ITREE with
        itree _ _ => change (ztac_id ITREE) with ITREE; subst ITREE
      end
  end;
  match goal with
    [GPACO := ?rel|-_] => subst GPACO
  end.

Ltac zsimpl_len :=
  simpl List.length in *;
  try rewrite ->!length_app in * ;
  try rewrite ->!length_insert in * ;
  try rewrite ->!length_app in * ;
  try rewrite ->!Nat.sub_diag in * ;
  simpl List.length in *;
  try nia.

Ltac zsimpl_ths :=
  ired;
  zsimpl_len;
  try (hrepeat do 1 (rewrite insert_app_l; [|zsimpl_len; fail]));
  try (rewrite !list_insert_insert).

Ltac zsimpl_lookup :=
  try (rewrite lookup_app_l; [|zsimpl_len; fail]);
  try (rewrite lookup_app_r; [|zsimpl_len; fail]).

Ltac zlookup_insert :=
  try (rewrite list_lookup_insert); zsimpl_len.

Ltac zlookup_insert_ne :=
  try (rewrite list_lookup_insert_ne); zsimpl_len.

Ltac ziter :=
  rewrite unfold_iterV; ired;
  try rewrite /LModTr.interp_stateE;
  try rewrite /LModTr.pure_state;
  zsimpl_lookup;
  zlookup_insert;
  zsimpl_ths;
  zss.

Ltac zstep :=
  ired; guclo gsim_indC_spec; econs; et; i;
  zsimpl_ths;
  zss.

Ltac zinst := try match goal with | |- smj => exact smj_top end.

Ltac ziter_s := zonly_s; ziter; zshow.
Ltac ziter_t := zonly_t; ziter; zshow.

Ltac zostep_s := zonly_s; zstep; zshow.
Ltac zostep_t := zonly_t; zstep; zshow.
  
Ltac zstep_s := unshelve zostep_s; zinst.
Ltac zstep_t := unshelve zostep_t; zinst.

Ltac zprogress :=
  gstep; econs; eapply gsim_progress; eauto using smj_lt_mid_top.

Tactic Notation "zprogress" "with" uconstr(ps0) uconstr(pt0) uconstr(ps) uconstr(pt) :=
  gstep; econs; eapply (gsim_progress _ _ _ ps pt ps0 pt0); eauto.
