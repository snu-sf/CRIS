From CRIS.common Require Import Common.
From CRIS.modules Require Import LMod.
From CRIS.simulations.lsim Require Import LSim.
From CRIS.proofmode Require Import HNorm HNormInstances.

Set Implicit Arguments.

#[export] Hint Resolve lsim_mon : paco.
#[export] Hint Resolve cpn8_wcompat : paco.

Ltac lreplace_s :=
  lazymatch goal with
  | [ |- ?rel (?st_s, ?itr_s) (?st_t, ?itr_t) ] =>
      refine (eq_ind_r (fun itr_s' => rel (st_s, itr_s') (st_t, itr_t)) _ _); cycle 1
  end.

Ltac lreplace_t :=
  lazymatch goal with
  | [ |- ?rel (?st_s, ?itr_s) (?st_t, ?itr_t) ] =>
      refine (eq_ind_r (fun itr_t' => rel (st_s, itr_s) (st_t, itr_t')) _ _); cycle 1
  end.

Ltac lnorm_s := lreplace_s; [hnorm_itr|].
Ltac lnorm_t := lreplace_t; [hnorm_itr|].

Ltac prep := lnorm_s; lnorm_t.

Ltac apply_lsimC_spec :=
  match goal with
  | [ |- gpaco8 (_lsim ?fl_src ?fl_tgt ?lw ?my_tid)
          _ _ _ _ _ _ _ _ _ _ _ ] =>
    apply (lsimC_spec fl_src fl_tgt lw my_tid)
  end.

Ltac guclo_lflagC :=
  match goal with
  | [ |- gpaco8 (_lsim ?fl_src ?fl_tgt ?lw ?my_tid)
          _ _ _ _ _ _ _ _ _ _ _ ] =>
    guclo (lflagC_spec fl_src fl_tgt lw my_tid);
      try exact (lsim_mon fl_src fl_tgt lw my_tid)
  end.

Ltac _step :=
  prep; apply_lsimC_spec; econs; i;
  match goal with
  | [ |- exists (_ : unit), _ ] => esplits; [eauto|..]; i
  | [ |- exists _, _ ] => fail 1
  | _ => idtac
  end.

Ltac step := _step; simpl; des_ifs_safe.
Ltac steps := (hrepeat ltac:(step)); prep.

Tactic Notation "hide" constr(tm) integer(occ) :=
  let tmp := fresh "tmp" in let TMP := fresh "TMP" in
  set (xxx := tm) at occ; remember xxx as tmp eqn : TMP;
  unfold xxx in *; clear xxx; guardH TMP.
Ltac unhide :=
  unguard; subst.
