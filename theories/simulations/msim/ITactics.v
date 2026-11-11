From iris.proofmode Require Import proofmode.
From CRIS.common Require Import Common ConcRA.
From CRIS.lib Require Import LAuto.

From CRIS.modules Require Import Sp LMod SMod Mod.
From CRIS.simulations.msim Require Import ISim TacticsCommon.

(**** TODO ****)
(* A tactic to handle meta variables *)

(************ User Notations **************)

(*** TODO: 
          What else should be displayed? 
          Simplify (hide) k-trees

***)

(***
  Step-level tactics
 ***)

Ltac _istep_s :=
  (******* isim ******)
  (** src **)
  match goal with
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ (tau;; _) _) ] =>
      iApply isim_tau_src
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ (trigger (Take (FSpec (fspec_to_rel _))) >>= _) _) ] =>
      let name := fresh "_q" in iApply isim_take_src_fspec; iIntros (name); simpl in name
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ (trigger (Take _) >>= _) _) ] =>
      let name := fresh "_q" in
      iApply isim_take_src; iIntros (name)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ (trigger (Assume ?P) >>= _) _) ] =>
      unfoldPrePost_term P; iApply isim_assume_src; iIntrosFresh "ASM"
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ (trigger (AssumeRes _) >>= _) _) ] =>
      iApply isim_assume_res_src; iIntrosFresh "ASM"
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ (assume _ >>= _) _) ] =>
      let name := fresh "ASM" in iApply isim_asm_src; iIntros (name)
  end.

Ltac istep_s := cNormS; _istep_s; cNormS.

Ltac isteps_s := cNormS; hrepeat (do 1 _istep_s; cNormS).

Ltac _istep_t :=
  (******* isim ******)
  (** tgt **)
  match goal with
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (tau;; _)) ] =>
      iApply isim_tau_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (trigger (Choose (FSpec (fspec_to_rel _))) >>= _)) ] =>
      let name := fresh "_q" in iApply isim_choose_tgt_fspec; iIntros (name); simpl in name
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (trigger (Choose _) >>= _)) ] =>
      let name := fresh "_q" in
      iApply isim_choose_tgt; iIntros (name)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (trigger (Guarantee ?P) >>= _)) ] =>
      unfoldPrePost_term P; iApply isim_guarantee_tgt; iIntrosFresh "GRT"
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (guarantee _ >>= _)) ] =>
      let name := fresh "GRT" in iApply isim_guar_tgt; iIntros (name)
  end.

Ltac istep_t := cNormT; _istep_t; cNormT.

Ltac isteps_t := cNormT; hrepeat (do 1 _istep_t; cNormT).

Ltac _istep tac :=
  match goal with
  (******* isim ******)
  (** both **)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ (Ret _) (Ret _)) ] =>
      iApply isim_ret
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ (trigger (IO _ _) >>= _) (trigger (IO _ _) >>= _)) ] =>
      iApply isim_io; tac
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ (trigger GetTid >>= _) (trigger GetTid >>= _)) ] =>
      iApply isim_gettid; tac
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ (trigger (Spawn _ _) >>= _) (trigger (Spawn _ _) >>= _)) ] =>
      iApply isim_spawn; tac
  end.

Tactic Notation "istep" "as" "(" simple_intropattern(name) ")" :=
  cNormS; cNormT; _istep ltac:(iIntros (name)); cNormS; cNormT.

Tactic Notation "istep" := istep as (?).

Ltac _iforce_s :=
  match goal with
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ (trigger (Choose (FSpec (fspec_to_rel _))) >>= _) _) ] =>
      iApply isim_choose_src_fspec
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ (trigger (Choose ?T) >>= _) _) ] =>
      iApply isim_choose_src
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ (trigger (Guarantee ?P) >>= _) _) ] =>
      unfoldPrePost_term P; iApply isim_guarantee_src
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ (unwrapN _ >>= _) _) ] =>
      iApply isim_unwrapN_src; iExists _
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ (guarantee _ >>= _) _) ] =>
      iApply isim_guar_src
  end
.

Tactic Notation "iforce_s" :=
  cNormS; _iforce_s; s; [..|try iExists _; cNormS].

Tactic Notation "iforce_s" uconstr(p) :=
  cNormS; _iforce_s; s; [..|iExists p; cNormS].

Ltac iforces_s :=
  cNormS; hrepeat do 1 (_iforce_s; s; [..|try iExists _; cNormS]).

Ltac _iforce_t :=
  match goal with
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (trigger (Take (FSpec (fspec_to_rel _))) >>= _)) ] =>
      iApply isim_take_tgt_fspec
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (trigger (Take _) >>= _)) ] =>
      iApply isim_take_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (trigger (Assume ?P) >>= _)) ] =>
      unfoldPrePost_term P; iApply isim_assume_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (assume _ >>= _)) ] =>
      iApply isim_asm_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (unwrapU _ >>= _)) ] =>
      iApply isim_unwrapU_tgt; iExists _
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (trigger (AssumeRes _) >>= _)) ] =>
      iApply isim_assume_res_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (RealUpdate (idx_to_rel ?P ?Q) >>= _)) ] =>
      unfoldPrePost_term P; unfoldPrePost_term Q; iApply isim_ru_tgt_simple
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (RealUpdate _ >>= _)) ] =>
      iApply isim_ru_tgt_simple_general
  end
.

Tactic Notation "iforce_t" :=
  cNormT; _iforce_t; s; [..|try iExists _; cNormT].

Tactic Notation "iforce_t" uconstr(p) :=
  cNormT; _iforce_t; s; [..|iExists p; cNormT].

Ltac iforces_t :=
  cNormT; hrepeat do 1 (_iforce_t; s; [..|try iExists _; cNormT]).

Ltac iinline_s :=
  cNormS; iApply isim_inline_src; [prove_inline_cond|cNormInlineS].

Ltac iinline_t :=
  cNormT; iApply isim_inline_tgt; [prove_inline_cond|cNormInlineT].

Tactic Notation "icall" uconstr(hyps) "as" "(" simple_intropattern(vret) ")" uconstr(IST) :=
  (cNormS; cNormT; iApply isim_call); iSplitL hyps; [try done|try clear vret; try iClear IST; iIntros (vret) IST; cNormS; cNormT].

Tactic Notation "ispawn" "as" "(" simple_intropattern(ntid) ")" :=
  cNormS; cNormT; iApply isim_spawn; iIntros (ntid); cNormS; cNormT.

Tactic Notation "iyield" uconstr(hyps) uconstr(IST) :=
  (cNormS; cNormT; iApply isim_yield); iSplitL hyps; [try done|try iClear IST; iIntros IST; cNormS; cNormT].

Ltac iby_coind CIH :=
  iApply isim_progress; iApply CIH.

Tactic Notation "ibind" uconstr(RR) uconstr(hyps) "as" "(" simple_intropattern(r_s) simple_intropattern(r_t) ")" uconstr(Q) :=
  iApply (isim_bind _ _ _ _ _ _ _ RR); iSplitL hyps; [et|try clear r_s; try clear r_t; try iClear Q; iIntros (r_s r_t) Q]; cNormS; cNormT.
Tactic Notation "ibind" uconstr(RR) "as" "(" simple_intropattern(r_s) simple_intropattern(r_t) ")" uconstr(Q) :=
  iApply (isim_bind _ _ _ _ _ _ _ RR); iSplitL; [et|try clear r_s; try clear r_t; try iClear Q; iIntros (r_s r_t) Q]; cNormS; cNormT.


Tactic Notation "iIst" constr(IST) "with" constr(H) :=
  match goal with
  | |- environments.envs_entails _ (isim _ _ ?Ist _ _ _ _ _ _) =>
      iAssert Ist with H as IST
  end.

(** Special Tactics for RealUpdate **)

(* Tactic Notation "iru_s_advanced" uconstr(P) := *)
(*   cNormS; iApply isim_ru_src_advanced; *)
(*   iExists P; iSplit; [try prove_precise|]. *)

(* Tactic Notation "iru_s" uconstr(P) := *)
(*   cNormS; iApply isim_ru_src; *)
(*   iExists P; iSplit; [try prove_precise|]. *)

(* Ltac iru_t := *)
(*   cNormT; iApply isim_ru_tgt. *)
