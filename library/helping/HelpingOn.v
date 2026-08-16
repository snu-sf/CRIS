From CRIS.common Require Import CRIS.
From CRIS.scheduler Require Import SchHeader SchI.
From CRIS.helping Require Export HelpingHeader HelpingResource.

(* Helping module *)
Module HelpingOn. Section HelpingOn.
  Context `{!crisG Γ Σ α β τ _S _I, !helpingGS}.

  Definition scopes (mn : string) : list string := [mn].

  Definition try_run (mn : string)
      (jobcode : SAny.t → itree crisE (SAny.t + SAny.t))
      (reqid : nat) : itree crisE Any.t :=
    oret <- trigger (Choose (option SAny.t));;
    match oret with
    | None =>
        N <- trigger (Choose (option namespace));;
        arg <- trigger (Choose SAny.t);;
        trigger (Guarantee (HelpPend reqid N arg));;;
        ret <- ITree.iter (λ arg, 𝒴@{N};;; SB.sandbox msk_pure (jobcode arg)) arg;;
        trigger (Assume (HelpDone reqid ret));;;
        Ret ret↑
    | Some ret =>
        trigger (Guarantee (HelpDone reqid ret));;;
        Ret ret↑
    end.
  #[global] Typeclasses Opaque try_run.

  Definition run (mn : string)
      (jobcode : SAny.t → itree crisE (SAny.t + SAny.t)) : Any.t → itree crisE Any.t :=
    λ arg,
      '(N, arg) : option namespace * SAny.t <- arg↓?;;
      reqid <- trigger (Take nat);;
      trigger (Assume (HelpPend reqid N arg));;;
      𝒴@{N};;;
      try_run mn jobcode reqid.
  #[global] Typeclasses Opaque run.

  Definition help (mn : string)
      (jobcode : SAny.t → itree crisE (SAny.t + SAny.t)) : Any.t → itree crisE Any.t :=
    λ arg,
      'Nhelp : option namespace <- arg↓?;;
      reqid <- trigger (Choose nat);;
      N <- trigger (Choose (option namespace));;
      jobarg <- trigger (Choose SAny.t);;
      trigger (Guarantee (HelpPend reqid N jobarg));;;
      option_Guarantee Nhelp;;;
      option_Assume N;;;
      ret <- ITree.iter (λ arg, 𝒴@{N};;; SB.sandbox msk_pure (jobcode arg)) jobarg;;
      option_Guarantee N;;;
      option_Assume Nhelp;;;
      trigger (Assume (HelpDone reqid ret));;;
      Ret tt↑.
  #[global] Typeclasses Opaque help.

  Definition fnsems (mn : string)
      (jobcode : SAny.t → itree crisE (SAny.t + SAny.t)) : fnsemmap :=
    {[funid (Helping.run mn) #
        (msk_scp (scopes mn) msk_true, (None, run mn jobcode));
      funid (Helping.help mn) #
        (msk_scp (scopes mn) msk_true, (None, help mn jobcode))]}.

  Program Definition Mod (mn : string)
      (jobcode : SAny.t → itree crisE (SAny.t + SAny.t)) : SMod.t := {|
    SMod.scopes := scopes mn;
    SMod.fnsems := fnsems mn jobcode;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t (mn : string)
      (jobcode : SAny.t → itree crisE (SAny.t + SAny.t)) : Mod.t :=
    SMod.to_mod ∅ (Mod mn jobcode).
End HelpingOn. End HelpingOn.

Module HelpingDummy. Section HelpingDummy.
  Context `{!crisG Γ Σ α β τ _S _I}.
  Context (mn : string).
  Definition scopes : list string := [mn].

  Definition fnsems : fnsemmap :=
    {[funid (Helping.run mn) # (msk_real (msk_scp scopes msk_true), (None, λ _, triggerNB));
      funid (Helping.help mn) # (msk_real (msk_scp scopes msk_true), (None, λ _, triggerNB))]}.

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t : Mod.t := SMod.to_mod ∅ Mod.
End HelpingDummy. End HelpingDummy.
