From CRIS.common Require Export CRIS.
From CRIS.modules Require Export SMod Mod.

Module SchHdr.
  Definition _spawn := fnsig "Sch._spawn" (fntyp (string * SAny.t) ()).
  Definition spawn := fnsig "Sch.spawn" (fntyp (string * SAny.t) nat).
  Definition yield := fnsig "Sch.yield" (fntyp () ()).
  Definition join := fnsig "Sch.join" (fntyp nat (option SAny.t)).

  Definition exports : gset string :=
    {[ fn_name spawn; fn_name yield; fn_name join ]}.
End SchHdr.

Definition SCH : string := "sch".
Global Opaque SCH.

(* Wrapping fspecs *)
Section FSpec.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition sfunN {A R} (ft: fntyp_t A R) `{coreE -< E} `{callE -< E} `{pgE -< E}
      (body : A -> itree E R) : SAny.t -> itree E SAny.t :=
    λ varg, varg <- varg↓↓!;; vret <- body varg;; Ret vret↑↑.

  Definition sfunU {A R} (ft: fntyp_t A R) `{coreE -< E} `{callE -< E} `{pgE -< E}
      (body : A -> itree E R) : SAny.t -> itree E SAny.t :=
    λ varg, varg <- varg↓↓?;; vret <- body varg;; Ret vret↑↑.

  Definition interp_cond (s : {n & GTerm.t n}) :=
    match s with
    | existT n p => ⟦ p ⟧
    end.
End FSpec.

Module Sch. Section Sch.
  Context `{coreE -< E, callE -< E}.

  Definition spawn (fnarg : string * SAny.t) : itree E nat :=
    'tid : nat <- ccallU SchHdr.spawn fnarg;; Ret tid.
  #[global] Typeclasses Opaque spawn.

  Definition choose_optbool : itree E (option bool) := trigger (Choose (option bool)).

  Definition yield : itree E unit :=
    Seal.sealing SCH
     (iterC ((λ (_: unit),
        b <- choose_optbool;;
        match b with
        | None => Ret (inr tt: () + ())
        | Some false => Ret (inl tt: () + ())
        | Some true =>
            trigger (Call (fn_name SchHdr.yield) tt↑);;;
            Ret (inl tt: () + ())
        end)) tt).
  #[global] Typeclasses Opaque yield.

  Definition terminate : itree E unit :=
    Seal.sealing SCH
      (iterC ((λ (_: unit),
        trigger (Call (fn_name SchHdr.yield) tt↑);;;
        Ret (inl tt: () + ())
      )) tt).
  #[global] Typeclasses Opaque terminate.

  Definition join (tid : nat) : itree E SAny.t :=
    ors <- ccallU SchHdr.join tid;; ors?.
  #[global] Typeclasses Opaque join.

  Definition yield_namespace `{!crisG Γ Σ α β τ Hsub Hinv, agE -< E}
      (N : option namespace) : itree E unit :=
    match N with
    | Some N =>
      iterC ((λ (_: unit),
        b <- trigger (Choose (option bool));;
        match b with
        | None => Ret (inr tt: () + ())
        | Some false => Ret (inl tt: () + ())
        | Some true =>
            trigger (Guarantee (winv (↑N, ↑N)));;;
            trigger (Call (fn_name SchHdr.yield) tt↑);;;
            trigger (Assume (winv (↑N, ↑N)));;;
            Ret (inl tt: () + ())
        end)) tt
    | None => yield
    end.
  #[global] Typeclasses Opaque yield_namespace.
End Sch. End Sch.

Notation 𝒴 := (Sch.yield).
Notation "'𝒴@{' N '}'" := (Sch.yield_namespace N) (format "'𝒴@{' N '}'").

Lemma yield_unfold `{coreE -< E, callE -< E} :
  @Sch.yield E _ _ =
  tau;; b <- trigger (Choose (option bool));;
  match b with
  | None => Ret tt
  | Some false => Sch.yield
  | Some true => trigger (Call (fn_name SchHdr.yield) tt↑);;; Sch.yield
  end.
Proof using.
  rewrite {1}/Sch.yield; unseal SCH; rewrite unfold_iterC.
  repeat f_equal. ired. repeat f_equal. extensionalities b. destruct b as [[|]|]; ss.
  { ired. f_equal. extensionalities x. rewrite /Sch.yield; unseal SCH; ss. }
  { ired. rewrite /Sch.yield; unseal SCH; ss. }
  { ired. done. }
Qed.

Section yield.
  Context `{!crisG Γ Σ α β τ Hsub Hinv}.
  Definition option_Guarantee (N : option namespace) : itree crisE unit :=
    match N with
    | Some N => trigger (Guarantee (winv (↑N, ↑N)))
    | None => Ret tt
    end.

  Definition option_Assume (N : option namespace) : itree crisE unit :=
    match N with
    | Some N => trigger (Assume (winv (↑N, ↑N)))
    | None => Ret tt
    end.

  Lemma yield_namespace_yield :
    𝒴@{None} =@{itree crisE unit} 𝒴.
  Proof. reflexivity. Qed.

  Lemma yield_namespace_unfold  N :
    Sch.yield_namespace N =@{itree crisE unit}
    tau;; b <- trigger (Choose (option bool));;
    match b with
    | None => Ret tt
    | Some false => Sch.yield_namespace N
    | Some true =>
        option_Guarantee N;;;
        trigger (Call (fn_name SchHdr.yield) tt↑);;;
        option_Assume N;;;
        Sch.yield_namespace N
    end.
  Proof using.
    rewrite {1}/Sch.yield_namespace; destruct N as [N|]; cycle 1.
    { rewrite yield_unfold; grind. }
    rewrite unfold_iterC. ired.
    repeat f_equal. extensionalities b. destruct b as [[|]|]; ss; ired; ss.
  Qed.
End yield.

Arguments Sch.yield_namespace : simpl never.

Definition yield_iter `{E : Type → Type, coreE -< E, callE -< E} {I R}
    (body : I → itree E (I + R)) (arg : I) : itree E R :=
  ret <- ITree.iter (λ arg : I, 𝒴;;; body arg) arg;; 𝒴;;; Ret ret.

Definition unfold_yield_iter `{E : Type → Type, coreE -< E, callE -< E} {I R}
    (body : I → itree E (I + R)) (arg : I) :
  yield_iter body arg =
  𝒴;;; ret <- body arg;;
  match ret with
  | inl i => tau;; yield_iter body i
  | inr ret => 𝒴;;; Ret ret
  end.
Proof.
  rewrite {1}/yield_iter unfold_iter; etrans; first hnorm_itr; grind.
  case_match; etrans; try hnorm_itr; grind; rewrite /yield_iter /=.
Qed.

Definition yield_namespace_iter `{!crisG Γ Σ α β τ _S _I} {I R}
    (N : option namespace) (body : I → itree crisE (I + R)) (arg : I) : itree crisE R :=
  ret <- ITree.iter (λ arg : I, 𝒴@{N};;; body arg) arg;; 𝒴@{N};;; Ret ret.

Global Typeclasses Opaque yield_namespace_iter.

Definition unfold_yield_namespace_iter `{!crisG Γ Σ α β τ _S _I} {I R}
    (N : option namespace) (body : I → itree crisE (I + R)) (arg : I) :
  yield_namespace_iter N body arg =
  𝒴@{N};;; ret <- body arg;;
  match ret with
  | inl i => tau;; yield_namespace_iter N body i
  | inr ret => 𝒴@{N};;; Ret ret
  end.
Proof.
  rewrite {1}/yield_namespace_iter unfold_iter; etrans; first hnorm_itr; grind.
  case_match; etrans; try hnorm_itr; grind; rewrite /yield_namespace_iter /=.
Qed.
