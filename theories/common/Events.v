From Stdlib Require Import String.
From CRIS.lib Require Import Coqlib.
From CRIS.lib Require Export ITreelib.
From CRIS.lib Require Import Any.

From CRIS.iris_system Require Import base_logic.base_logic.
From CRIS.iris_system Require Import own.

Variant coreE : Type → Type :=
| Choose (X : Type) : coreE X
| Take (X : Type) : coreE X
| IO {O : Type} {I : Type} (fn : string) (args : O) : coreE I.

Variant key : Set :=
| sf (s : string) (f : string)
.
Notation "s ↯ f" := (sf s f) (at level 9).

Definition scope (k : key) : string :=
  match k with
  | s ↯ f => s
  end.

#[global] Program Instance key_eq_dec : EqDecision key :=
  fun k1 k2 =>
    match k1, k2 with
    | s1 ↯ f1, s2 ↯ f2 =>
        match decide (s1 = s2) with
        | left _ => match decide (f1 = f2) with
                    | left _ => _
                    | right _ => _
                    end
        | right _ => _
        end
    end.
Next Obligation. intros. left. congruence. Qed.
Next Obligation. intros. right. congruence. Qed.
Next Obligation. intros. right. congruence. Qed.

#[global] Program Instance key_countable : Countable key :=
  {|
    encode k := match k with s ↯ f => encode (s, f) end;
    decode p := match decode p : option (string * string) with
                | Some (s, f) => Some (s ↯ f)
                | None => None
                end
  |}.
Next Obligation.
  intros [s f]. simpl. rewrite decode_encode. reflexivity.
Qed.

Definition lstateT (Σ : Type) : Type := (gmap key (option Any.t) * Σ)%type.
Variant lstateE (Σ : Type) : iEvent :=
| SUpdate (V: Type) (run : lstateT Σ → lstateT Σ * V) : lstateE Σ V.
Arguments SUpdate {Σ V} run.

Definition sPut {Σ} x : lstateE Σ unit := SUpdate (λ _, (x, tt)).
Definition sGet {Σ} : lstateE Σ (lstateT Σ) := SUpdate (λ x, (x, x)).

Variant callE : Type → Type :=
| Call (fn : string) (args : Any.t) : callE Any.t
| Spawn (fn : string) (args : Any.t) : callE nat
| Yield (tid : nat) : callE unit
| GetTid : callE nat.

Definition lmodE Σ : Type -> Type := callE +' lstateE Σ +' coreE.

Section EVENTS_HMOD.
  Context {Σ : GRA}.

  Variant pgE : Type -> Type :=
  | SPut (k : key) (v : Any.t) : pgE unit
  | SGet (k : key) : pgE Any.t.

  Variant agE : Type -> Type :=
  | Assume (P : iProp Σ) : agE unit
  | AssumeRes (r : Σ) : agE unit
  | Guarantee (P : iProp Σ) : agE unit.

  Definition crisE := agE +' callE +' pgE +' coreE.
End EVENTS_HMOD.

Section WRAP.
  Context `{coreE -< E}.

  Definition assumeK {R} (P : Prop) (itr : itree E R) := vis (Take P) (fun _ => itr).

  Definition guaranteeK {R} (P : Prop) (itr : itree E R) := vis (Choose P) (fun _ => itr).

  Definition assume (P : Prop) : itree E unit := trigger (Take P) ;;; Ret tt.

  Definition guarantee (P : Prop) : itree E unit := trigger (Choose P) ;;; Ret tt.

  Definition unwrapUK {X R} (x : option X) (ktr : X -> itree E R) : itree E R :=
    match x with
    | Some x => ktr x
    | None => v <- trigger (Take False);; match v: False with end
    end.

  Definition unwrapNK {X R} (x : option X) (ktr : X -> itree E R) : itree E R :=
    match x with
    | Some x => ktr x
    | None => v <- trigger (Choose False);; match v: False with end
    end.

  Definition unwrapU {X} (x : option X) : itree E X :=
    match x with
    | Some x => Ret x
    | None => v <- trigger (Take False);; match v: False with end
    end.

  Definition unwrapN {X} (x : option X) : itree E X :=
    match x with
    | Some x => Ret x
    | None => v <- trigger (Choose False);; match v: False with end
    end.

  Definition triggerUB {A} : itree E A := unwrapU None.

  Definition triggerNB {A} : itree E A := unwrapN None.

  Definition unleftU {X Y} (xy : X + Y) : itree E X :=
    match xy with
    | inl x => Ret x
    | inr y => triggerUB
    end.

  Definition unleftN {X Y} (xy : X + Y) : itree E X :=
    match xy with
    | inl x => Ret x
    | inr y => triggerNB
    end.

  Definition unrightU {X Y} (xy : X + Y) : itree E Y :=
    match xy with
    | inl x => triggerUB
    | inr y => Ret y
    end.

  Definition unrightN {X Y} (xy : X + Y) : itree E Y :=
    match xy with
    | inl x => triggerNB
    | inr y => Ret y
    end.

  Lemma assume_assumeK (P : Prop) :
    assume P = assumeK P (Ret tt).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma assumeK_assume {R} (P : Prop) (itr : itree E R) :
    assumeK P itr = assume P;;; itr.
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma assumeK_bind {U T} (P : Prop) (k1 : itree E U) (k2 : U -> itree E T) :
    (assumeK P k1 >>= k2) = assumeK P (k1 >>= k2).
  Proof using.
    eapply observe_eta; ss.
  Qed.

  Lemma guarantee_guaranteeK (P : Prop) :
    guarantee P = guaranteeK P (Ret tt).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma guaranteeK_guarantee {R} (P : Prop) (k : itree E R) :
    guaranteeK P k = guarantee P;;; k.
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma guaranteeK_bind {U T} (P : Prop) (k1 : itree E U) (k2 : U -> itree E T) :
    (guaranteeK P k1 >>= k2) = guaranteeK P (k1 >>= k2).
  Proof using.
    eapply observe_eta; ss.
  Qed.

  Lemma unwrapU_unwrapUK {X} (x : option X) :
    unwrapU x = unwrapUK x (fun x => Ret x).
  Proof using.
    eapply observe_eta; ss.
  Qed.

  Lemma unwrapUK_unwrapU {X R} (x : option X) (k : X -> itree E R) :
    unwrapUK x k = unwrapU x >>= k.
  Proof using.
    eapply observe_eta; destruct x; ss. f_equal. extensionality x. ss.
  Qed.

  Lemma unwrapUK_bind {X U T} (x : option X) (k1 : X -> itree E U) (k2 : U -> itree E T) :
    (unwrapUK x k1 >>= k2) = unwrapUK x (fun x => k1 x >>= k2).
  Proof using.
    eapply observe_eta; destruct x; ss. f_equal. extensionality x. ss.
  Qed.

  Lemma unwrapN_unwrapNK {X} (x : option X) :
    unwrapN x = unwrapNK x (fun x => Ret x).
  Proof using.
    eapply observe_eta; ss.
  Qed.

  Lemma unwrapNK_unwrapN {X R} (x : option X) (k : X -> itree E R) :
    unwrapNK x k = unwrapN x >>= k.
  Proof using.
    eapply observe_eta; destruct x; ss. f_equal. extensionality x. ss.
  Qed.

  Lemma unwrapNK_bind {X U T} (x : option X) (k1 : X -> itree E U) (k2 : U -> itree E T) :
    (unwrapNK x k1 >>= k2) = unwrapNK x (fun x => k1 x >>= k2).
  Proof using.
    eapply observe_eta; destruct x; ss. f_equal. extensionality x. ss.
  Qed.
End WRAP.

Notation "f '?'" := (unwrapU f) (at level 9).
Notation "f '!'" := (unwrapN f) (at level 9).

Section FancyReal.
  Context `{Σ: GRA}.

  Definition CRIS_FancyReal := "CRIS-FancyReal".
  Global Opaque CRIS_FancyReal.

  (* Epilogue for propheciable specification: extracts the exact resource from precondition *)
  Definition RealUpdate (pp: iProp Σ → iProp Σ → Prop) : itree crisE unit :=
    Seal.sealing CRIS_FancyReal (
      pr <- trigger (Choose Σ);;
      trigger (Guarantee (∀ P Q (PP: pp P Q), P ==∗ Own pr ∗ Q));;;
      trigger (AssumeRes pr)).

  Definition RealUpdateK {R} pp ktr : itree crisE R :=
    @RealUpdate pp >>= ktr.

  Lemma RealUpdate_RealUpdateK pp :
    RealUpdate pp = RealUpdateK pp (λ x, Ret x).
  Proof using. rewrite /RealUpdateK. by ired. Qed.

  Lemma RealUpdateK_RealUpdate {R} pp k :
    @RealUpdateK R pp k = RealUpdate pp >>= k.
  Proof using. refl. Qed.

  Lemma RealUpdateK_bind
      {R1 R2} pp
      (k1 : unit → itree crisE R1) (k2 : R1 → itree crisE R2) :
    @RealUpdateK R1 pp k1 >>= k2 =
    RealUpdateK pp (λ x, k1 x >>= k2).
  Proof using. rewrite /RealUpdateK. by ired. Qed.
End FancyReal.

Record fntyp_t (A : Type) (R : Type) : Type := mk_fntyp_t { }.
Definition fntyp A R : fntyp_t A R := @mk_fntyp_t A R.
Definition fnsig_t A R := (string * fntyp_t A R)%type.
Definition fnsig fn {A R} (t: fntyp_t A R) : fnsig_t A R := (fn, t).
Definition fn_name {A R} (s: fnsig_t A R) : string := s.1.
Definition fn_type {A R} (s: fnsig_t A R) : fntyp_t A R := s.2.
Coercion fn_type : fnsig_t >-> fntyp_t.

Section SYNTAX.
  Context `{coreE -< E, callE -< E, pgE -< E}.

  Definition ccallU {A R} (fs : fnsig_t A R) (varg : A) : itree E R :=
    vret <- trigger (Call (fn_name fs) (varg↑));; vret↓?.
  
  Definition ccallN {A R} (fs : fnsig_t A R) (varg : A) : itree E R :=
    vret <- trigger (Call (fn_name fs) (varg↑));; vret↓!.
  
  Definition cfunN {A R} (ft: fntyp_t A R) (body : A → itree E R) : Any.t → itree E Any.t :=
    λ varg, varg <- varg↓!;; vret <- body varg;; Ret vret↑.

  Definition cfunU {A R} (ft: fntyp_t A R) (body : A → itree E R) : Any.t → itree E Any.t :=
    λ varg, varg <- varg↓?;; vret <- body varg;; Ret vret↑.

  Definition cput {T} k (v : T) : itree E unit :=
    trigger (SPut k v↑).

  Definition cgetU {T} k : itree E T :=
    v <- trigger (SGet k);; v↓?.

  Definition cgetN {T} k : itree E T :=
    v <- trigger (SGet k);; (v↓!).
End SYNTAX.

Lemma case_itrL {Σ : Type} R (itr : itree (lmodE Σ) R) :
  (exists r, itr = Ret r) \/
  (exists itr', itr = tau;; itr') \/
  (exists V (e : coreE V) ktr, itr = v <- trigger e;; ktr v) \/
  (exists V run ktr, itr = v <- trigger (@SUpdate Σ V run);; ktr v) \/
  (exists V (e : callE V) ktr, itr = v <- trigger e;; ktr v).
Proof.
  ides itr; eauto.
  right. right. destruct e as [e | [e | e] ].
  - do 2 right. esplits. rewrite bind_trigger. eauto.
  - destruct e. right. left. esplits. rewrite bind_trigger. eauto.
  - left. esplits. rewrite bind_trigger. eauto.
Qed.

Lemma case_itrH `{Σ : GRA} {R} (itrH : itree crisE R) :
  (exists v, itrH = Ret v) \/
  (exists itrH', itrH = tau;; itrH') \/
  (exists P itrH', itrH = (trigger (Assume P);;; itrH')) \/
  (exists r itrH', itrH = (trigger (AssumeRes r) >>= itrH')) \/
  (exists P itrH', itrH = (trigger (Guarantee P);;; itrH')) \/
  (exists R (c : callE R) ktrH', itrH = (trigger c >>= ktrH')) \/
  (exists R (s : pgE R) ktrH', itrH = (trigger s >>= ktrH')) \/
  (exists R (e : coreE R) ktrH', itrH = (trigger e >>= ktrH')).
Proof using.
  ides itrH; eauto.
  right; right.
  destruct e; [destruct a|destruct s; [|destruct s]].
  - do 0 right; left. exists P, (k()). unfold trigger. rewrite bind_vis.
    repeat f_equal. extensionality x. destruct x. rewrite bind_ret_l. eauto.
  - do 1 right; left. exists r, k. unfold trigger. rewrite bind_vis.
    repeat f_equal. extensionality x. rewrite bind_ret_l. eauto.
  - do 2 right; left. exists P, (k()). unfold trigger. rewrite bind_vis.
    repeat f_equal. extensionality x. destruct x. rewrite bind_ret_l. eauto.
  - do 3 right; left. exists X, c, k. unfold trigger. rewrite bind_vis.
    repeat f_equal. extensionality x. rewrite bind_ret_l. eauto.
  - do 4 right; left. exists X, p, k. unfold trigger. rewrite bind_vis.
    repeat f_equal. extensionality x. rewrite bind_ret_l. eauto.
  - do 5 right. exists X, c, k. unfold trigger. rewrite bind_vis.
    repeat f_equal. extensionality x. rewrite bind_ret_l. eauto.
Qed.

(* Masks for sandboxing *)
Definition emask {Σ : GRA} : Type := ∀ X, crisE X → bool.

Definition msk_true `{Σ : GRA} : emask := λ X e, true.

Definition msk_scp `{Σ : GRA} (scp : list string) (msk : emask) : emask :=
  λ X e,
    match e with
    | (||SPut k _|)%sum => bool_decide (scope k ∈ scp)
    | (||SGet k|)%sum => bool_decide (scope k ∈ scp)
    | _ => msk X e
    end.

Definition msk_real `{Σ : GRA} (msk : emask) : emask :=
  λ X e,
    match e with
    | (Assume P|)%sum => false
    | (|||Take X)%sum => excluded_middle_informative (∃ P : Prop, X = P)
    | _ => msk X e
    end.

Definition msk_pure `{Σ : GRA} : emask := λ X e,
  match e with
  | (_|)%sum => true
  | (|_|)%sum  => false
  | (||_|)%sum  => false
  | (|||_)%sum  => true
  end.

  Definition msk_sys `{Σ : GRA} : emask := λ X e,
    match e with
    | inr1 (inl1 (Spawn _ _)) => true
    | inr1 (inl1 (Yield _)) => true
    | inr1 (inl1 (GetTid)) => true
    | _ => false
    end.

Definition msk_and `{Σ : GRA} (msk1 msk2 : emask) : emask :=
  λ X e, msk1 X e && msk2 X e.

Definition msk_or `{Σ : GRA} (msk1 msk2 : emask) : emask :=
  λ X e, msk1 X e || msk2 X e.

Definition img_msk `{Σ : GRA} (msk : emask) : Prop :=
  (∀ T, msk _ (subevent _ (Take T)) = true)
  ∧ (∀ T, msk _ (subevent _ (Choose T)) = true)
  ∧ (∀ P, msk _ (subevent _ (Assume P)) = true)
  ∧ (∀ P, msk _ (subevent _ (AssumeRes P)) = true)
  ∧ (∀ P, msk _ (subevent _ (Guarantee P)) = true).

Definition call_msk `{Σ : GRA} (msk : emask) : Prop :=
  ∀ fn x y,
    msk _ (subevent _ (Call fn x)) = msk _ (subevent _ (Call fn y))
    ∧ msk _ (subevent _ (Spawn fn x)) = msk _ (subevent _ (Spawn fn y)).

Definition msk_sub `{Σ : GRA} (m1 m2 : emask) : Prop :=
  ∀ X e, m1 X e → m2 X e.
