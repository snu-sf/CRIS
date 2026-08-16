From CRIS.modules Require Import FSpec.
From CRIS.common Require Import Common.
From CRIS.proofmode Require Import HNormClasses.

Module SB. Section SB.
  Context `{Σ : GRA}.

  (**** Sandboxing ****)

  Definition msk_default T (e : crisE T) : bool :=
    match e with
    | (|||Choose X)%sum => true
    | (|||Take X)%sum => excluded_middle_informative (∃ P : Prop, X = P)
    | (Guarantee _|)%sum => true
    | (AssumeRes _|)%sum => true
    | _ => false
    end.

  Definition handle (msk : emask) : crisE ~> itreeV crisE :=
    λ T e,
      if msk T (subevent _ e) || msk_default T (subevent _ e)
      then itreeV_vis (subevent _ e) (λ x, Ret x)
      else itreeV_vis (subevent _ (Take False)) (λ v, Ret (False_rect _ v)).

  Definition sandbox (msk : emask) {T} (itr : itree crisE T) : itree crisE T :=
    interpV (handle msk) itr.

  Definition sandbox_body (kb : emask * fbody) : Any.t → itree crisE Any.t :=
    λ arg, sandbox kb.1 (kb.2 arg).
End SB. End SB.

(* Sandboxing interpretation lemmas *)
Module SBRed. Section SBRed.
  Context `{Σ : GRA}.

  Lemma bind msk {A B} (itr : itree crisE A) (ktr : A → itree crisE B) :
    SB.sandbox msk (itr >>= ktr) =
    a <- (SB.sandbox msk itr);; (SB.sandbox msk (ktr a)).
  Proof using. rewrite /SB.sandbox interpV_bind; eauto. Qed.

  Lemma tau msk {A} (itr : itree crisE A) :
    SB.sandbox msk (tau;; itr) = tau;; (SB.sandbox msk itr).
  Proof using. rewrite /SB.sandbox interpV_tau; eauto. Qed.

  Lemma ret msk {A} (a : A) :
    SB.sandbox msk (Ret a) = Ret a.
  Proof using. rewrite /SB.sandbox interpV_ret; eauto. Qed.

  Lemma vis msk {X R} (e : crisE X) (k : X → itree crisE R) :
    SB.sandbox msk (Vis e k) =
    if msk X e || SB.msk_default X e
    then Vis e (λ x, SB.sandbox msk (k x))
    else vis (Take False) (λ v, Ret (False_rect _ v)).
  Proof using.
    rewrite /SB.sandbox interpV_vis /SB.handle ?subevent_subevent.
    case_match eqn : H; rewrite H /=.
    eapply observe_eta; grind; ss; f_equal; extensionalities; ss; grind.
    ired.
    eapply observe_eta; grind; ss; f_equal; extensionalities; ss; grind. 
  Qed.

  Lemma assumeK msk {R} P (itr : itree crisE R) :
    SB.sandbox msk (assumeK P itr) = assumeK P (SB.sandbox msk itr).
  Proof using.
    eapply observe_eta; ss. rewrite /SB.handle; s.
    destruct (excluded_middle_informative _); s; cycle 1.
    { exfalso. eapply n. et. }
    bsimpl; s; f_equal; extensionalities; ss; ired; eauto.
  Qed.

  Lemma guaranteeK msk {R} P (itr : itree crisE R) :
    SB.sandbox msk (guaranteeK P itr) = guaranteeK P (SB.sandbox msk itr).
  Proof using.
    eapply observe_eta; ss. rewrite /SB.handle; s.
    bsimpl; s; f_equal; extensionalities; ss; ired; eauto.
  Qed.

  Lemma unwrapUK msk {X R} x (ktr : X → itree crisE R) :
    SB.sandbox msk (unwrapUK x ktr) = unwrapUK x (λ x, SB.sandbox msk (ktr x)).
  Proof using.
    eapply observe_eta; ss. destruct x; et; ss. rewrite /SB.handle; s.
    destruct (excluded_middle_informative _); s; cycle 1.
    { exfalso. eapply n. et. }
    bsimpl; s; f_equal; extensionalities; ss; ired; eauto.
  Qed.

  Lemma unwrapNK msk {X R} (x : option X) (ktr : X → itree crisE R) :
    SB.sandbox msk (unwrapNK x ktr) = unwrapNK x (λ x, SB.sandbox msk (ktr x)).
  Proof using.
    eapply observe_eta; ss. destruct x; et; ss. rewrite /SB.handle; s.
    bsimpl; s; f_equal; extensionalities; ss; ired; eauto.
  Qed.

  Lemma ruK msk {R} pp (ktr : _ → itree crisE R) :
    SB.sandbox msk (RealUpdateK pp ktr) = RealUpdateK pp (λ x, SB.sandbox msk (ktr x)).
  Proof using.
    rewrite /RealUpdateK /RealUpdate. unseal CRIS_FancyReal. ired.
    rewrite !SBRed.bind !SBRed.vis !trigger_vis; s; bsimpl.
    f_equal; [repeat f_equal; extensionalities; apply ret|extensionalities].
    rewrite !SBRed.bind !SBRed.vis !trigger_vis; s; bsimpl.
    repeat (repeat f_equal; extensionalities); apply ret.
  Qed.

End SBRed. End SBRed.

Section INSTANCES.

  #[global] Instance HNormContext_SB_sandbox
    `{Σ : GRA} {R} msk (itr : itree crisE R)
    : HNormContext (SB.sandbox msk itr) (SB.sandbox msk) itr.
  Proof. constructor. reflexivity. Qed.

  #[global] Instance HNormReduce_SB_ret
    `{Σ : GRA} {A} msk (x : A)
    : HNormReduce (SB.sandbox msk) (Ret x) (Ret x) false
    | 10.
  Proof. constructor. eapply SBRed.ret. Qed.

  #[global] Instance HNormReduce_SB_tau
    `{Σ : GRA} {A} msk (t : itree crisE A)
    : HNormReduce
        (SB.sandbox msk) (Tau t) (Tau (SB.sandbox msk t)) false
    | 10.
  Proof. constructor. eapply SBRed.tau. Qed.

  #[global] Instance HNormReduce_SB_vis_choose
    `{Σ : GRA} {X R} msk (k : X -> itree crisE R)
    : HNormReduce
        (SB.sandbox msk) (vis (Choose X) k)
        (vis (Choose X) (fun x => SB.sandbox msk (k x))) false
    | 5.
  Proof.
    constructor. rewrite SBRed.vis /SB.msk_default /= orb_true_r. reflexivity.
  Qed.

  #[global] Instance HNormReduce_SB_vis_take
    `{Σ : GRA} {P : Prop} {R} msk (k : P -> itree crisE R)
    : HNormReduce
        (SB.sandbox msk) (vis (Take P) k)
        (vis (Take P) (fun x => SB.sandbox msk (k x))) false
    | 5.
  Proof.
    constructor. rewrite SBRed.vis /SB.msk_default /=.
    match goal with
    | |- context[excluded_middle_informative ?Q] =>
        destruct (excluded_middle_informative Q) eqn:DEC
    end; cycle 1.
    { exfalso. apply n. exists P. reflexivity. }
    s. rewrite orb_true_r. reflexivity.
  Qed.

  #[global] Instance HNormReduce_SB_vis
    `{Σ : GRA} {X R} msk (e : crisE X) (b : bool)
    (k : X -> itree crisE R)
    `{H : HNormBool (msk X e || SB.msk_default X e) b}
    : HNormReduce
        (SB.sandbox msk) (Vis e k)
        (if b
         then Vis e (fun x => SB.sandbox msk (k x))
         else vis (Take False) (fun v => Ret (False_rect _ v))) true
    | 10.
  Proof.
    constructor.
    rewrite SBRed.vis (@HNormBool_equal _ _ H).
    reflexivity.
  Qed.

  #[global] Instance HNormReduce_SB_assumeK
    `{Σ : GRA} {R} msk P (t : itree crisE R)
    : HNormReduce
        (SB.sandbox msk) (assumeK P t)
        (assumeK P (SB.sandbox msk t)) false
    | 5.
  Proof. constructor. eapply SBRed.assumeK. Qed.

  #[global] Instance HNormReduce_SB_guaranteeK
    `{Σ : GRA} {R} msk P (t : itree crisE R)
    : HNormReduce
        (SB.sandbox msk) (guaranteeK P t)
        (guaranteeK P (SB.sandbox msk t)) false
    | 5.
  Proof. constructor. eapply SBRed.guaranteeK. Qed.

  #[global] Instance HNormReduce_SB_unwrapUK
    `{Σ : GRA} {X R} msk (x : option X)
    (k : X -> itree crisE R)
    : HNormReduce
        (SB.sandbox msk) (unwrapUK x k)
        (unwrapUK x (fun y => SB.sandbox msk (k y))) false
    | 15.
  Proof. constructor. eapply SBRed.unwrapUK. Qed.

  #[global] Instance HNormReduce_SB_unwrapNK
    `{Σ : GRA} {X R} msk (x : option X)
    (k : X -> itree crisE R)
    : HNormReduce
        (SB.sandbox msk) (unwrapNK x k)
        (unwrapNK x (fun y => SB.sandbox msk (k y))) false
    | 15.
  Proof. constructor. eapply SBRed.unwrapNK. Qed.

  #[global] Instance HNormReduce_SB_RealUpdateK
    `{Σ : GRA} {R} msk pp (k : unit -> itree crisE R)
    : HNormReduce
        (SB.sandbox msk) (RealUpdateK pp k)
        (RealUpdateK pp (fun x => SB.sandbox msk (k x))) false
    | 5.
  Proof. constructor. eapply SBRed.ruK. Qed.

  #[global] Instance HNormReduce_SB_bind
    `{Σ : GRA} {A B} msk (t : itree crisE A)
    (k : A -> itree crisE B)
    : HNormReduce
        (SB.sandbox msk) (t >>= k)
        (x <- SB.sandbox msk t;; SB.sandbox msk (k x)) false
    | 30.
  Proof. constructor. eapply SBRed.bind. Qed.

End INSTANCES.

Section Properties.
  Context `{Σ: GRA}.

  Lemma sandbox_sandbox {R} (t : itree crisE R) (msk1 msk2 : emask) :
    msk_sub msk1 msk2 →
    SB.sandbox msk2 (SB.sandbox msk1 t) = SB.sandbox msk1 t.
  Proof using.
    intros Hmsk; eapply bisim_is_eq. ginit.
    revert R t msk1 msk2 Hmsk. gcofix CIH. i.
    rewrite (itree_eta t). destruct (observe t).
    { rewrite !SBRed.ret. gstep. econs. reflexivity. }
    { rewrite !SBRed.tau. gstep. econs. gbase. et. }

    rewrite -bind_trigger !SBRed.bind.
    rewrite !SBRed.vis; case_match eqn : Hmsk1; cycle 1.
    { rewrite !SBRed.vis; case_match eqn : Hmsk2; ss.
      { gstep. rewrite !bind_vis. econs; ss. }
      gstep. rewrite !bind_vis. econs; ss.
    }
    rewrite !SBRed.vis; case_match eqn : Hmsk2; ss; cycle 1.
    { bsimpl. destruct Hmsk2 as [E1 E2]. rewrite E2 in Hmsk1. des; ss.
      eapply Hmsk in Hmsk1. rewrite E1 in Hmsk1. ss. }
    rewrite !bind_vis. gstep. econs. intros x.
    rewrite !SBRed.ret; ired.
    gbase. eapply CIH. auto.
  Qed.
End Properties.

Notation "░ it" := (SB.sandbox _ it) (at level 60, only printing).
Notation "'⇓sbox(' msk ')'" := (SB.sandbox msk) (at level 60, only parsing).
