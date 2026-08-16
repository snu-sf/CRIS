From CRIS.common Require Import Common.
From CRIS.modules Require Import FSpec LMod.
From CRIS.proofmode Require Import HNormClasses.

Module ModTr. Section MID.
  Context `{Σ : GRA}.

  Definition put_res (mr : Σ) : itree (lmodE Σ) unit :=
    '(ms, _): _ <- trigger sGet;;
    trigger (sPut (ms, mr)).

  Definition get_res {R: Type} (k : Σ → itree (lmodE Σ) R) : itreeV (lmodE Σ) R :=
    itreeV_vis (subevent _ sGet) (λ '(ms, mr),
        k mr).

  Definition put_kv (k : key) (v : Any.t) : itreeV (lmodE Σ) unit :=
    itreeV_vis (subevent _ sGet) (λ '(ms, mr),
        trigger (sPut (<[k := Some v]> ms, mr))).

  Definition get_kv (k : key) : itreeV (lmodE Σ) Any.t :=
    itreeV_vis (subevent _ sGet) (λ '(ms, mr),
        Ret (default (tt↑) (mjoin (ms !! k)))).

  (* mid to tgt code *)
  Definition handle_pgE : pgE ~> itreeV (lmodE Σ) :=
    λ _ e,
      match e with
      | SPut k v => put_kv k v
      | SGet k => get_kv k
      end.

  Definition handle_Assume (P : iProp Σ) : itreeV (lmodE Σ) unit :=
    get_res (λ mr,
      mr' <- trigger (Take Σ);;
      assume (✓ mr' ∧ (Own mr' ⊢ |==> P ∗ Own mr));;;
      put_res mr').

  Definition handle_AssumeRes (r : Σ) : itreeV (lmodE Σ) unit :=
    get_res (λ mr,
      assume (✓ (r ⋅ mr));;;
      put_res (r ⋅ mr)).

  Definition handle_Guarantee (P : iProp Σ) : itreeV (lmodE Σ) unit :=
    get_res (λ mr,
      mr' <- trigger (Choose Σ);;
      guarantee (✓ mr' ∧ (Own mr ⊢ |==> P ∗ Own mr'));;;
      put_res mr').

  Definition handle_agE : agE ~> itreeV (lmodE Σ) :=
    λ _ e,
      match e with
      | Assume P => handle_Assume P
      | AssumeRes P => handle_AssumeRes P
      | Guarantee P => handle_Guarantee P
      end.

  Definition handle_crisE : crisE ~> itreeV (lmodE Σ) :=
    λ T e,
      match e with
      | (ag|)%sum => handle_agE _ ag
      | (|c|)%sum => itreeV_vis (subevent _ c) (λ r, Ret r)
      | (||pg|)%sum => handle_pgE _ pg
      | (|||c)%sum => itreeV_vis (subevent _ c) (λ r, Ret r)
      end.

  Definition trans : itree crisE ~> itree (lmodE Σ) :=
    interpV handle_crisE.

  Definition trans_fnsem (f : Any.t → itree crisE Any.t) : Any.t → itree (lmodE Σ) Any.t :=
    λ x, trans _ (f x).
End MID. End ModTr.
Arguments ModTr.trans {Σ} [T].

Module Red. Section RED.
  Import ModTr.
  (* itree reduction lemmas *)
  Context `{Σ : GRA}.

  Lemma bind (R S : Type) (s : itree crisE R) (k : R → itree crisE S) :
    trans (s >>= k) = st <- trans s;; trans (k st).
  Proof using. rewrite /trans interpV_bind //. Qed.

  Lemma tau (R : Type) (t : itree _ R) :
    trans (tau;; t) = tau;; (trans t).
  Proof using. rewrite /trans interpV_tau //. Qed.

  Lemma ret (R : Type) (t : R) :
    trans (Ret t) = Ret t.
  Proof using. rewrite /trans interpV_ret //. Qed.

  Lemma call (R : Type) (c : callE R) :
    trans (trigger c) = trigger c.
  Proof using. rewrite /trans interpV_trigger /=; grind. Qed.

  Lemma spawn fn arg :
    trans (trigger (Spawn fn arg)) = trigger (Spawn fn arg).
  Proof using. rewrite /trans interpV_trigger /=; grind. Qed.

  Lemma yield tid :
    trans (trigger (Yield tid)) = trigger (Yield tid).
  Proof using. rewrite /trans interpV_trigger /=; grind. Qed.

  Lemma pg (R : Type) (i : pgE R) :
    trans (trigger i) = itreeV_itree (handle_pgE _ i).
  Proof using. rewrite /trans interpV_trigger //. Qed.

  Lemma core (R : Type) (i : coreE R) :
    trans (trigger i) = trigger i.
  Proof using. rewrite /trans interpV_trigger /=; grind. Qed.

  Lemma triggerUB (R : Type) :
    trans (triggerUB) = triggerUB (A:=R).
  Proof using.
    rewrite /trans /triggerUB interpV_bind interpV_trigger; grind.
  Qed.

  Lemma triggerNB (R : Type) :
    trans (triggerNB) = triggerNB (A:=R).
  Proof using.
    rewrite /trans /triggerNB interpV_bind interpV_trigger; grind.
  Qed.

  Lemma unwrapU (R : Type) (i : option R) :
    trans (@unwrapU crisE _ _ i) = unwrapU i.
  Proof using.
    rewrite /trans /unwrapU; des_ifs; s; try rewrite interpV_ret; eauto using triggerUB.
  Qed.

  Lemma unwrapN (R : Type) (i : option R) :
    trans (@unwrapN crisE _ _ i) = unwrapN i.
  Proof using.
    rewrite /trans /unwrapN; des_ifs; s; try rewrite interpV_ret; eauto using triggerNB.
  Qed.

  Lemma Assume P :
    trans (trigger (Assume P)) = itreeV_itree (handle_Assume P).
  Proof using. rewrite /trans interpV_trigger //. Qed.

  Lemma AssumeRes r :
    trans (trigger (AssumeRes r)) = itreeV_itree (handle_AssumeRes r).
  Proof using. rewrite /trans interpV_trigger //. Qed.
  
  Lemma Guarantee P :
    trans (trigger (Guarantee P)) = itreeV_itree (handle_Guarantee P).
  Proof using. rewrite /trans interpV_trigger //. Qed.

  Lemma ext (R : Type) (itr0 itr1 : itree _ R) (EQ : itr0 = itr1) :
    trans itr0 = trans itr1.
  Proof using. subst; et. Qed.

  (* TODO : Same lemmas for other interps ( not defined yet. ) *)
  Global Instance rdb : red_database (mk_box (@ModTr.trans)) :=
    mk_rdb
      0
      (mk_box bind)
      (mk_box tau)
      (mk_box ret)
      (mk_box call)
      (* (mk_box spawn) *)
      (mk_box yield)
      (mk_box core)
      (mk_box pg)
      (mk_box triggerUB)
      (mk_box triggerNB)
      (mk_box unwrapU)
      (mk_box unwrapN)
      (mk_box Assume)
      (mk_box Guarantee)
      (mk_box ext).
End RED. End Red.

Section INSTANCES.
  Context `{Σ : GRA}.

  #[global] Instance HNormContext_ModTr_trans
    {R} (itr : itree crisE R)
    : HNormContext
        (ModTr.trans itr) (@ModTr.trans Σ R) itr.
  Proof. constructor. reflexivity. Qed.

  #[global] Instance HNormReduce_ModTr_ret
    {R} (x : R)
    : HNormReduce
        (@ModTr.trans Σ R) (Ret x) (Ret x) false
    | 10.
  Proof. constructor. eapply Red.ret. Qed.

  #[global] Instance HNormReduce_ModTr_tau
    {R} (t : itree crisE R)
    : HNormReduce
        (@ModTr.trans Σ R) (Tau t)
        (Tau (ModTr.trans t)) false
    | 10.
  Proof. constructor. eapply Red.tau. Qed.

  #[global] Instance HNormReduce_ModTr_vis_Assume
    {R} P (k : unit -> itree crisE R)
    : HNormReduce
        (@ModTr.trans Σ R) (vis (Events.Assume P) k)
        (x <- itreeV_itree (ModTr.handle_Assume P);;
         ModTr.trans (k x)) false
    | 10.
  Proof.
    constructor. rewrite vis_trigger Red.bind Red.Assume. reflexivity.
  Qed.

  #[global] Instance HNormReduce_ModTr_vis_Take
    {R X} (k : X -> itree crisE R)
    : HNormReduce
        (@ModTr.trans Σ R) (vis (Events.Take X) k)
        (x <- trigger (Take X);; ModTr.trans (k x)) false
    | 10.
  Proof.
    constructor.
    rewrite /ModTr.trans interpV_vis /itreeV_itree /=.
    rewrite bind_ret_r. reflexivity.
  Qed.

End INSTANCES.
