From CRIS.common Require Import Common.
From CRIS.modules Require Import FSpec SModTr.
From CRIS.proofmode Require Import HNormClasses.

Section BOOL_INSTANCES.

  #[global] Instance HNormBool_orb_true_l
    a b
    : HNormBool a true -> HNormBool (a || b) true
    | 5.
  Proof. intros [->]. constructor. eapply orb_true_l. Qed.

  #[global] Instance HNormBool_orb_true_r
    a b
    : HNormBool b true -> HNormBool (a || b) true
    | 5.
  Proof. intros [->]. constructor. eapply orb_true_r. Qed.

  #[global] Instance HNormBool_orb_false_l
    a b b'
    : HNormBool a false -> HNormBool b b' -> HNormBool (a || b) b'
    | 10.
  Proof. intros [->] [->]. constructor. eapply orb_false_l. Qed.

  #[global] Instance HNormBool_orb_false_r
    a a' b
    : HNormBool a a' -> HNormBool b false -> HNormBool (a || b) a'
    | 10.
  Proof. intros [->] [->]. constructor. eapply orb_false_r. Qed.

  #[global] Instance HNormBool_orb_cong
    a a' b b'
    : HNormBool a a' -> HNormBool b b' -> HNormBool (a || b) (a' || b')
    | 15.
  Proof. intros [->] [->]. constructor. reflexivity. Qed.

  #[global] Instance HNormBool_andb_true_l
    a b b'
    : HNormBool a true -> HNormBool b b' -> HNormBool (a && b) b'
    | 10.
  Proof. intros [->] [->]. constructor. eapply andb_true_l. Qed.

  #[global] Instance HNormBool_andb_true_r
    a a' b
    : HNormBool a a' -> HNormBool b true -> HNormBool (a && b) a'
    | 10.
  Proof. intros [->] [->]. constructor. eapply andb_true_r. Qed.

  #[global] Instance HNormBool_andb_false_l
    a b
    : HNormBool a false -> HNormBool (a && b) false
    | 5.
  Proof. intros [->]. constructor. eapply andb_false_l. Qed.

  #[global] Instance HNormBool_andb_false_r
    a b
    : HNormBool b false -> HNormBool (a && b) false
    | 5.
  Proof. intros [->]. constructor. eapply andb_false_r. Qed.

  #[global] Instance HNormBool_andb_cong
    a a' b b'
    : HNormBool a a' -> HNormBool b b' -> HNormBool (a && b) (a' && b')
    | 15.
  Proof. intros [->] [->]. constructor. reflexivity. Qed.

  #[global] Instance HNormBool_refl
    a
    : HNormBool a a
    | 20.
  Proof. constructor. reflexivity. Qed.

End BOOL_INSTANCES.

Section BIND_INSTANCES.

  #[global] Instance HNormContext_bind
    {E A B} (itr : itree E A) (ktr : A -> itree E B)
    : HNormContext (itr >>= ktr) (fun itr' => itr' >>= ktr) itr.
  Proof. constructor. reflexivity. Qed.

  #[global] Instance HNormReduce_bind_ret
    {E A B} (ktr : A -> itree E B) (x : A)
    : HNormReduce (fun t => t >>= ktr) (Ret x) (ktr x) true
    | 10.
  Proof. constructor. eapply bind_ret_l. Qed.

  #[global] Instance HNormReduce_bind_tau
    {E A B} (ktr : A -> itree E B) (t : itree E A)
    : HNormReduce (fun t => t >>= ktr) (Tau t) (Tau (t >>= ktr)) false
    | 10.
  Proof. constructor. eapply bind_tau. Qed.

  #[global] Instance HNormReduce_bind_vis
    {E A B X} (ktr : A -> itree E B)
    (e : E X) (k : X -> itree E A)
    : HNormReduce
        (fun t => t >>= ktr) (Vis e k)
        (Vis e (fun x => k x >>= ktr)) false
    | 20.
  Proof. constructor. eapply bind_vis. Qed.

  #[global] Instance HNormReduce_bind_assumeK
    `{coreE -< E} {A B} (ktr : A -> itree E B) P
    (t : itree E A)
    : HNormReduce
        (fun t => t >>= ktr) (assumeK P t)
        (assumeK P (t >>= ktr)) false
    | 5.
  Proof. constructor. eapply assumeK_bind. Qed.

  #[global] Instance HNormReduce_bind_guaranteeK
    `{coreE -< E} {A B} (ktr : A -> itree E B) P
    (t : itree E A)
    : HNormReduce
        (fun t => t >>= ktr) (guaranteeK P t)
        (guaranteeK P (t >>= ktr)) false
    | 5.
  Proof. constructor. eapply guaranteeK_bind. Qed.

  #[global] Instance HNormReduce_bind_unwrapUK
    `{coreE -< E} {X A B} (ktr : A -> itree E B)
    (x : option X) (k : X -> itree E A)
    : HNormReduce
        (fun t => t >>= ktr) (unwrapUK x k)
        (unwrapUK x (fun y => k y >>= ktr)) false
    | 15.
  Proof. constructor. eapply unwrapUK_bind. Qed.

  #[global] Instance HNormReduce_bind_unwrapNK
    `{coreE -< E} {X A B} (ktr : A -> itree E B)
    (x : option X) (k : X -> itree E A)
    : HNormReduce
        (fun t => t >>= ktr) (unwrapNK x k)
        (unwrapNK x (fun y => k y >>= ktr)) false
    | 15.
  Proof. constructor. eapply unwrapNK_bind. Qed.

  #[global] Instance HNormReduce_bind_RealUpdateK
    `{Σ : GRA} {A B} (ktr : A -> itree crisE B)
    pp (k : unit -> itree crisE A)
    : HNormReduce
        (fun t => t >>= ktr) (RealUpdateK pp k)
        (RealUpdateK pp (fun x => k x >>= ktr)) false
    | 5.
  Proof. constructor. eapply RealUpdateK_bind. Qed.

  #[global] Instance HNormReduce_bind_bind
    {E A B C} (ktr : B -> itree E C)
    (t : itree E A) (k : A -> itree E B)
    : HNormReduce
        (fun t => t >>= ktr) (t >>= k)
        (t >>= fun x => k x >>= ktr) false
    | 30.
  Proof. constructor. eapply bind_bind. Qed.

End BIND_INSTANCES.

Section FINISH_INSTANCES.

  #[global] Instance HNormFinish_vis
    {E X R} (e : E X) (k : X -> itree E R)
    : HNormFinish (Vis e k) (ITree.trigger e >>= k)
    | 20.
  Proof.
    constructor. unfold ITree.trigger. eapply observe_eta; cbn.
    f_equal. extensionality x. eapply observe_eta. reflexivity.
  Qed.

  #[global] Instance HNormFinish_assumeK
    `{coreE -< E} {R} P (t : itree E R)
    : HNormFinish (assumeK P t) (assume P;;; t)
    | 5.
  Proof. constructor. eapply assumeK_assume. Qed.

  #[global] Instance HNormFinish_guaranteeK
    `{coreE -< E} {R} P (t : itree E R)
    : HNormFinish (guaranteeK P t) (guarantee P;;; t)
    | 5.
  Proof. constructor. eapply guaranteeK_guarantee. Qed.

  #[global] Instance HNormFinish_unwrapUK
    `{coreE -< E} {X R} (x : option X) (k : X -> itree E R)
    : HNormFinish (unwrapUK x k) (unwrapU x >>= k)
    | 5.
  Proof. constructor. eapply unwrapUK_unwrapU. Qed.

  #[global] Instance HNormFinish_unwrapNK
    `{coreE -< E} {X R} (x : option X) (k : X -> itree E R)
    : HNormFinish (unwrapNK x k) (unwrapN x >>= k)
    | 5.
  Proof. constructor. eapply unwrapNK_unwrapN. Qed.

  #[global] Instance HNormFinish_RealUpdateK
    `{Σ : GRA} {R} pp (k : unit -> itree crisE R)
    : HNormFinish (RealUpdateK pp k) (RealUpdate pp >>= k)
    | 5.
  Proof. constructor. eapply RealUpdateK_RealUpdate. Qed.

End FINISH_INSTANCES.

Section EXPAND_INSTANCES.

  #[global] Instance HNormExpand_trigger
    `{subE -< E} {X : Type} (e : subE X)
    : HNormExpand (trigger e : itree E X) (vis e (fun x => Ret x))
    | 10.
  Proof. econstructor. reflexivity. Qed.

  #[global] Instance HNormExpand_fbody_trivial
    {Σ a}
    : HNormExpand
        (@fbody_trivial Σ a)
        (vis (Choose Any.t) (fun x => Ret x))
    | 10.
  Proof. econstructor. reflexivity. Qed.

  #[global] Instance HNormExpand_cput
    `{pgE -< E} {T : Type} (k : key) (v : T)
    : HNormExpand
        (cput k v : itree E ())
        (vis (SPut k v↑) (fun x => Ret x))
    | 10.
  Proof. econstructor. reflexivity. Qed.

  #[global] Instance HNormExpand_assume
    `{coreE -< E} (P : Prop)
    : HNormExpand (assume P : itree E ()) (assumeK P (Ret tt))
    | 10.
  Proof. econstructor. apply assume_assumeK. Qed.

  #[global] Instance HNormExpand_guarantee
    `{coreE -< E} (P : Prop)
    : HNormExpand (guarantee P : itree E ()) (guaranteeK P (Ret tt))
    | 10.
  Proof. econstructor. apply guarantee_guaranteeK. Qed.

  #[global] Instance HNormExpand_unwrapU_Any
    `{coreE -< E} {X : Type} (x : X)
    : HNormExpand
        (unwrapU (Any.downcast (Any.upcast x)) : itree E X)
        (Ret x)
    | 5.
  Proof. econstructor. rewrite Any.upcast_downcast. reflexivity. Qed.

  #[global] Instance HNormExpand_unwrapU_SAny
    `{coreE -< E} {X : Type} (x : X)
    : HNormExpand
        (unwrapU (SAny.downcast (SAny.upcast x)) : itree E X)
        (Ret x)
    | 5.
  Proof. econstructor. rewrite SAny.upcast_downcast. reflexivity. Qed.

  #[global] Instance HNormExpand_unwrapU
    `{coreE -< E} {X : Type} (x : option X)
    : HNormExpand
        (unwrapU x : itree E X)
        (unwrapUK x (fun x => Ret x))
    | 20.
  Proof. econstructor. apply unwrapU_unwrapUK. Qed.

  #[global] Instance HNormExpand_unwrapN_Any
    `{coreE -< E} {X : Type} (x : X)
    : HNormExpand
        (unwrapN (Any.downcast (Any.upcast x)) : itree E X)
        (Ret x)
    | 5.
  Proof. econstructor. rewrite Any.upcast_downcast. reflexivity. Qed.

  #[global] Instance HNormExpand_unwrapN_SAny
    `{coreE -< E} {X : Type} (x : X)
    : HNormExpand
        (unwrapN (SAny.downcast (SAny.upcast x)) : itree E X)
        (Ret x)
    | 5.
  Proof. econstructor. rewrite SAny.upcast_downcast. reflexivity. Qed.

  #[global] Instance HNormExpand_unwrapN
    `{coreE -< E} {X : Type} (x : option X)
    : HNormExpand
        (unwrapN x : itree E X)
        (unwrapNK x (fun x => Ret x))
    | 20.
  Proof. econstructor. apply unwrapN_unwrapNK. Qed.

  #[global] Instance HNormExpand_RealUpdate
    `{Σ : GRA} (pp : iProp Σ -> iProp Σ -> Prop)
    : HNormExpand
        (RealUpdate pp)
        (RealUpdateK pp (fun x => Ret x))
    | 10.
  Proof. econstructor. apply RealUpdate_RealUpdateK. Qed.

  #[global] Instance HNormExpand_HoareCall
    `{Σ : GRA} omsk fn varg
    : HNormExpand
        (@SModTr.HoareCall Σ None omsk fn varg)
        (vis (Call fn varg) (fun x => Ret x))
    | 10.
  Proof. econstructor. reflexivity. Qed.

  #[global] Instance HNormExpand_cgetU
    `{coreE -< E, pgE -< E} {T : Type} (k : key)
    : HNormExpand
        (cgetU k : itree E T)
        (v <- trigger (SGet k);; unwrapU (Any.downcast v))
    | 10.
  Proof. econstructor. reflexivity. Qed.

  #[global] Instance HNormExpand_cgetN
    `{coreE -< E, pgE -< E} {T : Type} (k : key)
    : HNormExpand
        (cgetN k : itree E T)
        (v <- trigger (SGet k);; unwrapN (Any.downcast v))
    | 10.
  Proof. econstructor. reflexivity. Qed.

  #[global] Instance HNormExpand_cfunU
    `{coreE -< E} {A R : Type}
    (ft : fntyp_t A R) (body : A -> itree E R) varg
    : HNormExpand
        (cfunU ft body varg)
        (arg <- unwrapU (Any.downcast varg);;
         ret <- body arg;; Ret (Any.upcast ret))
    | 10.
  Proof. econstructor. reflexivity. Qed.

  #[global] Instance HNormExpand_cfunN
    `{coreE -< E} {A R : Type}
    (ft : fntyp_t A R) (body : A -> itree E R) varg
    : HNormExpand
        (cfunN ft body varg)
        (arg <- unwrapN (Any.downcast varg);;
         ret <- body arg;; Ret (Any.upcast ret))
    | 10.
  Proof. econstructor. reflexivity. Qed.

  #[global] Instance HNormExpand_ccallU
    `{coreE -< E, callE -< E} {A R : Type}
    (fs : fnsig_t A R) (varg : A)
    : HNormExpand
        (ccallU fs varg : itree E R)
        (vret <- trigger (Call (fn_name fs) (Any.upcast varg));;
         unwrapU (Any.downcast vret))
    | 10.
  Proof. econstructor. reflexivity. Qed.

  #[global] Instance HNormExpand_ccallN
    `{coreE -< E, callE -< E} {A R : Type}
    (fs : fnsig_t A R) (varg : A)
    : HNormExpand
        (ccallN fs varg : itree E R)
        (vret <- trigger (Call (fn_name fs) (Any.upcast varg));;
         unwrapN (Any.downcast vret))
    | 10.
  Proof. econstructor. reflexivity. Qed.

  #[global] Instance HNormExpand_triggerUB
    `{coreE -< E} {A : Type}
    : HNormExpand
        (triggerUB : itree E A)
        (unwrapUK None (fun x => Ret x))
    | 10.
  Proof. econstructor. apply unwrapU_unwrapUK. Qed.

  #[global] Instance HNormExpand_triggerNB
    `{coreE -< E} {A : Type}
    : HNormExpand
        (triggerNB : itree E A)
        (unwrapNK None (fun x => Ret x))
    | 10.
  Proof. econstructor. apply unwrapN_unwrapNK. Qed.

End EXPAND_INSTANCES.
