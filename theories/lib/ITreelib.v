From ITreeS Require Export ITree.

From ExtLib Require Export
     Functor FunctorLaws
     Structures.Maps.
From CRIS.lib Require Import Coqlib.

Export SumNotations.
Export Monads.
Open Scope cat_scope.
Open Scope monad_scope.
Open Scope itree_scope.

Set Implicit Arguments.

Module ITreeNotations.
  Notation "t1 >>= k2" := (ITree.bind t1 k2)
    (at level 58, left associativity) : itree_scope.
  Notation "x <- t1 ;; t2" := (ITree.bind t1 (fun x => t2))
    (at level 62, t1 at next level, right associativity) : itree_scope.
  Notation "t1 ;;; t2" := (ITree.bind t1 (fun _ => t2))
    (at level 62, right associativity) : itree_scope.
  Notation "' p : T <- t1 ;; t2" :=
    (ITree.bind t1 (fun x_ : T => match x_ with p => t2 end))
      (at level 62, T at next level, t1 at next level, p pattern, right associativity) : itree_scope.
  Notation "tau;; t2" :=
    (Tau t2) (at level 200, right associativity) : itree_scope.
  Notation "f <$> x" := (@fmap _ _ _ _ f x) (at level 61, left associativity).
End ITreeNotations.
Export ITreeNotations.

(* Ltac f := first [eapply bisim_is_eq|eapply eq_is_bisim]. *)
(* Tactic Notation "f" "in" hyp(H) := first [eapply bisim_is_eq in H|eapply eq_is_bisim in H]. *)

Ltac ides itr :=
  let T := fresh "T" in
  destruct (observe itr) eqn:T;
  sym in T; apply simpobs in T; apply bisim_is_eq in T; rewrite T in *; clarify.
Ltac csc := clarify; simpl_depind; clarify.

Lemma bind_ret_l_forall
  {E} {X R: Type} (P: _ -> _ -> Prop) (k: X -> itree E R)
  :
  (forall v: X, P v (_v <- Ret v;; k _v)) -> (forall v: X, P v (k v)).
Proof.
  i. specialize (H v). revert H. rewrite bind_ret_l. eauto.
Qed.

Lemma bind_ret_r_rev:
  forall (E : iEvent) (R : Type) (s : itree E R), s = ' x : R <- s;; Ret x.
Proof.
  i. symmetry. apply bind_ret_r.
Qed.
 
Lemma map_vis {E: Type->Type} {X: Type} {R1 R2: Type} (e : E X) (k : X -> itree E R1) (f : R1 -> R2) :
  ITree.map f (Vis e k) = Vis e (fun x => f <$> (k x)).
Proof.
  unfold ITree.map. rewrite bind_vis. eauto.
Qed.

Lemma map_trigger `{E -< F} {X: Type} {S: Type} (f: X -> S) (e : E X)
  :
  @ITree.map F X S f (trigger e) = x <- trigger e;; Ret (f x).
Proof.
  unfold trigger. rewrite map_vis. s. rewrite bind_vis. eauto.
Qed.

Hint Rewrite @bind_ret_l : itree_axiom.
Hint Rewrite @bind_ret_r : itree_axiom.
Hint Rewrite @bind_tau : itree_axiom.
Hint Rewrite @bind_vis : itree_axiom.
Hint Rewrite @bind_trigger : itree_axiom.
Hint Rewrite @bind_bind : itree_axiom.
Local Tactic Notation "irw" "in" ident(H) := repeat (autorewrite with itree_axiom in H; cbn in H).
Local Tactic Notation "irw" := repeat (autorewrite with itree_axiom; cbn).

Lemma interp_trigger:
  forall (E F : iEvent) (X : Type) (e : E X) (f : E ~> itree F),
    interp f (ITree.trigger e) = x <- f X e;; tau;; Ret x.
Proof.
  i. rewrite unfold_interp. ss. f_equal. extensionality r.
  do 2 f_equal. rewrite interp_ret. eauto.
Qed.

Lemma subst_bind:
  forall E (T U: Type) (k : T -> itree E U) i, ITree.subst k i = ITree.bind i k.
Proof. i. refl. Qed.

Ltac iby3 TAC :=
  first [
      instantiate (1:= fun _ _ _ => _); TAC|
      instantiate (1:= fun _ _ _ => _ <- _ ;; _); TAC|
      instantiate (1:= fun _ _ _ => _ <- (_ <- _ ;; _) ;; _); TAC|
      instantiate (1:= fun _ _ _ => _ <- (_ <- (_ <- _ ;; _) ;; _) ;; _); TAC|
      instantiate (1:= fun _ _ _ => _ <- (_ <- (_ <- (_ <- _ ;; _) ;; _) ;; _) ;; _); TAC|
      instantiate (1:= fun _ _ _ => _ <- (_ <- (_ <- (_ <- (_ <- _ ;; _) ;; _) ;; _) ;; _) ;; _); TAC|
      fail
    ]
.

Ltac iby1 TAC :=
  first [
      instantiate (1:= fun '(_, (_, _)) => _); TAC|
      instantiate (1:= fun '(_, (_, _)) => _ <- _ ;; _); TAC|
      instantiate (1:= fun '(_, (_, _)) => _ <- (_ <- _ ;; _) ;; _); TAC|
      instantiate (1:= fun '(_, (_, _)) => _ <- (_ <- (_ <- _ ;; _) ;; _) ;; _); TAC|
      instantiate (1:= fun '(_, (_, _)) => _ <- (_ <- (_ <- (_ <- _ ;; _) ;; _) ;; _) ;; _); TAC|
      instantiate (1:= fun '(_, (_, _)) => _ <- (_ <- (_ <- (_ <- (_ <- _ ;; _) ;; _) ;; _) ;; _) ;; _); TAC|
      fail
    ]
.

Ltac ired1 :=
  first
    [ rewrite subst_bind
    | rewrite bind_bind
    | rewrite bind_ret_l
    | rewrite bind_ret_r
    | rewrite bind_tau
    | rewrite interp_vis
    | rewrite interp_ret
    | rewrite interp_tau
    | rewrite interp_trigger
    | rewrite interp_bind
    | rewrite interp_state_trigger
    | rewrite interp_state_bind
    | rewrite interp_state_tau
    | rewrite interp_state_ret
    | fail];
   cbn.

Ltac ired := cbn; hrepeat do 1 ired1.

Ltac grind_simplify :=
  cbn;
  (hrepeat do 1 (
      match goal with
      (* | [ |- tau;; ?a = tau;; ?b ] => do 2 f_equal *)
      | [ |- (go (TauF ?a)) = (go (TauF ?b)) ] => do 2 f_equal
      | [ |- (_ <- _ ;; _) = (_ <- _ ;; _) ] => Morphisms.f_equiv; apply func_ext_dep; i
      end; ii));
  ii; des_ifs_safe.

Ltac grind :=
  grind_simplify;
  hrepeat do 1 ((hrepeat_or_fail do 1 ired1); grind_simplify);
  des_ifs_safe.

(*** simple regression tests ***)
(*
Goal forall E R (itr : itree E R), (tau;; tau;; tau;; itr) = (tau;; tau;; itr). i. grind. Abort.
Goal forall E X Y (itr : itree E X) (ktr : X -> itree E Y), ((x <- itr;; tau;; tau;; Ret x) >>= ktr) = ((x <- itr;; tau;; Ret x) >>= ktr).
  i. progress grind. (*** it should progress ***)
Abort.
*)

Inductive taus E R : itree E R -> nat -> Prop :=
| taus_tau
    itr0 n
    (TL : taus itr0 n)
  :
    taus (Tau itr0) (1 + n)
| taus_ret
    r
  :
    taus (Ret r) 0
| taus_vis
    X (e : E X) k
  :
    taus (Vis e k) 0
.

Definition tauK {E} {R: Type} : R -> itree E R := fun r => tau;; Ret r.
Hint Unfold tauK : core.

Definition idK {E} {R: Type} : R -> itree E R := fun r => Ret r.
Hint Unfold idK : core.

Lemma idK_spec E (R: Type) (i0 : itree E R) : i0 = i0 >>= idK.
Proof. unfold idK. irw. refl. Qed.

Ltac resub :=
  hrepeat do 1 multimatch goal with
         | |- context[@ITree.trigger ?E ?R ?e] =>
           match e with
           | subevent _ _ => idtac
           | _ => replace (@ITree.trigger E R e) with (trigger e) by refl
           end
         | |- context[@subevent _ ?F ?prf _ (?e|)%sum] =>
           let my_tac := ltac:(fun H => replace (@subevent _ F prf _ (e|)%sum) with (@subevent _ F _ _ e) by H) in
           match (type of e) with
           | (_ +' _) _ => my_tac ltac:(destruct e; refl)
           | _ => my_tac ltac:(refl)
           end
         | |- context[@subevent _ ?F ?prf _ (|?e)%sum] =>
           let my_tac := ltac:(fun H => replace (@subevent _ F prf _ (|e)%sum) with (@subevent _ F _ _ e) by H) in
           match (type of e) with
           | (_ +' _) _ => my_tac ltac:(destruct e; refl)
           | _ => my_tac ltac:(refl)
           end
         | |- context[ITree.trigger (@subevent _ ?F ?prf _ (resum ?a ?b ?e))] =>
           replace (ITree.trigger (@subevent _ F prf _ (resum a b e))) with (ITree.trigger (@subevent _ F _ _ e)) by refl
         end.

Definition trivial_Handler `{E -< F} : forall T: Type, E T -> itree F T
  := fun T (e: E T) => trigger e.

Lemma observe_eta E R (itr0 itr1 : itree E R)
      (EQ : _observe itr0 = _observe itr1)
  :
    itr0 = itr1.
Proof.
  erewrite (itree_eta itr0).
  erewrite (itree_eta itr1).
  f_equal. auto.
Qed.

Lemma bind_ret_l_eta (A: Type) {E R} (k : A -> itree E R):
  (fun x : A => x0 <- Ret x;; k x0) = k.
Proof. extensionality x. grind. Qed.

Ltac grind_ret H := try rewrite !bind_ret_l_eta in H; subst.
Ltac grind_ret_gen :=
  hrepeat do 1 (match goal with
  [H : _ |- _] => rewrite !bind_ret_l_eta in H
  end).

Ltac itree_clarify H :=
  revert H; grind; try unfold trigger in H; try rewrite !bind_vis in H; try depdes H;
    grind_ret_gen; try rewrite !bind_ret_l_eta; subst.

Lemma trigger_vis
  `{subE -< E} {X : Type} (e : subE X) :
  (trigger e : itree E X) = vis e (fun x => Ret x).
Proof. reflexivity. Qed.

Lemma vis_trigger
  `{subE -< E} {X: Type} {T: Type} (e : subE X) (k : X -> itree E T) :
  vis e k = (trigger e >>= k).
Proof.
  eapply observe_eta; cbn. f_equal. extensionality x.
  eapply observe_eta. reflexivity.
Qed.

Lemma vis_bind `{subE -< E} {X: Type} {T U : Type}
  (e : subE X) (k1 : X -> itree E T) (k2 : T -> itree E U) :
  (vis e k1 >>= k2) = vis e (fun x => k1 x >>= k2).
Proof.
  rewrite ! vis_trigger.
  apply bind_bind.
Qed.

Lemma bind_ext {E : iEvent} {X Y: Type} (itr0 itr1: itree E X) (ktr : ktree E X Y) : itr0 = itr1 -> itr0 >>= ktr = itr1 >>= ktr. i; subst; refl. Qed.

Lemma bind_extk : forall [E : iEvent] [X Y: Type] [itr : itree E X] (ktr0 ktr1 : ktree E X Y),
    (forall x, ktr0 x = ktr1 x) -> (itr >>= ktr0) = (itr >>= ktr1)
.
Proof using. i. f_equiv. eapply func_ext. et. Qed.

Lemma tau_ext : forall [E : iEvent] [X : Type] [itr0 itr1 : itree E X],
    itr0 = itr1 -> (tau;; itr0) = (tau;; itr1)
.
Proof using. i. grind. Qed.

(***
 [itreeV E R] : same as [itree E R] but productive
 ***)

Variant itreeV E R :=
  | itreeV_nvis (t: itree E R)
  | itreeV_vis (X: Type) (e: E X) (k: X -> itree E R)
.

Definition itreeV_itree {E R} (i: itreeV E R) : itree E R :=
  match i with
  | itreeV_nvis t => tau;; t
  | itreeV_vis e k => ITree.trigger e >>= k
  end.

(***
 [interpV] : same as [interp] but does not introduce tau by only taking productive handlers.
 ***)

CoFixpoint interpV {E: iEvent} {F: iEvent} (handler: forall X: Type, E X -> itreeV F X)
  : forall T:Type, itree E T -> itree F T :=
  fun _ itr =>
  match (_observe itr) with
  | RetF r => Ret r
  | TauF t => tau;; interpV handler t
  | VisF e k =>
      match handler _ e with
      | itreeV_nvis t =>
          tau;; x <- t;; interpV handler (k x)
      | itreeV_vis e' k' =>
          Vis e' (fun x' => x <- k' x';; interpV handler (k x))
      end
  end.

Lemma interpV_ret {E F R} f x:
  @interpV E F R f (Ret x) = Ret x.
Proof.
  eapply observe_eta. eauto.
Qed.

Lemma interpV_tau {E F R} f t:
  @interpV E F f R (tau;; t) = tau;; interpV f t.
Proof.
  eapply observe_eta. eauto.
Qed.

Lemma interpV_vis {E F R} f U e k:
  @interpV E F f R (Vis e k) = x <- itreeV_itree (f U e);; interpV f (k x).
Proof.
  eapply observe_eta. s. destruct (f U e); s; eauto.
  f_equal. extensionalities. ired. eauto.
Qed.

Lemma interpV_trigger (E F: iEvent) (R : Type) (e : E R) f:
  @interpV E F f R (ITree.trigger e) = itreeV_itree (f R e).
Proof.
  unfold ITree.trigger. rewrite interpV_vis.
  rewrite <-(bind_ret_r (_ (f R e))) at 2.
  f_equal. extensionalities. rewrite interpV_ret. et.
Qed.

Lemma interpV_bind {E F} {R S} f (t: itree E R) (k: R -> itree E S):
  @interpV E F f S ('x: R <- t;; k x) = x <- interpV f t;; interpV f (k x).
Proof.
  eapply bisim_is_eq. ginit.
  revert R t k. gcofix CIH. i.
  rewrite (itree_eta t). destruct (observe t).
  - rewrite interpV_ret. ired. gfinal. right.
    eapply paco2_mon_bot; eauto. eapply eq_is_bisim. eauto.
  - ired. rewrite !interpV_tau. ired.
    gstep. econs. gbase. eauto.
  - rewrite bind_vis, !interpV_vis. destruct (f _ e); s; eauto.
    + ired. gstep. econs.
      guclo eqit_clo_bind. econs.
      { apply eq_is_bisim. refl. }
      i. subst. gbase. eauto.
    + ired. unfold trigger. rewrite !bind_vis.
      gstep. econs. i. ired.
      guclo eqit_clo_bind. econs.
      { apply eq_is_bisim. refl. }
      i. subst. gbase. eauto.
Qed.

(***
 [iterV] : same as [iter] but does not introduce tau by only taking productive handlers.
 ***)

CoFixpoint _iterV {E: iEvent} {R I: Type} (f: I -> itreeV E (I + R)%type) (itr: itree E (I + R)%type) : itree E R :=
  match (_observe itr) with
  | RetF (inl i) =>
      match f i with
      | itreeV_nvis t => tau;; _iterV f t
      | itreeV_vis e k => Vis e (fun x => _iterV f (k x))
      end
  | RetF (inr r) =>
      Ret r
  | TauF t => tau;; _iterV f t
  | VisF e k =>
      Vis e (fun x => _iterV f (k x))
  end.

Definition iterV {E: iEvent} {R I: Type} (f: I -> itreeV E (I + R)%type) (i: I) : itree E R :=
  _iterV f (itreeV_itree (f i)).

Lemma _iterV_ret_r {E R I} f r:
  @_iterV E R I f (Ret (inr r)) = Ret r.
Proof.
  eapply observe_eta. s. eauto.
Qed.

Lemma _iterV_ret_l {E R I} f i:
  @_iterV E R I f (Ret (inl i)) = _iterV f (itreeV_itree (f i)).
Proof.
  eapply observe_eta. s. destruct (f i); s; et.
  f_equal. extensionalities.
  rewrite bind_ret_l. et.
Qed.

Lemma _iterV_tau {E R I} f t:
  @_iterV E R I f (tau;; t) = tau;; _iterV f t.
Proof.
  eapply observe_eta. s. eauto.
Qed.

Lemma _iterV_vis {E: iEvent} {R I: Type} (X: Type) f (e: E X) k:
  @_iterV E R I f (Vis e k) = Vis e (fun x => _iterV f (k x)).
Proof.
  eapply observe_eta. s. eauto.
Qed.

Lemma unfold_iterV {E R I} f i:
  @iterV E R I f i =
    lr <- itreeV_itree (f i);;
    match lr with
    | inl l => iterV f l
    | inr r => Ret r
    end.
Proof.
  eapply bisim_is_eq. unfold iterV. ginit.
  generalize (itreeV_itree (f i)) as t. clear i.
  gcofix CIH. i.
  rewrite (itree_eta t). destruct (observe t).
  - destruct r0 as [i|rv].
    + rewrite _iterV_ret_l. ired.
      gfinal. right. eapply paco2_mon.
      * eapply eq_is_bisim. eauto.
      * ss.
    + rewrite _iterV_ret_r. ired. gstep. econs. reflexivity.
  - rewrite _iterV_tau. ired. gstep. econs. gbase. eauto.
  - rewrite _iterV_vis, bind_vis. gstep. econs. i. gbase. eauto.    
Qed.

(***
 [iterC] : same as [ITree.iter] but inserts tau at the beginning
 ***)

Definition iterC {E} {R I: Type} (f: I -> itree E (I + R)%type) : I -> itree E R :=
  fun i => tau;; ITree.iter f i.

Global Typeclasses Opaque iterC.

Lemma unfold_iterC {E} {R I: Type} (f: I -> itree E (I + R)%type) (i: I):
  iterC f i =
    tau;; res <- f i;; match res with inl i' => iterC f i' | inr r => Ret r end.
Proof.
  unfold iterC. rewrite unfold_iter. refl.
Qed.
