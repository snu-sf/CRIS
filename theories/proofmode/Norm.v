From CRIS.common Require Import Common.
From CRIS.proofmode Require Export LogicProgramming.

(** A stack of pending binds, indexed by its input and final result types. *)
Inductive Cont (E : Type -> Type) (A : Type) : Type -> Type :=
| CRet : Cont E A A
| CBind {B C} : (A -> itree E B) -> Cont E B C -> Cont E A C.

Arguments CRet {E A}.
Arguments CBind {E A B C} _ _.

(** Interpret the pending binds as a continuation on return values. *)
Fixpoint apply_cont {E A B} (ks : Cont E A B) : A -> itree E B :=
  match ks with
  | CRet => fun x => Ret x
  | CBind k ks => fun x => k x >>= apply_cont ks
  end.

(** Mark the input tree for [simpl] before continuing with [NormItr]. *)
#[projections(primitive)]
Record SimplItr {E A B} (ks : Cont E A B)
  (t : itree E A) (rhs : itree E B) : Prop :=
  { SimplItr_equal : t >>= apply_cont ks = rhs }.

(** Normalize a tree under a stack of pending continuations. *)
#[projections(primitive)]
Record NormItr {E A B} (ks : Cont E A B)
  (t : itree E A) (rhs : itree E B) : Prop :=
  { NormItr_equal : t >>= apply_cont ks = rhs }.

(** Apply the continuation stack to a return value. *)
#[projections(primitive)]
Record NormCont {E A B} (ks : Cont E A B)
  (x : A) (rhs : itree E B) : Prop :=
  { NormCont_equal : apply_cont ks x = rhs }.

Lemma SimplItr_start {E A} (t : itree E A) rhs
  : SimplItr CRet t rhs -> t = rhs.
Proof. intros [H]. cbn [apply_cont] in H. rewrite bind_ret_r in H. exact H. Qed.

Lemma SimplItr_NormItr {E A B} (ks : Cont E A B) (t : itree E A) rhs
  : NormItr ks t rhs -> SimplItr ks t rhs.
Proof. intros [H]. constructor. exact H. Qed.

(** Simplification is restricted to the input tree [t]. *)
#[global] Hint Extern 0 (SimplItr ?ks ?t ?rhs :- _) =>
  let t' := eval simpl in t in
  constructor; exact (SimplItr_NormItr ks t' rhs) : typeclass_instances.

#[global] Instance NormItr_ret {E A B}
  (ks : Cont E A B) (x : A) rhs
  : NormItr ks (Ret x) rhs :- NormCont ks x rhs | 10.
Proof. constructor. intros [H]. constructor. rewrite bind_ret_l. exact H. Qed.

#[global] Instance NormItr_tau {E A B}
  (ks : Cont E A B) (t : itree E A) rhs
  : NormItr ks (Tau t) (Tau rhs) :- NormItr ks t rhs | 10.
Proof.
  constructor. intros [H]. constructor.
  rewrite bind_tau. rewrite H. reflexivity.
Qed.

#[global] Instance NormItr_vis {E A B X} (ks : Cont E A B)
  (e : E X) (k : X -> itree E A) (k' : X -> itree E B)
  : NormItr ks (Vis e k) (Vis e k') :-
      forall x, SimplItr ks (k x) (k' x) | 10.
Proof.
  constructor. intro H. constructor.
  rewrite bind_vis. do 2 f_equal. extensionalities x.
  apply SimplItr_equal. apply H.
Qed.

#[global] Instance NormItr_bind {E A B C} (ks : Cont E B C)
  (t : itree E A) (k : A -> itree E B) rhs
  : NormItr ks (t >>= k) rhs :-
      NormItr (CBind k ks) t rhs | 10.
Proof. constructor. intros [H]. constructor. rewrite bind_bind. exact H. Qed.

(** Normalize the continuation of a stuck tree under its binder. This
    fallback follows the structural rules; [CRet] yields [t >>= Ret]. *)
#[global] Instance NormItr_stuck {E A B} (ks : Cont E A B)
  (t : itree E A) (k' : A -> itree E B)
  : NormItr ks t (t >>= k') :-
      forall x, NormCont ks x (k' x) | 100.
Proof.
  constructor. intro H. constructor. f_equal. extensionalities x.
  apply NormCont_equal. apply H.
Qed.

#[global] Instance NormCont_ret {E A} (x : A)
  : NormCont CRet x (Ret x : itree E A) :- True | 10.
Proof. constructor. intros _. constructor. reflexivity. Qed.

#[global] Instance NormCont_bind {E A B C} (ks : Cont E B C)
  (k : A -> itree E B) (x : A) rhs
  : NormCont (CBind k ks) x rhs :-
      SimplItr ks (k x) rhs | 10.
Proof. constructor. intros [H]. constructor. exact H. Qed.

(** Prove [t = rhs] by normalizing [t], including under continuation binders.
    [rhs] must be an evar. *)
Ltac norm_itr :=
  eapply SimplItr_start; inference.
