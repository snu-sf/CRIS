#[local] Generalizable All Variables.

Section HNORM_BOOL.

  Class HNormBool (a b : bool) : Prop :=
    { HNormBool_equal : a = b }.
  Hint Mode HNormBool + - : typeclass_instances.

End HNORM_BOOL.

Section HNORM_EXPAND.

  (** An instance must completely expand its outer head: its right-hand side
      must not require another [HNormExpand] step. *)
  Class HNormExpand {A : Type} (x : A) (y : A) : Prop :=
    { HNormExpand_equal : x = y }.
  Hint Mode HNormExpand + ! - : typeclass_instances.

  Lemma HNormExpand_apply `{HNormExpand A x y} rhs : y = rhs -> x = rhs.
  Proof. intro; subst. eapply HNormExpand_equal. Qed.

End HNORM_EXPAND.

Section HNORM_CONTEXT.

  (** A normalizable one-hole context.  Typeclass matching is
      conversion-aware, so program-level combinators whose unfolding exposes
      one of these contexts should be [Typeclasses Opaque] unless they are
      deliberately handled by [HNormExpand]. *)
  Class HNormContext
    {A B : Type}
    (a : A) (K : B -> A) (b : B) : Prop :=
    { HNormContext_equal : a = K b }.
  Hint Mode HNormContext + - ! - - : typeclass_instances.

  Record HNormContextRes
    {A B : Type}
    (K : B -> A) (b : B) (b' : B) (rhs : A) : Prop :=
    { HNormContextRes_goal1 : b = b'
    ; HNormContextRes_goal2 : K b' = rhs
    }.

  Lemma HNormContext_apply
    `{@HNormContext A B a K b}
    b' rhs
    : HNormContextRes K b b' rhs -> a = rhs.
  Proof. intros [-> <-]. eapply HNormContext_equal. Qed.

End HNORM_CONTEXT.

Section HNORM_REDUCE.

  (** [continue] requests continued normalization after the reduction. *)
  Class HNormReduce
    {A B : Type}
    (K : A -> B) (a : A) (b : B) (continue : bool) : Prop :=
    { HNormReduce_equal : K a = b }.
  Hint Mode HNormReduce + + ! ! - - : typeclass_instances.

  Record HNormReduceRes
    {B : Type}
    (b : B) (continue : bool) (rhs : B) : Prop :=
    { HNormReduceRes_goal1 : b = rhs
    }.

  Lemma HNormReduce_apply
    `{@HNormReduce A B K a b continue}
    rhs
    : HNormReduceRes b continue rhs -> K a = rhs.
  Proof. intros [->]. eapply HNormReduce_equal. Qed.

End HNORM_REDUCE.

Section HNORM_FINISH.

  (** A finish instance refolds one normalized head into its public form. *)
  Class HNormFinish {A : Type} (x y : A) : Prop :=
    { HNormFinish_equal : x = y }.
  Hint Mode HNormFinish + ! - : typeclass_instances.

  Lemma HNormFinish_apply `{HNormFinish A x y} rhs : y = rhs -> x = rhs.
  Proof. intro; subst. eapply HNormFinish_equal. Qed.

End HNORM_FINISH.
