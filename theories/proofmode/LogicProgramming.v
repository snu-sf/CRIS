From stdpp Require Import tactics.

(** An inference rule deriving [conclusion] from the proposition [premise]. *)
#[projections(primitive)]
Class InferRule (conclusion premise : Prop) : Prop :=
  { InferRule_apply : premise -> conclusion }.

Notation "P :- Q" := (InferRule P Q)
  (at level 100, Q at level 200, no associativity) : type_scope.

#[global] Hint Mode InferRule ! - : typeclass_instances.

(** Introduce binders, split conjunctions, and discharge [True]. Other goals
    use an [InferRule] instance or a [Hint Extern]. Rule selection commits
    before recursively solving the selected premise. *)
Ltac inference :=
  lazymatch goal with
  | |- forall _, _ => intro; inference
  | |- _ /\ _ => split; inference
  | |- True => exact I
  | _ =>
      notypeclasses refine (@InferRule_apply _ _ _ _);
      [ tc_solve | inference ]
  end.
