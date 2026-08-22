From CRIS.proofmode Require Import HNormClasses.
From CRIS.common Require Import Common.

(*** head normalization tactic ***)
(*
  itree term        t
  ktree term        k
  stuck term        s ::= opaque term
                        | s >>= k
                        | ↥ s
                        | ↧ s
                        | ░ s
  head normal term  v ::= Ret x
                        | Tau t
                        | vis e k
                        | assumeK P t
                        | guaranteeK P t
                        | unwrapUK x k
                        | unwrapNK x k
                        | RealUpdateK pre post k
                        | s
 *)

(* Opaque ReSum blocks instance resolution occasionally *)
Typeclasses Transparent ReSum.

(* Keep the wrapper heads distinct from their generic [Vis]/[bind] forms
   during typeclass search.  In particular, [unwrapUK] and [unwrapNK] stay
   transparent so their [Some] cases can reduce to [Ret]. *)
Typeclasses Opaque assumeK guaranteeK RealUpdateK.

Ltac _hnorm_itr :=
  try (notypeclasses refine (HNormExpand_apply _ _); [tc_solve|]);
  tryif notypeclasses refine (HNormContext_apply _ _ _); [tc_solve|] then
    lazymatch goal with
    | |- HNormContextRes ?K ?b ?b' ?rhs =>
        econstructor;
        [ _hnorm_itr
        | tryif notypeclasses refine (@HNormReduce_apply _ _ K b' _ _ _ _ _); [tc_solve|] then
            lazymatch goal with
            | |- HNormReduceRes ?b true ?rhs =>
                econstructor; simpl; _hnorm_itr
            | |- HNormReduceRes ?b false ?rhs =>
                econstructor; reflexivity
            end
          else
            reflexivity
        ]
    end
  else
    reflexivity.

Ltac hnorm_itr :=
  etransitivity;
  [ _hnorm_itr
  | s;
    try (notypeclasses refine (HNormFinish_apply _ _); [tc_solve|]);
    reflexivity
  ].
