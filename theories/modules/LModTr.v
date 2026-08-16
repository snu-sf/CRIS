From CRIS.common Require Import Common.
From CRIS.proofmode Require Import HNormClasses.

Module LModTr.
  Definition pure_state {S E} : E ~> stateT S (itree E) := λ _ e s, x <- trigger e;; Ret (s, x).

  Definition handle_stateE {Σ E} : lstateE Σ ~> stateT (lstateT Σ) (itree E) :=
    λ _ e glob,
      match e with
      | SUpdate run => Ret (run glob)
      end.

  Definition interp_stateE {Σ E} : itree (lstateE Σ +' E) ~> stateT (lstateT Σ) (itree E) :=
    State.interp_state (case_ handle_stateE pure_state).

  Definition ths_state {Σ} : Type := nat * list (itree (lmodE Σ) Any.t).

  Definition handle_callE {Σ} (prog: string → option (Any.t → itree (lmodE Σ) Any.t))
      : ths_state → itreeV (lstateE Σ +' coreE) (ths_state + Any.t) :=
    λ '(tid, ths),
      match base.lookup tid ths with
      | None => itreeV_nvis (triggerUB)
      | Some itr =>
          match observe (itr: itree (lmodE Σ) Any.t) with
          | RetF rv =>
              itreeV_nvis (if Nat.eq_dec tid 0 then Ret (inr rv) else triggerUB)
          | TauF itr' =>
              itreeV_nvis (Ret (inl (tid, <[tid := itr']> ths)))
          | VisF (inr1 e) k =>
              itreeV_vis (subevent _ e) (λ v, Ret (inl (tid, <[tid := k v]> ths)))
          | VisF (inl1 e) k =>
              itreeV_nvis
                (match e in callE T return (T → _) → _ with
                 | Call fn arg =>
                    λ k,
                      bd <- (prog fn)? ;;
                      Ret (inl (tid, <[tid := x <- bd arg;; tau;; k x]> ths))
                 | Spawn fn arg =>
                    λ k, let new_tid := List.length ths in
                      bd <- (prog fn)? ;;
                      Ret (inl (tid, (<[tid := k new_tid]> ths) ++ [bd arg]))
                 | Yield tid' =>
                    λ k, Ret (inl (tid', <[tid := k tt]> ths))
                 | GetTid =>
                    λ k, Ret (inl (tid, <[tid:=k tid]> ths))
                 end k)
          end
      end.

  Definition interp_callE {Σ} prog (itr : itree (lmodE Σ) Any.t) : itree (lstateE Σ +' coreE) Any.t :=
    iterV (handle_callE prog) (0, [itr]).

  Definition trans {Σ} prog (itr : itree (lmodE Σ) Any.t) (st : lstateT Σ): itree coreE _ :=
    interp_stateE Any.t (interp_callE prog itr) st.
End LModTr.

Section HNORM_INSTANCES.

  #[global] Instance HNormContext_LModTr_interp_stateE
    {Σ E R} (itr : itree (lstateE Σ +' E) R) (st : lstateT Σ)
    : HNormContext
        (LModTr.interp_stateE R itr st)
        (fun itr' => LModTr.interp_stateE R itr' st) itr.
  Proof. constructor. reflexivity. Qed.

  #[global] Instance HNormReduce_LModTr_state_ret
    {Σ E R} (x : R) (st : lstateT Σ)
    : HNormReduce
        (fun itr => @LModTr.interp_stateE Σ E R itr st)
        (Ret x) (Ret (st, x)) false
    | 10.
  Proof.
    constructor. unfold LModTr.interp_stateE. eapply interp_state_ret.
  Qed.

  #[global] Instance HNormReduce_LModTr_state_tau
    {Σ E R} (itr : itree (lstateE Σ +' E) R) (st : lstateT Σ)
    : HNormReduce
        (fun itr => @LModTr.interp_stateE Σ E R itr st)
        (Tau itr) (Tau (LModTr.interp_stateE R itr st)) false
    | 10.
  Proof.
    constructor. unfold LModTr.interp_stateE. eapply interp_state_tau.
  Qed.

  #[global] Instance HNormReduce_LModTr_state_vis
    {Σ E X R} (e : (lstateE Σ +' E) X)
    (k : X -> itree (lstateE Σ +' E) R) (st : lstateT Σ)
    : HNormReduce
        (fun itr => @LModTr.interp_stateE Σ E R itr st)
        (Vis e k)
        ((case_sum1 LModTr.handle_stateE LModTr.pure_state) X e st >>=
         fun sx =>
           Tau (LModTr.interp_stateE R (k (snd sx)) (fst sx))) true
    | 20.
  Proof.
    constructor. unfold LModTr.interp_stateE. eapply interp_state_vis.
  Qed.

  #[global] Instance HNormReduce_LModTr_state_unwrapUK
    {Σ E X R} `{coreE -< E} (x : option X)
    (k : X -> itree (lstateE Σ +' E) R) (st : lstateT Σ)
    : HNormReduce
        (fun itr => @LModTr.interp_stateE Σ E R itr st)
        (unwrapUK x k)
        (LModTr.interp_stateE R
           (match x with
            | Some y => k y
            | None => v <- trigger (Take False);; match v : False with end
            end) st) true
    | 15.
  Proof. constructor. unfold unwrapUK. reflexivity. Qed.

  #[global] Instance HNormReduce_LModTr_state_bind
    {Σ E A R} (itr : itree (lstateE Σ +' E) A)
    (k : A -> itree (lstateE Σ +' E) R) (st : lstateT Σ)
    : HNormReduce
        (fun itr => @LModTr.interp_stateE Σ E R itr st)
        (itr >>= k)
        (sx <- LModTr.interp_stateE A itr st;;
         LModTr.interp_stateE R (k (snd sx)) (fst sx)) false
    | 30.
  Proof.
    constructor. unfold LModTr.interp_stateE. eapply interp_state_bind.
  Qed.

End HNORM_INSTANCES.
