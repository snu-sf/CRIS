From iris.proofmode Require Import proofmode.
From CRIS.simulations.msim Require Import FnsemLookup.
From CRIS.modules Require Import Mod SMod.
From CRIS.proofmode Require Import HNormClasses HNormInstances.
From CRIS.proofmode Require Export HNorm.

(************ User Tactics **************)

Tactic Notation "cong" constr(f) :=
  refine (f_equal f _).

Lemma string_app_inv
  p s s'
  (EQ: (p ++ s = p ++ s')%string)
  :
  (s = s')%string.
Proof.
  revert_until p. induction p; i; ss.
  unfold append in EQ. depdes EQ. eauto.
Qed.

Ltac inv_string X :=
  inv X;
  (hrepeat do 1 match goal with [H: @eq string _ _|-_] =>
           apply string_app_inv in H
     end);
  ss.

Ltac prove_nodup :=
  (hrepeat do 1 (econs; [ii; ss; des; try match goal with [H: _ |- _] => inv_string H end|]));
  try (econs; fail).

Ltac prove_precise :=
  (hrepeat do 1 (iApply precise_sep; iSplit));
  first [iApply precise_pure|iApply precise_own|iApply precise_Own].

(* Tactic for coinduction *)

Lemma combine_quant A B (P : ∀ (a: A) (b: B), Prop)
    (PR : ∀ (ab : A * B), P (fst ab) (snd ab)) :
  ∀ a b, P a b.
Proof using. i. eapply (PR (a,b)). Qed.

Lemma combine_quant_dep A (B: A -> Type) (P: forall a (b: B a), Prop)
    (PR: ∀ (ab: sigT B), P (projT1 ab) (projT2 ab)):
  ∀ a b, P a b.
Proof using. i. eapply (PR (existT a b)). Qed.

Lemma destruct_quant {A B} (P: A*B → Prop):
  (∀ a: A*B, P a) ↔ (∀ (a:A) (b: B), P (a, b)).
Proof.
  split; i; et. destruct a; et.
Qed.

Lemma destruct_quant_dep {A} (F: A→Type) (P: sigT F → Prop):
  (∀ a: sigT F, P a) ↔ (∀ (a:A) (b: F a), P (existT a b)).
Proof.
  split; i; et. destruct a; et.
Qed.

Ltac combine_quant tm :=
  revert tm; first [apply combine_quant | apply combine_quant_dep].

Ltac destruct_quant CIH :=
  (hrepeat first [setoid_rewrite destruct_quant in CIH
                 | setoid_rewrite destruct_quant_dep in CIH]);
  simpl in CIH.

Ltac unfold_cris_defs :=
  rewrite /SB.sandbox_body; s;
  rewrite /SModTr.trans_fnsem /=.

Ltac move_aux :=
  (hrepeat do 1 match goal with [H: List.NoDup _ |- _ ] => guardH H; move H at top end);
  (hrepeat do 1 match goal with [H: incl _ (Mod.scopes _ _) |- _] => guardH H; move H at top end);
  (hrepeat do 1 match goal with [H: Mod.wf _ |- _ ] => guardH H; move H at top end);
  (* (hrepeat do 1 match goal with [H: ∀ _, sp_incl _ _ |- _ ] => guardH H; move H at top end); *)
  (hrepeat do 1 match goal with [H:=_:list (_ * (Any.t -> itree crisE Any.t)) |- _ ] => guardH H; move H at top end);
  unguard.

Tactic Notation "msk_solve" constr(P) :=
  (tryif is_closed_term P
      then
        (let r := eval vm_compute in P in change P with r)
      else (* solver for open proposition P - add further tactics in new scenarios *)
        (let a := fresh in case_bool_decide as a; [exfalso; set_solver+a|]
        ||let a := fresh in case_bool_decide as a; [|exfalso; set_solver+a]
        ||idtac)).

Ltac iIntrosFresh H :=
  iIntros H
  ||
  let H' := eval compute in (H ++ "'")%string in iIntrosFresh H'.

Ltac des_pairs :=
  (hrepeat do 1
    match goal with
    | [H: context[let () := ?x in _] |- _] =>
        match type of x with
        | () => destruct x
        | (_ * _)%type =>
            let n0 := fresh "_q" in let n1 := fresh "_q" in
            let EQ := fresh "EQq" in
            destruct x as [n0 n1] eqn: EQ
        end
    | |- context[let () := ?x in _] =>
        match type of x with
        | () => destruct x
        | (_ * _)%type =>
            let n0 := fresh "_q" in let n1 := fresh "_q" in
            let EQ := fresh "EQq" in
            destruct x as [n0 n1] eqn: EQ
        end
    end);
   subst.

Ltac unfoldPrePost_term term :=
  let TM := fresh "_term" in
  set (TM := term) at 1;
  (hrepeat do 1 match goal with
       [H := ?P |- _] =>
         match H with
           TM => match P with
                 | context[precond] => unfold precond in TM; simpl in TM
                 | context[postcond] => unfold postcond in TM; simpl in TM
                 (* | context[precondS] => unfold precondS in TM; simpl in TM *)
                 (* | context[postcondS] => unfold postcondS in TM; simpl in TM *)
                 end
         end
     end);
  subst TM.

Ltac unfoldPrePost :=
  hrepeat do 1 match goal with
  | |-context[precond] => rewrite /precond; s
  | |-context[postcond] => rewrite /postcond; s
  end.

Ltac set_marker marker :=
  assert (marker: True) by exact I.

Ltac hide_ihyps_env env :=
  match env with
  | environments.Enil => idtac
  | environments.Esnoc ?tl _ ?hyp =>
      hide_ihyps_env tl;
      let IHYP := fresh "IHYP" in
      set (IHYP := hyp) at 1
  end.

Ltac hide_ihyps :=
  match goal with
  | [ |- environments.envs_entails {|environments.env_intuitionistic := ?ienv; environments.env_spatial := ?env |} _] =>
      hide_ihyps_env ienv;
      hide_ihyps_env env
  end.

Ltac only_itree_s :=
  let ITREE := fresh "ITREE" in
  match goal with
  [|- _ (_ ?it _)] => first [set (ITREE := it) at 2|set (ITREE := it) at 1]
  end.

Ltac only_itree_t :=
  let ITREE := fresh "ITREE" in
  match goal with [|- _ (_ _ ?it)] => set (ITREE := it) at 1 end.

Ltac show_itree :=
  match goal with [H:_|-_] => unfold H; clear H end.

Ltac show_until marker :=
  (hrepeat do 1 match goal with
      [H: _ |- _] =>
        try match H with marker => fail 3 end;
        first [unfold H; clear H | revert H]
    end);
  clear marker; i.

Ltac fnsem_lookup_outer_head t :=
  lazymatch t with
  | ?f _ => fnsem_lookup_outer_head f
  | _ => t
  end.

Ltac fnsem_lookup_replace_outer_head t body :=
  lazymatch t with
  | ?f ?x =>
      let f' := fnsem_lookup_replace_outer_head f body in
      constr:(f' x)
  | _ => constr:(body)
  end.

(** Unfold exactly the outer constant. Rebuilding its application separately
    keeps fix/iota reduction out of the alias-exposure phase. *)
Ltac fnsem_lookup_delta_outer_once t :=
  let h := fnsem_lookup_outer_head t in
  let body := eval unfold h in h in
  let raw := fnsem_lookup_replace_outer_head t body in
  let t' := eval cbv beta zeta in raw in
  constr:(t').

(** Commit one delta attempt inside a closed term, leaving no Ltac
    backtracking choice when the later typeclass search fails. *)
Ltac fnsem_lookup_delta_outer_once_opt t :=
  let T := type of t in
  constr:((ltac:(first
    [ let t' := fnsem_lookup_delta_outer_once t in exact (Some t')
    | exact None
    ])) : option T).

Ltac fnsem_lookup_has_module_arg t :=
  lazymatch t with
  | ?f ?x =>
      let T := type of x in
      lazymatch T with
      | @Mod.t _ => constr:(true)
      | @SMod.t _ => constr:(true)
      | _ => fnsem_lookup_has_module_arg f
      end
  | _ => constr:(false)
  end.

Ltac fnsem_lookup_has_map_arg t :=
  lazymatch t with
  | ?f ?x =>
      let T := type of x in
      lazymatch T with
      | gmap _ _ => constr:(true)
      | _ => fnsem_lookup_has_map_arg f
      end
  | _ => constr:(false)
  end.

Ltac fnsem_lookup_normalize_module_args t :=
  lazymatch t with
  | ?f ?x =>
      let f' := fnsem_lookup_normalize_module_args f in
      let T := type of x in
      lazymatch T with
      | @Mod.t _ =>
          let x' := fnsem_lookup_normalize_module x in
          constr:(f' x')
      | @SMod.t _ =>
          let x' := fnsem_lookup_normalize_module x in
          constr:(f' x')
      | _ => constr:(f' x)
      end
  | _ => constr:(t)
  end
with fnsem_lookup_normalize_map_args t :=
  lazymatch t with
  | ?f ?x =>
      let f' := fnsem_lookup_normalize_map_args f in
      let T := type of x in
      lazymatch T with
      | gmap _ (option (emask * fbody)) =>
          let x' := fnsem_lookup_normalize_map x in
          constr:(f' x')
      | gmap _ (option (emask * (option fspec_rel * fbody))) =>
          let x' := fnsem_lookup_normalize_map x in
          constr:(f' x')
      | _ => constr:(f' x)
      end
  | _ => constr:(t)
  end
with fnsem_lookup_normalize_module m :=
  lazymatch m with
  | @Mod.mk ?Σ ?scopes ?fns ?initial ?sorted ?wfns ?winit ?nodup =>
      let fns' := fnsem_lookup_normalize_map fns in
      constr:(@Mod.mk Σ scopes fns' initial sorted wfns winit nodup)
  | @SMod.mk ?Σ ?scopes ?fns ?initial ?sorted ?wfns ?winit ?nodup =>
      let fns' := fnsem_lookup_normalize_map fns in
      constr:(@SMod.mk Σ scopes fns' initial sorted wfns winit nodup)
  | _ =>
      let delta := fnsem_lookup_delta_outer_once_opt m in
      lazymatch delta with
      | Some ?m' =>
          lazymatch m' with
          | @Mod.mk _ _ _ _ _ _ _ _ =>
              let has_arg := fnsem_lookup_has_module_arg m in
              lazymatch has_arg with
              | true => fnsem_lookup_normalize_module_args m
              | false => fnsem_lookup_normalize_module m'
              end
          | @SMod.mk _ _ _ _ _ _ _ _ =>
              let has_arg := fnsem_lookup_has_module_arg m in
              lazymatch has_arg with
              | true => fnsem_lookup_normalize_module_args m
              | false => fnsem_lookup_normalize_module m'
              end
          | _ => fnsem_lookup_normalize_module m'
          end
      | None => constr:(m)
      end
  end
with fnsem_lookup_normalize_map m :=
  lazymatch m with
  | Mod.fnsems ?md =>
      let md' := fnsem_lookup_normalize_module md in
      lazymatch md' with
      | @Mod.mk _ _ ?fns _ _ _ _ _ => fnsem_lookup_normalize_map fns
      | _ => constr:(Mod.fnsems md')
      end
  | SMod.fnsems ?md =>
      let md' := fnsem_lookup_normalize_module md in
      lazymatch md' with
      | @SMod.mk _ _ ?fns _ _ _ _ _ => fnsem_lookup_normalize_map fns
      | _ => constr:(SMod.fnsems md')
      end
  | @base.empty _ _ => constr:(m)
  | _ =>
      let has_arg := fnsem_lookup_has_map_arg m in
      lazymatch has_arg with
      | true => fnsem_lookup_normalize_map_args m
      | false =>
          let delta := fnsem_lookup_delta_outer_once_opt m in
          lazymatch delta with
          | Some ?m' => fnsem_lookup_normalize_map m'
          | None => constr:(m)
          end
      end
  end.

Ltac rewrite_fnsem_lookup fl fn :=
  let Hlookup := fresh "Hlookup" in
  first
    [ assert (Hlookup : FnsemLookupResult fl fn _) by
        solve [once (typeclasses eauto with fnsem_lookup)]
    | let fl' := fnsem_lookup_normalize_map fl in
      assert (Hlookup : FnsemLookupResult fl' fn _) by
        solve [once (typeclasses eauto with fnsem_lookup)]
    ];
  destruct Hlookup as [Hlookup];
  rewrite {1}Hlookup; clear Hlookup.

Ltac prove_inline_cond :=
  first
    [ eassumption
    | lazymatch goal with
      | |- ?fl !! ?fn = Some (Some _) =>
          solve [rewrite_fnsem_lookup fl fn; reflexivity]
      end
    | solve [simpl_map; rewrite /SB.sandbox_body /=; reflexivity]
    | fail 1 "cInline: unable to resolve the function body lookup"
    ].

Ltac prove_sb_cond :=
  by s; i; eauto; try rewrite !mask_app; s; eauto.

Ltac simpl_sp :=
  try match goal with |- context [ ?sp.1 !! ?key ] =>
    first
      [match goal with H: sp.1 !! _ = _ |- _ =>
         rewrite H
       end
      |match goal with H:?sp' ⊆ sp |- _ =>
         erewrite -> (lookup_weaken sp'.1 sp.1 key);
         [  | simpl_map; et; reflexivity | apply H ]
       end]
 end.

(* Normalization tactics *)
Ltac replace_s :=
  lazymatch goal with
  | |- environments.envs_entails ?env (?rel ?its ?itt) =>
      refine (eq_ind_r (λ i, environments.envs_entails env (rel i itt))
               _ _);
      cycle 1
  | |- environments.envs_entails ?env (?P ∗ (?rel ?its ?itt))%I =>
      refine (eq_ind_r (λ i, environments.envs_entails env (P ∗ (rel i itt))%I)
               _ _);
      cycle 1
  end.

Ltac replace_t :=
  lazymatch goal with
  | |- environments.envs_entails ?env (?rel ?its ?itt) =>
      refine (eq_ind_r (λ i, environments.envs_entails env (rel its i))
               _ _);
      cycle 1
  | |- environments.envs_entails ?env (?P ∗ (?rel ?its ?itt))%I =>
      refine (eq_ind_r (λ i, environments.envs_entails env (P ∗ (rel its i))%I)
               _ _);
      cycle 1
  end.

Ltac cNormS := try (replace_s; [s; hnorm_itr|]).
Ltac cNormT := try (replace_t; [s; hnorm_itr|]).

Ltac cNormInlineS := replace_s; [unfold_cris_defs; s; hnorm_itr|].
Ltac cNormInlineT := replace_t; [unfold_cris_defs; s; hnorm_itr|].
