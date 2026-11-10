From CRIS.common Require Import Common ConcRA.
From CRIS.modules Require Import Mod SMod.

Create HintDb fnsem_lookup discriminated.
(** [rewrite_fnsem_lookup] searches only this database. Lookup extensions
    should register their instances here so unsupported heads remain opaque.
    Recursive builders must leave their typeclass premises to the enclosing
    [fnsem_lookup] search by using [notypeclasses refine]. *)
Global Hint Variables Opaque : fnsem_lookup.
Global Hint Constants Opaque : fnsem_lookup.
Global Hint Projections Opaque : fnsem_lookup.
Global Hint Transparent Mod.fnsems SMod.fnsems : fnsem_lookup.

(** Keep concrete leaf-map search separate from composed module search so that
    wrapper instances do not compete at every insert. *)
Class MapLookupResult
  {K A} `{Countable K}
  (m : gmap K A) (k : K) (result : option A) : Prop :=
  { map_lookup_result_eq : m !! k = result }.

Global Hint Mode MapLookupResult + + + + + + - : typeclass_instances.
Global Hint Mode MapLookupResult + + + + + + - : fnsem_lookup.

Global Instance map_lookup_result_empty
  {K A} `{Countable K}
  k
  : MapLookupResult (∅ : gmap K A) k None.
Proof. constructor. apply lookup_empty. Qed.

Global Instance map_lookup_result_insert_hit
  {K A} `{Countable K}
  (m : gmap K A) k v
  : MapLookupResult (<[k := v]> m) k (Some v) | 5.
Proof. constructor. apply lookup_insert. Qed.

Global Instance map_lookup_result_insert
  {K A} `{Countable K}
  (m : gmap K A) k r k1 v1
  `{Hlookup : !MapLookupResult m k r}
  : MapLookupResult (<[k1 := v1]> m) k
      (if decide (k = k1) then Some v1 else r) | 10.
Proof.
  constructor. destruct (decide (k = k1)) as [-> | Hne].
  - apply lookup_insert.
  - rewrite lookup_insert_ne; [apply map_lookup_result_eq | congruence].
Qed.

Class FnsemLookupResult {A}
    (m : gmap fname A) (fn : fname) (result : option A) : Prop :=
  { fnsem_lookup_result_eq : m !! fn = result }.

Global Hint Mode FnsemLookupResult + + + - : typeclass_instances.
Global Hint Mode FnsemLookupResult + + + - : fnsem_lookup.

Global Instance fnsem_lookup_result_add `{Σ : GRA}
    (left right : @Mod.t Σ) fn left_result right_result
    `{Hleft : !FnsemLookupResult (Mod.fnsems left) fn left_result,
      Hright : !FnsemLookupResult (Mod.fnsems right) fn right_result} :
  FnsemLookupResult (Mod.fnsems (left ★ right)) fn
    (union_with uwnd left_result right_result) | 10.
Proof.
  constructor. rewrite /Mod.add /Mod.fnsems /= lookup_union_with
    !fnsem_lookup_result_eq.
  destruct left_result, right_result; done.
Qed.

Global Instance fnsem_lookup_result_to_mod
    `{!crisG Γ Σ α β τ _S _I}
    sp (m : SMod.t) fn result
    `{Hlookup : !MapLookupResult (SMod.fnsems m) fn result} :
  FnsemLookupResult (Mod.fnsems (SMod.to_mod sp m)) fn
    ((λ x : option (emask * (option fspec_rel * fbody)),
        map_snd (SModTr.trans_fnsem sp) <$> x) <$> result) | 30.
Proof.
  constructor. rewrite /SMod.to_mod /Mod.fnsems /= lookup_fmap
    map_lookup_result_eq //.
Qed.

Global Hint Resolve map_lookup_result_empty : fnsem_lookup.
Global Hint Extern 5 (MapLookupResult (<[_ := _]> _) _ _) =>
  lazymatch goal with
  | |- MapLookupResult (<[?k := ?v]> ?m) ?k _ =>
      exact (map_lookup_result_insert_hit m k v)
  end : fnsem_lookup.
Global Hint Extern 10 (MapLookupResult (<[_ := _]> _) _ _) =>
  lazymatch goal with
  | |- MapLookupResult (<[?k1 := ?v1]> ?m) ?k ?out =>
      let T := type of out in
      let r := open_constr:(_ : T) in
      notypeclasses refine
        (@map_lookup_result_insert _ _ _ _ m k r k1 v1 _)
  end : fnsem_lookup.
Global Hint Extern 10
  (FnsemLookupResult (Mod.fnsems (_ ★ _)) _ _) =>
  lazymatch goal with
  | |- FnsemLookupResult (Mod.fnsems (?l ★ ?r)) ?fn _ =>
      let MT := type of (Mod.fnsems l) in
      lazymatch MT with
      | gmap _ ?A =>
          let lr := open_constr:(_ : option A) in
          let rr := open_constr:(_ : option A) in
          notypeclasses refine
            (@fnsem_lookup_result_add _ l r fn lr rr _ _)
      end
  end : fnsem_lookup.
Global Hint Extern 30
  (FnsemLookupResult (Mod.fnsems (SMod.to_mod _ _)) _ _) =>
  lazymatch goal with
  | |- FnsemLookupResult (Mod.fnsems (SMod.to_mod ?sp ?m)) ?fn _ =>
      let MT := type of (SMod.fnsems m) in
      lazymatch MT with
      | gmap _ ?A =>
          let r := open_constr:(_ : option A) in
          notypeclasses refine
            (@fnsem_lookup_result_to_mod _ _ _ _ _ _ _ _ sp m fn r _);
          cbn [SMod.fnsems]
      end
  end : fnsem_lookup.
