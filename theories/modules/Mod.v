From CRIS.common Require Import Common.
From CRIS.modules Require Import LMod.
From iris.proofmode Require Import environments proofmode.
From CRIS.modules Require Export FSpec ModTr Sandbox Sp.
From CRIS.common Require Export Fn.
From stdpp Require Import sorting strings base list.

Definition uwnd {A} : option A → option A → option (option A) :=
  λ _ _, Some None.

Module Mod. Section Mod.
  Context {Σ : GRA}.

  Record t : Type := mk {
    scopes : list string;
    fnsems : gmap fname (option (emask * fbody));
    initial_st : gmap key (option Any.t);

    (* For definitional commutativity of addition *)
    sorted_scopes : StronglySorted String.le scopes;
    well_scoped_fns :
      map_Forall
        (λ _ '((msk, _) : emask * _),
          (∀ (k : key) (v : Any.t),
              msk _ (subevent _ (SPut k v)) = true → scope k ∈ scopes) ∧
          (∀ (k : key),
              msk _ (subevent _ (SGet k)) = true → scope k ∈ scopes))
        (omap id fnsems);
    well_scoped_init :
      (set_map scope (dom initial_st)) ⊆@{gset string} list_to_set scopes;
    nodup_init :
      NoDup scopes → map_Forall (const is_Some) initial_st;
  }.

  Record wf (md : t) : Prop := mk_wf {
    wf_fns : map_Forall (const is_Some) (fnsems md);
    wf_scopes : NoDup (scopes md);
  }.

  (** Linking *)
  Program Definition empty : t := {|
    scopes := [];
    fnsems := ∅;
    initial_st := ∅;
  |}.
  Solve All Obligations with ii; ss; econs.

  Program Definition add (ms1 ms2 : t) : t := {|
    scopes := merge_sort String.le ((scopes ms1) ++ (scopes ms2));
    fnsems := union_with uwnd (fnsems ms1) (fnsems ms2);
    initial_st := union_with uwnd (initial_st ms1) (initial_st ms2);
  |}.
  Next Obligation. intros; apply StronglySorted_merge_sort; typeclasses eauto. Qed.
  Next Obligation.
    intros ms1 ms2 fn [msk p].
    rewrite lookup_omap lookup_union_with.
    destruct ((fnsems ms1) !! fn) eqn: Heq1; destruct ((fnsems ms2) !! fn) eqn: Heq2; ss; intros ->.
    { hexploit (ms1.(well_scoped_fns) fn (msk, p)); eauto.
      { rewrite lookup_omap Heq1 //. }
      intros [? ?]; split; ii; rewrite merge_sort_Permutation elem_of_app; left; eauto.
    }
    { hexploit (ms2.(well_scoped_fns) fn (msk, p)); eauto.
      { rewrite lookup_omap Heq2 //. }  
      intros [? ?]; split; ii; rewrite merge_sort_Permutation elem_of_app; right; eauto.
    }
  Qed.
  Next Obligation.
    intros ms1 ms2 fn [[scp f] [-> [? Hin]%elem_of_dom]]%elem_of_map; ss.
    rewrite merge_sort_Permutation list_to_set_app elem_of_union.
    apply lookup_union_with_Some in Hin; des; ss; [left|right|left].
    { hexploit (ms1.(well_scoped_init)) => /(_ scp).
      intros k; apply: k; apply elem_of_map; eexists (scp ↯ f); split;
        eauto; apply elem_of_dom; done.
    }
    { hexploit (ms2.(well_scoped_init)) => /(_ scp).
      intros k; apply: k; apply elem_of_map; eexists (scp ↯ f); split;
        eauto; apply elem_of_dom; done.
    }
    { hexploit (ms1.(well_scoped_init)) => /(_ scp).
      intros k; apply: k; apply elem_of_map; eexists (scp ↯ f); split;
        eauto; apply elem_of_dom; done.
    }
  Qed.
  Next Obligation.
    intros ms1 ms2; rewrite merge_sort_Permutation; intros [? [Hnd ?]]%NoDup_app.
    rewrite map_Forall_lookup; intros [scp key] v.
    rewrite lookup_union_with_Some; intros [Hl | [Hl | [? [? [Hl1 Hl2]]]]]; des.
    { apply (nodup_init ms1); eauto. }
    { apply (nodup_init ms2); eauto. }
    exfalso; apply (Hnd scp).
    { hexploit (well_scoped_init ms1) => /(_ scp); rewrite elem_of_map.
      intros Hin1; hexploit Hin1;
        [exists (scp ↯ key); split; ss; apply elem_of_dom; eauto|].
      set_solver.
    }
    { hexploit (well_scoped_init ms2) => /(_ scp); rewrite elem_of_map.
      intros Hin2; hexploit Hin2;
        [exists (scp ↯ key); split; ss; apply elem_of_dom; eauto|].
      set_solver.
    }
  Qed.

  Lemma t_eq (ms1 ms2 : t) :
    scopes ms1 = scopes ms2 →
    fnsems ms1 = fnsems ms2 →
    initial_st ms1 = initial_st ms2 →
    ms1 = ms2.
  Proof.
    destruct ms1, ms2; ss. intros Hscp Hfns Hst.
    subst scopes0 fnsems0 initial_st0; f_equal; apply proof_irrelevance.
  Qed.

  Lemma add_comm (ms1 ms2 : t) : Mod.add ms1 ms2 = Mod.add ms2 ms1.
  Proof.
    apply t_eq; ss.
    { apply (StronglySorted_unique String.le).
      { apply StronglySorted_merge_sort; try typeclasses eauto. }
      { apply StronglySorted_merge_sort; try typeclasses eauto. }
      rewrite !merge_sort_Permutation comm //.
    }
    { apply fin_maps.union_with_comm; done. }
    { apply fin_maps.union_with_comm; done. }
  Qed.

  Lemma add_wf (ms1 ms2 : t) :
    wf ms1 → wf ms2 →
    dom (fnsems ms1) ## dom (fnsems ms2) →
    NoDup (scopes ms1 ++ scopes ms2) →
    wf (add ms1 ms2).
  Proof.
    intros Hwf1 Hwf2 Hfnsems Hscopes; econs.
    { rewrite map_Forall_lookup; intros i x; rewrite lookup_union_with.
      destruct (_ ms1 !! i) eqn : H1; destruct (_ ms2 !! i) eqn : H2; ss.
      { eapply elem_of_dom_2 in H1, H2; set_solver. }
      { inv Hwf1; i; clarify; eapply wf_fns0; eauto. }
      { inv Hwf2; i; clarify; eapply wf_fns0; eauto. }
    }
    { ss; rewrite merge_sort_Permutation //. }
  Qed.

  Lemma add_wf_inv (ms1 ms2 : t) :
    wf (add ms1 ms2) →
    wf ms1 ∧ wf ms2 ∧ (dom (fnsems ms1) ## dom (fnsems ms2)) ∧ NoDup (scopes ms1 ++ scopes ms2).
  Proof.
    intros [Hfnsems Hscopes]; ss; rewrite merge_sort_Permutation // in Hscopes; splits; eauto.
    { econs.
      { rewrite map_Forall_lookup; intros i x Hix; rewrite map_Forall_lookup in Hfnsems.
        hexploit (Hfnsems i x); eauto.
        rewrite lookup_union_with Hix; destruct (_ ms2 !! i) eqn : Hms2; ss.
        hexploit (Hfnsems i None); [rewrite lookup_union_with Hix Hms2 //|intros Hf; inv Hf].
      }
      { apply NoDup_app in Hscopes; by des. }
    }
    { econs.
      { rewrite map_Forall_lookup; intros i x Hix; rewrite map_Forall_lookup in Hfnsems.
        hexploit (Hfnsems i x); eauto.
        rewrite lookup_union_with Hix; destruct (_ ms1 !! i) eqn : Hms1; ss.
        hexploit (Hfnsems i None); [rewrite lookup_union_with Hix Hms1 //|intros Hf; inv Hf].
      }
      { apply NoDup_app in Hscopes; by des. }
    }
    { intros fn ??; rewrite map_Forall_lookup in Hfnsems; hexploit (Hfnsems fn None); [|by intros []].
      rewrite -> elem_of_dom in *; s; rewrite lookup_union_with; repeat (destruct (_ !! _)); ss;
        exfalso; eapply is_Some_None; eauto.
    }
  Qed.

  Lemma dom_fnsems_add (ms1 ms2 : t) :
    dom (fnsems (add ms1 ms2)) = dom (fnsems ms1) ∪ dom (fnsems ms2).
  Proof.
    apply set_eq; intros x; s; rewrite elem_of_union ?elem_of_dom lookup_union_with.
    destruct (_ ms1 !! x); destruct (_ ms2 !! x); ss; naive_solver.
  Qed.

  Lemma maxlen_scopes_add m1 m2:
    maxlen (Mod.scopes (add m1 m2)) = max (maxlen (Mod.scopes m1)) (maxlen (Mod.scopes m2)).
  Proof.
    s. rewrite /maxlen sorting.merge_sort_Permutation fmap_app list_max_app. et.
  Qed.

  Lemma lookup_add_l (ms1 ms2 : t) (fno : fname) (mb : emask * fbody) :
    wf (add ms1 ms2) →
    (fnsems ms1) !! fno = Some (Some mb) →
    (fnsems (add ms1 ms2)) !! fno = Some (Some mb).
  Proof.
    intros Hwf; rewrite /= lookup_union_with => Hin; rewrite Hin.
    hexploit (wf_fns _ Hwf); rewrite map_Forall_lookup => /(_ fno) /=.
    rewrite lookup_union_with Hin; destruct (_ ms2 !! _) eqn : Hms2; ss.
    by move => /(_ None (reflexivity _)) [? ?].
  Qed.

  Lemma lookup_add_r (ms1 ms2 : t) (fno : fname) (mb : emask * fbody) :
    wf (add ms1 ms2) →
    (fnsems ms2) !! fno = Some (Some mb) →
    (fnsems (add ms1 ms2)) !! fno = Some (Some mb).
  Proof.
    intros Hwf; rewrite /= lookup_union_with => Hin; rewrite Hin.
    hexploit (wf_fns _ Hwf); rewrite map_Forall_lookup => /(_ fno) /=.
    rewrite lookup_union_with Hin; destruct (_ ms1 !! _) eqn : Hms1; ss.
    by move => /(_ None (reflexivity _)) [? ?].
  Qed.

  Definition to_lmod (ms : t) (r : Σ) : LMod.t Σ := {|
    LMod.fnsems := ModTr.trans_fnsem <$> (SB.sandbox_body <$> omap id (fnsems ms));
    LMod.initial_st := (initial_st ms, r);
  |}.

  Lemma to_lmod_fnsems (m : t) (r : Σ) (fn : fname) :
    LMod.fnsems (Mod.to_lmod m r) !! fn =
    ModTr.trans_fnsem <$> (SB.sandbox_body <$> ((fnsems m) !! fn ≫= id)).
  Proof. ss; rewrite ?lookup_fmap lookup_omap //. Qed.

  Lemma mod_dom_subseteq (ms1 ms2 ms3 : t) :
    dom (fnsems ms1) ⊆ dom (fnsems ms2) →
    dom (fnsems (Mod.add ms1 ms3)) ⊆ dom (fnsems (Mod.add ms2 ms3)).
  Proof.
    intros Hsub x; rewrite ?elem_of_dom ?lookup_union_with.
    destruct (_ ms1 !! x) eqn: Heq1.
    { apply elem_of_dom_2, Hsub, elem_of_dom in Heq1.
      destruct (_ ms2 !! x) eqn : Heq2; [|inv Heq1].
      destruct (_ ms3 !! x); ss.
    }
    { apply not_elem_of_dom_2 in Heq1.
      destruct (_ ms3 !! x) eqn : Heq3; [|intros ?%is_Some_None]; ss.
      destruct (_ ms2 !! x) eqn : Heq2; ss.
    }
  Qed.

  Definition addL (ms : list t) : t := foldr add empty ms.
End Mod. End Mod.

Infix "★" := Mod.add (at level 60, right associativity).
Notation "⌽" := Mod.empty.

Definition real_mod `{Σ : GRA} (md : Mod.t) : Prop :=
  map_Forall
    (λ _ (v : option (emask * fbody)),
      match v with
      | Some (msk, _) =>
          (∀ P, msk _ (subevent _ (Assume P)) = false) ∧
          ∀ X, msk _ (subevent _ (Take X)) = true → ∃ (P : Prop), X = P
      | _ => True
      end) (Mod.fnsems md).

Lemma real_mod_add `{Σ : GRA} (md1 md2 : Mod.t) :
  real_mod md1 → real_mod md2 → real_mod (md1 ★ md2).
Proof.
  rewrite /real_mod !map_Forall_lookup => H1 H2 i x; rewrite /Mod.fnsems /= lookup_union_with /uwnd.
  specialize (H1 i); specialize (H2 i); i; repeat destruct lookup as [[[? ?]|]|]; ss; clarify.
  { hexploit (H1 (Some (e, f))); ss. }
  { hexploit (H2 (Some (e, f))); ss. }
Qed.

Section ModFacts.
  Context `{Σ : GRA}.

  Lemma mod_add_assoc (md1 md2 md3 : Mod.t) :
    md1 ★ (md2 ★ md3) = (md1 ★ md2) ★ md3.
  Proof using.
    destruct md1, md2, md3.
    apply Mod.t_eq; s; try rewrite assoc //.
    { apply (StronglySorted_unique String.le).
      { apply StronglySorted_merge_sort; try typeclasses eauto. }
      { apply StronglySorted_merge_sort; try typeclasses eauto. }
      rewrite !merge_sort_Permutation assoc //.
    }
    { apply map_eq; intros ?; rewrite ?lookup_union_with; repeat (destruct (_ !! _)); ss. }
    { apply map_eq; intros ?; rewrite ?lookup_union_with; repeat (destruct (_ !! _)); ss. }
  Qed.

  Lemma mod_add_empty_l (md : Mod.t) : ⌽ ★ md = md.
  Proof using.
    destruct md. apply Mod.t_eq; s; rewrite ?left_id //.
    apply (StronglySorted_unique String.le); eauto.
    { apply StronglySorted_merge_sort; try typeclasses eauto. }
    rewrite !merge_sort_Permutation //.
  Qed.

  Lemma mod_add_empty_r (md : Mod.t) : md ★ ⌽ = md.
  Proof using.
    destruct md. apply Mod.t_eq; s; rewrite ?right_id //.
    apply (StronglySorted_unique String.le); eauto.
    { apply StronglySorted_merge_sort; try typeclasses eauto. }
    rewrite !merge_sort_Permutation //.
  Qed.

End ModFacts.

Global Instance _mod_add_comm `{Σ: GRA} : Comm eq Mod.add := Mod.add_comm.
Global Instance _mod_add_assoc `{Σ: GRA} : Assoc eq Mod.add := mod_add_assoc.
Global Instance _mod_left_id `{Σ: GRA} : LeftId eq Mod.empty Mod.add := mod_add_empty_l.
Global Instance _mod_right_id `{Σ: GRA} : RightId eq Mod.empty Mod.add := mod_add_empty_r.

(* Lemmas related to module states and function maps *)
Lemma dom_union_with `{Countable K} {V} (m1 m2 : gmap K (option V)) :
  dom (union_with uwnd m1 m2) =
  dom m1 ∪ dom m2.
Proof.
  apply set_eq; intros x; split;
    rewrite elem_of_union ?elem_of_dom lookup_union_with; repeat destruct (_ !! _); ss; eauto.
  intros [[]|[]]; done.
Qed.

Lemma map_Forall_union_with_inv_gen `{Countable K} {V} (m1 m2 : gmap K (option V)) :
  map_Forall (const is_Some) (union_with uwnd m1 m2) →
  dom m1 ## dom m2.
Proof.
  rewrite ?map_Forall_lookup => Hwf; intros i [? H1]%elem_of_dom [? H2]%elem_of_dom;
    move: (Hwf i None); rewrite lookup_union_with H1 H2 /=; intros H3; hexploit H3; eauto.
  by intros [].
Qed.

Lemma map_Forall_union_with_inv `{Countable K} {V} (m1 m2 : gmap K (option V)) :
  map_Forall (const is_Some) (union_with uwnd m1 m2) →
  map_Forall (const is_Some) m1 ∧ map_Forall (const is_Some) m2.
Proof.
  rewrite ?map_Forall_lookup => Hwf; split; intros i v Hi; move: (Hwf i v);
    rewrite lookup_union_with Hi; repeat destruct (_ !! i) as [[|]|]; ss; clarify; eauto.
Qed.

Lemma map_Forall_union_with `{Countable K} {V} (m1 m2 : gmap K (option V)) :
  dom m1 ## dom m2 →
  map_Forall (const is_Some) m1 ∧ map_Forall (const is_Some) m2 →
  map_Forall (const is_Some) (union_with uwnd m1 m2).
Proof.
  intros Hdom; rewrite ?map_Forall_lookup => [[H1 H2] i] x;
    specialize (H1 i); specialize (H2 i); rewrite lookup_union_with;
    repeat match goal with | |- context [?m !! ?i] => destruct (m !! i) eqn : ? end;
    ss; try set_solver.
  repeat match goal with | H : _ !! _ = Some _ |- _ => eapply elem_of_dom_2 in H end; set_solver.
Qed.

Lemma lookup_union_with_l `{Countable K} {V} (m1 m2 : gmap K (option V)) (k : K) v :
  map_Forall (const is_Some) (union_with uwnd m1 m2) →
  m1 !! k = Some v →
  union_with uwnd m1 m2 !! k = Some v.
Proof.
  intros Hwf Hm1; rewrite lookup_union_with Hm1; destruct (m2 !! k) as [[|]|] eqn : Hm2; ss;
    apply map_Forall_lookup in Hwf; move: (Hwf k None); rewrite lookup_union_with Hm1 Hm2;
    move => /(_ eq_refl) [? ?] //.
Qed.

Lemma lookup_union_with_r `{Countable K} {V} (m1 m2 : gmap K (option V)) (k : K) v :
  map_Forall (const is_Some) (union_with uwnd m1 m2) →
  m2 !! k = Some v →
  union_with uwnd m1 m2 !! k = Some v.
Proof.
  intros Hwf Hm2; rewrite lookup_union_with Hm2; destruct (m1 !! k) as [[|]|] eqn : Hm1; ss;
    apply map_Forall_lookup in Hwf; move: (Hwf k None); rewrite lookup_union_with Hm1 Hm2;
    move => /(_ eq_refl) [? ?] //.
Qed.

Lemma insert_union_with_l' `{Countable K} {V} (m1 m2 : gmap K (option V)) (k : K) v :
  map_Forall (const is_Some) (union_with uwnd m1 m2) →
  is_Some (m1 !! k) →
  <[k := v]> (union_with uwnd m1 m2) =
  union_with uwnd (<[k := v]> m1) m2.
Proof.
  intros Hwf [? Hm1]; apply insert_union_with_l.
  destruct (m2 !! k) as [[|]|] eqn : Hm2; ss;
    apply map_Forall_lookup in Hwf; move: (Hwf k None); rewrite lookup_union_with Hm1 Hm2;
    move => /(_ eq_refl) [? ?] //.
Qed.

Lemma insert_union_with_r' `{Countable K} {V} (m1 m2 : gmap K (option V)) (k : K) v :
  map_Forall (const is_Some) (union_with uwnd m1 m2) →
  is_Some (m2 !! k) →
  <[k := v]> (union_with uwnd m1 m2) =
  union_with uwnd m1 (<[k := v]> m2).
Proof.
  intros Hwf [? Hm2]; apply insert_union_with_r.
  destruct (m1 !! k) as [[|]|] eqn : Hm1; ss;
    apply map_Forall_lookup in Hwf; move: (Hwf k None); rewrite lookup_union_with Hm1 Hm2;
    move => /(_ eq_refl) [? ?] //.
Qed.

Lemma map_Forall_insert_union_with `{Countable K} {V} (m1 m2 : gmap K (option V)) k v :
  map_Forall (const is_Some) (union_with uwnd m1 m2) →
  map_Forall (const is_Some) (<[k := Some v]> (union_with uwnd m1 m2)).
Proof.
  intros Hwf; destruct (decide (k ∈ dom m1)) as [Hm1|Hm1].
  { apply elem_of_dom in Hm1; rewrite insert_union_with_l' //.
    eapply map_Forall_union_with_inv_gen in Hwf as ?.
    eapply map_Forall_union_with_inv in Hwf as [? ?].
    eapply map_Forall_union_with.
    { rewrite dom_insert.
      rewrite -elem_of_dom in Hm1; set_solver.
    }
    { split; last done.
      apply map_Forall_insert_2; eauto; ss.
    }
  }
  rewrite insert_union_with_r.
  { eapply map_Forall_union_with_inv_gen in Hwf as ?.
    eapply map_Forall_union_with_inv in Hwf as [? ?].
    eapply map_Forall_union_with.
    { rewrite dom_insert. set_solver. }
    { split; first done.
      apply map_Forall_insert_2; eauto; ss.
    }
  }
  { destruct lookup eqn: temp; ss; eapply elem_of_dom_2 in temp; set_solver. }
Qed.

Lemma lookup_fnsems_inv `{Σ : GRA} (m1 m2 : Mod.t) (k : fname) v :
  Mod.wf (m1 ★ m2) →
  (Mod.fnsems (m1 ★ m2)) !! k = Some v →
  (Mod.fnsems m1 !! k = Some v ∧ Mod.fnsems m2 !! k = None) ∨
  (Mod.fnsems m1 !! k = None ∧ Mod.fnsems m2 !! k = Some v).
Proof.
  intros Hwf H; inv Hwf; rewrite map_Forall_lookup in wf_fns; hexploit (wf_fns); eauto.
  revert H; ss; rewrite lookup_union_with; repeat destruct (_ !! _); ss; intros H; eauto; inv H.
  intros []; ss.
Qed.

Lemma lookup_fnsems_l `{Σ : GRA} (m1 m2 : Mod.t) (k : fname) v :
  Mod.wf (m1 ★ m2) →
  (Mod.fnsems m1) !! k = Some v →
  (Mod.fnsems (m1 ★ m2)) !! k = Some v.
Proof.
  intros Hwf H; inv Hwf; ss.
  etransitivity; [eapply lookup_union_with_l|]; eauto.
Qed.

Lemma lookup_fnsems_l_2 `{Σ : GRA} (m1 m2 : Mod.t) (k : fname) :
  Mod.wf (m1 ★ m2) →
  k ∈ dom (Mod.fnsems m1) →
  (Mod.fnsems (m1 ★ m2)) !! k = Mod.fnsems m1 !! k.
Proof.
  intros Hwf H; rewrite /= lookup_union_with; destruct (Mod.fnsems m2 !! k) eqn : Hm2.
  { apply elem_of_dom_2 in Hm2; apply Mod.add_wf_inv in Hwf; des; exfalso; set_solver. }
  repeat destruct lookup; ss.
Qed.

Lemma lookup_fnsems_r `{Σ : GRA} (m1 m2 : Mod.t) (k : fname) v :
  Mod.wf (m1 ★ m2) →
  (Mod.fnsems m2) !! k = Some v →
  (Mod.fnsems (m1 ★ m2)) !! k = Some v.
Proof.
  intros Hwf H; inv Hwf; ss.
  etransitivity; [eapply lookup_union_with_r|]; eauto.
Qed.

Lemma lookup_fnsems_r_2 `{Σ : GRA} (m1 m2 : Mod.t) (k : fname) :
  Mod.wf (m1 ★ m2) →
  k ∈ dom (Mod.fnsems m2) →
  (Mod.fnsems (m1 ★ m2)) !! k = Mod.fnsems m2 !! k.
Proof.
  intros Hwf H; rewrite /= lookup_union_with; destruct (Mod.fnsems m1 !! k) eqn : Hm1.
  { apply elem_of_dom_2 in Hm1; apply Mod.add_wf_inv in Hwf; des; exfalso; set_solver. }
  repeat destruct lookup; ss.
Qed.

Lemma lookup_fnsems_None_l `{Σ : GRA} (m1 m2 : Mod.t) (k : fname) :
  Mod.wf (m1 ★ m2) →
  (Mod.fnsems m1) !! k = None →
  (Mod.fnsems (m1 ★ m2)) !! k = (Mod.fnsems m2) !! k.
Proof.
  intros Hwf H; inv Hwf; ss.
  rewrite lookup_union_with H; destruct (_ m2 !! _); ss.
Qed.

Lemma lookup_fnsems_None_r `{Σ : GRA} (m1 m2 : Mod.t) (k : fname) :
  Mod.wf (m1 ★ m2) →
  (Mod.fnsems m2) !! k = None →
  (Mod.fnsems (m1 ★ m2)) !! k = (Mod.fnsems m1) !! k.
Proof.
  intros Hwf H; inv Hwf; ss.
  rewrite lookup_union_with H; destruct (_ m1 !! _); ss.
Qed.

Lemma lookup_fnsems_l2 `{Σ : GRA} (m1 m2 : Mod.t) (k : fname) v :
  (Mod.fnsems m1) !! k = None →
  (Mod.fnsems m2) !! k = Some v →
  (Mod.fnsems (m1 ★ m2)) !! k = Some v.
Proof. rewrite lookup_union_with => -> -> //. Qed.

Lemma lookup_fnsems_r2 `{Σ : GRA} (m1 m2 : Mod.t) (k : fname) v :
  (Mod.fnsems m1) !! k = Some v →
  (Mod.fnsems m2) !! k = None →
  (Mod.fnsems (m1 ★ m2)) !! k = Some v.
Proof. rewrite lookup_union_with => -> -> //. Qed.

Lemma lookup_fnsems_None `{Σ : GRA} (m1 m2 : Mod.t) (k : fname) :
  (Mod.fnsems m1) !! k = None →
  (Mod.fnsems m2) !! k = None →
  (Mod.fnsems (m1 ★ m2)) !! k = None.
Proof. rewrite lookup_union_with => -> -> //. Qed.

(* Tactics for map definitions. *)
Tactic Notation "mod_tac1" tactic0(tac) := i;
  let rec go :=
    match goal with
    | |- Sorted.StronglySorted String.le ?scopes =>
        (apply Sorted.SSorted_nil || (apply Sorted.SSorted_cons; [go|by tac]))
    | |- map_Forall _ _ =>
        first
          [ rewrite fmap_insert; cbn; go
          | rewrite fmap_empty; cbn; go
          | rewrite omap_insert; cbn; go
          | rewrite omap_empty; go
          | apply map_Forall_insert_2; [by tac|go]
          | apply map_Forall_singleton; by tac
          | apply map_Forall_empty; by tac
          | (progress rewrite /Mod.fnsems); cbn; go
          ]
    | |- _ => (repeat rewrite Mod.dom_fnsems_add); set_solver
    end
  in go.
Ltac scope_solver := ss; split; i; case_decide; naive_solver.
Tactic Notation "mod_tac1" := mod_tac1 scope_solver.

Tactic Notation "mod_tac" tactic0(tac) :=
  i; repeat (eapply map_Forall_union_with;
             [by (repeat rewrite Mod.dom_fnsems_add); set_solver|split]);
  mod_tac1 tac.
Tactic Notation "mod_tac" := mod_tac scope_solver.

Ltac _real_mod_solver :=
  (split; ss; intros ??; destruct excluded_middle_informative; ss).

Ltac real_mod_solver :=
  rewrite /Mod.real_mod; mod_tac _real_mod_solver.

Ltac mod_eq_solver :=
  repeat (try rewrite -!assoc; try rewrite Mod.add_comm;
          try rewrite -!assoc; try (eapply f_equal2; [refl|])); et.

Ltac unfold_fnsem :=
  rewrite /Mod.fnsems /=;
  try match goal with | [|-context[?x]] =>
    match type of x with gmap fname (option (emask * (option fspec_rel * fbody))) =>
       rewrite {1}/x /=
    end
  end.

Hint Extern 80 (Mod.fnsems (_ ★ _) !! _ = Some _) => eapply lookup_fnsems_l2 : simpl_map.
Hint Extern 80 (Mod.fnsems (_ ★ _) !! _ = Some _) => eapply lookup_fnsems_r2 : simpl_map.
Hint Extern 80 (Mod.fnsems (_ ★ _) !! _ = None) => eapply lookup_fnsems_None : simpl_map.
Hint Extern 100 (?A !! _ = _) =>
  match type of A with
  | specmap => rewrite /A /=; simpl_map
  end : simpl_map.
Global Hint Extern 90 (_ ≠ _) => try by (let a := fresh in intros a; inv a) : simpl_map.
Global Hint Extern 90 =>
    match goal with
    | H : Mod.wf ?M |- Mod.fnsems ?M !! _ = _ =>
      (eapply Mod.lookup_add_l;
      [eauto|eapply Mod.add_wf_inv in H as [? [? [? ?]]]]; progress simpl_map) ||
      (eapply Mod.lookup_add_r;
        [eauto|eapply Mod.add_wf_inv in H as [? [? [? ?]]]]; progress simpl_map)
    end : simpl_map.
Hint Extern 81 (Mod.fnsems _ !! _ = Some _) => unfold_fnsem; simpl_map; eauto : simpl_map.
Hint Extern 81 (Mod.fnsems _ !! _ = None) => unfold_fnsem; simpl_map; eauto : simpl_map.

Arguments Mod.add : simpl never.
Arguments Mod.fnsems : simpl never.

(***************
 Map Notations
 **************)

Notation "m1 +# m2" := (union_with uwnd m1 m2) (at level 50) : stdpp_scope.

(*** Some on RHS ***)

Notation "{[ k1 # a1 ]}" := (singletonM k1 (Some a1))
  (at level 1, format
  "{[ k1  #  a1 ]}") : stdpp_scope.
Notation "{[ k1 # a1 ; k2 # a2 ]}" :=
  (<[ k1 := Some a1 ]> {[ k2 := Some a2 ]})
  (at level 1, format
  "{[ '[hv' '[' k1  #  a1 ;  ']' '/' '[' k2  #  a2 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 # a1 ; k2 # a2 ; k3 # a3 ]}" :=
  (<[ k1 := Some a1 ]> $ <[ k2 := Some a2 ]> {[ k3 := Some a3 ]})
  (at level 1, format
  "{[ '[hv' '[' k1  #  a1 ;  ']' '/' '[' k2  #  a2 ;  ']' '/' '[' k3  #  a3 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 # a1 ; k2 # a2 ; k3 # a3 ; k4 # a4 ]}" :=
  (<[ k1 := Some a1 ]> $ <[ k2 := Some a2 ]> $ <[ k3 := Some a3 ]> {[ k4 := Some a4 ]})
  (at level 1, format
  "{[ '[hv' '[' k1  #  a1 ;  ']' '/' '[' k2  #  a2 ;  ']' '/' '[' k3  #  a3 ;  ']' '/' '[' k4  #  a4 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 # a1 ; k2 # a2 ; k3 # a3 ; k4 # a4 ; k5 # a5 ]}" :=
  (<[ k1 := Some a1 ]> $ <[ k2 := Some a2 ]> $ <[ k3 := Some a3 ]> $ <[ k4 := Some a4 ]> {[ k5 := Some a5 ]})
  (at level 1, format
  "{[ '[hv' '[' k1  #  a1 ;  ']' '/' '[' k2  #  a2 ;  ']' '/' '[' k3  #  a3 ;  ']' '/' '[' k4  #  a4 ;  ']' '/' '[' k5  #  a5 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 # a1 ; k2 # a2 ; k3 # a3 ; k4 # a4 ; k5 # a5 ; k6 # a6 ]}" :=
  (<[ k1 := Some a1 ]> $ <[ k2 := Some a2 ]> $ <[ k3 := Some a3 ]> $ <[ k4 := Some a4 ]> $
    <[ k5 := Some a5 ]> {[ k6 := Some a6 ]})
  (at level 1, format
  "{[ '[hv' '[' k1  #  a1 ;  ']' '/' '[' k2  #  a2 ;  ']' '/' '[' k3  #  a3 ;  ']' '/' '[' k4  #  a4 ;  ']' '/' '[' k5  #  a5 ;  ']' '/' '[' k6  #  a6 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 # a1 ; k2 # a2 ; k3 # a3 ; k4 # a4 ; k5 # a5 ; k6 # a6 ; k7 # a7 ]}" :=
  (<[ k1 := Some a1 ]> $ <[ k2 := Some a2 ]> $ <[ k3 := Some a3 ]> $ <[ k4 := Some a4 ]> $
    <[ k5 := Some a5 ]> $ <[ k6 := Some a6 ]> {[ k7 := Some a7 ]})
  (at level 1, format
  "{[ '[hv' '[' k1  #  a1 ;  ']' '/' '[' k2  #  a2 ;  ']' '/' '[' k3  #  a3 ;  ']' '/' '[' k4  #  a4 ;  ']' '/' '[' k5  #  a5 ;  ']' '/' '[' k6  #  a6 ;  ']' '/' '[' k7  #  a7 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 # a1 ; k2 # a2 ; k3 # a3 ; k4 # a4 ; k5 # a5 ; k6 # a6 ; k7 # a7 ; k8 # a8 ]}" :=
  (<[ k1 := Some a1 ]> $ <[ k2 := Some a2 ]> $ <[ k3 := Some a3 ]> $ <[ k4 := Some a4 ]> $
    <[ k5 := Some a5 ]> $ <[ k6 := Some a6 ]> $ <[ k7 := Some a7 ]> {[ k8 := Some a8 ]})
  (at level 1, format
  "{[ '[hv' '[' k1  #  a1 ;  ']' '/' '[' k2  #  a2 ;  ']' '/' '[' k3  #  a3 ;  ']' '/' '[' k4  #  a4 ;  ']' '/' '[' k5  #  a5 ;  ']' '/' '[' k6  #  a6 ;  ']' '/' '[' k7  #  a7 ;  ']' '/' '[' k8  #  a8 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 # a1 ; k2 # a2 ; k3 # a3 ; k4 # a4 ; k5 # a5 ; k6 # a6 ; k7 # a7 ; k8 # a8 ; k9 # a9 ]}" :=
  (<[ k1 := Some a1 ]> $ <[ k2 := Some a2 ]> $ <[ k3 := Some a3 ]> $ <[ k4 := Some a4 ]> $
    <[ k5 := Some a5 ]> $ <[ k6 := Some a6 ]> $ <[ k7 := Some a7 ]> $ <[ k8 := Some a8 ]> {[ k9 := Some a9 ]})
  (at level 1, format
  "{[ '[hv' '[' k1  #  a1 ;  ']' '/' '[' k2  #  a2 ;  ']' '/' '[' k3  #  a3 ;  ']' '/' '[' k4  #  a4 ;  ']' '/' '[' k5  #  a5 ;  ']' '/' '[' k6  #  a6 ;  ']' '/' '[' k7  #  a7 ;  ']' '/' '[' k8  #  a8 ;  ']' '/' '[' k9  #  a9 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 # a1 ; k2 # a2 ; k3 # a3 ; k4 # a4 ; k5 # a5 ; k6 # a6 ; k7 # a7 ; k8 # a8 ; k9 # a9 ; k10 # a10 ]}" :=
  (<[ k1 := Some a1 ]> $ <[ k2 := Some a2 ]> $ <[ k3 := Some a3 ]> $ <[ k4 := Some a4 ]> $
    <[ k5 := Some a5 ]> $ <[ k6 := Some a6 ]> $ <[ k7 := Some a7 ]> $ <[ k8 := Some a8 ]> $
    <[ k9 := Some a9 ]> {[ k10 := Some a10 ]})
  (at level 1, format
  "{[ '[hv' '[' k1  #  a1 ;  ']' '/' '[' k2  #  a2 ;  ']' '/' '[' k3  #  a3 ;  ']' '/' '[' k4  #  a4 ;  ']' '/' '[' k5  #  a5 ;  ']' '/' '[' k6  #  a6 ;  ']' '/' '[' k7  #  a7 ;  ']' '/' '[' k8  #  a8 ;  ']' '/' '[' k9  #  a9 ;  ']' '/' '[' k10  #  a10 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 # a1 ; k2 # a2 ; k3 # a3 ; k4 # a4 ; k5 # a5 ; k6 # a6 ; k7 # a7 ; k8 # a8 ; k9 # a9 ; k10 # a10 ; k11 # a11 ]}" :=
  (<[ k1 := Some a1 ]> $ <[ k2 := Some a2 ]> $ <[ k3 := Some a3 ]> $ <[ k4 := Some a4 ]> $
    <[ k5 := Some a5 ]> $ <[ k6 := Some a6 ]> $ <[ k7 := Some a7 ]> $ <[ k8 := Some a8 ]> $
    <[ k9 := Some a9 ]> $ <[ k10 := Some a10 ]> {[ k11 := Some a11 ]})
  (at level 1, format
  "{[ '[hv' '[' k1  #  a1 ;  ']' '/' '[' k2  #  a2 ;  ']' '/' '[' k3  #  a3 ;  ']' '/' '[' k4  #  a4 ;  ']' '/' '[' k5  #  a5 ;  ']' '/' '[' k6  #  a6 ;  ']' '/' '[' k7  #  a7 ;  ']' '/' '[' k8  #  a8 ;  ']' '/' '[' k9  #  a9 ;  ']' '/' '[' k10  #  a10 ;  ']' '/' '[' k11  #  a11 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 # a1 ; k2 # a2 ; k3 # a3 ; k4 # a4 ; k5 # a5 ; k6 # a6 ; k7 # a7 ; k8 # a8 ; k9 # a9 ; k10 # a10 ; k11 # a11 ; k12 # a12 ]}" :=
  (<[ k1 := Some a1 ]> $ <[ k2 := Some a2 ]> $ <[ k3 := Some a3 ]> $ <[ k4 := Some a4 ]> $
    <[ k5 := Some a5 ]> $ <[ k6 := Some a6 ]> $ <[ k7 := Some a7 ]> $ <[ k8 := Some a8 ]> $
    <[ k9 := Some a9 ]> $ <[ k10 := Some a10 ]> $ <[ k11 := Some a11 ]> {[ k12 := Some a12 ]})
  (at level 1, format
  "{[ '[hv' '[' k1  #  a1 ;  ']' '/' '[' k2  #  a2 ;  ']' '/' '[' k3  #  a3 ;  ']' '/' '[' k4  #  a4 ;  ']' '/' '[' k5  #  a5 ;  ']' '/' '[' k6  #  a6 ;  ']' '/' '[' k7  #  a7 ;  ']' '/' '[' k8  #  a8 ;  ']' '/' '[' k9  #  a9 ;  ']' '/' '[' k10  #  a10 ;  ']' '/' '[' k11  #  a11 ;  ']' '/' '[' k12  #  a12 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 # a1 ; k2 # a2 ; k3 # a3 ; k4 # a4 ; k5 # a5 ; k6 # a6 ; k7 # a7 ; k8 # a8 ; k9 # a9 ; k10 # a10 ; k11 # a11 ; k12 # a12 ; k13 # a13 ]}" :=
  (<[ k1 := Some a1 ]> $ <[ k2 := Some a2 ]> $ <[ k3 := Some a3 ]> $ <[ k4 := Some a4 ]> $
    <[ k5 := Some a5 ]> $ <[ k6 := Some a6 ]> $ <[ k7 := Some a7 ]> $ <[ k8 := Some a8 ]> $
    <[ k9 := Some a9 ]> $ <[ k10 := Some a10 ]> $ <[ k11 := Some a11 ]> $ <[ k12 := Some a12 ]> {[ k13 := Some a13 ]})
  (at level 1, format
                 "{[ '[hv' '[' k1  #  a1 ;  ']' '/' '[' k2  #  a2 ;  ']' '/' '[' k3  #  a3 ;  ']' '/' '[' k4  #  a4 ;  ']' '/' '[' k5  #  a5 ;  ']' '/' '[' k6  #  a6 ;  ']' '/' '[' k7  #  a7 ;  ']' '/' '[' k8  #  a8 ;  ']' '/' '[' k9  #  a9 ;  ']' '/' '[' k10  #  a10 ;  ']' '/' '[' k11  #  a11 ;  ']' '/' '[' k12  #  a12 ;  ']' '/' '[' k13  #  a13 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 # a1 ; k2 # a2 ; k3 # a3 ; k4 # a4 ; k5 # a5 ; k6 # a6 ; k7 # a7 ; k8 # a8 ; k9 # a9 ; k10 # a10 ; k11 # a11 ; k12 # a12 ; k13 # a13 ; k14 # a14 ]}" :=
  (<[ k1 := Some a1 ]> $ <[ k2 := Some a2 ]> $ <[ k3 := Some a3 ]> $ <[ k4 := Some a4 ]> $
    <[ k5 := Some a5 ]> $ <[ k6 := Some a6 ]> $ <[ k7 := Some a7 ]> $ <[ k8 := Some a8 ]> $
    <[ k9 := Some a9 ]> $ <[ k10 := Some a10 ]> $ <[ k11 := Some a11 ]> $ <[ k12 := Some a12 ]> $ <[ k13 := Some a13 ]> {[ k14 := Some a14 ]})
  (at level 1, format
                 "{[ '[hv' '[' k1  #  a1 ;  ']' '/' '[' k2  #  a2 ;  ']' '/' '[' k3  #  a3 ;  ']' '/' '[' k4  #  a4 ;  ']' '/' '[' k5  #  a5 ;  ']' '/' '[' k6  #  a6 ;  ']' '/' '[' k7  #  a7 ;  ']' '/' '[' k8  #  a8 ;  ']' '/' '[' k9  #  a9 ;  ']' '/' '[' k10  #  a10 ;  ']' '/' '[' k11  #  a11 ;  ']' '/' '[' k12  #  a12 ;  ']' '/' '[' k13  #  a13 ;  ']' '/' '[' k14  #  a14 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 # a1 ; k2 # a2 ; k3 # a3 ; k4 # a4 ; k5 # a5 ; k6 # a6 ; k7 # a7 ; k8 # a8 ; k9 # a9 ; k10 # a10 ; k11 # a11 ; k12 # a12 ; k13 # a13 ; k14 # a14 ; k15 # a15 ]}" :=
  (<[ k1 := Some a1 ]> $ <[ k2 := Some a2 ]> $ <[ k3 := Some a3 ]> $ <[ k4 := Some a4 ]> $
    <[ k5 := Some a5 ]> $ <[ k6 := Some a6 ]> $ <[ k7 := Some a7 ]> $ <[ k8 := Some a8 ]> $
    <[ k9 := Some a9 ]> $ <[ k10 := Some a10 ]> $ <[ k11 := Some a11 ]> $ <[ k12 := Some a12 ]> $ <[ k13 := Some a13 ]> $ <[ k14 := Some a14 ]> {[ k15 := Some a15 ]})
  (at level 1, format
                 "{[ '[hv' '[' k1  #  a1 ;  ']' '/' '[' k2  #  a2 ;  ']' '/' '[' k3  #  a3 ;  ']' '/' '[' k4  #  a4 ;  ']' '/' '[' k5  #  a5 ;  ']' '/' '[' k6  #  a6 ;  ']' '/' '[' k7  #  a7 ;  ']' '/' '[' k8  #  a8 ;  ']' '/' '[' k9  #  a9 ;  ']' '/' '[' k10  #  a10 ;  ']' '/' '[' k11  #  a11 ;  ']' '/' '[' k12  #  a12 ;  ']' '/' '[' k13  #  a13 ;  ']' '/' '[' k14  #  a14 ;  ']' '/' '[' k15  #  a15 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 # a1 ; k2 # a2 ; k3 # a3 ; k4 # a4 ; k5 # a5 ; k6 # a6 ; k7 # a7 ; k8 # a8 ; k9 # a9 ; k10 # a10 ; k11 # a11 ; k12 # a12 ; k13 # a13 ; k14 # a14 ; k15 # a15 ; k16 # a16 ]}" :=
  (<[ k1 := Some a1 ]> $ <[ k2 := Some a2 ]> $ <[ k3 := Some a3 ]> $ <[ k4 := Some a4 ]> $
    <[ k5 := Some a5 ]> $ <[ k6 := Some a6 ]> $ <[ k7 := Some a7 ]> $ <[ k8 := Some a8 ]> $
    <[ k9 := Some a9 ]> $ <[ k10 := Some a10 ]> $ <[ k11 := Some a11 ]> $ <[ k12 := Some a12 ]> $ <[ k13 := Some a13 ]> $ <[ k14 := Some a14 ]> $ <[ k15 := Some a15 ]> {[ k16 := Some a16 ]})
  (at level 1, format
                 "{[ '[hv' '[' k1  #  a1 ;  ']' '/' '[' k2  #  a2 ;  ']' '/' '[' k3  #  a3 ;  ']' '/' '[' k4  #  a4 ;  ']' '/' '[' k5  #  a5 ;  ']' '/' '[' k6  #  a6 ;  ']' '/' '[' k7  #  a7 ;  ']' '/' '[' k8  #  a8 ;  ']' '/' '[' k9  #  a9 ;  ']' '/' '[' k10  #  a10 ;  ']' '/' '[' k11  #  a11 ;  ']' '/' '[' k12  #  a12 ;  ']' '/' '[' k13  #  a13 ;  ']' '/' '[' k14  #  a14 ;  ']' '/' '[' k15  #  a15 ;  ']' '/' '[' k16  #  a16 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 # a1 ; k2 # a2 ; k3 # a3 ; k4 # a4 ; k5 # a5 ; k6 # a6 ; k7 # a7 ; k8 # a8 ; k9 # a9 ; k10 # a10 ; k11 # a11 ; k12 # a12 ; k13 # a13 ; k14 # a14 ; k15 # a15 ; k16 # a16 ; k17 # a17 ]}" :=
  (<[ k1 := Some a1 ]> $ <[ k2 := Some a2 ]> $ <[ k3 := Some a3 ]> $ <[ k4 := Some a4 ]> $
    <[ k5 := Some a5 ]> $ <[ k6 := Some a6 ]> $ <[ k7 := Some a7 ]> $ <[ k8 := Some a8 ]> $
    <[ k9 := Some a9 ]> $ <[ k10 := Some a10 ]> $ <[ k11 := Some a11 ]> $ <[ k12 := Some a12 ]> $ <[ k13 := Some a13 ]> $ <[ k14 := Some a14 ]> $ <[ k15 := Some a15 ]> $ <[ k16 := Some a16 ]> {[ k17 := Some a17 ]})
  (at level 1, format
                 "{[ '[hv' '[' k1  #  a1 ;  ']' '/' '[' k2  #  a2 ;  ']' '/' '[' k3  #  a3 ;  ']' '/' '[' k4  #  a4 ;  ']' '/' '[' k5  #  a5 ;  ']' '/' '[' k6  #  a6 ;  ']' '/' '[' k7  #  a7 ;  ']' '/' '[' k8  #  a8 ;  ']' '/' '[' k9  #  a9 ;  ']' '/' '[' k10  #  a10 ;  ']' '/' '[' k11  #  a11 ;  ']' '/' '[' k12  #  a12 ;  ']' '/' '[' k13  #  a13 ;  ']' '/' '[' k14  #  a14 ;  ']' '/' '[' k15  #  a15 ;  ']' '/' '[' k16  #  a16 ;  ']' '/' '[' k17  #  a17 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 # a1 ; k2 # a2 ; k3 # a3 ; k4 # a4 ; k5 # a5 ; k6 # a6 ; k7 # a7 ; k8 # a8 ; k9 # a9 ; k10 # a10 ; k11 # a11 ; k12 # a12 ; k13 # a13 ; k14 # a14 ; k15 # a15 ; k16 # a16 ; k17 # a17 ; k18 # a18 ]}" :=
  (<[ k1 := Some a1 ]> $ <[ k2 := Some a2 ]> $ <[ k3 := Some a3 ]> $ <[ k4 := Some a4 ]> $
    <[ k5 := Some a5 ]> $ <[ k6 := Some a6 ]> $ <[ k7 := Some a7 ]> $ <[ k8 := Some a8 ]> $
    <[ k9 := Some a9 ]> $ <[ k10 := Some a10 ]> $ <[ k11 := Some a11 ]> $ <[ k12 := Some a12 ]> $ <[ k13 := Some a13 ]> $ <[ k14 := Some a14 ]> $ <[ k15 := Some a15 ]> $ <[ k16 := Some a16 ]> $ <[ k17 := Some a17 ]> {[ k18 := Some a18 ]})
  (at level 1, format
                 "{[ '[hv' '[' k1  #  a1 ;  ']' '/' '[' k2  #  a2 ;  ']' '/' '[' k3  #  a3 ;  ']' '/' '[' k4  #  a4 ;  ']' '/' '[' k5  #  a5 ;  ']' '/' '[' k6  #  a6 ;  ']' '/' '[' k7  #  a7 ;  ']' '/' '[' k8  #  a8 ;  ']' '/' '[' k9  #  a9 ;  ']' '/' '[' k10  #  a10 ;  ']' '/' '[' k11  #  a11 ;  ']' '/' '[' k12  #  a12 ;  ']' '/' '[' k13  #  a13 ;  ']' '/' '[' k14  #  a14 ;  ']' '/' '[' k15  #  a15 ;  ']' '/' '[' k16  #  a16 ;  ']' '/' '[' k17  #  a17 ;  ']' '/' '[' k18  #  a18 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 # a1 ; k2 # a2 ; k3 # a3 ; k4 # a4 ; k5 # a5 ; k6 # a6 ; k7 # a7 ; k8 # a8 ; k9 # a9 ; k10 # a10 ; k11 # a11 ; k12 # a12 ; k13 # a13 ; k14 # a14 ; k15 # a15 ; k16 # a16 ; k17 # a17 ; k18 # a18 ; k19 # a19 ]}" :=
  (<[ k1 := Some a1 ]> $ <[ k2 := Some a2 ]> $ <[ k3 := Some a3 ]> $ <[ k4 := Some a4 ]> $
    <[ k5 := Some a5 ]> $ <[ k6 := Some a6 ]> $ <[ k7 := Some a7 ]> $ <[ k8 := Some a8 ]> $
    <[ k9 := Some a9 ]> $ <[ k10 := Some a10 ]> $ <[ k11 := Some a11 ]> $ <[ k12 := Some a12 ]> $ <[ k13 := Some a13 ]> $ <[ k14 := Some a14 ]> $ <[ k15 := Some a15 ]> $ <[ k16 := Some a16 ]> $ <[ k17 := Some a17 ]> $ <[ k18 := Some a18 ]> {[ k19 := Some a19 ]})
  (at level 1, format
                 "{[ '[hv' '[' k1  #  a1 ;  ']' '/' '[' k2  #  a2 ;  ']' '/' '[' k3  #  a3 ;  ']' '/' '[' k4  #  a4 ;  ']' '/' '[' k5  #  a5 ;  ']' '/' '[' k6  #  a6 ;  ']' '/' '[' k7  #  a7 ;  ']' '/' '[' k8  #  a8 ;  ']' '/' '[' k9  #  a9 ;  ']' '/' '[' k10  #  a10 ;  ']' '/' '[' k11  #  a11 ;  ']' '/' '[' k12  #  a12 ;  ']' '/' '[' k13  #  a13 ;  ']' '/' '[' k14  #  a14 ;  ']' '/' '[' k15  #  a15 ;  ']' '/' '[' k16  #  a16 ;  ']' '/' '[' k17  #  a17 ;  ']' '/' '[' k18  #  a18 ;  ']' '/' '[' k19  #  a19 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 # a1 ; k2 # a2 ; k3 # a3 ; k4 # a4 ; k5 # a5 ; k6 # a6 ; k7 # a7 ; k8 # a8 ; k9 # a9 ; k10 # a10 ; k11 # a11 ; k12 # a12 ; k13 # a13 ; k14 # a14 ; k15 # a15 ; k16 # a16 ; k17 # a17 ; k18 # a18 ; k19 # a19 ; k20 # a20 ]}" :=
  (<[ k1 := Some a1 ]> $ <[ k2 := Some a2 ]> $ <[ k3 := Some a3 ]> $ <[ k4 := Some a4 ]> $
    <[ k5 := Some a5 ]> $ <[ k6 := Some a6 ]> $ <[ k7 := Some a7 ]> $ <[ k8 := Some a8 ]> $
    <[ k9 := Some a9 ]> $ <[ k10 := Some a10 ]> $ <[ k11 := Some a11 ]> $ <[ k12 := Some a12 ]> $ <[ k13 := Some a13 ]> $ <[ k14 := Some a14 ]> $ <[ k15 := Some a15 ]> $ <[ k16 := Some a16 ]> $ <[ k17 := Some a17 ]> $ <[ k18 := Some a18 ]> $ <[ k19 := Some a19 ]> {[ k20 := Some a20 ]})
  (at level 1, format
                 "{[ '[hv' '[' k1  #  a1 ;  ']' '/' '[' k2  #  a2 ;  ']' '/' '[' k3  #  a3 ;  ']' '/' '[' k4  #  a4 ;  ']' '/' '[' k5  #  a5 ;  ']' '/' '[' k6  #  a6 ;  ']' '/' '[' k7  #  a7 ;  ']' '/' '[' k8  #  a8 ;  ']' '/' '[' k9  #  a9 ;  ']' '/' '[' k10  #  a10 ;  ']' '/' '[' k11  #  a11 ;  ']' '/' '[' k12  #  a12 ;  ']' '/' '[' k13  #  a13 ;  ']' '/' '[' k14  #  a14 ;  ']' '/' '[' k15  #  a15 ;  ']' '/' '[' k16  #  a16 ;  ']' '/' '[' k17  #  a17 ;  ']' '/' '[' k18  #  a18 ;  ']' '/' '[' k19  #  a19 ;  ']' '/' '[' k20  #  a20 ']' ']' ]}") : stdpp_scope.

(*** fspec_to_rel on RHS ***)

Notation "{[ k1 @ a1 ]}" := (singletonM (k1) (fspec_to_rel a1) : gmap fname fspec_rel)
  (at level 1, format
  "{[ k1  @  a1 ]}") : stdpp_scope.
Notation "{[ k1 @ a1 ; k2 @ a2 ]}" :=
  (<[ k1 := fspec_to_rel a1 ]> {[ k2 := fspec_to_rel a2 ]} : gmap fname fspec_rel)
  (at level 1, format
  "{[ '[hv' '[' k1  @  a1 ;  ']' '/' '[' k2  @  a2 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 @ a1 ; k2 @ a2 ; k3 @ a3 ]}" :=
  (<[ k1 := fspec_to_rel a1 ]> $ <[ k2 := fspec_to_rel a2 ]> {[ k3 := fspec_to_rel a3 ]} : gmap fname fspec_rel)
  (at level 1, format
  "{[ '[hv' '[' k1  @  a1 ;  ']' '/' '[' k2  @  a2 ;  ']' '/' '[' k3  @  a3 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 @ a1 ; k2 @ a2 ; k3 @ a3 ; k4 @ a4 ]}" :=
  (<[ k1 := fspec_to_rel a1 ]> $ <[ k2 := fspec_to_rel a2 ]> $ <[ k3 := fspec_to_rel a3 ]> {[ k4 := fspec_to_rel a4 ]} : gmap fname fspec_rel)
  (at level 1, format
  "{[ '[hv' '[' k1  @  a1 ;  ']' '/' '[' k2  @  a2 ;  ']' '/' '[' k3  @  a3 ;  ']' '/' '[' k4  @  a4 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 @ a1 ; k2 @ a2 ; k3 @ a3 ; k4 @ a4 ; k5 @ a5 ]}" :=
  (<[ k1 := fspec_to_rel a1 ]> $ <[ k2 := fspec_to_rel a2 ]> $ <[ k3 := fspec_to_rel a3 ]> $ <[ k4 := fspec_to_rel a4 ]> {[ k5 := fspec_to_rel a5 ]} : gmap fname fspec_rel)
  (at level 1, format
  "{[ '[hv' '[' k1  @  a1 ;  ']' '/' '[' k2  @  a2 ;  ']' '/' '[' k3  @  a3 ;  ']' '/' '[' k4  @  a4 ;  ']' '/' '[' k5  @  a5 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 @ a1 ; k2 @ a2 ; k3 @ a3 ; k4 @ a4 ; k5 @ a5 ; k6 @ a6 ]}" :=
  (<[ k1 := fspec_to_rel a1 ]> $ <[ k2 := fspec_to_rel a2 ]> $ <[ k3 := fspec_to_rel a3 ]> $ <[ k4 := fspec_to_rel a4 ]> $
    <[ k5 := fspec_to_rel a5 ]> {[ k6 := fspec_to_rel a6 ]} : gmap fname fspec_rel)
  (at level 1, format
  "{[ '[hv' '[' k1  @  a1 ;  ']' '/' '[' k2  @  a2 ;  ']' '/' '[' k3  @  a3 ;  ']' '/' '[' k4  @  a4 ;  ']' '/' '[' k5  @  a5 ;  ']' '/' '[' k6  @  a6 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 @ a1 ; k2 @ a2 ; k3 @ a3 ; k4 @ a4 ; k5 @ a5 ; k6 @ a6 ; k7 @ a7 ]}" :=
  (<[ k1 := fspec_to_rel a1 ]> $ <[ k2 := fspec_to_rel a2 ]> $ <[ k3 := fspec_to_rel a3 ]> $ <[ k4 := fspec_to_rel a4 ]> $
    <[ k5 := fspec_to_rel a5 ]> $ <[ k6 := fspec_to_rel a6 ]> {[ k7 := fspec_to_rel a7 ]} : gmap fname fspec_rel)
  (at level 1, format
  "{[ '[hv' '[' k1  @  a1 ;  ']' '/' '[' k2  @  a2 ;  ']' '/' '[' k3  @  a3 ;  ']' '/' '[' k4  @  a4 ;  ']' '/' '[' k5  @  a5 ;  ']' '/' '[' k6  @  a6 ;  ']' '/' '[' k7  @  a7 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 @ a1 ; k2 @ a2 ; k3 @ a3 ; k4 @ a4 ; k5 @ a5 ; k6 @ a6 ; k7 @ a7 ; k8 @ a8 ]}" :=
  (<[ k1 := fspec_to_rel a1 ]> $ <[ k2 := fspec_to_rel a2 ]> $ <[ k3 := fspec_to_rel a3 ]> $ <[ k4 := fspec_to_rel a4 ]> $
    <[ k5 := fspec_to_rel a5 ]> $ <[ k6 := fspec_to_rel a6 ]> $ <[ k7 := fspec_to_rel a7 ]> {[ k8 := fspec_to_rel a8 ]} : gmap fname fspec_rel)
  (at level 1, format
  "{[ '[hv' '[' k1  @  a1 ;  ']' '/' '[' k2  @  a2 ;  ']' '/' '[' k3  @  a3 ;  ']' '/' '[' k4  @  a4 ;  ']' '/' '[' k5  @  a5 ;  ']' '/' '[' k6  @  a6 ;  ']' '/' '[' k7  @  a7 ;  ']' '/' '[' k8  @  a8 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 @ a1 ; k2 @ a2 ; k3 @ a3 ; k4 @ a4 ; k5 @ a5 ; k6 @ a6 ; k7 @ a7 ; k8 @ a8 ; k9 @ a9 ]}" :=
  (<[ k1 := fspec_to_rel a1 ]> $ <[ k2 := fspec_to_rel a2 ]> $ <[ k3 := fspec_to_rel a3 ]> $ <[ k4 := fspec_to_rel a4 ]> $
    <[ k5 := fspec_to_rel a5 ]> $ <[ k6 := fspec_to_rel a6 ]> $ <[ k7 := fspec_to_rel a7 ]> $ <[ k8 := fspec_to_rel a8 ]> {[ k9 := fspec_to_rel a9 ]} : gmap fname fspec_rel)
  (at level 1, format
  "{[ '[hv' '[' k1  @  a1 ;  ']' '/' '[' k2  @  a2 ;  ']' '/' '[' k3  @  a3 ;  ']' '/' '[' k4  @  a4 ;  ']' '/' '[' k5  @  a5 ;  ']' '/' '[' k6  @  a6 ;  ']' '/' '[' k7  @  a7 ;  ']' '/' '[' k8  @  a8 ;  ']' '/' '[' k9  @  a9 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 @ a1 ; k2 @ a2 ; k3 @ a3 ; k4 @ a4 ; k5 @ a5 ; k6 @ a6 ; k7 @ a7 ; k8 @ a8 ; k9 @ a9 ; k10 @ a10 ]}" :=
  (<[ k1 := fspec_to_rel a1 ]> $ <[ k2 := fspec_to_rel a2 ]> $ <[ k3 := fspec_to_rel a3 ]> $ <[ k4 := fspec_to_rel a4 ]> $
    <[ k5 := fspec_to_rel a5 ]> $ <[ k6 := fspec_to_rel a6 ]> $ <[ k7 := fspec_to_rel a7 ]> $ <[ k8 := fspec_to_rel a8 ]> $
    <[ k9 := fspec_to_rel a9 ]> {[ k10 := fspec_to_rel a10 ]} : gmap fname fspec_rel)
  (at level 1, format
  "{[ '[hv' '[' k1  @  a1 ;  ']' '/' '[' k2  @  a2 ;  ']' '/' '[' k3  @  a3 ;  ']' '/' '[' k4  @  a4 ;  ']' '/' '[' k5  @  a5 ;  ']' '/' '[' k6  @  a6 ;  ']' '/' '[' k7  @  a7 ;  ']' '/' '[' k8  @  a8 ;  ']' '/' '[' k9  @  a9 ;  ']' '/' '[' k10  @  a10 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 @ a1 ; k2 @ a2 ; k3 @ a3 ; k4 @ a4 ; k5 @ a5 ; k6 @ a6 ; k7 @ a7 ; k8 @ a8 ; k9 @ a9 ; k10 @ a10 ; k11 @ a11 ]}" :=
  (<[ k1 := fspec_to_rel a1 ]> $ <[ k2 := fspec_to_rel a2 ]> $ <[ k3 := fspec_to_rel a3 ]> $ <[ k4 := fspec_to_rel a4 ]> $
    <[ k5 := fspec_to_rel a5 ]> $ <[ k6 := fspec_to_rel a6 ]> $ <[ k7 := fspec_to_rel a7 ]> $ <[ k8 := fspec_to_rel a8 ]> $
    <[ k9 := fspec_to_rel a9 ]> $ <[ k10 := fspec_to_rel a10 ]> {[ k11 := fspec_to_rel a11 ]} : gmap fname fspec_rel)
  (at level 1, format
  "{[ '[hv' '[' k1  @  a1 ;  ']' '/' '[' k2  @  a2 ;  ']' '/' '[' k3  @  a3 ;  ']' '/' '[' k4  @  a4 ;  ']' '/' '[' k5  @  a5 ;  ']' '/' '[' k6  @  a6 ;  ']' '/' '[' k7  @  a7 ;  ']' '/' '[' k8  @  a8 ;  ']' '/' '[' k9  @  a9 ;  ']' '/' '[' k10  @  a10 ;  ']' '/' '[' k11  @  a11 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 @ a1 ; k2 @ a2 ; k3 @ a3 ; k4 @ a4 ; k5 @ a5 ; k6 @ a6 ; k7 @ a7 ; k8 @ a8 ; k9 @ a9 ; k10 @ a10 ; k11 @ a11 ; k12 @ a12 ]}" :=
  (<[ k1 := fspec_to_rel a1 ]> $ <[ k2 := fspec_to_rel a2 ]> $ <[ k3 := fspec_to_rel a3 ]> $ <[ k4 := fspec_to_rel a4 ]> $
    <[ k5 := fspec_to_rel a5 ]> $ <[ k6 := fspec_to_rel a6 ]> $ <[ k7 := fspec_to_rel a7 ]> $ <[ k8 := fspec_to_rel a8 ]> $
    <[ k9 := fspec_to_rel a9 ]> $ <[ k10 := fspec_to_rel a10 ]> $ <[ k11 := fspec_to_rel a11 ]> {[ k12 := fspec_to_rel a12 ]} : gmap fname fspec_rel)
  (at level 1, format
  "{[ '[hv' '[' k1  @  a1 ;  ']' '/' '[' k2  @  a2 ;  ']' '/' '[' k3  @  a3 ;  ']' '/' '[' k4  @  a4 ;  ']' '/' '[' k5  @  a5 ;  ']' '/' '[' k6  @  a6 ;  ']' '/' '[' k7  @  a7 ;  ']' '/' '[' k8  @  a8 ;  ']' '/' '[' k9  @  a9 ;  ']' '/' '[' k10  @  a10 ;  ']' '/' '[' k11  @  a11 ;  ']' '/' '[' k12  @  a12 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 @ a1 ; k2 @ a2 ; k3 @ a3 ; k4 @ a4 ; k5 @ a5 ; k6 @ a6 ; k7 @ a7 ; k8 @ a8 ; k9 @ a9 ; k10 @ a10 ; k11 @ a11 ; k12 @ a12 ; k13 @ a13 ]}" :=
  (<[ k1 := fspec_to_rel a1 ]> $ <[ k2 := fspec_to_rel a2 ]> $ <[ k3 := fspec_to_rel a3 ]> $ <[ k4 := fspec_to_rel a4 ]> $
    <[ k5 := fspec_to_rel a5 ]> $ <[ k6 := fspec_to_rel a6 ]> $ <[ k7 := fspec_to_rel a7 ]> $ <[ k8 := fspec_to_rel a8 ]> $
    <[ k9 := fspec_to_rel a9 ]> $ <[ k10 := fspec_to_rel a10 ]> $ <[ k11 := fspec_to_rel a11 ]> $ <[ k12 := fspec_to_rel a12 ]> {[ k13 := fspec_to_rel a13 ]} : gmap fname fspec_rel)
  (at level 1, format
                 "{[ '[hv' '[' k1  @  a1 ;  ']' '/' '[' k2  @  a2 ;  ']' '/' '[' k3  @  a3 ;  ']' '/' '[' k4  @  a4 ;  ']' '/' '[' k5  @  a5 ;  ']' '/' '[' k6  @  a6 ;  ']' '/' '[' k7  @  a7 ;  ']' '/' '[' k8  @  a8 ;  ']' '/' '[' k9  @  a9 ;  ']' '/' '[' k10  @  a10 ;  ']' '/' '[' k11  @  a11 ;  ']' '/' '[' k12  @  a12 ;  ']' '/' '[' k13  @  a13 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 @ a1 ; k2 @ a2 ; k3 @ a3 ; k4 @ a4 ; k5 @ a5 ; k6 @ a6 ; k7 @ a7 ; k8 @ a8 ; k9 @ a9 ; k10 @ a10 ; k11 @ a11 ; k12 @ a12 ; k13 @ a13 ; k14 @ a14 ]}" :=
  (<[ k1 := fspec_to_rel a1 ]> $ <[ k2 := fspec_to_rel a2 ]> $ <[ k3 := fspec_to_rel a3 ]> $ <[ k4 := fspec_to_rel a4 ]> $
    <[ k5 := fspec_to_rel a5 ]> $ <[ k6 := fspec_to_rel a6 ]> $ <[ k7 := fspec_to_rel a7 ]> $ <[ k8 := fspec_to_rel a8 ]> $
    <[ k9 := fspec_to_rel a9 ]> $ <[ k10 := fspec_to_rel a10 ]> $ <[ k11 := fspec_to_rel a11 ]> $ <[ k12 := fspec_to_rel a12 ]> $ <[ k13 := fspec_to_rel a13 ]> {[ k14 := fspec_to_rel a14 ]} : gmap fname fspec_rel)
  (at level 1, format
                 "{[ '[hv' '[' k1  @  a1 ;  ']' '/' '[' k2  @  a2 ;  ']' '/' '[' k3  @  a3 ;  ']' '/' '[' k4  @  a4 ;  ']' '/' '[' k5  @  a5 ;  ']' '/' '[' k6  @  a6 ;  ']' '/' '[' k7  @  a7 ;  ']' '/' '[' k8  @  a8 ;  ']' '/' '[' k9  @  a9 ;  ']' '/' '[' k10  @  a10 ;  ']' '/' '[' k11  @  a11 ;  ']' '/' '[' k12  @  a12 ;  ']' '/' '[' k13  @  a13 ;  ']' '/' '[' k14  @  a14 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 @ a1 ; k2 @ a2 ; k3 @ a3 ; k4 @ a4 ; k5 @ a5 ; k6 @ a6 ; k7 @ a7 ; k8 @ a8 ; k9 @ a9 ; k10 @ a10 ; k11 @ a11 ; k12 @ a12 ; k13 @ a13 ; k14 @ a14 ; k15 @ a15 ]}" :=
  (<[ k1 := fspec_to_rel a1 ]> $ <[ k2 := fspec_to_rel a2 ]> $ <[ k3 := fspec_to_rel a3 ]> $ <[ k4 := fspec_to_rel a4 ]> $
    <[ k5 := fspec_to_rel a5 ]> $ <[ k6 := fspec_to_rel a6 ]> $ <[ k7 := fspec_to_rel a7 ]> $ <[ k8 := fspec_to_rel a8 ]> $
    <[ k9 := fspec_to_rel a9 ]> $ <[ k10 := fspec_to_rel a10 ]> $ <[ k11 := fspec_to_rel a11 ]> $ <[ k12 := fspec_to_rel a12 ]> $ <[ k13 := fspec_to_rel a13 ]> $ <[ k14 := fspec_to_rel a14 ]> {[ k15 := fspec_to_rel a15 ]} : gmap fname fspec_rel)
  (at level 1, format
                 "{[ '[hv' '[' k1  @  a1 ;  ']' '/' '[' k2  @  a2 ;  ']' '/' '[' k3  @  a3 ;  ']' '/' '[' k4  @  a4 ;  ']' '/' '[' k5  @  a5 ;  ']' '/' '[' k6  @  a6 ;  ']' '/' '[' k7  @  a7 ;  ']' '/' '[' k8  @  a8 ;  ']' '/' '[' k9  @  a9 ;  ']' '/' '[' k10  @  a10 ;  ']' '/' '[' k11  @  a11 ;  ']' '/' '[' k12  @  a12 ;  ']' '/' '[' k13  @  a13 ;  ']' '/' '[' k14  @  a14 ;  ']' '/' '[' k15  @  a15 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 @ a1 ; k2 @ a2 ; k3 @ a3 ; k4 @ a4 ; k5 @ a5 ; k6 @ a6 ; k7 @ a7 ; k8 @ a8 ; k9 @ a9 ; k10 @ a10 ; k11 @ a11 ; k12 @ a12 ; k13 @ a13 ; k14 @ a14 ; k15 @ a15 ; k16 @ a16 ]}" :=
  (<[ k1 := fspec_to_rel a1 ]> $ <[ k2 := fspec_to_rel a2 ]> $ <[ k3 := fspec_to_rel a3 ]> $ <[ k4 := fspec_to_rel a4 ]> $
    <[ k5 := fspec_to_rel a5 ]> $ <[ k6 := fspec_to_rel a6 ]> $ <[ k7 := fspec_to_rel a7 ]> $ <[ k8 := fspec_to_rel a8 ]> $
    <[ k9 := fspec_to_rel a9 ]> $ <[ k10 := fspec_to_rel a10 ]> $ <[ k11 := fspec_to_rel a11 ]> $ <[ k12 := fspec_to_rel a12 ]> $ <[ k13 := fspec_to_rel a13 ]> $ <[ k14 := fspec_to_rel a14 ]> $ <[ k15 := fspec_to_rel a15 ]> {[ k16 := fspec_to_rel a16 ]} : gmap fname fspec_rel)
  (at level 1, format
                 "{[ '[hv' '[' k1  @  a1 ;  ']' '/' '[' k2  @  a2 ;  ']' '/' '[' k3  @  a3 ;  ']' '/' '[' k4  @  a4 ;  ']' '/' '[' k5  @  a5 ;  ']' '/' '[' k6  @  a6 ;  ']' '/' '[' k7  @  a7 ;  ']' '/' '[' k8  @  a8 ;  ']' '/' '[' k9  @  a9 ;  ']' '/' '[' k10  @  a10 ;  ']' '/' '[' k11  @  a11 ;  ']' '/' '[' k12  @  a12 ;  ']' '/' '[' k13  @  a13 ;  ']' '/' '[' k14  @  a14 ;  ']' '/' '[' k15  @  a15 ;  ']' '/' '[' k16  @  a16 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 @ a1 ; k2 @ a2 ; k3 @ a3 ; k4 @ a4 ; k5 @ a5 ; k6 @ a6 ; k7 @ a7 ; k8 @ a8 ; k9 @ a9 ; k10 @ a10 ; k11 @ a11 ; k12 @ a12 ; k13 @ a13 ; k14 @ a14 ; k15 @ a15 ; k16 @ a16 ; k17 @ a17 ]}" :=
  (<[ k1 := fspec_to_rel a1 ]> $ <[ k2 := fspec_to_rel a2 ]> $ <[ k3 := fspec_to_rel a3 ]> $ <[ k4 := fspec_to_rel a4 ]> $
    <[ k5 := fspec_to_rel a5 ]> $ <[ k6 := fspec_to_rel a6 ]> $ <[ k7 := fspec_to_rel a7 ]> $ <[ k8 := fspec_to_rel a8 ]> $
    <[ k9 := fspec_to_rel a9 ]> $ <[ k10 := fspec_to_rel a10 ]> $ <[ k11 := fspec_to_rel a11 ]> $ <[ k12 := fspec_to_rel a12 ]> $ <[ k13 := fspec_to_rel a13 ]> $ <[ k14 := fspec_to_rel a14 ]> $ <[ k15 := fspec_to_rel a15 ]> $ <[ k16 := fspec_to_rel a16 ]> {[ k17 := fspec_to_rel a17 ]} : gmap fname fspec_rel)
  (at level 1, format
                 "{[ '[hv' '[' k1  @  a1 ;  ']' '/' '[' k2  @  a2 ;  ']' '/' '[' k3  @  a3 ;  ']' '/' '[' k4  @  a4 ;  ']' '/' '[' k5  @  a5 ;  ']' '/' '[' k6  @  a6 ;  ']' '/' '[' k7  @  a7 ;  ']' '/' '[' k8  @  a8 ;  ']' '/' '[' k9  @  a9 ;  ']' '/' '[' k10  @  a10 ;  ']' '/' '[' k11  @  a11 ;  ']' '/' '[' k12  @  a12 ;  ']' '/' '[' k13  @  a13 ;  ']' '/' '[' k14  @  a14 ;  ']' '/' '[' k15  @  a15 ;  ']' '/' '[' k16  @  a16 ;  ']' '/' '[' k17  @  a17 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 @ a1 ; k2 @ a2 ; k3 @ a3 ; k4 @ a4 ; k5 @ a5 ; k6 @ a6 ; k7 @ a7 ; k8 @ a8 ; k9 @ a9 ; k10 @ a10 ; k11 @ a11 ; k12 @ a12 ; k13 @ a13 ; k14 @ a14 ; k15 @ a15 ; k16 @ a16 ; k17 @ a17 ; k18 @ a18 ]}" :=
  (<[ k1 := fspec_to_rel a1 ]> $ <[ k2 := fspec_to_rel a2 ]> $ <[ k3 := fspec_to_rel a3 ]> $ <[ k4 := fspec_to_rel a4 ]> $
    <[ k5 := fspec_to_rel a5 ]> $ <[ k6 := fspec_to_rel a6 ]> $ <[ k7 := fspec_to_rel a7 ]> $ <[ k8 := fspec_to_rel a8 ]> $
    <[ k9 := fspec_to_rel a9 ]> $ <[ k10 := fspec_to_rel a10 ]> $ <[ k11 := fspec_to_rel a11 ]> $ <[ k12 := fspec_to_rel a12 ]> $ <[ k13 := fspec_to_rel a13 ]> $ <[ k14 := fspec_to_rel a14 ]> $ <[ k15 := fspec_to_rel a15 ]> $ <[ k16 := fspec_to_rel a16 ]> $ <[ k17 := fspec_to_rel a17 ]> {[ k18 := fspec_to_rel a18 ]} : gmap fname fspec_rel)
  (at level 1, format
                 "{[ '[hv' '[' k1  @  a1 ;  ']' '/' '[' k2  @  a2 ;  ']' '/' '[' k3  @  a3 ;  ']' '/' '[' k4  @  a4 ;  ']' '/' '[' k5  @  a5 ;  ']' '/' '[' k6  @  a6 ;  ']' '/' '[' k7  @  a7 ;  ']' '/' '[' k8  @  a8 ;  ']' '/' '[' k9  @  a9 ;  ']' '/' '[' k10  @  a10 ;  ']' '/' '[' k11  @  a11 ;  ']' '/' '[' k12  @  a12 ;  ']' '/' '[' k13  @  a13 ;  ']' '/' '[' k14  @  a14 ;  ']' '/' '[' k15  @  a15 ;  ']' '/' '[' k16  @  a16 ;  ']' '/' '[' k17  @  a17 ;  ']' '/' '[' k18  @  a18 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 @ a1 ; k2 @ a2 ; k3 @ a3 ; k4 @ a4 ; k5 @ a5 ; k6 @ a6 ; k7 @ a7 ; k8 @ a8 ; k9 @ a9 ; k10 @ a10 ; k11 @ a11 ; k12 @ a12 ; k13 @ a13 ; k14 @ a14 ; k15 @ a15 ; k16 @ a16 ; k17 @ a17 ; k18 @ a18 ; k19 @ a19 ]}" :=
  (<[ k1 := fspec_to_rel a1 ]> $ <[ k2 := fspec_to_rel a2 ]> $ <[ k3 := fspec_to_rel a3 ]> $ <[ k4 := fspec_to_rel a4 ]> $
    <[ k5 := fspec_to_rel a5 ]> $ <[ k6 := fspec_to_rel a6 ]> $ <[ k7 := fspec_to_rel a7 ]> $ <[ k8 := fspec_to_rel a8 ]> $
    <[ k9 := fspec_to_rel a9 ]> $ <[ k10 := fspec_to_rel a10 ]> $ <[ k11 := fspec_to_rel a11 ]> $ <[ k12 := fspec_to_rel a12 ]> $ <[ k13 := fspec_to_rel a13 ]> $ <[ k14 := fspec_to_rel a14 ]> $ <[ k15 := fspec_to_rel a15 ]> $ <[ k16 := fspec_to_rel a16 ]> $ <[ k17 := fspec_to_rel a17 ]> $ <[ k18 := fspec_to_rel a18 ]> {[ k19 := fspec_to_rel a19 ]} : gmap fname fspec_rel)
  (at level 1, format
                 "{[ '[hv' '[' k1  @  a1 ;  ']' '/' '[' k2  @  a2 ;  ']' '/' '[' k3  @  a3 ;  ']' '/' '[' k4  @  a4 ;  ']' '/' '[' k5  @  a5 ;  ']' '/' '[' k6  @  a6 ;  ']' '/' '[' k7  @  a7 ;  ']' '/' '[' k8  @  a8 ;  ']' '/' '[' k9  @  a9 ;  ']' '/' '[' k10  @  a10 ;  ']' '/' '[' k11  @  a11 ;  ']' '/' '[' k12  @  a12 ;  ']' '/' '[' k13  @  a13 ;  ']' '/' '[' k14  @  a14 ;  ']' '/' '[' k15  @  a15 ;  ']' '/' '[' k16  @  a16 ;  ']' '/' '[' k17  @  a17 ;  ']' '/' '[' k18  @  a18 ;  ']' '/' '[' k19  @  a19 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 @ a1 ; k2 @ a2 ; k3 @ a3 ; k4 @ a4 ; k5 @ a5 ; k6 @ a6 ; k7 @ a7 ; k8 @ a8 ; k9 @ a9 ; k10 @ a10 ; k11 @ a11 ; k12 @ a12 ; k13 @ a13 ; k14 @ a14 ; k15 @ a15 ; k16 @ a16 ; k17 @ a17 ; k18 @ a18 ; k19 @ a19 ; k20 @ a20 ]}" :=
  (<[ k1 := fspec_to_rel a1 ]> $ <[ k2 := fspec_to_rel a2 ]> $ <[ k3 := fspec_to_rel a3 ]> $ <[ k4 := fspec_to_rel a4 ]> $
    <[ k5 := fspec_to_rel a5 ]> $ <[ k6 := fspec_to_rel a6 ]> $ <[ k7 := fspec_to_rel a7 ]> $ <[ k8 := fspec_to_rel a8 ]> $
    <[ k9 := fspec_to_rel a9 ]> $ <[ k10 := fspec_to_rel a10 ]> $ <[ k11 := fspec_to_rel a11 ]> $ <[ k12 := fspec_to_rel a12 ]> $ <[ k13 := fspec_to_rel a13 ]> $ <[ k14 := fspec_to_rel a14 ]> $ <[ k15 := fspec_to_rel a15 ]> $ <[ k16 := fspec_to_rel a16 ]> $ <[ k17 := fspec_to_rel a17 ]> $ <[ k18 := fspec_to_rel a18 ]> $ <[ k19 := fspec_to_rel a19 ]> {[ k20 := fspec_to_rel a20 ]} : gmap fname fspec_rel)
  (at level 1, format
                 "{[ '[hv' '[' k1  @  a1 ;  ']' '/' '[' k2  @  a2 ;  ']' '/' '[' k3  @  a3 ;  ']' '/' '[' k4  @  a4 ;  ']' '/' '[' k5  @  a5 ;  ']' '/' '[' k6  @  a6 ;  ']' '/' '[' k7  @  a7 ;  ']' '/' '[' k8  @  a8 ;  ']' '/' '[' k9  @  a9 ;  ']' '/' '[' k10  @  a10 ;  ']' '/' '[' k11  @  a11 ;  ']' '/' '[' k12  @  a12 ;  ']' '/' '[' k13  @  a13 ;  ']' '/' '[' k14  @  a14 ;  ']' '/' '[' k15  @  a15 ;  ']' '/' '[' k16  @  a16 ;  ']' '/' '[' k17  @  a17 ;  ']' '/' '[' k18  @  a18 ;  ']' '/' '[' k19  @  a19 ;  ']' '/' '[' k20  @  a20 ']' ']' ]}") : stdpp_scope.
