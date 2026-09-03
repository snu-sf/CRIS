From CRIS.common Require Import Common.
From iris.algebra Require Import auth excl functions reservation_map.
From iris.proofmode Require Import proofmode.
From stdpp Require Import coPset.

Definition stateV : cmra := exclR (leibnizO Any.t).

Definition stateF : ucmra :=
  string -d> reservation_mapUR stateV.

Definition stateR : ucmra := authUR stateF.

Definition state_key_encode (k : key) : positive := encode k.

#[local] Instance state_key_encode_inj :
    Inj (=) (=) state_key_encode.
Proof. intros x y. apply encode_inj. Qed.

Definition stateΣ : GRA := #[stateR].

Global Instance subG_stateΣ Σ : subG stateΣ Σ → inG stateR Σ.
Proof. solve_inG. Qed.

Class stateGpreS (Σ : GRA) :=
  { #[local] stateGpreS_inG :: inG stateR Σ
  }.

Global Instance subG_stateGpreS Σ : subG stateΣ Σ → stateGpreS Σ.
Proof. solve_inG. Qed.

Class stateGS (Σ : GRA) :=
  { stateGS_stateGpreS : stateGpreS Σ
  ; name_tgt : gname
  ; name_src : gname
  }.

Local Existing Instances stateGS_stateGpreS stateGpreS_inG.

Section DEFINITIONS.

  Context `{!stateGS Σ}.

  Definition state_data (k : key) (v : Any.t) : stateF :=
    discrete_fun_singleton (scope k)
      (reservation_map_data (A := stateV) (state_key_encode k) (Excl v)).

  Definition state_token (scp : string) (E : coPset) : stateF :=
    discrete_fun_singleton scp (reservation_map_token (A := stateV) E).

  Definition points_to_tgt (k : key) (v : Any.t) : iProp Σ :=
    own name_tgt (◯ state_data k v).

  Definition points_to_src (k : key) (v : Any.t) : iProp Σ :=
    own name_src (◯ state_data k v).

  Definition uninit_tgt_scope (scp : string) (E : coPset) : iProp Σ :=
    own name_tgt (◯ state_token scp E).

  Definition uninit_src_scope (scp : string) (E : coPset) : iProp Σ :=
    own name_src (◯ state_token scp E).

  Definition uninit_tgt (k : key) : iProp Σ :=
    uninit_tgt_scope (scope k) {[ state_key_encode k ]}.

  Definition uninit_src (k : key) : iProp Σ :=
    uninit_src_scope (scope k) {[ state_key_encode k ]}.

  Definition state_cell_tgt (k : key) (ov : option Any.t) : iProp Σ :=
    match ov with
    | Some v => points_to_tgt k v
    | None => uninit_tgt k
    end.

  Definition state_cell_src (k : key) (ov : option Any.t) : iProp Σ :=
    match ov with
    | Some v => points_to_src k v
    | None => uninit_src k
    end.

  Definition live_state (m : gmap key (option Any.t)) : gmap key Any.t :=
    omap id m.

  Definition state_slice (S : gset string)
      (m : gmap key (option Any.t)) : gmap key Any.t :=
    filter (fun kv : key * Any.t => scope kv.1 ∈ S) (live_state m).

  Definition state_entries (scp : string)
      (m : gmap key (option Any.t)) : gmap key Any.t :=
    filter (fun kv : key * Any.t => scope kv.1 = scp) (live_state m).

  Definition state_values (scp : string)
      (m : gmap key (option Any.t)) : gmap positive stateV :=
    kmap state_key_encode (Excl <$> state_entries scp m).

  Definition state_fields (scp : string)
      (m : gmap key (option Any.t)) : gset positive :=
    dom (state_values scp m).

  Definition state_uninit_set (scp : string)
      (m : gmap key (option Any.t)) : coPset :=
    ⊤ ∖ gset_to_coPset (state_fields scp m).

  Definition state_present (m : gmap key (option Any.t)) : stateF :=
    fun scp =>
      ReservationMap (state_values scp m)
        (CoPset (state_uninit_set scp m)).

  Definition state_absent (S : gset string)
      (m : gmap key (option Any.t)) : stateF :=
    fun scp =>
      if decide (scp ∈ S)
      then reservation_map_token (A := stateV) (state_uninit_set scp m)
      else ε.

  Definition state_points (S : gset string)
      (m : gmap key (option Any.t)) : stateF :=
    [^op map] k ↦ v ∈ state_slice S m, state_data k v.

  Definition state_fragment (S : gset string)
      (m : gmap key (option Any.t)) : stateF :=
    fun scp =>
      if decide (scp ∈ S) then state_present m scp else ε.

  Definition state_fragment_rest (S : gset string)
      (m : gmap key (option Any.t)) : stateF :=
    fun scp =>
      if decide (scp ∈ S) then ε else state_present m scp.

  Definition SI_tgt (m : gmap key (option Any.t)) : iProp Σ :=
    own name_tgt (● state_present m).

  Definition SI_src (m : gmap key (option Any.t)) : iProp Σ :=
    own name_src (● state_present m).

End DEFINITIONS.

Definition state_init_tgt {Σ : GRA} (S : gset string)
    (m : gmap key (option Any.t)) (STATE : stateGS Σ) : iProp Σ :=
  let _ : stateGS Σ := STATE in
  ([∗ map] k ↦ v ∈ state_slice S m, points_to_tgt k v) ∗
  own name_tgt (◯ state_absent S m).

Definition state_init_src {Σ : GRA} (S : gset string)
    (m : gmap key (option Any.t)) (STATE : stateGS Σ) : iProp Σ :=
  let _ : stateGS Σ := STATE in
  ([∗ map] k ↦ v ∈ state_slice S m, points_to_src k v) ∗
  own name_src (◯ state_absent S m).

Definition set_state_cell (k : key) (ov : option Any.t)
    (m : gmap key (option Any.t)) : gmap key (option Any.t) :=
  match ov with
  | Some v => <[k := Some v]> m
  | None => delete k m
  end.

Definition state_cell_transition (ov ov' : option Any.t) : Prop :=
  ov' = ov ∨ is_Some ov'.

Section BASIC_LEMMAS.

  Context `{!stateGS Σ}.

  #[local] Instance stateF_lookup_op_homomorphism scp :
      MonoidHomomorphism op op (≡)
        (fun f : stateF => f scp).
  Proof.
    split; [split|]; try apply _.
    - intros n f g EQ. exact (EQ scp).
    - intros f g. by rewrite discrete_fun_lookup_op.
    - done.
  Qed.

  Lemma live_state_lookup m k :
    live_state m !! k = mjoin (m !! k).
  Proof.
    rewrite /live_state lookup_omap.
    by destruct (m !! k) as [[v|]|].
  Qed.

  Lemma state_slice_lookup S m k :
    state_slice S m !! k =
      if decide (scope k ∈ S) then mjoin (m !! k) else None.
  Proof.
    rewrite /state_slice map_lookup_filter live_state_lookup.
    destruct (decide (scope k ∈ S)) as [IN|NIN].
    - destruct (mjoin (m !! k)); simpl; by repeat case_guard.
    - destruct (mjoin (m !! k)); simpl; by repeat case_guard.
  Qed.

  Lemma state_slice_lookup_in S m k (IN : scope k ∈ S) :
    state_slice S m !! k = mjoin (m !! k).
  Proof. rewrite state_slice_lookup. by case_decide. Qed.

  Lemma state_slice_lookup_notin S m k (NIN : scope k ∉ S) :
    state_slice S m !! k = None.
  Proof. rewrite state_slice_lookup. by case_decide. Qed.

  Lemma state_data_lookup k v scp :
    state_data k v scp =
      if decide (scope k = scp)
      then reservation_map_data (A := stateV)
        (state_key_encode k) (Excl v)
      else ε.
  Proof.
    rewrite /state_data.
    destruct (decide (scope k = scp)) as [EQ|NEQ].
    - subst scp. by rewrite discrete_fun_lookup_singleton.
    - by rewrite discrete_fun_lookup_singleton_ne.
  Qed.

  Lemma state_slice_insert S m k v (IN : scope k ∈ S) :
    state_slice S (<[k := Some v]> m) = <[k := v]> (state_slice S m).
  Proof.
    rewrite /state_slice /live_state (omap_insert_Some id m k (Some v) v) //.
    apply map_filter_insert_True. done.
  Qed.

  Lemma state_slice_delete S m k :
    state_slice S (delete k m) = delete k (state_slice S m).
  Proof.
    rewrite /state_slice /live_state omap_delete.
    rewrite map_filter_delete. done.
  Qed.

  Lemma state_slice_set_state_cell_eq S m1 m2 k ov
      (IN : scope k ∈ S)
      (EQ : state_slice S m1 = state_slice S m2) :
    state_slice S (set_state_cell k ov m1) =
      state_slice S (set_state_cell k ov m2).
  Proof.
    destruct ov as [v|]; simpl.
    - rewrite (state_slice_insert S m1 k v IN)
        (state_slice_insert S m2 k v IN) EQ //.
    - rewrite !state_slice_delete EQ //.
  Qed.

  Lemma state_slice_union S1 S2 m :
    state_slice (S1 ∪ S2) m = state_slice S1 m ∪ state_slice S2 m.
  Proof.
    rewrite /state_slice -map_filter_or -map_filter_ext.
    intros [scp field] v LOOK. simpl. set_solver.
  Qed.

  Lemma state_slice_disjoint S1 S2 m (DISJ : S1 ## S2) :
    state_slice S1 m ##ₘ state_slice S2 m.
  Proof.
    apply elem_of_disjoint in DISJ.
    rewrite map_disjoint_spec. intros [scp field] x y LOOK1 LOOK2.
    rewrite /state_slice in LOOK1, LOOK2.
    apply map_lookup_filter_Some in LOOK1.
    apply map_lookup_filter_Some in LOOK2.
    destruct LOOK1 as [_ IN1]. destruct LOOK2 as [_ IN2].
    simpl in IN1, IN2.
    exact (DISJ scp IN1 IN2).
  Qed.

  Lemma state_values_lookup m k :
    state_values (scope k) m !! state_key_encode k =
      Excl <$> live_state m !! k.
  Proof.
    rewrite /state_values lookup_kmap lookup_fmap
      /state_entries map_lookup_filter.
    destruct (live_state m !! k); simpl; by repeat case_guard.
  Qed.

  Lemma state_values_insert m k v scp :
    state_values scp (<[k := Some v]> m) =
      if decide (scope k = scp)
      then <[state_key_encode k := Excl v]> (state_values scp m)
      else state_values scp m.
  Proof.
    rewrite /state_values /state_entries /live_state
      (omap_insert_Some id m k (Some v) v) //.
    destruct (decide (scope k = scp)) as [EQ|NEQ].
    - rewrite map_filter_insert_True; last done.
      rewrite fmap_insert kmap_insert. done.
    - rewrite map_filter_insert_False; last done.
      rewrite map_filter_delete delete_notin //.
      rewrite map_lookup_filter.
      destruct (omap id m !! k); simpl; by repeat case_guard.
  Qed.

  Lemma elem_of_state_fields m k :
    state_key_encode k ∈ state_fields (scope k) m ↔
      is_Some (live_state m !! k).
  Proof.
    rewrite /state_fields elem_of_dom state_values_lookup.
    apply fmap_is_Some.
  Qed.

  Lemma elem_of_state_uninit_set m k :
    state_key_encode k ∈ state_uninit_set (scope k) m ↔
      live_state m !! k = None.
  Proof.
    rewrite /state_uninit_set elem_of_difference elem_of_top
      elem_of_gset_to_coPset elem_of_state_fields.
    rewrite eq_None_not_Some. tauto.
  Qed.

  Lemma state_fields_slice_ext S m1 m2 scp
      (IN : scp ∈ S) (EQ : state_slice S m1 = state_slice S m2) :
    state_fields scp m1 = state_fields scp m2.
  Proof.
    assert (FILTER : ∀ m,
        state_entries scp m =
          filter (fun kv : key * Any.t => scope kv.1 = scp)
            (state_slice S m)).
    { intros m. rewrite /state_entries /state_slice.
      symmetry. apply map_filter_filter_l.
      intros [key_scope field] v LOOK EQSCOPE. simpl in *.
      by subst key_scope. }
    assert (ENTRIES : state_entries scp m1 = state_entries scp m2).
    { rewrite !FILTER EQ. done. }
    by rewrite /state_fields /state_values ENTRIES.
  Qed.

  Lemma state_absent_slice_ext S m1 m2
      (EQ : state_slice S m1 = state_slice S m2) :
    state_absent S m1 ≡ state_absent S m2.
  Proof.
    intros scp. rewrite /state_absent /state_uninit_set.
    destruct (decide (scp ∈ S)) as [IN|NIN]; last done.
    by rewrite (state_fields_slice_ext S m1 m2 scp IN EQ).
  Qed.

  Lemma state_fields_insert m k v scp :
    state_fields scp (<[k := Some v]> m) =
      if decide (scope k = scp)
      then {[state_key_encode k]} ∪ state_fields scp m
      else state_fields scp m.
  Proof.
    rewrite /state_fields state_values_insert.
    destruct (decide (scope k = scp)); first by rewrite dom_insert_L.
    done.
  Qed.

  Lemma state_absent_insert_new S m k v
      (IN : scope k ∈ S) (NONE : live_state m !! k = None) :
    state_absent S m ≡
      state_token (scope k) {[state_key_encode k]} ⋅
        state_absent S (<[k := Some v]> m).
  Proof.
    intros scp.
    rewrite discrete_fun_lookup_op /state_absent /state_token.
    destruct (decide (scp ∈ S)) as [INS|NINS].
    - destruct (decide (scope k = scp)) as [EQ|NEQ].
      + subst scp. rewrite discrete_fun_lookup_singleton.
        assert (ABS : state_uninit_set (scope k)
            (<[k := Some v]> m) =
            state_uninit_set (scope k) m ∖ {[state_key_encode k]}).
        { apply set_eq. intros i.
          rewrite /state_uninit_set state_fields_insert.
          case_decide; last contradiction.
          rewrite !elem_of_difference !elem_of_top
            !elem_of_gset_to_coPset elem_of_union elem_of_singleton.
          set_solver. }
        rewrite ABS -reservation_map_token_difference; first done.
        intros i. rewrite elem_of_singleton => ->.
        rewrite elem_of_state_uninit_set. exact NONE.
      + rewrite discrete_fun_lookup_singleton_ne // left_id.
        rewrite /state_uninit_set state_fields_insert. case_decide; done.
    - destruct (decide (scope k = scp)) as [EQ|NEQ].
      + subst scp. exfalso. set_solver.
      + rewrite discrete_fun_lookup_singleton_ne // left_id. done.
  Qed.

  Lemma state_absent_union S1 S2 m (DISJ : S1 ## S2) :
    state_absent (S1 ∪ S2) m ≡
      state_absent S1 m ⋅ state_absent S2 m.
  Proof.
    apply elem_of_disjoint in DISJ. intros scp.
    rewrite discrete_fun_lookup_op /state_absent.
    destruct (decide (scp ∈ S1)) as [IN1|NIN1];
      destruct (decide (scp ∈ S2)) as [IN2|NIN2].
    - exfalso. exact (DISJ scp IN1 IN2).
    - destruct (decide (scp ∈ S1 ∪ S2)) as [IN|NIN].
      + by rewrite right_id.
      + exfalso. apply NIN. set_solver.
    - destruct (decide (scp ∈ S1 ∪ S2)) as [IN|NIN].
      + by rewrite left_id.
      + exfalso. apply NIN. set_solver.
    - destruct (decide (scp ∈ S1 ∪ S2)) as [IN|NIN].
      + exfalso. set_solver.
      + by rewrite left_id.
  Qed.

  Lemma state_fields_insert_existing m k v old
      (LOOK : live_state m !! k = Some old) scp :
    state_fields scp (<[k := Some v]> m) = state_fields scp m.
  Proof.
    rewrite state_fields_insert.
    destruct (decide (scope k = scp)) as [EQ|NEQ]; last done.
    subst scp.
    assert (IN : state_key_encode k ∈ state_fields (scope k) m).
    { rewrite elem_of_state_fields. eauto. }
    apply set_eq. intros i. rewrite elem_of_union elem_of_singleton.
    split.
    - intros [->|Hi]; done.
    - intros Hi. right. done.
  Qed.

  Lemma state_absent_insert_existing S m k v old
      (LOOK : live_state m !! k = Some old) :
    state_absent S (<[k := Some v]> m) ≡ state_absent S m.
  Proof.
    intros scp.
    rewrite /state_absent /state_uninit_set.
    by rewrite (state_fields_insert_existing m k v old LOOK scp).
  Qed.

  Lemma state_absent_insert_value S m k v1 v2 :
    state_absent S (<[k := Some v1]> m) ≡
      state_absent S (<[k := Some v2]> m).
  Proof.
    intros scp. rewrite /state_absent /state_uninit_set.
    by rewrite !state_fields_insert.
  Qed.

  Lemma state_present_valid m : ✓ state_present m.
  Proof.
    intros scp. rewrite /state_present reservation_map_valid_eq /=.
    split.
    - intros i.
      destruct (state_values scp m !! i) as [[x|]|] eqn:LOOK.
      + exact I.
      + have BAD := LOOK.
        apply lookup_kmap_Some in BAD as (k & -> & BAD).
        2: apply state_key_encode_inj.
        rewrite lookup_fmap in BAD.
        destruct (state_entries scp m !! k) as [y|] eqn:ENTRY;
          [change (Some (Excl y) = Some ExclInvalid) in BAD
          |change (None = Some (@ExclInvalid Any.t)) in BAD];
          discriminate BAD.
      + exact I.
    - intros i. destruct (state_values scp m !! i) as [x|] eqn:LOOK;
        last by left.
      right. rewrite /state_uninit_set elem_of_difference elem_of_top
        elem_of_gset_to_coPset. intros [_ NIN]. apply NIN.
      by apply elem_of_dom; eauto.
  Qed.

  Lemma reservation_map_points (sm : gmap key Any.t) :
    ([^op map] k ↦ v ∈ sm,
      reservation_map_data (A := stateV) (state_key_encode k) (Excl v))
      ≡ (ReservationMap
          (kmap state_key_encode (Excl <$> sm)) ε :
            reservation_map stateV).
  Proof.
    induction sm as [|k v sm NONE IH] using map_ind.
    - rewrite big_opM_empty fmap_empty kmap_empty. done.
    - rewrite big_opM_insert // fmap_insert kmap_insert IH.
      rewrite /reservation_map_data /op /cmra_op /=.
      assert (ENC_NONE :
          (kmap state_key_encode (Excl <$> sm) : gmap positive stateV) !!
            state_key_encode k = None).
      { rewrite lookup_kmap lookup_fmap NONE. done. }
      split; simpl.
      + rewrite -(insert_singleton_op _ _ _ ENC_NONE). done.
      + rewrite left_id. done.
  Qed.

  Lemma state_slice_scope S m scp :
    filter (fun kv : key * Any.t => scope kv.1 = scp)
      (state_slice S m) =
      if decide (scp ∈ S) then state_entries scp m else ∅.
  Proof.
    destruct (decide (scp ∈ S)) as [IN|NIN].
    - rewrite /state_slice /state_entries.
      apply map_filter_filter_l.
      intros [key_scope field] v LOOK EQSCOPE. simpl in *.
      by subst key_scope.
    - apply map_empty_filter_2.
      intros [key_scope field] v LOOK EQSCOPE.
      rewrite /state_slice in LOOK.
      apply map_lookup_filter_Some in LOOK as [_ INS]. simpl in *.
      subst key_scope. contradiction.
  Qed.

  Lemma state_points_filter (sm : gmap key Any.t) scp :
    ([^op map] k ↦ v ∈ sm,
      if decide (scope k = scp)
      then reservation_map_data (A := stateV)
        (state_key_encode k) (Excl v)
      else ε) ≡
    ([^op map] k ↦ v ∈
      filter (fun kv : key * Any.t => scope kv.1 = scp) sm,
      reservation_map_data (A := stateV)
        (state_key_encode k) (Excl v)).
  Proof.
    induction sm as [|k v sm NONE IH] using map_ind.
    - rewrite map_filter_empty !big_opM_empty. done.
    - rewrite big_opM_insert //.
      destruct (decide (scope k = scp)) as [EQ|NEQ].
      + rewrite map_filter_insert_True; last done.
        rewrite big_opM_insert; last by rewrite map_lookup_filter NONE.
        rewrite IH. done.
      + rewrite map_filter_insert_False; last done.
        rewrite map_filter_delete delete_notin;
          last by rewrite map_lookup_filter NONE.
        rewrite left_id IH. done.
  Qed.

  Lemma state_points_lookup S m scp :
    state_points S m scp ≡
      if decide (scp ∈ S)
      then (ReservationMap (state_values scp m) ε :
        reservation_map stateV)
      else ε.
  Proof.
    rewrite /state_points
      (big_opM_commute (fun f : stateF => f scp)
        (fun k v => state_data k v) (state_slice S m)).
    transitivity ([^op map] k ↦ v ∈ state_slice S m,
      if decide (scope k = scp)
      then reservation_map_data (A := stateV)
        (state_key_encode k) (Excl v)
      else ε).
    { apply big_opM_proper. intros k v LOOK.
      rewrite state_data_lookup. done. }
    transitivity ([^op map] k ↦ v ∈
      filter (fun kv : key * Any.t => scope kv.1 = scp)
        (state_slice S m),
      reservation_map_data (A := stateV)
        (state_key_encode k) (Excl v)).
    { apply state_points_filter. }
    rewrite state_slice_scope.
    destruct (decide (scp ∈ S)) as [IN|NIN].
    - rewrite reservation_map_points /state_values. done.
    - rewrite big_opM_empty. done.
  Qed.

  Lemma state_fragment_points S m :
    state_fragment S m ≡ state_points S m ⋅ state_absent S m.
  Proof.
    intros scp. rewrite discrete_fun_lookup_op state_points_lookup
      /state_fragment /state_absent /state_present.
    destruct (decide (scp ∈ S)); last by rewrite left_id.
    rewrite /op /cmra_op /=. split; simpl.
    - by rewrite right_id.
    - by rewrite left_id.
  Qed.

  Lemma state_fragment_included S m :
    state_fragment S m ≼ state_present m.
  Proof.
    exists (state_fragment_rest S m). intros scp.
    rewrite discrete_fun_lookup_op /state_fragment /state_fragment_rest.
    destruct (decide (scp ∈ S)); by rewrite ?left_id ?right_id.
  Qed.

  Local Lemma state_points_sep γ S m :
    own γ (◯ state_points S m) ⊢
      [∗ map] k ↦ v ∈ state_slice S m, own γ (◯ state_data k v).
  Proof.
    rewrite /state_points big_opM_auth_frag.
    apply big_opM_own_1.
  Qed.

  Lemma reservation_map_replace_local_update
      (values : gmap positive stateV) E i (v vn : Any.t)
      (LOOK : values !! i = Some (Excl v)) :
    ((ReservationMap values (CoPset E) : reservation_map stateV),
      reservation_map_data (A := stateV) i (Excl v)) ~l~>
    ((ReservationMap (<[i := Excl vn]> values) (CoPset E) :
        reservation_map stateV),
      reservation_map_data (A := stateV) i (Excl vn)).
  Proof.
    rewrite local_update_unital_discrete.
    intros [frame [Ef|]] VALID EQ; last by destruct EQ.
    destruct EQ as [EQm EQE]. simpl in EQm, EQE.
    rewrite reservation_map_valid_eq /= in VALID.
    destruct VALID as [VALID DISJ].
    assert (NONE : frame !! i = None).
    { destruct (frame !! i) as [x|] eqn:FRAME; last done.
      exfalso. move: (VALID i).
      rewrite EQm lookup_op lookup_singleton FRAME /=.
      by destruct x. }
    split.
    - rewrite reservation_map_valid_eq /=. split.
      + intros j. destruct (decide (i = j)) as [->|NEQ].
        * rewrite lookup_insert. done.
        * rewrite lookup_insert_ne //.
      + intros j. destruct (decide (i = j)) as [->|NEQ].
        * right. destruct (DISJ j) as [ABSENT|NIN]; last done.
          rewrite LOOK in ABSENT. discriminate.
        * rewrite lookup_insert_ne //.
    - split; simpl.
      + intros j. destruct (decide (i = j)) as [->|NEQ].
        * rewrite lookup_insert lookup_op lookup_singleton NONE /= right_id.
          done.
        * move: (EQm j).
          rewrite lookup_insert_ne // !lookup_op !lookup_singleton_ne //
            !left_id.
      + exact EQE.
  Qed.

  Lemma reservation_map_insert_local_update
      (values : gmap positive stateV) E i (v : Any.t)
      (IN : i ∈ E) :
    ((ReservationMap values (CoPset E) : reservation_map stateV),
      reservation_map_token (A := stateV) {[i]}) ~l~>
    ((ReservationMap (<[i := Excl v]> values) (CoPset (E ∖ {[i]})) :
        reservation_map stateV),
      reservation_map_data (A := stateV) i (Excl v)).
  Proof.
    rewrite local_update_unital_discrete.
    intros [frame [Ef|]] VALID EQ; last by destruct EQ.
    destruct EQ as [EQm EQE]. simpl in EQm, EQE.
    destruct (decide ({[i]} ## Ef)) as [DISJE|NDISJE].
    2: { exfalso.
      rewrite /op /cmra_op /= decide_False // in EQE. }
    rewrite /op /cmra_op /= decide_True // in EQE.
    inversion EQE; subst E.
    rewrite reservation_map_valid_eq /= in VALID.
    destruct VALID as [VALID DISJ].
    assert (NONE : frame !! i = None).
    { have EQmi := EQm i.
      rewrite lookup_op lookup_empty left_id in EQmi.
      apply leibniz_equiv in EQmi.
      move: (DISJ i). rewrite EQmi.
      intros [ABSENT|NIN]; first done. exfalso. set_solver. }
    split.
    - rewrite reservation_map_valid_eq /=. split.
      + intros j. destruct (decide (i = j)) as [->|NEQ].
        * rewrite lookup_insert. done.
        * rewrite lookup_insert_ne //.
      + intros j. destruct (decide (i = j)) as [->|NEQ].
        * right. set_solver.
        * rewrite lookup_insert_ne //.
          move: (DISJ j). set_solver.
    - split; simpl.
      + intros j. destruct (decide (i = j)) as [->|NEQ].
        * rewrite lookup_insert lookup_op lookup_singleton NONE /= right_id.
          done.
        * move: (EQm j).
          rewrite lookup_insert_ne // !lookup_op lookup_empty
            !lookup_singleton_ne // !left_id.
      + rewrite left_id. f_equal. set_solver.
  Qed.

  Lemma state_present_update_local m k v vn
      (LOOK : live_state m !! k = Some v) :
    (state_present m, state_data k v) ~l~>
      (state_present (<[k := Some vn]> m), state_data k vn).
  Proof.
    apply discrete_fun_local_update. intros scp.
    rewrite /state_present /state_data.
    destruct (decide (scope k = scp)) as [EQ|NEQ].
    - subst scp. rewrite !discrete_fun_lookup_singleton state_values_insert.
      case_decide; try contradiction.
      rewrite /state_uninit_set
        (state_fields_insert_existing m k vn v LOOK (scope k)).
      apply reservation_map_replace_local_update.
      by rewrite state_values_lookup LOOK.
    - rewrite !discrete_fun_lookup_singleton_ne //.
      rewrite state_values_insert. case_decide; try contradiction.
      rewrite /state_uninit_set
        (state_fields_insert_existing m k vn v LOOK scp).
      reflexivity.
  Qed.

  Lemma state_present_insert_local m k v
      (NONE : live_state m !! k = None) :
    (state_present m,
      state_token (scope k) {[state_key_encode k]}) ~l~>
      (state_present (<[k := Some v]> m), state_data k v).
  Proof.
    apply discrete_fun_local_update. intros scp.
    rewrite /state_present /state_token /state_data.
    destruct (decide (scope k = scp)) as [EQ|NEQ].
    - subst scp. rewrite !discrete_fun_lookup_singleton state_values_insert.
      case_decide; try contradiction.
      assert (ABS : state_uninit_set (scope k)
          (<[k := Some v]> m) =
          state_uninit_set (scope k) m ∖ {[state_key_encode k]}).
      { apply set_eq. intros i.
        rewrite /state_uninit_set state_fields_insert.
        case_decide; try contradiction.
        rewrite !elem_of_difference !elem_of_top
          !elem_of_gset_to_coPset elem_of_union elem_of_singleton.
        set_solver. }
      rewrite ABS. apply reservation_map_insert_local_update.
      by rewrite elem_of_state_uninit_set.
    - rewrite !discrete_fun_lookup_singleton_ne //.
      rewrite state_values_insert. case_decide; try contradiction.
      rewrite /state_uninit_set state_fields_insert.
      case_decide; try contradiction. reflexivity.
  Qed.

  Lemma state_present_data_lookup m k v
      (VALID : ✓ (● state_present m ⋅ ◯ state_data k v)) :
    live_state m !! k = Some v.
  Proof.
    apply auth_both_valid_discrete in VALID as [INCL _].
    have INCL_SCOPE :=
      discrete_fun_included_spec_1 _ _ (scope k) INCL.
    rewrite /state_data discrete_fun_lookup_singleton /state_present
      reservation_map_included in INCL_SCOPE.
    destruct INCL_SCOPE as [DATA _].
    assert (VALUES_VALID : ✓ state_values (scope k) m).
    { have VALID := state_present_valid m (scope k).
      rewrite reservation_map_valid_eq /= in VALID.
      destruct VALID as [VALUES_VALID _]. exact VALUES_VALID. }
    rewrite /reservation_map_data /=
      (singleton_included_exclusive_l _ _ _ _) // in DATA.
    rewrite state_values_lookup in DATA.
    apply leibniz_equiv in DATA.
    destruct (live_state m !! k) as [w|] eqn:LIVE; last discriminate.
    inversion DATA. done.
  Qed.

  Lemma state_present_uninit_lookup m k
      (VALID : ✓ (● state_present m ⋅
        ◯ state_token (scope k) {[state_key_encode k]})) :
    live_state m !! k = None.
  Proof.
    apply auth_both_valid_discrete in VALID as [INCL _].
    have INCL_SCOPE :=
      discrete_fun_included_spec_1 _ _ (scope k) INCL.
    rewrite /state_token discrete_fun_lookup_singleton /state_present
      reservation_map_included in INCL_SCOPE.
    destruct INCL_SCOPE as [_ TOKEN].
    rewrite /reservation_map_token /= coPset_disj_included in TOKEN.
    rewrite -elem_of_state_uninit_set. apply TOKEN. set_solver.
  Qed.

  Lemma SI_tgt_lookup m k v :
    SI_tgt m -∗ points_to_tgt k v -∗
      ⌜m !! k = Some (Some v)⌝.
  Proof.
    iIntros "AUTH PT".
    iCombine "AUTH PT" gives %VALID.
    have LIVE := state_present_data_lookup m k v VALID.
    rewrite live_state_lookup in LIVE.
    iPureIntro. destruct (m !! k) as [[w|]|]; inversion LIVE. done.
  Qed.

  Lemma SI_src_lookup m k v :
    SI_src m -∗ points_to_src k v -∗
      ⌜m !! k = Some (Some v)⌝.
  Proof.
    iIntros "AUTH PT".
    iCombine "AUTH PT" gives %VALID.
    have LIVE := state_present_data_lookup m k v VALID.
    rewrite live_state_lookup in LIVE.
    iPureIntro. destruct (m !! k) as [[w|]|]; inversion LIVE. done.
  Qed.

  Lemma uninit_tgt_scope_split scp E i (IN : i ∈ E) :
    uninit_tgt_scope scp E ⊣⊢
      uninit_tgt_scope scp {[i]} ∗
      uninit_tgt_scope scp (E ∖ {[i]}).
  Proof.
    rewrite /uninit_tgt_scope /state_token.
    rewrite -own_op -auth_frag_op.
    rewrite discrete_fun_singleton_op.
    rewrite -reservation_map_token_difference; first done.
    set_solver.
  Qed.

  Lemma uninit_src_scope_split scp E i (IN : i ∈ E) :
    uninit_src_scope scp E ⊣⊢
      uninit_src_scope scp {[i]} ∗
      uninit_src_scope scp (E ∖ {[i]}).
  Proof.
    rewrite /uninit_src_scope /state_token.
    rewrite -own_op -auth_frag_op.
    rewrite discrete_fun_singleton_op.
    rewrite -reservation_map_token_difference; first done.
    set_solver.
  Qed.

  Lemma SI_tgt_update m k v v' :
    SI_tgt m -∗ points_to_tgt k v ==∗
      SI_tgt (<[k := Some v']> m) ∗ points_to_tgt k v'.
  Proof.
    iIntros "AUTH PT".
    iCombine "AUTH PT" gives %VALID.
    have LIVE := state_present_data_lookup m k v VALID.
    iCombine "AUTH PT" as "STATE".
    iMod (own_update with "STATE") as "STATE".
    { apply auth_update, state_present_update_local. exact LIVE. }
    rewrite own_op. iDestruct "STATE" as "[$ $]". done.
  Qed.

  Lemma SI_src_update m k v v' :
    SI_src m -∗ points_to_src k v ==∗
      SI_src (<[k := Some v']> m) ∗ points_to_src k v'.
  Proof.
    iIntros "AUTH PT".
    iCombine "AUTH PT" gives %VALID.
    have LIVE := state_present_data_lookup m k v VALID.
    iCombine "AUTH PT" as "STATE".
    iMod (own_update with "STATE") as "STATE".
    { apply auth_update, state_present_update_local. exact LIVE. }
    rewrite own_op. iDestruct "STATE" as "[$ $]". done.
  Qed.

  Lemma SI_tgt_insert m k v (NONE : m !! k = None) :
    SI_tgt m -∗ uninit_tgt k ==∗
      SI_tgt (<[k := Some v]> m) ∗ points_to_tgt k v.
  Proof.
    iIntros "AUTH UNINIT".
    assert (LIVE : live_state m !! k = None).
    { by rewrite live_state_lookup NONE. }
    iCombine "AUTH UNINIT" as "STATE".
    iMod (own_update with "STATE") as "STATE".
    { apply auth_update, state_present_insert_local. exact LIVE. }
    rewrite own_op. iDestruct "STATE" as "[$ $]". done.
  Qed.

  Lemma SI_src_insert m k v (NONE : m !! k = None) :
    SI_src m -∗ uninit_src k ==∗
      SI_src (<[k := Some v]> m) ∗ points_to_src k v.
  Proof.
    iIntros "AUTH UNINIT".
    assert (LIVE : live_state m !! k = None).
    { by rewrite live_state_lookup NONE. }
    iCombine "AUTH UNINIT" as "STATE".
    iMod (own_update with "STATE") as "STATE".
    { apply auth_update, state_present_insert_local. exact LIVE. }
    rewrite own_op. iDestruct "STATE" as "[$ $]". done.
  Qed.

  Lemma SI_tgt_uninit_lookup m k :
    SI_tgt m -∗ uninit_tgt k -∗ ⌜mjoin (m !! k) = None⌝.
  Proof.
    iIntros "AUTH UNINIT".
    iCombine "AUTH UNINIT" gives %VALID.
    iPureIntro. rewrite -live_state_lookup.
    exact (state_present_uninit_lookup m k VALID).
  Qed.

  Lemma SI_src_uninit_lookup m k :
    SI_src m -∗ uninit_src k -∗ ⌜mjoin (m !! k) = None⌝.
  Proof.
    iIntros "AUTH UNINIT".
    iCombine "AUTH UNINIT" gives %VALID.
    iPureIntro. rewrite -live_state_lookup.
    exact (state_present_uninit_lookup m k VALID).
  Qed.

End BASIC_LEMMAS.

Section INIT_LAWS.

  Context {Σ : GRA}.

  Lemma state_init_tgt_ext `{STATE : !stateGS Σ} S m1 m2
      (EQ : state_slice S m1 = state_slice S m2) :
    state_init_tgt S m1 STATE ⊣⊢ state_init_tgt S m2 STATE.
  Proof.
    rewrite /state_init_tgt /= EQ.
    rewrite (state_absent_slice_ext S m1 m2 EQ). done.
  Qed.

  Lemma state_init_src_ext `{STATE : !stateGS Σ} S m1 m2
      (EQ : state_slice S m1 = state_slice S m2) :
    state_init_src S m1 STATE ⊣⊢ state_init_src S m2 STATE.
  Proof.
    rewrite /state_init_src /= EQ.
    rewrite (state_absent_slice_ext S m1 m2 EQ). done.
  Qed.

  Lemma state_init_tgt_union `{STATE : !stateGS Σ} S1 S2 m
      (DISJ : S1 ## S2) :
    state_init_tgt (S1 ∪ S2) m STATE ⊣⊢
      state_init_tgt S1 m STATE ∗ state_init_tgt S2 m STATE.
  Proof.
    rewrite /state_init_tgt /= state_slice_union.
    rewrite big_sepM_union; last by apply state_slice_disjoint.
    rewrite state_absent_union // auth_frag_op own_op.
    iSplit.
    - iIntros "[[P1 P2] [A1 A2]]". iFrame.
    - iIntros "[[P1 A1] [P2 A2]]". iFrame.
  Qed.

  Lemma state_init_src_union `{STATE : !stateGS Σ} S1 S2 m
      (DISJ : S1 ## S2) :
    state_init_src (S1 ∪ S2) m STATE ⊣⊢
      state_init_src S1 m STATE ∗ state_init_src S2 m STATE.
  Proof.
    rewrite /state_init_src /= state_slice_union.
    rewrite big_sepM_union; last by apply state_slice_disjoint.
    rewrite state_absent_union // auth_frag_op own_op.
    iSplit.
    - iIntros "[[P1 P2] [A1 A2]]". iFrame.
    - iIntros "[[P1 A1] [P2 A2]]". iFrame.
  Qed.

End INIT_LAWS.

Section INIT_ACCESS.

  Context {Σ : GRA}.

  Lemma state_init_tgt_acc `{STATE : !stateGS Σ} S m k
      (SCOPE : scope k ∈ S) :
    state_init_tgt S m STATE ⊢
      ∃ ov, ⌜ov = mjoin (m !! k)⌝ ∗ state_cell_tgt k ov ∗
        (∀ ov', ⌜state_cell_transition ov ov'⌝ -∗
          state_cell_tgt k ov' -∗
          state_init_tgt S (set_state_cell k ov' m) STATE).
  Proof.
    rewrite /state_init_tgt /=. iIntros "[PTS ABS]".
    destruct (live_state m !! k) as [v|] eqn:LOOK.
    - assert (SL : state_slice S m !! k = Some v).
      { rewrite (state_slice_lookup_in S m k SCOPE)
          -live_state_lookup LOOK. done. }
      iDestruct (big_sepM_delete _ _ _ _ SL with "PTS") as "[PT PTS]".
      iExists (Some v). iSplit.
      { iPureIntro. rewrite -live_state_lookup. done. }
      iFrame "PT". iIntros (ov') "%TRANS CELL".
      destruct ov' as [v'|].
      + rewrite /set_state_cell /state_init_tgt /= state_slice_insert //.
        iSplitL "CELL PTS".
        { rewrite -insert_delete_insert big_sepM_insert ?lookup_delete //.
          iFrame. }
        rewrite (state_absent_insert_existing S m k v' v LOOK). iFrame.
      + exfalso. destruct TRANS as [EQ|SOME]; first discriminate.
        by destruct SOME.
    - assert (SL : state_slice S m !! k = None).
      { rewrite (state_slice_lookup_in S m k SCOPE)
          -live_state_lookup LOOK. done. }
      iEval (rewrite (state_absent_insert_new S m k (tt↑) SCOPE LOOK)
        auth_frag_op own_op) in "ABS".
      iDestruct "ABS" as "[UNINIT ABS]".
      iExists None. iSplit.
      { iPureIntro. rewrite -live_state_lookup. done. }
      iFrame "UNINIT". iIntros (ov') "%TRANS CELL".
      destruct ov' as [v'|].
      + rewrite /set_state_cell /state_init_tgt /= state_slice_insert //.
        iSplitL "CELL PTS".
        { rewrite big_sepM_insert //; iFrame. }
        rewrite (state_absent_insert_value S m k v' (tt↑)). iFrame.
      + assert (EQSL : state_slice S m = state_slice S (delete k m)).
        { rewrite state_slice_delete delete_notin //. }
        rewrite /set_state_cell /= -EQSL
          -(state_absent_slice_ext S m (delete k m) EQSL).
        iFrame "PTS".
        iEval (rewrite /state_cell_tgt /uninit_tgt /uninit_tgt_scope)
          in "CELL".
        iCombine "CELL ABS" as "ABS".
        iEval (rewrite
          -(state_absent_insert_new S m k (tt↑) SCOPE LOOK))
          in "ABS". iFrame.
  Qed.

  Lemma state_init_src_acc `{STATE : !stateGS Σ} S m k
      (SCOPE : scope k ∈ S) :
    state_init_src S m STATE ⊢
      ∃ ov, ⌜ov = mjoin (m !! k)⌝ ∗ state_cell_src k ov ∗
        (∀ ov', ⌜state_cell_transition ov ov'⌝ -∗
          state_cell_src k ov' -∗
          state_init_src S (set_state_cell k ov' m) STATE).
  Proof.
    rewrite /state_init_src /=. iIntros "[PTS ABS]".
    destruct (live_state m !! k) as [v|] eqn:LOOK.
    - assert (SL : state_slice S m !! k = Some v).
      { rewrite (state_slice_lookup_in S m k SCOPE)
          -live_state_lookup LOOK. done. }
      iDestruct (big_sepM_delete _ _ _ _ SL with "PTS") as "[PT PTS]".
      iExists (Some v). iSplit.
      { iPureIntro. rewrite -live_state_lookup. done. }
      iFrame "PT". iIntros (ov') "%TRANS CELL".
      destruct ov' as [v'|].
      + rewrite /set_state_cell /state_init_src /= state_slice_insert //.
        iSplitL "CELL PTS".
        { rewrite -insert_delete_insert big_sepM_insert ?lookup_delete //.
          iFrame. }
        rewrite (state_absent_insert_existing S m k v' v LOOK). iFrame.
      + exfalso. destruct TRANS as [EQ|SOME]; first discriminate.
        by destruct SOME.
    - assert (SL : state_slice S m !! k = None).
      { rewrite (state_slice_lookup_in S m k SCOPE)
          -live_state_lookup LOOK. done. }
      iEval (rewrite (state_absent_insert_new S m k (tt↑) SCOPE LOOK)
        auth_frag_op own_op) in "ABS".
      iDestruct "ABS" as "[UNINIT ABS]".
      iExists None. iSplit.
      { iPureIntro. rewrite -live_state_lookup. done. }
      iFrame "UNINIT". iIntros (ov') "%TRANS CELL".
      destruct ov' as [v'|].
      + rewrite /set_state_cell /state_init_src /= state_slice_insert //.
        iSplitL "CELL PTS".
        { rewrite big_sepM_insert //; iFrame. }
        rewrite (state_absent_insert_value S m k v' (tt↑)). iFrame.
      + assert (EQSL : state_slice S m = state_slice S (delete k m)).
        { rewrite state_slice_delete delete_notin //. }
        rewrite /set_state_cell /= -EQSL
          -(state_absent_slice_ext S m (delete k m) EQSL).
        iFrame "PTS".
        iEval (rewrite /state_cell_src /uninit_src /uninit_src_scope)
          in "CELL".
        iCombine "CELL ABS" as "ABS".
        iEval (rewrite
          -(state_absent_insert_new S m k (tt↑) SCOPE LOOK))
          in "ABS". iFrame.
  Qed.

End INIT_ACCESS.

Section ALLOCATION.

  Context `{PRE : !stateGpreS Σ}.

  Lemma state_alloc S_src S_tgt st_src st_tgt
      (NODUPS : map_Forall (const is_Some) st_src)
      (NODUPT : map_Forall (const is_Some) st_tgt) :
    ⊢ o=> ∃ STATE : stateGS Σ,
      @SI_src Σ STATE st_src ∗
      @SI_tgt Σ STATE st_tgt ∗
      @state_init_src Σ S_src st_src STATE ∗
      @state_init_tgt Σ S_tgt st_tgt STATE.
  Proof.
    iMod (own_alloc
      (● state_present st_src ⋅ ◯ state_fragment S_src st_src))
      as (γ_src) "[AUTH_SRC FRAG_SRC]".
    { apply auth_both_valid_discrete. split.
      - apply state_fragment_included.
      - apply state_present_valid. }
    iMod (own_alloc
      (● state_present st_tgt ⋅ ◯ state_fragment S_tgt st_tgt))
      as (γ_tgt) "[AUTH_TGT FRAG_TGT]".
    { apply auth_both_valid_discrete. split.
      - apply state_fragment_included.
      - apply state_present_valid. }
    pose (STATE := Build_stateGS Σ PRE γ_tgt γ_src).
    iEval (rewrite state_fragment_points auth_frag_op own_op)
      in "FRAG_SRC".
    iEval (rewrite state_fragment_points auth_frag_op own_op)
      in "FRAG_TGT".
    iDestruct "FRAG_SRC" as "[PTS_SRC ABSENT_SRC]".
    iDestruct "FRAG_TGT" as "[PTS_TGT ABSENT_TGT]".
    iDestruct (@state_points_sep Σ STATE γ_src S_src st_src
      with "PTS_SRC") as "PTS_SRC".
    iDestruct (@state_points_sep Σ STATE γ_tgt S_tgt st_tgt
      with "PTS_TGT") as "PTS_TGT".
    iModIntro. iExists STATE.
    rewrite /SI_src /SI_tgt /state_init_src /state_init_tgt
      /points_to_src /points_to_tgt /=.
    iFrame.
  Qed.

End ALLOCATION.

Notation "k '↦tgt' v" := (points_to_tgt k v)
  (at level 20, format "k  ↦tgt  v") : bi_scope.
Notation "k '↦src' v" := (points_to_src k v)
  (at level 20, format "k  ↦src  v") : bi_scope.
