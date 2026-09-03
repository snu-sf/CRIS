From CRIS.common Require Import Common ConcRA.
From CRIS.modules Require Import Mod.
From CRIS.modules Require Export FSpec SModTr Sp.
From stdpp Require Import sorting strings.

Notation fnsemmap := (gmap fname (option (emask * (option fspec_rel * fbody)))).

Module SMod. Section Smod.
  Context `{!crisG Γ Σ α β τ _S _I}.

  (* The image of the maps are lifted by option to make the module append operation total. *)
  Record t : Type := mk {
    scopes : list string;
    fnsems : fnsemmap;
    initial_st : gmap key (option Any.t);

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

  Lemma t_eq (ms1 ms2 : t) :
    scopes ms1 = scopes ms2 →
    fnsems ms1 = fnsems ms2 →
    initial_st ms1 = initial_st ms2 →
    ms1 = ms2.
  Proof.
    destruct ms1, ms2; ss. intros Hscp Hfns Hst.
    subst scopes0 fnsems0 initial_st0; f_equal; apply proof_irrelevance.
  Qed.

  (**** Real ****)

  Definition is_real (m: t) : Prop :=
    ∀ fno msk fspo fbd,
      (fnsems m) !! fno = Some (Some (msk, (fspo, fbd))) -> fspo = None.

  (**** Linking ****)
  Program Definition empty : t := {|
    scopes := [];
    fnsems := ∅;
    initial_st := ∅;
  |}.
  Solve All Obligations with try done; econs.

  Program Definition add ms1 ms2 : t := {|
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

  Lemma add_comm (ms1 ms2 : t) : add ms1 ms2 = add ms2 ms1.
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

  Program Definition to_mod (sp : specmap) (ms : t) : Mod.t := {|
    Mod.scopes := ms.(scopes);
    Mod.fnsems := (λ (x : option _), (map_snd (SModTr.trans_fnsem sp)) <$> x) <$> ms.(fnsems);
    Mod.initial_st := ms.(initial_st);
  |}.
  Next Obligation. ii; eapply sorted_scopes. Qed.
  Next Obligation.
    intros sp ms fno [msk p].
    rewrite lookup_omap lookup_fmap. destruct (fnsems ms !! fno) eqn: Heq; intros FIND; ss.
    destruct o as [[msk0 [fspo p0]]|]; ss. inv FIND.
    hexploit (well_scoped_fns ms). i. unfold map_Forall in H. specialize (H fno (msk, (fspo, p0))).
    eapply H. rewrite lookup_omap Heq; refl.
  Qed.
  Next Obligation. ii. destruct ms. ss. eauto. Qed.
  Next Obligation.
    ii. destruct ms. ss.
    hexploit nodup_init0; eauto. i. specialize (H1 i). eapply H1; eauto.
  Qed.

  Lemma to_mod_add sp (ms1 ms2 : t) :
    to_mod sp (add ms1 ms2) = Mod.add (to_mod sp ms1) (to_mod sp ms2).
  Proof.
    apply Mod.t_eq; ss; apply map_eq; intros i;
      rewrite /Mod.fnsems; s; simpl_map; rewrite !lookup_union_with ?lookup_fmap;
      repeat destruct (_ !! i); ss.
  Qed.

  Definition addL (ms : list t) : t :=
    foldr add empty ms.

  Lemma to_mod_addL sp (mds : list t)  :
    to_mod sp (addL mds) = Mod.addL (List.map (to_mod sp) mds).
  Proof using.
    induction mds; ss; first by (apply Mod.t_eq).
    rewrite to_mod_add IHmds //.
  Qed.

  Program Definition update_spec (f: option fspec_rel → option fspec_rel) (ms: t) : t := {|
    scopes := ms.(scopes);
    fnsems := (.≫= (λ '(msk, bd), Some (msk, (f bd.1,bd.2)))) <$> ms.(fnsems);
    initial_st := ms.(initial_st);
  |}.
  Next Obligation. ii; eapply sorted_scopes. Qed.
  Next Obligation.
    intros f ms fn [? ?] Hin; hexploit (ms.(well_scoped_fns)); eauto.
    rewrite lookup_omap_id_Some lookup_fmap in Hin;
      destruct (_ !! _) as [[[p1 [p2 p3]]|]|] eqn : Hin';
      ss; clarify.
    intros Hwf. hexploit (Hwf fn (e, (p2, p3))); ss.
    rewrite lookup_omap_id_Some; ss.
  Qed.
  Next Obligation. intros f ms; ii; destruct ms; ss; eauto. Qed.
  Next Obligation.
    ii. destruct ms. ss.
    hexploit nodup_init0; eauto. i. specialize (H1 i). eapply H1; eauto.
  Qed.

  Program Definition filter (mskF: emask → emask) (ms: t) : t := {|
    scopes := ms.(scopes);
    fnsems := (.≫= (λ '(msk, bd), Some (msk_and msk (mskF msk), bd))) <$> ms.(fnsems);
    initial_st := ms.(initial_st);
  |}.
  Next Obligation. ii; eapply sorted_scopes. Qed.
  Next Obligation.
    intros mskF ms fn [? ?] Hin; hexploit (ms.(well_scoped_fns)); eauto.
    rewrite lookup_omap_id_Some lookup_fmap in Hin;
      destruct (_ !! _) as [[[p1 [p2 p3]]|]|] eqn : Hin';
      ss; clarify.
    intros Hwf. hexploit (Hwf fn (p1, (p2, p3))); ss.
    { rewrite lookup_omap_id_Some; ss. }
    i. destruct H as [Hput Hget]. unfold msk_and; split; i; bsimpl; des; et.
  Qed.
  Next Obligation. intros mskF ms; ii; destruct ms; ss; eauto. Qed.
  Next Obligation.
    ii. destruct ms. ss.
    hexploit nodup_init0; eauto. i. specialize (H1 i). eapply H1; eauto.
  Qed.

  Lemma filter_add mskF (ms1 ms2 : t) :
    filter mskF (add ms1 ms2) = add (filter mskF ms1) (filter mskF ms2).
  Proof.
    apply t_eq; ss; apply map_eq; intros i;
      rewrite /Mod.fnsems; s; simpl_map; rewrite !lookup_union_with ?lookup_fmap;
      repeat destruct (_ !! i); ss.
  Qed.

  Program Definition to_mod_cancel (sp : specmap) (ms : t) : Mod.t := {|
    Mod.scopes := ms.(scopes);
    Mod.fnsems := (λ (x : option _), (λ y, (y.1, SModTr.trans_cancel sp y)) <$> x) <$> ms.(fnsems);
    Mod.initial_st := ms.(initial_st);
  |}.
  Next Obligation. ii; eapply sorted_scopes. Qed.
  Next Obligation.
    intros sp ms fno [msk p].
    rewrite lookup_omap lookup_fmap. destruct (fnsems ms !! fno) eqn: Heq; intros FIND; ss.
    destruct o as [[msk0 [fspo p0]]|]; ss. inv FIND.
    hexploit (well_scoped_fns ms). i. unfold map_Forall in H. specialize (H fno (msk, (fspo, p0))).
    eapply H. rewrite lookup_omap Heq; refl.
  Qed.
  Next Obligation. ii. destruct ms. ss. eauto. Qed.
  Next Obligation.
    ii. destruct ms. ss.
    hexploit nodup_init0; eauto. i. specialize (H1 i). eapply H1; eauto.
  Qed.

  Lemma to_mod_cancel_add sp (ms1 ms2 : t) :
    to_mod_cancel sp (add ms1 ms2) = Mod.add (to_mod_cancel sp ms1) (to_mod_cancel sp ms2).
  Proof.
    apply Mod.t_eq; ss; apply map_eq; intros i;
      rewrite /Mod.fnsems; s; simpl_map; rewrite !lookup_union_with ?lookup_fmap;
      repeat destruct (_ !! i); ss.
  Qed.
  
  Program Definition cancel (ms : t) : t := {|
    scopes := ms.(scopes);
    fnsems := (.≫= (λ '(msk, bd), Some (msk, (None, bd.2)))) <$> ms.(fnsems);
    initial_st := ms.(initial_st);
  |}.
  Next Obligation. ii; eapply sorted_scopes. Qed.
  Next Obligation.
    intros ms fn [? ?] Hin; hexploit (ms.(well_scoped_fns)); eauto.
    rewrite lookup_omap_id_Some lookup_fmap in Hin;
      destruct (_ !! _) as [[[p1 [p2 p3]]|]|] eqn : Hin';
      ss; clarify.
    intros Hwf; specialize (Hwf fn (e, (p2, p3))); ss; apply Hwf.
    rewrite lookup_omap_id_Some; ss.
  Qed.
  Next Obligation. intros ms; ii; destruct ms; ss; eauto. Qed.
  Next Obligation.
    ii. destruct ms. ss.
    hexploit nodup_init0; eauto. i. specialize (H1 i). eapply H1; eauto.
  Qed.

  Lemma cancel_add (ms1 ms2 : t) : cancel (add ms1 ms2) = add (cancel ms1) (cancel ms2).
  Proof.
    apply t_eq; ss; apply map_eq; intros i; simpl_map; rewrite !lookup_union_with ?lookup_fmap;
      repeat destruct (_ !! i); ss.
  Qed.

  Definition sp_core_from (md : t) :=
    omap id (fst ∘ snd <$> omap id md.(fnsems)).

  Definition sp_from (md : t) : specmap :=
    (sp_core_from md, true).

  Definition cancellable (ms : t) : Prop :=
    map_Forall
      (λ k v, match v with | Some (msk, _) => img_msk msk ∧ call_msk msk | _ => True end)
      (fnsems ms).

  Lemma sp_core_from_lookup fn fspo (m: t)
    (LU: sp_core_from m !! fn = Some fspo)
    :
    ∃ msk fbd, fnsems m !! fn = Some (Some (msk, (Some fspo, fbd))).
  Proof.
    rewrite lookup_omap lookup_fmap lookup_omap in LU.
    destruct (fnsems _ !! _) eqn: Lm_fn; ss.
    destruct o as [[msk [fspo' fbd]]|]; ss. subst. et.
  Qed.

  Lemma sp_core_from_add_lookup fn fspo (m1 m2: t)
    (LU: sp_core_from (add m1 m2) !! fn = Some fspo)
    :
    (sp_core_from m1 !! fn = Some fspo ∧ sp_core_from m2 !! fn = None)
    ∨
    (sp_core_from m1 !! fn = None ∧ sp_core_from m2 !! fn = Some fspo).
  Proof.
    rewrite lookup_omap_Some in LU. des.
    rewrite lookup_fmap_Some in LU0. des; subst.
    rewrite lookup_omap_Some in LU1. des.
    rewrite lookup_union_with_Some in LU0.
    destruct x as [[? []]|]; ss. depdes LU1 LU; ss; subst.
    rewrite /sp_core_from. rewrite !lookup_omap !lookup_fmap !lookup_omap.
    des; ss; rewrite LU0 LU1; et.
  Qed.

  Lemma cancellable_add (ms1 ms2 : t) :
    cancellable ms1 → cancellable ms2 → cancellable (add ms1 ms2).
  Proof.
    rewrite /cancellable !map_Forall_lookup; intros Hi1 Hi2 i x; specialize (Hi1 i);
      specialize (Hi2 i); rewrite lookup_union_with; repeat destruct (_ !! i); i; ss; clarify;
      des_ifs; naive_solver.
  Qed.
End Smod. End SMod.

Arguments SMod.sp_core_from : simpl never.

Infix "☆" := SMod.add (at level 60, right associativity).

Section Aux.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Lemma lookup_sp_from md fn kboo
    (FIND: md.(SMod.fnsems) !! funid fn = kboo) :
    SMod.sp_core_from md !! (funid fn) =
      match kboo with
      | Some (Some (_, (Some fsp, _))) => Some fsp
      | _ => None
      end.
  Proof using.
    subst. s. rewrite lookup_omap lookup_fmap lookup_omap. des_ifs.
  Qed.
End Aux.
