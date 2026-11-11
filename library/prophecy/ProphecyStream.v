From CRIS.common Require Import CRIS.
From CRIS.prophecy Require Import ProphecyHeader ProphecyRA ProphecyA.
From stdpp Require Import streams list.

Definition obs_stream {X} (obs_seq : nat → X) : stream X :=
  let cofix go n := obs_seq n :.: go (S n) in go 0.

Lemma lookup_obs_stream {X} (obs_seq : nat → X) (n : nat) :
  obs_stream obs_seq !.! n = obs_seq n.
Proof.
  rewrite /obs_stream. remember 0 as i. set (n2 := n) at 2.
  assert (i + n = n2) as Hin by lia; revert Hin.
  generalize i n2; clear dependent i n2. induction n as [|n IHn].
  { intros ??; rewrite Nat.add_0_r; intros ->; ss. }
  intros i n2 Hi; s; rewrite (IHn (S i) n2); ss; lia.
Qed.

Lemma stake_S {X} (str : stream X) (n : nat) :
  stake (S n) str = stake n str ++ [str !.! n].
Proof.
  revert str; induction n as [|n Hn] using Nat.strong_induction_le; first ss.
  intros str; specialize (Hn n (Nat.le_refl _) (stail str)); ss; rewrite Hn; ss.
Qed.

Lemma length_firstn {X} (obs_seq : nat → X) n :
  length (Prophecy.firstn obs_seq n) = n.
Proof. induction n; ss; lia. Qed.

Fixpoint list_stream_app {X} (l : list X) (str : stream X) : stream X :=
  match l with
  | hd :: tl => scons hd (list_stream_app tl str)
  | [] => str
  end.

Lemma list_stream_app_app {X} (l1 l2 : list X) (str : stream X) :
  list_stream_app (l1 ++ l2) str = list_stream_app l1 (list_stream_app l2 str).
Proof. revert l2 str; induction l1 as [|e1 l1]; ii; ss; f_equal; auto. Qed.

Lemma list_stream_app_stake {X} (l : list X) str :
  stake (length l) (list_stream_app l str) = l.
Proof. induction l as [|x l IHl]; ss; by rewrite IHl. Qed.

Lemma lookup_list_stream_app_r {X} (l : list X) str n :
  length l ≤ n → list_stream_app l str !.! n = str !.! (n - length l).
Proof.
  revert l str; induction n; intros l str Hl.
  { assert (length l = 0) as Hl2 by lia; apply nil_length_inv in Hl2; subst l.
    rewrite length_nil //=.
  }
  destruct l as [|e l]; ss. apply IHn; lia.
Qed.

Definition stream_prophecy (Obs : Type) `{Inhabited Obs} : Prophecy.t.
Proof.
  refine {| Prophecy.Pro := stream Obs;
            Prophecy.Obs := Obs;
            Prophecy.consistent := λ l p, reverse l = stake (length l) p;
            Prophecy.obs_default := inhabitant;
            Prophecy.coverage := _ |}.
  intros obs_seq; exists (obs_stream obs_seq). intros i; rewrite length_firstn.
  induction i as [|i]; first ss.
  simpl Prophecy.firstn; rewrite reverse_cons. rewrite stake_S IHi; f_equal.
  rewrite lookup_obs_stream //.
Defined.

Lemma stream_prophecy_consistent_head {X} `{Inhabited X} (rs : list X) str obs :
  (stream_prophecy X).(Prophecy.consistent) (obs :: rs) (list_stream_app (reverse rs) str) →
  shead str = obs.
Proof.
  rewrite /stream_prophecy /=. intros Hconsistent.
  change (shead (list_stream_app (reverse rs) str) ::
          stake (length rs) (stail (list_stream_app (reverse rs) str)))
    with (stake (S (length rs)) (list_stream_app (reverse rs) str)) in Hconsistent.
  rewrite stake_S in Hconsistent.
  replace (length rs) with (length (reverse rs)) in Hconsistent by rewrite length_reverse //.
  rewrite list_stream_app_stake in Hconsistent.
  rewrite lookup_list_stream_app_r in Hconsistent; last by rewrite length_reverse.
  rewrite length_reverse Nat.sub_diag /= in Hconsistent.
  rewrite reverse_cons app_inj_tail_iff in Hconsistent. by destruct Hconsistent as [_ <-].
Qed.

Lemma list_stream_app_consume {X} (rs : list X) str obs :
  shead str = obs →
  list_stream_app (reverse (obs :: rs)) (stail str) = list_stream_app (reverse rs) str.
Proof.
  intros Hhead. rewrite reverse_cons list_stream_app_app /=.
  destruct str; ss; clarify.
Qed.

Definition ProphResolveInst : Type :=
  { P : Prophecy.t & (P.(Prophecy.Pro) * list P.(Prophecy.Obs) * P.(Prophecy.Obs))%type }.

Section ProphecyStream.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !prophGS}.
  Context {Obs : Type} `{Inhabited Obs}.

  Definition stream_proph_inst (str : stream Obs) (rs : list Obs) : ProphInst :=
    existT (stream_prophecy Obs) (list_stream_app (reverse rs) str, rs).

  Definition stream_proph_resolve_arg (str : stream Obs) (rs : list Obs) (obs : Obs) : ProphResolveInst :=
    existT (stream_prophecy Obs) (list_stream_app (reverse rs) str, rs, obs).

  Definition stream_proph_resolved_inst (str : stream Obs) (rs : list Obs) (obs : Obs) : ProphInst :=
    existT (stream_prophecy Obs) (list_stream_app (reverse rs) str, obs :: rs).

  Definition stream_proph (id : Prophecy.ID) (str : stream Obs) : iProp Σ :=
    (∃ rs, proph id (stream_proph_inst str rs))%I.

  Definition syn_stream_proph {n} (id : Prophecy.ID) (str : τ{stream Obs, n}%SAT) : GTerm.t n :=
    (∃ (rs : τ{list Obs}),
      syn_proph id (stream_proph_inst str rs))%SAT.

  Global Instance stream_proph_red {n} id str :
    SLRed n (syn_stream_proph id str) (stream_proph id str).
  Proof. solve_sl_red. Qed.

  Lemma stream_proph_new id :
    (∃ p, proph id (existT (stream_prophecy Obs) (p, []))) -∗
    ∃ str, stream_proph id str.
  Proof.
    iIntros "H". iDestruct "H" as (p) "Hp".
    iExists p. rewrite /stream_proph. iExists []. ss.
  Qed.

  Lemma stream_proph_resolve id str rs obs :
    (stream_prophecy Obs).(Prophecy.consistent) (obs :: rs) (list_stream_app (reverse rs) str) →
    proph id (stream_proph_resolved_inst str rs obs) -∗
    ⌜shead str = obs⌝ ∗ stream_proph id (stail str).
  Proof.
    iIntros (Hconsistent) "Hp".
    pose proof (stream_prophecy_consistent_head rs str obs Hconsistent) as Hhead.
    iSplit; first done. rewrite /stream_proph.
    iExists (obs :: rs). rewrite /stream_proph_inst /stream_proph_resolved_inst.
    rewrite (list_stream_app_consume rs str obs Hhead). iFrame.
  Qed.

  Lemma stream_proph_resolve_open id str obs :
    stream_proph id str -∗
    ∃ rs,
      proph id (stream_proph_inst str rs) ∗
      (∀ Hconsistent : (stream_prophecy Obs).(Prophecy.consistent)
          (obs :: rs) (list_stream_app (reverse rs) str),
        proph id (stream_proph_resolved_inst str rs obs) -∗
        ⌜shead str = obs⌝ ∗ stream_proph id (stail str)).
  Proof.
    iIntros "Hproph". rewrite /stream_proph.
    iDestruct "Hproph" as (rs) "Hp".
    iExists rs. iFrame. iIntros (Hconsistent) "Hp".
    iApply (stream_proph_resolve with "Hp"). exact Hconsistent.
  Qed.
End ProphecyStream.

Section ProphecyStreamWSim.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !prophGS}.
  Context `{!stateGS Σ}.
  Context {Obs : Type} `{Inhabited Obs}.

  Context (fl_s fl_t : gmap fname (Any.t → itree crisE Any.t)).
  Context (Ist : iProp Σ).
  Context (R_s R_t : Type).
  Context (RR : retr_type Σ R_s R_t).
  Context (ps pt : bool).

  Context (mn : string) (sp : specmap).

  Lemma wsim_stream_proph_new id k_s k_t E1 E2 g :
    fl_t !! fid (Prophecy.new mn) =
      Some (SB.sandbox_body
        (msk_scp [] (CFilter.msk_filter_in ∅ msk_true),
          SModTr.trans_fnsem sp (fsp_some ProphecyA.new_spec, fbody_trivial))) →
    img_msk (msk_scp [] (CFilter.msk_filter_in ∅ msk_true)) →
    free_id (.=id) -∗
    (∀ str : stream Obs, stream_proph id str -∗
      wsim fl_s fl_t Ist (E1, E2) g R_s R_t RR ps true
        k_s (k_t tt↑)) -∗
    wsim fl_s fl_t Ist (E1, E2) g R_s R_t RR ps pt
      k_s (x <- trigger (Call (Prophecy.new mn).1 id↑);; k_t x).
  Proof.
    iIntros (Hfind Hmsk) "Hfree K".
    cInlineT. cForceT (_, stream_prophecy Obs).
    cForcesT. iSplitL "Hfree".
    { repeat iSplit; first iPureIntro; ss. }
    cStepsT. iDestruct "GRT" as "[-> [%p [-> Hproph]]]".
    iPoseProof (stream_proph_new with "[Hproph]") as "Hproph".
    { iExists p. iFrame. }
    iDestruct "Hproph" as (str) "Hproph".
    iApply ("K" with "Hproph").
  Qed.

  Lemma wsim_stream_proph_resolve id (str : stream Obs) (obs : Obs) k_s k_t E1 E2 g :
    fl_t !! fid (Prophecy.resolve mn) =
      Some (SB.sandbox_body
        (msk_scp [] (CFilter.msk_filter_in ∅ msk_true),
          SModTr.trans_fnsem sp (fsp_some ProphecyA.resolve_spec, fbody_trivial))) →
    img_msk (msk_scp [] (CFilter.msk_filter_in ∅ msk_true)) →
    stream_proph id str -∗
    (⌜shead str = obs⌝ -∗ stream_proph id (stail str) -∗
      wsim fl_s fl_t Ist (E1, E2) g R_s R_t RR ps true
        k_s (k_t tt↑)) -∗
    wsim fl_s fl_t Ist (E1, E2) g R_s R_t RR ps pt
      k_s
      (x <- trigger (Call (Prophecy.resolve mn).1 (id, obs↑↑)↑);; k_t x).
  Proof.
    iIntros (Hfind Hmsk) "Hproph K".
    iPoseProof (stream_proph_resolve_open id str obs with "Hproph") as "Hopen".
    iDestruct "Hopen" as (rs) "[Hp Hclose]".
    cInlineT. cForceT (_, stream_proph_resolve_arg str rs obs).
    cForcesT. iSplitL "Hp".
    { repeat iSplit; eauto. }
    cStepsT. iDestruct "GRT" as "[-> [[-> %Hconsistent] Hp]]".
    iPoseProof ("Hclose" $! Hconsistent with "Hp") as "[%Hhead Hproph]".
    iApply ("K" with "[] Hproph"). done.
  Qed.
End ProphecyStreamWSim.
