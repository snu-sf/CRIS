From CRIS.common Require Import CRIS.
From CRIS.filter Require Export CallFilter.
From CRIS.prophecy Require Export ProphecyHeader ProphecyRA.
From CRIS.helping Require Export HelpingHeader.
From Stdlib Require Import Ensembles.

Module ProphecyA. Section ProphecyA.
  Context `{!crisG Γ Σ α β τ _S _I, !prophGS}.
  Context (mn : string).

  Definition scopes : list string := [].

  Definition new_spec : fspec :=
    fspec_simple
      (λ '(id, P),
        ((λ varg, ⌜varg = id↑⌝ ∗ free_id (.=id))%I,
        (λ vret, ∃ (p : P.(Prophecy.Pro)), ⌜vret = tt↑⌝ ∗ proph id (existT P (p, nil))))%I).

  Definition resolve_spec : fspec :=
    fspec_simple
      (λ '(id, existT Proph (p, obs_seq, obs)),
        ((λ varg,
          ⌜varg = (id, obs↑↑)↑⌝
          ∗ proph id (existT Proph (p, obs_seq))),
        (λ vret,
          ⌜vret = tt↑ /\ Proph.(Prophecy.consistent) (obs :: obs_seq) p⌝
          ∗ proph id (existT Proph (p, obs :: obs_seq))))%I
      ).

  Definition close_spec: fspec :=
    fspec_simple
      (λ '(id, existT Proph (p, obs_seq)),
        ((λ varg, ⌜varg = id↑⌝ ∗ proph id (existT Proph (p, obs_seq))),
        (λ vret, ⌜vret = tt↑⌝ ∗ free_id (.=id)))
      )%I.

  Definition mask : emask := msk_scp scopes (CFilter.msk_filter_in ∅ msk_true).
  
  Definition fnsems : fnsemmap :=
    {[fid (Prophecy.new mn)     # (mask, (fsp_some new_spec, fbody_trivial));
      fid (Prophecy.resolve mn) # (mask, (fsp_some resolve_spec, fbody_trivial));
      fid (Prophecy.close mn)   # (mask, (fsp_some close_spec, fbody_trivial))]}.

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with try mod_tac.

  Definition initial_cond : iProp Σ := proph_auth (Full_set _) (λ _, dummy_prophinst).

  Definition t sp := SMod.to_mod sp Mod.

  Lemma filter_helping mn0 sp:
    CFilter.filter (Helping.exports mn0) (t sp) = t sp.
  Proof. cfilter_solver. Qed.

End ProphecyA. End ProphecyA.
