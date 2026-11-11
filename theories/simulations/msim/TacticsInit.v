From CRIS.common Require Import Common ConcRA.
From iris.proofmode Require Export proofmode.
From CRIS.simulations.msim Require Export FnsemLookup.
From CRIS.simulations.msim Require Import
  TacticsCommon ITactics WTactics Tactics ISim ISimFacts WSim.
From CRIS.modules Require Import Mod SModTr.

Ltac rewrite_fnsem_lookup_in fl fn H :=
  let Hlookup := fresh "Hlookup" in
  first
    [ assert (Hlookup : FnsemLookupResult fl fn _) by
        solve [once (typeclasses eauto with fnsem_lookup)];
      destruct Hlookup as [Hlookup];
      rewrite Hlookup in H; clear Hlookup
    | let fl' := fnsem_lookup_normalize_map fl in
      let Hrhs :=
        lazymatch type of H with
        | _ = ?Hrhs => Hrhs
        end in
      change (fl' !! fn = Hrhs) in H;
      assert (Hlookup : FnsemLookupResult fl' fn _) by
        solve [once (typeclasses eauto with fnsem_lookup)];
      destruct Hlookup as [Hlookup];
      rewrite Hlookup in H; clear Hlookup
    ].

Ltac cStartModSim_with Ist :=
  let STATE := fresh "STATE" in
  first [ unfold bi_emp_valid | idtac ];
  (first
    [ lazymatch goal with
      | |- ?P ⊢ ISim.t ?ctx (?ms_src ★ ?md) (?ms_tgt ★ ?md) =>
          iIntros "INIT";
          iApply (ISim_reflR ctx ms_src ms_tgt md Ist with "[INIT] []")
      end;
      [ iIntros (STATE);
        rewrite /ISim.init_ist;
        iIntros (Hwf);
        iSplit;
        [ iPureIntro; (refl||eauto using submseteq_nil_l)
        | iIntros "SRC TGT"
        ]
      | iIntros (STATE);
        rewrite /ISim.sim_funs;
        iIntros (Hwf);
        iSplit;
        [ iPureIntro;
          split;
          [ try timeout 1 mod_tac
          | try ((repeat rewrite Mod.dom_fnsems_add); set_solver)
          ]
        | let fn := fresh "fn" in
          iIntros (fn) "%Hfn";
          match goal with
          | Hfn : fn ∈ dom _ |- _ =>
              (repeat rewrite Mod.dom_fnsems_add in Hfn);
              set_unfold in Hfn; des; subst
          end
        ]
      ]
    | lazymatch goal with
      | |- ?P ⊢ ISim.t ?ctx ?ms_src ?ms_tgt =>
          rewrite /ISim.t;
          iIntros "INIT" (STATE);
          iExists (Ist STATE);
          iSplitL "INIT";
          [ rewrite /ISim.init_ist;
            iIntros (Hwf);
            iSplit;
            [ iPureIntro; (refl||eauto using submseteq_nil_l)
            | iIntros "SRC TGT"
            ]
          | rewrite /ISim.sim_funs;
            iIntros (Hwf);
            iSplit;
            [ iPureIntro;
              split;
              [ try timeout 1 mod_tac
              | try ((repeat rewrite Mod.dom_fnsems_add); set_solver)
              ]
            | let fn := fresh "fn" in
              iIntros (fn) "%Hfn";
              match goal with
              | Hfn : fn ∈ dom _ |- _ =>
                  (repeat rewrite Mod.dom_fnsems_add in Hfn);
                  set_unfold in Hfn; des; subst
              end
            ]
          ]
      end
    ]).

Ltac cStartModSim_infer :=
  let Ist := open_constr:(_ : stateGS _ -> iProp _) in
  cStartModSim_with Ist.

Tactic Notation "cStartModSim" := cStartModSim_infer.
Tactic Notation "cStartModSim" constr(Ist) := cStartModSim_with Ist.

Ltac cStartFunSim :=
  iStartProof;
  lazymatch goal with
  | |- environments.envs_entails _
        (ISim.sim_fun _ _ _ _ _) => idtac
  | |- environments.envs_entails _
        (_ -∗ ISim.sim_fun _ _ _ _ _) =>
      first [ iIntros "#?" | iIntros "?" ]
  end;
  lazymatch goal with
  | |- environments.envs_entails _
        (ISim.sim_fun ?ctx ?ms_src ?ms_tgt ?Ist ?fn) =>
      rewrite /ISim.sim_fun;
      let fl_src := fresh "fl_src" in
      let fl_tgt := fresh "fl_tgt" in
      let EXTS := fresh "EXTS" in
      let EXTT := fresh "EXTT" in
      let Hfs := fresh "Hfs" in
      let Hbase := fresh "Hbase" in
      let Hext := fresh "Hext" in
      iIntros "%WFS %WFT" (fl_src EXTS fl_tgt EXTT fs Hfs);
      assert (Hbase : sandbox_fnsemmap (Mod.fnsems ms_src) !! fn =
        Some _) by (clear Hfs; prove_inline_cond);
      pose proof (lookup_weaken _ _ _ _ Hbase
        (ISim.fnsem_ext_subseteq _ _ _ EXTS)) as Hext;
      rewrite Hext in Hfs; injection Hfs as <-;
      try clear Hbase; try clear Hext;
      iExists _;
      iSplit; first (iPureIntro; prove_inline_cond);
      rewrite /isim_fsem;
      iModIntro;
      iIntros (arg) "IST"; iApply wsim_isim;
      rewrite /SB.sandbox_body; simpl fst; simpl snd;
      rewrite /SModTr.trans_fnsem /SModTr.HoareFun /cfunU /cfunN
  end.
