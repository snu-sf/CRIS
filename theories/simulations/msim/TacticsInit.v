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

Ltac cStartModSim :=
  first [ unfold bi_emp_valid | idtac ];
  (first
    [ iApply ISim_reflR;
      [ rewrite /ISim.init_ist;
        iIntros (Hwf);
        iSplit;
        [ iPureIntro; (refl||eauto using submseteq_nil_l)
        | iIntros (STATE) "SRC TGT"
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
    | lazymatch goal with
      | |- ?P ⊢ ISim.t ?ctx ?ms_src ?ms_tgt ?Ist =>
          rewrite /ISim.t;
          iIntros "INIT";
          iSplitL "INIT";
          [ rewrite /ISim.init_ist;
            iIntros (Hwf);
            iSplit;
            [ iPureIntro; (refl||eauto using submseteq_nil_l)
            | iIntros (STATE) "SRC TGT"
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
      iIntros (STATE);
      iIntros "%WFS %WFT" (fs);
      first
        [ iIntros "%";
          match goal with
          | Hfs : _ = Some (Some _) |- _ =>
              rewrite_fnsem_lookup_in
                (sandbox_fnsemmap (Mod.fnsems ms_src)) fn Hfs;
              cbn in Hfs;
              lazymatch type of Hfs with
              | Some (Some _) = Some (Some _) => simplify_eq
              | _ => fail 0
              end
          end
        | simpl_map;
          iIntros "%";
          match goal with
          | Hfs : _ = Some (Some _) |- _ =>
              cbn in Hfs; simplify_eq
          end
        ];
      iExists _;
      iSplit; first (iPureIntro; prove_inline_cond);
      rewrite /isim_fsem;
      iModIntro;
      iIntros (arg) "IST"; iApply wsim_isim;
      rewrite /SB.sandbox_body; simpl fst; simpl snd;
      rewrite /SModTr.trans_fnsem /SModTr.HoareFun /cfunU /cfunN
  end.
