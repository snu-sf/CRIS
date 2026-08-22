From iris.bi Require Import bi.
From iris.proofmode Require Export proofmode.
From iris.proofmode Require Import
  base environments intro_patterns reduction spec_patterns.

Section bi_proset_mixin.

  Context (PROP : bi).
  Context (ob : Type).
  Context (hom : ob -> ob -> PROP).

  Record BiProsetMixin : Prop :=
    {
      proset_mixin_refl : forall x, emp ⊢ hom x x;
      proset_mixin_trans : forall x y z, hom x y ∗ hom y z ⊢ hom x z;
    }.

  Context (unit : ob).
  Context (tensor : ob -> ob -> ob).

  Record BiMonProsetMixin : Prop :=
    {
      proset_mixin_tensor_hom : forall x x' y y', hom x x' ∗ hom y y' ⊢ hom (tensor x y) (tensor x' y');
      proset_mixin_tensor_assoc : forall x y z, emp ⊢ hom (tensor (tensor x y) z) (tensor x (tensor y z));
      proset_mixin_tensor_assoc_inv : forall x y z, emp ⊢ hom (tensor x (tensor y z)) (tensor (tensor x y) z);
      proset_mixin_tensor_left_unit : forall x, emp ⊢ hom (tensor unit x) x;
      proset_mixin_tensor_left_unit_inv : forall x, emp ⊢ hom x (tensor unit x);
      proset_mixin_tensor_right_unit : forall x, emp ⊢ hom (tensor x unit) x;
      proset_mixin_tensor_right_unit_inv : forall x, emp ⊢ hom x (tensor x unit);
    }.

  Record BiSymMonProsetMixin : Prop :=
    {
      proset_mixin_tensor_braid : forall x y, emp ⊢ hom (tensor x y) (tensor y x);
    }.

End bi_proset_mixin.

Section bi_proset.

  (* (PROP,∗,emp)-enriched preordered set equipped with symmetric monoidal structure *)
  Record BiProset (PROP : bi) : Type :=
    { proset_ob :> Type;
      proset_hom : proset_ob -> proset_ob -> PROP;
      proset_unit : proset_ob;
      proset_tensor : proset_ob -> proset_ob -> proset_ob;
      proset_bi_proset_mixin : BiProsetMixin PROP proset_ob proset_hom;
      proset_bi_mon_proset_mixin : BiMonProsetMixin PROP proset_ob proset_hom proset_unit proset_tensor;
      proset_bi_sym_mon_proset_mixin : BiSymMonProsetMixin PROP proset_ob proset_hom proset_tensor;
    }.

End bi_proset.

(** A framing witness removes [R] from [P], leaving [Q]. *)
Class BiProsetFrame {PROP : bi} (X : BiProset PROP) (R P Q : X) :=
  biproset_frame :
    ⊢ proset_hom _ X (proset_tensor _ X R Q) P.
Global Arguments BiProsetFrame {_} _ _ _ _.
Global Arguments biproset_frame {_} _ _ _ _ {_}.
Global Hint Mode BiProsetFrame + + + ! - : typeclass_instances.

(** * Proof-mode representation *)

Definition bpenv_replace {A}
    (i j : ident) (y : A) (Γ : env A) : option (env A) :=
  env_replace i (Esnoc Enil j y) Γ.

Definition bpenv_split {A}
    (i i1 i2 : ident) (x1 x2 : A) (Γ : env A) : option (env A) :=
  env_replace i (Esnoc (Esnoc Enil i1 x1) i2 x2) Γ.

Fixpoint bpenv_remove_ident (i : ident) (ids : list ident)
    : option (list ident) :=
  match ids with
  | [] => None
  | j :: ids =>
      if ident_beq i j then Some ids
      else
        match bpenv_remove_ident i ids with
        | Some ids' => Some (j :: ids')
        | None => None
        end
  end.

Fixpoint bpenv_partition {A} (ids : list ident) (Γ : env A)
    : option (env A * env A) :=
  match Γ with
  | Enil =>
      match ids with
      | [] => Some (Enil, Enil)
      | _ => None
      end
  | Esnoc Γ i x =>
      match bpenv_remove_ident i ids with
      | Some ids' =>
          '(Γ1, Γ2) ← bpenv_partition ids' Γ;
          Some (Esnoc Γ1 i x, Γ2)
      | None =>
          '(Γ1, Γ2) ← bpenv_partition ids Γ;
          Some (Γ1, Esnoc Γ2 i x)
      end
  end.

Fixpoint bpenv_interp {PROP : bi}
    (X : BiProset PROP) (Γ : env X) : X :=
  match Γ with
  | Enil => proset_unit _ X
  | Esnoc Γ _ x => proset_tensor _ X (bpenv_interp X Γ) x
  end.

Fixpoint bpenv_interp_stripped_go {PROP : bi}
    (X : BiProset PROP) (acc : X) (Γ : env X) : X :=
  match Γ with
  | Enil => acc
  | Esnoc Γ _ x =>
      bpenv_interp_stripped_go X (proset_tensor _ X x acc) Γ
  end.

Definition bpenv_interp_stripped {PROP : bi}
    (X : BiProset PROP) (Γ : env X) : X :=
  match Γ with
  | Enil => proset_unit _ X
  | Esnoc Γ _ x => bpenv_interp_stripped_go X x Γ
  end.

Definition bpenv_entails {PROP : bi}
    (X : BiProset PROP) (Γ : env X) (Q : X) : PROP :=
  proset_hom _ X (bpenv_interp X Γ) Q.
Global Arguments bpenv_entails {_} _ _ _.
Global Arguments bpenv_entails : simpl never.

Section bi_proset_laws.
  Context {PROP : bi} (X : BiProset PROP).

  Lemma biproset_refl x :
    ⊢ proset_hom _ X x x.
  Proof.
    exact (proset_mixin_refl _ _ _ (proset_bi_proset_mixin _ X) x).
  Qed.

  Lemma biproset_trans x y z :
    proset_hom _ X x y ∗ proset_hom _ X y z
      ⊢ proset_hom _ X x z.
  Proof.
    exact (proset_mixin_trans _ _ _ (proset_bi_proset_mixin _ X)
      x y z).
  Qed.

  Lemma biproset_tensor_hom x x' y y' :
    proset_hom _ X x x' ∗ proset_hom _ X y y'
      ⊢ proset_hom _ X
          (proset_tensor _ X x y) (proset_tensor _ X x' y').
  Proof.
    exact (proset_mixin_tensor_hom _ _ _ _ _
      (proset_bi_mon_proset_mixin _ X) x x' y y').
  Qed.

  Lemma biproset_tensor_assoc x y z :
    ⊢ proset_hom _ X
      (proset_tensor _ X (proset_tensor _ X x y) z)
      (proset_tensor _ X x (proset_tensor _ X y z)).
  Proof.
    exact (proset_mixin_tensor_assoc _ _ _ _ _
      (proset_bi_mon_proset_mixin _ X) x y z).
  Qed.

  Lemma biproset_tensor_assoc_inv x y z :
    ⊢ proset_hom _ X
      (proset_tensor _ X x (proset_tensor _ X y z))
      (proset_tensor _ X (proset_tensor _ X x y) z).
  Proof.
    exact (proset_mixin_tensor_assoc_inv _ _ _ _ _
      (proset_bi_mon_proset_mixin _ X) x y z).
  Qed.

  Lemma biproset_tensor_left_unit_inv x :
    ⊢ proset_hom _ X x
      (proset_tensor _ X (proset_unit _ X) x).
  Proof.
    exact (proset_mixin_tensor_left_unit_inv _ _ _ _ _
      (proset_bi_mon_proset_mixin _ X) x).
  Qed.

  Lemma biproset_tensor_left_unit x :
    ⊢ proset_hom _ X
      (proset_tensor _ X (proset_unit _ X) x) x.
  Proof.
    exact (proset_mixin_tensor_left_unit _ _ _ _ _
      (proset_bi_mon_proset_mixin _ X) x).
  Qed.

  Lemma biproset_tensor_right_unit x :
    ⊢ proset_hom _ X
      (proset_tensor _ X x (proset_unit _ X)) x.
  Proof.
    exact (proset_mixin_tensor_right_unit _ _ _ _ _
      (proset_bi_mon_proset_mixin _ X) x).
  Qed.

  Lemma biproset_tensor_braid x y :
    ⊢ proset_hom _ X
      (proset_tensor _ X x y) (proset_tensor _ X y x).
  Proof.
    exact (proset_mixin_tensor_braid _ _ _ _
      (proset_bi_sym_mon_proset_mixin _ X) x y).
  Qed.

  Lemma biproset_tensor_move_right x y z :
    ⊢ proset_hom _ X
      (proset_tensor _ X (proset_tensor _ X x y) z)
      (proset_tensor _ X (proset_tensor _ X x z) y).
  Proof.
    iApply biproset_trans.
    iSplitL.
    - iApply biproset_tensor_assoc.
    - iApply biproset_trans.
      iSplitL.
      + iApply biproset_tensor_hom.
        iSplitL.
        * iApply biproset_refl.
        * iApply biproset_tensor_braid.
      + iApply biproset_tensor_assoc_inv.
  Qed.

  Global Instance biproset_frame_unit P :
    BiProsetFrame X (proset_unit _ X) P P | 0.
  Proof.
    unfold BiProsetFrame.
    iApply biproset_tensor_left_unit.
  Qed.

  Global Instance biproset_frame_here R :
    BiProsetFrame X R R (proset_unit _ X) | 1.
  Proof.
    unfold BiProsetFrame.
    iApply biproset_tensor_right_unit.
  Qed.

  Global Instance biproset_frame_tensor_l R P :
    BiProsetFrame X R (proset_tensor _ X R P) P | 2.
  Proof.
    unfold BiProsetFrame.
    iApply biproset_refl.
  Qed.

  Global Instance biproset_frame_tensor_r R P :
    BiProsetFrame X R (proset_tensor _ X P R) P | 3.
  Proof.
    unfold BiProsetFrame.
    iApply biproset_tensor_braid.
  Qed.

  Global Instance biproset_frame_tensor_l_rec R P1 P2 Q
      `{!BiProsetFrame X R P1 Q} :
    BiProsetFrame X R
      (proset_tensor _ X P1 P2) (proset_tensor _ X Q P2) | 9.
  Proof.
    unfold BiProsetFrame.
    iApply biproset_trans.
    iSplitL.
    - iApply biproset_tensor_assoc_inv.
    - iApply biproset_tensor_hom.
      iSplitL.
      + iApply biproset_frame.
      + iApply biproset_refl.
  Qed.

  Global Instance biproset_frame_tensor_r_rec R P1 P2 Q
      `{!BiProsetFrame X R P2 Q} :
    BiProsetFrame X R
      (proset_tensor _ X P1 P2) (proset_tensor _ X P1 Q) | 10.
  Proof.
    unfold BiProsetFrame.
    iApply biproset_trans.
    iSplitL.
    - iApply biproset_tensor_assoc_inv.
    - iApply biproset_trans.
      iSplitL.
      + iApply biproset_tensor_hom.
        iSplitL.
        * iApply biproset_tensor_braid.
        * iApply biproset_refl.
      + iApply biproset_trans.
        iSplitL.
        * iApply biproset_tensor_assoc.
        * iApply biproset_tensor_hom.
          iSplitL.
          -- iApply biproset_refl.
          -- iApply biproset_frame.
  Qed.

  Lemma bpenv_replace_hom Γ Γ' i j x y
      (LOOKUP : env_lookup i Γ = Some x)
      (REPLACE : bpenv_replace i j y Γ = Some Γ') :
    proset_hom _ X x y
      ⊢ proset_hom _ X (bpenv_interp X Γ) (bpenv_interp X Γ').
  Proof.
    unfold bpenv_replace in REPLACE.
    revert Γ' x LOOKUP REPLACE.
    induction Γ as [|Γ IH k z]; intros Γ' x LOOKUP REPLACE; simpl in *.
    { discriminate. }
    destruct (ident_beq_reflect i k) as [->|Hik].
    - simplify_eq.
      destruct (env_lookup j Γ); simplify_eq.
      iIntros "Hxy".
      iApply biproset_tensor_hom.
      iSplitR "Hxy".
      + iApply biproset_refl.
      + iExact "Hxy".
    - destruct (ident_beq_reflect k j) as [->|Hkj]; simplify_eq.
      destruct (env_replace i (Esnoc Enil j y) Γ) as [Γ''|]
        eqn:Hreplace;
        simpl in REPLACE; simplify_eq.
      iIntros "Hxy".
      iApply biproset_tensor_hom.
      iSplitL.
      + iApply (IH Γ'' x); [done|done|].
        iExact "Hxy".
      + iApply biproset_refl.
  Qed.

  Lemma bpenv_split_hom Γ Γ' i i1 i2 x1 x2
      (LOOKUP :
        env_lookup i Γ =
          Some (proset_tensor _ X x1 x2))
      (SPLIT : bpenv_split i i1 i2 x1 x2 Γ = Some Γ') :
    ⊢ proset_hom _ X (bpenv_interp X Γ) (bpenv_interp X Γ').
  Proof.
    unfold bpenv_split in SPLIT.
    revert Γ' LOOKUP SPLIT.
    induction Γ as [|Γ IH j x]; intros Γ' LOOKUP SPLIT; simpl in *.
    { discriminate. }
    destruct (ident_beq_reflect i j) as [->|Hij].
    - simplify_eq.
      destruct (env_lookup i1 Γ) as [p1|] eqn:H1.
      + simpl in SPLIT. discriminate.
      + simpl in SPLIT.
        destruct (ident_beq_reflect i2 i1) as [->|Hi2i1].
        * simpl in SPLIT. discriminate.
        * destruct (env_lookup i2 Γ) as [p2|] eqn:H2.
          -- simpl in SPLIT. discriminate.
          -- simpl in SPLIT. simplify_eq.
             iApply biproset_tensor_assoc_inv.
    - destruct (ident_beq_reflect j i2) as [->|Hji2].
      + simpl in SPLIT. discriminate.
      + destruct (ident_beq_reflect j i1) as [->|Hji1].
        * simpl in SPLIT. discriminate.
        * simpl in SPLIT.
          destruct
            (env_replace i (Esnoc (Esnoc Enil i1 x1) i2 x2) Γ)
            as [Γ''|] eqn:Hsplit.
          -- simpl in SPLIT. simplify_eq.
             iApply biproset_tensor_hom.
             iSplitL.
             ++ iApply (IH Γ''); done.
             ++ iApply biproset_refl.
          -- simpl in SPLIT. discriminate.
  Qed.

  Lemma bpenv_partition_hom ids Γ Γ1 Γ2
      (PARTITION : bpenv_partition ids Γ = Some (Γ1, Γ2)) :
    ⊢ proset_hom _ X (bpenv_interp X Γ)
      (proset_tensor _ X (bpenv_interp X Γ1) (bpenv_interp X Γ2)).
  Proof.
    revert ids Γ1 Γ2 PARTITION.
    induction Γ as [|Γ IH i x];
      intros ids Γ1 Γ2 PARTITION; simpl in PARTITION.
    - destruct ids; simplify_eq.
      iApply biproset_tensor_left_unit_inv.
    - destruct (bpenv_remove_ident i ids) as [ids'|] eqn:Hremove.
      + destruct (bpenv_partition ids' Γ) as [[Γ1' Γ2']|]
          eqn:Hpartition; simpl in PARTITION; simplify_eq.
        iApply biproset_trans.
        iSplitL.
        * iApply biproset_tensor_hom.
          iSplitL.
          -- iApply (IH ids'); done.
          -- iApply biproset_refl.
        * iApply biproset_tensor_move_right.
      + destruct (bpenv_partition ids Γ) as [[Γ1' Γ2']|]
          eqn:Hpartition; simpl in PARTITION; simplify_eq.
        iApply biproset_trans.
        iSplitL.
        * iApply biproset_tensor_hom.
          iSplitL.
          -- iApply (IH ids); done.
          -- iApply biproset_refl.
        * iApply biproset_tensor_assoc.
  Qed.

  Lemma bpenv_start i x Q :
    bpenv_entails X (Esnoc Enil i x) Q
      ⊢ proset_hom _ X x Q.
  Proof.
    iIntros "H".
    iApply biproset_trans.
    iSplitR "H".
    - iApply biproset_tensor_left_unit_inv.
    - iExact "H".
  Qed.

  Lemma bpenv_apply Γ x y :
    proset_hom _ X x y ∗ bpenv_entails X Γ x
      ⊢ bpenv_entails X Γ y.
  Proof.
    iIntros "[Hxy Hx]".
    iApply biproset_trans.
    iFrame.
  Qed.

  Lemma bpenv_partition_entails ids Γ Γ1 Γ2 x y
      (PARTITION : bpenv_partition ids Γ = Some (Γ1, Γ2)) :
    bpenv_entails X Γ1 x ∗ bpenv_entails X Γ2 y
      ⊢ bpenv_entails X Γ (proset_tensor _ X x y).
  Proof.
    iIntros "[Hx Hy]".
    iApply biproset_trans.
    iSplitR "Hx Hy".
    - iApply (bpenv_partition_hom ids Γ Γ1 Γ2 PARTITION).
    - iApply biproset_tensor_hom.
      iFrame.
  Qed.

  Lemma bpenv_partition_entails_right ids Γ Γ1 Γ2 x y
      (PARTITION : bpenv_partition ids Γ = Some (Γ1, Γ2)) :
    bpenv_entails X Γ2 x ∗ bpenv_entails X Γ1 y
      ⊢ bpenv_entails X Γ (proset_tensor _ X x y).
  Proof.
    iIntros "[Hx Hy]".
    iApply biproset_trans.
    iSplitR "Hx Hy".
    - iApply biproset_trans.
      iSplitL.
      + iApply (bpenv_partition_hom ids Γ Γ1 Γ2 PARTITION).
      + iApply biproset_tensor_braid.
    - iApply biproset_tensor_hom.
      iFrame.
  Qed.

  Lemma bpenv_assert ids Γ Γ1 Γ2 i x Q
      (PARTITION : bpenv_partition ids Γ = Some (Γ1, Γ2)) :
    bpenv_entails X Γ1 x ∗
      bpenv_entails X (Esnoc Γ2 i x) Q
      ⊢ bpenv_entails X Γ Q.
  Proof.
    iIntros "[Hx HQ]".
    iApply biproset_trans.
    iSplitR "Hx HQ".
    - iApply (bpenv_partition_hom ids Γ Γ1 Γ2 PARTITION).
    - iApply biproset_trans.
      iSplitL "Hx".
      + iApply biproset_tensor_hom.
        iSplitL "Hx".
        * iExact "Hx".
        * iApply biproset_refl.
      + iApply biproset_trans.
        iSplitR "HQ".
        * iApply biproset_tensor_braid.
        * iExact "HQ".
  Qed.

  Lemma bpenv_interp_stripped_go_hom Γ acc :
    ⊢ proset_hom _ X
      (proset_tensor _ X (bpenv_interp X Γ) acc)
      (bpenv_interp_stripped_go X acc Γ).
  Proof.
    revert acc.
    induction Γ as [|Γ IH i x]; intros acc.
    - simpl. iApply biproset_tensor_left_unit.
    - simpl. iApply biproset_trans.
      iSplitL.
      + iApply biproset_tensor_assoc.
      + iApply IH.
  Qed.

  Lemma bpenv_interp_stripped_hom Γ :
    ⊢ proset_hom _ X
      (bpenv_interp X Γ) (bpenv_interp_stripped X Γ).
  Proof.
    destruct Γ as [|Γ i x].
    - simpl. iApply biproset_refl.
    - simpl. iApply bpenv_interp_stripped_go_hom.
  Qed.

  Lemma bpenv_stop Γ Q :
    proset_hom _ X (bpenv_interp_stripped X Γ) Q
      ⊢ bpenv_entails X Γ Q.
  Proof.
    iIntros "H".
    iApply biproset_trans.
    iSplitR "H".
    - iApply bpenv_interp_stripped_hom.
    - iExact "H".
  Qed.

  Lemma bpenv_delete_unit Γ i
      (LOOKUP : env_lookup i Γ = Some (proset_unit _ X)) :
    ⊢ proset_hom _ X
      (bpenv_interp X Γ) (bpenv_interp X (env_delete i Γ)).
  Proof.
    induction Γ as [|Γ IH j x]; simpl in LOOKUP.
    { discriminate. }
    destruct (ident_beq i j) eqn:Hij.
    - simplify_eq.
      cbn [env_delete]. rewrite Hij. simpl.
      iApply biproset_tensor_right_unit.
    - cbn [env_delete]. rewrite Hij. simpl.
      iApply biproset_tensor_hom.
      iSplitL.
      + iApply IH. done.
      + iApply biproset_refl.
  Qed.

  Lemma bpenv_drop_unit Γ i Q
      (LOOKUP : env_lookup i Γ = Some (proset_unit _ X)) :
    bpenv_entails X (env_delete i Γ) Q
      ⊢ bpenv_entails X Γ Q.
  Proof.
    iIntros "H".
    iApply biproset_trans.
    iSplitR "H".
    - iApply (bpenv_delete_unit Γ i LOOKUP).
    - iExact "H".
  Qed.

  Lemma bpenv_singleton_refl i x :
    ⊢ bpenv_entails X (Esnoc Enil i x) x.
  Proof.
    iApply biproset_tensor_left_unit.
  Qed.

  Lemma bpenv_frame Γ Γ' i R P Q
      (PARTITION :
        bpenv_partition [i] Γ = Some (Esnoc Enil i R, Γ'))
      `{!BiProsetFrame X R P Q} :
    bpenv_entails X Γ' Q ⊢ bpenv_entails X Γ P.
  Proof.
    iIntros "HQ".
    iApply biproset_trans.
    iSplitL "HQ".
    - iApply
        (bpenv_partition_entails [i] Γ (Esnoc Enil i R) Γ'
          R Q PARTITION).
      iSplitR "HQ".
      + iApply bpenv_singleton_refl.
      + iExact "HQ".
    - iApply biproset_frame.
  Qed.

  Lemma bpenv_rename Γ Γ' i j x Q
      (LOOKUP : env_lookup i Γ = Some x)
      (REPLACE : bpenv_replace i j x Γ = Some Γ') :
    bpenv_entails X Γ' Q ⊢ bpenv_entails X Γ Q.
  Proof.
    iIntros "H".
    iApply biproset_trans.
    iSplitR "H".
    - iApply (bpenv_replace_hom Γ Γ' i j x x LOOKUP REPLACE).
      iApply biproset_refl.
    - iExact "H".
  Qed.

  Lemma bpenv_destruct Γ Γ' i i1 i2 x1 x2 Q
      (LOOKUP :
        env_lookup i Γ =
          Some (proset_tensor _ X x1 x2))
      (SPLIT : bpenv_split i i1 i2 x1 x2 Γ = Some Γ') :
    bpenv_entails X Γ' Q ⊢ bpenv_entails X Γ Q.
  Proof.
    iIntros "H".
    iApply biproset_trans.
    iSplitR "H".
    - iApply (bpenv_split_hom Γ Γ' i i1 i2 x1 x2 LOOKUP SPLIT).
    - iExact "H".
  Qed.

  Lemma bpenv_pose Γ Γ' i j x y Q
      (LOOKUP : env_lookup i Γ = Some x)
      (REPLACE : bpenv_replace i j y Γ = Some Γ') :
    proset_hom _ X x y ∗ bpenv_entails X Γ' Q
      ⊢ bpenv_entails X Γ Q.
  Proof.
    iIntros "[Hxy H]".
    iApply biproset_trans.
    iSplitR "H".
    - iApply (bpenv_replace_hom Γ Γ' i j x y LOOKUP REPLACE).
      iExact "Hxy".
    - iExact "H".
  Qed.

  Lemma bpenv_pose_selected ids Γ Γ1 Γ2 Γ' i j x y Q
      (PARTITION : bpenv_partition ids Γ = Some (Γ1, Γ2))
      (REPLACE :
        bpenv_replace i j y (Esnoc Γ2 i x) = Some Γ') :
    proset_hom _ X x y ∗
      (bpenv_entails X Γ1 x ∗ bpenv_entails X Γ' Q)
      ⊢ bpenv_entails X Γ Q.
  Proof.
    iIntros "[Hxy [Hx HQ]]".
    iApply (bpenv_assert ids Γ Γ1 Γ2 i x Q PARTITION).
    iSplitL "Hx"; first iExact "Hx".
    iApply (bpenv_pose (Esnoc Γ2 i x) Γ' i j x y Q
      (env_lookup_snoc Γ2 i x) REPLACE).
    iFrame.
  Qed.
End bi_proset_laws.

(** * Proof-state notation *)

Global Arguments bpenv_entails {_} _ _%_proof_scope _.

Notation "Γp '--------------------------------------' □ Γs '--------------------------------------' ∗ Γb '--------------------------------------' ⊗ Q" :=
  (envs_entails (Envs Γp Γs _) (bpenv_entails _ Γb Q))
  (at level 1, Γs at level 200, Γb at level 200, Q at level 200,
   left associativity,
   format "'[' Γp '--------------------------------------' □ '//' Γs '--------------------------------------' ∗ '//' Γb '--------------------------------------' ⊗ '//' Q ']'",
   only printing) : stdpp_scope.
Notation "Γs '--------------------------------------' ∗ Γb '--------------------------------------' ⊗ Q" :=
  (envs_entails (Envs Enil Γs _) (bpenv_entails _ Γb Q))
  (at level 1, Γb at level 200, Q at level 200, left associativity,
   format "'[' Γs '--------------------------------------' ∗ '//' Γb '--------------------------------------' ⊗ '//' Q ']'",
   only printing) : stdpp_scope.
Notation "Γp '--------------------------------------' □ Γb '--------------------------------------' ⊗ Q" :=
  (envs_entails (Envs Γp Enil _) (bpenv_entails _ Γb Q))
  (at level 1, Γb at level 200, Q at level 200, left associativity,
   format "'[' Γp '--------------------------------------' □ '//' Γb '--------------------------------------' ⊗ '//' Q ']'",
   only printing) : stdpp_scope.
Notation "Γp '--------------------------------------' □ Γs '--------------------------------------' ∗ Q" :=
  (envs_entails (Envs Γp Γs _) (bpenv_entails _ Enil Q))
  (at level 1, Γs at level 200, Q at level 200, left associativity,
   format "'[' Γp '--------------------------------------' □ '//' Γs '--------------------------------------' ∗ '//' Q ']'",
   only printing) : stdpp_scope.
Notation "Γb '--------------------------------------' ⊗ Q" :=
  (envs_entails (Envs Enil Enil _) (bpenv_entails _ Γb Q))
  (at level 1, Q at level 200, left associativity,
   format "'[' Γb '--------------------------------------' ⊗ '//' Q ']'",
   only printing) : stdpp_scope.
Notation "Γs '--------------------------------------' ∗ Q" :=
  (envs_entails (Envs Enil Γs _) (bpenv_entails _ Enil Q))
  (at level 1, Q at level 200, left associativity,
   format "'[' Γs '--------------------------------------' ∗ '//' Q ']'",
   only printing) : stdpp_scope.
Notation "Γp '--------------------------------------' □ Q" :=
  (envs_entails (Envs Γp Enil _) (bpenv_entails _ Enil Q))
  (at level 1, Q at level 200, left associativity,
   format "'[' Γp '--------------------------------------' □ '//' Q ']'",
   only printing) : stdpp_scope.
Notation "'--------------------------------------' ⊗ Q" :=
  (envs_entails (Envs Enil Enil _) (bpenv_entails _ Enil Q))
  (at level 1, Q at level 200,
   format "'[' '--------------------------------------' ⊗ '//' Q ']'",
   only printing) : stdpp_scope.

(** * Proof-mode tactics *)

(** ** User guide

The [j] tactics extend IPM with a third, linear context of BiProset
objects.  Ordinary [i] tactics remain available for the intuitionistic and
spatial BI contexts.  A proof state therefore has the following shape:

{[
  intuitionistic BI context
  --------------------------------------□
  spatial BI context
  --------------------------------------∗
  BiProset tensor context
  --------------------------------------⊗
  BiProset goal
]}

- [jStartProof] enters the mode.  Use [jStartProof (X)] when the
  BiProset cannot be inferred.  [jStopProof] exposes the underlying
  [proset_hom], removing its implicit leading unit unless the BiProset
  context is empty.
- [jIntros "(H1 & H2)"] and [jDestruct "H" as "(H1 & H2)"] move tensor
  components into the BiProset context.
- [jIntros "HP" "HX"] first introduces [HP] into the IPM context and then
  introduces [HX] into the BiProset context.
- [jApply "H"] closes a goal with a matching BiProset hypothesis, or
  applies an IPM hypothesis containing a BiProset morphism.
- [jFrame "H"] removes a matching named hypothesis from a possibly nested
  tensor goal.  [jFrame] tries every BiProset hypothesis, skipping those
  that do not occur in the goal.
- [jUnitIntro] closes a monoidal-unit goal when the BiProset context is
  empty.  A unit-valued hypothesis can be removed with
  [jDestruct "H" as "_"].
- [jSplitL "H1 H2"] and [jSplitR "H1 H2"] split a tensor goal.  The names
  may come from either the IPM spatial context or the BiProset context.
- [jAssert P with "[H1 H2]" as "H"] is a cut.  Its first goal proves [P]
  from the selected hypotheses; its second goal replaces them with [H : P].
- [jPoseProof "REF" with "H1" as "H2"] applies a morphism to one BiProset
  hypothesis.  [REF] may be spatial or persistent.  Omitting [with]
  searches for a matching hypothesis.
- [jPoseProof "REF" with "[H1 H2]" as "H"] applies a morphism to several
  BiProset hypotheses.  It leaves a separate first goal from their tensor
  to the source of [REF], and continues with them replaced by its target.
- [jPoseProof thm with "[HP]" "[HX]" as "HY"] first specializes [thm]
  with IPM hypotheses [HP], then applies the resulting morphism to the
  selected BiProset hypotheses [HX].  Unresolved Coq premises of [thm]
  become goals first, followed by the IPM premise selected by [HP], the
  BiProset source selected by [HX], and the continuation goal.

Introduction patterns follow IPM syntax.  Bracketed [with] arguments are
IPM specialization patterns; unbracketed arguments denote one hypothesis.
*)

Ltac jStartProof :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (bpenv_entails _ _ _) => idtac
  | |- envs_entails _ (@proset_hom _ ?X ?x ?Q) =>
      let H := iFresh in
      iApply (bpenv_start X H x Q)
  | |- ?G => fail "jStartProof: not a BiProset entailment:" G
  end.

Ltac jStartProofIn X :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (bpenv_entails X _ _) => idtac
  | |- envs_entails ?Δ ?P =>
      lazymatch P with
      | ?hom ?x ?Q =>
          first
            [ change (envs_entails Δ (@proset_hom _ X x Q));
              let H := iFresh in
              iApply (bpenv_start X H x Q)
            | fail "jStartProof: goal is not a morphism of" X ]
      | _ => fail "jStartProof: goal is not a binary morphism"
      end
  | |- ?G => fail "jStartProof: not a BiProset entailment:" G
  end.

Tactic Notation "jStartProof" "(" constr(X) ")" :=
  jStartProofIn X.

Ltac jEval t :=
  eval cbv [
    env_lookup env_replace env_delete env_app pm_option_bind
    bpenv_replace bpenv_split bpenv_remove_ident
    bpenv_partition mbind option_bind
    ident_beq positive_beq string_beq ascii_beq beq
  ] in t.

Tactic Notation "jStopProof" :=
  lazymatch goal with
  | |- envs_entails _ (bpenv_entails ?X ?Γ ?Q) =>
      iApply (bpenv_stop X Γ Q);
      cbn [bpenv_interp_stripped bpenv_interp_stripped_go]
  | |- _ => fail "jStopProof: BiProset proof mode not started"
  end.

Tactic Notation "jUnitIntro" :=
  jStartProof;
  lazymatch goal with
  | |- envs_entails ?Δ (bpenv_entails ?X Enil ?Q) =>
      first
        [ change
            (envs_entails Δ
              (bpenv_entails X Enil (proset_unit _ X)));
          unfold bpenv_entails; simpl;
          iApply biproset_refl
        | fail "jUnitIntro: goal is not the monoidal unit:" Q ]
  | |- envs_entails _ (bpenv_entails _ ?Γ _) =>
      fail "jUnitIntro: BiProset context is not empty:" Γ
  end.

Ltac jLookup Γ H :=
  let result := jEval (env_lookup H Γ) in
  lazymatch result with
  | Some ?x => constr:(x)
  | None =>
      let H := pretty_ident H in
      fail "BiProset hypothesis" H "not found"
  | ?result => fail "jLookup: could not reduce lookup" result
  end.

Ltac jAsIdent H :=
  lazymatch type of H with
  | ident => H
  | string => constr:(INamed H)
  | ?T => fail "expected a BiProset hypothesis identifier, got" T
  end.

Ltac jRename H Hnew :=
  jStartProof;
  lazymatch goal with
  | |- envs_entails _ (bpenv_entails ?X ?Γ ?Q) =>
      let x := jLookup Γ H in
      let result := jEval (bpenv_replace H Hnew x Γ) in
      lazymatch result with
      | Some ?Γ' =>
          iApply (bpenv_rename X Γ Γ' H Hnew x Q eq_refl eq_refl)
      | None =>
          let Hnew := pretty_ident Hnew in
          fail "jRename:" Hnew "not fresh"
      end
  end.

Ltac jDestructHyp H pat :=
  lazymatch pat with
  | IIdent ?Hnew => jRename H Hnew
  | IFresh =>
      let Hnew := iFresh in
      jRename H Hnew
  | IList [[?pat1; ?pat2]] =>
      jStartProof;
      lazymatch goal with
      | |- envs_entails _ (bpenv_entails ?X ?Γ ?Q) =>
          let x := jLookup Γ H in
          lazymatch x with
          | ?tensor ?x1 ?x2 =>
              let expected :=
                constr:(proset_tensor _ X x1 x2) in
              first
                [ unify x expected
                | let H := pretty_ident H in
                  fail "jDestruct:" H "does not contain a tensor" ];
              let H1 := iFresh in
              let H2 := iFresh in
              let result := jEval (bpenv_split H H1 H2 x1 x2 Γ) in
              lazymatch result with
              | Some ?Γ' =>
                  iApply (bpenv_destruct X Γ Γ' H H1 H2 x1 x2 Q
                    eq_refl eq_refl);
                  jDestructHyp H1 pat1;
                  jDestructHyp H2 pat2
              | None =>
                  fail "jDestruct: generated identifiers are not fresh"
              end
          | _ =>
              let H := pretty_ident H in
              fail "jDestruct:" H "does not contain a tensor"
          end
      end
  | IDrop =>
      jStartProof;
      lazymatch goal with
      | |- envs_entails _ (bpenv_entails ?X ?Γ ?Q) =>
          let x := jLookup Γ H in
          first
            [ unify x (proset_unit _ X)
            | let H := pretty_ident H in
              fail "jDestruct:" H "is not the monoidal unit" ];
          iApply (bpenv_drop_unit X Γ H Q eq_refl)
      end
  | _ => fail "jDestruct: unsupported introduction pattern"
  end.

Tactic Notation "jDestruct" constr(H) "as" constr(pat) :=
  let H := jAsIdent H in
  let pat := intro_pat.parse_one pat in
  jDestructHyp H pat.

Tactic Notation "jIntros" constr(pat) :=
  jStartProof;
  let pats := intro_pat.parse pat in
  lazymatch pats with
  | [?pat] =>
      lazymatch goal with
      | |- envs_entails _
          (bpenv_entails _ (Esnoc Enil ?H _) _) =>
          jDestructHyp H pat
      | _ => fail "jIntros: BiProset context is not empty"
      end
  | _ => fail "jIntros: expected one introduction pattern"
  end.

Tactic Notation "jIntros" constr(ipat) constr(jpat) :=
  iIntros ipat;
  jIntros jpat.

Tactic Notation "jIntros" "(" constr(X) ")" constr(pat) :=
  jStartProofIn X;
  let pats := intro_pat.parse pat in
  lazymatch pats with
  | [?pat] =>
      lazymatch goal with
      | |- envs_entails _
          (bpenv_entails X (Esnoc Enil ?H _) _) =>
          jDestructHyp H pat
      | _ => fail "jIntros: BiProset context is not empty"
      end
  | _ => fail "jIntros: expected one introduction pattern"
  end.

(* Split selectors range over both the IPM and BiProset contexts. *)
Ltac jClassifySplitHyps Δ Γ ids :=
  lazymatch ids with
  | [] => constr:((@nil ident, @nil ident))
  | ?H :: ?ids =>
      let classified := jClassifySplitHyps Δ Γ ids in
      lazymatch classified with
      | (?iids, ?jids) =>
          let jresult := jEval (env_lookup H Γ) in
          let iresult := eval pm_eval in (envs_lookup H Δ) in
          lazymatch jresult with
          | Some _ =>
              lazymatch iresult with
              | Some _ =>
                  let H := pretty_ident H in
                  fail "jSplit:" H "is ambiguous"
              | None => constr:((iids, H :: jids))
              end
          | None =>
              lazymatch iresult with
              | Some _ => constr:((H :: iids, jids))
              | None =>
                  let H := pretty_ident H in
                  fail "jSplit: hypothesis" H "not found"
              | ?result =>
                  fail "jSplit: could not inspect IPM lookup" result
              end
          | ?result =>
              fail "jSplit: could not inspect BiProset lookup" result
          end
      | ?classified =>
          fail "jSplit: could not classify hypotheses" classified
      end
  | ?ids => fail "jSplit: could not parse hypotheses" ids
  end.

Ltac jSplitIPM d ids :=
  eapply coq_tactics.tac_sep_split with d ids _ _;
    [ tc_solve
    | pm_reduce;
      lazymatch goal with
      | |- False => fail "jSplit: could not split the IPM context"
      | _ => split
      end ].

Ltac jSplitCoreIds d ids :=
  jStartProof;
  lazymatch goal with
  | |- envs_entails ?Δ (bpenv_entails ?X ?Γ ?Q) =>
      let classified := jClassifySplitHyps Δ Γ ids in
      lazymatch classified with
      | (?iids, ?jids) =>
          lazymatch Q with
          | ?tensor ?x ?y =>
              let expected := constr:(proset_tensor _ X x y) in
              first
                [ unify Q expected
                | fail "jSplit: goal does not contain a tensor" ];
              let result := jEval (bpenv_partition jids Γ) in
              lazymatch result with
              | Some (?Γ1, ?Γ2) =>
                  lazymatch d with
                  | Left =>
                      iApply (bpenv_partition_entails
                        X jids Γ Γ1 Γ2 x y eq_refl);
                      jSplitIPM Left iids
                  | Right =>
                      iApply (bpenv_partition_entails_right
                        X jids Γ Γ1 Γ2 x y eq_refl);
                      jSplitIPM Right iids
                  | ?d => fail "jSplit: invalid direction" d
                  end
              | None => fail "jSplit: could not split the BiProset context"
              | ?result =>
                  fail "jSplit: could not reduce BiProset split" result
              end
          | _ => fail "jSplit: goal does not contain a tensor"
          end
      | ?classified =>
          fail "jSplit: could not classify hypotheses" classified
      end
  | |- ?G => fail "jSplit: not in BiProset proof mode:" G
  end.

Ltac jSplitCore d Hs :=
  let ids := String.words Hs in
  let ids := eval vm_compute in (INamed <$> ids) in
  jSplitCoreIds d ids.

Tactic Notation "jSplitL" constr(Hs) := jSplitCore Left Hs.
Tactic Notation "jSplitR" constr(Hs) := jSplitCore Right Hs.
Tactic Notation "jSplitL" := jSplitCore Right "".
Tactic Notation "jSplitR" := jSplitCore Left "".

Ltac jFrameHyp H :=
  jStartProof;
  lazymatch goal with
  | |- envs_entails _ (bpenv_entails ?X ?Γ ?P) =>
      let result := jEval (env_lookup H Γ) in
      lazymatch result with
      | Some ?R =>
          let partition := jEval (bpenv_partition [H] Γ) in
          lazymatch partition with
          | Some (Esnoc Enil H R, ?Γ') =>
              let Q := open_constr:(_ : X) in
              first
                [ let frame :=
                    constr:(
                      ltac:(tc_solve) : BiProsetFrame X R P Q) in
                  iApply
                    (@bpenv_frame _ X Γ Γ' H R P Q eq_refl frame);
                  try jUnitIntro
                | let H := pretty_ident H in
                  fail "jFrame: cannot frame BiProset hypothesis" H ]
          | ?partition =>
              fail "jFrame: could not isolate BiProset hypothesis"
                partition
          end
      | None =>
          let H := pretty_ident H in
          fail "jFrame: BiProset hypothesis" H "not found"
      | ?result =>
          fail "jFrame: could not inspect BiProset lookup" result
      end
  | |- ?G => fail "jFrame: not in BiProset proof mode:" G
  end.

Ltac jFrameHyps ids :=
  lazymatch ids with
  | [] => idtac
  | ?H :: ?ids => jFrameHyp H; jFrameHyps ids
  end.

Ltac jFrameCore Hs :=
  let ids := String.words Hs in
  let ids := eval vm_compute in (INamed <$> ids) in
  lazymatch ids with
  | [] => fail "jFrame: expected at least one BiProset hypothesis"
  | _ => jFrameHyps ids
  end.

Ltac jFrameAny :=
  jStartProof;
  lazymatch goal with
  | |- envs_entails _ (bpenv_entails _ ?Γ _) =>
      let rec go ids :=
        lazymatch ids with
        | [] => try jUnitIntro
        | ?H :: ?ids => try jFrameHyp H; go ids
        end in
      let ids := eval lazy in (env_dom Γ) in
      go ids
  end.

Tactic Notation "jFrame" constr(Hs) := jFrameCore Hs.
Tactic Notation "jFrame" := jFrameAny.

Ltac jFresh Γ :=
  let H := iFresh in
  let result := jEval (env_lookup H Γ) in
  lazymatch result with
  | None => H
  | Some _ => jFresh Γ
  | ?result => fail "jFresh: could not inspect BiProset context" result
  end.

Ltac jParseSpatialGoal tac Hs :=
  let pats := spec_pat.parse Hs in
  lazymatch pats with
  | [SGoal (SpecGoal GSpatial false [] ?ids false)] => ids
  | _ =>
      fail tac
        "expects one spatial selection pattern of the form [H1 .. Hn]"
  end.

Ltac jAssertCore P ids pat :=
  jStartProof;
  lazymatch goal with
  | |- envs_entails ?Δ (bpenv_entails ?X ?Γ ?Q) =>
      let classified := jClassifySplitHyps Δ Γ ids in
      lazymatch classified with
      | (?iids, ?jids) =>
          let result := jEval (bpenv_partition jids Γ) in
          lazymatch result with
          | Some (?Γ1, ?Γ2) =>
              let Hnew := jFresh Γ2 in
              iApply
                (bpenv_assert X jids Γ Γ1 Γ2 Hnew P Q eq_refl);
              jSplitIPM Left iids;
              [ idtac | jDestructHyp Hnew pat ]
          | None => fail "jAssert: could not split the BiProset context"
          | ?result =>
              fail "jAssert: could not reduce BiProset split" result
          end
      | ?classified =>
          fail "jAssert: could not classify hypotheses" classified
      end
  | |- ?G => fail "jAssert: not in BiProset proof mode:" G
  end.

Tactic Notation "jAssert" open_constr(P)
    "with" constr(Hs) "as" constr(pat) :=
  let ids := jParseSpatialGoal "jAssert:" Hs in
  let pat := intro_pat.parse_one pat in
  jAssertCore P ids pat.

Ltac jFind Γ x :=
  lazymatch Γ with
  | Esnoc ?Γ ?H ?y =>
      lazymatch x with
      | y => constr:(H)
      | _ => jFind Γ x
      end
  | Enil => fail 1
  end.

Ltac jWithMorphism X P tac :=
  lazymatch P with
  | @proset_hom _ ?X' ?x ?y =>
      unify X X';
      tac x y
  | ?hom ?x ?y =>
      let expected := constr:(proset_hom _ X x y) in
      first
        [ unify P expected; tac x y
        | fail "expected a BiProset morphism, got" P ]
  | _ => fail "expected a BiProset morphism, got" P
  end.

(* A BiProset name acts as an exact hypothesis; other terms are morphisms. *)
Ltac jApplyBpenv H :=
  lazymatch goal with
  | |- envs_entails _ (bpenv_entails ?X ?Γ ?Q) =>
      lazymatch Γ with
      | Esnoc Enil ?H' ?x =>
          first
            [ unify H H'; unify x Q;
              iApply (bpenv_singleton_refl X H x)
            | let H := pretty_ident H in
              fail "jApply: BiProset hypothesis" H
                "does not match the goal" ]
      | _ =>
          let H := pretty_ident H in
          fail "jApply: BiProset hypothesis" H
            "is not the only hypothesis"
      end
  end.

Ltac jApplyMorphismCore Hm X Γ Q x y :=
  first
    [ unify y Q
    | fail "jApply: morphism target does not match the goal" ];
  iApply (bpenv_apply X Γ x y);
  iFrame Hm.

Ltac jApplyMorphism lem :=
  let Hm := iFresh in
  let ipat := constr:(IIdent Hm) in
  iPoseProof lem as ipat;
  lazymatch goal with
  | |- envs_entails ?Δ (bpenv_entails ?X ?Γ ?Q) =>
      let result := eval pm_eval in (envs_lookup Hm Δ) in
      lazymatch result with
      | Some (?p, ?P) =>
          let go x y := jApplyMorphismCore Hm X Γ Q x y in
          jWithMorphism X P go
      | None => fail "jApply: internal IPM hypothesis not found"
      end
  end.

Ltac jApplyCore lem :=
  jStartProof;
  lazymatch type of lem with
  | string =>
      let H := constr:(INamed lem) in
      lazymatch goal with
      | |- envs_entails _ (bpenv_entails _ ?Γ _) =>
          let result := jEval (env_lookup H Γ) in
          lazymatch result with
          | Some _ => jApplyBpenv H
          | None => jApplyMorphism lem
          end
      end
  | ident => jApplyBpenv lem
  | _ => jApplyMorphism lem
  end.

Tactic Notation "jApply" open_constr(lem) := jApplyCore lem.

Ltac jClearPersistent H p :=
  lazymatch p with
  | true => iClear H
  | false => idtac
  end.

Ltac jPoseMorphismCore Hm p H pat X Γ Q x y :=
  let x' := jLookup Γ H in
  first
    [ unify x x'
    | let H := pretty_ident H in
      fail "jPoseProof: morphism source does not match" H ];
  let Hnew := iFresh in
  let replaced := jEval (bpenv_replace H Hnew y Γ) in
  lazymatch replaced with
  | Some ?Γ' =>
      iApply (bpenv_pose X Γ Γ' H Hnew x y Q eq_refl eq_refl);
      iFrame Hm;
      jClearPersistent Hm p;
      jDestructHyp Hnew pat
  | None => fail "jPoseProof: generated identifier is not fresh"
  end.

Ltac jPoseMorphism Hm H pat :=
  lazymatch goal with
  | |- envs_entails ?Δ (bpenv_entails ?X ?Γ ?Q) =>
      let result := eval pm_eval in (envs_lookup Hm Δ) in
      lazymatch result with
      | Some (?p, ?P) =>
          let go x y := jPoseMorphismCore Hm p H pat X Γ Q x y in
          jWithMorphism X P go
      | None => fail "jPoseProof: internal IPM hypothesis not found"
      end
  end.

Ltac jAddIdent H ids :=
  lazymatch ids with
  | [] => constr:([H])
  | ?H' :: ?ids' =>
      first
        [ constr_eq H H'; constr:(ids)
        | let ids'' := jAddIdent H ids' in
          constr:(H' :: ids'') ]
  end.

Ltac jSpatialHypIds Δ ids :=
  lazymatch ids with
  | [] => constr:(@nil ident)
  | ?H :: ?ids =>
      let ids' := jSpatialHypIds Δ ids in
      let result := eval pm_eval in (envs_lookup H Δ) in
      lazymatch result with
      | Some (true, _) => ids'
      | Some (false, _) => constr:(H :: ids')
      | None =>
          let H := pretty_ident H in
          fail "jPoseProof: IPM hypothesis" H "not found"
      | ?result =>
          fail "jPoseProof: could not inspect IPM lookup" result
      end
  end.

Ltac jMorphismHypIds Δ lem ids :=
  lazymatch type of lem with
  | string =>
      let H := constr:(INamed lem) in
      let result := eval pm_eval in (envs_lookup H Δ) in
      lazymatch result with
      | Some (true, _) => ids
      | Some (false, _) => jAddIdent H ids
      | _ => ids
      end
  | _ => ids
  end.

Ltac jPoseProofAt lem iids H pat :=
  jStartProof;
  lazymatch goal with
  | |- envs_entails ?Δ (bpenv_entails ?X ?Γ ?Q) =>
      let iids := jMorphismHypIds Δ lem iids in
      let x := jLookup Γ H in
      let y := open_constr:(_ : X) in
      let Hnew := jFresh Γ in
      let replaced := jEval (bpenv_replace H Hnew y Γ) in
      lazymatch replaced with
      | Some ?Γ' =>
          iApply (bpenv_pose X Γ Γ' H Hnew x y Q eq_refl eq_refl);
          jSplitIPM Left iids;
          [ iApply lem | jDestructHyp Hnew pat ]
      | None => fail "jPoseProof: generated identifier is not fresh"
      | ?result =>
          fail "jPoseProof: could not replace BiProset hypothesis" result
      end
  | |- ?G => fail "jPoseProof: not in BiProset proof mode:" G
  end.

Ltac jPoseProofMany lem iids ids pat :=
  jStartProof;
  lazymatch goal with
  | |- envs_entails ?Δ (bpenv_entails ?X ?Γ _) =>
      let iids := jMorphismHypIds Δ lem iids in
      let classified := jClassifySplitHyps Δ Γ ids in
      lazymatch classified with
      | ([], ?jids) =>
          let result := jEval (bpenv_partition jids Γ) in
          lazymatch result with
          | Some (?Γ1, ?Γ2) =>
              let x := open_constr:(_ : X) in
              let y := open_constr:(_ : X) in
              let Hsrc := jFresh Γ in
              let Hnew := jFresh (Esnoc Γ Hsrc x) in
              let replaced :=
                jEval
                  (bpenv_replace Hsrc Hnew y (Esnoc Γ2 Hsrc x)) in
              lazymatch replaced with
              | Some ?Γ' =>
                  iApply
                    (bpenv_pose_selected X jids Γ Γ1 Γ2 Γ'
                      Hsrc Hnew x y _ eq_refl eq_refl);
                  jSplitIPM Left iids;
                  [ iApply lem
                  | let noids := constr:(@nil ident) in
                    jSplitIPM Left noids;
                    [ idtac | jDestructHyp Hnew pat ] ]
              | None =>
                  fail "jPoseProof: generated identifier is not fresh"
              | ?result =>
                  fail
                    "jPoseProof: could not construct replacement context"
                    result
              end
          | None => fail "jPoseProof: could not split BiProset context"
          | ?result =>
              fail "jPoseProof: could not reduce BiProset split" result
          end
      | (?found, _) =>
          fail "jPoseProof: the selection contains IPM hypotheses" found
      end
  | |- ?G => fail "jPoseProof: not in BiProset proof mode:" G
  end.

Ltac jPoseProofAuto lem pat :=
  jStartProof;
  let Hm := iFresh in
  let ipat := constr:(IIdent Hm) in
  iPoseProof lem as ipat;
  [.. |
  lazymatch goal with
  | |- envs_entails ?Δ (bpenv_entails ?X ?Γ _) =>
      let result := eval pm_eval in (envs_lookup Hm Δ) in
      lazymatch result with
      | Some (?p, ?P) =>
          let go x y :=
            first
              [ let H := jFind Γ x in jPoseMorphism Hm H pat
              | fail
                  "jPoseProof: morphism source not found in BiProset context" ]
          in jWithMorphism X P go
      | None => fail "jPoseProof: internal IPM hypothesis not found"
      end
  end ].

Ltac jPoseProofWith lem iids Hs pat :=
  let pats := spec_pat.parse Hs in
  lazymatch pats with
  | [SIdent ?H []] => jPoseProofAt lem iids H pat
  | [SGoal (SpecGoal GSpatial false [] ?ids false)] =>
      jPoseProofMany lem iids ids pat
  | _ =>
      fail "jPoseProof: expected a hypothesis or one spatial selection"
        "pattern"
  end.

Tactic Notation "jPoseProof" open_constr(lem)
    "with" constr(Hs) "as" constr(pat) :=
  let pat := intro_pat.parse_one pat in
  let iids := constr:(@nil ident) in
  jPoseProofWith lem iids Hs pat.

Tactic Notation "jPoseProof" open_constr(lem)
    "with" constr(iHs) constr(jHs) "as" constr(pat) :=
  let pat := intro_pat.parse_one pat in
  jStartProof;
  lazymatch goal with
  | |- envs_entails ?Δ (bpenv_entails _ _ _) =>
      let pats := spec_pat.parse iHs in
      let ids :=
        lazymatch pats with
        | [SIdent ?H []] => constr:([H])
        | [SGoal (SpecGoal GSpatial false [] ?ids false)] => ids
        | _ =>
            fail "jPoseProof: expected an IPM hypothesis or one"
              "spatial selection pattern"
        end in
      let iids := jSpatialHypIds Δ ids in
      let lem := constr:((lem with iHs)) in
      jPoseProofWith lem iids jHs pat
  end.

Tactic Notation "jPoseProof" open_constr(lem) "as" constr(pat) :=
  let pat := intro_pat.parse_one pat in
  jPoseProofAuto lem pat.
