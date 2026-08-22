From Stdlib Require Import String.
From Stdlib Require Export ZArith.
From Stdlib Require Export Znumtheory.
From Stdlib Require Export List.
From Stdlib Require Export Bool.
From CRIS.lib Require Export sflib.
From Paco Require Export paco.
From Stdlib Require Export Basics.
From Stdlib Require Import Relations.
From Stdlib Require Export RelationClasses.
From Stdlib Require Import Wellfounded.
From Stdlib Require Export Classical_Prop.
From Stdlib Require Export Lia.
From CRIS.lib Require Export StdAxioms.
From Stdlib Require Import Relation_Operators.
From Stdlib Require Export List.
From Stdlib Require Export ClassicalDescription.
From Stdlib Require Export Program.
From Stdlib Require Export Morphisms.
From Stdlib Require Import Sorting.Permutation.
From Stdlib Require Import Program.
From Stdlib Require Import Classical_Pred_Type.

Set Implicit Arguments.

Global Generalizable All Variables.
(* Global Unset Transparent Obligations. *)
Add Search Blacklist "_obligation_".

(* TODO : if it is mature enough, move it to sflib & remove this file *)

Global Program Instance incl_PreOrder {A} : PreOrder (@incl A).
Next Obligation. ii. ss. Qed.
Next Obligation. ii. eauto. Qed.

Hint Unfold Basics.compose : core.

Hint Unfold flip : core.

Definition sumbool_to_bool {P Q : Prop} (a : {P} + {Q}) : bool := if a then true else false.

Coercion sumbool_to_bool : sumbool >-> bool.

Ltac is_prop H :=
  let ty := type of H in
  match type of ty with
  | Prop => idtac
  | _ => fail 1
  end.

Ltac clear_until id :=
  on_last_hyp ltac:(fun id' => match id' with
                               | id => idtac
                               | _ => clear id'; clear_until id
                               end).

Ltac sp H :=
  let TAC := ss; eauto in
  let ty := type of H in
  match eval hnf in ty with
  | forall (a : ?A), _ =>
    (* let A := (eval compute in _A) in *)
    match goal with
    | [a0 : A, a1 : A, a2 : A, a3 : A, a4 : A, a5 : A |- _] => fail 2 "6 candidates!" a0 "," a1 "," a2 "," a3 "," a4 "," a5
    | [a0 : A, a1 : A, a2 : A, a3 : A, a4 : A |- _] => fail 2 "5 candidates!" a0 "," a1 "," a2 "," a3 "," a4
    | [a0 : A, a1 : A, a2 : A, a3 : A |- _] => fail 2 "4 candidates!" a0 "," a1 "," a2 "," a3
    | [a0 : A, a1 : A, a2 : A |- _] => fail 2 "3 candidates!" a0 "," a1 "," a2
    | [a0 : A, a1 : A |- _] => fail 2 "2 candidates!" a0 "," a1
    | [a0 : A |- _] => specialize (H a0)
    | _ =>
      tryif is_prop A
      then
        let name := fresh in
        assert(name : A) by TAC; specialize (H name); clear name
      else
        fail 2 "No specialization possible!"
    end
  | _ => fail 1 "Nothing to specialize!"
  end.

(*
Goal let my_nat := nat in
     let my_f := my_nat -> Prop in
     forall (f : my_f) (g : nat -> Prop) (x : nat) (y : my_nat), False.
  i. sp f. sp g.
Abort.
*)

(* copied from : https://robbertkrebbers.nl/research/ch2o/tactics.html *)
Hint Extern 998 (_ = _) => f_equal : f_equal.
Hint Extern 999 => congruence : congruence.
Hint Extern 1000 => lia : lia.

Lemma find_map
      X Y (f : Y -> bool) (x2y : X -> Y) xs:
    find f (map x2y xs) = option_map x2y (find (f ∘ x2y) xs).
Proof. autounfold. ginduction xs; ii; ss. des_ifs; ss. Qed.

(* copied from promising/lib/Basic.v *)

Ltac refl := reflexivity.
Ltac etrans := etransitivity.
Ltac congr := congruence.

Hint Extern 997 => lia : lia.

Ltac simpl_bool := unfold Datatypes.is_true in *; unfold is_true in *; autorewrite with simpl_bool in *.
Ltac bsimpl := simpl_bool.

Ltac sym := symmetry.
Tactic Notation "sym" "in" hyp(H) := symmetry in H.

Global Opaque Z.mul.

Ltac et:= eauto.

Lemma cons_app
      X xhd (xtl : list X):
    xhd :: xtl = [xhd] ++ xtl.
Proof. ss. Qed.

Lemma list_map_injective A B (f : A -> B)
      (INJECTIVE : forall a0 a1 (EQ : f a0 = f a1), a0 = a1)
      l0 l1
      (LEQ : map f l0 = map f l1):
    l0 = l1.
Proof.
  revert l1 LEQ. induction l0; i; ss; destruct l1; ss. inv LEQ. f_equal; eauto.
Qed.

Lemma app_eq_inv
      A (x0 x1 y0 y1 : list A)
      (EQ : x0 ++ x1 = y0 ++ y1)
      (LEN : (length x0) = (length y0)):
    x0 = y0 /\ x1 = y1.
Proof.
  ginduction x0; ii; ss.
  { destruct y0; ss. }
  destruct y0; ss. clarify. exploit IHx0; eauto. i; des. clarify.
Qed.

Lemma firstn_S
      (A : Type) (l : list A) n:
      (le (Datatypes.length l) n /\ firstn (n + 1) l = firstn n l)
    \/ (lt n (Datatypes.length l) /\ exists x, firstn (n + 1) l = (firstn n l) ++ [x]).
Proof.
  ginduction l; i; try sfby (left; do 2 rewrite firstn_nil; split; ss; lia). destruct n.
  { right. ss. split; try lia. eauto. }
  specialize (IHl n). ss. des.
  - left. split; try lia. rewrite IHl0. ss.
  - right. split; try lia. rewrite IHl0. eauto.
Qed.

Lemma nodup_length
      X (xs : list X) x_dec
  :
    <<LEN : (length (nodup x_dec xs) <= length (xs))%nat>>
.
Proof.
  r.
  ginduction xs; ii; ss. exploit IHxs; et. i; des. des_ifs; ss; try rewrite x0; try lia.
Qed.

(* TODO : Coqlib? *)
Lemma nodup_app_l A (l0 l1 : list A)
      (ND : NoDup (l0 ++ l1))
  :
    NoDup l0.
Proof.
  induction l0.
  { econs. }
  ss. inv ND. econs; et.
  ii. eapply H1. eapply List.in_or_app. auto.
Qed.

Lemma nodup_app_r A (l0 l1 : list A)
      (ND : NoDup (l0 ++ l1))
  :
    NoDup l1.
Proof.
  induction l0; ss. inv ND. auto.
Qed.

Lemma nodup_comm A (l0 l1 : list A)
      (NODUP : NoDup (l0 ++ l1))
  :
    NoDup (l1 ++ l0).
Proof.
  eapply Permutation_NoDup; [|et].
  eapply Permutation_app_comm.
Qed.

Lemma NoDup_snoc
      X (x : X) xs
      (NIN : ~In x xs)
      (NDUP : NoDup xs)
  :
    <<NDUP : NoDup (xs ++ [x])>>
.
Proof.
  ginduction xs; ii; ss.
  - econs; et.
  - apply not_or_and in NIN. des.
    eapply NoDup_cons_iff in NDUP; des; ss.
    econs; et.
    + rewrite in_app_iff. apply and_not_or. esplits; et.
      * ss. ii; des; clarify.
    + eapply IHxs; et.
Qed.

Lemma NoDup_rev
      X (xs : list X)
      (UNIQ : NoDup xs)
  :
    <<UNIQ : NoDup (rev xs)>>
.
Proof.
  ginduction xs; ii; ss.
  inv UNIQ. eapply IHxs in H2.
  eapply NoDup_snoc; et. rewrite <- in_rev. ss.
Qed.

Lemma NoDup_app_disjoint A (l0 l1 : list A) (NODUP : NoDup (l0 ++ l1))
  :
    forall a (IN0 : List.In a l0) (IN1 : List.In a l1), False.
Proof.
  revert NODUP. induction l0; et. i. ss. des; ss.
  { subst. inv NODUP. eapply H1. eapply in_or_app. auto. }
  { eapply IHl0; et. inv NODUP. ss. }
Qed.

Lemma func_ext_rev
      A B
      (a : A)
      (f g : A -> B)
      (EQ : f = g)
  :
    f a = g a
.
Proof.
  clarify.
Qed.

(*** TODO : move to CoqlibC ***)
Lemma NoDup_inj_aux
      X Y (f : X -> Y) xs
      (NODUP : NoDup (map f xs))
      x0 x1
      (NEQ : x0 <> x1)
      (IN0 : In x0 xs)
      (IN1 : In x1 xs)
  :
    f x0 <> f x1
.
Proof.
  ginduction xs; i; ss.
  inv NODUP. des; clarify; et.
  - intro T. rewrite <- T in *. eapply H1. erewrite in_map_iff. eauto.
  - intro T. rewrite T in *. eapply H1. erewrite in_map_iff. eauto.
Qed.

Module Type SEAL.
  Parameter sealing : string -> forall X : Type, X -> X.
  Parameter sealing_eq : forall key X (x : X), sealing key x = x.
End SEAL.
Module Seal : SEAL.
  Definition sealing (_ : string) X (x : X) := x.
  Lemma sealing_eq key X (x : X) : sealing key x = x.
  Proof. refl. Qed.
End Seal.

Ltac seal_with key x :=
  replace x with (Seal.sealing key x); [|eapply Seal.sealing_eq].
Ltac seal x :=
  let key := fresh "key" in
  assert (key:= "_default_");
  seal_with key x.
Ltac unseal x :=
  match (type of x) with
  | string => (hrepeat do 1 rewrite (@Seal.sealing_eq x)); try clear x
  | _ => (hrepeat do 1 rewrite (@Seal.sealing_eq _ _ x));
         hrepeat do 1 match goal with
                | [ H : string |- _ ] => clear H
                end
  end
.

Notation "☃ y" := (Seal.sealing _ y) (at level 60, only printing).
Goal forall x, 5 + 5 = x. i. seal 5. seal x. Fail progress cbn. unseal key0. unseal 5. progress cbn. Abort.
Goal forall x y z, x + y = z. i. seal x. seal y. unseal y. unseal key. Abort.
Goal forall x y z, x + y = z. i. seal_with "a" x. seal_with "b" y. unseal "a". unseal "b". Abort.

Notation "f ∘ g" := (fun x => (f (g x))).

Definition map_fst A B C (f : A -> C) : A * B -> C * B := fun '(a, b) => (f a, b).
Definition map_snd A B C (f : B -> C) : A * B -> A * C := fun '(a, b) => (a, f b).

Lemma fst_map_snd {A B C} f:
  (fst ∘ @map_snd A B C f) = fst.
Proof.
  extensionalities. destruct H. s. eauto.
Qed.

Notation "(∘)" := (fun g f => g ∘ f) (at level 0, left associativity).

Definition or_else X (ox : option X) (d : X) := match ox with | Some x => x | None => d end.

Lemma flat_map_map A B C (f : A -> B) (g : B -> list C) (l : list A)
  :
    flat_map g (map f l) = flat_map (g ∘ f) l.
Proof.
  induction l; ss. f_equal; auto.
Qed.

Lemma map_flat_map A B C (f : A -> list B) (g : B -> C) (l : list A)
  :
    List.map g (flat_map f l)
    =
    flat_map (List.map g) (List.map f l).
Proof.
  induction l; ss. rewrite List.map_app. f_equal; auto.
Qed.

Lemma flat_map_single A B (f : A -> B) (l : list A)
  :
    flat_map (fun a => [f a]) l
    =
    List.map f l.
Proof.
  induction l; ss.
Qed.

Global Open Scope nat_scope.

(* Lemmas about string *)

Lemma string_length_app (s1 s2: string):
  String.length (String.append s1 s2) = String.length s1 + String.length s2.
Proof.
  revert s2. induction s1; i; ss.
  fold append. rewrite IHs1. et.
Qed.
  
Definition strings_maxlen (l: list string) : nat :=
  list_max (List.map String.length l).

Fixpoint string_repeat (s: string) (n: nat) : string :=
  match n with
  | 0 => ""
  | S n' => String.append s (string_repeat s n')
  end.

Lemma string_repeat_length s n:
  String.length (string_repeat s n) = n * String.length s.
Proof.
  induction n; ss.
  rewrite string_length_app. rewrite IHn. et.
Qed.

Lemma strings_maxlen_app l1 l2:
  strings_maxlen (l1++l2) = max (strings_maxlen l1) (strings_maxlen l2).
Proof.
  revert l2. induction l1; et.
  i. s. unfold strings_maxlen in *. ss.
  rewrite IHl1. nia.
Qed.

Lemma strings_maxlen_notin s l
  (LONG: String.length s > strings_maxlen l)
  :
  ~ existsb (String.eqb s) l.
Proof.
  ii. eapply existsb_exists in H. des. eapply String.eqb_eq in H0; subst.
  revert_until l. induction l; i; ss.
  des; subst.
  - unfold strings_maxlen in LONG. ss. nia.
  - eapply IHl; et. unfold strings_maxlen in *. ss. nia.
Qed.

Lemma string_ex_not_in (l: list string):
  exists s, ~ In s l.
Proof.
  exists (string_repeat "H" (1 + strings_maxlen l)).
  ii. eapply strings_maxlen_notin; cycle 1.
  - eapply existsb_exists. esplits; [apply H|apply String.eqb_refl].
  - rewrite string_repeat_length. s. nia.
Qed.

From stdpp Require Import base list.

(* Lemmas about names *)
Definition maxlen (s : list string) : nat :=
  list_max (String.length <$> s).

Fixpoint mname_long (n : nat) : string :=
  match n with
  | 0 => ""
  | S n' => String.append "." (mname_long n')
  end.

Lemma mname_long_length n : String.length (mname_long n) = n.
Proof. induction n; ss. rewrite IHn. et. Qed.

Lemma elem_of_maxlen (fn : string) (s : list string) :
  fn ∈ s → String.length fn ≤ maxlen s.
Proof. i; eapply max_list_elem_of_le, elem_of_list_fmap; esplits; eauto. Qed.

Lemma maxlen_app s1 s2 : maxlen (s1 ++ s2) = maxlen s1 `max` maxlen s2.
Proof. unfold maxlen. rewrite fmap_app, list_max_app. et. Qed.

Lemma list_max_in k ns
  (IN: In k ns)
  :
  k <= list_max ns.
Proof.
  induction ns; ss; des; subst; try nia.
  apply IHns in IN. nia.
Qed.  
