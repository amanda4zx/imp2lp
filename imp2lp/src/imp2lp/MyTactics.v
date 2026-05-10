From Stdlib Require Import List.
From coqutil Require Import Datatypes.List.

Ltac destruct_match_hyp :=
  lazymatch goal with
    H: context[match ?x with _ => _ end] |- _ =>
      let E := fresh "E" in
      destruct x eqn:E end.

Ltac do_injection :=
  lazymatch goal with
    H: ?c _ = ?c _ |- _ => injection H; intros; subst
  end.

Ltac clear_refl := lazymatch goal with H: ?x = ?x |- _ => clear H end.

Ltac invert_Forall2 :=
  lazymatch goal with
  | H: Forall2 _ (_ :: _) _ |- _ => inversion H; subst; clear H
  | H: Forall2 _ _ (_ :: _) |- _ => inversion H; subst; clear H
  | H: Forall2 _ nil _ |- _ => inversion H; subst; clear H
  | H: Forall2 _ _ nil |- _ => inversion H; subst; clear H
  end.

Ltac invert_Forall :=
  lazymatch goal with
  | H: Forall _ (_ :: _) |- _ => inversion H; subst; clear H
  | H: Forall _ nil |- _ => inversion H; subst; clear H
  end.

Ltac invert_pair :=
  lazymatch goal with
  | H: (_, _) = (_, _) |- _ => inversion H; subst; clear H
  | H: _ = (_, _) |- _ => inversion H; subst; clear H
  end.

Ltac invert_cons :=
  lazymatch goal with H: _ :: _ = _ :: _ |- _ => inversion H; subst end.

Ltac invert_Exists :=
  lazymatch goal with
    H: Exists _ _ |- _ =>
      inversion H; subst; clear H
  end.

Ltac destruct_exists :=
  lazymatch goal with
    H: exists _, _ |- _ => destruct H end.

Ltac rewrite_l_to_r :=
  lazymatch goal with
  | H: ?x = _, H': context[?x] |- _ => rewrite H in H'
  | H: ?x = _ |- context[?x] => rewrite H
  end.

Ltac rewrite_asm :=
  lazymatch goal with
    H: ?x = _ |- context[?x] => rewrite H
  end.

Ltac apply_Forall_In :=
  lazymatch goal with
    H: Forall _ ?l, _: In _ ?l |- _ =>
      eapply List.Forall_In in H; eauto end.

Ltac invert_NoDup :=
  lazymatch goal with H: NoDup (_ :: _) |- _ => inversion H; subst end.
