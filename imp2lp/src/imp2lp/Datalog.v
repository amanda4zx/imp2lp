From Stdlib Require Import String ZArith List Bool Permutation.
Require Import coqutil.Map.Interface.

Import ListNotations.

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
  end.

Ltac invert_pair :=
  lazymatch goal with
    H: _ = (_, _) |- _ => inversion H; subst; clear H
  end.

Ltac invert_cons :=
  lazymatch goal with H: _ :: _ = _ :: _ |- _ => inversion H; subst end.

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


(* Values from evaluating Datalog terms *)
Inductive obj : Set :=
  Bobj : bool -> obj | Zobj : Z -> obj | Sobj : string -> obj.

(* Functions on Datalog terms *)
Variant fn : Set :=
  fn_Not | fn_And | fn_Plus | fn_StringConcat | fn_StringLength | fn_BLit (_ : bool) | fn_ZLit (_ : Z) | fn_SLit (_ : string).


Definition interp_fun (f : fn) (l : list obj) : option obj :=
  match f, l with
  | fn_Not, [Bobj b] => Some (Bobj (negb b))
  | fn_And, [Bobj x; Bobj y] => Some (Bobj (x && y))
  | fn_ZPlus, [Zobj x; Zobj y] => Some (Zobj (x + y))
  | fn_StringConcat, [Sobj x; Sobj y]=> Some (Sobj (x ++ y))
  | fn_StringLength, [Sobj x] => Some (Zobj (Z.of_nat (String.length x)))
  | fn_BLit b, [] => Some (Bobj b)
  | fn_ZLit n, [] => Some (Zobj n)
  | fn_SLit s, [] => Some (Sobj s)
  | _, _ => None
  end%Z.

(* Datalog term variables *)
Variant var : Set := DVar (n : nat).

(* Datalog terms *)
Inductive dexpr :=
| var_dexpr (v : var)
| fun_dexpr (f : fn) (args : list dexpr).

(* Datalog propositions that can appear as atoms on the RHS of a rule *)
Variant dprop :=
| DProp_Lt (e1 e2 : dexpr) | DProp_Eq (e1 e2 : dexpr).

(* Datalog relation names *)
Variant rel : Set :=
  nat_rel (n : nat).

Record fact :=
  { fact_R : rel;
    fact_args : list dexpr }.

Record rule := { rule_head : fact; rule_body : list fact; rule_prop : list dprop }.

(* Proof-theoretic semantics *)
Section WithContext.
  Context {context : map.map var obj} {context_ok : map.ok context}.

  Unset Elimination Schemes.
  Inductive interp_dexpr (ctx : context) : dexpr -> obj -> Prop :=
  | interp_var_dexpr x v :
    map.get ctx x = Some v ->
    interp_dexpr ctx (var_dexpr x) v
  | interp_fun_dexpr f args args' v :
    Forall2 (interp_dexpr ctx) args args' ->
    interp_fun f args' = Some v ->
    interp_dexpr ctx (fun_dexpr f args) v.
  Set Elimination Schemes.

  Section interp_dexpr_ind.
    Context (ctx : context).
    Context (P : dexpr -> obj -> Prop).
    Hypothesis (f_var : forall x v, map.get ctx x = Some v -> P (var_dexpr x) v)
      (f_fun : forall f args args' v, Forall2 (interp_dexpr ctx) args args' ->
                                      interp_fun f args' = Some v ->
                                      Forall2 P args args' ->
                                      P (fun_dexpr f args) v).

    Section __.
      Context (interp_dexpr_ind : forall e v, interp_dexpr ctx e v -> P e v).

      Fixpoint interp_dexpr_args_ind (args : list dexpr) (args' : list obj) (H : Forall2 (interp_dexpr ctx) args args') : Forall2 P args args' :=
        match H with
        | Forall2_nil _ => Forall2_nil _
        | Forall2_cons arg arg' Harg Hargs =>
            Forall2_cons arg arg' (interp_dexpr_ind arg arg' Harg) (interp_dexpr_args_ind _ _ Hargs)
        end.
    End __.

    Fixpoint interp_dexpr_ind e v (H : interp_dexpr ctx e v) : P e v :=
      match H with
      | interp_var_dexpr _ x v Hvar => f_var x v Hvar
      | interp_fun_dexpr _ f args args' v Hargs Hf =>
          f_fun f args args' v Hargs Hf
            (interp_dexpr_args_ind interp_dexpr_ind args args' Hargs)
      end.
  End interp_dexpr_ind.

  Lemma interp_dexpr_unique : forall ctx e v v',
      interp_dexpr ctx e v ->
      interp_dexpr ctx e v' ->
      v = v'.
  Proof.
    intros * H. generalize dependent v'.
    induction H; intros * H'; inversion H'; subst.
    1: congruence.
    assert (args' = args'0).
    { clear H0 H6 H'. generalize dependent args'0.
      induction H1; subst; auto; intros;
        inversion H4; subst; auto.
      apply H0 in H5; subst.
      f_equal. clear H4. invert_Forall2; auto. }
    congruence.
  Qed.

  Inductive interp_prop (ctx : context) : dprop -> Prop :=
  | interp_lt_prop e1 e2 n1 n2 :
    interp_dexpr ctx e1 (Zobj n1) ->
    interp_dexpr ctx e2 (Zobj n2) ->
    Z.lt n1 n2 ->
    interp_prop ctx (DProp_Lt e1 e2)
  | interp_eq_prop e1 e2 v :
    interp_dexpr ctx e1 v ->
    interp_dexpr ctx e2 v ->
    interp_prop ctx (DProp_Eq e1 e2).

  Inductive interp_fact (ctx: context) : fact -> rel * list obj -> Prop :=
  | mk_interp_fact f args' :
    Forall2 (interp_dexpr ctx) f.(fact_args) args' ->
    interp_fact ctx f (f.(fact_R), args').


 Inductive rule_impl' : context -> rule -> rel * list obj -> list (rel * list obj) -> Prop :=
  | mk_rule_impl' r f' hyps' ctx :
    interp_fact ctx r.(rule_head) f' ->
    Forall2 (interp_fact ctx) r.(rule_body) hyps' ->
    Forall (interp_prop ctx) r.(rule_prop) ->
    rule_impl' ctx r f' hyps'.

  Hint Constructors rule_impl' : core.

  Definition rule_impl r f hyps :=
    exists ctx,
      rule_impl' ctx r f hyps.

  Lemma normal_rule_impl hyps concl f' hyps' ctx ps :
    interp_fact ctx concl f' ->
    Forall2 (interp_fact ctx) hyps hyps' ->
    Forall (interp_prop ctx) ps ->
    rule_impl {| rule_body := hyps; rule_head := concl; rule_prop := ps |} f' hyps'.
  Proof.
    intros. cbv [rule_impl]. exists ctx.
    constructor; cbn; auto.
  Qed.

  Unset Elimination Schemes.
  Inductive pftree {T : Type} (P : T -> list T -> Prop) : T -> Prop :=
  | mkpftree x l :
    P x l ->
    Forall (pftree P) l ->
    pftree P x.
  Set Elimination Schemes.
  Hint Constructors pftree : core.

  Section pftree_ind.
    Context {T : Type} (P : T -> list T -> Prop).
    Context (P' : T -> Prop).

    Hypothesis (f_mkpftree : forall x l, P x l -> Forall (pftree P) l -> Forall P' l -> P' x).

    Section __.
      Context (pftree_ind : forall x, pftree P x -> P' x).

      Fixpoint pftree_list_ind {l : list T} (H : Forall (pftree P) l) : Forall P' l :=
        match H with
        | Forall_nil _ => Forall_nil _
        | Forall_cons x Hx Hl => Forall_cons x (pftree_ind x Hx) (pftree_list_ind Hl)
        end.
    End __.

    Fixpoint pftree_ind x (H : pftree P x) : P' x :=
      match H with
        mkpftree _ x l Hxl Hl => f_mkpftree x l Hxl Hl (pftree_list_ind pftree_ind Hl)
      end.
  End pftree_ind.

  (*semantics of programs*)
  Definition prog_impl_fact (p : list rule) : rel * list obj -> Prop :=
    pftree (fun f' hyps' => Exists (fun r => rule_impl r f' hyps') p).
End WithContext.

(* Datalog base types *)
Variant dtype := DBool | DNumber | DSymbol.

Record decl := { decl_R : rel; decl_sig : list (string * dtype) }.
