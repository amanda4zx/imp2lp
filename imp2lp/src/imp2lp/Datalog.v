From Stdlib Require Import String ZArith List Bool.
Require Import coqutil.Map.Interface.

Import ListNotations.

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
  | interp_fun_dexpr f args args' x :
    Forall2 (interp_dexpr ctx) args args' ->
    interp_fun f args' = Some x ->
    interp_dexpr ctx (fun_dexpr f args) x.
  Set Elimination Schemes.

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

  (*semantics of programs*)
  Definition prog_impl_fact (p : list rule) : rel * list obj -> Prop :=
    pftree (fun f' hyps' => Exists (fun r => rule_impl r f' hyps') p).
End WithContext.

(* Datalog base types *)
Variant dtype := DBool | DNumber | DSymbol.

Require Import imp2lp.SrcLang imp2lp.Value.
Require Import coqutil.Datatypes.Result.

Section WithVarenv.
  Context {varenv : map.map (string * string) (var * dtype)} {varenv_ok : map.ok varenv}.

  Fixpoint lower_aexpr (m : varenv) (e : aexpr) : dexpr :=
    match e with
    | ABool b => fun_dexpr (fn_BLit b) []
    | AInt n => fun_dexpr (fn_ZLit n) []
    | AString s => fun_dexpr (fn_SLit s) []
    | ANot e => fun_dexpr fn_Not [lower_aexpr m e]
    | AAnd e1 e2 => fun_dexpr fn_And [lower_aexpr m e1; lower_aexpr m e2]
    | APlus e1 e2 => fun_dexpr fn_Plus [lower_aexpr m e1; lower_aexpr m e2]
    | AStringConcat e1 e2 => fun_dexpr fn_StringConcat [lower_aexpr m e1; lower_aexpr m e2]
    | AStringLength e => fun_dexpr fn_StringLength [lower_aexpr m e]
    | AAccess x attr => match map.get m (x, attr) with
                        | Some (v, _) => var_dexpr v
                        | None => var_dexpr (DVar 0) (* unreachable *)
                        end
    end.

  Definition lower_pexpr (m : varenv) (e : pexpr) : dprop :=
    match e with
    | PLt e1 e2 => DProp_Lt (lower_aexpr m e1) (lower_aexpr m e2)
    | PEq e1 e2 => DProp_Eq (lower_aexpr m e1) (lower_aexpr m e2)
    end.

  Definition lower_type (t : type) : dtype :=
    match t with
    | TBool => DBool
    | TInt => DNumber
    | TString => DSymbol
    | _ => DBool (* unused *)
    end.

  Definition lower_atomic_value (v : value) : obj :=
    match v with
    | VInt n => Zobj n
    | VBool b => Bobj b
    | VString s => Sobj s
    (* unused cases *)
    | VList _ | VRecord _ | VSet _ => Bobj false
    end.
End WithVarenv.

Require Import coqutil.Tactics.case_match.

Section WithMaps.
  Context {varenv : map.map (string * string) (var * dtype)} {varenv_ok : map.ok varenv}.
  (* ??? for concrete map implementation of varenv, see pyrosome utils poslistmap trimap*)
  Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
  Context {locals: map.map string value} {locals_ok: map.ok locals}.
  Context {context : map.map var obj} {context_ok : map.ok context}.

  Definition locals_wf (Genv : tenv) (env : locals) : Prop :=
    forall x t, map.get Genv x = Some t ->
                match map.get env x with
                | Some v => type_of_value v t
                | None => False
                end.

  Definition maps_wf (Genv : tenv) (env : locals) (m : varenv) (ctx : context) :=
    forall x tl vl,
      map.get Genv x = Some (TRecord tl) ->
      map.get env x = Some (VRecord vl) ->
      forall attr t v,
        access_record tl attr = Success t ->
        access_record vl attr = Success v ->
        match map.get m (x, attr) with
        | Some (x', t') => map.get ctx x' = Some (lower_atomic_value v) /\ t' = lower_type t
        | _ => False
        end.

  Ltac apply_aexpr_type_sound_IH :=
    lazymatch goal with
      IH: _ -> ?x -> type_of_value _ _, H: ?x |- _ =>
        let H' := fresh "H'" in
        apply IH in H as H'; clear IH; auto; inversion H'; subst
    end.

  Ltac destruct_match_hyp :=
    lazymatch goal with
      H: context[match ?x with _ => _ end] |- _ =>
        let E := fresh "E" in
        destruct x eqn:E end.

  Ltac do_injection :=
    lazymatch goal with
      H: ?c _ = ?c _ |- _ => injection H; intros; subst
    end.

  Ltac invert_Forall2 :=
    lazymatch goal with
    | H: Forall2 _ (_ :: _) _ |- _ => inversion H; subst; clear H
    | H: Forall2 _ _ (_ :: _) |- _ => inversion H; subst; clear H
    | H: Forall2 _ _ _ |- _ => inversion H; subst; clear H
    end.

  Ltac rewrite_asm :=
    lazymatch goal with
      H: ?x = _ |- context[?x] => rewrite H
    end.

  Lemma Forall2_access_record : forall A B vl tl attr t (P : A -> B -> Prop),
      Forall2 (fun vp tp => fst vp = fst tp) vl tl ->
      Forall2 (fun vp tp => P (snd vp) (snd tp)) vl tl ->
      access_record tl attr = Success t ->
      match access_record vl attr with
      | Success v => P v t
      | _ => False
      end.
  Proof.
    induction 1; cbn; intros; try discriminate.
    do 2 destruct_match_hyp;
    invert_Forall2; case_match; cbn in *; subst.
    1:{ rewrite String.eqb_eq in *.
        do_injection. rewrite String.eqb_refl.
        assumption. }
    1:{ rewrite_asm. apply IHForall2 in H8; auto. }
  Qed.

  Lemma aexpr_type_sound : forall Genv env e t,
      type_of_aexpr Genv e t ->
      tenv_wf Genv ->
      locals_wf Genv env ->
      type_of_value (interp_aexpr env e) t.
  Proof.
    induction 1; intros; cbn; try constructor;
      repeat apply_aexpr_type_sound_IH; try constructor.
    apply H2 in H. case_match; intuition idtac.
    inversion H.
    lazymatch goal with
      H: Forall2 (fun _ _ => type_of_value _ _) _ _ |- _ =>
        eapply Forall2_access_record in H
    end; eauto.
    case_match; intuition fail.
  Qed.

  Ltac apply_aexpr_type_sound :=
    lazymatch goal with
      H: type_of_aexpr _ ?e _ |- _ =>
        eapply aexpr_type_sound in H
    end.

  Ltac invert_type_of_value :=
    lazymatch goal with
      H: type_of_value _ _ |- _ =>
        inversion H; subst; clear H
    end.

  Lemma lower_aexpr_sound : forall Genv env e t m ctx,
      type_of_aexpr Genv e t ->
      tenv_wf Genv ->
      locals_wf Genv env ->
      maps_wf Genv env m ctx ->
      interp_dexpr ctx (lower_aexpr m e) (lower_atomic_value (interp_aexpr env e)).
  Proof.
    induction 1; cbn; intros;
      try now (repeat econstructor);
      try now (repeat econstructor; eauto; cbn;
               repeat (apply_aexpr_type_sound; eauto);
               repeat invert_type_of_value; reflexivity).
    lazymatch goal with
      H1: locals_wf ?Genv _, H2: map.get ?Genv _ = Some _ |- _ =>
        let H' := fresh "H'" in
        apply H1 in H2 as H'
    end.
    destruct_match_hyp; intuition idtac.
    invert_type_of_value.
    lazymatch goal with
      H1: maps_wf ?Genv ?env _ _,
        H2: map.get ?env _ = _ |- _ =>
        eapply H1 in H2
    end; eauto.
    lazymatch goal with
      H: Forall2 (fun _ _ => type_of_value _ _) _ _ |- _ =>
        eapply Forall2_access_record in H
    end; eauto. destruct_match_hyp; intuition idtac.
    lazymatch goal with
      H1: context[access_record _ _ = _ -> _],
        H2: access_record _ _ = _ |- _ =>
        eapply H1 in H2
    end; eauto.
    case_match; intuition idtac.
    case_match. constructor; intuition fail.
  Qed.
(*
    Lemma lower_expr_sound : forall Genv env e t m,
        lower_expr out next_rel e = (prog, next_rel', tl') ->
        out < next_rel ->
        type_of_expr Genv e tl ->
        interp_expr env e = VSet s ->
        tl' = lower_record_type tl /\
          forall vl, In vl s <-> prog_impl_fact prog out (lower_record vl)
    doesn't touch other r.
*)

End WithMaps.
