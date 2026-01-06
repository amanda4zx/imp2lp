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

Require Import imp2lp.SrcLang imp2lp.Value.
Require Import coqutil.Datatypes.Result.

Section WithVarenv.
  Context {varenv : map.map (string * string) var} {varenv_ok : map.ok varenv}.

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
                        | Some v => var_dexpr v
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

  Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.

  Definition get_aexpr_type (Genv : tenv) (e : aexpr) : type :=
    match e with
    | ABool _ | ANot _ | AAnd _ _ => TBool
    | AInt _ | APlus _ _ | AStringLength _ => TInt
    | AString _ | AStringConcat _ _ => TString
    | AAccess x attr => match map.get Genv x with
                        | Some (TRecord tl) => match access_record tl attr with
                                               | Success t => t
                                               | _ => TBool (* unused case *)
                                               end
                        | _ => TBool (* unused cases *)
                        end
    end.

  Definition lower_rexpr (Genv : tenv) (m : varenv) (e : rexpr) : list dexpr * list (string * type) :=
    match e with
      RRecord l =>
        (List.map (fun '(_, a) => lower_aexpr m a) (record_sort l),
          List.map (fun '(s, a) => (s, get_aexpr_type Genv a)) (record_sort l))
    end.

  Fixpoint mk_vars (name : nat) (len : nat) : list var :=
    match len with
    | O => []
    | S l => DVar name :: (mk_vars (S name) l)
    end.

  Fixpoint put_attr_bindings (m : varenv) (x : string) (attrs : list string) (vars : list var) : varenv :=
    match attrs, vars with
    | [], _ | _, [] => m
    | attr :: attrs, v :: vars =>
        map.put (put_attr_bindings m x attrs vars) (x, attr) v
    end.

  Definition lower_rec_type : list (string * type) -> list (string * dtype) :=
    List.map (fun '(s, t) => (s, lower_type t)).

  Fixpoint lower_expr (out : rel) (next_rel : nat) (e : expr) : list decl * list rule * nat * list (string * type) :=
  match e with
  | EEmptySet l => ([], [], next_rel, l)
  | ESetInsert r s =>
      let '(r', _) := lower_rexpr map.empty map.empty r in
      let aux := nat_rel next_rel in
      let '(dcls, rls, next_rel', attr_tys) := lower_expr aux (S next_rel) s in
      let vs := List.map var_dexpr (mk_vars 0 (List.length attr_tys)) in
      ( dcls,
        rls ++
         [ {| rule_head := {| fact_R := out; fact_args := r' |};
                 rule_body := [];
             rule_prop := [] |};
           {| rule_head := {| fact_R := out; fact_args := vs |};
                 rule_body := [ {| fact_R := aux; fact_args := vs |} ];
             rule_prop := [] |} ],
        next_rel',
        attr_tys)
  | EFilter s x p =>
      (* out vs :- aux vs, p *)
      let aux := nat_rel next_rel in
      let '(dcls, rls, next_rel', attr_tys) := lower_expr aux (S next_rel) s in
      let vars := mk_vars 0 (List.length attr_tys) in
      let p' := List.map (lower_pexpr (put_attr_bindings map.empty x (List.map fst attr_tys) vars)) p in
      let vs := List.map var_dexpr vars in
      (dcls ++
        [ {| decl_R := aux; decl_sig := lower_rec_type attr_tys |} ],
        rls ++
         [ {| rule_head := {| fact_R := out; fact_args := vs |};
             rule_body := [ {| fact_R := aux; fact_args := vs |} ];
             rule_prop := p' |}],
        next_rel',
        attr_tys)
  | EJoin s1 s2 x1 x2 p r =>
      (* out (lower_rexpr m r) :- aux1 vs1, aux2 vs2, lower_aexpr m p *)
      let aux1 := nat_rel next_rel in
      let '(dcls1, rls1, next_rel1, attr_tys1) := lower_expr aux1 (S next_rel) s1 in
      let aux2 := nat_rel next_rel1 in
      let '(dcls2, rls2, next_rel2, attr_tys2) := lower_expr aux2 (S next_rel1) s2 in
      let vars1 := mk_vars 0 (List.length attr_tys1) in
      let vars2 := mk_vars (List.length attr_tys1) (List.length attr_tys2) in
      let m := put_attr_bindings (put_attr_bindings map.empty x1 (List.map fst attr_tys1) vars1) x2 (List.map fst attr_tys2) vars2 in
      let vs1 := List.map var_dexpr vars1 in
      let vs2 := List.map var_dexpr vars2 in
      let p' := List.map (lower_pexpr m) p in
      let '(r', attr_tys) := lower_rexpr (map.put (map.put map.empty x1 (TRecord attr_tys1)) x2 (TRecord attr_tys2)) m r in
      (dcls1 ++ dcls2 ++
         [ {| decl_R := aux1; decl_sig := lower_rec_type attr_tys1 |};
           {| decl_R := aux2; decl_sig := lower_rec_type attr_tys2 |} ],
        rls1 ++ rls2 ++ [ {| rule_head := {| fact_R := out; fact_args := r' |} ;
            rule_body :=
              [ {| fact_R := aux1; fact_args := vs1 |};
                {| fact_R := aux2; fact_args := vs2 |} ];
           rule_prop := p' |} ],
        next_rel2,
        attr_tys)
  | EProj s x r =>
      (* out rs :- aux vs *)
      let aux := nat_rel next_rel in
      let '(dcls, rls, next_rel', attr_tys) := lower_expr aux (S next_rel) s in
      let vars := mk_vars 0 (List.length attr_tys) in
      let '(r', out_attr_tys) := lower_rexpr (map.put map.empty x (TRecord attr_tys)) (put_attr_bindings map.empty x (List.map fst attr_tys) vars) r in
      let vs := List.map var_dexpr vars in
      (dcls ++
         [ {| decl_R := aux; decl_sig := lower_rec_type attr_tys |} ],
        rls ++
         [ {| rule_head := {| fact_R := out; fact_args := r' |};
             rule_body := [ {| fact_R := aux; fact_args := vs |} ];
             rule_prop := [] |}],
        next_rel',
        out_attr_tys)
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
  Context {varenv : map.map (string * string) var} {varenv_ok : map.ok varenv}.
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
        | Some x' => map.get ctx x' = Some (lower_atomic_value v)
        | _ => False
        end.

  Lemma tenv_wf_empty : tenv_wf map.empty.
  Proof.
    unfold tenv_wf; intros. rewrite map.get_empty in H; congruence.
  Qed.

  Lemma locals_wf_empty : forall (l : locals), locals_wf map.empty l.
  Proof.
    unfold locals_wf; intros. rewrite map.get_empty in *; congruence.
  Qed.

  Lemma maps_wf_empty : forall m ctx, maps_wf map.empty map.empty m ctx.
  Proof.
    unfold maps_wf; intros. rewrite map.get_empty in *; congruence.
  Qed.

  Ltac apply_aexpr_type_sound_IH :=
    lazymatch goal with
      IH: _ -> ?x -> type_of_value _ _, H: ?x |- _ =>
        let H' := fresh "H'" in
        apply IH in H as H'; clear IH; auto; inversion H'; subst
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
    lazymatch goal with
      H: locals_wf ?Genv _, H': map.get ?Genv _ = _ |- _ =>
        apply H in H'
    end. case_match; intuition idtac.
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

  Ltac apply_aexpr_type_sound' e :=
    lazymatch goal with
      H: type_of_aexpr _ e _ |- _ =>
        eapply aexpr_type_sound in H
    end.

  Ltac invert_type_of_value :=
    lazymatch goal with
      H: type_of_value _ _ |- _ =>
        inversion H; subst; clear H
    end.

  Lemma lower_aexpr_complete : forall Genv env e t m ctx,
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
    constructor; intuition fail.
  Qed.

  Ltac invert_interp_dexpr :=
    lazymatch goal with
      H: interp_dexpr _ _ _ |- _ =>
        inversion H; subst
    end.

  Ltac rewrite_aexpr_value :=
    lazymatch goal with
      H: _ = interp_aexpr _ _ |- _ =>
        rewrite <- H in *; clear H
    end.

  Ltac apply_lower_aexpr_sound_IH :=
    lazymatch goal with
      IH: context[interp_dexpr _ (lower_aexpr _ ?e) _ -> _],
        H: interp_dexpr _ (lower_aexpr _ ?e) _ |- _ =>
        apply IH in H
    end.
  Lemma lower_aexpr_sound : forall Genv env e t m ctx,
      type_of_aexpr Genv e t ->
      tenv_wf Genv ->
      locals_wf Genv env ->
      maps_wf Genv env m ctx ->
      forall v,
      interp_dexpr ctx (lower_aexpr m e) v ->
      v = lower_atomic_value (interp_aexpr env e).
  Proof.
    induction 1; cbn; intros.
    all: invert_interp_dexpr;
      try (cbn in *; invert_Forall2; congruence).
    all: try (cbn in *; repeat invert_Forall2;
              repeat (apply_lower_aexpr_sound_IH; auto);
              subst; repeat (apply_aexpr_type_sound; eauto);
              repeat invert_type_of_value;
              repeat rewrite_aexpr_value; cbn in *; congruence).
    1,2: eapply H3 in H as H';
    destruct (map.get env x) eqn:E1; intuition idtac;
    inversion H'; subst;
    lazymatch goal with
      H: Forall2 (fun _ _ => fst _ = fst _) _ _ |- _ =>
        eapply Forall2_access_record in H
    end; eauto;
    destruct_match_hyp; intuition idtac;
    eapply H4 in E; eauto; destruct_match_hyp; intuition idtac;
    congruence.
  Qed.

  Lemma type_of_aexpr_atomic : forall Genv e t,
      type_of_aexpr Genv e t ->
      is_atomic_type t.
  Proof.
    induction 1; cbn; auto.
  Qed.

  Lemma lower_atomic_value_inj : forall t v1 v2,
    is_atomic_type t ->
    type_of_value v1 t -> type_of_value v2 t ->
    lower_atomic_value v1 = lower_atomic_value v2 ->
    v1 = v2.
  Proof.
    intros; destruct t; cbn in *; intuition idtac.
    all: repeat invert_type_of_value; cbn in *; congruence.
  Qed.

  Ltac apply_interp_dexpr_unique :=
    lazymatch goal with
      H1: interp_dexpr _ ?e _,
        H2: interp_dexpr _ ?e _ |- _ =>
        pose proof (interp_dexpr_unique _ _ _ _ H1 H2);
        clear H1 H2
    end.

  Ltac apply_value_eqb_eq :=
    lazymatch goal with
      H: value_eqb _ _ = _ |- _ =>
        apply value_eqb_eq in H; subst
    end.

  Lemma lower_pexpr_correct : forall Genv env e m ctx,
      well_typed_pexpr Genv e ->
      tenv_wf Genv ->
      locals_wf Genv env ->
      maps_wf Genv env m ctx ->
      interp_prop ctx (lower_pexpr m e) <-> interp_pexpr env e = true.
  Proof.
    induction 1; cbn; intros.
    1:{ split; intro H_asm.
        1:{ inversion H_asm; subst.
            repeat lazymatch goal with
                     H: type_of_aexpr _ ?e _ |- _ =>
                       let H' := fresh "H'" in
                       eapply lower_aexpr_sound in H as H'; eauto;
                       apply_aexpr_type_sound' e; eauto
                   end.
            repeat invert_type_of_value.
            repeat lazymatch goal with
                     H: _ = interp_aexpr _ _ |- _ =>
                       rewrite <- H in *; clear H
                   end; cbn in *.
            repeat apply_interp_dexpr_unique.
            repeat (do_injection; clear_refl).
            rewrite Z.ltb_lt. assumption. }
        1:{ repeat (destruct_match_hyp; try discriminate).
            repeat lazymatch goal with
                     H: type_of_aexpr _ ?e _ |- _ =>
                       let H' := fresh "H'" in
                       eapply lower_aexpr_complete in H as H'; eauto;
                       clear H
                   end.
            repeat rewrite_l_to_r; cbn in *.
            econstructor; eauto.
            apply Z.ltb_lt; assumption. } }
    1:{ split; intro H_asm.
        1:{ inversion H_asm; subst.
            repeat lazymatch goal with
                     H: type_of_aexpr _ ?e _ |- _ =>
                       let H' := fresh "H'" in
                       let H'' := fresh "H''" in
                       eapply lower_aexpr_sound in H as H'; eauto;
                       apply type_of_aexpr_atomic in H as H'';
                       apply_aexpr_type_sound' e; eauto
                   end.
            repeat apply_interp_dexpr_unique. subst.
            lazymatch goal with
              H: lower_atomic_value _ = _ |- _ =>
                eapply lower_atomic_value_inj in H
            end; eauto.
            rewrite_asm. apply value_eqb_refl. }
        1:{ repeat (destruct_match_hyp; try discriminate).
            repeat lazymatch goal with
                     H: type_of_aexpr _ ?e _ |- _ =>
                       let H' := fresh "H'" in
                       eapply lower_aexpr_complete in H as H'; eauto;
                       clear H
                   end.
            apply_value_eqb_eq.
            repeat rewrite_l_to_r; cbn in *.
            econstructor; eauto. } }
  Qed.

  Lemma lower_rexpr_complete : forall Genv env m ctx e l attr_tys t,
      type_of_rexpr Genv e t ->
      lower_rexpr Genv m e = (l, attr_tys) ->
      tenv_wf Genv ->
      locals_wf Genv env ->
      maps_wf Genv env m ctx ->
      forall vl,
      interp_rexpr env e = vl ->
        Forall2 (interp_dexpr ctx) l (map (fun v => lower_atomic_value (snd v)) vl).
  Proof.
    intros * H. inversion H; subst; cbn.
    intros. invert_pair. remember (record_sort el) as l.
    clear Heql H H0.
    generalize dependent tl.
    induction l; cbn; constructor; auto;
      invert_Forall2; eauto.
    1: case_match; cbn in *;
    eapply lower_aexpr_complete; eauto.
    inversion H1; subst; eauto.
  Qed.

  Lemma lower_rexpr_sound : forall Genv env m ctx e l attr_tys t,
      type_of_rexpr Genv e t ->
      lower_rexpr Genv m e = (l, attr_tys) ->
      tenv_wf Genv ->
      locals_wf Genv env ->
      maps_wf Genv env m ctx ->
      forall vl,
        Forall2 (interp_dexpr ctx) l vl ->
        Forall2 (fun p v => lower_atomic_value (snd p) = v) (interp_rexpr env e) vl.
  Proof.
    intros * H. inversion H; subst; cbn.
    intros. invert_pair. remember (record_sort el) as l.
    clear Heql H H0.
    generalize dependent vl. generalize dependent tl.
    induction l; cbn; intros.
    1: invert_Forall2; constructor.
    repeat invert_Forall2. constructor; eauto.
    case_match; cbn in *; subst.
    eapply lower_aexpr_sound in H3; eauto.
  Qed.

  Definition rel_lt (r1 r2 : rel) : Prop :=
    match r1, r2 with
      nat_rel n1, nat_rel n2 =>
        Nat.lt n1 n2
    end.

  Definition rel_le (r1 r2 : rel) : Prop :=
    match r1, r2 with
      nat_rel n1, nat_rel n2 =>
        Nat.le n1 n2
    end.

  Definition lower_rec_value (v : value) : list obj :=
    match v with
    | VRecord l => map (fun p => lower_atomic_value (snd p)) l
    | _ => []
    end.

  Lemma set_insert_incl : forall (l : list value) v p,
      In p (set_insert v l) -> p = v \/ In p l.
  Proof.
    induction l; cbn; intros; intuition auto.
    1: subst; auto.
    repeat destruct_match_hyp;
      inversion H; subst; auto.
    apply IHl in H0; intuition idtac.
  Qed.

  Ltac invert_type_wf :=
    lazymatch goal with
    | H: type_wf (TRecord ?tl) |- _ => inversion H; clear H; subst
    end.

  Lemma tenv_wf_step : forall G t, tenv_wf G -> type_wf t -> forall x, tenv_wf (map.put G x t).
  Proof.
    unfold tenv_wf; intros. destruct (String.eqb x x0) eqn:E.
    - rewrite String.eqb_eq in *; subst. rewrite map.get_put_same in *.
      injection H1; intro; subst; auto.
    - rewrite String.eqb_neq in *. rewrite map.get_put_diff in *; eauto.
  Qed.

  Lemma locals_wf_step : forall G E,
      locals_wf G E ->
      forall x t v,
        type_of_value v t ->
        locals_wf (map.put G x t) (map.put E x v).
  Proof.
    unfold locals_wf; intros.
    destruct (String.eqb x0 x) eqn:E_x.
    - rewrite String.eqb_eq in E_x. rewrite E_x in *.
      rewrite map.get_put_same. rewrite map.get_put_same in H1. congruence.
    - rewrite String.eqb_neq in E_x. rewrite map.get_put_diff; auto.
      rewrite map.get_put_diff in H1; auto. apply H. auto.
    Qed.

  Lemma type_of_expr__type_wf : forall e t,
      type_of_expr e t -> type_wf t.
  Proof.
    induction 1; auto;
      lazymatch goal with
        H: type_of_rexpr _ _ _ |- _ =>
          inversion H; auto
      end.
  Qed.

  Ltac invert_type_of_rexpr :=
    lazymatch goal with
      H: type_of_rexpr _ _ _ |- _ =>
        inversion H; subst; clear H
    end.

  Lemma expr_type_sound : forall e t,
      type_of_expr e t ->
      match interp_expr e with
      | VSet s => Forall (fun v => type_of_value v t) s
      | _ => False
      end.
  Proof.
    induction 1; cbn; intros.
    1: constructor.
    all: destruct_match_hyp; intuition idtac.
    1:{ inversion H; subst.
        rewrite Forall_forall; intros ? H_in.
        apply set_insert_incl in H_in.
        intuition idtac; subst.
        2: apply_Forall_In.
        cbn; constructor.
        1:{ revert H2; clear; intros.
            induction H2; auto.
            cbn in *; intuition idtac; constructor; auto.
            case_match; auto. }
        1:{ revert H2 H3.
            repeat lazymatch goal with
                     H: map.ok _ |- _ => revert H
                   end. clear; intros.
            induction H2; auto.
            cbn; constructor; invert_Forall2; intuition auto.
            case_match; cbn in *;
              eauto using aexpr_type_sound, tenv_wf_empty, locals_wf_empty. } }
    1:{ eapply incl_Forall.
        1: apply incl_filter.
        assumption. }
    1:{ destruct_match_hyp; intuition idtac.
        eapply Permutation_Forall.
        1: apply Permuted_value_sort.
        repeat (rewrite Forall_flat_map;
                rewrite Forall_forall; intros;
                apply_Forall_In).
        case_match; auto.
        constructor; auto.
        inversion H2; subst.
        constructor; cbn;
          clear H2 H5; induction H6; auto;
          cbn; constructor; invert_Forall2; auto;
          case_match; cbn in *; intuition idtac.
        apply_aexpr_type_sound;
          eauto using tenv_wf_step, tenv_wf_empty, type_of_expr__type_wf,
          locals_wf_step, locals_wf_empty. }
    1:{ eapply Permutation_Forall.
        1: apply Permuted_value_sort.
        apply Forall_map.
        rewrite Forall_forall; intros; apply_Forall_In.
        invert_type_of_rexpr.
        constructor; cbn; auto;
          clear H2; induction H3; auto;
          invert_Forall2;
          cbn; constructor; auto;
          case_match; cbn; auto.
        apply_aexpr_type_sound; eauto using tenv_wf_step,
          tenv_wf_empty, type_of_expr__type_wf,
          locals_wf_step, locals_wf_empty. }
  Qed.

  Lemma get_aexpr_type_correct : forall Genv e t,
      type_of_aexpr Genv e t ->
      get_aexpr_type Genv e = t.
  Proof.
    induction 1; cbn; auto.
    repeat rewrite_asm. reflexivity.
  Qed.

  Lemma lower_rexpr_type_sound : forall Genv e t,
      type_of_rexpr Genv e t ->
      forall m e's tl,
        lower_rexpr Genv m e = (e's, tl) ->
        t = TRecord tl.
  Proof.
    intros * H; inversion H; subst; clear H; cbn; intros.
    invert_pair. f_equal.
    clear H0.
    induction H1; cbn in *; auto.
    invert_Forall2; case_match; f_equal; auto.
    destruct y; cbn in *; f_equal; auto.
    erewrite get_aexpr_type_correct; eauto.
  Qed.

  Lemma lower_expr_type_sound : forall e t,
      type_of_expr e t ->
      forall out n dcls rls next_rel tl,
        lower_expr out n e = (dcls, rls, next_rel, tl) ->
        t = TRecord tl.
  Proof.
    induction 1; cbn; intros; invert_pair; auto.
    all: repeat destruct_match_hyp; invert_pair;
      repeat lazymatch goal with
        IH: forall _ _ _ _ _ _, lower_expr _ _ ?e = _ -> _,
      H: lower_expr _ _ ?e = _ |- _ =>
      apply IH in H; clear IH
    end; auto;
    lazymatch goal with
      H: type_of_rexpr _ _ _ |- _ =>
        eapply lower_rexpr_type_sound in H; subst; eauto
    end.
  Qed.

  Lemma Forall2_map_r : forall A B C P (f : A -> B) (l : list C) l',
      Forall2 (fun x y => P x (f y)) l l' -> Forall2 P l (map f l').
  Proof.
    induction 1; cbn; auto.
  Qed.

  Fixpoint put_ctx (ctx : context) (xl : list var) (vl : list obj) : context :=
    match xl, vl with
    | [], _ | _, [] => ctx
    | x :: xl, v :: vl => map.put (put_ctx ctx xl vl) x v
    end.

  Lemma record_value_ctx : forall rv tl ctx vars,
      type_of_value rv (TRecord tl) ->
      Forall2 (fun x v => map.get ctx x = Some v) vars (lower_rec_value rv) ->
      Forall2 (interp_dexpr ctx)
        (map var_dexpr vars)
        (lower_rec_value rv).
  Proof.
    intros * H1 H2.
    inversion H1; subst; clear H1.
    cbn in *.
    lazymatch goal with
      |- Forall2 _ _ (map ?f ?vl) =>
        remember (map f vl) as l;
        generalize dependent vl;
        generalize dependent l
    end.
    generalize dependent tl.
    induction vars; intros.
    1:{ invert_Forall2.
        lazymatch goal with
          H: [] = _ |- _ =>
            symmetry in H; apply map_eq_nil in H; subst
          end.
        auto. }
    1:{ invert_Forall2. cbn.
        destruct vl; cbn in *; try discriminate.
        destruct tl; repeat invert_Forall2.
        invert_cons; clear_refl.
        constructor; eauto.
        constructor; auto. }
  Qed.

  Lemma prog_impl_fact_weaken : forall prog prog' f,
      incl prog prog' ->
      prog_impl_fact prog f ->
      prog_impl_fact prog' f.
    unfold prog_impl_fact. intros.
    induction H0.
    econstructor.
    1: eapply incl_Exists; eauto.
    rewrite Forall_forall; intros.
    apply_Forall_In.
  Qed.

  Ltac invert_NoDup :=
    lazymatch goal with H: NoDup (_ :: _) |- _ => inversion H; subst end.

  Lemma put_ctx_correct : forall ctx vars vs,
      NoDup vars ->
      length vars = length vs ->
      Forall2 (fun x v => map.get (put_ctx ctx vars vs) x = Some v) vars vs.
  Proof.
    intros; generalize dependent vs.
    induction vars; cbn; auto; intros.
    1:{ symmetry in H0; rewrite length_zero_iff_nil in H0.
        subst; constructor. }
    1:{ invert_NoDup.
        destruct vs; cbn in *; try discriminate.
        do_injection. constructor.
        1: rewrite map.get_put_same; reflexivity.
        1:{ eapply List.Forall2_impl_strong.
            2: eauto.
            cbn; intros.
            assert(x <> a).
            { intro contra. subst. intuition fail. }
            rewrite map.get_put_diff; auto. } }
  Qed.

  Definition get_var_nat (x : var) :=
    match x with
      DVar n => n
    end.

  Lemma mk_vars_lb : forall n l,
      Forall (fun x => n <= get_var_nat x) (mk_vars n l).
  Proof.
    intros; revert n.
    induction l; intros; cbn; auto.
    constructor; cbn; auto.
    rewrite Forall_forall.
    specialize (IHl (S n)).
    intros. apply_Forall_In.
    eapply Nat.le_trans; try eassumption.
    apply Nat.le_succ_diag_r.
  Qed.

  Lemma mk_vars_NoDup : forall n l,
      NoDup (mk_vars n l).
  Proof.
    intros; revert n; induction l; cbn; auto using NoDup_nil.
    intros; constructor; auto.
    intro contra.
    eapply List.Forall_In in contra.
    2: apply mk_vars_lb.
    cbn in *. apply Nat.nle_succ_diag_l in contra.
    assumption.
  Qed.

  Lemma mk_vars_length : forall n l,
      Datatypes.length (mk_vars n l) = l.
  Proof.
    intros; revert n; induction l; cbn; auto.
  Qed.

  Lemma put_ctx_sound : forall ctx vars vs,
      NoDup vars ->
      length vars = length vs ->
      Forall2 (interp_dexpr (put_ctx ctx vars vs))
        (map var_dexpr vars) vs.
  Proof.
    induction vars; cbn; intros.
    1:{ lazymatch goal with
        H: 0 = _ |- _ =>
          symmetry in H; apply length_zero_iff_nil in H
      end. subst; auto. }
    1:{ destruct vs; cbn in *; try discriminate.
        invert_NoDup.
        do_injection. constructor; auto.
        2:{ eapply List.Forall2_impl_strong.
            2: eauto.
            cbn; intros.
            rewrite in_map_iff in *.
            destruct_exists; intuition idtac; subst.
            assert(x0 <> a).
            { intro contra. subst. intuition fail. }
            invert_interp_dexpr.
            constructor. rewrite map.get_put_diff; auto. }
        constructor. rewrite map.get_put_same; reflexivity. }
  Qed.

  Ltac destruct_String_eqb x y :=
    let E := fresh "E" in
    destruct (String.eqb x y) eqn:E; rewrite ?String.eqb_eq, ?String.eqb_neq in *; subst.

  Ltac rewrite_map_get_put_hyp :=
    multimatch goal with
    | H: context[map.get (map.put _ ?x _) ?x] |- _ =>
        rewrite map.get_put_same in H
    | H: context[map.get (map.put _ _ _) _] |- _ =>
        rewrite map.get_put_diff in H; try now (simpl in *; intuition auto)
    end.

  Ltac rewrite_map_get_put_goal :=
    multimatch goal with
    | |- context[map.get (map.put _ ?x _) ?x] =>
        rewrite map.get_put_same
    | |- context[map.get (map.put _ _ _) _] =>
        rewrite map.get_put_diff; try now (simpl in *; intuition auto)
    end.

  Lemma put_ctx_nil : forall ctx vars,
      put_ctx ctx vars nil = ctx.
  Proof.
    induction vars; auto.
  Qed.

  Lemma put_ctx_None : forall x ctx vars l,
      ~ In x vars ->
      map.get ctx x = None ->
      map.get (put_ctx ctx vars l) x = None.
  Proof.
    induction vars; cbn; auto; intros.
    case_match; intuition auto.
    rewrite_map_get_put_goal.
  Qed.

  Lemma maps_wf_step : forall Genv env m ctx,
      maps_wf Genv env m ctx ->
      forall x tl vl vars,
        type_of_value (VRecord vl) (TRecord tl) ->
        NoDup vars ->
        Forall (fun x' => map.get ctx x' = None) vars ->
        length vars = length tl ->
        maps_wf (map.put Genv x (TRecord tl))
          (map.put env x (VRecord vl))
          (put_attr_bindings m x (map fst tl) vars)
          (put_ctx ctx vars (map (fun p => lower_atomic_value (snd p)) vl)).
  Proof.
    unfold maps_wf; intros * ?.
    induction tl; cbn; intros.
    1:{ destruct_String_eqb x x0;
        repeat rewrite_map_get_put_hyp.
        1:{ do_injection; cbn in *; discriminate. }
        1:{ invert_type_of_value. invert_Forall2.
            cbn. rewrite put_ctx_nil. eapply H; eauto. } }
    1:{ destruct_String_eqb x x0;
        repeat rewrite_map_get_put_hyp.
        2:{ invert_type_of_value. repeat invert_Forall2.
            destruct vars; cbn in *; try discriminate.
            do_injection. invert_NoDup.
            destruct_String_eqb x x0;
              try congruence.
            rewrite_map_get_put_goal; try congruence.
            invert_Forall.
            eapply IHtl with (x:=x0) in H6; eauto;
              try rewrite_map_get_put_goal.
            2: constructor; eauto.
            case_match; intuition idtac.
            assert(v0 <> v1).
            { intro; subst.
              rewrite put_ctx_None in *; auto. discriminate. }
            rewrite_map_get_put_goal. }
        1:{ invert_type_of_value. repeat invert_Forall2.
            case_match; cbn in *; try discriminate.
            repeat (do_injection; clear_refl). invert_NoDup. invert_Forall.
            destruct_String_eqb (fst a) attr;
              repeat rewrite_map_get_put_goal; try congruence;
              destruct x, a; cbn in *; subst.
            1:{ rewrite String.eqb_refl in *.
                congruence. }
            1:{ lazymatch goal with
                H: _ <> _ |- _ =>
                  rewrite <- String.eqb_neq, eqb_sym in H;
                  rewrite H in *
              end.
                eapply IHtl with (x:=x0) in H6; eauto;
                  try (rewrite_map_get_put_goal; reflexivity).
                2: constructor; auto.
                case_match; intuition idtac.
                assert(v0 <> v2).
                { intro; subst.
                  rewrite put_ctx_None in *; auto. discriminate. }
                rewrite_map_get_put_goal. } } }
  Qed.

  Lemma maps_wf_step2 : forall Genv env m ctx,
      maps_wf Genv env m ctx ->
      forall x tl vl vars,
        type_of_value (VRecord vl) (TRecord tl) ->
        NoDup vars ->
        Forall2 (fun x' v' => map.get ctx x' = Some v') vars (map (fun p => lower_atomic_value (snd p)) vl) ->
        length vars = length tl ->
        maps_wf (map.put Genv x (TRecord tl))
          (map.put env x (VRecord vl))
          (put_attr_bindings m x (map fst tl) vars)
          ctx.
  Proof.
    Admitted.

  Definition var_eqb (x y : var) :=
    match x, y with
      DVar a, DVar b => a =? b
    end.

  Instance var_eq_dec : forall x y : var, BoolSpec (x = y) (x <> y) (var_eqb x y).
  Proof.
    intros.
    destruct (var_eqb x y) eqn:E; constructor.
    all: destruct x, y; cbn in *; f_equal; auto.
    1: apply Nat.eqb_eq; assumption.
    1: intro. do_injection; rewrite Nat.eqb_refl in *; discriminate.
  Qed.

  Lemma put_put_ctx_diff : forall ctx x v vars vs,
      ~ In x vars ->
      put_ctx (map.put ctx x v) vars vs = map.put (put_ctx ctx vars vs) x v.
  Proof.
    induction vars; cbn; auto; intros.
    intuition idtac.
    case_match; auto.
    rewrite IHvars; auto.
    rewrite Properties.map.put_put_diff; auto.
  Qed.

  Lemma put_ctx_diff : forall ctx vars1 vars2 vs1 vs2,
    Forall (fun x => ~ In x vars2) vars1 ->
              put_ctx (put_ctx ctx vars1 vs1) vars2 vs2 =
                put_ctx (put_ctx ctx vars2 vs2) vars1 vs1.
  Proof.
    intros * H; revert vs1 vs2.
    induction H; cbn; auto; intros.
    case_match; auto. rewrite <- IHForall.
    apply map.map_ext; intro y.
    rewrite put_put_ctx_diff; auto.
  Qed.

  Lemma mk_vars_range : forall n l,
      Forall (fun x => n <= (get_var_nat x) /\ (get_var_nat x) < n + l) (mk_vars n l).
  Proof.
    intros *; revert n.
    induction l; cbn; intros; auto.
    constructor; cbn; intuition auto.
    1:{ unfold lt. rewrite <- Nat.add_succ_comm.
        apply Nat.le_add_r. }
    1:{ eapply Forall_impl; eauto.
        cbn; intros. intuition idtac.
        1:{ rewrite Nat.succ_le_mono.
            apply le_S; assumption. }
        1:{ rewrite Nat.add_succ_r; assumption. } }
  Qed.

  Lemma mk_vars_disjoint : forall n1 n2 l1 l2,
      n1 + l1 <= n2 ->
      Forall (fun x => ~ In x (mk_vars n2 l2)) (mk_vars n1 l1).
  Proof.
    intros; rewrite Forall_forall; intros.
    intro contra.
    repeat lazymatch goal with
      H: In _ _ |- _ =>
        eapply List.Forall_In in H; eauto using mk_vars_range
           end; cbn in *.
    intuition idtac.
    eapply Nat.lt_le_trans in H; try eassumption.
    apply Nat.lt_nge in H. intuition fail.
  Qed.

  Lemma mk_vars_disjoint2 : forall n1 n2 l1 l2,
      n1 + l1 <= n2 ->
      Forall (fun x => ~ In x (mk_vars n1 l1)) (mk_vars n2 l2).
  Proof.
    intros; rewrite Forall_forall; intros.
    intro contra.
    eapply List.Forall_In in contra.
    2: apply mk_vars_disjoint; eauto.
    eauto.
  Qed.

  Ltac apply_in_nil :=
    lazymatch goal with
      H: In _ nil |- _ => apply in_nil in H
    end.

  Ltac destruct_In :=
    lazymatch goal with
      H: In _ (_ :: _) |- _ => destruct H; subst end.

  Ltac prove_tenv_wf := eauto using tenv_wf_step, tenv_wf_empty, type_of_expr__type_wf.

  Ltac prove_locals_wf := repeat eapply locals_wf_step; auto using locals_wf_empty; constructor; auto.

  Ltac prove_maps_wf :=
    repeat eapply maps_wf_step;
    auto using maps_wf_empty, mk_vars_NoDup, mk_vars_length;
    try (rewrite Forall_forall; intros; apply map.get_empty);
    try now (constructor; auto).

  Ltac prove_lower_expr_complete'_hyps :=
    repeat constructor; auto; cbn;
    lazymatch goal with
      H: prog_impl_fact _ (?r, _) |- pftree _ (?r, _) =>
        eapply prog_impl_fact_weaken in H
    end; eauto;
    repeat lazymatch goal with
      | |- incl ?x (?x ++ _) =>
          apply incl_appl, incl_refl
      | |- incl ?x (_ ++ _) => apply incl_appr
      end.

  Ltac apply_lower_expr_complete'_IH :=
    lazymatch goal with
    | IH: context[lower_expr _ _ ?e = _],
        H: lower_expr _ _ ?e = _ |- _ =>
        eapply IH in H
    end.

  Ltac apply_lower_expr_complete'_IH2 :=
    lazymatch goal with
    | IH: context[VSet ?l = _ -> _],
        H: In _ ?l |- _ =>
        let P := fresh "P" in
        eapply IH in H as P; clear IH
    end.

  Ltac prove_vars_rec_eq_len :=
    rewrite mk_vars_length;
    lazymatch goal with
      H: lower_expr _ _ _ = (_, _, _, ?tl) |- context[length ?tl] =>
        eapply lower_expr_type_sound in H
    end; eauto;
    do_injection; invert_type_of_value; cbn;
    rewrite length_map;
    symmetry; eapply Forall2_length; eauto.

  Lemma lower_expr_complete' : forall e t,
      type_of_expr e t ->
      forall s out next_rel dcls prog next_rel' tl',
        lower_expr out next_rel e = (dcls, prog, next_rel', tl') ->
        interp_expr e = VSet s ->
        forall rv, In rv s -> prog_impl_fact prog (out, lower_rec_value rv).
  Proof.
    induction 1; cbn; intros.
    1:{ repeat invert_pair; do_injection.
        apply_in_nil; intuition fail. }
    1:{ (* ESetInsert e s *)
      eapply expr_type_sound in H0 as S0; eauto.
      destruct_match_hyp; try now intuition idtac.
      do_injection; clear_refl.
      lazymatch goal with
        H: In _ (set_insert _ _) |- _ =>
          apply set_insert_incl in H
      end.
      intuition idtac; subst;
        repeat destruct_match_hyp; invert_pair.
      1:{ (* r is the newly inserted record e *)
        cbn.
        eapply lower_rexpr_complete in E0;
          eauto using tenv_wf_empty, locals_wf_empty, maps_wf_empty.
        econstructor.
        2: apply Forall_nil.
        rewrite Exists_exists.
        eexists; split.
        1: eapply in_or_app; right; left; reflexivity.
        econstructor. constructor; auto.
        constructor; cbn.
        induction E0; auto.
        constructor; eauto. }
      1:{ (* r is already in s *)
        apply_Forall_In.
        eapply lower_rexpr_type_sound in E0; eauto; subst.
        apply_lower_expr_complete'_IH2; auto.
        2: eassumption.
        invert_pair.
        econstructor.
        1:{ (* rule at the root of the proof tree *)
          rewrite Exists_exists.
          eexists. intuition idtac.
          1: apply in_or_app; right; right; constructor; reflexivity.
          econstructor.
          constructor; cbn; auto.
          1:{ constructor; cbn.
              eapply record_value_ctx; eauto.
              apply put_ctx_correct with (ctx := map.empty).
              1: apply mk_vars_NoDup.
              1: prove_vars_rec_eq_len. }
          1:{ constructor; auto. constructor; cbn.
              apply put_ctx_sound.
              1: apply mk_vars_NoDup.
              1: prove_vars_rec_eq_len. } }
        1:{ (* proof tree for the hypothesis *)
          constructor; auto; cbn.
          eapply prog_impl_fact_weaken.
          1: apply incl_appl, incl_refl.
          auto. } } }
    1:{ (* filter *)
      eapply expr_type_sound in H as S; eauto.
      destruct_match_hyp; try now intuition idtac.
      do_injection; clear_refl.
      intuition idtac; subst;
        repeat destruct_match_hyp; invert_pair.
      eapply lower_expr_type_sound in E0 as S0; eauto; subst.
      lazymatch goal with
        H: In _ (filter _ _) |- _ =>
          eapply filter_In in H; intuition eauto
      end.
      apply_Forall_In. invert_type_of_value.
      apply_lower_expr_complete'_IH; eauto.
      econstructor.
      1:{ (* rule at the root of the proof tree *)
        rewrite Exists_exists.
        eexists; split.
        1: eapply in_or_app; right; left; reflexivity.
        econstructor. constructor; cbn.
        1:{ constructor; cbn.
            eapply put_ctx_sound.
            1: apply mk_vars_NoDup.
            1:{ rewrite mk_vars_length. rewrite length_map.
                symmetry; eapply Forall2_length; eauto. } }
        1:{ constructor; auto. constructor; cbn.
            eapply put_ctx_sound.
            1: apply mk_vars_NoDup.
            1:{ rewrite mk_vars_length. rewrite length_map.
                symmetry; eapply Forall2_length; eauto. } }
        instantiate (1:=map.empty).
        eapply List.forallb_to_Forall
          with (P:=fun x => interp_pexpr _ x = true)
          in H2; eauto.
        induction ps; auto.
        cbn; constructor; repeat invert_Forall; auto.
        erewrite lower_pexpr_correct; eauto.
        1: prove_tenv_wf.
        1: prove_locals_wf.
        1: prove_maps_wf. }
      1: (* proof tree for the hypothesis *)
        prove_lower_expr_complete'_hyps. }
    1:{ (* join *)
      lazymatch goal with
        H: type_of_expr e1 _,
          H0: type_of_expr e2 _ |- _ =>
          eapply expr_type_sound in H as S; eauto;
          eapply expr_type_sound in H0 as S0; eauto
      end.
      repeat (destruct_match_hyp; try now intuition idtac).
      do_injection; clear_refl.
      intuition idtac; subst; invert_pair.
      lazymatch goal with
        E: lower_expr _ _ e1 = _,
          E0: lower_expr _ _ e2 = _ |- _ =>
          eapply lower_expr_type_sound in E as E'; eauto;
          eapply lower_expr_type_sound in E0 as E0'; eauto
      end; subst.
      lazymatch goal with
        H: In _ (value_sort _) |- _ =>
          eapply Permutation_in in H;
          [ | apply Permutation_sym, Permuted_value_sort ]
      end.
      repeat (
          lazymatch goal with
            H: In _ (flat_map _ _) |- _ =>
              apply in_flat_map in H
          end; destruct_exists; intuition idtac).
      destruct_match_hyp; [ | apply_in_nil; intuition fail].
      destruct_In; [ | apply_in_nil; intuition fail].
      repeat (apply_lower_expr_complete'_IH2; eauto).
      repeat apply_Forall_In. repeat invert_type_of_value.
      econstructor.
      1:{ (* rule at the root of the proof tree *)
        rewrite Exists_exists.
        eexists; split.
        1: repeat (eapply in_or_app; right; try now (left; reflexivity)).
        econstructor. constructor; cbn.
        1:{ constructor; cbn.
            eapply lower_rexpr_complete in E7; eauto.
            1: eauto using tenv_wf_step, tenv_wf_empty, type_of_expr__type_wf.
        1: prove_tenv_wf.
        1: prove_locals_wf.
        1:{ prove_maps_wf. rewrite Forall_forall; intros.
            apply put_ctx_None; auto using map.get_empty.
            lazymatch goal with
              H: In _ (mk_vars _ _) |- _ =>
                eapply List.Forall_In in H
            end.
            2: apply mk_vars_disjoint2.
            1: cbn in *; eassumption.
            auto. } }
        1:{ repeat constructor; auto; cbn.
            1:{ rewrite put_ctx_diff.
                2: eauto using mk_vars_disjoint.
                apply put_ctx_sound; auto using mk_vars_NoDup.
                rewrite mk_vars_length. rewrite length_map.
                symmetry; eapply Forall2_length; eauto. }
            1:{ eapply put_ctx_sound; auto using mk_vars_NoDup.
                rewrite mk_vars_length. rewrite length_map.
                symmetry; eapply Forall2_length; eauto. } }
        eapply List.forallb_to_Forall
          with (P:=fun x => interp_pexpr _ x = true)
          in E2; eauto.
        induction ps; auto.
        cbn; constructor; repeat invert_Forall; auto.
        erewrite lower_pexpr_correct; eauto.
        1: prove_tenv_wf.
        1: prove_locals_wf.
        1:{ prove_maps_wf.
            rewrite Forall_forall; intros.
            apply put_ctx_None; auto using map.get_empty.
            lazymatch goal with
              H: In _ (mk_vars _ _) |- _ =>
                eapply List.Forall_In in H
            end.
            2: apply mk_vars_disjoint2.
            1: cbn in *; eassumption.
            auto. } }
      1: (* proof tree for the hypothesis *)
        prove_lower_expr_complete'_hyps. }
    1:{ lazymatch goal with
        H: type_of_expr _ _|- _ =>
          eapply expr_type_sound in H as S; eauto
      end.
repeat (destruct_match_hyp; try now intuition idtac).
      do_injection; clear_refl.
      intuition idtac; subst; invert_pair.
      lazymatch goal with
        E: lower_expr _ _ _ = _ |- _ =>
          eapply lower_expr_type_sound in E as E'; eauto
      end; subst.
      lazymatch goal with
        H: In _ (value_sort _) |- _ =>
          eapply Permutation_in in H;
          [ | apply Permutation_sym, Permuted_value_sort ]
      end.
      lazymatch goal with
        H: In _ (map _ _) |- _ =>
          rewrite in_map_iff in H
      end; destruct_exists; intuition idtac.
      apply_lower_expr_complete'_IH2; eauto.
      repeat apply_Forall_In. repeat invert_type_of_value.
      econstructor.
      1:{ (* rule at the root of the proof tree *)
        rewrite Exists_exists.
        eexists; split.
        1: repeat (eapply in_or_app; right; try now (left; reflexivity)).
        econstructor. constructor; cbn; auto.
        1:{ constructor; cbn.
            lazymatch goal with
              E: lower_rexpr _ _ _ = _ |- _ =>
                eapply lower_rexpr_complete in E
              end; eauto.
        1: prove_tenv_wf.
        1: prove_locals_wf.
        1: prove_maps_wf. }
        1:{ repeat constructor; auto; cbn.
            eapply put_ctx_sound; auto using mk_vars_NoDup.
                rewrite mk_vars_length. rewrite length_map.
                symmetry; eapply Forall2_length; eauto. } }
      1: (* proof tree for the hypothesis *)
        prove_lower_expr_complete'_hyps. }
    Unshelve. all: apply map.empty.
  Qed.

  Print Assumptions lower_expr_complete'.

  Lemma In_set_insert : forall x l,
      In x (set_insert x l).
  Proof.
    intros. induction l; cbn; auto.
    repeat case_match.
    1: left; reflexivity.
    1: apply_value_eqb_eq; left; reflexivity.
    1: right; auto.
    Qed.
(* ???
  Lemma prog_rule_head_lb : forall r0 r n e dcls rls r' tl',
      rel_lt r0 r ->
      rel_lt r (nat_rel n) ->
      lower_expr r n e = (dcls, rls, r', tl') ->
      Forall (fun rl => rel_lt r0 rl.(rule_head).(fact_R)) rls.
  Admitted.
*)
  Lemma rel_lt_not_refl : forall r,
      ~ rel_lt r r.
  Proof.
    intros; unfold rel_lt; case_match; cbn.
    auto using Nat.lt_irrefl.
  Qed.

  Lemma Forall2_eq_map : forall A B (f : A -> B) vl vl',
      Forall2 (fun v v' => f v = v') vl vl' ->
      vl' = map f vl.
  Proof.
    induction 1; cbn; congruence.
  Qed.

  Lemma set_insert_preserve_In : forall x y l,
      In x l -> In x (set_insert y l).
  Proof.
    induction l; cbn; auto.
    intuition idtac; subst; repeat case_match.
    all: repeat (try (left; reflexivity); right); auto.
  Qed.
(* ???
  Lemma lower_expr_rule_body_rel_lb : forall e r n dcls rls n' tl,
      lower_expr r n e = (dcls, rls, n', tl) ->
      rel_lt r (nat_rel n) ->
      Forall (fun rl =>
                (Forall (fun hyp => rel_le r hyp.(fact_R)) rl.(rule_body)))
        rls.
  Proof.
    induction e; cbn; intros; invert_pair.
    1: constructor.
    1:{ repeat destruct_match_hyp. invert_pair. admit. }
  Admitted.

  Lemma lower_expr_fresh_rel_gt : forall e r n dcls rls n' tl,
      lower_expr r n e = (dcls, rls, n', tl) ->
      rel_lt r (nat_rel n) ->
      n <= n' /\
        Forall (fun rl => forall hyp, In hyp rl.(rule_body) -> rel_lt hyp.(fact_R) (nat_rel n')) rls.
    Admitted.

 *)

  Lemma Forall2_interp_dexpr_unique : forall ctx l vl vl',
      Forall2 (interp_dexpr ctx) l vl ->
      Forall2 (interp_dexpr ctx) l vl' ->
      vl = vl'.
  Proof.
    intros * H; revert vl'; induction H; cbn; intros;
    invert_Forall2; auto.
    f_equal; eauto using interp_dexpr_unique.
  Qed.

  Ltac invert_rule_impl :=
    lazymatch goal with
      H: rule_impl _ _ _ |- _ =>
        inversion H; subst; clear H
    end;
    lazymatch goal with
      H: rule_impl' _ _ _ _ |- _ =>
        inversion H; subst; clear H
    end.

  Ltac invert_interp_fact :=
    lazymatch goal with
      H: interp_fact _ _ _ |- _ =>
        inversion H; subst; clear H
    end.

  Inductive rel_dep_on (prog : list rule) : rel -> rel -> Prop :=
  | rel_dep_on_base rl hyp : In rl prog ->
                             In hyp rl.(rule_body) ->
                             rel_dep_on prog rl.(rule_head).(fact_R) hyp.(fact_R)
  | rel_dep_on_trans r1 r2 r3 : rel_dep_on prog r1 r2 ->
                                rel_dep_on prog r2 r3 ->
                                rel_dep_on prog r1 r3.

  Lemma prog_impl_fact_factor : forall prog prog' f,
      (* new rules in prog' can only be applied at most once
         at the root of the proof tree
         if the hypotheses of the new rules do not depend on any head of the new rules *)
      prog_impl_fact (prog ++ prog') f ->
      (forall rl1 rl2, In rl1 prog' -> In rl2 prog' ->
                     forall hyp, In hyp rl2.(rule_body) ->
                                 ~ rel_dep_on (prog ++ prog') hyp.(fact_R) rl1.(rule_head).(fact_R)) ->
      prog_impl_fact prog f \/
        exists hyps rl, In rl prog' /\ rule_impl rl f hyps /\ Forall (prog_impl_fact prog) hyps.
  Proof.
    unfold prog_impl_fact. intros.
    induction H.
    rewrite Exists_app in *.
  Admitted.

  Lemma prog_impl_fact_or : forall prog prog' f,
      prog_impl_fact (prog ++ prog') f ->
      (forall rl rl',
          In rl prog ->
          In rl' prog' ->
          ~ rel_dep_on (prog ++ prog') rl.(rule_head).(fact_R) rl'.(rule_head).(fact_R) /\
            ~ rel_dep_on (prog ++ prog') rl'.(rule_head).(fact_R) rl.(rule_head).(fact_R)) ->
      prog_impl_fact prog f \/ prog_impl_fact prog' f.
  Admitted.

  Definition Forall_body P (rl : rule) :=
    Forall (fun hyp => P hyp) rl.(rule_body).

  Definition rel_le_lt (lb ub r : rel) :=
    rel_le lb r /\ rel_lt r ub.

  Definition rule_le_lt (lb ub : rel) (rl : rule) : Prop :=
    rel_le_lt lb ub rl.(rule_head).(fact_R) /\
      Forall_body (fun hyp => rel_le_lt lb ub hyp.(fact_R)) rl.

  Lemma lower_expr_rel_bounds : forall r n e dcls rls n' tl,
      lower_expr r n e = (dcls, rls, n', tl) ->
      rel_lt r (nat_rel n) ->
      Forall (rule_le_lt r (nat_rel n')) rls.
  Admitted.

  Lemma rel_le_refl : forall r, rel_le r r.
  Proof.
    destruct r; cbn; auto.
  Qed.

  Lemma lower_expr_fresh_rel : forall r n e dcls rls n' tl,
      lower_expr r n e = (dcls, rls, n', tl) ->
      rel_lt r (nat_rel n) ->
      n <= n'.
  Admitted.

  Lemma fresh_heads_not_dep : forall rls rls' lb ub r r',
      Forall (rule_le_lt lb ub) rls ->
      Forall (fun rl' => ~ rel_le_lt lb ub rl'.(rule_head).(fact_R)) rls' ->
      rel_le_lt lb ub r ->
      ~ rel_le_lt lb ub r' ->
      ~ rel_dep_on (rls ++ rls') r r'.
  Admitted.

  (* ??? first attempt
  Lemma prog_impl_fact_fresh_heads : forall prog prog' f,
      (* new rules in prog' can only be applied at most once
         at the root of the proof tree
         if the heads of the new rules are not in the body of any rules *)
      prog_impl_fact (prog ++ prog') f ->
      (forall r1 r2, In r1 prog' -> In r2 (prog ++ prog') ->
                     forall hyp, In hyp r2.(rule_body) ->
                                 r1.(rule_head).(fact_R) <> hyp.(fact_R)) ->
      prog_impl_fact prog f \/
        exists hyps r, In r prog' /\ rule_impl r f hyps /\ Forall (prog_impl_fact prog) hyps.
  Proof.
    unfold prog_impl_fact. intros.
    induction H.
    rewrite Exists_app in *.
  Admitted.
   *)
  Ltac invert_pftree :=
    lazymatch goal with
        H: pftree _ _ |- _ =>
          inversion H; subst
    end.

  Ltac apply_lower_expr_sound'_IH :=
    lazymatch goal with
      IH: context[lower_expr _ _ ?e = _ -> _],
        H: lower_expr _ _ ?e = _ |- _ =>
        eapply IH in H
    end.

  Ltac apply_lower_expr_sound'_IH2 :=
    lazymatch goal with
      IH: context [ lower_expr _ _ ?e = _ -> _ ],
        _: lower_expr _ _ ?e = (_, ?rls, _, _),
          H: prog_impl_fact ?rls _ |- _ =>
        eapply IH in H
    end.

  Lemma rel_lt_nge : forall r r',
      rel_lt r r' -> ~ rel_le r' r.
  Admitted.

  Lemma rule_le_lt_weaken : forall lb lb' ub ub' rl,
      rel_le lb' lb ->
      rel_le ub ub' ->
      rule_le_lt lb ub rl ->
      rule_le_lt lb' ub' rl.
  Admitted.

  Lemma Forall2_interp_dexpr_alt : forall ctx vars vl,
      Forall2 (interp_dexpr ctx) (map var_dexpr vars) (lower_rec_value (VRecord vl)) ->
      Forall2 (fun x' v' => map.get ctx x' = Some v')
        vars (map (fun p => lower_atomic_value (snd p)) vl).
  Proof.
    induction vars; cbn; intros.
    1:{ invert_Forall2.
        symmetry in H0; apply map_eq_nil in H0.
        constructor. }
    1:{ destruct vl; cbn in *; invert_Forall2.
        constructor; auto.
        invert_interp_dexpr; assumption. }
  Qed.

  Lemma rel_lt_le_trans : forall r1 r2 r3,
      rel_lt r1 r2 -> rel_le r2 r3 -> rel_lt r1 r3.
  Proof.
    destruct r1, r2, r3.
    cbn; eauto using Nat.lt_le_trans.
  Qed.

  Lemma indep_rules_not_dep : forall lb lb' ub ub' rls rls' r r',
      Forall (rule_le_lt lb ub) rls ->
      Forall (rule_le_lt lb' ub') rls' ->
      rel_le ub lb' \/ rel_le ub' lb ->
      rel_le_lt lb ub r ->
      rel_le_lt lb' ub' r' ->
      ~rel_dep_on (rls ++ rls') r r'.
  Admitted.

  Lemma rel_dep_on_app_comm : forall rls rls' r1 r2,
      rel_dep_on (rls ++ rls') r1 r2 <-> rel_dep_on (rls' ++ rls) r1 r2.
  Admitted.

  Ltac apply_rel_lt_nge :=
    lazymatch goal with
      H: rel_lt ?r ?r', _: rel_le ?r' ?r |- _ =>
        apply rel_lt_nge in H;
        intuition fail
    end.

  Ltac prove_rel_indep :=
    lazymatch goal with
      H: rel_dep_on _ _ _ |- _ =>
        eapply fresh_heads_not_dep in H;
        eauto;
        [ eapply lower_expr_rel_bounds; eauto;
          cbn; auto
        | |  unfold rel_le_lt;
             intuition auto using rel_le_refl;
             eapply lower_expr_fresh_rel; eauto;
             cbn; auto
        | ];
        repeat constructor; cbn;
        unfold rel_le_lt; intuition idtac;
        apply_rel_lt_nge
    end.

  Ltac prove_prog_cannot_impl :=
    lazymatch goal with
      H: lower_expr _ _ _ = (_, ?prog, _, _),
        _: prog_impl_fact ?prog _ |- _ =>
        apply lower_expr_rel_bounds in H
    end; cbn; auto;
    unfold prog_impl_fact in *;
    invert_pftree;
    rewrite Exists_exists in *;
    destruct_exists; intuition idtac;
    apply_Forall_In;
    invert_rule_impl; invert_interp_fact;
    unfold rule_le_lt, rel_le_lt in *; intuition idtac;
    apply_rel_lt_nge.

  Lemma lower_expr_sound' : forall e t,
      type_of_expr e t ->
      forall s out next_rel dcls prog next_rel' tl',
        rel_lt out (nat_rel next_rel) ->
        lower_expr out next_rel e = (dcls, prog, next_rel', tl') ->
        interp_expr e = VSet s ->
        (*  rel_ltb next_rel all_rels_in_prog
        rel_lt all_rels_in_prog next_rel' *)
        forall vl, prog_impl_fact prog (out, vl) ->
                   exists rv, In rv s /\ vl = lower_rec_value rv.
  Proof.
    unfold prog_impl_fact.
    induction 1; cbn; intros.
    1:{ repeat invert_pair; do_injection; intuition idtac.
        invert_pftree.
        rewrite Exists_nil in *; intuition fail. }
    1:{ (* ESetInsert e s *)
      destruct_match_hyp; try now intuition idtac.
      do_injection.
      repeat destruct_match_hyp; clear_refl.
      invert_pair.

      lazymatch goal with
        H: pftree _ _ |- _ =>
          eapply prog_impl_fact_factor in H
      end.
      2:{ intros.
          assert(H_hd : rl1.(rule_head).(fact_R) = out).
          { repeat destruct_In; cbn in *; intuition idtac. }
          rewrite H_hd.
          lazymatch goal with
            H: In rl1 _ |- _ => clear H end.
          repeat destruct_In; cbn in *; intuition idtac;
            subst; cbn in *.
          prove_rel_indep. }
      intuition idtac.
      1: (* Only the fresh rules can implement the output relation *)
        prove_prog_cannot_impl.
      (* two possible root nodes of the proof tree *)
      repeat destruct_exists.
      repeat destruct_In; cbn in *; intuition idtac.
      1:{ (* vl is the newly added record value *)
        invert_rule_impl; invert_interp_fact.
        cbn in *; invert_Forall2.
        lazymatch goal with
          E: lower_rexpr _ _ _ = _ |- _ =>
            eapply lower_rexpr_sound in E
        end; eauto.
        1:{ eexists. intuition idtac.
            1: apply In_set_insert.
            cbn; eauto using Forall2_eq_map. }
        1: prove_tenv_wf.
        1: prove_locals_wf.
        1: prove_maps_wf. }
      1:{ (* vl is already in the set *)
        subst. invert_rule_impl.
        cbn in *; repeat invert_Forall2.
        repeat invert_interp_fact. invert_Forall.
        repeat lazymatch goal with
                 H: Forall _ [] |- _ => clear H end.
        apply_lower_expr_sound'_IH; cbn; auto.
        1:{ destruct_exists.
            eexists; intuition idtac.
            1: apply set_insert_preserve_In; eauto.
            eassumption. }
        cbn in *.
        assert(vl = args').
        { eauto using Forall2_interp_dexpr_unique. }
        subst. assumption. } }
    1:{ (* filter *)
      destruct_match_hyp; try now intuition idtac.
      do_injection.
      repeat destruct_match_hyp; clear_refl.
      invert_pair.

      lazymatch goal with
        H: pftree _ _ |- _ =>
          eapply prog_impl_fact_factor in H
      end; cbn; eauto.
      2:{ cbn; intros.
          intuition idtac; subst; cbn in *.
          intuition idtac; subst; cbn in *.
          prove_rel_indep. }
      intuition idtac.
      1: prove_prog_cannot_impl.

      repeat destruct_exists; intuition idtac.
      repeat destruct_In; cbn in *; intuition idtac.
      invert_rule_impl; invert_interp_fact.
      cbn in *. repeat invert_Forall2.
      invert_interp_fact; cbn in *.
      assert (vl = args').
      { eauto using Forall2_interp_dexpr_unique. }
      subst.
      invert_Forall.
      repeat lazymatch goal with
               H: Forall _ [] |- _ => clear H end.

      lazymatch goal with
        H: type_of_expr _ _ |- _ =>
          eapply expr_type_sound in H as T
      end; destruct_match_hyp; intuition idtac.
      do_injection.
      lazymatch goal with
        H: lower_expr _ _ _ = _ |- _ =>
          eapply lower_expr_type_sound in H as L
      end; eauto; subst.
      apply_lower_expr_sound'_IH; cbn; auto.
      1:{ destruct_exists.
          eexists; intuition idtac.
          2: eauto.
          rewrite filter_In; intuition idtac.
          rewrite forallb_forall; intros.
          repeat apply_Forall_In; subst.
          repeat invert_type_of_value.
          rewrite <- lower_pexpr_correct; eauto.
          1:{ rewrite Forall_map in *. apply_Forall_In. }
          1: prove_tenv_wf.
          1: prove_locals_wf.
          1:{ apply maps_wf_step2; prove_maps_wf.
              apply Forall2_interp_dexpr_alt; auto. } }
      1: assumption. }
    1:{ (* join *)
      lazymatch goal with
        H: type_of_expr e1 _,
          H0: type_of_expr e2 _ |- _ =>
          eapply expr_type_sound in H as S; eauto;
          eapply expr_type_sound in H0 as S0; eauto
      end.
      repeat destruct_match_hyp; try now intuition idtac.
      do_injection.
      repeat destruct_match_hyp; clear_refl.
      invert_pair.
      lazymatch goal with
        E: lower_expr _ _ e1 = _,
          E0: lower_expr _ _ e2 = _ |- _ =>
          eapply lower_expr_type_sound in E as E'; eauto;
          eapply lower_expr_type_sound in E0 as E0'; eauto;
          eapply lower_expr_rel_bounds in E as H'; eauto; cbn; auto;
          eapply lower_expr_rel_bounds in E0 as H0'; eauto; cbn; auto;
          eapply lower_expr_fresh_rel in E as F; eauto;
          eapply lower_expr_fresh_rel in E0 as F0; eauto
      end; subst; cbn; auto.

      rewrite app_assoc in *.
      lazymatch goal with
        H: pftree _ _ |- _ =>
          eapply prog_impl_fact_factor in H
      end; cbn; eauto.
      2:{ cbn; intros.
          intuition idtac; subst; cbn in *.
          intuition idtac; subst; cbn in *.
          all: lazymatch goal with
               | H:rel_dep_on _ _ _ |- _ =>
                   eapply fresh_heads_not_dep
                   with (lb:=nat_rel next_rel) (ub:=nat_rel next_rel') in H; eauto
               end;
            [ apply Forall_app; split;
              eapply Forall_impl; try eassumption;
              intros; eapply rule_le_lt_weaken; try eassumption;
              cbn; eauto using Nat.le_trans
            | repeat constructor; cbn; unfold rel_le_lt;
              intuition idtac; apply_rel_lt_nge
            | unfold rel_le_lt;
              intuition auto using rel_le_refl;
              cbn; eauto using Nat.lt_le_trans, Nat.le_trans
            | unfold rel_le_lt;
              intuition idtac; apply_rel_lt_nge ]. }
      intuition idtac.
      1:{ (* Only the fresh rules can implement the output relation *)
            unfold prog_impl_fact in *; invert_pftree.
            rewrite Exists_exists in *; destruct_exists.
            rewrite in_app_iff in *.
            intuition idtac; apply_Forall_In;
              invert_rule_impl; invert_interp_fact;
              unfold rule_le_lt, rel_le_lt in *; intuition idtac.
            1: apply_rel_lt_nge.
            lazymatch goal with
              _: rel_lt ?x (nat_rel ?n),
                _: Datatypes.S ?n <= ?n' |- _ =>
                assert(rel_lt x (nat_rel n'))
            end.
            { eapply rel_lt_le_trans.
              1: apply H3.
              cbn; eauto using Nat.le_trans. }
            apply_rel_lt_nge. }
      1:{ repeat destruct_exists; intuition idtac.
          repeat destruct_In; cbn in *; intuition idtac.
          invert_rule_impl; invert_interp_fact.
          cbn in *. repeat invert_Forall2.
          repeat invert_interp_fact; cbn in *.
          repeat invert_Forall.
          repeat lazymatch goal with
                   H: Forall _ [] |- _ => clear H end.

          lazymatch goal with
            H: prog_impl_fact (_ ++ _) _ |- _ =>
              apply prog_impl_fact_or in H
          end;
          [ | intros; split;
              [ | rewrite rel_dep_on_app_comm ];
              eapply indep_rules_not_dep; eauto;
              intuition idtac; cbn; auto;
              repeat apply_Forall_In;
              unfold rule_le_lt in *; intuition idtac ].
          intuition idtac.
          1:{ unfold prog_impl_fact in *.
              invert_pftree.
              rewrite Exists_exists in *.
              repeat destruct_exists; intuition idtac.
              apply_Forall_In.
              invert_rule_impl. invert_interp_fact.
              unfold rule_le_lt, rel_le_lt in *;
                intuition idtac.
              rewrite_l_to_r.
              cbn in *; apply Nat.lt_irrefl in H19; intuition fail. }

          lazymatch goal with
            H: prog_impl_fact (_ ++ _) _ |- _ =>
              apply prog_impl_fact_or in H
          end;
          [ | intros; split;
              [ | rewrite rel_dep_on_app_comm ];
              eapply indep_rules_not_dep; eauto;
              intuition idtac; cbn; auto;
              repeat apply_Forall_In;
              unfold rule_le_lt in *; intuition idtac ].
          intuition idtac.
          2:{ unfold prog_impl_fact in *.
              invert_pftree.
              rewrite Exists_exists in *.
              repeat destruct_exists; intuition idtac.
              apply_Forall_In.
              invert_rule_impl. invert_interp_fact.
              unfold rule_le_lt, rel_le_lt in *;
                intuition idtac.
              repeat rewrite_l_to_r.
              cbn in *. rewrite Nat.le_succ_l, Nat.lt_nge in *.
              intuition fail. }

          repeat(apply_lower_expr_sound'_IH;
                 [ | | reflexivity | ]; cbn; eauto).
          repeat destruct_exists; intuition idtac.

          eexists; split;
            repeat apply_Forall_In;
            repeat invert_type_of_value.
          1:{ eapply Permutation_in.
              1: eapply Permuted_value_sort.
              repeat (rewrite in_flat_map;
                      eexists; split; eauto).
              lazymatch goal with
                |- context[if ?e then _ else _] =>
                  assert(e = true)
              end.
              { rewrite forallb_forall; intros.
                rewrite Forall_map in *.
                repeat apply_Forall_In.
                erewrite <- lower_pexpr_correct; eauto.
                1: prove_tenv_wf.
                1: prove_locals_wf.
                1: repeat (eapply maps_wf_step2; prove_maps_wf;
                           try apply Forall2_interp_dexpr_alt; auto). }
              repeat rewrite_l_to_r. constructor; eauto. }
          lazymatch goal with
            H: lower_rexpr _ _ _ = _ |- _ =>
              eapply lower_rexpr_sound in H
          end; eauto.
          1: apply Forall2_eq_map; eassumption.
          1: prove_tenv_wf.
          1: prove_locals_wf.
          1: repeat (eapply maps_wf_step2; prove_maps_wf;
                     try apply Forall2_interp_dexpr_alt; auto). } }
    1:{ (* projection *)
      destruct_match_hyp; try now intuition idtac.
      do_injection.
      repeat destruct_match_hyp; clear_refl.
      invert_pair.

      lazymatch goal with
        H: pftree _ _ |- _ =>
          eapply prog_impl_fact_factor in H
      end; cbn; eauto.
      2:{ cbn; intros.
          intuition idtac; subst; cbn in *.
          intuition idtac; subst; cbn in *.
          prove_rel_indep. }
      intuition idtac.
      1: prove_prog_cannot_impl.

      repeat destruct_exists; intuition idtac.
      repeat destruct_In; cbn in *; intuition idtac.
      invert_rule_impl; invert_interp_fact.
      cbn in *. repeat invert_Forall2.
      invert_interp_fact; cbn in *.
      invert_Forall.
      repeat lazymatch goal with
               H: Forall _ [] |- _ => clear H end.

      lazymatch goal with
        H: type_of_expr _ _ |- _ =>
          eapply expr_type_sound in H as T
      end; destruct_match_hyp; intuition idtac.
      do_injection; clear_refl.
      lazymatch goal with
        H: lower_expr _ _ _ = _ |- _ =>
          eapply lower_expr_type_sound in H as L
      end; eauto; subst.

      lazymatch goal with
        IH: context [ lower_expr _ _ ?e = _ -> _ ],
          _: lower_expr _ _ ?e = (_, ?rls, _, _),
            H: prog_impl_fact ?rls _ |- _ =>
          eapply IH in H
      end; cbn; eauto.
      destruct_exists.
      eexists; intuition idtac.
      1:{ eapply Permutation_in.
          1: apply Permuted_value_sort.
          rewrite in_map_iff.
          eapply lower_rexpr_type_sound in H0 as H0';
            eauto; subst. }
      apply_Forall_In. invert_type_of_value.
      eapply lower_rexpr_sound in H8; eauto.
      1:{ apply Forall2_eq_map in H8; eassumption. }
      1: prove_tenv_wf.
      1: prove_locals_wf.
      1: apply maps_wf_step2; prove_maps_wf;
      apply Forall2_interp_dexpr_alt; auto. }
  Qed.

End WithMaps.
