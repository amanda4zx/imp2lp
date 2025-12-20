From Stdlib Require Import String ZArith List Bool.
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
  | H: Forall2 _ _ _ |- _ => inversion H; subst; clear H
  end.

Ltac rewrite_l_to_r :=
  lazymatch goal with
  | H: ?x = _, H': context[?x] |- _ => rewrite H in H'
  | H: ?x = _ |- context[?x] => rewrite H
  end.

Ltac rewrite_asm :=
  lazymatch goal with
    H: ?x = _ |- context[?x] => rewrite H
  end.


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
        put_attr_bindings (map.put m (x, attr) v) x attrs vars
    end.

  Definition lower_rec_type : list (string * type) -> list (string * dtype) :=
    List.map (fun '(s, t) => (s, lower_type t)).

  Fixpoint lower_expr (out : rel) (next_rel : nat) (Genv : tenv) (e : expr) : list decl * list rule * nat * list (string * type) :=
  match e with
  | EEmptySet l => ([], [], next_rel, l)
  | ESetInsert r s =>
      let '(r', _) := lower_rexpr Genv map.empty r in
      let '(dcls, rls, next_rel', attr_tys) := lower_expr out next_rel Genv s in
      let vs := List.map var_dexpr (mk_vars 0 (List.length attr_tys)) in
      ( dcls,
        rls ++
         [ {| rule_head := {| fact_R := out; fact_args := r' |};
                 rule_body := [];
             rule_prop := [] |} ],
        next_rel',
        attr_tys)
  | EFilter s x p =>
      (* out vs :- aux vs, p *)
      let aux := nat_rel next_rel in
      let '(dcls, rls, next_rel', attr_tys) := lower_expr aux (S next_rel) Genv s in
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
      let '(dcls1, rls1, next_rel1, attr_tys1) := lower_expr aux1 (S next_rel) Genv s1 in
      let aux2 := nat_rel next_rel1 in
      let '(dcls2, rls2, next_rel2, attr_tys2) := lower_expr aux2 (S next_rel1) Genv s2 in
      let vars1 := mk_vars 0 (List.length attr_tys1) in
      let vars2 := mk_vars (List.length attr_tys1) (List.length attr_tys2) in
      let m := put_attr_bindings (put_attr_bindings map.empty x1 (List.map fst attr_tys1) vars1) x2 (List.map fst attr_tys2) vars2 in
      let vs1 := List.map var_dexpr vars1 in
      let vs2 := List.map var_dexpr vars2 in
      let p' := List.map (lower_pexpr m) p in
      let '(r', attr_tys) := lower_rexpr (map.put (map.put Genv x1 (TRecord attr_tys1)) x2 (TRecord attr_tys2)) m r in
      (dcls1 ++ dcls2 ++
         [ {| decl_R := aux1; decl_sig := lower_rec_type attr_tys1 |};
           {| decl_R := aux2; decl_sig := lower_rec_type attr_tys2 |} ],
        [ {| rule_head := {| fact_R := out; fact_args := r' |} ;
            rule_body :=
              [ {| fact_R := aux1; fact_args := vs1 |};
                {| fact_R := aux2; fact_args := vs2 |} ];
           rule_prop := p' |} ],
        next_rel2,
        attr_tys)
  | EProj s x r =>
      (* out rs :- aux vs *)
      let aux := nat_rel next_rel in
      let '(dcls, rls, next_rel', attr_tys) := lower_expr aux (S next_rel) Genv s in
      let vars := mk_vars 0 (List.length attr_tys) in
      let '(r', out_attr_tys) := lower_rexpr Genv (put_attr_bindings map.empty x (List.map fst attr_tys) vars) r in
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
    constructor; intuition fail.
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

  Lemma lower_pexpr_sound : forall Genv env e m ctx,
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
                       eapply lower_aexpr_sound in H as H'; eauto;
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
                       eapply lower_aexpr_sound in H as H'; eauto;
                       clear H
                   end.
            apply_value_eqb_eq.
            repeat rewrite_l_to_r; cbn in *.
            econstructor; eauto. } }
  Qed.

  Ltac invert_pair :=
    lazymatch goal with
      H: _ = (_, _) |- _ => inversion H; subst; clear H
    end.

  Ltac destruct_exists :=
    lazymatch goal with
      H: exists _, _ |- _ => destruct H end.

  Lemma lower_rexpr_sound : forall Genv env m ctx e l attr_tys t vl,
      type_of_rexpr Genv e t ->
      lower_rexpr Genv m e = (l, attr_tys) ->
      interp_rexpr env e = vl ->
      tenv_wf Genv ->
      locals_wf Genv env ->
      maps_wf Genv env m ctx ->
      Forall2 (fun e' v => interp_dexpr ctx e' (lower_atomic_value (snd v))) l vl.
  Proof.
    intros * H. inversion H; subst; cbn.
    intros. invert_pair. remember (record_sort el) as l.
    lazymatch goal with
      H: Forall2 _ _ _ |- _ =>
        eapply Permutation.Permutation_Forall2 in H
    end; [ | apply Permuted_record_sort ].
    destruct_exists; intuition idtac.
    rewrite <- Heql in *. clear Heql H3.
    generalize dependent x.
    induction l; cbn; constructor; auto;
      invert_Forall2; eauto.
    case_match; cbn.
    eapply lower_aexpr_sound; eauto.
  Qed.

  Definition rel_lt (r1 r2 : rel) : Prop :=
    match r1, r2 with
      nat_rel n1, nat_rel n2 =>
        Nat.lt n1 n2
    end.

  Definition lower_rec_value (v : value) : list obj :=
    match v with
    | VRecord l => map (fun p => lower_atomic_value (snd p)) l
    | _ => []
    end.

  Lemma expr_type_sound : forall Genv env e t,
      type_of_expr Genv e t ->
      locals_wf Genv env ->
      match interp_expr env e with
      | VSet s => Forall (fun v => type_of_value v t) s
      | _ => False
      end.
  Proof.
    induction 1; cbn; intros.
    1: constructor.
    1:{ apply IHtype_of_expr in H1.
        destruct_match_hyp; intuition idtac.
        inversion H; subst. admit. }
    Admitted.

  Lemma lower_expr_sound' : forall Genv env e t,
      type_of_expr Genv e t ->
      (* rel_lt out (nat_rel next_rel) -> *)
      forall s out next_rel dcls prog next_rel' tl',
        lower_expr out next_rel Genv e = (dcls, prog, next_rel', tl') ->
        interp_expr env e = VSet s ->
        locals_wf Genv env ->
        (*  rel_ltb next_rel all_rels_in_prog
        rel_lt all_rels_in_prog next_rel' *)
        forall rv, In rv s <-> prog_impl_fact prog (out, lower_rec_value rv).
  Proof.
    induction 1; cbn; intros.
    1:{ repeat invert_pair; do_injection; intuition idtac.
        1: lazymatch goal with
             H: In _ nil |- _ => apply in_nil in H
           end; intuition fail.
        1: inversion H0; subst;
        rewrite Exists_nil in *; intuition fail. }
    1:{ eapply expr_type_sound in H0; eauto.
        destruct_match_hyp; intuition idtac.
        1:{ econstructor.
          (*  split cases between rv = interp_rexpr env r and In rv l. *) all: admit. }
        Admitted.

End WithMaps.
