(* Include mutable variable constructs and use Owen's Datalog definitions *)

From Stdlib Require Import String ZArith List Bool Permutation.
From coqutil Require Import Map.Interface Decidable.
Require Import Datalog.Datalog.
Require Import imp2lp.SrcLangWithVar imp2lp.Value.
Require Import coqutil.Datatypes.Result.
Import ListNotations.

Definition var : Type := string + nat.

Variant obj : Set :=
  Bobj : bool -> obj | Zobj : Z -> obj | Sobj : string -> obj.

Variant Bfn : Set :=
  fn_BLit (_ : bool) | fn_Not | fn_And | fn_Lt | fn_Eq.

Variant Zfn : Set :=
  fn_ZLit (_ : Z) | fn_Plus | fn_StringLength.

Variant Sfn : Set :=
  fn_SLit (_ : string) | fn_StringConcat.

Variant fn : Set :=
  fnB (_ : Bfn) | fnZ (_ : Zfn) | fnS (_ : Sfn).

Definition obj_eqb (x y : obj) : bool :=
  match x, y with
  | Bobj x, Bobj y => eqb x y
  | Zobj x, Zobj y => (x =? y)%Z
  | Sobj x, Sobj y => (x =? y)%string
  | _, _ => false
  end.

Definition interp_Bfn (f : Bfn) (l : list obj) : option bool :=
  match f, l with
  | fn_BLit b, [] => Some b
  | fn_Not, [Bobj x] => Some (negb x)
  | fn_And, [Bobj x; Bobj y] => Some (x && y)
  | fn_Lt, [Zobj x; Zobj y] => Some (x <? y)%Z
  | fn_Eq, [x; y] => Some (obj_eqb x y)
  | _, _ => None
  end.

Definition interp_Zfn (f : Zfn) (l : list obj) : option Z :=
  match f, l with
  | fn_ZLit z, [] => Some z
  | fn_Plus, [Zobj x; Zobj y] => Some (x + y)%Z
  | fn_StringLength, [Sobj x] => Some (Z.of_nat (String.length x))
  | _, _ => None
  end.

Definition interp_Sfn (f : Sfn) (l : list obj) : option string :=
  match f, l with
  | fn_SLit s, [] => Some s
  | fn_StringConcat, [Sobj x; Sobj y] => Some (x ++ y)%string
  | _, _ => None
  end.

Variant rel : Set :=
  (* ??? Assume no shadowing and use variable names as relation/datalog var names. *)
  | str_rel : string -> rel (* unary for variables, assuming SSA form *)
  | nat_rel : nat -> rel
  | true_rel (* unary, true if arg is true *).

Variant aggregator : Set :=.

Definition var_eqb (x y : var) : bool :=
  match x, y with
  | inl x, inl y => (x =? y)%string
  | inr x, inr y => (x =? y)%nat
  | _, _ => false
  end.

Lemma var_eqb_spec x y : BoolSpec (x = y) (x <> y) (var_eqb x y).
Proof.
  destruct x, y; simpl; try (constructor; congruence).
  1: destruct (s =? s0)%string eqn:E; constructor;
  rewrite ?String.eqb_eq, ?String.eqb_neq in *; congruence.
  1: destruct (n =? n0)%nat eqn:E; constructor;
  rewrite ?Nat.eqb_eq, ?Nat.eqb_neq in *; congruence.
Qed.

Section __.
  Let interp_fn (f : fn) (l : list obj) : option obj :=
        match f with
        | fnB f => option_map Bobj (interp_Bfn f l)
        | fnZ f => option_map Zobj (interp_Zfn f l)
        | fnS f => option_map Sobj (interp_Sfn f l)
        end.

  Let get_set (x : obj) : option (list obj) := None.
  (* ??? Do we expect the new aggregation mechanism to replace this? *)

  Let agg_id (a : aggregator) : obj :=
        match a with
        end.

  Let interp_agg (a : aggregator) : obj -> obj -> obj :=
        match a with
        end.

  Instance Sig : signature fn aggregator obj :=
    { interp_fun := interp_fn ;
      get_set := get_set;
      agg_id := agg_id;
      interp_agg := interp_agg }.
End __.
#[local] Existing Instance Sig.
Existing Instance var_eqb_spec.
Instance str_eqb_spec : EqDecider String.eqb := String.eqb_spec.

Section __.
  Local Notation rule := (rule rel var fn aggregator).
  Local Notation dexpr := (Datalog.expr var fn).
  Local  Notation fact := (fact rel var fn).

  Section WithVarenv.
    (* Context {varenv : map.map string rel} {varenv_ok : map.ok varenv}. *)
    Context {attrenv : map.map (string * string) var} {attrenv_ok : map.ok attrenv}.

    Fixpoint lower_aexpr (m : attrenv) (e : aexpr) : (dexpr * list fact) :=
      (* Assume no variable shadowing.
         env: maps each immutable variable containing an atomic value to a singleton relation with one column;
         m: maps each (row variable, attribute) pair to a datalog variable.
         return (datalog expression, list of clauses assumed for the expression, new threshold for fresh variables *)
      match e with
      | AVar x => (var_expr (inl x), [ {| fact_R:=str_rel x; fact_args:=[var_expr (inl x)] |} ])
      | ABool b => (fun_expr (fnB (fn_BLit b)) [], [])
      | AInt n => (fun_expr (fnZ (fn_ZLit n)) [], [])
      | AString s => (fun_expr (fnS (fn_SLit s)) [], [])
      | ALet e1 x e2 => let '(e1', conds1) := lower_aexpr m e1 in
                        let '(e2', conds2) := lower_aexpr m e2 in
                        (e2', {| fact_R:=str_rel x; fact_args:=[e1'] |} :: conds1 ++ conds2)
      | ANot e => let '(e', conds) := lower_aexpr m e in
                  (fun_expr (fnB fn_Not) [e'], conds)
      | AAnd e1 e2 => let '(e1', conds1) := lower_aexpr m e1 in
                      let '(e2', conds2) := lower_aexpr m e2 in
                      (fun_expr (fnB fn_And) [e1'; e2'], conds1 ++ conds2)
      | APlus e1 e2 => let '(e1', conds1) := lower_aexpr m e1 in
                       let '(e2', conds2) := lower_aexpr m e2 in
                       (fun_expr (fnZ fn_Plus) [e1'; e2'], conds1 ++ conds2)
      | AStringConcat e1 e2 => let '(e1', conds1) := lower_aexpr m e1 in
                               let '(e2', conds2) := lower_aexpr m e2 in
                               (fun_expr (fnS fn_StringConcat) [e1'; e2'], conds1 ++ conds2)
      | AStringLength e => let '(e', conds) := lower_aexpr m e in
                           (fun_expr (fnZ fn_StringLength) [e'], conds)
      | AAccess x attr => (match map.get m (x, attr) with
                           | Some x' => var_expr x'
                           | None => fun_expr (fnB (fn_BLit false)) [] (* unreachable *)
                           end, [])
      end.

    Definition lower_pexpr (m : attrenv) (e : pexpr) : (dexpr * list fact) :=
      match e with
      | PLt e1 e2 =>
          let '(e1', conds1) := lower_aexpr m e1 in
          let '(e2', conds2) := lower_aexpr m e2 in
          (fun_expr (fnB fn_Lt) [e1'; e2'], conds1 ++ conds2)
      | PEq e1 e2 =>
          let '(e1', conds1) := lower_aexpr m e1 in
          let '(e2', conds2) := lower_aexpr m e2 in
          (fun_expr (fnB fn_Eq) [e1'; e2'], conds1 ++ conds2)
      end.

    (* Datalog base types *)
    Variant dtype := DBool | DNumber | DString.

    Record decl := { decl_R : rel; decl_sig : list (string * dtype) }.

    Definition lower_type (t : type) : dtype :=
      match t with
      | TBool => DBool
      | TInt => DNumber
      | TString => DString
      | _ => DBool (* unused *)
      end.

  Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.

  Fixpoint get_aexpr_type (Genv : tenv) (e : aexpr) : type :=
    match e with
    | AVar x => match map.get Genv x with
                | Some t => t
                | _ => TBool (* unused case *)
                end
    | ABool _ | ANot _ | AAnd _ _ => TBool
    | AInt _ | APlus _ _ | AStringLength _ => TInt
    | AString _ | AStringConcat _ _ => TString
    | ALet e1 x e2 => get_aexpr_type (map.put Genv x (get_aexpr_type Genv e1)) e2
    | AAccess x attr => match map.get Genv x with
                        | Some (TRecord tl) => match access_record tl attr with
                                               | Success t => t
                                               | _ => TBool (* unused case *)
                                               end
                        | _ => TBool (* unused cases *)
                        end
    end.

  Definition lower_rexpr (Genv : tenv) (m : attrenv) (e : rexpr) : list dexpr * list fact * list (string * type) :=
    match e with
      RRecord l =>
        (List.map (fun '(_, a) => fst (lower_aexpr m a)) (record_sort l),
          List.concat (List.map (fun '(_, a) => snd (lower_aexpr m a)) (record_sort l)),
          List.map (fun '(s, a) => (s, get_aexpr_type Genv a)) (record_sort l))
    end.

  Fixpoint mk_vars (name : nat) (len : nat) : list var :=
    match len with
    | O => []
    | S l => inr name :: (mk_vars (S name) l)
    end.

  Fixpoint put_attr_bindings (m : attrenv) (x : string) (attrs : list string) (vars : list var) : attrenv :=
    match attrs, vars with
    | [], _ | _, [] => m
    | attr :: attrs, v :: vars =>
        map.put (put_attr_bindings m x attrs vars) (x, attr) v
    end.

  Definition lower_rec_type : list (string * type) -> list (string * dtype) :=
    List.map (fun '(s, t) => (s, lower_type t)).

  Fixpoint lower_expr (Gstore : tenv) (out : rel) (next_rel : nat) (e : expr) : list decl * list rule * nat * list (string * type) :=
      match e with
      | ELoc x =>
          let attr_tys := match map.get Gstore x with
                          | Some (TRecord l) => l
                          | _ => [] (* unreachable for well-typed expressions *)
                          end in
          let vs := List.map var_expr (mk_vars 0 (List.length attr_tys)) in
          ([],
            [{| rule_concls := [{| fact_R := out; fact_args := vs |}];
               rule_hyps := [{| fact_R := str_rel x; fact_args := vs|}];
               rule_agg := None;
               rule_set_hyps := [] |}],
            next_rel,
            attr_tys)
      | EEmptySet l => ([], [], next_rel, l)
      | ESetInsert r s =>
          let '(r', asms, _) := lower_rexpr map.empty map.empty r in
          let aux := nat_rel next_rel in
          let '(dcls, rls, next_rel', attr_tys) := lower_expr Gstore aux (S next_rel) s in
          let vs := List.map var_expr (mk_vars 0 (List.length attr_tys)) in
          (dcls,
            rls ++
              [ {| rule_concls := [{| fact_R := out; fact_args := r' |}];
                  rule_hyps := asms;
                  rule_agg := None;
                  rule_set_hyps := [] |};
                {| rule_concls := [{| fact_R := out; fact_args := vs |}];
                  rule_hyps := [ {| fact_R := aux; fact_args := vs |} ];
                  rule_agg := None;
                  rule_set_hyps := [] |} ],
            next_rel',
            attr_tys)
      | EFilter s x p =>
          (* out vs :- aux vs, p *)
          let aux := nat_rel next_rel in
          let '(dcls, rls, next_rel', attr_tys) := lower_expr Gstore aux (S next_rel) s in
          let vars := mk_vars 0 (List.length attr_tys) in
          let p_asms := List.map (lower_pexpr (put_attr_bindings map.empty x (List.map fst attr_tys) vars)) p in
          let p' := List.map fst p_asms in
          let asms := List.concat (List.map snd p_asms) in
          let vs := List.map var_expr vars in
          (dcls ++
             [ {| decl_R := aux; decl_sig := lower_rec_type attr_tys |} ],
            rls ++
              [ {| rule_concls := [ {| fact_R := out; fact_args := vs |} ];
                  rule_hyps := [ {| fact_R := aux; fact_args := vs |};
                                 {| fact_R := true_rel; fact_args := p' |} ] ++ asms;
               rule_agg := None;
               rule_set_hyps := [] |} ],
            next_rel',
            attr_tys)
      | EJoin s1 s2 x1 x2 p r =>
      (* out (lower_rexpr m r) :- aux1 vs1, aux2 vs2, lower_aexpr m p *)
          let aux1 := nat_rel next_rel in
          let '(dcls1, rls1, next_rel1, attr_tys1) := lower_expr Gstore aux1 (S next_rel) s1 in
          let aux2 := nat_rel next_rel1 in
          let '(dcls2, rls2, next_rel2, attr_tys2) := lower_expr Gstore aux2 (S next_rel1) s2 in
          let vars1 := mk_vars 0 (List.length attr_tys1) in
          let vars2 := mk_vars (List.length attr_tys1) (List.length attr_tys2) in
          let m := put_attr_bindings (put_attr_bindings map.empty x1 (List.map fst attr_tys1) vars1) x2 (List.map fst attr_tys2) vars2 in
          let vs1 := List.map var_expr vars1 in
          let vs2 := List.map var_expr vars2 in
          let p_asms := List.map (lower_pexpr m) p in
          let p' := List.map fst p_asms in
          let asms_p := List.concat (List.map snd p_asms) in
          let '(r', asms_r, attr_tys) := lower_rexpr (map.put (map.put map.empty x1 (TRecord attr_tys1)) x2 (TRecord attr_tys2)) m r in
          (dcls1 ++ dcls2 ++
             [ {| decl_R := aux1; decl_sig := lower_rec_type attr_tys1 |};
               {| decl_R := aux2; decl_sig := lower_rec_type attr_tys2 |} ],
            rls1 ++ rls2 ++
              [ {| rule_concls := [ {| fact_R := out; fact_args := r' |} ] ;
                  rule_hyps :=
                    [ {| fact_R := aux1; fact_args := vs1 |};
                      {| fact_R := aux2; fact_args := vs2 |};
                      {| fact_R := true_rel; fact_args := p' |} ] ++ asms_r ++ asms_p;
                  rule_agg := None;
                  rule_set_hyps := [] |} ],
            next_rel2,
            attr_tys)
      | EProj s x r =>
          (* out rs :- aux vs *)
          let aux := nat_rel next_rel in
          let '(dcls, rls, next_rel', attr_tys) := lower_expr Gstore aux (S next_rel) s in
          let vars := mk_vars 0 (List.length attr_tys) in
          let '(r', asms, out_attr_tys) := lower_rexpr (map.put map.empty x (TRecord attr_tys)) (put_attr_bindings map.empty x (List.map fst attr_tys) vars) r in
          let vs := List.map var_expr vars in
          (dcls ++
             [ {| decl_R := aux; decl_sig := lower_rec_type attr_tys |} ],
            rls ++
              [ {| rule_concls := [ {| fact_R := out; fact_args := r' |} ];
                  rule_hyps := [ {| fact_R := aux; fact_args := vs |} ] ++ asms;
                  rule_agg := None;
                  rule_set_hyps := [] |}],
            next_rel',
            out_attr_tys)
      end.
  End WithVarenv.
End __.
