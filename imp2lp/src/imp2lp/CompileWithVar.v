(* Include mutable variable constructs and use Owen's Datalog definitions *)

From Stdlib Require Import String ZArith List Bool Permutation.
From coqutil Require Import Map.Interface Decidable.
Require Import Datalog.Datalog.
Require Import imp2lp.SrcLangWithVar imp2lp.Value.
Require Import coqutil.Datatypes.Result.
Require Import coqutil.Tactics.case_match.
Import ListNotations.

Inductive var : Type :=
| name_var : string -> var
| attr_var : string * string -> var
| time_var : var .

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
  (* Assume no shadowing and and no repeated use of the same variable name,
so we can use variable names as relation/datalog var names. *)
  | str_rel : string -> rel (* unary for variables, assuming SSA form *)
  | nat_rel : nat -> rel
  | blk_rel : nat -> rel
  | ret_rel : rel
  | true_rel (* unary, true if arg is true *).

Variant aggregator : Set :=.

Definition var_eqb (x y : var) : bool :=
  match x, y with
  | name_var x, name_var y => (x =? y)%string
  | attr_var (x1, x2), attr_var (y1, y2) => (x1 =? y1)%string && (x2 =? y2)%string
  | time_var, time_var => true
  | _, _ => false
  end.

Lemma var_eqb_spec x y : BoolSpec (x = y) (x <> y) (var_eqb x y).
Proof.
  destruct x, y; simpl; repeat case_match; try (constructor; congruence).
  1: destruct (s =? s0)%string eqn:E; constructor;
  rewrite ?String.eqb_eq, ?String.eqb_neq in *; congruence.
  1: destruct (s =? s1)%string eqn:E1;
  destruct (s0 =? s2)%string eqn:E2; cbn; constructor;
  rewrite ?String.eqb_eq, ?String.eqb_neq in *; try congruence.
Qed.

Section __.
  Let interp_fn (f : fn) (l : list obj) : option obj :=
        match f with
        | fnB f => option_map Bobj (interp_Bfn f l)
        | fnZ f => option_map Zobj (interp_Zfn f l)
        | fnS f => option_map Sobj (interp_Sfn f l)
        end.

  Let get_set (x : obj) : option (list obj) := None.

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
  Local Notation fact := (fact rel var fn).

  Section WithVarenv.
    (* Context {varenv : map.map string rel} {varenv_ok : map.ok varenv}. *)
    Context {attrenv : map.map (string * string) var} {attrenv_ok : map.ok attrenv}.
    Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.

    Context (timestamp_attr singleton_attr: string).

    Section WithTimestamp.
      Context (in_timestamp : dexpr).

      Fixpoint lower_aexpr (m : attrenv) (e : aexpr) : (dexpr * list fact) :=
        (* Assume no variable shadowing and no reuse of variable names, even across mutable and immutable variables
         m: maps each (row variable, attribute) pair to a datalog variable.
         return (datalog expression, list of clauses assumed for the expression, new threshold for fresh variables *)
        match e with
        | AVar x | ALoc x => (var_expr (name_var x), [ {| fact_R:=str_rel x; fact_args:=[in_timestamp; var_expr (name_var x)] |} ])
        | ABool b => (fun_expr (fnB (fn_BLit b)) [], [])
        | AInt n => (fun_expr (fnZ (fn_ZLit n)) [], [])
        | AString s => (fun_expr (fnS (fn_SLit s)) [], [])
        | ALet e1 x e2 => let '(e1', conds1) := lower_aexpr m e1 in
                          let '(e2', conds2) := lower_aexpr m e2 in
                          (e2', {| fact_R:=str_rel x; fact_args:=[in_timestamp; e1'] |} :: conds1 ++ conds2)
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

      Fixpoint get_aexpr_type (Gstore Genv : tenv) (e : aexpr) : type :=
        match e with
        | AVar x => match map.get Genv x with
                    | Some t => t
                    | _ => TBool (* unused case *)
                    end
        | ALoc x => match map.get Gstore x with
                    | Some t => t
                    | _ => TBool (* unused case *)
                    end
        | ABool _ | ANot _ | AAnd _ _ => TBool
        | AInt _ | APlus _ _ | AStringLength _ => TInt
        | AString _ | AStringConcat _ _ => TString
        | ALet e1 x e2 => get_aexpr_type Gstore (map.put Genv x (get_aexpr_type Gstore Genv e1)) e2
        | AAccess x attr => match map.get Genv x with
                            | Some (TRecord tl) => match access_record tl attr with
                                                   | Success t => t
                                                   | _ => TBool (* unused case *)
                                                   end
                            | _ => TBool (* unused cases *)
                            end
        end.

      Definition lower_rexpr (Gstore Genv : tenv) (m : attrenv) (e : rexpr) : list dexpr * list fact * list (string * type) :=
        match e with
          RRecord l =>
            (List.map (fun '(_, a) => fst (lower_aexpr m a)) (record_sort l),
              List.concat (List.map (fun '(_, a) => snd (lower_aexpr m a)) (record_sort l)),
              List.map (fun '(s, a) => (s, get_aexpr_type Gstore Genv a)) (record_sort l))
        end.

      Fixpoint mk_vars (name : string) (tl : list (string * type)) : list var :=
        match tl with
        | [] => []
        | (attr, _) :: tl => attr_var (name, attr) :: (mk_vars name tl)
        end.

      Fixpoint put_attr_bindings (m : attrenv) (x : string) (attrs : list string) (vars : list var) : attrenv :=
        match attrs, vars with
        | [], _ | _, [] => m
        | attr :: attrs, v :: vars =>
            map.put (put_attr_bindings m x attrs vars) (x, attr) v
        end.

      Definition lower_rec_type : list (string * type) -> list (string * dtype) :=
        List.map (fun '(s, t) => (s, lower_type t)).
    End WithTimestamp.

    Section WithTimestamp.
      Section WithGstore.
        Context (Gstore : tenv).
        Context (blk_hyps : list fact). (* assumptions created in lower_block *)

        Fixpoint lower_expr (in_timestamp out_timestamp : dexpr) (out : rel) (next_rel : nat) (e : expr) :
          list decl * list rule * nat * list (string * type) :=
          match e with
          | EAtom a =>
              let '(a', asms) := lower_aexpr in_timestamp map.empty a in
              ([],
                [{| rule_concls := [{| fact_R := out; fact_args := [out_timestamp; a'] |}];
                   rule_hyps := asms ++ blk_hyps;
                   rule_agg := None;
                   rule_set_hyps := [] |}],
                next_rel,
                [(singleton_attr, get_aexpr_type Gstore map.empty a)])
          | ELoc x =>
              let attr_tys := match map.get Gstore x with
                              | Some (TSet (TRecord l)) => l
                              | _ => [] (* unreachable for well-typed expressions *)
                              end in
              let vs := List.map var_expr (mk_vars x attr_tys) in
              ([],
                [{| rule_concls := [{| fact_R := out; fact_args := out_timestamp :: vs |}];
                   rule_hyps := [{| fact_R := str_rel x; fact_args := in_timestamp :: vs|}] ++ blk_hyps;
                   rule_agg := None;
                   rule_set_hyps := [] |}],
                next_rel,
                attr_tys)
          | EEmptySet tl => ([], [], next_rel, tl)
          | ESetInsert r s =>
              let '(r', asms, _) := lower_rexpr in_timestamp Gstore map.empty map.empty r in
              let aux := nat_rel next_rel in
              let '(dcls, rls, next_rel', attr_tys) := lower_expr in_timestamp in_timestamp aux (S next_rel) s in
              let vs := List.map var_expr (mk_vars "" attr_tys) in
              (dcls ++
                 [ {| decl_R := aux; decl_sig := lower_rec_type ((timestamp_attr, TInt) :: attr_tys) |} ],
                rls ++
                  [ {| rule_concls := [{| fact_R := out; fact_args := out_timestamp :: r' |}];
                      rule_hyps := asms ++ blk_hyps;
                      rule_agg := None;
                      rule_set_hyps := [] |};
                    {| rule_concls := [{| fact_R := out; fact_args := out_timestamp :: vs |}];
                      rule_hyps := [ {| fact_R := aux; fact_args := in_timestamp :: vs |} ] ++ blk_hyps;
                      rule_agg := None;
                      rule_set_hyps := [] |} ],
                next_rel',
                attr_tys)
          | EFilter s x p =>
              (* out vs :- aux vs, p *)
              let aux := nat_rel next_rel in
              let '(dcls, rls, next_rel', attr_tys) := lower_expr in_timestamp in_timestamp aux (S next_rel) s in
              let vars := mk_vars x attr_tys in
              let p_asms := List.map (lower_pexpr in_timestamp (put_attr_bindings map.empty x (List.map fst attr_tys) vars)) p in
              let ps' := List.map fst p_asms in
              let asms := List.concat (List.map snd p_asms) in
              let vs := List.map var_expr vars in
              (dcls ++
                 [ {| decl_R := aux; decl_sig := lower_rec_type ((timestamp_attr, TInt) :: attr_tys) |} ],
                rls ++
                  [ {| rule_concls := [ {| fact_R := out; fact_args := out_timestamp :: vs |} ];
                      rule_hyps := [ {| fact_R := aux; fact_args := in_timestamp :: vs |} ] ++
                                     (List.map (fun p' => {| fact_R := true_rel; fact_args := [p'] |}) ps') ++
                                     asms ++ blk_hyps;
                      rule_agg := None;
                      rule_set_hyps := [] |} ],
                next_rel',
                attr_tys)
          | EJoin s1 s2 x1 x2 p r =>
              (* out (lower_rexpr m r) :- aux1 vs1, aux2 vs2, lower_aexpr m p *)
              let aux1 := nat_rel next_rel in
              let '(dcls1, rls1, next_rel1, attr_tys1) := lower_expr in_timestamp in_timestamp aux1 (S next_rel) s1 in
              let aux2 := nat_rel next_rel1 in
              let '(dcls2, rls2, next_rel2, attr_tys2) := lower_expr in_timestamp in_timestamp aux2 (S next_rel1) s2 in
              let vars1 := mk_vars x1 attr_tys1 in
              let vars2 := mk_vars x2 attr_tys2 in
              let m := put_attr_bindings (put_attr_bindings map.empty x1 (List.map fst attr_tys1) vars1) x2 (List.map fst attr_tys2) vars2 in
              let vs1 := List.map var_expr vars1 in
              let vs2 := List.map var_expr vars2 in
              let p_asms := List.map (lower_pexpr in_timestamp m) p in
              let ps' := List.map fst p_asms in
              let asms_p := List.concat (List.map snd p_asms) in
              let '(r', asms_r, attr_tys) := lower_rexpr in_timestamp Gstore (map.put (map.put map.empty x1 (TRecord attr_tys1)) x2 (TRecord attr_tys2)) m r in
              (dcls1 ++ dcls2 ++
                 [ {| decl_R := aux1; decl_sig := lower_rec_type ((timestamp_attr, TInt) :: attr_tys1) |};
                   {| decl_R := aux2; decl_sig := lower_rec_type ((timestamp_attr, TInt) :: attr_tys2) |} ],
                rls1 ++ rls2 ++
                  [ {| rule_concls := [ {| fact_R := out; fact_args := out_timestamp :: r' |} ] ;
                      rule_hyps :=
                        [ {| fact_R := aux1; fact_args := in_timestamp :: vs1 |};
                          {| fact_R := aux2; fact_args := in_timestamp :: vs2 |} ] ++
                          (List.map (fun p' => {| fact_R := true_rel; fact_args := [p'] |}) ps') ++
                          asms_r ++ asms_p ++ blk_hyps;
                      rule_agg := None;
                      rule_set_hyps := [] |} ],
                next_rel2,
                attr_tys)
          | EProj s x r =>
              (* out rs :- aux vs *)
              let aux := nat_rel next_rel in
              let '(dcls, rls, next_rel', attr_tys) := lower_expr in_timestamp in_timestamp aux (S next_rel) s in
              let vars := mk_vars x attr_tys in
              let '(r', asms, out_attr_tys) := lower_rexpr in_timestamp Gstore (map.put map.empty x (TRecord attr_tys)) (put_attr_bindings map.empty x (List.map fst attr_tys) vars) r in
              let vs := List.map var_expr vars in
              (dcls ++
                 [ {| decl_R := aux; decl_sig := lower_rec_type ((timestamp_attr, TInt) :: attr_tys) |} ],
                rls ++
                  [ {| rule_concls := [ {| fact_R := out; fact_args := out_timestamp :: r' |} ];
                      rule_hyps := [ {| fact_R := aux; fact_args := in_timestamp :: vs |} ] ++ asms ++ blk_hyps;
                      rule_agg := None;
                      rule_set_hyps := [] |}],
                next_rel',
                out_attr_tys)
          end.
      End WithGstore.
    End WithTimestamp.

    Fixpoint mk_tenv (muts : list (string * type)) : tenv :=
      match muts with
      | [] => map.empty
      | (x, t) :: muts => map.put (mk_tenv muts) x t
      end.

    Definition dexpr_plus_one (e : dexpr) :=
      fun_expr (fnZ fn_Plus) [e; fun_expr (fnZ (fn_ZLit 1)) []].

    Fixpoint lower_mut_assignments (hyps : list fact) (Gstore : tenv) (next_rel : nat) (asgs : list (string * expr)) : list decl * list rule * nat :=
      match asgs with
      | [] => ([], [], next_rel)
      | (x, e) :: asgs =>
          let '(dcls0, rls0, next_rel0, _) :=
            lower_expr Gstore
            hyps (* blk_hyps *)
            (dexpr_plus_one (var_expr time_var)) (* out_timestamp*)
            (var_expr time_var) (* in_timestamp *)
            (str_rel x) next_rel e in
          let '(dcls, rls, next_rel') :=
            lower_mut_assignments hyps Gstore next_rel0 asgs in
          (dcls0 ++ dcls, rls0 ++ rls, next_rel')
      end.

    Definition lower_block (g : cfg) (next_rel : nat) (blk_id : nat) : list decl * list rule * nat :=
      let '(muts, blks) := g in
      let Gstore := mk_tenv muts in
      match nth_error blks blk_id with
      | Some blk =>
          match blk with
          | BGoto (n, es) =>
              let '(dcls, rls, next_rel') :=
                lower_mut_assignments
                  [{| fact_R := blk_rel blk_id; fact_args := [var_expr time_var] |}]
                  Gstore next_rel (combine (List.map fst muts) es) in
              (dcls,
                rls ++
                  [{| rule_concls := [ {| fact_R := blk_rel n; fact_args := [dexpr_plus_one (var_expr time_var)] |} ];
                     rule_hyps := [ {| fact_R := blk_rel blk_id; fact_args := [var_expr time_var]|} ];
                     rule_agg := None;
                     rule_set_hyps := [] |}], next_rel')
          | BIf p (n1, es1) (n2, es2) =>
              let '(p', asms) := lower_pexpr (var_expr time_var) map.empty p in
              let '(dcls1, rls1, next_rel1) :=
                lower_mut_assignments
                  ([{| fact_R := blk_rel blk_id; fact_args := [var_expr time_var] |};
                   {| fact_R := true_rel; fact_args := [p'] |} ] ++ asms)
                  Gstore next_rel (combine (List.map fst muts) es1) in
              let neg_p' := fun_expr (fnB fn_Not) [p'] in
              let '(dcls2, rls2, next_rel2) :=
                lower_mut_assignments
                  ([{| fact_R := blk_rel blk_id; fact_args := [var_expr time_var] |};
                   {| fact_R := true_rel; fact_args := [neg_p'] |} ] ++ asms)
                  Gstore next_rel (combine (List.map fst muts) es2) in
              (dcls1 ++ dcls2,
                rls1 ++ rls2 ++
                  [{| rule_concls := [{| fact_R := blk_rel n1; fact_args := [dexpr_plus_one (var_expr time_var)] |}];
                     rule_hyps := [{| fact_R := blk_rel blk_id; fact_args := [var_expr time_var] |};
                                   {| fact_R := true_rel; fact_args := [p'] |} ] ++ asms;
                     rule_agg := None;
                     rule_set_hyps := [] |};
                  {| rule_concls := [{| fact_R := blk_rel n2; fact_args := [dexpr_plus_one (var_expr time_var)] |}];
                     rule_hyps := [{| fact_R := blk_rel blk_id; fact_args := [var_expr time_var] |};
                                   {| fact_R := true_rel; fact_args := [neg_p'] |} ] ++ asms;
                     rule_agg := None;
                     rule_set_hyps := [] |}],
              next_rel2)

          | BRet =>
              ([],
                [ {| rule_concls := [ {| fact_R := ret_rel ; fact_args := [var_expr time_var] |} ];
                    rule_hyps := [ {| fact_R := blk_rel blk_id; fact_args := [var_expr time_var] |} ];
                    rule_agg := None;
                    rule_set_hyps := [] |} ], next_rel)
          end
      | None => ([], [], 0) (* unreachable case *)
      end.

    Fixpoint lower_blocks (g : cfg) (next_rel : nat) (blk_id : nat) : list decl * list rule * nat :=
      match blk_id with
      | O => lower_block g next_rel O
      | S n => let '(dcls1, rls1, next_rel1) := lower_blocks g next_rel n in
               let '(dcls2, rls2, next_rel2) := lower_block g next_rel1 (S n) in
               (dcls1 ++ dcls2, rls1 ++ rls2, next_rel2)
      end.

    Definition lower_cfg (g : cfg) : list decl * list rule :=
      let '(muts_tys, blks) := g in
      let mut_dcls := List.map
                        (fun '(x, t) =>
                           {| decl_R := str_rel x;
                             decl_sig := match t with
                                         | TSet (TRecord tl) => (timestamp_attr, DNumber) :: lower_rec_type tl
                                         | t => [(timestamp_attr, DNumber); (singleton_attr, lower_type t)]
                                         end |})
                        muts_tys in
      let '(dcls, rls, _) := match List.length blks with
                             | O => ([], [], 0)
                             | S n => lower_blocks g O n
                             end in
      (mut_dcls ++ dcls, rls).
  End WithVarenv.


End __.
