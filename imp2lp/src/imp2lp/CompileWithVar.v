(* Include mutable variable constructs and use Owen's Datalog definitions *)

From Stdlib Require Import String ZArith List Bool Permutation.
From coqutil Require Import Map.Interface Decidable.
Require Import Datalog.Datalog.
Require Import imp2lp.SrcLangWithVar imp2lp.Value.
Require Import coqutil.Datatypes.Result.
Require Import coqutil.Tactics.case_match.
Import ListNotations.

Inductive var : Type :=
| singleton_var : string -> var
| access_var : string * string -> var
| attr_var : string -> var
| time_var : var.

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
  | str_rel : string -> rel (* unary for variables *)
  | res_rel : string -> rel (* for the values of mutable variables upon program termination *)
  | nat_rel : nat -> rel
  | blk_rel : nat -> rel
  | ret_rel : rel
  | true_rel (* unary, true if arg is true *).

Variant aggregator : Set :=.

Definition var_eqb (x y : var) : bool :=
  match x, y with
  | singleton_var x, singleton_var y => (x =? y)%string
  | access_var (x1, x2), access_var (y1, y2) => (x1 =? y1)%string && (x2 =? y2)%string
  | attr_var x, attr_var y => (x =? y)%string
  | time_var, time_var => true
  | _, _ => false
  end.

Lemma var_eqb_spec x y : BoolSpec (x = y) (x <> y) (var_eqb x y).
Proof.
  destruct x, y; simpl; repeat case_match; try (constructor; congruence).
  1,3: destruct (s =? s0)%string eqn:E; constructor;
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
    (* Context {varenv : map.map string rel} {varenv_ok : map.ok varenv}.
    Context {attrenv : map.map (string * string) var} {attrenv_ok : map.ok attrenv}. *)
    Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.

    Context (timestamp_attr singleton_attr: string).

    Section WithTimestamp.
      Context (in_timestamp : dexpr).

      Fixpoint lower_aexpr (e : aexpr) : (dexpr * list fact) :=
        (* Assume no variable shadowing and no reuse of variable names, even across mutable and immutable variables
         m: maps each (row variable, attribute) pair to a datalog variable.
         return (datalog expression, list of clauses assumed for the expression, new threshold for fresh variables *)
        match e with
        | AVar x => (var_expr (singleton_var x), [])
        | ALoc x => (var_expr (singleton_var x), [ {| fact_R:=str_rel x; fact_args:=[in_timestamp; var_expr (singleton_var x)] |} ])
        | ABool b => (fun_expr (fnB (fn_BLit b)) [], [])
        | AInt n => (fun_expr (fnZ (fn_ZLit n)) [], [])
        | AString s => (fun_expr (fnS (fn_SLit s)) [], [])
        | ALet e1 x e2 => let '(e1', conds1) := lower_aexpr e1 in
                          let '(e2', conds2) := lower_aexpr e2 in
                          (e2', {| fact_R:=true_rel; fact_args:=[fun_expr (fnB fn_Eq) [var_expr (singleton_var x); e1']] |} :: conds1 ++ conds2)
        | ANot e => let '(e', conds) := lower_aexpr e in
                    (fun_expr (fnB fn_Not) [e'], conds)
        | AAnd e1 e2 => let '(e1', conds1) := lower_aexpr e1 in
                        let '(e2', conds2) := lower_aexpr e2 in
                        (fun_expr (fnB fn_And) [e1'; e2'], conds1 ++ conds2)
        | APlus e1 e2 => let '(e1', conds1) := lower_aexpr e1 in
                         let '(e2', conds2) := lower_aexpr e2 in
                         (fun_expr (fnZ fn_Plus) [e1'; e2'], conds1 ++ conds2)
        | AStringConcat e1 e2 => let '(e1', conds1) := lower_aexpr e1 in
                                 let '(e2', conds2) := lower_aexpr e2 in
                                 (fun_expr (fnS fn_StringConcat) [e1'; e2'], conds1 ++ conds2)
        | AStringLength e => let '(e', conds) := lower_aexpr e in
                             (fun_expr (fnZ fn_StringLength) [e'], conds)
        | AAccess x attr => (var_expr (access_var (x, attr)), [])
        end.

      Definition lower_pexpr (e : pexpr) : (dexpr * list fact) :=
        match e with
        | PLt e1 e2 =>
            let '(e1', conds1) := lower_aexpr e1 in
            let '(e2', conds2) := lower_aexpr e2 in
            (fun_expr (fnB fn_Lt) [e1'; e2'], conds1 ++ conds2)
        | PEq e1 e2 =>
            let '(e1', conds1) := lower_aexpr e1 in
            let '(e2', conds2) := lower_aexpr e2 in
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

      Definition get_rexpr_type (Gstore Genv : tenv) (r : rexpr) : type :=
        match r with
          RRecord l =>
            TRecord
              (List.map (fun '(attr, a) => (attr, get_aexpr_type Gstore Genv a)) l)
        end.

      Fixpoint get_expr_type (Gstore : tenv) (e : expr) : type :=
        match e with
        | EAtom a => get_aexpr_type Gstore map.empty a
        | ELoc x => match map.get Gstore x with
                    | Some t => t
                    | _ => TBool (* unused case *)
                    end
        | EEmptySet tl => TSet (TRecord tl)
        | ESetInsert r e => get_expr_type Gstore e
        | EFilter e x p => get_expr_type Gstore e
        | EJoin e1 e2 x1 x2 p r =>
            match get_expr_type Gstore e1 with
            | TSet t1 =>
                match get_expr_type Gstore e2 with
                | TSet t2 =>
                    TSet (get_rexpr_type Gstore (map.put (map.put map.empty x1 t1) x2 t2) r)
                | _ => TBool
                end
            | _ => TBool
            end
        | EProj e x r =>
            match get_expr_type Gstore e with
            | TSet t =>
                TSet (get_rexpr_type Gstore (map.put map.empty x t) r)
            | _ => TBool
            end
        end.


      Definition lower_rexpr (Gstore Genv : tenv) (e : rexpr) : list dexpr * list fact * list (string * dtype) :=
        match e with
          RRecord l =>
            (List.map (fun '(_, a) => fst (lower_aexpr a)) (record_sort l),
              List.concat (List.map (fun '(_, a) => snd (lower_aexpr a)) (record_sort l)),
              List.map (fun '(s, a) => (s, lower_type (get_aexpr_type Gstore Genv a))) (record_sort l))
        end.

      Fixpoint mk_vars (name : string) (attrs : list string) : list var :=
        match attrs with
        | [] => []
        | attr :: attrs => access_var (name, attr) :: (mk_vars name attrs)
        end.

      (* ??? remove
      Fixpoint put_attr_bindings (m : attrenv) (x : string) (attrs : list string) (vars : list var) : attrenv :=
        match attrs, vars with
        | [], _ | _, [] => m
        | attr :: attrs, v :: vars =>
            map.put (put_attr_bindings m x attrs vars) (x, attr) v
        end.
*)
      Definition lower_rec_type : list (string * type) -> list (string * dtype) :=
        List.map (fun '(s, t) => (s, lower_type t)).
    End WithTimestamp.

    Definition dexpr_zero : dexpr := fun_expr (fnZ (fn_ZLit 0)) [].
    Definition dexpr_plus_one (e : dexpr) :=
      fun_expr (fnZ fn_Plus) [e; fun_expr (fnZ (fn_ZLit 1)) []].

    Section WithTimestamp.
      Section WithGstore.
        Context (Gstore : tenv).
        Context (blk_hyps : list fact). (* assumptions created in lower_block *)

        Fixpoint lower_expr (to_next_ts : bool) (out : rel) (next_rel : nat) (e : expr) :
          list decl * list rule * nat * list (string * dtype) :=
          let in_timestamp := var_expr time_var in
          let out_timestamp := if to_next_ts
                               then dexpr_plus_one in_timestamp
                               else in_timestamp in
          match e with
          | EAtom a =>
              let '(a', asms) := lower_aexpr in_timestamp a in
              ([],
                [{| rule_concls := [{| fact_R := out; fact_args := [out_timestamp; a'] |}];
                   rule_hyps := asms ++ blk_hyps;
                   rule_agg := None;
                   rule_set_hyps := [] |}],
                next_rel,
                [(singleton_attr, lower_type (get_aexpr_type Gstore map.empty a))])
          | ELoc x =>
              let tl := match map.get Gstore x with
                              | Some (TSet (TRecord tl)) => tl
                              | _ => [] (* unreachable for well-typed expressions *)
                              end in
              let attr_tys := lower_rec_type tl in
              let vs := List.map (fun x => var_expr (attr_var x)) (List.map fst tl) in
              ([],
                [{| rule_concls := [{| fact_R := out; fact_args := out_timestamp :: vs |}];
                   rule_hyps := [{| fact_R := str_rel x; fact_args := in_timestamp :: vs|}] ++ blk_hyps;
                   rule_agg := None;
                   rule_set_hyps := [] |}],
                next_rel,
                attr_tys)
          | EEmptySet tl => ([], [], next_rel, lower_rec_type tl)
          | ESetInsert r s =>
              let '(r', asms, _) := lower_rexpr in_timestamp Gstore map.empty r in
              let aux := nat_rel next_rel in
              let '(dcls, rls, next_rel', attr_tys) := lower_expr false aux (S next_rel) s in
              let tl := match get_rexpr_type Gstore map.empty r with
                        | TSet (TRecord tl) => tl
                        | _ => []
                        end in
              let vs := List.map (fun attr => var_expr (attr_var attr)) (List.map fst tl) in
              (dcls ++
                 [ {| decl_R := aux; decl_sig := (timestamp_attr, DNumber) :: attr_tys |} ],
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
              let '(dcls, rls, next_rel', attr_tys) := lower_expr false aux (S next_rel) s in
              let tl := match get_expr_type Gstore s with
                        | TSet (TRecord tl) => tl
                        | _ => []
                        end in
              let vars := mk_vars x (List.map fst tl) in
              let p_asms := List.map (lower_pexpr in_timestamp) p in
              let ps' := List.map fst p_asms in
              let asms := List.concat (List.map snd p_asms) in
              let vs := List.map var_expr vars in
              (dcls ++
                 [ {| decl_R := aux; decl_sig := (timestamp_attr, DNumber) :: attr_tys |} ],
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
              (* out (lower_rexpr m r) :- aux1 vs1, aux2 vs2, lower_aexpr p *)
              let aux1 := nat_rel next_rel in
              let '(dcls1, rls1, next_rel1, attr_tys1) := lower_expr false aux1 (S next_rel) s1 in
              let aux2 := nat_rel next_rel1 in
              let '(dcls2, rls2, next_rel2, attr_tys2) := lower_expr false aux2 (S next_rel1) s2 in
              let tl1 := match get_expr_type Gstore s1 with
                         | TSet (TRecord tl1) => tl1
                         | _ => []
                         end in
              let tl2 := match get_expr_type Gstore s2 with
                         | TSet (TRecord tl2) => tl2
                         | _ => []
                         end in
              let vars1 := mk_vars x1 (List.map fst tl1) in
              let vars2 := mk_vars x2 (List.map fst tl2) in
              let vs1 := List.map var_expr vars1 in
              let vs2 := List.map var_expr vars2 in
              let p_asms := List.map (lower_pexpr in_timestamp) p in
              let ps' := List.map fst p_asms in
              let asms_p := List.concat (List.map snd p_asms) in
              let Genv := map.put (map.put map.empty x1 (TRecord tl1)) x2 (TRecord tl2) in
              let '(r', asms_r, attr_tys) := lower_rexpr in_timestamp Gstore Genv r in
              (dcls1 ++ dcls2 ++
                 [ {| decl_R := aux1; decl_sig := (timestamp_attr, DNumber) :: attr_tys1 |};
                   {| decl_R := aux2; decl_sig := (timestamp_attr, DNumber) :: attr_tys2 |} ],
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
              let '(dcls, rls, next_rel', attr_tys) := lower_expr false aux (S next_rel) s in
              let tl := match get_expr_type Gstore s with
                        | TSet (TRecord tl) => tl
                        | _ => []
                        end in
              let vars := mk_vars x (List.map fst attr_tys) in
              let Genv := map.put map.empty x (TRecord tl) in
              let '(r', asms, out_attr_tys) := lower_rexpr in_timestamp Gstore Genv r in
              let vs := List.map var_expr vars in
              (dcls ++
                 [ {| decl_R := aux; decl_sig := (timestamp_attr, DNumber) :: attr_tys |} ],
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

    (* ??? remove
    Fixpoint lower_mut_assignments0 (next_rel : nat) (asgs : list (string * expr)) :
      list decl * list rule * nat :=
      match asgs with
      | [] => ([], [], next_rel)
      | (x, e) :: asgs =>
          let '(dcls0, rls0, next_rel0, _) :=
            lower_expr map.empty
              [] (* no hypothesis at entry *)
              dexpr_zero (* out_timestamp*)
              dexpr_zero (* in_timestamp *)
              (str_rel x) next_rel e in
          let '(dcls, rls, next_rel') :=
            lower_mut_assignments0 next_rel0 asgs in
          (dcls0 ++ dcls, rls0 ++ rls, next_rel')
      end.
*)
    Fixpoint lower_mut_assignments (hyps : list fact) (Gstore : tenv) (next_rel : nat) (asgs : list (string * expr)) :
          list decl * list rule * nat :=
      match asgs with
      | [] => ([], [], next_rel)
      | (x, e) :: asgs =>
          let '(dcls0, rls0, next_rel0, _) :=
            lower_expr Gstore
            hyps (* blk_hyps *)
            true (* increment timestamp *)
            (str_rel x) next_rel e in
          let '(dcls, rls, next_rel') :=
            lower_mut_assignments hyps Gstore next_rel0 asgs in
          (dcls0 ++ dcls, rls0 ++ rls, next_rel')
      end.

    Definition lower_block (sig : list (string * type)) (next_rel : nat) (blk : block) (blk_id : nat) :
      list decl * list rule * nat :=
      let Gstore := mk_tenv sig in
      match blk with
      | BGoto es n =>
          let '(dcls, rls, next_rel') :=
            lower_mut_assignments
              [{| fact_R := blk_rel blk_id; fact_args := [var_expr time_var] |}]
              Gstore next_rel (combine (List.map fst sig) es) in
          (dcls,
            rls ++
              [{| rule_concls := [ {| fact_R := blk_rel n; fact_args := [dexpr_plus_one (var_expr time_var)] |} ];
                 rule_hyps := [ {| fact_R := blk_rel blk_id; fact_args := [var_expr time_var]|} ];
                 rule_agg := None;
                 rule_set_hyps := [] |}], next_rel')
      | BIf p es1 n1 es2 n2 =>
          let '(p', asms) := lower_pexpr (var_expr time_var) p in
          let '(dcls1, rls1, next_rel1) :=
            lower_mut_assignments
              ([{| fact_R := blk_rel blk_id; fact_args := [var_expr time_var] |};
                {| fact_R := true_rel; fact_args := [p'] |} ] ++ asms)
              Gstore next_rel (combine (List.map fst sig) es1) in
          let neg_p' := fun_expr (fnB fn_Not) [p'] in
          let '(dcls2, rls2, next_rel2) :=
            lower_mut_assignments
              ([{| fact_R := blk_rel blk_id; fact_args := [var_expr time_var] |};
                {| fact_R := true_rel; fact_args := [neg_p'] |} ] ++ asms)
              Gstore next_rel (combine (List.map fst sig) es2) in
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
      end.

    Fixpoint lower_blocks  (sig : list (string * type)) (next_rel : nat) (blks : list block) (cur_id : nat) : list decl * list rule * nat :=
      match blks with
      | [] => ([], [], next_rel)
      | blk :: blks =>
          let '(dcls1, rls1, next_rel1) := lower_block sig next_rel blk cur_id in
          let '(dcls2, rls2, next_rel2) := lower_blocks sig next_rel1 blks (S cur_id) in
          (dcls1 ++ dcls2, rls1 ++ rls2, next_rel2)
      end.

    Definition lower_mut_res (mut_ty : (string * type)) : rule :=
      let '(x, t) := mut_ty in
      match t with
      | TSet (TRecord tl)
      | TRecord tl =>
          let vs := List.map (fun x => var_expr (attr_var x)) (List.map fst tl) in
          {| rule_concls := [ {| fact_R := res_rel x; fact_args := vs |} ];
            rule_hyps := [ {| fact_R := ret_rel; fact_args := [var_expr time_var] |};
                           {| fact_R := str_rel x; fact_args := var_expr time_var :: vs |}];
            rule_agg := None;
            rule_set_hyps := [] |}
      | t =>
          let v := var_expr (singleton_var x) in
          {| rule_concls := [ {| fact_R := res_rel x; fact_args := [v] |} ];
            rule_hyps := [ {| fact_R := ret_rel; fact_args := [var_expr time_var] |};
                           {| fact_R := str_rel x; fact_args := [var_expr time_var; v] |}];
            rule_agg := None;
            rule_set_hyps := [] |}
      end.

    Definition decl_mut_rels (p : string *  type) : list decl :=
      let '(x, t) := p in
      match t with
      | TSet (TRecord tl)
      | TRecord tl =>
          [ {| decl_R := str_rel x;
              decl_sig := (timestamp_attr, DNumber) :: lower_rec_type tl |};
            {| decl_R := res_rel x;
              decl_sig := lower_rec_type tl |} ]
      | _ =>
          [ {| decl_R := str_rel x;
              decl_sig := (timestamp_attr, DNumber) :: [(singleton_attr, lower_type t)] |};
            {| decl_R := res_rel x;
              decl_sig := [(singleton_attr, lower_type t)] |} ]
      end.

    Definition lower_atomic_value (v : value) : obj :=
      match v with
      | VInt n => Zobj n
      | VBool b => Bobj b
      | VString s => Sobj s
      (* unused cases *)
      | VList _ | VRecord _ | VSet _ => Bobj false
      end.

    Definition lower_rec_value (v : value) : list obj :=
      match v with
      | VRecord l => map (fun p => lower_atomic_value (snd p)) l
      | _ => []
      end.

    Definition dexpr_literal (v : obj) : dexpr :=
      match v with
      | Bobj b => fun_expr (fnB (fn_BLit b)) []
      | Zobj z => fun_expr (fnZ (fn_ZLit z)) []
      | Sobj s => fun_expr (fnS (fn_SLit s)) []
      end.

    Definition lower_init_value (out : rel) (v : value) : list rule :=
      match v with
      | VSet l => map (fun v =>
                         {| rule_concls :=
                             [ {| fact_R := out;
                                 fact_args := dexpr_zero :: map dexpr_literal (lower_rec_value v) |} ];
                           rule_hyps := [];
                           rule_agg := None;
                           rule_set_hyps := [] |}) l
      | VRecord _ => [ {| rule_concls :=
                             [ {| fact_R := out;
                                 fact_args := dexpr_zero :: map dexpr_literal (lower_rec_value v) |} ];
                           rule_hyps := [];
                           rule_agg := None;
                           rule_set_hyps := [] |} ]
      | v => [ {| rule_concls :=
                   [ {| fact_R := out;
                       fact_args := [ dexpr_zero; dexpr_literal (lower_atomic_value v) ] |} ];
                       rule_hyps := [];
                       rule_agg := None;
                       rule_set_hyps := [] |} ]
      end.

    Definition lower_cfg (g : cfg) : list decl * list rule :=
      let g_sig := g.(sig_blks).(sig) in
      let mut_dcls := List.concat (map decl_mut_rels g_sig) in
      let init_str_rls := List.concat
                            (map (fun '(x, v) => lower_init_value (str_rel x) v)
                               (combine (map fst g_sig) g.(str_ptr).(str))) in
      let entry_blk_rl :=
        match g.(str_ptr).(ptr) with
        | Some n =>
            {| rule_concls :=
                [{| fact_R := blk_rel n; fact_args := [dexpr_zero] |}];
              rule_hyps := [];
              rule_agg := None;
              rule_set_hyps := [] |}
        | None =>
            {| rule_concls :=
                [{| fact_R := ret_rel; fact_args := [dexpr_zero] |}];
              rule_hyps := [];
              rule_agg := None;
              rule_set_hyps := [] |}
        end in
      let '(dcls, rls, _) := lower_blocks g_sig O g.(sig_blks).(blks) O in
      let res_rls := List.map lower_mut_res g_sig in
      (mut_dcls ++ dcls,
        entry_blk_rl ::
          init_str_rls ++ rls ++ res_rls).

    Context {venv: map.map string value} {venv_ok: map.ok venv}.
    Context {context : map.map var obj} {context_ok: map.ok context}.

    Definition lower_value (v : value) : list (list obj) :=
      (* lower source language value to set of datalog obj tuples *)
      match v with
      | VSet l => map lower_rec_value l
      | VRecord _ => [ lower_rec_value v ]
      | v => (* atomic value *)
          [ [ lower_atomic_value v ] ]
      end.

    Definition is_lowered_to_at (v : value) (rls : list rule) (res : rel) (ts : Z) : Prop :=
      Forall (fun vs => prog_impl_fact rls (res, Zobj ts :: vs)) (lower_value v).

    Definition is_lowered_from_at (rls : list rule) (res : rel) (v : value) (ts : Z) : Prop :=
      forall vs', prog_impl_fact rls (res, Zobj ts :: vs') ->
                  In vs' (lower_value v).

    Definition is_lowered_to (v : value) (rls : list rule) (res : rel) : Prop :=
      Forall (fun vs => prog_impl_fact rls (res, vs)) (lower_value v).

    Definition is_lowered_from (rls : list rule) (res : rel) (v : value) : Prop :=
      forall vs', prog_impl_fact rls (res, vs') ->
                  In vs' (lower_value v).

    Definition venv_is_lowered_to_at (muts : list string) (str : list value) (rls : list rule) (ts : Z) : Prop :=
      Forall2 (fun x v => is_lowered_to_at v rls (str_rel x) ts) muts str.

    Definition venv_is_lowered_to (muts : list string) (str : list value) (rls : list rule) : Prop :=
      Forall2 (fun x v => is_lowered_to v rls (res_rel x)) muts str.

    Definition venv_is_lowered_from_at (rls : list rule) (muts : list string) (str : list value) (ts : Z) : Prop :=
      Forall2 (fun x v => is_lowered_from_at rls (res_rel x) v ts) muts str.

    Definition venv_is_lowered_from (rls : list rule) (muts : list string) (str : list value) : Prop :=
      Forall2 (fun x v => is_lowered_from rls (res_rel x) v) muts str.

    (* ???
    Lemma lower_cfg_complete'' : forall (g : cfg) (store : venv) dcls rls n ts store' m,
        lower_cfg g = (dcls, rls) ->
        well_typed_block g.(sig) g.(blks) n ->
        block_step g.(sig) g.(blks) store n store' m ->
        venv_is_lowered_to_at Gstore store rls ts ->
        prog_impl_fact rls (blk_rel n, [Zobj (Z.of_nat ts)]) ->
        match m with
        | Some n' =>
            venv_is_lowered_to_at Gstore store' rls (S ts) /\
              prog_impl_fact rls (blk_rel n, [Zobj (Z.of_nat ts + 1)])
        | None => store' = store /\
                    venv_is_lowered_to Gstore store' rls
        end.
      Admitted.

    Lemma lower_cfg_complete' : forall (g : cfg) (Gstore : tenv) (store : venv) dcls rls n ts store' m,
        lower_cfg g = (dcls, rls) ->
        Gstore = mk_tenv g.(sig) ->
        well_typed_cfg g ->
        block_steps g.(sig) g.(blks) store n store' m ->
        venv_is_lowered_to_at Gstore store rls ts ->
        prog_impl_fact rls (blk_rel n, [Zobj (Z.of_nat ts)]) ->
        match m with
        | Some n' =>
            exists ts',
            venv_is_lowered_to_at Gstore store' rls ts' /\
              prog_impl_fact rls (blk_rel n, [Zobj (Z.of_nat ts')])
        | None => venv_is_lowered_to Gstore store' rls
        end.
    Admitted.
     *)(*

    Lemma lower_cfg_complete'' : forall (g : cfg) (store : venv) dcls rls blk n ts store' m,
        lower_cfg g = (dcls, rls) ->
        (* well_typed_block g.(sig) (List.length g.(blks)) blk -> *)
        venv_is_lowered_to_at (mk_tenv g.(sig)) store rls ts ->
        nth_error g.(blks) n = Some blk ->
        prog_impl_fact rls (blk_rel n, [Zobj ts]) ->
        block_step g.(sig) store blk store' m ->
        match m with
        | Some n' =>
            venv_is_lowered_to_at (mk_tenv g.(sig)) store' rls (ts + 1) /\
              prog_impl_fact rls (blk_rel n', [Zobj (ts + 1)])
        | None => store' = store /\
                    venv_is_lowered_to (mk_tenv g.(sig)) store' rls
        end.
    Proof.
      intros. inversion H3; subst.
      1:{ unfold lower_cfg in *.
    Admitted.

    Lemma lower_mut_assignments_complete : forall hyps Gstore sig0 args next_rel dcls rls next_rel',
        Forall2 (fun (e : expr) (t : type) => type_of_expr Gstore e t)
          args (map snd sig0) ->
        lower_mut_assignments hyps Gstore next_rel (combine (map fst sig0) args) = (dcls, rls, next_rel') ->
        venv_is_lowered_to_at (mk_tenv sig0)
          (mk_venv (map fst sig0) (map (interp_expr map.empty) args))
          rls 0.

    Lemma lower_expr_complete : forall Gstore store blk_hyps in_ts out_ts out next_rel e dcls rls rls0 next_rel' tl' in_v out_v ctx t,
        lower_expr Gstore blk_hyps in_ts out_ts out next_rel e =
          (dcls, rls, next_rel', tl') ->
        type_of_expr Gstore e t ->
        incl rls rls0 ->
        (forall (x,t) in Gstore, (x,v) in store,
           prog_impl_fact rls0 (str_rel x, [in_v; x_v])) ->
      (forall h, In h hyps,
      interp_fact ctx? h h' ->
      prog_impl_fact rls0 h') ->

        Datalog.interp_expr ctx? in_ts (Zobj in_v) ->
        Datalog.interp_expr ctx? out_ts (Zobj out_v) ->
        tenv_wf Gstore ->
        venv_wf Gstore store ->
        is_lowered_to_at t (interp_expr store e) rls out out_v.

    Lemma lower_mut_assignments0_complete : forall sig0 args next_rel dcls rls next_rel',
        Forall2 (fun (e : expr) (t : type) => type_of_expr map.empty e t)
          args (map snd sig0) ->
        lower_mut_assignments0 next_rel (combine (map fst sig0) args) = (dcls, rls, next_rel') ->
        venv_is_lowered_to_at (mk_tenv sig0)
          (mk_venv (map fst sig0) (map (interp_expr map.empty) args))
          rls 0.
    Proof.
      intros *. remember (map snd sig0) as l.
      induction 1; destruct sig0; try discriminate; cbn in *.
        *)

    Lemma prog_impl_fact_weaken : forall (rls rls' : list rule) f,
      prog_impl_fact rls f -> incl rls rls' ->
      prog_impl_fact rls' f.
    Proof.
      unfold prog_impl_fact.
      induction 1. intros.
      econstructor.
      1: eapply incl_Exists; eauto.
      rewrite Forall_forall; intros.
      apply_Forall_In.
    Qed.

    Ltac invert_type_of_value :=
      lazymatch goal with
        H: type_of_value _ _ |- _ =>
          inversion H; subst; clear H
      end.

    Ltac invert_SSorted :=
      lazymatch goal with
        H: Sorted.StronglySorted _ (_ :: _) |- _ =>
          inversion H; subst
      end.

    Lemma interp_expr__dexpr_literal_atomic : forall vl tl,
        type_wf (TRecord tl) ->
        type_of_value (VRecord vl) (TRecord tl) ->
        Forall2 (Datalog.interp_expr map.empty)
          (map dexpr_literal
             (map
                (fun p => lower_atomic_value (snd p))
                vl))
          (map (fun p => lower_atomic_value (snd p))
             vl).
    Proof.
      intros.
      lazymatch goal with
        H: type_wf _ |- _ => inversion H; subst; clear H
      end; invert_type_of_value;
      repeat lazymatch goal with
          H: Forall2 _ (_ :: _) _ |- _ =>
            inversion H; subst; clear H
        end.
      generalize dependent tl.
      induction vl; cbn; constructor;
        destruct tl; invert_Forall2.
      1: destruct (snd a); cbn; econstructor; eauto.
      1:{ cbn in *. invert_Forall.
          repeat invert_Forall2.
          invert_NoDup. invert_SSorted.
          eapply IHvl; eauto. }
    Qed.

    Lemma lower_init_value_complete : forall x v t,
        type_of_value v t ->
        type_wf t ->
        Forall
          (fun vs =>
             prog_impl_fact (lower_init_value (str_rel x) v)
               (str_rel x, Zobj 0 :: vs))
          (lower_value v).
    Proof.
      destruct 1; cbn.
      1-3: repeat econstructor.
      1:{ repeat econstructor.
          eapply interp_expr__dexpr_literal_atomic; eauto.
          constructor; auto. }
      1:{ inversion 1; subst.
          induction l; cbn; constructor.
          1:{ repeat econstructor.
              invert_Forall. instantiate (1:=map.empty).
              lazymatch goal with
                H: type_of_value _ _ |- _ =>
                  inversion H; subst
              end.
              cbn.
              eapply interp_expr__dexpr_literal_atomic; eauto. }
          1:{ invert_Forall.
              rewrite Forall_forall; intros.
              eapply prog_impl_fact_weaken.
              1:{ apply IHl in H5.
                  apply_Forall_In. }
              apply incl_tl, incl_refl. }
          Unshelve. all: apply map.empty. }
    Qed.

    Lemma venv_is_lowered_to_at_0 : forall g_sig g_str rls,
        sig_wf g_sig ->
        str_wf (map snd g_sig) g_str ->
        incl (concat
                (map (fun '(x, v) => lower_init_value (str_rel x) v)
                   (combine (map fst g_sig) g_str))) rls ->
        venv_is_lowered_to_at (map fst g_sig) g_str rls 0.
    Proof.
      unfold str_wf, sig_wf. induction g_sig; cbn; intros;
        invert_Forall2; constructor; cbn in *;
        intuition idtac; invert_Forall; invert_NoDup.
      1:{ unfold is_lowered_to_at.
          rewrite Forall_forall.
          intros.
          lazymatch goal with
            H: type_of_value _ _ |- _ =>
              eapply lower_init_value_complete in H
          end; trivial.
          apply_Forall_In.
          eapply prog_impl_fact_weaken; eauto.
          eapply List.incl_app_bw_l; eassumption. }
      1:{ apply IHg_sig; auto.
          eapply List.incl_app_bw_r. eauto. }
    Qed.

    Lemma cfg_steps__ptr_Some : forall g_sig g_d g_d',
        cfg_steps g_sig g_d g_d' ->
        forall n',
        g_d'.(ptr) = Some n' ->
        exists n, g_d.(ptr) = Some n.
    Proof.
      induction 1; intros.
      1: eexists; eauto.
      1:{ lazymatch goal with
          H: cfg_step _ _ _ |- _ =>
            destruct H
        end.
          eauto. }
    Qed.

    Ltac rewrite_asm_hyp :=
      lazymatch goal with
        H: ?x = _, _: context[?x] |- _ =>
          rewrite H in *
      end.

    Ltac apply_in_nil :=
      lazymatch goal with
        H: In _ nil |- _ => apply in_nil in H
      end.

    Ltac destruct_In :=
      lazymatch goal with
        H: In _ (_ :: _) |- _ => destruct H; subst end.

    Fixpoint mk_context (m : context) xl vl :=
      match xl, vl with
      | [], _ | _, [] => m
      | x :: xl, v :: vl => mk_context (map.put m x v) xl vl
      end.

    Lemma mk_context_get_put_diff : forall x xl vl,
        ~ In x xl ->
        forall m,
          map.get (mk_context m xl vl) x = map.get m x.
    Proof.
      induction xl; cbn; auto; intros.
      destruct vl; auto.
      intuition idtac.
      erewrite IHxl; auto.
      rewrite_map_get_put_goal.
    Qed.

    Lemma mk_context_rec_sound : forall (vl : list (string * value)) tl,
        Forall2 (fun vp tp => type_of_value (snd vp) (snd tp)) vl tl ->
        NoDup (map fst tl) ->
        forall m,
        Forall2 (Datalog.interp_expr (mk_context m (map attr_var (map fst tl)) (map (fun p => lower_atomic_value (snd p)) vl)))
          (map (fun x => var_expr (attr_var x)) (map fst tl))
          (map (fun p => lower_atomic_value (snd p)) vl).
      induction 1; cbn; constructor.
      1:{ constructor. rewrite mk_context_get_put_diff.
          1: rewrite_map_get_put_goal; reflexivity.
          invert_NoDup.
          intro contra. rewrite in_map_iff in contra.
          destruct_exists. intuition idtac.
          do_injection. intuition fail. }
      1: invert_NoDup; auto.
    Qed.

    Ltac invert_type_wf :=
      lazymatch goal with
        H: type_wf _ |- _ =>
          inversion H; subst; clear H
      end.

    Lemma lower_mut_res__res_rel : forall x t rls ts v,
        In (lower_mut_res (x, t)) rls ->
        type_of_value v t -> type_wf t ->
        prog_impl_fact rls (ret_rel, [Zobj ts]) ->
        is_lowered_to_at v rls (str_rel x) ts ->
        is_lowered_to v rls (res_rel x).
    Proof.
      unfold is_lowered_to_at, is_lowered_to; intros.
      invert_type_wf; cbn in *;
      invert_type_of_value; cbn in *.
      1-3: constructor;
      invert_Forall;
      econstructor;
      [ rewrite Exists_exists; eexists;
        intuition eauto; econstructor;
        (repeat eexists; repeat econstructor;
         [ lazymatch goal with
             |- _ = Some ?v =>
               instantiate (1:=map.put (map.put map.empty time_var (Zobj ts)) (singleton_var x) v)
           end | .. ];
         repeat rewrite_map_get_put_goal; eauto)
      | constructor; auto ].
      1:{ constructor; auto.
          econstructor.
          1:{ rewrite Exists_exists; eexists;
              intuition eauto. econstructor.
              repeat eexists; repeat econstructor; cbn.
              1:{ lazymatch goal with
                  |- Forall2 _ (map _ ?sl) ?vl =>
                    instantiate (1:=mk_context (map.put map.empty time_var (Zobj ts)) (map attr_var sl) vl)
                end;
                  apply mk_context_rec_sound; auto. }
              1,2: rewrite mk_context_get_put_diff;
              [ rewrite_map_get_put_goal; eauto
              | intro contra;
                rewrite in_map_iff in contra;
                destruct_exists; intuition discriminate ].
              1:{ apply mk_context_rec_sound; auto. } }
          1:{ invert_Forall. repeat constructor; cbn; auto. } }
      1:{ rewrite Forall_forall; intros.
          apply_Forall_In.
          rewrite in_map_iff in *.
          destruct_exists; intuition idtac.
          apply_Forall_In. invert_type_of_value. cbn.
          invert_type_wf.
           econstructor.
          1:{ rewrite Exists_exists; eexists;
              intuition eauto. econstructor.
              repeat eexists; repeat econstructor; cbn.
              1:{ lazymatch goal with
                  |- Forall2 _ (map _ ?sl) ?vl =>
                    instantiate (1:=mk_context (map.put map.empty time_var (Zobj ts)) (map attr_var sl) vl)
                end;
                  apply mk_context_rec_sound; auto. }
              1,2: rewrite mk_context_get_put_diff;
              [ rewrite_map_get_put_goal; eauto
              | intro contra;
                rewrite in_map_iff in contra;
                destruct_exists; intuition discriminate ].
              1:{ apply mk_context_rec_sound; auto. } }
          1:{ repeat constructor; cbn; auto. } }
    Qed.


    Lemma lower_mut_res__venv_is_lowered_to : forall g_sig g_str rls ts,
        incl (map lower_mut_res g_sig) rls ->
        sig_wf g_sig ->
        str_wf (map snd g_sig) g_str ->
        prog_impl_fact rls (ret_rel, [Zobj ts]) ->
        venv_is_lowered_to_at (map fst g_sig) g_str rls ts ->
        venv_is_lowered_to (map fst g_sig) g_str rls.
    Proof.
      induction g_sig; destruct g_str;
        unfold str_wf, venv_is_lowered_to_at; intros; invert_Forall2;
        cbn in *; constructor.
      all: lazymatch goal with
             H: incl (_ :: _) _ |- _ =>
               apply incl_cons_inv in H
           end.
      all: unfold sig_wf in *; intuition idtac.
      1:{ invert_Forall2.
          destruct a; cbn in *.
          invert_Forall.
          eapply lower_mut_res__res_rel; intuition eauto. }
      1:{ eapply IHg_sig; eauto.
          1: cbn in *; invert_NoDup; invert_Forall; intuition assumption.
          1: invert_Forall2; auto. }
    Qed.

    Theorem lower_cfg_complete' : forall (g : cfg) (Gstore : tenv) (g_d' : cfg_dynamic) dcls rls,
        lower_cfg g = (dcls, rls) ->
        Gstore = mk_tenv g.(sig_blks).(sig) ->
        well_typed_cfg g ->
        cfg_steps g.(sig_blks) g.(str_ptr) g_d' ->
        let muts := map fst g.(sig_blks).(sig) in
        match g_d'.(ptr) with
        | Some n =>
            exists ts, venv_is_lowered_to_at muts g_d'.(str) rls ts /\
                         prog_impl_fact rls (blk_rel n, [Zobj ts])
        | None => venv_is_lowered_to muts g_d'.(str) rls
        end.
    Proof.
      unfold well_typed_cfg, lower_cfg; intros.
      intuition idtac.
      lazymatch goal with
        H: context[cfg_steps] |- _ =>
          induction H
      end; intros.
      1:{ repeat destruct_match_hyp; subst;
          invert_pair.
          1:{ exists 0%Z; split.
              1:{ unfold sig_wf in *.
                  apply venv_is_lowered_to_at_0; auto.
                  apply incl_tl, incl_appl, incl_refl. }
              1:{ econstructor.
                  1:{ left. econstructor.
                      repeat eexists; eauto;
                        repeat econstructor. }
                  trivial. } }
          1:{ eapply lower_mut_res__venv_is_lowered_to; eauto.
              3:{ apply venv_is_lowered_to_at_0; auto.



            unfold venv_is_lowered_to.
              unfold str_wf in *.
              remember g_d.(str) as g_str.
              remember g.(sig_blks).(sig) as g_sig.
              generalize dependent g_sig.
              induction g_str; intros;
                destruct g_sig; invert_Forall2; cbn; constructor.
              2:{ eauto.
              rewrite List.Forall2_combine.
              apply lower_mut_res__res_rel.
              unfold lower_mut_res.

            unfold venv_is_lowered_to. admit. } }
      1:{ lazymatch goal with
          H: context[cfg_step] |- _ =>
            inversion H; subst
        end.
          repeat rewrite_asm_hyp.
          eapply cfg_steps__ptr_Some in H7; eauto.
          destruct_exists. rewrite_asm_hyp.
          repeat destruct_match_hyp; subst.
          case_match.
    Admitted.


    Theorem lower_cfg_sound : forall (g : cfg) (Gstore : tenv) (store : venv) dcls rls,
        lower_cfg g = (dcls, rls) ->
        Gstore = mk_tenv g.(sig) ->
        well_typed_cfg g ->
        cfg_impl g store ->
        venv_is_lowered_from Gstore rls store.
    Admitted.
  End WithVarenv.

End __.
Wanted to change the definitions of lower_aexpr and lower_pexpr and lower_rexpr to return via output relation, as their soundness lemmas now involve a separate set of rules from which we can deduce (str_rel x)[t; ...], and it's unclear how to talk about interp_fact and Datalog.interp_expr with respect to some "free relation" that's created in a separate set of rules.

But cannot change because of the way relational algebra constructs are lowered: the assumption of variable names for accessing the attribute of a row only has the scope within a rule, and generating a rule for lower_aexpr / lower_pexpr won't do.


                                                                                                                                                            entry a pointer                                                                                        relate v with sets of tuples
