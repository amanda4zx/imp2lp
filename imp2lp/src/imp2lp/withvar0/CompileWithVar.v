From Stdlib Require Import String ZArith List Bool Permutation.
From coqutil Require Import Map.Interface Decidable Datatypes.Result Datatypes.List Tactics.case_match.
From imp2lp Require Import withvar0.Datalog withvar0.SrcLangWithVar Value MyTactics.
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
      Fixpoint lower_aexpr (e : aexpr) : (dexpr * list fact) :=
        (* Assume no variable shadowing and no reuse of variable names, even across mutable and immutable variables
         m: maps each (row variable, attribute) pair to a datalog variable.
         return (datalog expression, list of clauses assumed for the expression, new threshold for fresh variables *)
        match e with
        (* | AVar x => (var_expr (singleton_var x), []) *)
        | ALoc x => (var_expr (singleton_var x), [ {| fact_R:=str_rel x; fact_args:=[var_expr time_var; var_expr (singleton_var x)] |} ])
        | ABool b => (fun_expr (fnB (fn_BLit b)) [], [])
        | AInt n => (fun_expr (fnZ (fn_ZLit n)) [], [])
        | AString s => (fun_expr (fnS (fn_SLit s)) [], [])
        (* | ALet e1 x e2 => let '(e1', conds1) := lower_aexpr e1 in
                          let '(e2', conds2) := lower_aexpr e2 in
                          (e2', {| fact_R:=true_rel; fact_args:=[fun_expr (fnB fn_Eq) [var_expr (singleton_var x); e1']] |} :: conds1 ++ conds2) *)
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

      Definition get_aexpr_type (g_sig : list (string * type)) (Genv : tenv) (e : aexpr) : type :=
        match e with
        (* | AVar x => match map.get Genv x with
                    | Some t => t
                    | _ => TBool (* unused case *)
                    end *)
        | ALoc x => match access_record g_sig x with
                    | Success t => t
                    | _ => TBool (* unused case *)
                    end
        | ABool _ | ANot _ | AAnd _ _ => TBool
        | AInt _ | APlus _ _ | AStringLength _ => TInt
        | AString _ | AStringConcat _ _ => TString
        (* | ALet e1 x e2 => get_aexpr_type Gstore (map.put Genv x (get_aexpr_type Gstore Genv e1)) e2 *)
        | AAccess x attr => match map.get Genv x with
                            | Some (TRecord tl) => match access_record tl attr with
                                                   | Success t => t
                                                   | _ => TBool (* unused case *)
                                                   end
                            | _ => TBool (* unused cases *)
                            end
        end.

      Definition get_rexpr_type g_sig (Genv : tenv) (r : rexpr) : type :=
        match r with
          RRecord l =>
            TRecord
              (List.map (fun '(attr, a) => (attr, get_aexpr_type g_sig Genv a)) (record_sort l))
        end.

      Fixpoint get_expr_type g_sig (e : expr) : type :=
        match e with
        | EAtom a => get_aexpr_type g_sig map.empty a
        | ELoc x => match access_record g_sig x with
                    | Success t => t
                    | _ => TBool (* unused case *)
                    end
        | EEmptySet tl => TSet (TRecord tl)
        | ESetInsert r e => get_expr_type g_sig e
        | EFilter e x p => get_expr_type g_sig e
        | EJoin e1 e2 x1 x2 p r =>
            match get_expr_type g_sig e1 with
            | TSet t1 =>
                match get_expr_type g_sig e2 with
                | TSet t2 =>
                    TSet (get_rexpr_type g_sig (map.put (map.put map.empty x1 t1) x2 t2) r)
                | _ => TBool
                end
            | _ => TBool
            end
        | EProj e x r =>
            match get_expr_type g_sig e with
            | TSet t =>
                TSet (get_rexpr_type g_sig (map.put map.empty x t) r)
            | _ => TBool
            end
        end.

      Lemma get_aexpr_type_correct : forall g_sig Genv a t,
          type_of_aexpr g_sig Genv a t ->
          get_aexpr_type g_sig Genv a = t.
      Proof.
        induction 1; cbn; repeat rewrite_asm; auto.
      Qed.

      Ltac invert_type_wf :=
        lazymatch goal with
          H: type_wf _ |- _ =>
            inversion H; subst; clear H
        end.

      Ltac invert_SSorted :=
        lazymatch goal with
          H: Sorted.StronglySorted _ (_ :: _) |- _ =>
            inversion H; subst; clear H
        end.

      Lemma get_rexpr_type_correct : forall g_sig Genv e t,
          type_of_rexpr g_sig Genv e t ->
          get_rexpr_type g_sig Genv e = t.
      Proof.
        destruct 1; cbn. f_equal.
        remember (record_sort el) as l. clear Heql.
        induction H1; cbn; auto.
        invert_Forall2. case_match; f_equal.
        1:{ destruct y; f_equal; auto.
            apply get_aexpr_type_correct; auto. }
        1:{ apply IHForall2; auto.
            invert_type_wf; cbn in *;
              invert_NoDup; invert_SSorted; invert_Forall.
            constructor; auto. }
      Qed.

      Lemma get_expr_type_correct : forall g_sig e t,
          type_of_expr g_sig e t ->
          get_expr_type g_sig e = t.
      Proof.
        induction 1; cbn; repeat rewrite_asm;
          auto using get_aexpr_type_correct.
        all: f_equal; auto using get_rexpr_type_correct.
      Qed.

      Definition lower_rexpr g_sig (Genv : tenv) (e : rexpr) : list dexpr * list fact * list (string * dtype) :=
        match e with
          RRecord l =>
            (List.map (fun '(_, a) => fst (lower_aexpr a)) (record_sort l),
              List.concat (List.map (fun '(_, a) => snd (lower_aexpr a)) (record_sort l)),
              List.map (fun '(s, a) => (s, lower_type (get_aexpr_type g_sig Genv a))) (record_sort l))
        end.

      Definition mk_vars (name : string) (tl : list (string * type)) : list var :=
        map (fun '(attr, _) => access_var (name, attr)) tl.

      Definition lower_rec_type : list (string * type) -> list (string * dtype) :=
        List.map (fun '(s, t) => (s, lower_type t)).
    End WithTimestamp.

    Definition dexpr_zero : dexpr := fun_expr (fnZ (fn_ZLit 0)) [].
    Definition dexpr_plus_one (e : dexpr) :=
      fun_expr (fnZ fn_Plus) [e; fun_expr (fnZ (fn_ZLit 1)) []].

    Section WithTimestamp.
      Section WithGsig.
        Context (g_sig : list (string * type)).
        Context (blk_hyps : list fact). (* assumptions created in lower_block *)

        Fixpoint lower_expr (to_next_ts : bool) (out : rel) (next_rel : nat) (e : expr) :
          list decl * list rule * nat * list (string * dtype) :=
          let in_timestamp := var_expr time_var in
          let out_timestamp := if to_next_ts
                               then dexpr_plus_one in_timestamp
                               else in_timestamp in
          match e with
          | EAtom a =>
              let '(a', asms) := lower_aexpr a in
              ([],
                [{| rule_concls := [{| fact_R := out; fact_args := [out_timestamp; a'] |}];
                   rule_hyps := asms ++ blk_hyps;
                   rule_agg := None;
                   rule_set_hyps := [] |}],
                next_rel,
                [(singleton_attr, lower_type (get_aexpr_type g_sig map.empty a))])
          | ELoc x =>
              let tl := match access_record g_sig x with
                        | Success (TSet (TRecord tl))
                        | Success (TRecord tl) => tl
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
              let '(r', asms, _) := lower_rexpr g_sig map.empty r in
              let aux := nat_rel next_rel in
              let '(dcls, rls, next_rel', attr_tys) := lower_expr false aux (S next_rel) s in
              let tl := match get_rexpr_type g_sig map.empty r with
                        | TRecord tl => tl
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
              let tl := match get_expr_type g_sig s with
                        | TSet (TRecord tl) => tl
                        | _ => []
                        end in
              let vars := mk_vars x tl in
              let p_asms := List.map lower_pexpr p in
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
              let tl1 := match get_expr_type g_sig s1 with
                         | TSet (TRecord tl1) => tl1
                         | _ => []
                         end in
              let tl2 := match get_expr_type g_sig s2 with
                         | TSet (TRecord tl2) => tl2
                         | _ => []
                         end in
              let vars1 := mk_vars x1 tl1 in
              let vars2 := mk_vars x2 tl2 in
              let vs1 := List.map var_expr vars1 in
              let vs2 := List.map var_expr vars2 in
              let p_asms := List.map lower_pexpr p in
              let ps' := List.map fst p_asms in
              let asms_p := List.concat (List.map snd p_asms) in
              let Genv := map.put (map.put map.empty x1 (TRecord tl1)) x2 (TRecord tl2) in
              let '(r', asms_r, attr_tys) := lower_rexpr g_sig Genv r in
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
              let tl := match get_expr_type g_sig s with
                        | TSet (TRecord tl) => tl
                        | _ => []
                        end in
              let vars := mk_vars x tl in
              let Genv := map.put map.empty x (TRecord tl) in
              let '(r', asms, out_attr_tys) := lower_rexpr g_sig Genv r in
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
      End WithGsig.
    End WithTimestamp.

    Fixpoint lower_mut_assignments (hyps : list fact) g_sig (next_rel : nat) (asgs : list (string * expr)) :
          list decl * list rule * nat :=
      match asgs with
      | [] => ([], [], next_rel)
      | (x, e) :: asgs =>
          let '(dcls0, rls0, next_rel0, _) :=
            lower_expr g_sig
            hyps (* blk_hyps *)
            true (* increment timestamp *)
            (str_rel x) next_rel e in
          let '(dcls, rls, next_rel') :=
            lower_mut_assignments hyps g_sig next_rel0 asgs in
          (dcls0 ++ dcls, rls0 ++ rls, next_rel')
      end.

    Definition lower_block (g_sig : list (string * type)) (next_rel : nat) (blk : block) (blk_id : nat) :
      list decl * list rule * nat :=
      match blk with
      | BGoto es n =>
          let '(dcls, rls, next_rel') :=
            lower_mut_assignments
              [{| fact_R := blk_rel blk_id; fact_args := [var_expr time_var] |}]
              g_sig next_rel (combine (List.map fst g_sig) es) in
          (dcls,
            rls ++
              [{| rule_concls := [ {| fact_R := blk_rel n; fact_args := [dexpr_plus_one (var_expr time_var)] |} ];
                 rule_hyps := [ {| fact_R := blk_rel blk_id; fact_args := [var_expr time_var]|} ];
                 rule_agg := None;
                 rule_set_hyps := [] |}], next_rel')
      | BIf p es1 n1 es2 n2 =>
          let '(p', asms) := lower_pexpr p in
          let '(dcls1, rls1, next_rel1) :=
            lower_mut_assignments
              ([{| fact_R := blk_rel blk_id; fact_args := [var_expr time_var] |};
                {| fact_R := true_rel; fact_args := [p'] |} ] ++ asms)
              g_sig next_rel (combine (List.map fst g_sig) es1) in
          let neg_p' := fun_expr (fnB fn_Not) [p'] in
          let '(dcls2, rls2, next_rel2) :=
            lower_mut_assignments
              ([{| fact_R := blk_rel blk_id; fact_args := [var_expr time_var] |};
                {| fact_R := true_rel; fact_args := [neg_p'] |} ] ++ asms)
              g_sig next_rel (combine (List.map fst g_sig) es2) in
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
      | _ =>
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
      | VRecord l => map (fun v => lower_atomic_value v) (map snd l)
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

    Definition true_rl : rule :=
      {| rule_concls :=
          [{| fact_R := true_rel; fact_args := [fun_expr (fnB (fn_BLit true)) []] |}];
        rule_hyps := [];
        rule_agg := None;
        rule_set_hyps := [] |}.

    Definition lower_cfg (g : cfg) : list decl * list rule :=
      let g_sig := g.(sig_blks).(sig) in
      let mut_dcls := List.concat (map decl_mut_rels g_sig) in
      let true_dcl := {| decl_R:=true_rel; decl_sig:=[(""%string, DBool)] |} in
      let init_str_rls := List.concat
                            (map (fun '(x, v) => lower_init_value (str_rel x) v)
                               g.(str_ptr).(str)) in
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
      (mut_dcls ++ dcls ++ [ true_dcl ],
        entry_blk_rl ::
          init_str_rls ++ rls ++ res_rls ++ [ true_rl ]).

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

    Definition venv_is_lowered_to_at (str : list (string * value)) (rls : list rule) (ts : Z) : Prop :=
      Forall (fun '(x, v) => is_lowered_to_at v rls (str_rel x) ts) str.

    Definition venv_is_lowered_to (str : list (string * value)) (rls : list rule) : Prop :=
      Forall (fun '(x, v) => is_lowered_to v rls (res_rel x)) str.

    Definition venv_is_lowered_from_at (rls : list rule) (str : list (string * value)) (ts : Z) : Prop :=
      Forall (fun '(x, v) => is_lowered_from_at rls (str_rel x) v ts) str.

    Definition venv_is_lowered_from (rls : list rule) (str : list (string * value)) : Prop :=
      Forall (fun '(x, v) => is_lowered_from rls (res_rel x) v) str.

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
                (fun v => lower_atomic_value v)
                (map snd vl)))
          (map (fun v => lower_atomic_value v)
             (map snd vl)).
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
          invert_cons; eapply IHvl; eauto. }
    Qed.

    (* ===== Compiler completeness proofs ===== *)

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
        str_wf g_sig g_str ->
        incl (concat
                (map (fun '(x, v) => lower_init_value (str_rel x) v) g_str)) rls ->
        venv_is_lowered_to_at g_str rls 0.
    Proof.
      unfold str_wf, sig_wf; intuition idtac. generalize dependent g_str.
      induction g_sig; cbn; intros; destruct g_str; try discriminate;
        constructor; cbn in *;
        intuition idtac; invert_Forall; invert_NoDup;
        invert_cons; invert_Forall2.
      1:{ case_match. unfold is_lowered_to_at.
          rewrite Forall_forall.
          intros; cbn in *.
          lazymatch goal with
            H: type_of_value _ _ |- _ =>
              eapply lower_init_value_complete in H
          end; trivial.
          apply_Forall_In.
          eapply prog_impl_fact_weaken; eauto.
          lazymatch goal with
            H: incl (_ ++ _) _ |- _ => apply incl_app_inv in H
          end. intuition fail. }
      1:{ apply IHg_sig; auto.
          lazymatch goal with
            H: incl (_ ++ _) _ |- _ => apply incl_app_inv in H
          end. intuition fail. }
    Qed.

    Lemma incl_app_bw_l {A} (l l1 l2 : list A) :
      incl (l1 ++ l2) l ->
      incl l1 l.
    Proof. intros H. cbv [incl] in *. intros. apply H. apply in_app_iff. auto. Qed.

    Lemma incl_app_bw_r {A} (l l1 l2 : list A) :
      incl (l1 ++ l2) l ->
      incl l2 l.
    Proof. intros H. cbv [incl] in *. intros. apply H. apply in_app_iff. auto. Qed.

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
        Forall2 (fun tp vp => type_of_value (snd vp) (snd tp)) tl vl ->
        NoDup (map fst tl) ->
        forall m,
        Forall2 (Datalog.interp_expr (mk_context m (map attr_var (map fst tl)) (map (fun v => lower_atomic_value v) (map snd vl))))
          (map (fun x => var_expr (attr_var x)) (map fst tl))
          (map (fun v => lower_atomic_value v) (map snd vl)).
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
                end.
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
        str_wf g_sig g_str ->
        prog_impl_fact rls (ret_rel, [Zobj ts]) ->
        venv_is_lowered_to_at g_str rls ts ->
        venv_is_lowered_to g_str rls.
    Proof.
      induction g_sig; destruct g_str;
        unfold str_wf, venv_is_lowered_to_at; intros;
        intuition idtac; invert_Forall2;
        cbn in *; constructor.
      all: lazymatch goal with
             H: incl (_ :: _) _ |- _ =>
               apply incl_cons_inv in H
           end.
      all: unfold sig_wf in *; intuition idtac.
      1:{ case_match; invert_cons; cbn in *.
          destruct a; cbn in *.
          repeat invert_Forall.
          eapply lower_mut_res__res_rel; intuition eauto. }
      1:{ invert_cons; invert_Forall; eapply IHg_sig; eauto.
          1: cbn in *; invert_NoDup; invert_Forall; intuition assumption.
          1: unfold str_wf; intuition fail. }
    Qed.

    Definition vars_of (x : string) (t : type) :=
      match t with
      | TRecord tl
      | TSet (TRecord tl) =>
          mk_vars x tl
      | _ => [ singleton_var x ]
      end.
(*
    Definition context_wf (ts : Z) (g_sig : list (string * type)) (g_str : list value) (Genv : tenv) (env : venv) (ctx : context) :=
      map.get ctx time_var = Some (Zobj ts) /\
        Forall2 (fun '(x, t) v =>
                   is_atomic_type t -> map.get ctx (singleton_var x) = Some (lower_atomic_value v)) g_sig g_str /\
                   (* Exists (Forall2 (fun x' v' => map.get ctx x' = Some v') (vars_of x t)) (lower_value v)) g_sig g_str /\ *)
        forall x t v, map.get Genv x = Some t ->
                      map.get env x = Some v ->
                      Exists (Forall2 (fun x' v' => map.get ctx x' = Some v') (vars_of x t)) (lower_value v).
 *)

    Definition context_wf (ts : Z) (g_sig : list (string * type)) (g_str : list (string * value)) (Genv : tenv) (env : venv) (ctx : context) :=
      map.get ctx time_var = Some (Zobj ts) /\
        (forall x t v,
            access_record g_sig x = Success t ->
            access_record g_str x = Success v ->
            is_atomic_type t ->
            (* Only atomic mutable variables will appear in block hyps and assumptions from aexpr compilation. Omitting this condition breaks the property as mutable variables whose value equal to the empty set has lower_value returning nil *)
            Exists (Forall2 (fun x' v' => map.get ctx x' = Some v') (vars_of x t)) (lower_value v)) /\
        forall x t v,
          map.get Genv x = Some t ->
          map.get env x = Some v ->
          (* immutable variables only take record values, arising from relational algebra constructs, so the problem with mutable variables as described above do not occur *)
          Exists (Forall2 (fun x' v' => map.get ctx x' = Some v') (vars_of x t)) (lower_value v).

    Ltac invert_type_of_expr :=
      lazymatch goal with
        H: context[type_of_expr] |- _ =>
          inversion H; subst
      end.

    Ltac  invert_type_of_aexpr :=
      lazymatch goal with
        H: context[type_of_aexpr] |- _ =>
          inversion H; subst
      end.

    Lemma Forall2_In_l : forall A B (P : A -> B -> Prop) l l' x,
        Forall2 P l l' -> In x l ->
        exists x', In x' l' /\ P x x'.
    Proof.
      induction 1; cbn; intuition idtac; subst.
      1: eexists; eauto.
      destruct_exists.
      exists x1; intuition fail.
    Qed.

    Lemma Forall2_and A B R1 R2 (xs : list A) (ys : list B) :
      Forall2 R1 xs ys ->
      Forall2 R2 xs ys ->
      Forall2 (fun x y => R1 x y /\ R2 x y) xs ys.
    Proof.
      induction 1; intros; invert_Forall2; eauto.
    Qed.


    Ltac apply_Forall2_and :=
      lazymatch goal with
        H: Forall2 _ ?l1 ?l2, H': Forall2 _ ?l1 ?l2 |- _ =>
          pose proof (Forall2_and _ _ _ _ H H');
          clear H H'
      end.

    Ltac invert_is_atomic_type :=
      lazymatch goal with
        H: context[is_atomic_type] |- _ =>
          inversion H; clear H
      end.

    Ltac invert_Datalog_interp_expr :=
      lazymatch goal with
        H: Datalog.interp_expr _ _ _ |- _ =>
          inversion H; subst; clear H
      end.

    Lemma access_record_Forall : forall A (P : string -> A -> Prop) l x y,
        Forall (fun '(x, y) => P x y) l ->
        access_record l x = Success y ->
        P x y.
    Proof.
      induction 1; cbn; try discriminate.
      repeat case_match; auto.
      injection 1. rewrite String.eqb_eq in *.
      congruence.
    Qed.

    Lemma lower_value_atomic : forall v t,
        type_of_value v t ->
        is_atomic_type t ->
        lower_value v = [[ lower_atomic_value v ]].
    Proof.
      inversion 1; intuition idtac;
        lazymatch goal with
          H: is_atomic_type _ |- _ =>
            inversion H
        end.
    Qed.

    Lemma vars_of_atomic : forall x t,
        is_atomic_type t ->
        vars_of x t = [ singleton_var x ].
    Proof.
      destruct t; intuition idtac;
        lazymatch goal with
          H: is_atomic_type _ |- _ =>
            inversion H
        end.
    Qed.

    Ltac invert_interp_fact :=
      lazymatch goal with
        H: interp_fact _ _ _ |- _ =>
          inversion H; subst
      end.

    Ltac apply_Forall2_access_record :=
      lazymatch goal with
      | _: Forall2 _ ?g_sig _, H: access_record ?g_sig _ = Success ?t
        |- _ =>
          let H_v := fresh "H_v" in
          eapply Forall2_access_record in H as H_v
      end.

    Ltac apply_access_record_Forall :=
      lazymatch goal with
        H: Forall _ ?l, _: access_record ?l _ = _ |- _ =>
          eapply access_record_Forall in H
      end.

    Ltac invert_Exists :=
      lazymatch goal with
        H: Exists _ _ |- _ =>
          inversion H; subst; clear H
      end.

    Lemma lower_aexpr_asms_hold : forall a a' asms Genv env t g_sig g_str ts ctx rls,
        lower_aexpr a = (a', asms) ->
        type_of_aexpr g_sig Genv a t ->
        context_wf ts g_sig g_str Genv env ctx ->
        venv_is_lowered_to_at g_str rls ts ->
        str_wf g_sig g_str ->
        Forall (fun asm => exists asm', interp_fact ctx asm asm' /\ prog_impl_fact rls asm') asms.
    Proof.
      induction a; cbn; intros;
        try invert_pair; repeat constructor.
      1:{ intros.
          unfold venv_is_lowered_to_at, str_wf, context_wf in *.
          intuition idtac.
          invert_type_of_aexpr.
          repeat constructor; cbn; eauto.

          apply_Forall2_access_record; eauto.
          destruct_match_hyp; intuition idtac.
          lazymatch goal with
            H: context[is_atomic_type _ -> _], H': is_atomic_type _ |- _ =>
              eapply H in H' as H_ctx
          end; eauto; intuition idtac.
          erewrite lower_value_atomic in *; eauto.
          erewrite vars_of_atomic in *; eauto.
          repeat invert_Exists. repeat invert_Forall2.
          eexists; split.
          1: repeat constructor; cbn; eauto.
          cbn.
          apply_access_record_Forall; eauto.
          unfold is_lowered_to_at in *.
          erewrite lower_value_atomic in *; eauto.
          invert_Forall. assumption. }
      all: repeat destruct_match_hyp; invert_pair;
        invert_type_of_aexpr; repeat rewrite Forall_app;
        intuition idtac; eauto.
    Qed.

    Lemma Forall2_access_record_same : forall A B P l l' x (v : A) (v' : B),
        Forall2 P l l' ->
        map fst l = map fst l' ->
        access_record l x = Success v ->
        access_record l' x = Success v' ->
        P (x, v) (x, v').
    Proof.
      induction 1; cbn; try discriminate.
      do 3 case_match; cbn;
      intros; invert_cons;
      rewrite ?String.eqb_eq in *;
      repeat (do_injection; clear_refl).
      1: rewrite String.eqb_refl in *; congruence.
      1: rewrite_l_to_r; auto.
    Qed.

    Ltac apply_aexpr_type_sound :=
      lazymatch goal with
        H: type_of_aexpr _ _ _ _ |- _ =>
          eapply aexpr_type_sound in H
      end.

    Ltac rewrite_interp_aexpr :=
      lazymatch goal with
      | H: _ = interp_aexpr _ _ ?a |- context[interp_aexpr _ _ ?a] =>
          rewrite <- H in *
      | H: _ = interp_aexpr _ _ ?a, _: context[interp_aexpr _ _ ?a] |- _ =>
          rewrite <- H in *
      end.

    Ltac apply_lower_aexpr_complete_IH :=
      lazymatch goal with
        IH: context[tenv_wf _ -> _], H: tenv_wf _ |- _ =>
          let IH' := fresh "IH'" in
          eapply IH in H as IH'; clear IH
      end.

    Lemma Forall2_map_l {A B C} R (f : A -> B) (l1 : list A) (l2 : list C) :
      Forall2 (fun x => R (f x)) l1 l2 <->
        Forall2 R (map f l1) l2.
    Proof.
      split; intros H.
      - induction H. 1: constructor. constructor; assumption.
      - remember (map f l1) as l1' eqn:E. revert l1 E. induction H; intros l1 Hl1.
        + destruct l1; inversion Hl1. constructor.
        + destruct l1; inversion Hl1. subst. constructor; auto.
    Qed.

    Lemma Forall2_flip_iff {A B} R (l1 : list A) (l2 : list B) :
      Forall2 (fun x y => R y x) l2 l1 <->
        Forall2 R l1 l2.
    Proof.
      split; auto using Forall2_flip.
    Qed.

    Lemma Forall2_map_r {A B C} R (f : B -> C) (l1 : list A) (l2 : list B) :
      Forall2 (fun x y => R x (f y)) l1 l2 <->
        Forall2 R l1 (map f l2).
    Proof.
      symmetry. rewrite <- Forall2_flip_iff, <- Forall2_map_l, <- Forall2_flip_iff.
      reflexivity.
    Qed.

    Lemma lower_aexpr_complete : forall ts g_sig g_str Genv env a t ctx a' asms,
        lower_aexpr a = (a', asms) ->
        type_of_aexpr g_sig Genv a t ->
        context_wf ts g_sig g_str Genv env ctx ->
        str_wf g_sig g_str ->
        venv_wf Genv env ->
        sig_wf g_sig -> tenv_wf Genv ->
        Datalog.interp_expr ctx a' (lower_atomic_value (interp_aexpr g_str env a)).
    Proof.
      induction a; cbn; intros;
        unfold str_wf, context_wf in *;
        intuition idtac; invert_type_of_aexpr.
      1:{ invert_pair.
          apply_Forall2_access_record; eauto.
          destruct_match_hyp; intuition idtac.
          lazymatch goal with
            H: context[is_atomic_type _ -> _], H': is_atomic_type _ |- _ =>
              eapply H in H' as H_ctx
          end; eauto.
          erewrite lower_value_atomic in *; eauto.
          erewrite vars_of_atomic in *; eauto.
          repeat invert_Exists. invert_Forall2.
          constructor; assumption. }
      1-3: invert_pair; econstructor; eauto.
      all: try (repeat destruct_match_hyp;
                repeat (apply_lower_aexpr_complete_IH; eauto);
                invert_pair;
                repeat (apply_aexpr_type_sound; unfold str_wf; eauto);
                repeat invert_type_of_value; cbn;
                econstructor; eauto; cbn;
                repeat rewrite_interp_aexpr; cbn; congruence).
      1:{ invert_pair.
          lazymatch goal with
            H: venv_wf ?G _, H': map.get ?G _ = _ |- _ =>
              apply H in H' as H_env
          end.
          destruct_match_hyp; intuition idtac.
          invert_type_of_value.
          eapply H9 in E; eauto. cbn in *.
          repeat invert_Exists.
          apply_Forall2_access_record; eauto.
          destruct_match_hyp; intuition idtac.
          unfold mk_vars in *.
          rewrite <- Forall2_map_l, <- !Forall2_map_r in *.
          eapply Forall2_access_record_same in H10; eauto.
          constructor; assumption. }
    Qed.

    Lemma type_of_aexpr_is_atomic_type : forall g_sig Genv a t,
        type_of_aexpr g_sig Genv a t ->
        is_atomic_type t.
    Proof.
      inversion 1; subst; try constructor; auto.
    Qed.

    Fixpoint mk_atomic_wf_context (m : context) (ts : Z) (g_sig : list (string * type)) (g_str : list (string * value)) : context :=
      match g_sig, g_str with
      | [], _ | _, [] => map.put m time_var (Zobj ts)
      | (x, t) :: g_sig, (_, v) :: g_str =>
          if is_atomic_type_com t
          then map.put (mk_atomic_wf_context m ts g_sig g_str) (singleton_var x) (lower_atomic_value v)
          else mk_atomic_wf_context m ts g_sig g_str
      end.

    Lemma get_atomic_wf_context_time_var : forall m ts g_sig g_str,
        str_wf g_sig g_str ->
        map.get (mk_atomic_wf_context m ts g_sig g_str) time_var = Some (Zobj ts).
    Proof.
      unfold str_wf; induction g_sig; cbn;
        intuition idtac; invert_Forall2.
      1: rewrite_map_get_put_goal; reflexivity.
      repeat case_match.
      1: rewrite_map_get_put_goal.
      all: apply IHg_sig; cbn in *; invert_cons;
        intuition fail.
    Qed.

    Lemma put_mk_vars_get_time_var : forall tl vl m x,
        map.get (mk_context m (mk_vars x tl) vl) time_var = map.get m time_var.
    Proof.
      unfold mk_vars. induction tl; cbn; auto.
      intros; case_match; auto.
      erewrite IHtl. case_match.
      rewrite_map_get_put_goal.
    Qed.

    Lemma is_atomic_type_com_false_iff : forall t,
        is_atomic_type_com t = false <-> ~is_atomic_type t.
    Proof.
      destruct t; cbn; intuition idtac; discriminate.
    Qed.

    Lemma mk_atomic_wf_context_wf : forall ts g_sig g_str m,
        str_wf g_sig g_str ->
        sig_wf g_sig ->
        context_wf ts g_sig g_str map.empty map.empty (mk_atomic_wf_context m ts g_sig g_str).
    Proof.
      unfold sig_wf, str_wf; induction g_sig; cbn;
        intuition idtac; invert_Forall2.
      1:{ unfold context_wf; intuition idtac.
          1: rewrite_map_get_put_goal; reflexivity.
          1: discriminate.
          1: rewrite map.get_empty in *; discriminate. }
      cbn in *; invert_cons.
      repeat case_match.
      1:{ invert_NoDup. invert_Forall.
          pose proof (IHg_sig _ m (conj H4 H7) (conj H8 H10)).
          cbn in *.
          unfold context_wf in *; intuition idtac.
          1:{ rewrite_map_get_put_goal; auto. }
          1:{ cbn in *; destruct_match_hyp.
              1:{ rewrite String.eqb_eq in *; subst.
                  repeat (do_injection; clear_refl).
                  erewrite vars_of_atomic, lower_value_atomic; eauto.
                  repeat constructor.
                  rewrite_map_get_put_goal; reflexivity. }
              eapply H0 in H13 as H'; eauto.
              erewrite vars_of_atomic, lower_value_atomic in *; eauto.
              2,3: eapply Forall2_access_record in H3; eauto;
              destruct_match_hyp; intuition idtac;
              congruence.
              repeat invert_Exists. repeat invert_Forall2.
              repeat constructor. rewrite_map_get_put_goal.
              intro contra. do_injection.
              rewrite String.eqb_refl in *; discriminate. }
          1:{ rewrite map.get_empty in *. discriminate. } }
      1:{ invert_NoDup. invert_Forall.
          pose proof (IHg_sig _ m (conj H4 H7) (conj H8 H10)).
          cbn in *.
          unfold context_wf in *.
          intuition idtac; auto.
          cbn in *. destruct_match_hyp.
          1:{ rewrite String.eqb_eq in *; subst.
              repeat (do_injection; clear_refl).
              rewrite is_atomic_type_com_false_iff in *.
              intuition fail. }
          apply H0; auto. }
    Qed.

    Lemma String_eqb_compare : forall s1 s2,
        String.eqb s1 s2 =
          match String.compare s1 s2 with
          | Eq => true
          | _ => false
          end.
    Proof.
      intros.
      case_match.
      1: apply compare_eq_iff in case_match_eqn; subst; apply String.eqb_refl.
      all: rewrite eqb_neq in *; intro contra; subst;
        rewrite string_compare_refl in *; discriminate.
    Qed.

    Lemma obj_eqb_iff_value_eqb : forall v1 v2 t,
        type_of_value v1 t -> type_of_value v2 t ->
        is_atomic_type t ->
        obj_eqb (lower_atomic_value v1) (lower_atomic_value v2) = value_eqb v1 v2.
    Proof.
      destruct t; cbn; intuition idtac;
        repeat invert_type_of_value; unfold value_eqb; cbn.
      1: apply Z.eqb_compare.
      1: destruct b0, b; auto.
      1: apply String_eqb_compare.
    Qed.

    Ltac invert_well_typed_pexpr :=
      lazymatch goal with
        H: context[well_typed_pexpr] |- _ =>
          inversion H; subst
      end.

    Lemma lower_pexpr_asms_hold : forall e e' asms Genv env g_sig g_str ts ctx rls,
        lower_pexpr e = (e', asms) ->
        well_typed_pexpr g_sig Genv e ->
        context_wf ts g_sig g_str Genv env ctx ->
        venv_is_lowered_to_at g_str rls ts ->
        str_wf g_sig g_str ->
        Forall (fun asm => exists asm', interp_fact ctx asm asm' /\ prog_impl_fact rls asm') asms.
    Proof.
      destruct e; cbn; intros; repeat destruct_match_hyp;
        invert_well_typed_pexpr; invert_pair;
        apply Forall_app; intuition idtac;
        eapply lower_aexpr_asms_hold; eauto.
    Qed.

    Lemma lower_pexpr_complete : forall ts g_sig g_str Genv env e ctx e' asms,
        lower_pexpr e = (e', asms) ->
        well_typed_pexpr g_sig Genv e ->
        context_wf ts g_sig g_str Genv env ctx ->
        str_wf g_sig g_str ->
        venv_wf Genv env ->
        sig_wf g_sig -> tenv_wf Genv ->
        Datalog.interp_expr ctx e' (lower_atomic_value (VBool (interp_pexpr g_str env e))).
    Proof.
      destruct e; cbn; intros; repeat destruct_match_hyp.
      1:{ invert_well_typed_pexpr.
          repeat (lazymatch goal with
                    H: lower_aexpr _ = _ |- _ =>
                      eapply lower_aexpr_complete in H
                  end; eauto).
          repeat (apply_aexpr_type_sound; eauto).
          repeat invert_type_of_value.
          repeat rewrite_interp_aexpr; cbn in *.
          invert_pair. repeat econstructor; eauto. }
      1:{ invert_well_typed_pexpr.
          repeat (lazymatch goal with
                    H: lower_aexpr _ = _ |- _ =>
                      eapply lower_aexpr_complete in H
                  end; eauto).
          lazymatch goal with
            H: context[type_of_aexpr] |- _ =>
              eapply type_of_aexpr_is_atomic_type in H as H_atomic
          end.
          repeat (apply_aexpr_type_sound; eauto).
          invert_pair. repeat econstructor; eauto; cbn.
          repeat f_equal. eapply obj_eqb_iff_value_eqb; eauto. }
    Qed.

    Lemma lower_rexpr_asms_hold : forall g_sig Genv r r' asms tl' t ts g_str env ctx rls,
      lower_rexpr g_sig Genv r = (r', asms, tl') ->
      type_of_rexpr g_sig Genv r t ->
      context_wf ts g_sig g_str Genv env ctx ->
      venv_is_lowered_to_at g_str rls ts ->
      str_wf g_sig g_str ->
      Forall
        (fun asm : fact =>
           exists asm' : rel * list obj,
             interp_fact ctx asm asm' /\ prog_impl_fact rls asm')
        asms.
    Proof.
      inversion 2; subst; cbn in *.
      invert_pair. remember (record_sort el) as l.
      lazymatch goal with
        H1: context[type_of_rexpr], H2: l = _ |- _ =>
          clear H1 H2
      end.
      invert_type_wf. rewrite Forall_concat.
      induction H2; cbn in *; auto; intros.
      invert_Forall2; invert_Forall; invert_NoDup; invert_SSorted.
      case_match. constructor; auto.
      eapply lower_aexpr_asms_hold; eauto.
      apply surjective_pairing.
    Qed.

    Lemma lower_rexpr_complete : forall g_sig Genv r r' asms tl' t ts g_str env ctx rls,
        lower_rexpr g_sig Genv r = (r', asms, tl') ->
        type_of_rexpr g_sig Genv r t ->
        context_wf ts g_sig g_str Genv env ctx ->
        venv_is_lowered_to_at g_str rls ts ->
        str_wf g_sig g_str ->
        venv_wf Genv env ->
        sig_wf g_sig ->
        tenv_wf Genv ->
        Forall2 (Datalog.interp_expr ctx) r' (map lower_atomic_value (map snd (interp_rexpr g_str env r))).
    Proof.
      inversion 2; subst; cbn in *.
      invert_pair. remember (record_sort el) as l.
      lazymatch goal with
        H1: context[type_of_rexpr], H2: l = _ |- _ =>
          clear H1 H2
      end.
      invert_type_wf.
      induction H2; cbn in *; auto; intros.
      invert_Forall2; invert_Forall; invert_NoDup; invert_SSorted.
      case_match; cbn. constructor; auto.
      eapply lower_aexpr_complete; eauto.
      apply surjective_pairing.
    Qed.

    Lemma construct_hyps_interp : forall (ctx : context) P hyps,
        Forall (fun hyp => exists hyp', interp_fact (rel:=rel) ctx hyp hyp' /\ P hyp') hyps ->
        exists hyps', Forall2 (interp_fact ctx) hyps hyps' /\ Forall P hyps'.
    Proof.
      induction 1; cbn.
      1:{ exists []; intuition idtac; constructor. }
      1:{ repeat destruct_exists. eexists.
          intuition idtac; econstructor; eauto. }
    Qed.

    Lemma length_eq_Forall2_combine : forall A B l1 l2 (P : A -> B -> Prop),
        length l1 = length l2 ->
        Forall2 P l1 l2 <->
          Forall (fun '(x1, x2) => P x1 x2) (combine l1 l2).
    Proof.
      split.
      1: induction 1; cbn; auto.
      1:{ generalize dependent l2.
          induction l1; destruct l2; try discriminate;
            constructor; cbn in *; invert_Forall; auto. }
    Qed.

    Lemma in_map_inj : forall A B x (f : A -> B) l,
        (forall x y, f x = f y -> x = y) ->
        In (f x) (map f l) -> In x l.
    Proof.
      induction l; cbn; auto; intros.
      intuition idtac.
      left. auto.
    Qed.

    Lemma In_get_mk_context_attr_var : forall A x (v : A) vl m g,
        In (x, v) vl ->
        NoDup (map fst vl) ->
        map.get (mk_context m (map attr_var (map fst vl)) (map g (map snd vl))) (attr_var x) = Some (g v).
    Proof.
      induction vl; intros.
      1: apply_in_nil; intuition fail.
      1:{ cbn in *; invert_NoDup; intuition auto.
          destruct a; invert_pair; cbn in *.
          rewrite mk_context_get_put_diff.
          2:{ intro contra; apply in_map_inj in contra; auto.
              intros. do_injection; reflexivity. }
          rewrite_map_get_put_goal; reflexivity. }
    Qed.

    Ltac assert_exists_hyps' ctx rls hyps :=
      assert(exists hyps', Forall2 (interp_fact ctx) hyps hyps' /\ Forall (prog_impl_fact rls) hyps').

    Ltac prove_exists_hyps' :=
      apply construct_hyps_interp;
      lazymatch goal with
        H: context[context_wf] |- _ =>
          apply H
      end; subst;
      apply mk_atomic_wf_context_wf; auto.

    Lemma combine_map_fst_map_snd : forall A B (l : list (A * B)),
        combine (map fst l) (map snd l) = l.
    Proof.
      induction l; cbn; auto.
      f_equal; auto.
      destruct a; trivial.
    Qed.

    Lemma get_atomic_wf_context_attr_var : forall m x ts g_sig g_str,
        map.get (mk_atomic_wf_context m ts g_sig g_str) (attr_var x) = map.get m (attr_var x).
    Proof.
      induction g_sig; cbn; intros.
      1:{ rewrite_map_get_put_goal. }
      1:{ repeat case_match; eauto; rewrite_map_get_put_goal. }
    Qed.

    Lemma Permutation_incl {A} (l l' : list A) :
      Permutation l l' ->
      incl l l'.
    Proof. cbv [incl]. eauto using Permutation_in. Qed.

    Lemma set_insert_incl2 : forall v l,
        incl (set_insert v l) (v :: l).
    Proof.
      induction l; cbn; auto using incl_refl.
      repeat case_match; auto using incl_refl, incl_tl.
      apply incl_cons.
      1: apply in_cons; left; reflexivity.
      eapply incl_tran; eauto.
      eapply incl_tran.
      1: eapply incl_tl.
      2: apply Permutation_incl, perm_swap.
      apply incl_refl.
    Qed.

    Ltac apply_type_sound :=
      lazymatch goal with
        H: type_of_expr _ _ _ |- _ =>
          let H_v := fresh "H_v" in
          eapply type_sound in H as H_v
      end.

    Ltac prove_interp_expr_attr_vars :=
      subst; rewrite_asm;
      rewrite <- Forall2_map_l, <- Forall2_map_r;
      erewrite length_eq_Forall2_combine;
      [ | rewrite !length_map; reflexivity ];
      rewrite combine_map_fst_map_snd;
      rewrite Forall_forall; intros;
      case_match; constructor;
      rewrite get_atomic_wf_context_attr_var;
      apply In_get_mk_context_attr_var; auto;
      lazymatch goal with
        H: context[type_of_expr] |- _ =>
          apply type_of_expr__type_wf in H
      end; auto;
      repeat invert_type_wf; rewrite_l_to_r; assumption.

    Ltac apply_incl :=
      lazymatch goal with
        H: incl _ _ |- _ =>
          apply H
      end.

    Lemma atomic_wf_context_step : forall x tl vl m ts g_sig g_str,
        context_wf ts g_sig g_str map.empty map.empty m ->
          context_wf ts g_sig g_str map.empty map.empty (mk_context m (mk_vars x tl) vl).
    Proof.
      induction tl; cbn; auto; intros.
      case_match; auto. case_match.
      apply IHtl. unfold context_wf in *; intuition idtac.
      1: rewrite_map_get_put_goal.
      1:{ eapply H in H4 as H'; eauto.
          rewrite Exists_exists in *.
          destruct_exists.
          eexists; intuition eauto.
          rewrite vars_of_atomic in *; auto.
          repeat invert_Forall2. repeat constructor.
          rewrite_map_get_put_goal. }
      1:{ rewrite map.get_empty in *; discriminate. }
    Qed.

    Lemma neq_vars_mk_vars_disjoint : forall x1 x2 z tl1 tl2,
        ~x1 = x2 -> In z (mk_vars x1 tl1) -> ~In z (mk_vars x2 tl2).
    Proof.
      induction tl1; cbn; auto; intros.
      destruct_match_hyp; intuition subst.
      2: eapply IHtl1; eauto.
      induction tl2; auto.
      cbn in *; destruct_match_hyp; intuition subst.
      do_injection. congruence.
    Qed.

    Lemma neq_vars_not_In : forall x1 x2 z t tl2,
        ~x1 = x2 -> In z (vars_of x1 t) -> ~In z (mk_vars x2 tl2).
    Proof.
      destruct t; cbn; intuition subst.
      all: try (induction tl2; cbn in *; auto;
                destruct_match_hyp; intuition discriminate).
      1: eapply neq_vars_mk_vars_disjoint; eauto.
      1:{ destruct_match_hyp.
          all: try (destruct_In; induction tl2; cbn in *; auto;
                    destruct_match_hyp; intuition discriminate).
          eapply neq_vars_mk_vars_disjoint; eauto. }
    Qed.

    Lemma In_access_var_mk_vars_In_map_fst : forall x s tl,
        In (access_var (x, s)) (mk_vars x tl) -> In s (map fst tl).
    Proof.
      induction tl; cbn; auto.
      case_match; intuition cbn.
      do_injection. left; trivial.
    Qed.

    Lemma get_mk_context_access_rec : forall vl tl,
        type_of_value (VRecord vl) (TRecord tl) ->
        type_wf (TRecord tl) ->
        forall m x,
          Forall2 (fun x' v' =>
                     map.get
                       (mk_context m (mk_vars x tl)
                          (map lower_atomic_value (map snd vl)))
                       x' =
                       Some v')
            (mk_vars x tl)
            (map lower_atomic_value (map snd vl)).
    Proof.
      inversion 1; subst; unfold mk_vars; intro; invert_type_wf.
      induction H3; auto; cbn; constructor; case_match; cbn in *;
        invert_NoDup; invert_SSorted; invert_Forall; invert_cons.
      1:{ rewrite mk_context_get_put_diff.
          2: intro contra; apply In_access_var_mk_vars_In_map_fst in contra; auto.
              rewrite_map_get_put_goal. reflexivity. }
      1:{ apply IHForall2; auto; constructor; auto. }
    Qed.

    Lemma context_wf_step : forall m ts g_sig g_str Genv env,
        context_wf ts g_sig g_str Genv env m ->
        venv_wf Genv env ->
        forall x tl vl,
          type_wf (TRecord tl) ->
          type_of_value (VRecord vl) (TRecord tl) ->
          context_wf ts g_sig g_str (map.put Genv x (TRecord tl)) (map.put env x (VRecord vl)) (mk_context m (mk_vars x tl) (map lower_atomic_value (map snd vl))).
    Proof.
      unfold context_wf; intuition idtac.
      1: rewrite put_mk_vars_get_time_var; assumption.
      1:{ lazymatch goal with
          H: context[is_atomic_type _ -> _],
            H': is_atomic_type _ |- _ =>
            eapply H in H' as H_new
        end; eauto.
          rewrite vars_of_atomic in *; auto.
          rewrite Exists_exists in *. destruct_exists.
          eexists; intuition eauto.
          repeat invert_Forall2. repeat constructor.
          rewrite mk_context_get_put_diff; auto.
          lazymatch goal with
            H1: context[type_of_value], H2: type_wf _ |- _ =>
              clear H1 H2
          end.
          induction tl; cbn; auto.
          case_match. intuition discriminate. }
      1:{ destruct_String_eqb x x0;
          repeat rewrite_map_get_put_hyp.
          2:{ eapply H3 in H6; eauto.
              rewrite Exists_exists in *.
              destruct_exists. eexists; intuition eauto.
              eapply List.Forall2_impl_strong; eauto; cbn; intros.
              rewrite mk_context_get_put_diff; auto.
              1:{ repeat (do_injection; clear_refl).
                  invert_type_of_value.
                  eauto using neq_vars_not_In; eauto. } }
          repeat (do_injection; clear_refl).
          cbn; rewrite Exists_exists. eexists; split.
          1: left; reflexivity.
          apply get_mk_context_access_rec; auto. }
    Qed.

    Lemma interp_expr_mk_context_mk_vars : forall tl (vl : list (string * value)),
        Forall2 (fun tp vp => type_of_value (snd vp) (snd tp)) tl vl ->
        NoDup (map fst tl) ->
        forall m x,
        Forall2 (Datalog.interp_expr (mk_context m (mk_vars x tl) (map lower_atomic_value (map snd vl)))) (map var_expr (mk_vars x tl)) (map lower_atomic_value (map snd vl)).
    Proof.
      induction 1; cbn; auto; intros; invert_NoDup.
      constructor.
      1:{ econstructor. rewrite mk_context_get_put_diff.
          1: rewrite_map_get_put_goal; reflexivity.
          case_match. cbn in *.
          intro contra. rewrite in_map_iff in contra.
          destruct_exists; destruct_match_hyp; intuition idtac.
          do_injection.
          lazymatch goal with
            H: In (_, _) _ |- _ =>
              apply in_map with (f:=fst) in H
          end. cbn in *; congruence. }
      1:{ apply IHForall2; auto. }
      Qed.

    Lemma lower_pexprs_true : forall ctx (rln : rel) ps,
        Forall (fun p =>
                  Datalog.interp_expr ctx p (Bobj true)) (map fst (map lower_pexpr ps)) ->
        Forall2 (interp_fact ctx)
          (map
             (fun p' =>
                {| fact_R := rln; fact_args := [p'] |})
             (map fst (map lower_pexpr ps)))
          (map (fun _ => (rln, [Bobj true])) ps).
    Proof.
      induction ps; cbn; auto; intros; constructor; invert_Forall; auto.
      econstructor; cbn; auto.
    Qed.

    Lemma pexpr_forallb_true : forall ctx ts g_sig g_str Genv env ps,
        forallb
          (fun p : pexpr =>
             interp_pexpr g_str env p)
          ps = true ->
        Forall
          (well_typed_pexpr g_sig Genv)
          ps ->
        context_wf ts g_sig g_str Genv env ctx ->
        str_wf g_sig g_str ->
        venv_wf Genv env ->
        sig_wf g_sig ->
        tenv_wf Genv ->
        Forall
          (fun p => Datalog.interp_expr ctx p (Bobj true))
          (map fst (map lower_pexpr ps)).
    Proof.
      induction ps; cbn; auto; intros; constructor; invert_Forall;
      rewrite andb_true_iff in *; intuition idtac.
      destruct (lower_pexpr a) eqn:E. cbn.
      assert (HE : Bobj true = (lower_atomic_value (VBool (interp_pexpr g_str env a)))).
      { rewrite_asm; reflexivity. }
      rewrite HE; eapply lower_pexpr_complete; eauto.
    Qed.

    Lemma construct_concat_hyps_interp : forall P (ctx : context) hypss,
        Forall (fun hyps =>
                  exists hyps',
                    Forall2 (interp_fact ctx) hyps hyps' /\ Forall P hyps') hypss ->
        exists hyps' : list (rel * list obj),
          Forall2 (interp_fact ctx) (concat hypss) hyps' /\ Forall P hyps'.
    Proof.
      induction hypss; cbn; intros.
      1: eexists; eauto.
      invert_Forall.
      apply IHhypss in H3. repeat destruct_exists.
      eexists. intuition idtac; eauto using Forall2_app.
      apply Forall_app; intuition fail.
    Qed.

    Lemma interp_expr_mk_context_diff : forall m xl xl' vl vl',
        Forall2 (Datalog.interp_expr m) (map var_expr xl') vl' ->
        Forall (fun x => ~In x xl) xl' ->
        Forall2 (Datalog.interp_expr (mk_context m xl vl)) (map var_expr xl') vl'.
    Proof.
      induction xl'; cbn; intros; invert_Forall2; auto.
      constructor; invert_Forall; auto.
      econstructor. rewrite mk_context_get_put_diff; auto.
      invert_Datalog_interp_expr; assumption.
    Qed.

    Lemma lower_expr_complete : forall e hyps b out next_rel e_dcls e_rls rls next_rel' tl t g_sig g_str ts,
        lower_expr g_sig hyps b out next_rel e = (e_dcls, e_rls, next_rel', tl) ->
        In true_rl rls ->
        type_of_expr g_sig e t ->
        str_wf g_sig g_str ->
        sig_wf g_sig ->
        incl e_rls rls ->
        (forall ctx,
            context_wf ts g_sig g_str map.empty map.empty ctx ->
            Forall (fun hyp => exists hyp', interp_fact ctx hyp hyp' /\ prog_impl_fact rls hyp') hyps) ->
        venv_is_lowered_to_at g_str rls ts ->
        is_lowered_to_at (interp_expr g_str e) rls out (ts + if b then 1 else 0).
    Proof.
      induction e; cbn; intros;
        repeat (destruct_match_hyp; []); invert_pair.
      all: invert_type_of_expr; unfold is_lowered_to_at; auto.
      (* EAtom *)
      1:{ erewrite lower_value_atomic;
          eauto using aexpr_type_sound, tenv_wf_empty, venv_wf_empty, type_of_aexpr_is_atomic_type.
          repeat constructor.
          remember (mk_atomic_wf_context map.empty ts g_sig g_str) as ctx.
          assert_exists_hyps' ctx rls hyps.
          { prove_exists_hyps'. }
          assert_exists_hyps' ctx rls l.
          { apply construct_hyps_interp.
            eapply lower_aexpr_asms_hold; eauto.
            subst. apply mk_atomic_wf_context_wf; auto. }
          repeat destruct_exists.
          econstructor.
          1:{ rewrite Exists_exists.
              eexists; intuition idtac.
              1:{ rewrite incl_Forall_in_iff in *.
                  invert_Forall. eassumption. }
              econstructor. repeat eexists; cbn; repeat econstructor.
              1:{ instantiate (1:=ctx); subst.
                  case_match.
                  1:{ unfold dexpr_plus_one.
                      repeat econstructor; cbn.
                      1: apply get_atomic_wf_context_time_var.
                      all: auto. }
                  constructor.
                  rewrite Z.add_0_r; auto using get_atomic_wf_context_time_var. }
              1: eapply lower_aexpr_complete; eauto using tenv_wf_empty, venv_wf_empty.
              1: instantiate(1:=ts); subst;
              apply mk_atomic_wf_context_wf; auto.
              apply Forall2_app; subst; eauto. }
          1:{ rewrite app_nil_r. apply Forall_app.
              intuition idtac. } }
      (* ELoc *)
      1:{ unfold str_wf in *;
          intuition idtac.
          apply_Forall2_access_record; eauto.
          destruct_match_hyp; intuition idtac.
          unfold venv_is_lowered_to_at in *.
          apply_access_record_Forall; eauto.
          invert_type_of_value.
          unfold is_lowered_to_at in *.
          rewrite Forall_forall; intros.
          apply_Forall_In. cbn in *.
          rewrite in_map_iff in *.
          destruct_exists; intuition idtac.
          apply_Forall_In.
          invert_type_of_value. cbn in *.
          remember (map attr_var (map fst t0)) as xl.
          remember (map (fun v => lower_atomic_value v) (map snd vl)) as vl'.
          remember (mk_atomic_wf_context (mk_context map.empty xl vl') ts g_sig g_str) as ctx.
          assert_exists_hyps' ctx rls hyps.
          { prove_exists_hyps'; unfold str_wf; auto. }
          destruct_exists.
          econstructor.
          1:{ rewrite Exists_exists; eexists; intuition idtac.
              1: apply_incl; left; reflexivity.
              econstructor. repeat eexists; repeat econstructor;
                repeat rewrite_asm; eauto.
              1:{ subst.
                  case_match; repeat econstructor; cbn.
                  1,3: try rewrite Z.add_0_r; apply get_atomic_wf_context_time_var; unfold str_wf; auto.
                  1: reflexivity. }
              1:{ prove_interp_expr_attr_vars. }
              1:{ instantiate(1:=Zobj ts). subst.
                  apply get_atomic_wf_context_time_var; unfold str_wf; auto. }
              1:{ instantiate (1:=map lower_atomic_value (map snd vl)).
                  prove_interp_expr_attr_vars. } }
          1:{ cbn; constructor; try apply Forall_app; intuition auto.
              subst. assumption. } }
      (* EInsert *)
      1:{ apply_type_sound; eauto; invert_type_of_value; cbn.
          rewrite Lists.List.Forall_map.
          eapply incl_Forall.
          1: apply set_insert_incl2.
          constructor.
          1:{ cbn.
              remember (mk_atomic_wf_context map.empty ts g_sig g_str) as ctx.
              assert_exists_hyps' ctx rls hyps.
              { prove_exists_hyps'. }
              assert_exists_hyps' ctx rls l1.
              { apply construct_hyps_interp.
                eapply lower_rexpr_asms_hold; eauto.
                subst. apply mk_atomic_wf_context_wf; auto. }
              repeat destruct_exists; intuition idtac; econstructor.
              1:{ rewrite Exists_exists; eexists; intuition idtac.
                  1:{ apply_incl. rewrite in_app_iff; right.
                      left; reflexivity. }
                  repeat econstructor; cbn.
                  1:{ instantiate(1:=ctx); subst.
                      case_match; repeat econstructor; try rewrite Z.add_0_r; eauto using get_atomic_wf_context_time_var. }
                  1:{ subst; eapply lower_rexpr_complete; eauto using tenv_wf_empty, venv_wf_empty, mk_atomic_wf_context_wf. }
                  1:{ apply Forall2_app; eauto. } }
              1:{ cbn; rewrite app_nil_r.
                  apply Forall_app. intuition auto. } }
          1:{ lazymatch goal with
              H: type_of_rexpr _ _ _ _ |- _ =>
                apply get_rexpr_type_correct in H as Hr;
                rewrite Hr in *; clear Hr;
                inversion H; subst
            end.
              lazymatch goal with
                IH: context[type_of_expr _ _ _ -> _],
                  H: type_of_expr _ _ _ |- _ =>
                  eapply IH in H
              end; eauto using incl_app_bw_l.
              unfold is_lowered_to_at in *.
              rewrite <- H in *; cbn in *.
              rewrite Z.add_0_r, Lists.List.Forall_map in *.
              rewrite Forall_forall; intros; apply_Forall_In.
              apply_Forall_In; invert_type_of_value.
              remember (mk_atomic_wf_context (mk_context map.empty (map attr_var (map fst vl)) (map lower_atomic_value (map snd vl))) ts g_sig g_str) as ctx.
              assert_exists_hyps' ctx rls hyps.
              { prove_exists_hyps'. }
              destruct_exists; intuition idtac.
              econstructor.
              1:{ rewrite Exists_exists; eexists; split.
                  1:{ apply_incl. rewrite in_app_iff; right.
                      right. left. reflexivity. }
                  econstructor; repeat eexists; repeat constructor; cbn.
                  1:{ instantiate(1:=ctx); subst.
                      case_match; repeat econstructor; try rewrite Z.add_0_r; auto using get_atomic_wf_context_time_var. }
                  1: prove_interp_expr_attr_vars.
                  1:{ instantiate(1:=Zobj ts).
                      subst; auto using get_atomic_wf_context_time_var. }
                  1:{ instantiate(1:=map lower_atomic_value (map snd vl)).
                      prove_interp_expr_attr_vars. }
                  1: eauto. }
              1:{ cbn; rewrite app_nil_r; repeat constructor; auto. } } }
      (* EFilter *)
      1:{ apply_type_sound; eauto.
          invert_type_of_value.
          lazymatch goal with
            H: type_of_expr _ _ _ |- _ =>
              apply get_expr_type_correct in H as He;
              rewrite He in *; clear He;
              apply type_of_expr__type_wf in H as H_wf; auto
          end. repeat invert_type_wf.
          cbn. rewrite Forall_forall; intros.
          rewrite in_map_iff in *; destruct_exists;
            rewrite filter_In in *; intuition idtac.
          apply_Forall_In. invert_type_of_value.
          remember (mk_context (mk_atomic_wf_context map.empty ts g_sig g_str) (mk_vars x tl0) (map lower_atomic_value (map snd vl))) as ctx.
          assert_exists_hyps' ctx rls hyps.
          { apply construct_hyps_interp.
            lazymatch goal with
            | H:context [ context_wf ] |- _ => apply H
            end. subst. apply atomic_wf_context_step.
            apply mk_atomic_wf_context_wf; auto. }
          assert_exists_hyps' ctx rls (concat (map snd (map lower_pexpr p))).
          { apply construct_concat_hyps_interp.
            rewrite Forall_forall; intros.
            apply construct_hyps_interp.
            rewrite map_map, in_map_iff in *.
            destruct_exists. intuition idtac. apply_Forall_In.
            destruct (lower_pexpr x1) eqn:Ep.
            cbn in *; subst.
            eapply lower_pexpr_asms_hold; eauto.
            replace (map (fun x => lower_atomic_value (snd x)) vl) with
              (map lower_atomic_value (map snd vl)); auto using map_map.
            eapply context_wf_step; eauto using venv_wf_empty,
            mk_atomic_wf_context_wf; constructor; auto. }
          repeat destruct_exists; intuition idtac.
          econstructor.
          1:{ rewrite Exists_exists. eexists; split.
              1:{ apply_incl. rewrite in_app_iff; right.
                  left; reflexivity. }
              1:{ econstructor. repeat eexists; repeat econstructor.
                  1:{ instantiate (1:=ctx); subst.
                      case_match; try rewrite Z.add_0_r;
                        repeat econstructor;
                        try rewrite put_mk_vars_get_time_var;
                        auto using get_atomic_wf_context_time_var. }
                  1:{ subst. cbn.
                      apply interp_expr_mk_context_mk_vars; auto. }
                  1:{ instantiate (1:=Zobj ts); subst.
                      rewrite put_mk_vars_get_time_var;
                        auto using get_atomic_wf_context_time_var. }
                  1:{ subst; auto using interp_expr_mk_context_mk_vars. }
                  1:{ repeat apply Forall2_app; eauto.
                      1:{ apply lower_pexprs_true. subst.
                          eapply pexpr_forallb_true; eauto.
                          1:{ apply context_wf_step; auto using venv_wf_empty, mk_atomic_wf_context_wf;
                              constructor; auto. }
                          1: apply venv_wf_step; auto using venv_wf_empty; constructor; auto.
                          1: apply tenv_wf_step; auto using tenv_wf_empty; constructor; auto. } } } }
          1:{ cbn. constructor.
              1:{ eapply IHe in E; eauto.
                  2: eauto using incl_app_bw_l.
                  unfold is_lowered_to_at in E.
                  lazymatch goal with
                    H: _ = interp_expr _ _ |- _ =>
                      rewrite <- H in E
                  end.
                  rewrite Z.add_0_r in *.
                  cbn in *.
                  lazymatch goal with
                    H: In _ _ |- _ =>
                      apply in_map with (f:=lower_rec_value) in H
                  end. apply_Forall_In. }
              1: repeat (apply Forall_app; split); auto.
              rewrite Forall_forall; intros.
              rewrite in_map_iff in *; destruct_exists; intuition subst.
              econstructor.
              1:{ rewrite Exists_exists. eexists; split; eauto.
                  econstructor; repeat eexists; repeat econstructor. }
              cbn; trivial. } }
      (* EJoin *)
      1:{ lazymatch goal with
            H: type_of_expr _ e1 _ |- _ =>
              apply get_expr_type_correct in H as He;
              rewrite He in *; clear He;
              apply type_of_expr__type_wf in H as H_wf1; auto;
              eapply type_sound in H as H_sound1; eauto
        end.
          lazymatch goal with
            H: type_of_expr _ e2 _ |- _ =>
              apply get_expr_type_correct in H as He;
              rewrite He in *; clear He;
              apply type_of_expr__type_wf in H as H_wf2; auto;
              eapply type_sound in H as H_sound2; eauto
          end.
          repeat invert_type_of_value. repeat invert_type_wf.
          cbn. rewrite Forall_forall; intros.
          rewrite in_map_iff in *; destruct_exists; intuition idtac.
          lazymatch goal with
            H: In _ (value_sort _) |- _ =>
              eapply Permutation_in in H;
              [ | apply Permutation_sym, Permuted_value_sort]
          end.
          repeat (rewrite in_flat_map in *; destruct_exists; intuition idtac).
          destruct_match_hyp; [ | apply_in_nil; intuition fail ].
          destruct_In; [ | apply_in_nil; intuition fail ].
          repeat apply_Forall_In. repeat invert_type_of_value.
          remember (mk_context
                      (mk_context
                         (mk_atomic_wf_context map.empty ts g_sig g_str)
                         (mk_vars x tl1)
                         (map lower_atomic_value (map snd vl)))
                      (mk_vars y tl0)
                      (map lower_atomic_value (map snd vl0))) as ctx.
          assert_exists_hyps' ctx rls hyps.
          { apply construct_hyps_interp.
            lazymatch goal with
            | H:context [ context_wf ] |- _ => apply H
            end. subst. repeat apply atomic_wf_context_step.
            apply mk_atomic_wf_context_wf; auto. }
          assert_exists_hyps' ctx rls (concat (map snd (map lower_pexpr p))).
          { apply construct_concat_hyps_interp.
            rewrite Forall_forall; intros.
            apply construct_hyps_interp.
            rewrite map_map, in_map_iff in *.
            destruct_exists. intuition idtac. apply_Forall_In.
            destruct (lower_pexpr x1) eqn:Ep.
            cbn in *; subst.
            eapply lower_pexpr_asms_hold; eauto.
            repeat lazymatch goal with
              |- context[map (fun _ => lower_atomic_value (snd _)) ?vl] =>
            replace (map (fun x => lower_atomic_value (snd x)) vl) with
                (map lower_atomic_value (map snd vl)); auto using map_map
              end.
            repeat eapply context_wf_step; try apply venv_wf_step;
              eauto using venv_wf_empty, mk_atomic_wf_context_wf;
              constructor; auto. }
          assert_exists_hyps' ctx rls l7.
          { subst. apply construct_hyps_interp.
            eapply lower_rexpr_asms_hold; eauto.
            repeat eapply context_wf_step; repeat apply venv_wf_step;
              eauto using mk_atomic_wf_context_wf, venv_wf_empty;
              constructor; auto. }
          repeat destruct_exists; intuition idtac.
          econstructor.
          1:{ rewrite Exists_exists. eexists; split.
              1:{ apply_incl. do 2 (rewrite in_app_iff; right).
                  left; reflexivity. }
              1:{ econstructor; repeat eexists; repeat econstructor; cbn.
                  1:{ instantiate (1:=ctx); subst.
                      case_match; try rewrite Z.add_0_r; repeat econstructor.
                      1,3: rewrite !put_mk_vars_get_time_var;
                      apply get_atomic_wf_context_time_var; auto.
                      1: reflexivity. }
                  1:{ eapply lower_rexpr_complete; eauto.
                      1: subst; repeat apply context_wf_step.
                      all: repeat apply venv_wf_step;
                        repeat apply tenv_wf_step;
                        auto using mk_atomic_wf_context_wf, tenv_wf_empty, venv_wf_empty;
                        try constructor; auto. }
                  1,3: instantiate (1:=Zobj ts); subst;
                  rewrite !put_mk_vars_get_time_var;
                  apply get_atomic_wf_context_time_var; auto.
                  1:{ instantiate (1:=map lower_atomic_value (map snd vl)); subst.
                      apply interp_expr_mk_context_diff.
                      2: rewrite Forall_forall; eauto using neq_vars_mk_vars_disjoint.
                  apply interp_expr_mk_context_mk_vars; auto. }
                  1:{ instantiate (1:=map lower_atomic_value (map snd vl0)); subst.
                      apply interp_expr_mk_context_mk_vars; auto. }
                  1:{ repeat apply Forall2_app; eauto.
                      apply lower_pexprs_true; subst.
                      eapply pexpr_forallb_true;
                        eauto; repeat apply context_wf_step;
                        repeat apply venv_wf_step;
                        repeat apply tenv_wf_step;
                        eauto using mk_atomic_wf_context_wf, venv_wf_empty, tenv_wf_empty;
                      constructor; auto. } } }
          1:{ cbn. repeat constructor.
              1,2: lazymatch goal with
                   _: In (VRecord ?vl) ?l,
                     _: VSet ?l = interp_expr _ ?e,
                  IH: context[lower_expr _ _ _ _ _ ?e = _ -> _],
                         H: lower_expr _ _ _ _ _ ?e = _ |-
                   context[?vl] =>
                    eapply IH in H; eauto;
                    [ | eauto using incl_app_bw_r, incl_app_bw_l ];
                    unfold is_lowered_to_at in H
                 end;
              lazymatch goal with
                H: _ = ?x, _: context[?x] |- _ =>
                  rewrite <- H in *
              end;
              rewrite Z.add_0_r in *;
              cbn in *;
              lazymatch goal with
                _: Forall _ (map _ ?l),
                  H: In _ ?l |- _ =>
                  apply in_map with (f:=lower_rec_value) in H
              end; apply_Forall_In.
              1: repeat (apply Forall_app; split); auto.
              rewrite Forall_forall; intros.
              rewrite in_map_iff in *; destruct_exists; intuition subst.
              econstructor.
              1:{ rewrite Exists_exists. eexists; split; eauto.
                  econstructor; repeat eexists; repeat econstructor. }
              cbn; trivial. } }
      (* EProj *)
      1:{ lazymatch goal with
            H: type_of_expr _ e _ |- _ =>
              apply get_expr_type_correct in H as He;
              rewrite He in *; clear He;
              apply type_of_expr__type_wf in H as H_wf; auto;
              eapply type_sound in H as H_sound; eauto
        end.
          repeat invert_type_of_value. repeat invert_type_wf.
          cbn. rewrite Forall_forall; intros.
          rewrite in_map_iff in *; destruct_exists; intuition idtac.
           lazymatch goal with
            H: In _ (value_sort _) |- _ =>
              eapply Permutation_in in H;
              [ | apply Permutation_sym, Permuted_value_sort]
           end.
           rewrite in_map_iff in *; destruct_exists; intuition idtac.
           apply_Forall_In. invert_type_of_value.
           remember (mk_context
                       (mk_atomic_wf_context map.empty ts g_sig g_str)
                       (mk_vars x tl0)
                       (map lower_atomic_value (map snd vl))) as ctx.
          assert_exists_hyps' ctx rls hyps.
          { apply construct_hyps_interp.
            lazymatch goal with
            | H:context [ context_wf ] |- _ => apply H
            end. subst. repeat apply atomic_wf_context_step.
            apply mk_atomic_wf_context_wf; auto. }
          assert_exists_hyps' ctx rls l4.
          { subst. apply construct_hyps_interp.
            eapply lower_rexpr_asms_hold; eauto.
            repeat eapply context_wf_step; repeat apply venv_wf_step;
              eauto using mk_atomic_wf_context_wf, venv_wf_empty;
              constructor; auto. }
          repeat destruct_exists; intuition idtac.
          econstructor.
           1:{ rewrite Exists_exists. eexists; split.
               1:{ apply_incl. rewrite in_app_iff; right; left; reflexivity. }
               econstructor. repeat eexists; repeat econstructor.
               1:{ instantiate (1:=ctx); subst.
                   case_match; try rewrite Z.add_0_r; repeat econstructor.
                      1,3: rewrite !put_mk_vars_get_time_var;
                      apply get_atomic_wf_context_time_var; auto.
                      1: reflexivity. }
                  1:{ eapply lower_rexpr_complete; eauto.
                      1: subst; repeat apply context_wf_step.
                      all: repeat apply venv_wf_step;
                        repeat apply tenv_wf_step;
                        auto using mk_atomic_wf_context_wf, tenv_wf_empty, venv_wf_empty;
                        try constructor; auto. }
                  1: instantiate (1:=Zobj ts); subst;
               rewrite !put_mk_vars_get_time_var;
               apply get_atomic_wf_context_time_var; auto.
               1:{ instantiate (1:=map lower_atomic_value (map snd vl)); subst.
                   apply interp_expr_mk_context_mk_vars; auto. }
               1:{ apply Forall2_app; eauto. } }
           1:{ cbn. repeat constructor.
              1: lazymatch goal with
                   _: In (VRecord ?vl) ?l,
                     _: VSet ?l = interp_expr _ ?e,
                  IH: context[lower_expr _ _ _ _ _ ?e = _ -> _],
                         H: lower_expr _ _ _ _ _ ?e = _ |-
                   context[?vl] =>
                    eapply IH in H; eauto;
                    [ | eauto using incl_app_bw_r, incl_app_bw_l ];
                    unfold is_lowered_to_at in H
                 end;
              lazymatch goal with
                H: _ = ?x, _: context[?x] |- _ =>
                  rewrite <- H in *
              end;
              rewrite Z.add_0_r in *;
              cbn in *;
              lazymatch goal with
                _: Forall _ (map _ ?l),
                  H: In _ ?l |- _ =>
                  apply in_map with (f:=lower_rec_value) in H
              end; apply_Forall_In.
              1: repeat (apply Forall_app; split); auto. } }
      Unshelve. all: apply map.empty.
    Qed.

    Ltac invert_block_step :=
      lazymatch goal with
        H: block_step _ _ _ _ _ |- _ =>
          inversion H; subst
      end.

    Lemma lower_mut_assignments_complete : forall g_sig g_sig' asgns,
        Forall2 (fun tp e => type_of_expr g_sig e (snd tp)) g_sig' asgns ->
        forall hyps ts g_str next_rel dcls rls rls' next_rel',
          lower_mut_assignments hyps g_sig next_rel (combine (map fst g_sig') asgns) = (dcls, rls, next_rel') ->
          incl rls rls' ->
          In true_rl rls' ->
          str_wf g_sig g_str ->
          sig_wf g_sig ->
          venv_is_lowered_to_at g_str rls' ts ->
          (forall ctx : context,
              context_wf ts g_sig g_str map.empty map.empty ctx ->
              Forall
                (fun hyp : fact =>
                   exists hyp' : rel * list obj,
                     interp_fact ctx hyp hyp' /\ prog_impl_fact rls' hyp') hyps) ->
          Forall2
            (fun x v =>
               is_lowered_to_at v rls' (str_rel x) (ts + 1))
            (map fst g_sig') (map (interp_expr g_str) asgns).
    Proof.
      induction 1; cbn; intros.
      1:{ invert_pair. constructor. }
      1:{ repeat destruct_match_hyp; invert_pair.
          constructor.
          1:{ eapply lower_expr_complete in E; eauto.
              lazymatch goal with
                H: incl (_ ++ _) _ |- _ =>
                  apply incl_app_inv in H
              end; intuition fail. }
          1:{ eapply IHForall2; eauto.
              lazymatch goal with
                H: incl (_ ++ _) _ |- _ =>
                  apply incl_app_inv in H
              end; intuition fail. } }
    Qed.

    Lemma lower_blk_complete : forall g_sig g_blks next_rel blk n dcls blk_rls next_rel' rls g_str g_str' g_ptr' ts,
        lower_block g_sig next_rel blk n = (dcls, blk_rls, next_rel') ->
        incl blk_rls rls ->
        incl (map lower_mut_res g_sig) rls ->
        In true_rl rls ->
        well_typed_block g_sig (List.length g_blks) blk ->
        nth_error g_blks n = Some blk ->
        block_step (map fst g_sig) g_str blk g_str' g_ptr' ->
        str_wf g_sig g_str ->
        sig_wf g_sig ->
        venv_is_lowered_to_at g_str rls ts ->
        prog_impl_fact rls (blk_rel n, [Zobj ts]) ->
        match g_ptr' with
        | Some n' => venv_is_lowered_to_at g_str' rls (ts + 1) /\
                       prog_impl_fact rls (blk_rel n', [Zobj (ts + 1)])
        | None => venv_is_lowered_to g_str' rls
        end.
    Proof.
      destruct blk; cbn; intros.
      1:{ repeat destruct_match_hyp; subst.
          invert_block_step.
          lazymatch goal with
            H: context[well_typed_block] |- _ =>
              inversion H; subst
          end.
          split.
          1:{ unfold venv_is_lowered_to_at.
              eapply length_eq_Forall2_combine.
              1:{ rewrite !length_map.
                  eapply Forall2_length; eauto. }
              1:{ eapply lower_mut_assignments_complete; eauto.
                  1:{ invert_pair.
                      lazymatch goal with
                        H: incl (_ ++ _) _ |- _ =>
                          apply incl_app_inv in H
                      end. intuition fail. }
                  intros. repeat constructor.
                  eexists; intuition eauto. repeat constructor.
                  unfold context_wf in *; intuition fail. } }
          1:{ invert_pair. econstructor.
              1:{ rewrite Exists_exists. eexists.
                  intuition idtac.
                  1:{ rewrite incl_Forall_in_iff, Forall_app in *.
                      intuition idtac.
                      repeat invert_Forall.
                      eassumption. }
                  econstructor. repeat eexists;
                    repeat econstructor.
                  1: instantiate (2:=map.put map.empty time_var (Zobj ts)).
                  1,3: rewrite_map_get_put_goal; reflexivity.
                  constructor. }
              1:{ cbn. repeat constructor. assumption. } } }
      1:{ repeat destruct_match_hyp; subst.
          invert_block_step;
          lazymatch goal with
            H: context[well_typed_block] |- _ =>
              inversion H; subst
          end.
          (* then branch *)
          1:{ split.
              1:{ unfold venv_is_lowered_to_at.
                  eapply length_eq_Forall2_combine.
                  1:{ rewrite !length_map.
                      eapply Forall2_length; eauto. }
                  1:{ eapply lower_mut_assignments_complete; eauto.
                      1:{ invert_pair.
                          repeat (lazymatch goal with
                            H: incl (_ ++ _) _ |- _ =>
                              apply incl_app_inv in H
                          end; intuition idtac). }
                      intros. repeat constructor.
                      1:{ eexists; intuition eauto.
                          repeat constructor.
                          unfold context_wf in *; intuition fail. }
                      1:{ eexists. intuition idtac.
                          1:{ econstructor; repeat constructor.
                              eapply lower_pexpr_complete; eauto using tenv_wf_empty, venv_wf_empty. }
                          cbn. repeat econstructor.
                          rewrite Exists_exists. eexists; intuition eauto.
                          econstructor. repeat eexists; repeat econstructor;
                            cbn; congruence. }
                      1:{ eapply lower_pexpr_asms_hold; eauto. } } }
              1:{ invert_pair.
                  remember (mk_atomic_wf_context map.empty ts g_sig g_str) as ctx.
                  assert(exists asms', Forall2 (interp_fact ctx) l asms' /\ Forall (prog_impl_fact rls) asms').
                  { eapply construct_hyps_interp.
                    eapply lower_pexpr_asms_hold; eauto.
                    instantiate(1:=map.empty).
                    rewrite_asm. eapply mk_atomic_wf_context_wf; auto. }
                  destruct_exists. subst.
           econstructor.
                  1:{ rewrite Exists_exists. eexists.
                      intuition idtac.
                      1:{ apply H0. do 2 (apply in_or_app; right).
                          left. reflexivity. }
                      1:{ econstructor. repeat eexists; repeat econstructor; eauto using get_atomic_wf_context_time_var.
                          1: reflexivity.
                          1:{ eapply lower_pexpr_complete; eauto using tenv_wf_empty, venv_wf_empty, mk_atomic_wf_context_wf. } } }
                  1:{ cbn. repeat constructor;
                      try rewrite app_nil_r; intuition idtac.
                      econstructor.
                      1: rewrite Exists_exists; eexists; intuition eauto.
                      1: econstructor; repeat eexists; repeat econstructor; cbn; congruence.
                      trivial. } } }
          (* else branch *)
          1:{ split.
              1:{ unfold venv_is_lowered_to_at.
                  eapply length_eq_Forall2_combine.
                  1:{ rewrite !length_map.
                      eapply Forall2_length; eauto. }
                  1:{ eapply lower_mut_assignments_complete; eauto.
                      1:{ invert_pair.
                          repeat (lazymatch goal with
                            H: incl (_ ++ _) _ |- _ =>
                              apply incl_app_inv in H
                          end; intuition idtac). }
                      intros. repeat constructor.
                      1:{ eexists; intuition eauto.
                          repeat constructor.
                          unfold context_wf in *; intuition fail. }
                      1:{ eexists. intuition idtac.
                          1:{ econstructor; repeat econstructor.
                              1: eapply lower_pexpr_complete; eauto using tenv_wf_empty, venv_wf_empty.
                              reflexivity. }
                          cbn. repeat econstructor.
                          rewrite Exists_exists. eexists; intuition eauto.
                          econstructor. repeat eexists; repeat econstructor;
                            try rewrite_asm; cbn; congruence. }
                      1:{ eapply lower_pexpr_asms_hold; eauto. } } }
              1:{ invert_pair.
                  remember (mk_atomic_wf_context map.empty ts g_sig g_str) as ctx.
                  assert(exists asms', Forall2 (interp_fact ctx) l asms' /\ Forall (prog_impl_fact rls) asms').
                  { eapply construct_hyps_interp.
                    eapply lower_pexpr_asms_hold; eauto.
                    instantiate(1:=map.empty).
                    rewrite_asm. eapply mk_atomic_wf_context_wf; auto. }
                  destruct_exists. subst.
           econstructor.
                  1:{ rewrite Exists_exists. eexists.
                      intuition idtac.
                      1:{ apply H0. do 2 (apply in_or_app; right).
                          right; left. reflexivity. }
                      1:{ econstructor. repeat eexists; repeat econstructor; eauto using get_atomic_wf_context_time_var.
                          1: reflexivity.
                          1:{ eapply lower_pexpr_complete; eauto using tenv_wf_empty, venv_wf_empty, mk_atomic_wf_context_wf. }
                          1: reflexivity. } }
                  1:{ cbn. repeat constructor;
                      try rewrite app_nil_r; intuition idtac.
                      econstructor.
                      1: rewrite Exists_exists; eexists; intuition eauto.
                      1: econstructor; repeat eexists; repeat econstructor; try rewrite_asm; cbn; congruence.
                      trivial. } } } }
      1:{ invert_block_step.
          eapply lower_mut_res__venv_is_lowered_to; eauto.
          invert_pair. econstructor.
          1:{ rewrite Exists_exists.
              eexists; intuition idtac.
              1:{ rewrite incl_Forall_in_iff in H0.
                  invert_Forall. eassumption. }
              econstructor. repeat eexists;
                repeat econstructor.
              1: instantiate (1:=map.put map.empty time_var (Zobj ts)).
              all: rewrite_map_get_put_goal; reflexivity. }
          repeat constructor; cbn.
          assumption. }
      Unshelve.
      all: apply map.empty.
    Qed.

    Lemma incl_lower_block__lower_blocks : forall g_sig n m blks blk next_rel dcls rls next_rel',
        lower_blocks g_sig next_rel blks m = (dcls, rls, next_rel') ->
        nth_error blks n = Some blk ->
        exists blk_next_rel blk_dcls blk_rls blk_next_rel',
          lower_block g_sig blk_next_rel blk (n+m) = (blk_dcls, blk_rls, blk_next_rel') /\
            incl blk_rls rls.
    Proof.
      induction n; cbn; intros;
        destruct_match_hyp; try discriminate.
      1:{ do_injection. cbn in *.
          repeat destruct_match_hyp.
          invert_pair.
          repeat eexists; eauto using incl_appl, incl_refl. }
      1:{ cbn in *.
          repeat destruct_match_hyp.
          invert_pair.
          rewrite plus_n_Sm.
          eapply IHn in E2; eauto.
          repeat destruct_exists. intuition idtac.
          repeat eexists; eauto using incl_tran, incl_appr. }
    Qed.

    Theorem lower_cfg_complete' : forall (g : cfg) (g_d' : cfg_dynamic) dcls rls,
        lower_cfg g = (dcls, rls) ->
        well_typed_cfg g ->
        cfg_steps g.(sig_blks) g.(str_ptr) g_d' ->
        match g_d'.(ptr) with
        | Some n =>
            exists ts, venv_is_lowered_to_at g_d'.(str) rls ts /\
                         prog_impl_fact rls (blk_rel n, [Zobj ts])
        | None => venv_is_lowered_to g_d'.(str) rls
        end.
    Proof.
      unfold lower_cfg; intros.
      destruct g; cbn in *.
      intuition idtac.
      lazymatch goal with
        H: context[cfg_steps] |- _ =>
          induction H
      end; intros.
      1:{ unfold well_typed_cfg in *; cbn in *; intuition idtac.
          repeat destruct_match_hyp; subst;
          invert_pair.
          1:{ exists 0%Z; split.
              1:{ eapply venv_is_lowered_to_at_0; eauto.
                  apply incl_tl, incl_appl, incl_refl. }
              1:{ econstructor.
                  1:{ left. econstructor.
                      repeat eexists; eauto;
                        repeat econstructor. }
                  trivial. } }
          1:{ eapply lower_mut_res__venv_is_lowered_to; eauto.
              1:{ auto using incl_tl, incl_appl, incl_appr, incl_refl. }
              1:{ econstructor.
                  1:{ rewrite Exists_exists; eexists.
                      intuition idtac.
                      1: left; reflexivity.
                      econstructor; repeat eexists; repeat econstructor. }
                  1: trivial. }
              1:{ eapply venv_is_lowered_to_at_0; eauto.
                  auto using incl_tl, incl_appl, incl_refl. } } }
      1:{ lazymatch goal with
          H: well_typed_cfg _, H': cfg_steps _ _ _ |- _ =>
            eapply cfg_type_preservation in H' as H_ty
        end; eauto; inversion H_ty; subst; clear H_ty;
          cbn in *; intuition idtac.
          lazymatch goal with
            H: context[cfg_step] |- _ =>
              inversion H; subst
          end.
          repeat rewrite_asm_hyp.
          lazymatch goal with
            _: cfg_steps _ _ ?g_d,
              H: ptr ?g_d = Some _ |- _ =>
              eapply cfg_steps__ptr_Some in H
          end; eauto.
          destruct_exists. rewrite_asm_hyp.
          repeat destruct_match_hyp; subst.
          destruct_exists; intuition idtac.
          eapply incl_lower_block__lower_blocks in E; eauto.
          repeat destruct_exists. rewrite Nat.add_0_r in *; intuition idtac.
          eapply lower_blk_complete in H10.
          1:{ case_match; auto. 1: eexists; eauto. assumption. }
          all: eauto.
          1,2: invert_pair;
          eauto using incl_tran, incl_tl, incl_appr, incl_appl, incl_refl.
          1:{ invert_pair. right. rewrite !in_app_iff. repeat (right; try now left). }
          1:{ lazymatch goal with
              H: context[nth_error] |- _ =>
                eapply nth_error_In in H
            end. apply_Forall_In. } }
      Unshelve.
      all: apply map.empty.
    Qed.

    Theorem lower_cfg_complete : forall (g : cfg) (g_d' : cfg_dynamic) dcls rls,
        lower_cfg g = (dcls, rls) ->
        well_typed_cfg g ->
        cfg_steps g.(sig_blks) g.(str_ptr) g_d' ->
        g_d'.(ptr) = None ->
        venv_is_lowered_to g_d'.(str) rls.
    Proof.
      intros; eapply lower_cfg_complete' in H; eauto.
      rewrite_asm_hyp; assumption.
    Qed.

    (* ===== Compiler soundness proofs ===== *)

    Ltac invert_prog_impl_fact :=
      lazymatch goal with
            H: prog_impl_fact _ _ |- _ =>
              inversion H; subst; clear H
      end.

    Ltac invert_rule_impl :=
      lazymatch goal with
            H: rule_impl _ _ _ |- _ =>
              inversion H; subst; clear H
      end.

    Ltac invert_rule_impl' :=
      lazymatch goal with
            H: rule_impl' _ _ _ _ _ |- _ =>
              inversion H; subst; clear H
      end.

    Ltac invert_prog_impl_fact_singleton_concls :=
      invert_prog_impl_fact;
      rewrite Exists_exists in *; destruct_exists;
      intuition idtac;
      destruct_In; try (apply_in_nil; intuition fail);
      invert_rule_impl;
      repeat destruct_exists; intuition idtac;
      invert_rule_impl'; cbn in *;
      rewrite Exists_exists in *; destruct_exists;
      intuition idtac;
      destruct_In; try (apply_in_nil; intuition fail);
      invert_interp_fact; cbn in *;
      repeat invert_Forall2; repeat invert_Datalog_interp_expr;
      cbn in *; repeat destruct_match_hyp; try discriminate;
      cbn in *; repeat (clear_refl; do_injection).

    Lemma interp_dexpr_literal : forall ctx v v',
        Datalog.interp_expr ctx (dexpr_literal v) v' ->
        v = v'.
    Proof.
      destruct v; cbn; inversion 1; subst; cbn in *;
        destruct_match_hyp; cbn in *; congruence.
    Qed.

    Lemma Forall2_map_eq : forall A B f (xs : list A) (ys : list B),
        Forall2 (fun x y => f x = y) xs ys -> map f xs = ys.
    Proof.
      induction 1; auto; cbn.
      f_equal; auto.
    Qed.

    Lemma lower_init_value_sound : forall (x : string) (v : value) (t : type),
       type_of_value v t ->
       type_wf t ->
       forall vs, prog_impl_fact (lower_init_value (str_rel x) v) (str_rel x, Zobj 0 :: vs) ->
                  In vs (lower_value v).
    Proof.
      destruct 1; cbn.
      1-3: intros; left;
      invert_prog_impl_fact_singleton_concls; reflexivity.
      1:{ intros; left.
          invert_prog_impl_fact_singleton_concls; subst.
          apply Forall2_map_eq.
          rewrite <- !Forall2_map_l in *.
          eapply Forall2_impl; eauto.
          cbn; intros.
          eapply interp_dexpr_literal; eassumption. }
      1:{ intros. invert_type_wf.
          invert_prog_impl_fact.
          assert (l0 = []).
          { rewrite Exists_exists in *.
            destruct_exists; intuition idtac.
            rewrite in_map_iff in *.
            destruct_exists; intuition idtac.
            subst. invert_rule_impl.
            repeat destruct_exists.
            intuition idtac. invert_rule_impl'.
            cbn in *. invert_Forall2.
            lazymatch goal with
              H: interp_option_agg_expr _ _ _ _ |- _ =>
                inversion H; subst
            end.
            reflexivity. }
          subst. invert_Forall.
          induction H; cbn in *.
          1:{ rewrite Exists_nil in *; intuition fail. }
          1:{ inversion H0; subst; auto; clear H0.
              invert_rule_impl.
              repeat destruct_exists; intuition idtac.
              invert_rule_impl'; cbn in *.
              rewrite Exists_exists in *.
              destruct_exists; intuition idtac.
              repeat destruct_In; try apply_in_nil; intuition idtac.
              invert_interp_fact; cbn in *.
              invert_Forall2.
              left. unfold lower_rec_value in *.
              invert_type_of_value.
              eapply Forall2_map_eq.
              rewrite <- !Forall2_map_l in *.
              eapply Forall2_impl; eauto.
              cbn; intros. eauto using interp_dexpr_literal. } }
    Qed.

    Definition rl_only_from (P : rule -> Prop) (rls rls' : list rule) :=
      forall rl, P rl -> In rl rls -> In rl rls'.
(* ???
    (forall x r, P x -> r in R1
    (forall R_base fac, prog_impl_fact R_base fac -> P fac)
      [[ R1 ++ R2 ]] = [[ prog(R1) ++ R2 ]] *)

    Lemma venv_is_lowered_from_at_0 : forall g_sig g_str rls,
        sig_wf g_sig ->
        str_wf g_sig g_str ->
        incl (concat (map (fun '(x, v) => lower_init_value (str_rel x) v) g_str)) rls ->
        venv_is_lowered_from_at rls g_str 0.

(* ???
      (str_rel x, 0 :: a) :- (R, a).


      S : P(fact) <-> p : P(ground_rule).
      [[ init_rls ]]S : P(fact).
      = [[ init_rls ++ p ]].

      = [[ init_rls ++ p ]]S
          [[ p ]] [[ init_rls ]]S

          [[ init_rls ++ p ++ (prog(S)) ]] = [[ p + prog(init_rls ++ prog(S)) ]] *)


    Proof.
      unfold str_wf, sig_wf; intuition idtac. generalize dependent g_str.
      induction g_sig; cbn; intros; destruct g_str; try discriminate;
        constructor; cbn in *;
        intuition idtac; invert_Forall; invert_NoDup;
        invert_cons; invert_Forall2.
      1:{ case_match. unfold is_lowered_from_at.
          intros; cbn in *.
          invert_prog_impl_fact.
          rewrite Exists_exists in *.
          destruct_exists; intuition idtac.
          invert_rule_impl;
            repeat destruct_exists; intuition idtac;
            invert_rule_impl'; cbn in *;
            rewrite Exists_exists in *; destruct_exists;
            intuition idtac;
            invert_interp_fact.

          lazymatch goal with
            H: type_of_value _ _ |- _ =>
              eapply lower_init_value_sound in H
          end; eauto.
      admit. }
      1:{ apply IHg_sig; auto.
          eapply incl_app_bw_r. eauto. }
    Admitted.


        (* rl_only_from
          (fun rl => exists x, In (res_rel x) (map fact_R (rule_concls rl)))
          rls
          (List.map lower_mut_res g_sig) -> *)

    Lemma lower_mut_res__venv_is_lowered_from : forall g_sig g_str rls ts,
        incl (map lower_mut_res g_sig) rls ->
        sig_wf g_sig ->
        str_wf g_sig g_str ->
        prog_impl_fact rls (ret_rel, [Zobj ts]) ->
        venv_is_lowered_from_at rls g_str ts ->
        venv_is_lowered_from rls g_str.
    Proof.
    Admitted.

    Theorem lower_cfg_sound' : forall (g : cfg) (g_d' : cfg_dynamic) dcls rls,
        lower_cfg g = (dcls, rls) ->
        well_typed_cfg g ->
        cfg_steps g.(sig_blks) g.(str_ptr) g_d' ->
        match g_d'.(ptr) with
        | Some n =>
            exists ts, venv_is_lowered_from_at rls g_d'.(str) ts /\
                         prog_impl_fact rls (blk_rel n, [Zobj ts])
        | None => venv_is_lowered_from rls g_d'.(str)
        end.
     Proof.
      unfold lower_cfg; intros.
      destruct g; cbn in *.
      intuition idtac.
      lazymatch goal with
        H: context[cfg_steps] |- _ =>
          induction H
      end; intros.
      1:{ unfold well_typed_cfg in *; cbn in *; intuition idtac.
          repeat destruct_match_hyp; subst;
          invert_pair.
          1:{ exists 0%Z; split.
              1:{ eapply venv_is_lowered_from_at_0; eauto.
                  apply incl_tl, incl_appl, incl_refl. }
              1:{ econstructor.
                  1:{ left. econstructor.
                      repeat eexists; eauto;
                        repeat econstructor. }
                  trivial. } }
          1:{ eapply lower_mut_res__venv_is_lowered_from; eauto.
              1:{ auto using incl_tl, incl_appl, incl_appr, incl_refl. }
              1:{ econstructor.
                  1:{ rewrite Exists_exists; eexists.
                      intuition idtac.
                      1: left; reflexivity.
                      econstructor; repeat eexists; repeat econstructor. }
                  1: trivial. }
              1:{ eapply venv_is_lowered_from_at_0; eauto.
                  auto using incl_tl, incl_appl, incl_refl. } } }
      Admitted.
  End WithVarenv.
End __.

Print Assumptions lower_cfg_complete'.
