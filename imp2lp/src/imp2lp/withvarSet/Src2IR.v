From imp2lp.withvarSet Require Import SrcLang Intermediate Utils.
From imp2lp Require Import MyTactics Value.
From Stdlib Require Import List String.
From Datalog Require Import Pftree Datalog.
From coqutil Require Import Map.Interface Tactics.case_match Result.

Import ListNotations.

(* Compiler from the CFG source language to the structured Datalog IR.

   Definitions and correctness criteria only; no proofs yet.  The criteria are
   stated as [Prop]-valued definitions so that Rocq type-checks them without
   requiring a proof. *)

Definition mk_clause (R : rel) (args : list expr) : clause :=
  {| clause.rel := R; clause.args := args |}.

Definition mk_rule (concl : clause) (hyps : list clause) : rule :=
  rule.impl [ concl ] hyps.

Definition mk_dblock (asgns : list module) (fl : dflow) : dblock :=
  {| dblock_asgns := asgns; dblock_fl := fl |}.

Definition mk_dprog (init : module) (blks : list dblock) : dprog :=
  {| dprog_init := init; dprog_blks := blks |}.

Local Coercion glob_rel : global_rel >-> Intermediate.rel.

(* ===== Lowering expressions ===== *)

Fixpoint lower_aexpr (e : SrcLang.aexpr) : expr * list clause :=
  match e with
  | ALoc x =>
      (expr.var (mut_var x),
        [ mk_clause (glob_rel (mut_rel x)) [ expr.var (mut_var x) ] ])
  | ABool b => (expr.app (fnB (fn_BLit b)) [], [])
  | AInt z => (expr.app (fnZ (fn_ZLit z)) [], [])
  | AString s => (expr.app (fnS (fn_SLit s)) [], [])
  | ANot a =>
      let '(a', hyps) := lower_aexpr a in
      (expr.app (fnB fn_Not) [a'], hyps)
  | AAnd a1 a2 =>
      let '(a1', hyps1) := lower_aexpr a1 in
      let '(a2', hyps2) := lower_aexpr a2 in
      (expr.app (fnB fn_And) [a1'; a2'], hyps1 ++ hyps2)
  | APlus a1 a2 =>
      let '(a1', hyps1) := lower_aexpr a1 in
      let '(a2', hyps2) := lower_aexpr a2 in
      (expr.app (fnZ fn_Plus) [a1'; a2'], hyps1 ++ hyps2)
  | AStringConcat a1 a2 =>
      let '(a1', hyps1) := lower_aexpr a1 in
      let '(a2', hyps2) := lower_aexpr a2 in
      (expr.app (fnS fn_StringConcat) [a1'; a2'], hyps1 ++ hyps2)
  | AStringLength a =>
      let '(a', hyps) := lower_aexpr a in
      (expr.app (fnZ fn_StringLength) [a'], hyps)
  | AAccess x attr => (expr.var (access_var x attr), [])
  end.

Definition lower_rexpr (r : rexpr) : list expr * list clause :=
  match r with
    RRecord el =>
      (List.map (fun '(_, a) => fst (lower_aexpr a)) (record_sort el),
        List.concat (List.map (fun '(_, a) => snd (lower_aexpr a)) (record_sort el)))
  end.

(* Equality is monomorphic: the compiler picks the function from the operand type *)
Definition eq_fn (t : type) : fn :=
  match t with
  | TBool => fnB fn_EqB
  | TString => fnB fn_EqS
  | _ => fnB fn_EqZ
  end.

Section WithMap.
  Context {context : map.map dvar dvalue} {context_ok : map.ok context}.
  Context {tenv : map.map String.string type} {tenv_ok : map.ok tenv}.
  Context {venv : map.map String.string Value.value} {venv_ok : map.ok venv}.

  Section WithGSig.
    Context (g_sig : list type).

    Definition compute_type_of_aexpr (Genv : tenv) (a : SrcLang.aexpr) : type :=
      match a with
      | ALoc x => match nth_error g_sig x with
                  | Some t => t
                  | _ => TInt (* unreachable for well-typed expressions *)
                  end
      | ABool _ | ANot _ | AAnd _ _ => TBool
      | AInt _ | APlus _ _ | AStringLength _ => TInt
      | AString _ | AStringConcat _ _ => TString
      | AAccess x attr =>
          match map.get Genv x with
          | Some (TRecord l) =>
              match access_record l attr with
              | Success t => t
              | _ => TInt
              end
          | _ => TInt
          end
      end.

    Definition compute_type_of_rexpr (Genv : tenv) (r : SrcLang.rexpr) : type :=
      match r with
      | RRecord el =>
          TRecord (map (fun '(attr, a) => (attr, compute_type_of_aexpr Genv a)) (record_sort el))
      end.

    Fixpoint compute_type_of_expr (e : SrcLang.expr) : type :=
      match e with
      | EAtom a => compute_type_of_aexpr map.empty a
      | ELoc x => match nth_error g_sig x with
                  | Some t => t
                  | _ => TInt
                  end
      | EEmptySet tl => TSet (TRecord tl)
      | ESetInsert r e => compute_type_of_expr e
      | EFilter e _ _ => compute_type_of_expr e
      | EJoin e1 e2 x1 x2 _ r =>
          match compute_type_of_expr e1, compute_type_of_expr e2 with
          | TSet t1, TSet t2 =>
              TSet (compute_type_of_rexpr (map.put (map.put map.empty x1 t1) x2 t2) r)
          | _, _ => TInt
          end
      | EProj e x r =>
          match compute_type_of_expr e with
          | TSet t => TSet (compute_type_of_rexpr (map.put map.empty x t) r)
          | _ => TInt
          end
      end.

    (* Predicates are lowered against the type of their operands *)
    Definition lower_pexpr (Genv : tenv) (p : pexpr) : expr * list clause :=
      match p with
      | PLt a1 a2 =>
          let '(a1', hyps1) := lower_aexpr a1 in
          let '(a2', hyps2) := lower_aexpr a2 in
          (expr.app (fnB fn_LtZ) [a1'; a2'], hyps1 ++ hyps2)
      | PEq a1 a2 =>
          let '(a1', hyps1) := lower_aexpr a1 in
          let '(a2', hyps2) := lower_aexpr a2 in
          (expr.app (eq_fn (compute_type_of_aexpr Genv a1)) [a1'; a2'], hyps1 ++ hyps2)
      end.

    Fixpoint args_of_type (t : type) : list string :=
      match t with
      | TInt | TBool | TString => [""%string]
      | TRecord l => map fst l
      | TSet t => args_of_type t
      end.

    (* [lower_expr' out e] gives [e]'s rules, with its result in relation
       [aux_rel out], and the first unused relation number. *)
    Fixpoint lower_expr' (Genv : tenv) (out : nat) (e : SrcLang.expr) : (list rule * nat) :=
      match e with
      | EAtom a =>
          let '(a', hyps) := lower_aexpr a in
          ([ mk_rule (mk_clause (aux_rel out) [a']) hyps ], S out)
      | ELoc x =>
          let attrs := args_of_type (compute_type_of_expr e) in
          let args := map (fun attr => expr.var (attr_var attr)) attrs in
          ([ mk_rule (mk_clause (aux_rel out) args)
               [ mk_clause (glob_rel (mut_rel x)) args ] ], S out)
      | EEmptySet tl => ([], S out)
      | ESetInsert r e =>
          let '(r', hyps) := lower_rexpr r in
          let '(rls, out') := lower_expr' Genv (S out) e in
          let attrs := args_of_type (compute_type_of_expr e) in
          let args := map (fun attr => expr.var (attr_var attr)) attrs in
          ([ mk_rule (mk_clause (aux_rel out) r') hyps;
             mk_rule (mk_clause (aux_rel out) args)
               [ mk_clause (aux_rel (S out)) args ] ] ++ rls,
            out')
      | EFilter e x ps =>
          let true_out := S out in
          let e_out := S (S out) in
          let '(rls, out') := lower_expr' Genv e_out e in
          let Genv' := map.put Genv x (compute_type_of_expr e) in
          let ps' := map (lower_pexpr Genv') ps in
          let attrs := args_of_type (compute_type_of_expr e) in
          let args := map (fun attr => expr.var (access_var x attr)) attrs in
          ([ mk_rule (mk_clause (aux_rel out) args)
               ([ mk_clause (aux_rel e_out) args ] ++
                  flat_map (fun '(p', hyps) => [ mk_clause (aux_rel true_out) [p'] ] ++ hyps) ps');
             mk_rule (mk_clause (aux_rel true_out) [expr.app (fnB (fn_BLit true)) []]) [] ] ++ rls,
            out')
      | EJoin e1 e2 x1 x2 ps r =>
          let true_out := S out in
          let e1_out := S (S out) in
          let '(rls1, out1') := lower_expr' Genv e1_out e1 in
          let e2_out := S out1' in
          let '(rls2, out2') := lower_expr' Genv e2_out e2 in
          let Genv' := map.put (map.put Genv x1 (compute_type_of_expr e1)) x2 (compute_type_of_expr e2) in
          let ps' := map (lower_pexpr Genv') ps in
          let '(r', hyps) := lower_rexpr r in
          let attrs1 := args_of_type (compute_type_of_expr e1) in
          let args1 := map (fun attr => expr.var (access_var x1 attr)) attrs1 in
          let attrs2 := args_of_type (compute_type_of_expr e2) in
          let args2 := map (fun attr => expr.var (access_var x2 attr)) attrs2 in
          ([ mk_rule (mk_clause (aux_rel out) r')
               ([ mk_clause (aux_rel e1_out) args1;
                  mk_clause (aux_rel e2_out) args2 ] ++
                  flat_map (fun '(p', hyps) => [ mk_clause (aux_rel true_out) [p'] ] ++ hyps) ps');
             mk_rule (mk_clause (aux_rel true_out) [expr.app (fnB (fn_BLit true)) []]) [] ] ++
             rls1 ++ rls2,
            out2')
      | EProj e x r =>
          let e_out := S out in
          let '(rls, out') := lower_expr' Genv e_out e in
          let '(r', hyps) := lower_rexpr r in
          let attrs := args_of_type (compute_type_of_expr e) in
          let args := map (fun attr => expr.var (access_var x attr)) attrs in
          ([ mk_rule (mk_clause (aux_rel out) r')
               ([ mk_clause (aux_rel e_out) args ] ++ hyps) ] ++ rls,
            out')
      end.

    Definition lower_expr (e : SrcLang.expr) : module :=
      mk_module (fst (lower_expr' map.empty 0 e)).

    (* ===== Lowering the rest ===== *)

    Definition lower_flow (fl : flow) : dflow :=
      match fl with
      | FGoto n => DFGoto n
      | FIf p n1 n2 => DFIf (lower_expr p) n1 n2
      | FRet => DFRet
      end.

    Definition lower_block (blk : block) : dblock :=
      match blk with
        Blk asgns fl => mk_dblock (map lower_expr asgns) (lower_flow fl)
      end.

    Definition lower_atomic_value_reified (v : Value.value) : list expr :=
      match v with
      | VInt n => [ expr.app (fnZ (fn_ZLit n)) [] ]
      | VBool b => [ expr.app (fnB (fn_BLit b)) [] ]
      | VString s => [ expr.app (fnS (fn_SLit s)) [] ]
      | _ => []
      end.

    Fixpoint lower_value_reified (v : Value.value) : list (list expr) :=
      match v with
      | VInt _ | VBool _ | VString _ => [ lower_atomic_value_reified v ]
      | VRecord l => [ flat_map lower_atomic_value_reified (map snd l) ]
      | VList l | VSet l => flat_map lower_value_reified l
      end.

    Definition lower_init_str : list Value.value -> list rule :=
      apply_with_idx
        (fun x v =>
           map (fun vs' => mk_rule (mk_clause (mut_rel x) vs') []) (lower_value_reified v)).

    Definition lower_init_ptr (n : option nat) : rule :=
      match n with
      | Some n => mk_rule (mk_clause (blk_rel n) []) []
      | None => mk_rule (mk_clause terminate_rel []) []
      end.

    Definition lower_cfg (g : cfg) : dprog :=
      mk_dprog
        (mk_module (lower_init_ptr g.(str_ptr).(ptr) :: lower_init_str g.(str_ptr).(str)))
        (List.map lower_block g.(sig_blks).(blks)).
  End WithGSig.

  (* ===== How source states appear as Datalog facts ===== *)

  Definition lower_atomic_value (v : Value.value) : list dvalue :=
    match v with
    | VBool b => [ DVBool b ]
    | VInt n => [ DVInt n ]
    | VString s => [ DVString s ]
    | _ => []
    end.

  Fixpoint lower_value (v : Value.value) : list (list dvalue) :=
    match v with
    | VBool _ | VInt _ | VString _ => [ lower_atomic_value v ]
    | VRecord l => [ flat_map lower_atomic_value (map snd l) ]
    | VList l | VSet l => flat_map lower_value l
    end.

  Definition lower_str (str : list Value.value) (f : fact) : Prop :=
    exists x v vs', nth_error str x = Some v /\
                      In vs' (lower_value v) /\
                      f = mk_fact (glob_rel (mut_rel x)) vs'.

  Definition lower_ptr (ptr : option nat) (f : fact) : Prop :=
    match ptr with
    | Some n => f = mk_fact (glob_rel (blk_rel n)) []
    | None => f = mk_fact (glob_rel terminate_rel) []
    end.

  Definition lower_state (g_d : cfg_dynamic) (f : fact) : Prop :=
    lower_str g_d.(str) f \/ lower_ptr g_d.(ptr) f.

  Definition lower_option_state (g_d : option cfg_dynamic) : fact -> Prop :=
    match g_d with
    | Some g_d => lower_state g_d
    | None => fun _ => False
    end.

  Definition db_subset (db1 db2 : fact -> Prop) : Prop :=
    forall f, db1 f -> db2 f.

  (* ===== Correctness criteria =====

     At step [ts], the facts derived by the compiled IR program are exactly the
     lowered source state: completeness is "lowered state is derived", soundness
     is "everything derived is lowered state". *)

  Lemma lower_cfg_complete :
    forall (ts : nat) (g : cfg) (g_d : cfg_dynamic),
      cfg_steps (venv:=venv) g.(sig_blks) g.(str_ptr) ts = Some g_d ->
      well_typed_cfg g ->
      forall f, lower_state g_d f ->
                dprog_impl (lower_cfg g.(sig_blks).(sig) g) ts f.
  Admitted.

  Lemma lower_cfg_sound :
    forall (g : cfg) (ts : nat),
      well_typed_cfg g ->
      db_subset
        (dprog_impl (lower_cfg g.(sig_blks).(sig) g) ts)
        (lower_option_state (cfg_steps (venv:=venv) g.(sig_blks) g.(str_ptr) ts)).
  Admitted.
End WithMap.
