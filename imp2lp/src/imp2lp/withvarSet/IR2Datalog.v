From imp2lp.withvarSet Require Import Intermediate Utils.
From Stdlib Require Import List String ZArith.
From Datalog Require Import Pftree Datalog.
From coqutil Require Import Map.Interface.

Import ListNotations.

(* Compiler from the structured Datalog IR to plain Datalog: each fact gains a
   timestamp column, and the rules of a block are guarded by "this block is
   active at time t".

   Definitions and correctness criteria only; no proofs yet. *)

(* ===== The target instantiation ===== *)

Variant rel' : Type :=
  | glob_rel' : global_rel -> rel'
  | aux_rel' (b : nat) (x : option nat) (a : nat).
  (* b: block, x: Some i when lowering the assignment to variable i,
     None for a branch condition; a: the IR's auxiliary relation number *)

Variant var' : Type :=
  | dvar' (v : dvar)
  | time_var.

(* The IR's types, named before the target instances shadow the abbreviations *)
Definition ir_expr := @expr.expr dvar fn.
Definition ir_clause := @clause.clause Intermediate.rel dvar fn.
Definition ir_rule := @rule.rule Intermediate.rel dvar fn aggregator.

#[export] Instance tgt_relT : relT := rel'.
#[export] Instance tgt_exprvarT : exprvarT := var'.

Section WithContext'.
  Context {context' : map.map var' dvalue} {context'_ok : map.ok context'}.

  #[export] Instance tgt_params : datalog_params (_rel := rel') (_exprvar := var') := {}.

  (* ===== Lowering rules ===== *)

  Fixpoint lower_dexpr (e : ir_expr) : expr :=
    match e with
    | expr.var x => expr.var (dvar' x)
    | expr.app f args => expr.app f (List.map lower_dexpr args)
    end.

  Definition mk_clause' (R : rel') (args : list expr) : clause :=
    {| clause.rel := R; clause.args := args |}.

  Definition time : expr := expr.var time_var.

  Definition one_plus (e : expr) : expr := expr.app (fnN fn_Incr) [e].

  Definition zero : expr := expr.app (fnN (fn_NLit 0)) [].

  Section WithParams.
    Context (b : nat) (x : option nat).

    Definition lower_rel (r : Intermediate.rel) : rel' :=
      match r with
      | glob_rel r => glob_rel' r
      | aux_rel a => aux_rel' b x a
      end.

    Definition lower_clause (cl : ir_clause) : clause :=
      mk_clause' (lower_rel cl.(clause.rel)) (time :: List.map lower_dexpr cl.(clause.args)).

    Definition lower_rule (rl : ir_rule) : rule :=
      match rl with
      | rule.impl concls hyps =>
          rule.impl (List.map lower_clause concls) (List.map lower_clause hyps)
      | _ => rule.impl [] []
      end.

    Definition mk_blk_active_clause (ts : expr) : clause :=
      mk_clause' (glob_rel' (blk_rel b)) [ts].
  End WithParams.

  (* The initial store and program counter are asserted at time 0 *)
  Definition lower_init_clause (cl : ir_clause) : clause :=
    mk_clause' (lower_rel 0 None cl.(clause.rel)) (zero :: List.map lower_dexpr cl.(clause.args)).

  Definition lower_init_rule (rl : ir_rule) : rule :=
    match rl with
    | rule.impl [ concl ] [] => rule.impl [ lower_init_clause concl ] []
    | _ => rule.impl [] []
    end.

  (* One variable per column; [n] is the arity of the mutable variable *)
  Definition mut_args (n : nat) : list expr :=
    List.map (fun i => expr.var (dvar' (mut_var i))) (seq 0 n).

  Definition mk_mut_update_rule (b x n : nat) : rule :=
    rule.impl
      [ mk_clause' (glob_rel' (mut_rel x)) (one_plus time :: mut_args n) ]
      [ mk_clause' (aux_rel' b (Some x) 0) (time :: mut_args n);
        mk_blk_active_clause b time ].

  Definition lower_flow (b : nat) (fl : dflow) : list rule :=
    match fl with
    | DFGoto b' =>
        [ rule.impl
            [ mk_blk_active_clause b' (one_plus time) ]
            [ mk_blk_active_clause b time ] ]
    | DFIf p b1 b2 =>
        List.map (lower_rule b None) p.(program.rules) ++
          [ rule.impl
              [ mk_blk_active_clause b1 (one_plus time) ]
              [ mk_blk_active_clause b time;
                mk_clause' (aux_rel' b None 0) [time; expr.app (fnB (fn_BLit true)) []] ];
            rule.impl
              [ mk_blk_active_clause b2 (one_plus time) ]
              [ mk_blk_active_clause b time;
                mk_clause' (aux_rel' b None 0) [time; expr.app (fnB (fn_BLit false)) []] ] ]
    | DFRet =>
        [ rule.impl
            [ mk_clause' (glob_rel' terminate_rel) [one_plus time] ]
            [ mk_blk_active_clause b time ] ]
    end.

  (* [arities] gives the number of columns of each mutable variable's relation *)
  Definition lower_asgns (b : nat) (var_ar : list nat) (l : list module) : list rule :=
    apply_with_idx
      (fun x m =>
         match nth_error var_ar x with
         | Some n => mk_mut_update_rule b x n :: List.map (lower_rule b (Some x)) m.(program.rules)
         | None => []
         end) l.

  Definition lower_dblock (var_ar : list nat) (b : nat) (blk : dblock) : list rule :=
    lower_asgns b var_ar blk.(dblock_asgns) ++ lower_flow b blk.(dblock_fl).

  Definition lower_dblocks (var_ar : list nat) (blks : list dblock) : list rule :=
    apply_with_idx (lower_dblock var_ar) blks.

  Definition lower_dprog (var_ar : list nat) (pr : dprog) : list rule :=
    List.map lower_init_rule pr.(dprog_init).(program.rules) ++
      lower_dblocks var_ar pr.(dprog_blks).

  Definition tgt_program (rls : list rule) : program :=
    {| program.rules := rls; program.meta_rules := [] |}.

  (* ===== Well-formed IR programs ===== *)

  (* ===== Shapes =====

     The arity data is given explicitly, not existentially, so that per-module
     facts compose into a statement about the whole compiled program:
     [var_ar] is the arity of each mutable variable's relation, and
     [aux b x a] the arity of the IR's auxiliary relation [a] inside the module
     for block [b] and slot [x] ([Some i]: the assignment to variable [i];
     [None]: the branch condition).  The indices are exactly those of the
     target's [aux_rel' b x a]. *)

  Definition glob_arity (var_ar : list nat) (r : global_rel) : nat :=
    match r with
    | mut_rel x => nth x var_ar 0
    | blk_rel _ | terminate_rel => 0
    end.

  Definition concl_aux_arity_ok (aux : nat -> nat) (rl : ir_rule) : Prop :=
    match rl with
    | rule.impl [ concl ] _ =>
        match concl.(clause.rel) with
        | aux_rel a => List.length concl.(clause.args) = aux a
        | glob_rel _ => False
        end
    | _ => False
    end.

  Definition module_wf (aux : nat -> nat) (m : module) : Prop :=
    Forall (concl_aux_arity_ok aux) m.(program.rules) /\
      m.(program.meta_rules) = [].

  Definition init_module_wf (var_ar : list nat) (m : module) : Prop :=
    Forall (fun rl =>
              match rl with
              | rule.impl [ concl ] [] =>
                  match concl.(clause.rel) with
                  | glob_rel g => List.length concl.(clause.args) = glob_arity var_ar g
                  | aux_rel _ => False
                  end
              | _ => False
              end) m.(program.rules) /\
      m.(program.meta_rules) = [].

  Definition dblock_wf (var_ar : list nat) (aux : option nat -> nat -> nat) (blk : dblock) : Prop :=
    List.length blk.(dblock_asgns) = List.length var_ar /\
      (forall x m n,
          nth_error blk.(dblock_asgns) x = Some m ->
          nth_error var_ar x = Some n ->
          module_wf (aux (Some x)) m /\ aux (Some x) 0 = n) /\
      match blk.(dblock_fl) with
      | DFIf p _ _ => module_wf (aux None) p /\ aux None 0 = 1
      | _ => True
      end.

  Definition dprog_wf (var_ar : list nat) (aux : nat -> option nat -> nat -> nat) (pr : dprog) : Prop :=
    init_module_wf var_ar pr.(dprog_init) /\
      (forall b blk, nth_error pr.(dprog_blks) b = Some blk -> dblock_wf var_ar (aux b) blk).

  Section WithIRContext.
    Context {context : map.map dvar dvalue} {context_ok : map.ok context}.


    (* ===== Correctness criteria =====

       A global fact derived at timestamp [ts] by the Datalog program
       corresponds to the same fact in the IR's database at step [ts]. *)

    Lemma lower_dprog_sound :
      forall (var_ar : list nat) aux (pr : dprog),
        dprog_wf var_ar aux pr ->
        forall (g : global_rel) (us : list dvalue) (ts : nat),
          program.interp (tgt_program (lower_dprog var_ar pr)) (fun _ => False)
            (fact.normal {| normal_fact.rel := glob_rel' g;
                            normal_fact.args := DVNat ts :: us |}) ->
          dprog_impl pr ts (mk_fact (glob_rel g) us).
    Admitted.

    Lemma lower_dprog_complete :
      forall (var_ar : list nat) aux (pr : dprog),
        dprog_wf var_ar aux pr ->
        forall (g : global_rel) (us : list dvalue) (ts : nat),
          dprog_impl pr ts (mk_fact (glob_rel g) us) ->
          program.interp (tgt_program (lower_dprog var_ar pr)) (fun _ => False)
            (fact.normal {| normal_fact.rel := glob_rel' g;
                            normal_fact.args := DVNat ts :: us |}).
    Admitted.

  End WithIRContext.
End WithContext'.
