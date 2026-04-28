From imp2lp.withvarScalar Require Import Intermediate BlockDatalog Datalog.
From Stdlib Require Import ZArith List.
Import ListNotations.

Variant rel' : Type :=
  | mut_rel' (x : nat)
  | blk_rel' (b : nat)
  | terminate_rel'
  | aux_rel' (b : nat) (x : option nat) (a : nat)
  | out_rel' (x : nat).

Variant fn :=
  | blit_fn (b : bool)
  | zlit_fn (z : Z)
  | nlit_fn (n : nat)
  | not_fn
  | and_fn
  | plus_fn
  | lt_fn
  | eq_fn.

Variant var' :=
  | dvar (n : nat)
  | time_var.

Notation aggregator := False.
Notation expr' := (Datalog.expr var' fn).
Notation clause' := (Datalog.clause rel' var' fn).
Notation rule' := (rule rel' var' fn aggregator).

Fixpoint lower_dexpr (e : dexpr) : expr' :=
  match e with
  | DVar x => var_expr (dvar x)
  | DBool b => fun_expr (blit_fn b) []
  | DInt z => fun_expr (zlit_fn z) []
  | DNot e => fun_expr not_fn [lower_dexpr e]
  | DAnd e1 e2 => fun_expr and_fn [lower_dexpr e1; lower_dexpr e2]
  | DPlus e1 e2 => fun_expr plus_fn [lower_dexpr e1; lower_dexpr e2]
  | DLt e1 e2 => fun_expr lt_fn [lower_dexpr e1; lower_dexpr e2]
  | DEq e1 e2 => fun_expr eq_fn [lower_dexpr e1; lower_dexpr e2]
  end.

Notation clause_rel0 := Intermediate.clause_rel.
Notation clause_args0 := Intermediate.clause_args.

Section WithParams.
  Context (b : nat) (x : option nat).
  (* x = None if not lowering an assignment *)

  Definition lower_rel (r : rel) : rel' :=
    match r with
    | mut_rel y => mut_rel' y
    | terminate_rel => terminate_rel'
    | aux_rel a => aux_rel' b x a
    | blk_rel b => blk_rel' b
    end.

  Definition lower_clause (cl : Intermediate.clause) : Datalog.clause rel' var' fn :=
    {| clause_rel := lower_rel cl.(clause_rel0);
      clause_args := (var_expr time_var) :: List.map lower_dexpr cl.(clause_args0) |}.

  Definition lower_rule (rl : Intermediate.rule) : rule' :=
    normal_rule
      [ lower_clause rl.(rule_concl) ]
      (List.map lower_clause rl.(rule_hyps)).

  Definition mk_blk_active_clause (ts : expr') : clause' :=
    {| clause_rel := blk_rel' b; clause_args := [ts] |}.
End WithParams.

Definition one_plus (e : expr') : expr' :=
  fun_expr plus_fn [fun_expr (nlit_fn 1) []; e ].

Definition lower_init_clause (cl : Intermediate.clause) : Datalog.clause rel' var' fn :=
  {| clause_rel := lower_rel 0 None cl.(clause_rel0);
    clause_args := (fun_expr (nlit_fn 0) []) :: List.map lower_dexpr cl.(clause_args0) |}.

Definition lower_init_rule (rl : Intermediate.rule) : rule' :=
  normal_rule
    [ lower_init_clause rl.(rule_concl) ]
    [].

Definition mk_mut_update_rule (b x : nat) : rule' :=
  normal_rule
    [ {| clause_rel := mut_rel' x; clause_args := [ one_plus (var_expr time_var); var_expr (dvar 0) ] |} ]
    [ {| clause_rel := aux_rel' b (Some x) 0; clause_args := [ var_expr time_var; var_expr (dvar 0) ] |};
      mk_blk_active_clause b (var_expr time_var) ].

Definition lower_flow (b : nat) (fl : dflow) : list rule' :=
  match fl with
  | DFGoto b' =>
      [ normal_rule
          [ mk_blk_active_clause b' (one_plus (var_expr time_var)) ]
          [ mk_blk_active_clause b (var_expr time_var) ] ]
  | DFIf p b1 b2 =>
      List.map (lower_rule b None) p ++
        [ normal_rule
            [ mk_blk_active_clause b1 (one_plus (var_expr time_var)) ]
            [ mk_blk_active_clause b (var_expr time_var);
              {| clause_rel := aux_rel' b None 0; clause_args := [var_expr time_var; fun_expr (blit_fn true) []] |} ];
          normal_rule
            [ mk_blk_active_clause b2 (one_plus (var_expr time_var)) ]
            [ mk_blk_active_clause b (var_expr time_var);
              {| clause_rel := aux_rel' b None 0; clause_args := [var_expr time_var; fun_expr (blit_fn false) []] |} ]
        ]
  | DFRet => [ normal_rule
                 [ {| clause_rel := terminate_rel'; clause_args := [var_expr time_var] |} ]
                 [ mk_blk_active_clause b (var_expr time_var) ] ]
  end.

Fixpoint apply_with_idx' {A B} (f : nat -> A -> list B) (x : nat) (l : list A) : list B :=
  match l with
  | [] => []
  | a :: l => f x a ++ apply_with_idx' f (S x) l
  end.

Definition apply_with_idx {A B} (f : nat -> A -> list B) := apply_with_idx' f 0.

Definition lower_asgns (b : nat) (l : list module) : list rule' :=
  apply_with_idx (fun x rls => mk_mut_update_rule b x :: List.map (lower_rule b (Some x)) rls) l.

Definition mk_out_rule (x : nat) : rule' :=
  normal_rule
    [ {| clause_rel := out_rel' x; clause_args := [var_expr (dvar 0)] |} ]
    [ {| clause_rel := mut_rel' x; clause_args := [var_expr time_var; var_expr (dvar 0)] |};
      {| clause_rel := terminate_rel'; clause_args := [var_expr time_var] |}].

Definition mk_out_rules (l : list unit) :=
  apply_with_idx (fun x _ => [mk_out_rule x]) l.

Definition lower_dblock (b : nat) (blk : dblock) : list rule' :=
  lower_asgns b blk.(dblock_asgns) ++ lower_flow b blk.(dblock_fl).

Definition lower_dblocks (blks : list dblock) :=
    apply_with_idx (fun b blk => lower_dblock b blk) blks.

Definition lower_dprog (pr : dprog) : list rule' :=
  List.map lower_init_rule pr.(dprog_init) ++ lower_dblocks pr.(dprog_blks).

Definition concl_is_aux_rel (rl : Intermediate.rule) : Prop :=
  match rl.(rule_concl).(clause_rel0) with
  | aux_rel _ => False
  | _ => True
  end.

Definition init_module_wf (rls : module) :=
  Forall (fun rl => ~ concl_is_aux_rel rl /\
                      rl.(rule_hyps) = []) rls.

Definition dblock_wf (blk : dblock) :=
  Forall (Forall concl_is_aux_rel) blk.(dblock_asgns) /\
    match blk.(dblock_fl) with
    | DFIf p _ _ => Forall concl_is_aux_rel p
    | _ => True
    end.

Definition dprog_wf (pr : dprog) :=
  init_module_wf pr.(dprog_init) /\
    Forall dblock_wf pr.(dprog_blks).
