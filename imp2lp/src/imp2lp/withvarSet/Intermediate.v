From Stdlib Require Import String List ZArith.
From coqutil Require Import Map.Interface.
From Datalog Require Import Pftree Datalog.

Import ListNotations.

(* A structured Datalog IR for the CFG language with sets of records *)

(* ===== Relations and variables ===== *)

Variant global_rel : Type :=
  | mut_rel : nat -> global_rel     (* contents of mutable variable x *)
  | terminate_rel : global_rel      (* the program has returned *)
  | blk_rel : nat -> global_rel.    (* block n is active *)

Variant rel : Type :=
  | glob_rel : global_rel -> rel
  | aux_rel (a : nat).              (* local to one module *)

Inductive dvar : Type :=
  | mut_var : nat -> dvar
  | access_var : string -> string -> dvar  (* attribute attr of row variable x *)
  | attr_var : string -> dvar.

(* ===== Values and functions ===== *)

Variant dvalue : Set :=
  | DVNat (n : nat)
  | DVInt (z : Z)
  | DVBool (b : bool)
  | DVString (s : string).

(* Functions are monomorphic, with one equality per type, so that programs can
   be given types in TypedDatalog *)
Variant Bfn : Set :=
  | fn_BLit (_ : bool) | fn_Not | fn_And
  | fn_LtZ | fn_EqZ | fn_EqB | fn_EqS.

Variant Zfn : Set :=
  fn_ZLit (_ : Z) | fn_Plus | fn_StringLength.

Variant Nfn : Set :=
  fn_NLit (_ : nat) | fn_Incr.

Variant Sfn : Set :=
  fn_SLit (_ : string) | fn_StringConcat.

Variant fn : Set :=
  fnB (_ : Bfn) | fnZ (_ : Zfn) | fnN (_ : Nfn) | fnS (_ : Sfn).

Definition interp_Bfn (f : Bfn) (l : list dvalue) : option bool :=
  match f, l with
  | fn_BLit b, [] => Some b
  | fn_Not, [DVBool x] => Some (negb x)
  | fn_And, [DVBool x; DVBool y] => Some (x && y)%bool
  | fn_LtZ, [DVInt x; DVInt y] => Some (x <? y)%Z
  | fn_EqZ, [DVInt x; DVInt y] => Some (x =? y)%Z
  | fn_EqB, [DVBool x; DVBool y] => Some (Bool.eqb x y)
  | fn_EqS, [DVString x; DVString y] => Some (x =? y)%string
  | _, _ => None
  end.

Definition interp_Zfn (f : Zfn) (l : list dvalue) : option Z :=
  match f, l with
  | fn_ZLit z, [] => Some z
  | fn_Plus, [DVInt x; DVInt y] => Some (x + y)%Z
  | fn_StringLength, [DVString x] => Some (Z.of_nat (String.length x))
  | _, _ => None
  end.

Definition interp_Nfn (f : Nfn) (l : list dvalue) : option nat :=
  match f, l with
  | fn_NLit n, [] => Some n
  | fn_Incr, [DVNat n] => Some (S n)
  | _, _ => None
  end.

Definition interp_Sfn (f : Sfn) (l : list dvalue) : option string :=
  match f, l with
  | fn_SLit s, [] => Some s
  | fn_StringConcat, [DVString x; DVString y] => Some (x ++ y)%string
  | _, _ => None
  end.

Definition interp_fn (f : fn) (l : list dvalue) : option dvalue :=
  match f with
  | fnB f => option_map DVBool (interp_Bfn f l)
  | fnZ f => option_map DVInt (interp_Zfn f l)
  | fnN f => option_map DVNat (interp_Nfn f l)
  | fnS f => option_map DVString (interp_Sfn f l)
  end.

(* ===== Instantiating the Datalog framework ===== *)

(* No aggregation *)
Definition aggregator := Empty_set.

#[export] Instance ir_relT : relT := rel.
#[export] Instance ir_exprvarT : exprvarT := dvar.
#[export] Instance ir_fnT : fnT := fn.
#[export] Instance ir_aggregatorT : aggregatorT := aggregator.
#[export] Instance ir_valueT : valueT := dvalue.

#[export] Instance ir_semantics : datalog_semantics fn aggregator dvalue :=
  { interp_fun := interp_fn;
    get_nat := fun v => match v with DVNat n => n | _ => O end;
    agg_bop := fun a => match a with end;
    agg_id := fun a => match a with end }.

Section WithContext.
  Context {context : map.map dvar dvalue} {context_ok : map.ok context}.

  #[export] Instance ir_params : datalog_params (_rel := rel) := {}.

  (* A module is a Datalog program with ordinary rules only *)
  Definition module := program.

  Definition mk_module (rls : list rule) : module :=
    {| program.rules := rls; program.meta_rules := [] |}.

  (* ===== Block structure ===== *)

  Variant dflow :=
    | DFGoto (k : nat)
    | DFIf (cond : module) (k1 k2 : nat)
    | DFRet.

  Record dblock :=
    { dblock_asgns : list module; dblock_fl : dflow }.

  Record dprog :=
    { dprog_init : module; dprog_blks : list dblock }.

  (* ===== Semantics: one block per step, timestamps kept out of the rules ===== *)

  Definition mk_fact (R : rel) (args : list dvalue) : fact :=
    fact.normal {| normal_fact.rel := R; normal_fact.args := args |}.

  Definition mk_asgns_db (asgns : list module) (db : fact -> Prop) (f : fact) : Prop :=
    exists x asgn args,
      nth_error asgns x = Some asgn /\
        program.interp asgn db (mk_fact (aux_rel 0) args) /\
        f = mk_fact (glob_rel (mut_rel x)) args.

  Definition mk_flow_db (fl : dflow) (db : fact -> Prop) (f : fact) : Prop :=
    match fl with
    | DFGoto k => f = mk_fact (glob_rel (blk_rel k)) nil
    | DFIf cond k1 k2 =>
        (program.interp cond db (mk_fact (aux_rel 0) [DVBool true]) /\
           f = mk_fact (glob_rel (blk_rel k1)) nil) \/
          (program.interp cond db (mk_fact (aux_rel 0) [DVBool false]) /\
             f = mk_fact (glob_rel (blk_rel k2)) nil)
    | DFRet => f = mk_fact (glob_rel terminate_rel) nil
    end.

  Fixpoint dblocks_impl (blks : list dblock) (in_db : fact -> Prop) (t : nat) : fact -> Prop :=
    match t with
    | O => in_db
    | S t => let db := dblocks_impl blks in_db t in
             fun f => exists k blk,
                 db (mk_fact (glob_rel (blk_rel k)) nil) /\
                   nth_error blks k = Some blk /\
                   (mk_flow_db blk.(dblock_fl) db f \/
                      mk_asgns_db blk.(dblock_asgns) db f)
    end.

  Definition dprog_impl (prg : dprog) : nat -> fact -> Prop :=
    dblocks_impl prg.(dprog_blks) (program.interp prg.(dprog_init) (fun _ => False)).
End WithContext.
