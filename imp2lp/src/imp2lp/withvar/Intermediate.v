From Stdlib Require Import String List ZArith.
From imp2lp Require Import Value.
From imp2lp.withvar Require Import SrcLang Datalog.
From coqutil Require Import Map.Interface.

Import ListNotations.

(* A structured Datalog IR for a scalar source language allowing loops  *)
Variant global_rel : Type :=
  | mut_rel : nat -> global_rel
  | terminate_rel : global_rel
  | blk_rel : nat -> global_rel.

Variant rel : Type :=
  | glob_rel : global_rel -> rel
  | aux_rel (a : nat).

Inductive dvar : Type :=
| mut_var : nat -> dvar
| access_var : string -> string -> dvar
| attr_var : string -> dvar.

Variant dvalue : Set :=
  | DVNat (n : nat)
  | DVInt (z : Z)
  | DVBool (b : bool)
  | DVString (s : string).

Variant Bfn : Set :=
  fn_BLit (_ : bool) | fn_Not | fn_And | fn_Lt | fn_Eq.

Variant Zfn : Set :=
  fn_ZLit (_ : Z) | fn_Plus | fn_StringLength.

Variant Nfn : Set :=
  fn_NLit (_ : nat) | fn_Incr.

Variant Sfn : Set :=
  fn_SLit (_ : string) | fn_StringConcat.

Variant fn : Set :=
  fnB (_ : Bfn) | fnZ (_ : Zfn) | fnN (_ : Nfn) | fnS (_ : Sfn).

Definition dvalue_eqb (x y : dvalue) : bool :=
  match x, y with
  | DVBool x, DVBool y => Bool.eqb x y
  | DVInt x, DVInt y => (x =? y)%Z
  | DVNat x, DVNat y => (x =? y)%nat
  | DVString x, DVString y => (x =? y)%string
  | _, _ => false
  end.

Definition interp_Bfn (f : Bfn) (l : list dvalue) : option bool :=
  match f, l with
  | fn_BLit b, [] => Some b
  | fn_Not, [DVBool x] => Some (negb x)
  | fn_And, [DVBool x; DVBool y] => Some (x && y)%bool
  | fn_Lt, [DVInt x; DVInt y] => Some (x <? y)%Z
  | fn_Eq, [x; y] => Some (dvalue_eqb x y)
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

Definition aggregator := False.

Notation dexpr := (Datalog.expr dvar fn).
Notation clause := (Datalog.clause rel dvar fn).
Notation rule := (Datalog.rule rel dvar fn aggregator).
Notation fact := (Datalog.fact rel dvalue).

Instance Sig : signature fn aggregator dvalue :=
  { interp_fun := interp_fn;
    interp_agg := fun _ _ => DVNat 0 }.

Definition module := list rule.

Variant dflow :=
  | DFGoto (k : nat)
  | DFIf (cond : module) (k1 k2 : nat)
  | DFRet.

Record dblock :=
  { dblock_asgns : list module; dblock_fl : dflow }.

Record dprog :=
  { dprog_init : module; dprog_blks : list dblock }.
(* init to encode initial mut dvar values and intitial block number *)

Section WithMap.
 Context {context : map.map dvar dvalue} {context_ok : map.ok context}.

 Definition mk_asgns_db (asgns : list module) (db : fact -> Prop) (f : fact) : Prop :=
   exists x asgn args,
     nth_error asgns x = Some asgn /\
       prog_impl asgn db (normal_fact (aux_rel 0) args) /\
       f = normal_fact (glob_rel (mut_rel x)) args.

 Definition mk_flow_db (fl : dflow) (db : fact -> Prop) (f : fact) : Prop :=
   match fl with
   | DFGoto k => f = normal_fact (glob_rel (blk_rel k)) nil
   | DFIf cond k1 k2 => (prog_impl cond db (normal_fact (aux_rel 0) [DVBool true]) /\
                           f = normal_fact (glob_rel (blk_rel k1)) nil) \/
                          (prog_impl cond db (normal_fact (aux_rel 0) [DVBool false]) /\
                             f = normal_fact (glob_rel (blk_rel k2)) nil)
   | DFRet => f = normal_fact (glob_rel terminate_rel) nil
   end.

 Fixpoint dblocks_impl (blks : list dblock) (in_db : fact -> Prop) (t : nat) : fact -> Prop :=
   match t with
   | O => in_db
   | S t => let db := dblocks_impl blks in_db t in
            fun f => exists k blk,
                db (normal_fact (glob_rel (blk_rel k)) nil) /\
                  nth_error blks k = Some blk /\
                  (mk_flow_db blk.(dblock_fl) db f \/
                     mk_asgns_db blk.(dblock_asgns) db f)
   end.

 Definition dprog_impl (prg : dprog) : nat -> fact -> Prop :=
   let init_db := prog_impl prg.(dprog_init) (fun _ => False) in
   dblocks_impl prg.(dprog_blks) init_db.
End WithMap.
