From Stdlib Require Import String List ZArith.
From imp2lp Require Import Value.
From imp2lp.withvarScalar Require Import SrcLang Datalog.
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
(* ???
Coercion glob_rel : global_rel >-> rel. *)

Variant fn :=
  | blit_fn (b : bool)
  | zlit_fn (z : Z)
  | nlit_fn (n : nat)
  | not_fn
  | and_fn
  | plus_fn
  | lt_fn
  | eq_fn.

Definition var := nat.

Variant dvalue : Type :=
  | DVNat (n : nat)
  | DVInt (z : Z)
  | DVBool (b : bool).

Definition dvalue_eqb (a b : dvalue) : bool :=
  match a, b with
  | DVInt n1, DVInt n2 => Z.eqb n1 n2
  | DVBool b1, DVBool b2 => Bool.eqb b1 b2
  | _, _ => false
  end.

Definition interp_fun (f : fn) (l : list dvalue) : option dvalue :=
  match f, l with
  | blit_fn b, [] => Some (DVBool b)
  | zlit_fn z, [] => Some (DVInt z)
  | nlit_fn n, [] => Some (DVNat n)
  | not_fn, [DVBool b] => Some (DVBool (negb b))
  | and_fn, [DVBool b1; DVBool b2] => Some (DVBool (andb b1 b2))
  | plus_fn, [DVInt z1; DVInt z2] => Some (DVInt (z1 + z2))
  | plus_fn, [DVNat n1; DVNat n2] => Some (DVNat (n1 + n2))
  | lt_fn, [DVInt z1; DVInt z2] => Some (DVBool (Z.ltb z1 z2))
  | eq_fn, [v1; v2] => Some (DVBool (dvalue_eqb v1 v2))
  | _, _ => None
  end.

Definition aggregator := False.
Notation dexpr := (Datalog.expr var fn).
Notation clause := (Datalog.clause rel var fn).
Notation rule := (Datalog.rule rel var fn aggregator).
Notation fact := (Datalog.fact rel dvalue).

Instance Sig : signature fn False dvalue :=
  { interp_fun := interp_fun;
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
(* init to encode initial mut var values and intitial block number *)

Section WithMap.
 Context {context : map.map nat dvalue} {context_ok : map.ok context}.

 Definition mk_asgns_db (db : fact -> Prop) (asgns : list module) (f : fact) : Prop :=
   exists x asgn args,
     nth_error asgns x = Some asgn /\
       prog_impl asgn db (normal_fact (aux_rel 0) args) /\
       f = normal_fact (glob_rel (mut_rel x)) args.

 Definition mk_flow_db (db : fact -> Prop) (fl : dflow) (f : fact) : Prop :=
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
                  (mk_flow_db db blk.(dblock_fl) f \/
                     mk_asgns_db db blk.(dblock_asgns) f)
   end.

 Definition dprog_impl (prg : dprog) : nat -> fact -> Prop :=
   let init_db := prog_impl prg.(dprog_init) (fun _ => False) in
   dblocks_impl prg.(dprog_blks) init_db.
End WithMap.
