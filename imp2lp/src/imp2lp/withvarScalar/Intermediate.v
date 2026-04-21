From Stdlib Require Import String List ZArith.
From imp2lp Require Import Value withvarScalar.SrcLang.
From coqutil Require Import Map.Interface.

Import ListNotations.

(* A structured Datalog IR for a scalar source language allowing loops  *)
Variant rel : Type :=
  | mut_rel : nat -> rel
  | terminate_rel : rel
  | aux_rel : nat -> rel
  | blk_rel : nat -> rel.

Inductive dexpr : Type :=
| DVar (a : nat)
| DBool (b : bool)
| DInt (n : Z)
| DNot (e : dexpr)
| DAnd (e1 e2 : dexpr)
| DPlus (e1 e2 : dexpr)
| DLt (e1 e2 : dexpr)
| DEq (e1 e2 : dexpr).

Record clause :=
  { clause_rel : rel; clause_args : list dexpr }.

Record rule :=
  { rule_concl : clause; rule_hyps : list clause }.

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

Variant dvalue : Type :=
  | DVBool (b : bool)
  | DVInt (n : Z).

Record fact :=
  { fact_rel : rel; fact_args : list dvalue }.

Definition mk_fact R args : fact :=
  {| fact_rel := R; fact_args := args |}.

Inductive pftree {T : Type} (P : T -> list T -> Prop) (Q : T -> Prop) : T -> Prop :=
| pftree_leaf x :
  Q x ->
  pftree _ _ x
| pftree_step x l :
  P x l ->
  Forall (pftree _ _) l ->
  pftree _ _ x.


Definition union_db {A} (db1 db2 : A -> Prop) :=
  fun f => db1 f \/ db2 f.

Definition equiv {A} (P Q : A -> Prop) :=
  forall a, P a <-> Q a.

Section WithMap.
 Context {context : map.map nat dvalue} {context_ok : map.ok context}.

 Inductive interp_clause : context -> clause -> fact -> Prop :=.

 Definition rule_impl (ctx : context) (rl : rule) (f : fact) (f_hyps : list fact) :=
   interp_clause ctx rl.(rule_concl) f /\
     Forall2 (interp_clause ctx) rl.(rule_hyps) f_hyps.

 Definition rules_impl (db : fact -> Prop) (rls : list rule) : fact -> Prop :=
   pftree (fun f f_hyps => exists rl ctx, In rl rls /\ rule_impl ctx rl f f_hyps) db.

 Definition mk_asgns_db (db : fact -> Prop) (asgns : list module) (f : fact) : Prop :=
   exists x asgn args,
     nth_error asgns x = Some asgn /\
       rules_impl db asgn (mk_fact (aux_rel 0) args) /\
       f = mk_fact (mut_rel x) args.

 Definition mk_flow_db (db : fact -> Prop) (fl : dflow) (f : fact) : Prop :=
   match fl with
   | DFGoto k => f = mk_fact (blk_rel k) nil
   | DFIf cond k1 k2 => (rules_impl db cond (mk_fact (aux_rel 0) [DVBool true]) /\ f = mk_fact (blk_rel k1) nil) \/
                          (rules_impl db cond (mk_fact (aux_rel 0) [DVBool false]) /\ f = mk_fact (blk_rel k2) nil)
   | DFRet => f = mk_fact terminate_rel nil
   end.

 Inductive dblocks_impl (blks : list dblock) : (fact -> Prop) -> nat -> (fact -> Prop) -> Prop :=
 | DIBase db : dblocks_impl blks db 0 db
 | DIStep db1 db2 db3 t k blk:
   dblocks_impl blks db1 t db2 ->
   db2 (mk_fact (blk_rel k) nil) ->
   nth_error blks k = Some blk ->
   equiv db3 (union_db (mk_flow_db db2 blk.(dblock_fl)) (mk_asgns_db db2 blk.(dblock_asgns))) ->
   dblocks_impl blks db1 (S t) db3.

 Definition dprog_impl (prg : dprog) : nat -> (fact -> Prop) -> Prop :=
   let init_db := rules_impl (fun _ => False) prg.(dprog_init) in
   dblocks_impl prg.(dprog_blks) init_db.
End WithMap.
