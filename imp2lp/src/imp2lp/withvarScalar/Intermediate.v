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

Definition dvalue_eqb (a b : dvalue) : bool :=
  match a, b with
  | DVInt n1, DVInt n2 => Z.eqb n1 n2
  | DVBool b1, DVBool b2 => Bool.eqb b1 b2
  | _, _ => false
  end.

Record fact :=
  { fact_rel : rel; fact_args : list dvalue }.

Definition mk_fact R args : fact :=
  {| fact_rel := R; fact_args := args |}.

Unset Elimination Schemes.
Inductive pftree {T : Type} (P : T -> list T -> Prop) (Q : T -> Prop) : T -> Prop :=
| pftree_leaf x :
  Q x ->
  pftree _ _ x
| pftree_step x l :
  P x l ->
  Forall (pftree _ _) l ->
  pftree _ _ x.
Set Elimination Schemes.

Section __.
  Context (T : Type) (P : T -> list T -> Prop)
         (Q P0 : T -> Prop).
  Context (H1: forall x : T, Q x -> P0 x)
  (H2: forall (x : T) (l : list T),
      P x l -> Forall (pftree P Q) l -> Forall P0 l -> P0 x).

  Section Tmp.
    Context(pftree_IS : forall (t: T), pftree P Q t -> P0 t).
    Fixpoint mk_step_hyp (l : list T) (H : Forall (pftree P Q) l) : Forall P0 l :=
      match H with
      | Forall_nil _ => Forall_nil _
      | Forall_cons _ Hx HFl =>
          Forall_cons _ (pftree_IS _ Hx) (mk_step_hyp _ HFl)
      end.
  End Tmp.

  Fixpoint pftree_IS (t : T)(H : pftree P Q t) : P0 t :=
    match H with
    | pftree_leaf _ _ _ HQ => H1 _ HQ
    | pftree_step _ _ _ l Hl HFl =>
        H2 _ l Hl HFl (mk_step_hyp pftree_IS l HFl)
    end.
End __.

Lemma pftree_ind {U : Type} (P : U -> list U -> Prop) Q R :
  (forall x, Q x -> R x) ->
  (forall x l,
      P x l ->
      Forall (pftree P Q) l ->
      Forall R l ->
      R x) ->
  forall x, pftree P Q x -> R x.
Proof.
  intros H1 H2. fix self 2.
  intros x Hx. inversion Hx; subst. 1: auto. eapply H2. 1,2: eassumption.
  clear -H0 self. induction H0; eauto.
Qed.

Definition union_db {A} (db1 db2 : A -> Prop) :=
  fun f => db1 f \/ db2 f.

Definition equiv {A} (P Q : A -> Prop) :=
  forall a, P a <-> Q a.

Section WithMap.
 Context {context : map.map nat dvalue} {context_ok : map.ok context}.

 Inductive interp_dexpr (ctx : context) : dexpr -> dvalue -> Prop :=
 | IDVar x v : map.get ctx x = Some v ->
             interp_dexpr ctx (DVar x) v
 | IDBool b : interp_dexpr ctx (DBool b) (DVBool b)
 | IDInt n : interp_dexpr ctx (DInt n) (DVInt n)
 | IDNot e b : interp_dexpr ctx e (DVBool b) ->
             interp_dexpr ctx (DNot e) (DVBool (negb b))
 | IDAnd e1 e2 b1 b2 : interp_dexpr ctx e1 (DVBool b1) ->
                interp_dexpr ctx e2 (DVBool b2) ->
                interp_dexpr ctx (DAnd e1 e2) (DVBool (andb b1 b2))
 | IDPlus e1 e2 n1 n2 : interp_dexpr ctx e1 (DVInt n1) ->
                interp_dexpr ctx e2 (DVInt n2) ->
                interp_dexpr ctx (DPlus e1 e2) (DVInt (n1 + n2))
 | IDLt e1 e2 n1 n2 : interp_dexpr ctx e1 (DVInt n1) ->
                interp_dexpr ctx e2 (DVInt n2) ->
                interp_dexpr ctx (DLt e1 e2) (DVBool (Z.leb n1 n2))
 | IDEq e1 e2 v1 v2 : interp_dexpr ctx e1 v1 ->
                interp_dexpr ctx e2 v2 ->
                interp_dexpr ctx (DEq e1 e2) (DVBool (dvalue_eqb v1 v2)).

 Variant interp_clause (ctx : context) : clause -> fact -> Prop :=
   mk_IC c f : c.(clause_rel) = f.(fact_rel) ->
   Forall2 (interp_dexpr ctx) c.(clause_args) f.(fact_args) ->
   interp_clause ctx c f.

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
