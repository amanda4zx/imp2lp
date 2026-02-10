From Stdlib Require Import String ZArith List Bool Sorted Permutation.

Import ListNotations.
Open Scope list_scope.

Ltac destruct_match_hyp :=
  lazymatch goal with
    H: context[match ?x with _ => _ end] |- _ =>
      let E := fresh "E" in
      destruct x eqn:E end.

Ltac do_injection :=
  lazymatch goal with
    H: ?c _ = ?c _ |- _ => injection H; intros; subst
  end.

Ltac clear_refl := lazymatch goal with H: ?x = ?x |- _ => clear H end.

Ltac invert_Forall2 :=
  lazymatch goal with
  | H: Forall2 _ (_ :: _) _ |- _ => inversion H; subst; clear H
  | H: Forall2 _ _ (_ :: _) |- _ => inversion H; subst; clear H
  | H: Forall2 _ nil _ |- _ => inversion H; subst; clear H
  | H: Forall2 _ _ nil |- _ => inversion H; subst; clear H
  end.

Ltac invert_Forall :=
  lazymatch goal with
  | H: Forall _ (_ :: _) |- _ => inversion H; subst; clear H
  end.

Ltac invert_pair :=
  lazymatch goal with
    H: (_, _) = (_, _) |- _ => inversion H; subst; clear H
  end.

Ltac invert_cons :=
  lazymatch goal with H: _ :: _ = _ :: _ |- _ => inversion H; subst end.

Ltac destruct_exists :=
  lazymatch goal with
    H: exists _, _ |- _ => destruct H end.

Ltac rewrite_l_to_r :=
  lazymatch goal with
  | H: ?x = _, H': context[?x] |- _ => rewrite H in H'
  | H: ?x = _ |- context[?x] => rewrite H
  end.

Ltac rewrite_asm :=
  lazymatch goal with
    H: ?x = _ |- context[?x] => rewrite H
  end.

Ltac apply_in_nil :=
  lazymatch goal with
    H: In _ nil |- _ => apply in_nil in H
  end.

Ltac invert_NoDup :=
  lazymatch goal with H: NoDup (_ :: _) |- _ => inversion H; subst end.

(* Fiat2 types *)
Inductive type : Type :=
| TInt
| TBool
| TString
| TRecord : list (string * type) -> type
| TSet : type -> type.

Scheme Boolean Equality for type. (* creates type_beq *)

Declare Scope fiat2_scope. Local Open Scope fiat2_scope.
Notation "t1 =? t2" := (type_beq t1 t2) (at level 70) : fiat2_scope.

(* Simple expressions *)
Inductive aexpr : Type :=
| AVar (x : string)
| ALoc (x : string)
| ABool (b : bool)
| AInt (n : Z)
| AString (s : string)
| ALet (a1 : aexpr) (x : string) (a2 : aexpr)
| ANot (a : aexpr)
| AAnd (a1 a2 : aexpr)
| APlus (a1 a2 : aexpr)
| AStringConcat (a1 a2 : aexpr)
| AStringLength (a : aexpr)
| AAccess (x attr : string).

Inductive pexpr : Type :=
| PLt (a1 a2 : aexpr)
| PEq (a1 a2 : aexpr).

(* Record construction *)
Variant rexpr : Type :=
  RRecord (l : list (string * aexpr)).

(* Expressions *)
Inductive expr : Type :=
| EAtom (a : aexpr)
| ELoc (x : string)
| EEmptySet (l : list (string * type))
| ESetInsert (r : rexpr) (e : expr)
(* relational algebra *)
| EFilter (e : expr) (x : string) (p : list pexpr) (* Select a subset of rows from table *)
| EJoin (e1 e2 : expr) (x y : string) (p : list pexpr) (r : rexpr) (* Join two tables *)
| EProj (e : expr) (x : string) (r : rexpr) (* Generalized projection *).

Definition block_call : Type := nat * list expr.

Inductive block :=
| BGoto (bc : block_call)
| BIf (e : pexpr) (bc1 bc2 : block_call)
| BRet.

Record cfg := { sig : list (string * type); entry : block_call; blks : list block }.
  (* First declare all mutable variables, each annotated with its schema *)

(* Semantics *)
Require Import imp2lp.Value.
Require Import coqutil.Map.Interface coqutil.Datatypes.Result.
Require Import coqutil.Tactics.case_match.

Ltac destruct_String_eqb x y :=
  let E := fresh "E" in
  destruct (String.eqb x y) eqn:E; rewrite ?String.eqb_eq, ?String.eqb_neq in *; subst.

Ltac rewrite_map_get_put_hyp :=
  multimatch goal with
  | H: context[map.get (map.put _ ?x _) ?x] |- _ =>
      rewrite map.get_put_same in H
  | H: context[map.get (map.put _ _ _) _] |- _ =>
      rewrite map.get_put_diff in H; try now (simpl in *; intuition auto)
  end.

Ltac rewrite_map_get_put_goal :=
  multimatch goal with
  | |- context[map.get (map.put _ ?x _) ?x] =>
      rewrite map.get_put_same
  | |- context[map.get (map.put _ _ _) _] =>
      rewrite map.get_put_diff; try now (simpl in *; intuition auto)
  end.

Ltac apply_Forall_In :=
  lazymatch goal with
    H: Forall _ ?l, _: In _ ?l |- _ =>
      eapply List.Forall_In in H; eauto end.

Definition is_atomic_type (t : type) : Prop :=
  match t with
  | TInt | TBool | TString => True
  | _ => False
  end.

Definition is_atomic_type_com (t : type) : bool :=
  match t with
  | TInt | TBool | TString => true
  | _ => false
  end.

Inductive type_wf : type -> Prop :=
| WFTInt : type_wf TInt
| WFTBool : type_wf TBool
| WFTString : type_wf TString
| WFTRecord tl : NoDup (map fst tl) ->
                 StronglySorted (fun a b => is_true (record_entry_leb a b)) tl ->
                 Forall (fun p => type_wf (snd p) /\ is_atomic_type (snd p)) tl ->
                 type_wf (TRecord tl)
| WFTSet tl : type_wf (TRecord tl) ->
             type_wf (TSet (TRecord tl)).

Inductive type_of_value : value -> type -> Prop :=
| TVInt n : type_of_value (VInt n) TInt
| TVBool b : type_of_value (VBool b) TBool
| TVString s : type_of_value (VString s) TString
| TVRecord vl tl :
  Forall2 (fun vp tp => fst vp = fst tp) vl tl ->
  Forall2 (fun vp tp => type_of_value (snd vp) (snd tp)) vl tl ->
  type_of_value (VRecord vl) (TRecord tl)
| TVSet l t : Forall (fun v => type_of_value v t) l ->
              type_of_value (VSet l) (TSet t).

Section WithMap.
  Context {venv: map.map string value} {venv_ok: map.ok venv}.

  Definition default_value := VBool false.

  Section WithStore.
    Context (store : venv).

    Fixpoint interp_aexpr (env : venv) (e : aexpr) : value :=
      match e with
      | AVar x => match map.get env x with
                  | Some v => v
                  | _ => default_value
                  end
      | ALoc x => match map.get store x with
                  | Some v => v
                  | _ => default_value
                  end
      | ABool b => VBool b
      | AInt n => VInt n
      | AString s => VString s
      | ALet e1 x e2 => interp_aexpr (map.put env x (interp_aexpr env e1)) e2
      | ANot e => match interp_aexpr env e with
                  | VBool b => VBool (negb b)
                  | _ => default_value
                  end
      | AAnd e1 e2 => match interp_aexpr env e1, interp_aexpr env e2 with
                      | VBool b1, VBool b2 => VBool (andb b1 b2)
                      | _, _ => default_value
                      end
      | APlus e1 e2 => match interp_aexpr env e1, interp_aexpr env e2 with
                       | VInt n1, VInt n2 => VInt (n1 + n2)
                       | _, _ => default_value
                       end
      | AStringConcat e1 e2 => match interp_aexpr env e1, interp_aexpr env e2 with
                               | VString s1, VString s2 => VString (s1 ++ s2)
                               | _, _ => default_value
                               end
      | AStringLength e => match interp_aexpr env e with
                           | VString s => VInt (Z.of_nat (String.length s))
                           | _ => default_value
                           end
      | AAccess x attr => match map.get env x with
                          | Some (VRecord r) => match access_record r attr with
                                                | Success v => v
                                                | _ => default_value
                                                end
                          | _ => default_value
                          end
      end.

    Definition interp_pexpr (env : venv) (e : pexpr) : bool :=
      match e with
      | PLt e1 e2 => match interp_aexpr env e1, interp_aexpr env e2 with
                     | VInt n1, VInt n2 => Z.ltb n1 n2
                     | _, _ => false
                     end
      | PEq e1 e2 => value_eqb (interp_aexpr env e1) (interp_aexpr env e2)
      end.

    Definition interp_rexpr (env : venv) (e : rexpr) : list (string * value) :=
      match e with
      | RRecord l => List.map (fun '(s, a) => (s, interp_aexpr env a)) (record_sort l)
      end.

    Fixpoint set_insert (v : value) (l : list value) :=
      match l with
      | nil => v :: nil
      | v' :: l' => if value_ltb v v' then v :: v' :: l'
                    else if value_eqb v v' then l
                         else v' :: set_insert v l'
      end.

    Fixpoint interp_expr (e : expr) : value :=
      match e with
      | EAtom a => interp_aexpr map.empty a
      | ELoc x => match map.get store x with
                  | Some v => v
                  | _ => default_value
                  end
      | EEmptySet _ => VSet []
      | ESetInsert r e => match interp_expr e with
                          | VSet s => VSet (set_insert (VRecord (interp_rexpr map.empty r)) s)
                          | _ => default_value
                          end
      | EFilter e x ps => match interp_expr e with
                          | VSet s => VSet (filter
                                              (fun r => forallb (fun p => interp_pexpr (map.put map.empty x r) p) ps)
                                              s)
                          | _ => default_value
                          end
      | EJoin e1 e2 x1 x2 ps r =>
          match interp_expr e1, interp_expr e2 with
          | VSet s1, VSet s2 =>
              VSet
                (value_sort
                   (flat_map
                      (fun r1 =>
                         flat_map
                           (fun r2 =>
                              let env' := map.put (map.put map.empty x1 r1) x2 r2 in
                              if forallb (fun p => interp_pexpr env' p) ps
                              then [VRecord (interp_rexpr env' r)]
                              else [])
                           s2)
                      s1))
          | _, _ => default_value
          end
      | EProj e x r => match interp_expr e with
                       | VSet s =>
                           VSet (value_sort (List.map (fun v => VRecord (interp_rexpr (map.put map.empty x v) r)) s))
                       | _ => default_value
                       end
      end.
  End WithStore.

  Fixpoint mk_venv (xs : list string) (vs : list value) :=
    match xs, vs with
    | [], _ | _, [] => map.empty
    | x :: xs, v :: vs => map.put (mk_venv xs vs) x v
    end.

  (* ??? remove
  Inductive block_step (sig : list (string * type)) (blks : list block) (store : venv) (n : nat) : venv -> option nat -> Prop :=
  | BSGoto n' args store' :
    nth_error blks n = Some (BGoto (n', args)) ->
    store' = mk_venv (List.map fst sig) (List.map (interp_expr store) args) ->
    block_step sig blks store n store' (Some n')
  | BSIf_true e n1 args1 bc2 store' :
    nth_error blks n = Some (BIf e (n1, args1) bc2) ->
    store' = mk_venv (List.map fst sig) (List.map (interp_expr store) args1) ->
    interp_pexpr store map.empty e = true ->
    block_step sig blks store n store' (Some n1)
  | BSIf_false e bc1 n2 args2 store' :
    nth_error blks n = Some (BIf e bc1 (n2, args2)) ->
    store' = mk_venv (List.map fst sig) (List.map (interp_expr store) args2) ->
    interp_pexpr store map.empty e = false ->
    block_step sig blks store n store' (Some n2)
  | BSRet :
    nth_error blks n = Some BRet ->
    block_step sig blks store n store None.
   *)

(* ??? remove
  Inductive block_steps (sig : list (string * type)) (blks : list block) (store : venv) (n : nat) : venv -> option nat -> Prop :=
  | BSS_base : block_steps sig blks store n store (Some n)
  | BSS_trans store' n' blk' store'' m :
    block_steps sig blks store n store' (Some n') ->
    nth_error blks n' = Some blk' ->
    block_step sig store' blk' store'' m ->
    block_steps sig blks store n store'' m.

  Definition cfg_impl (g : cfg) (store : venv) : Prop :=
    let '(n, args) := g.(entry) in
    let store0 := mk_venv (List.map fst g.(sig)) (List.map (interp_expr map.empty) args) in
    block_steps g.(sig) g.(blks) store0 n store None.
 *)

  Inductive block_step (sig : list (string * type)) (store : venv) : block -> venv -> option nat -> Prop :=
  | BSGoto n' args store' :
    store' = mk_venv (List.map fst sig) (List.map (interp_expr store) args) ->
    block_step sig store (BGoto (n', args)) store' (Some n')
  | BSIf_true e n1 args1 bc2 store' :
    store' = mk_venv (List.map fst sig) (List.map (interp_expr store) args1) ->
    interp_pexpr store map.empty e = true ->
    block_step sig store (BIf e (n1, args1) bc2) store' (Some n1)
  | BSIf_false e bc1 n2 args2 store' :
    store' = mk_venv (List.map fst sig) (List.map (interp_expr store) args2) ->
    interp_pexpr store map.empty e = false ->
    block_step sig store (BIf e bc1 (n2, args2)) store' (Some n2)
  | BSRet :
    block_step sig store BRet store None.

  Inductive cfg_steps (g : cfg) : venv -> option nat -> Prop :=
  | CS_base n args store0 :
    g.(entry) = (n, args) ->
    store0 = mk_venv (List.map fst g.(sig)) (List.map (interp_expr map.empty) args) ->
    cfg_steps g store0 (Some n)
  | CS_next store store' n blk m :
    cfg_steps g store (Some n) ->
    nth_error g.(blks) n = Some blk ->
    block_step g.(sig) store blk store' m ->
    cfg_steps g store' m.

  Context {tenv : map.map string type} {env_ok : map.ok tenv}.

  Fixpoint mk_tenv (ps : list (string * type)) : tenv :=
    match ps with
    | [] => map.empty
    | (x, t) :: ps => map.put (mk_tenv ps) x t
    end.

  Definition tenv_wf (G : tenv) :=
    forall x t, map.get G x = Some t ->
                type_wf t.

  Section WithGstore.
    Context (Gstore : tenv).

    Inductive type_of_aexpr (Genv : tenv) : aexpr -> type -> Prop :=
    | TAVar x t : map.get Genv x = Some t ->
                  is_atomic_type t ->
                  type_of_aexpr Genv (AVar x) t
    | TALoc x t : map.get Gstore x = Some t ->
                  is_atomic_type t ->
                  type_of_aexpr Genv (ALoc x) t
    | TABool b : type_of_aexpr Genv (ABool b) TBool
    | TAInt n : type_of_aexpr Genv (AInt n) TInt
    | TAString s : type_of_aexpr Genv (AString s) TString
    | TALet e1 x e2 t1 t2 : type_of_aexpr Genv e1 t1 ->
                            type_of_aexpr (map.put Genv x t1) e2 t2 ->
                            type_of_aexpr Genv (ALet e1 x e2) t2
    | TANot e : type_of_aexpr Genv e TBool ->
                type_of_aexpr Genv (ANot e) TBool
    | TAAnd e1 e2 : type_of_aexpr Genv e1 TBool ->
                    type_of_aexpr Genv e2 TBool ->
                    type_of_aexpr Genv (AAnd e1 e2) TBool
    | TAPlus e1 e2 : type_of_aexpr Genv e1 TInt ->
                     type_of_aexpr Genv e2 TInt ->
                     type_of_aexpr Genv (APlus e1 e2) TInt
    | TAStringConcat e1 e2 : type_of_aexpr Genv e1 TString ->
                             type_of_aexpr Genv e2 TString ->
                             type_of_aexpr Genv (AStringConcat e1 e2) TString
    | TAStringLength e : type_of_aexpr Genv e TString ->
                         type_of_aexpr Genv (AStringLength e) TInt
    | TAAccess x attr l t : map.get Genv x = Some (TRecord l) ->
                            access_record l attr = Success t ->
                            is_atomic_type t ->
                            type_of_aexpr Genv (AAccess x attr) t.

    Inductive well_typed_pexpr (Genv : tenv) : pexpr -> Prop :=
    | TPLt e1 e2 : type_of_aexpr Genv e1 TInt ->
                   type_of_aexpr Genv e2 TInt ->
                   well_typed_pexpr Genv (PLt e1 e2)
    | TPEq e1 e2 t : type_of_aexpr Genv e1 t ->
                     type_of_aexpr Genv e2 t ->
                     well_typed_pexpr Genv (PEq e1 e2).

    Inductive type_of_rexpr (Genv : tenv) : rexpr -> type -> Prop :=
    | TRRecord el tl : type_wf (TRecord tl) ->
                       Forall2 (fun ep tp => fst ep = fst tp) (record_sort el) tl ->
                       Forall2 (fun ep tp => type_of_aexpr Genv (snd ep) (snd tp)) (record_sort el) tl ->
                       type_of_rexpr Genv (RRecord el) (TRecord tl).

    Inductive type_of_expr : expr -> type -> Prop :=
    | TEAtom a t : type_of_aexpr map.empty a t ->
                 type_of_expr (EAtom a) t
    | TELoc x t : map.get Gstore x = Some t ->
                   type_of_expr (ELoc x) t
    | TEEmptySet tl : type_wf (TRecord tl) ->
                      type_of_expr (EEmptySet tl) (TSet (TRecord tl))
    | TESetInsert r e t : type_of_rexpr map.empty r t ->
                          type_of_expr e (TSet t) ->
                          type_of_expr (ESetInsert r e) (TSet t)
    | TEFilter e x ps t : type_of_expr e (TSet t) ->
                          Forall (well_typed_pexpr (map.put map.empty x t)) ps ->
                          type_of_expr (EFilter e x ps) (TSet t)
    | TEJoin e1 e2 x1 x2 ps r t1 t2 t :
      type_of_expr e1 (TSet t1) ->
      type_of_expr e2 (TSet t2) ->
      Forall (well_typed_pexpr (map.put (map.put map.empty x1 t1) x2 t2)) ps ->
      type_of_rexpr (map.put (map.put map.empty x1 t1) x2 t2) r t ->
      type_of_expr (EJoin e1 e2 x1 x2 ps r) (TSet t)
    | TEProj e x r t1 t2 : type_of_expr e (TSet t1) ->
                           type_of_rexpr (map.put map.empty x t1) r t2 ->
                           type_of_expr (EProj e x r) (TSet t2).

    Import ResultMonadNotations.
    Open Scope string_scope.
    Fixpoint type_check_aexpr (Genv : tenv) (e : aexpr) : result type :=
      match e with
      | AVar x => match map.get Genv x with
                  | Some t => Success t
                  | _ => error:(x "not in scope")
                  end
      | ALoc x => match map.get Gstore x with
                  | Some t => Success t
                  | _ => error:(x "not in scope")
                  end
      | ABool _ => Success TBool
      | AInt _ => Success TInt
      | AString _ => Success TString
      | ALet e1 x e2 => match type_check_aexpr Genv e1 with
                        | Success t =>
                            type_check_aexpr (map.put Genv x t) e2
                        | err => err
                        end
      | ANot e => t <- type_check_aexpr Genv e;;
                  if type_beq t TBool
                  then Success TBool
                  else error:(e "has type" t "but expected a Boolean")
      | AAnd e1 e2 => t1 <- type_check_aexpr Genv e1;;
                      if type_beq t1 TBool
                      then t2 <- type_check_aexpr Genv e2;;
                           if type_beq t2 TBool
                           then Success TBool
                           else error:(e2 "has type" t2 "but expected a Boolean")
                      else error:(e1 "has type" t1 "but expected a Boolean")
      | APlus e1 e2 => t1 <- type_check_aexpr Genv e1;;
                       if type_beq t1 TInt
                       then t2 <- type_check_aexpr Genv e2;;
                            if type_beq t2 TInt
                            then Success TInt
                            else error:(e2 "has type" t2 "but expected an integer")
                       else error:(e1 "has type" t1 "but expected an integer")
      | AStringLength e => t <- type_check_aexpr Genv e;;
                           if type_beq t TString
                           then Success TInt
                           else error:(e "has type" t "but expected a string")
      | AStringConcat e1 e2 => t1 <- type_check_aexpr Genv e1;;
                               if type_beq t1 TString
                               then t2 <- type_check_aexpr Genv e2;;
                                    if type_beq t2 TString
                                    then Success TString
                                    else error:(e2 "has type" t2 "but expected a string")
                               else error:(e1 "has type" t1 "but expected a string")
      | AAccess x attr => match map.get Genv x with
                          | Some (TRecord l) => access_record l x
                          | _ => error:("Variable" x "does not have a record type")
                          end
      end.
  End WithGstore.

  (* ??? remove
  Inductive well_typed_block (Gstore : tenv) (sig : list (string * type)) (blks : list block) (blk_id : nat) : Prop :=
  | WTBGoto n es :
    nth_error blks blk_id = Some (BGoto (n, es)) ->
    n < List.length blks ->
    Forall2 (fun e t => type_of_expr Gstore e t) es (List.map snd sig) ->
    well_typed_block Gstore sig blks blk_id
  | WTBIf p n1 es1 n2 es2 :
    nth_error blks blk_id = Some (BIf p (n1, es1) (n2, es2)) ->
    n1 < List.length blks ->
    n2 < List.length blks ->
    well_typed_pexpr Gstore map.empty p ->
    Forall2 (fun e t => type_of_expr Gstore e t) es1 (List.map snd sig) ->
    Forall2 (fun e t => type_of_expr Gstore e t) es2 (List.map snd sig) ->
    well_typed_block Gstore sig blks blk_id
  | WTBRet :
    nth_error blks blk_id = Some BRet ->
    well_typed_block Gstore sig blks blk_id.
*)

  Inductive well_typed_block (sig : list (string * type)) (num_blks : nat) : block -> Prop :=
  | WTBGoto n es Gstore :
    n < num_blks ->
    Gstore = mk_tenv sig ->
    Forall2 (fun e t => type_of_expr Gstore e t) es (List.map snd sig) ->
    well_typed_block sig num_blks (BGoto (n, es))
  | WTBIf p n1 es1 n2 es2 Gstore :
    n1 < num_blks ->
    n2 < num_blks ->
    Gstore = mk_tenv sig ->
    well_typed_pexpr Gstore map.empty p ->
    Forall2 (fun e t => type_of_expr Gstore e t) es1 (List.map snd sig) ->
    Forall2 (fun e t => type_of_expr Gstore e t) es2 (List.map snd sig) ->
    well_typed_block sig num_blks (BIf p (n1, es1) (n2, es2))
  | WTBRet :
    well_typed_block sig num_blks BRet.

  (* ??? remove
  Definition is_mut_ty (t : type) : Prop :=
    (* Restrict mutable variable types to sets of records of atomic types or atomic types *)
    match t with
    | TSet (TRecord tl) => Forall (fun '(_, t) => is_atomic_type t) tl
    | _ => is_atomic_type t
    end. *)

  Definition well_typed_cfg (g : cfg) : Prop :=
    let '(n, args) := g.(entry) in
    let num_blks := List.length g.(blks) in
    n < num_blks /\
      NoDup (List.map fst g.(sig)) /\
      Forall2 (fun e t => type_of_expr map.empty e t) args (List.map snd g.(sig)) /\
      Forall (well_typed_block g.(sig) num_blks) g.(blks).

  Definition venv_wf (Genv : tenv) (env : venv) : Prop :=
    forall x t, map.get Genv x = Some t ->
                match map.get env x with
                | Some v => type_of_value v t
                | None => False
                end.

  Lemma Forall2_access_record : forall A B vl tl attr t (P : A -> B -> Prop),
      Forall2 (fun vp tp => fst vp = fst tp) vl tl ->
      Forall2 (fun vp tp => P (snd vp) (snd tp)) vl tl ->
      access_record tl attr = Success t ->
      match access_record vl attr with
      | Success v => P v t
      | _ => False
      end.
  Proof.
    induction 1; cbn; intros; try discriminate.
    do 2 destruct_match_hyp;
    invert_Forall2; case_match; cbn in *; subst.
    1:{ rewrite String.eqb_eq in *.
        do_injection. rewrite String.eqb_refl.
        assumption. }
    1:{ rewrite_asm. apply IHForall2 in H8; auto. }
  Qed.

  Lemma tenv_wf_step : forall G t, tenv_wf G -> type_wf t -> forall x, tenv_wf (map.put G x t).
  Proof.
    unfold tenv_wf; intros. destruct (String.eqb x x0) eqn:E.
    - rewrite String.eqb_eq in *; subst. rewrite map.get_put_same in *.
      injection H1; intro; subst; auto.
    - rewrite String.eqb_neq in *. rewrite map.get_put_diff in *; eauto.
  Qed.

  Lemma venv_wf_step : forall G E,
      venv_wf G E ->
      forall x t v,
        type_of_value v t ->
        venv_wf (map.put G x t) (map.put E x v).
  Proof.
    unfold venv_wf; intros.
    destruct (String.eqb x0 x) eqn:E_x.
    - rewrite String.eqb_eq in E_x. rewrite E_x in *.
      rewrite map.get_put_same. rewrite map.get_put_same in H1. congruence.
    - rewrite String.eqb_neq in E_x. rewrite map.get_put_diff; auto.
      rewrite map.get_put_diff in H1; auto. apply H. auto.
  Qed.

  Lemma tenv_wf_empty : tenv_wf map.empty.
  Proof.
    unfold tenv_wf; intros. rewrite map.get_empty in H; congruence.
  Qed.

  Lemma venv_wf_empty : forall (l : venv), venv_wf map.empty l.
  Proof.
    unfold venv_wf; intros. rewrite map.get_empty in *; congruence.
  Qed.

  Lemma type_of_aexpr__type_wf : forall Gstore Genv a t,
      type_of_aexpr Gstore Genv a t ->
      tenv_wf Gstore -> tenv_wf Genv ->
      type_wf t.
  Proof.
    induction 1; try now constructor.
    all: try (intros; destruct t; cbn in *; intuition idtac; constructor).
    intros. apply IHtype_of_aexpr2; eauto using tenv_wf_step.
  Qed.

  Lemma type_of_expr__type_wf : forall Gstore e t,
      type_of_expr Gstore e t ->
      tenv_wf Gstore ->
      type_wf t.
  Proof.
    induction 1; eauto using type_of_aexpr__type_wf, tenv_wf_empty.
    1: constructor; auto.
    all: lazymatch goal with
           H: type_of_rexpr _ _ _ _ |- _ =>
             inversion H; subst
         end; constructor; auto.
  Qed.

  Ltac apply_aexpr_type_sound_IH :=
    lazymatch goal with
      IH: _ -> _ -> _ -> ?x -> type_of_value _ _, H: ?x |- _ =>
        let H' := fresh "H'" in
        apply IH in H as H'; clear IH; auto; inversion H'; subst
    end.

  Ltac apply_venv_wf :=
    lazymatch goal with
      H: map.get ?G _ = _, H': venv_wf ?G _ |- _ =>
        apply H' in H end.

  Ltac aexpr_type_sound_IH :=
    lazymatch goal with
    | IH: context[type_of_value (interp_aexpr _ _ ?e) _] |-
        type_of_value (interp_aexpr _ _ ?e) _ =>
        eapply IH
    | IH: context[venv_wf ?Genv _ -> type_of_value (interp_aexpr _ _ ?e) _],
        H: venv_wf ?Genv _ |- _ =>
        let H' := fresh "H" in
          eapply IH in H as H'; eauto; inversion H'; subst; clear IH
    end.

  Lemma aexpr_type_sound : forall Gstore Genv e t,
      type_of_aexpr Gstore Genv e t ->
      tenv_wf Gstore -> tenv_wf Genv ->
      forall store env,
      venv_wf Gstore store ->
      venv_wf Genv env ->
      type_of_value (interp_aexpr store env e) t.
  Proof.
    induction 1; intros; cbn; try constructor.
    1,2: apply_venv_wf; case_match; intuition fail.
    1:{ aexpr_type_sound_IH; eauto using tenv_wf_step, venv_wf_step.
        apply tenv_wf_step; eauto using type_of_aexpr__type_wf. }
    all: repeat aexpr_type_sound_IH; try constructor.
    1:{ lazymatch goal with
        H: venv_wf ?Genv _, H': map.get ?Genv _ = _ |- _ =>
          apply H in H'
      end. case_match; intuition idtac.
        inversion H; subst.
        lazymatch goal with
          H: Forall2 (fun _ _ => type_of_value _ _) _ _ |- _ =>
            eapply Forall2_access_record in H
        end; eauto.
        case_match; intuition fail. }
  Qed.

  Lemma set_insert_incl : forall (l : list value) v p,
      In p (set_insert v l) -> p = v \/ In p l.
  Proof.
    induction l; cbn; intros; intuition auto.
    1: subst; auto.
    repeat destruct_match_hyp;
      inversion H; subst; auto.
    apply IHl in H0; intuition idtac.
  Qed.

  Ltac invert_type_of_value :=
    lazymatch goal with
      H: type_of_value _ _ |- _ =>
        inversion H; subst
    end.

  Lemma Forall2_map_l : forall A B C P (f : A -> B) l (l' : list C),
      Forall2 (fun x y => P (f x) y) l l' -> Forall2 P (map f l) l'.
  Proof.
    induction 1; cbn; auto.
  Qed.

  Lemma rexpr_type_sound : forall Gstore Genv e t store env,
      type_of_rexpr Gstore Genv e t ->
      tenv_wf Gstore -> tenv_wf Genv ->
      venv_wf Gstore store -> venv_wf Genv env ->
      type_of_value (VRecord (interp_rexpr store env e)) t.
  Proof.
    destruct 1; cbn; intros.
    remember (record_sort el) as l.
    constructor.
    1:{ eapply Forall2_map_l.
        clear Heql H.
        induction H0; constructor; invert_Forall2; auto.
        destruct x; cbn; auto. }
    1:{ eapply Forall2_map_l.
        clear Heql H.
        induction H0; constructor; invert_Forall2; auto.
        destruct x; cbn in *; auto.
        eapply aexpr_type_sound; eauto. }
  Qed.

  Ltac apply_type_of_expr__type_wf :=
    lazymatch goal with
      H: type_of_expr _ _ (_ ?t) |- type_wf ?t =>
        apply type_of_expr__type_wf in H; auto;
        inversion H; subst
    end.

  Ltac prove_tenv_wf :=
    repeat apply tenv_wf_step;
    auto using tenv_wf_empty;
    apply_type_of_expr__type_wf; trivial.

  Ltac prove_venv_wf :=
    repeat apply venv_wf_step;
    auto using venv_wf_empty;
    repeat apply_Forall_In.

  Ltac apply_type_sound_IH :=
    lazymatch goal with
      IH: context[type_of_value (interp_expr _ ?e) _],
        H: venv_wf _ _ |-
        context[interp_expr _ ?e] =>
        let H' := fresh "H'" in
        apply IH in H as H'; auto;
        inversion H'; subst
    end.

  Theorem type_sound : forall Gstore e t store,
      type_of_expr Gstore e t ->
      tenv_wf Gstore ->
      venv_wf Gstore store ->
      type_of_value (interp_expr store e) t.
  Proof.
    induction 1; cbn; intros.
    1:{ eapply aexpr_type_sound; eauto using tenv_wf_empty, venv_wf_empty. }
    1:{ apply_venv_wf. case_match; intuition fail. }
    1:{ constructor; auto. }
    1:{ apply_type_sound_IH. constructor.
        rewrite Forall_forall; intros ? H_in.
        apply set_insert_incl in H_in; intuition subst.
        2: apply_Forall_In.
        eapply rexpr_type_sound; eauto using tenv_wf_step, tenv_wf_empty, venv_wf_empty. }
    1:{ apply_type_sound_IH. constructor.
        eapply incl_Forall; try eassumption.
        apply incl_filter. }
    1:{ repeat apply_type_sound_IH. constructor.
        erewrite <- Permuted_value_sort.
        rewrite Forall_flat_map.
        rewrite Forall_forall; intros.
        rewrite Forall_flat_map.
        rewrite Forall_forall; intros.
        case_match; constructor; auto.
        eapply rexpr_type_sound; eauto.
        1: prove_tenv_wf.
        1: prove_venv_wf. }
    1:{ apply_type_sound_IH. constructor.
        erewrite <- Permuted_value_sort.
        rewrite Forall_map.
        rewrite Forall_forall; intros.
        eapply rexpr_type_sound; eauto.
        1: prove_tenv_wf.
        1: prove_venv_wf. }
  Qed.

  Lemma get_mk_tenv : forall l x t,
      map.get (mk_tenv l) x = Some t -> In (x, t) l.
  Proof.
    induction l; cbn; intros.
    1: rewrite map.get_empty in *; discriminate.
    1:{ destruct_match_hyp; subst.
        destruct_String_eqb s x;
          rewrite_map_get_put_hyp.
        do_injection. intuition fail. }
  Qed.

  Lemma Forall2_get_mk_venv : forall A B P (l : list A) (l' : list (string * B)) f x y,
      Forall2 P l (List.map snd l') ->
      NoDup (List.map fst l') ->
      In (x, y) l' ->
      exists z, map.get (mk_venv (List.map fst l') (List.map f l)) x = Some (f z) /\ P z y.
  Proof.
    intros * H. remember (List.map snd l') as sl'.
    generalize dependent l'.
    induction H; intros.
    1:{ destruct l'; try discriminate.
        apply_in_nil. intuition fail. }
    1:{ destruct l'; try discriminate.
        1:{ invert_Forall2.
            repeat (destruct l'0; try discriminate; []).
            cbn in *.
            intuition idtac; subst; cbn in *.
            invert_cons. rewrite_map_get_put_goal.
            eexists; eauto. }
        1:{ invert_Forall2.
            destruct l'0; try discriminate; cbn in *.
            invert_cons. invert_NoDup.
            intuition idtac; subst; cbn in *.
            1:{ rewrite_map_get_put_goal.
                eexists; eauto. }
            1:{ destruct p; cbn in *.
                rewrite_map_get_put_goal.
                intro contra; subst.
                lazymatch goal with
                  H: In _ _ |- _ =>
                    apply in_map with (f := fst) in H
                end.
                intuition fail. } } }
  Qed.

  Lemma tenv_wf_mk_tenv : forall l,
      Forall type_wf (List.map snd l) ->
      tenv_wf (mk_tenv l).
  Proof.
    unfold tenv_wf; intros * ? * H.
    apply get_mk_tenv in H.
    apply in_map with (f := snd) in H.
    apply_Forall_In.
  Qed.

  Ltac rewrite_get_mk_venv :=
    unfold venv_wf; intros;
    lazymatch goal with
      H: map.get (mk_tenv _) _ = _ |- _ =>
        apply get_mk_tenv in H
    end;
    lazymatch goal with
      H: Forall2 _ ?es _ |- context[?es] =>
        eapply Forall2_get_mk_venv in H
    end; eauto;
    destruct_exists; intuition idtac;
    lazymatch goal with
      H: map.get _ _ = _ |- _ =>
        rewrite H
    end.

  Lemma block_step_preserve_ty : forall num_blks sig store store' m blk,
      well_typed_block sig num_blks blk ->
      venv_wf (mk_tenv sig) store ->
      block_step sig store blk store' m ->
      NoDup (List.map fst sig) ->
      Forall type_wf (List.map snd sig) ->
      venv_wf (mk_tenv sig) store'.
  Proof.
    induction 1; intros.
    all: lazymatch goal with
           H: context[block_step] |- _ =>
             inversion H; subst; clear H
         end; try assumption;
      rewrite_get_mk_venv;
      eapply type_sound; eauto using tenv_wf_mk_tenv.
    Qed.

  Lemma Forall2_In_r : forall A B (P : A -> B -> Prop) l l' x',
      Forall2 P l l' -> In x' l' ->
      exists x, In x l /\ P x x'.
  Proof.
    induction 1; cbn; intuition idtac; subst.
    1: eexists; eauto.
    destruct_exists.
    exists x0; intuition fail.
  Qed.

  Theorem cfg_type_sound : forall g store m,
      well_typed_cfg g ->
      cfg_steps g store m ->
      venv_wf (mk_tenv g.(sig)) store.
  Proof.
    unfold well_typed_cfg; intros.
    destruct g; cbn in *.
    repeat destruct_match_hyp; subst.
    induction H0; cbn in *; intuition idtac.
    1:{ invert_pair.
        rewrite_get_mk_venv.
        eapply type_sound; eauto using tenv_wf_mk_tenv, tenv_wf_empty, venv_wf_empty. }
    1:{ lazymatch goal with
        H: context[block_step] |- _ =>
          eapply block_step_preserve_ty in H
      end; eauto.
        1:{ lazymatch goal with
            H: nth_error _ _ = _ |- _ =>
              apply nth_error_In in H
          end. apply_Forall_In. }
        1:{ rewrite Forall_forall; intros.
            lazymatch goal with
              H: Forall2 _ _ ?l, _: In _ ?l |- _ =>
                eapply Forall2_In_r in H
            end; eauto.
            destruct_exists. intuition idtac.
            eapply type_of_expr__type_wf; eauto using tenv_wf_empty. } }
  Qed.
End WithMap.
