From Stdlib Require Import String ZArith List Bool Sorted Permutation.

Import ListNotations.
Open Scope list_scope.

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

Definition cfg : Type :=
  (* First declare all mutable variables, each annotated with its schema *)
  list (string * type) * list block.

(* Semantics *)
Require Import imp2lp.Value.
Require Import coqutil.Map.Interface coqutil.Datatypes.Result.

Inductive type_wf : type -> Prop :=
| WFTInt : type_wf TInt
| WFTBool : type_wf TBool
| WFTString : type_wf TString
| WFTRecord tl : NoDup (map fst tl) ->
                 StronglySorted (fun a b => is_true (record_entry_leb a b)) tl ->
                 Forall (fun p => type_wf (snd p)) tl ->
                 type_wf (TRecord tl)
| WFTSet t : type_wf t ->
             type_wf (TSet t).

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

  Fixpoint make_venv (xs : list string) (vs : list value) :=
    match xs, vs with
    | [], _ | _, [] => map.empty
    | x :: xs, v :: vs => map.put (make_venv xs vs) x v
    end.

  Inductive block_step (g : cfg) (store : venv) (n : nat) : venv -> option nat -> Prop :=
  | BSGoto n' args store' :
   nth_error (snd g) n = Some (BGoto (n', args)) ->
    store' = make_venv (List.map fst (fst g)) (List.map (interp_expr store) args) ->
    block_step g store n store' (Some n')
  | BSIf_true e n1 args1 bc2 store' :
    nth_error (snd g) n = Some (BIf e (n1, args1) bc2) ->
    store' = make_venv (List.map fst (fst g)) (List.map (interp_expr store) args1) ->
    interp_pexpr store map.empty e = true ->
    block_step g store n store' (Some n1)
  | BSIf_false e bc1 n2 args2 store' :
    nth_error (snd g) n = Some (BIf e bc1 (n2, args2)) ->
    store' = make_venv (List.map fst (fst g)) (List.map (interp_expr store) args2) ->
    interp_pexpr store map.empty e = false ->
    block_step g store n store' (Some n2)
  | BSRet :
    nth_error (snd g) n = Some BRet ->
    block_step g store n store None.

  Inductive block_steps (g : cfg) (store : venv) (n : nat) : venv -> option nat -> Prop :=
  | BSS_base : block_steps g store n store (Some n)
  | BSS_trans store' n' store'' m : block_steps g store n store' (Some n') ->
                block_step g store' n store'' m ->
                block_steps g store n store'' m.

  Definition cfg_impl (g : cfg) (store : venv) : Prop :=
    block_steps g map.empty 0 store None.

  Definition is_atomic_type (t : type) : Prop :=
    match t with
    | TInt | TBool | TString => True
    | _ => False
    end.

  Context {tenv : map.map string type} {env_ok : map.ok tenv}.

  Definition tenv_wf (G : tenv) :=
    forall x t, map.get G x = Some t -> type_wf t.

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
End WithMap.
