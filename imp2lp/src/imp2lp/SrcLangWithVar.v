From Stdlib Require Import String ZArith List Bool Sorted Permutation.

Import ListNotations.
Open Scope list_scope.

(* Fiat2 types *)
Inductive type : Type :=
| TInt
| TBool
| TString
| TRecord : list (string * type) -> type.

Scheme Boolean Equality for type. (* creates type_beq *)

Declare Scope fiat2_scope. Local Open Scope fiat2_scope.
Notation "t1 =? t2" := (type_beq t1 t2) (at level 70) : fiat2_scope.

(* ??? Tried adding variables, with immutable ones only as aexpr and mutable ones as expr
 but where should declaration happen? cmd level -> complicate operational semantics? *)

(* Simple expressions *)
Inductive aexpr : Type :=
| AVar (x : string)
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
| ELoc (tbl : string)
| EEmptySet (l : list (string * type))
| ESetInsert (r : rexpr) (e : expr)
(* relational algebra *)
| EFilter (e : expr) (x : string) (p : list pexpr) (* Select a subset of rows from table *)
| EJoin (e1 e2 : expr) (x y : string) (p : list pexpr) (r : rexpr) (* Join two tables *)
| EProj (e : expr) (x : string) (r : rexpr) (* Generalized projection *).

Inductive cmd : Type :=
| CSkip
| CSeq (c1 c2 : cmd)
| CLetMut (e : expr) (tbl : string) (c : cmd)
| CAssign (x : string) (e : expr)
| CIf (e : aexpr) (c1 c2 : cmd).

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
                 type_wf (TRecord tl).

Inductive type_of_value : value -> type -> Prop :=
| TVInt n : type_of_value (VInt n) TInt
| TVBool b : type_of_value (VBool b) TBool
| TVString s : type_of_value (VString s) TString
| TVRecord vl tl :
  Forall2 (fun vp tp => fst vp = fst tp) vl tl ->
  Forall2 (fun vp tp => type_of_value (snd vp) (snd tp)) vl tl ->
  type_of_value (VRecord vl) (TRecord tl).

Section WithMap.
  Context {locals: map.map string value} {locals_ok: map.ok locals}.

  Definition default_value := VBool false.

  Fixpoint interp_aexpr (env : locals) (e : aexpr) : value :=
    match e with
    | AVar x => match map.get env x with
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

  Definition interp_pexpr (env : locals) (e : pexpr) : bool :=
    match e with
    | PLt e1 e2 => match interp_aexpr env e1, interp_aexpr env e2 with
                   | VInt n1, VInt n2 => Z.ltb n1 n2
                   | _, _ => false
                   end
    | PEq e1 e2 => value_eqb (interp_aexpr env e1) (interp_aexpr env e2)
    end.

  Definition interp_rexpr (env : locals) (e : rexpr) : list (string * value) :=
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

  Section WithStore.
    Context (store : locals).

    Fixpoint interp_expr (env : locals) (e : expr) : value :=
      match e with
      | ELoc x => match map.get store x with
                  | Some v => v
                  | _ => default_value
                  end
      | EEmptySet _ => VSet []
      | ESetInsert r e => match interp_expr env e with
                          | VSet s => VSet (set_insert (VRecord (interp_rexpr env r)) s)
                          | _ => default_value
                          end
      (* | EEmptyList _ => VList []
    | EListInsert r e => match interp_expr env e with
                         | VList l => VList (VRecord (interp_rexpr env r) :: l)
                         | _ => default_value
                         end *)
     (* | ELet a x e => interp_expr (map.put env x (interp_aexpr env a)) e *)
      | EFilter e x ps => match interp_expr env e with
                          | VSet s => VSet (filter
                                              (fun r => forallb (fun p => interp_pexpr (map.put env x r) p) ps)
                                              s)
                          | _ => default_value
                          end
      | EJoin e1 e2 x1 x2 ps r => match interp_expr env e1, interp_expr env e2 with
                                  | VSet s1, VSet s2 =>
                                      VSet
                                        (value_sort
                                           (flat_map
                                              (fun r1 =>
                                                 flat_map
                                                   (fun r2 =>
                                                      let env' := map.put (map.put env x1 r1) x2 r2 in
                                                      if forallb (fun p => interp_pexpr env' p) ps then [VRecord (interp_rexpr env' r)]
                                                      else []) s2) s1))
                                  | _, _ => default_value
                                  end
      | EProj e x r => match interp_expr env e with
                       | VSet s =>
                           VSet (value_sort (List.map (fun v => VRecord (interp_rexpr (map.put env x v) r)) s))
                       | _ => default_value
                       end
      end.
  End WithStore.

  Fixpoint interp_cmd (store env : locals) (c : cmd) : locals :=
    match c with
    | CSkip => store
    | CSeq c1 c2 => interp_cmd (interp_cmd store env c1) env c2
    | CLetMut e x c => interp_cmd (map.put store x (interp_expr store env e)) env c
    | CAssign x e => map.put store x (interp_expr store env e)
    | CIf e c1 c2 => match interp_aexpr env e with
                     | VBool true => interp_cmd store env c1
                     | VBool false => interp_cmd store env c2
                     | _ => store (* unreachable cases *)
                     end
    end.

  (* ??? scoping problem with CLetMut: maintain a stack of things to recover?
  Inductive cmd_step (store env : locals) :
    cmd -> stack of frames shape dep on construct ->
    locals -> locals -> cmd -> list (string * option value) ->
    Prop :=
  | SCRestore stk x v :
    cmd_step store env CSkip ((x, v) :: stk)
      (map.update store x v) env CSkip stk
  | SCNext c stk :
    cmd_step store env (CSeq CSkip c) stk
      store env c stk
  | SCSeq stk c1 c2 store' env' c1' stk' :
    cmd_step store env c1
      store' env' c1' stk' ->
    cmd_step store env (CSeq c1 c2) stk
      store' env' (CSeq c1' c2) stk'
  | SCLetMut stk e x c v :
    interp_expr store env e = v ->
    cmd_step store env (CLetMut e x c) stk
      (map.put store x v) env c ((x, map.get store x) :: stk)
  (* ??? Doesn't work e.g. CLetMut e x (CSeq c1 c2)
   CLetMut e x (CSeq (CLetMut e' x' c1) c2 *)
  | SCAssign stk e x v :
    interp_expr store env e = v ->
    cmd_step store env (CAssign x e) stk
      (map.put store x v) env CSkip stk
  | SCIfTrue stk e c1 c2 :
    interp_aexpr env e = VBool true ->
    cmd_step store env (CIf e c1 c2) stk
      store env c1 stk
  | SCIfFalse stk e c1 c2 :
    interp_aexpr env e = VBool false ->
    cmd_step store env (CIf e c1 c2) stk
      store env c2 stk.


    TAPL abstract machine CEK
*)

  Definition is_atomic_type (t : type) : Prop :=
    match t with
    | TInt | TBool | TString => True
    | _ => False
    end.

  Context {tenv : map.map string type} {env_ok : map.ok tenv}.

  Definition tenv_wf (G : tenv) :=
    forall x t, map.get G x = Some t -> type_wf t.

  Section WithGenv.
    Context (Genv : tenv).

    Inductive type_of_aexpr : aexpr -> type -> Prop :=
    | TAVar x t : map.get Genv x = Some t ->
                  is_atomic_type t ->
                  type_of_aexpr (AVar x) t
    | TABool b : type_of_aexpr (ABool b) TBool
    | TAInt n : type_of_aexpr (AInt n) TInt
    | TAString s : type_of_aexpr (AString s) TString
    | TANot e : type_of_aexpr e TBool ->
                type_of_aexpr (ANot e) TBool
    | TAAnd e1 e2 : type_of_aexpr e1 TBool ->
                    type_of_aexpr e2 TBool ->
                    type_of_aexpr (AAnd e1 e2) TBool
    | TAPlus e1 e2 : type_of_aexpr e1 TInt ->
                     type_of_aexpr e2 TInt ->
                     type_of_aexpr (APlus e1 e2) TInt
    | TAStringConcat e1 e2 : type_of_aexpr e1 TString ->
                     type_of_aexpr e2 TString ->
                     type_of_aexpr (AStringConcat e1 e2) TString
    | TAStringLength e : type_of_aexpr e TString ->
                         type_of_aexpr (AStringLength e) TInt
    | TAAccess x attr l t : map.get Genv x = Some (TRecord l) ->
                            access_record l attr = Success t ->
                            is_atomic_type t ->
                            type_of_aexpr (AAccess x attr) t.

    Inductive well_typed_pexpr : pexpr -> Prop :=
    | TPLt e1 e2 : type_of_aexpr e1 TInt ->
                   type_of_aexpr e2 TInt ->
                   well_typed_pexpr (PLt e1 e2)
    | TPEq e1 e2 t : type_of_aexpr e1 t ->
                     type_of_aexpr e2 t ->
                     well_typed_pexpr (PEq e1 e2).

    Inductive type_of_rexpr : rexpr -> type -> Prop :=
    | TRRecord el tl : type_wf (TRecord tl) ->
                       Forall2 (fun ep tp => fst ep = fst tp) (record_sort el) tl ->
                       Forall2 (fun ep tp => type_of_aexpr (snd ep) (snd tp)) (record_sort el) tl ->
                       type_of_rexpr (RRecord el) (TRecord tl).
  End WithGenv.

  Section WithGstore.
    Context (Gstore : tenv).

    Inductive type_of_expr (Genv : tenv) : expr -> type -> Prop :=
    | TELoc x t : map.get Gstore x = Some t ->
                   type_of_expr Genv (ELoc x) t
    | TEEmptySet tl : type_wf (TRecord tl) ->
                      type_of_expr Genv (EEmptySet tl) (TRecord tl)
    | TESetInsert r e t : type_of_rexpr Genv r t ->
                          type_of_expr Genv e t ->
                          type_of_expr Genv (ESetInsert r e) t
   (* ??? | TELet e1 x e2 t1 t2: type_of_aexpr Genv e1 t1 ->
                           type_of_expr (map.put Genv x t1) e2 t2 ->
                           type_of_expr Genv (ELet e1 x e2) t2 *)
    | TEFilter e x ps t : type_of_expr Genv e t ->
                          Forall (well_typed_pexpr (map.put Genv x t)) ps ->
                          type_of_expr Genv (EFilter e x ps) t
    | TEJoin e1 e2 x1 x2 ps r t1 t2 t :
      type_of_expr Genv e1 t1 ->
      type_of_expr Genv e2 t2 ->
      Forall (well_typed_pexpr (map.put (map.put Genv x1 t1) x2 t2)) ps ->
      type_of_rexpr (map.put (map.put Genv x1 t1) x2 t2) r t ->
      type_of_expr Genv (EJoin e1 e2 x1 x2 ps r) t
    | TEProj e x r t1 t2 : type_of_expr Genv e t1 ->
                           type_of_rexpr (map.put Genv x t1) r t2 ->
                           type_of_expr Genv (EProj e x r) t2.

  Import ResultMonadNotations.
  Open Scope string_scope.
  Fixpoint type_check_aexpr (Genv : tenv) (e : aexpr) : result type :=
    match e with
    | AVar x => match map.get Genv x with
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
