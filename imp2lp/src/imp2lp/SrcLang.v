From Stdlib Require Import String ZArith List Bool Sorted.

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

(* Simple expressions *)
Inductive aexpr : Type :=
| ABool (b : bool)
| AInt (n : Z)
| AString (s : string)
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
| EEmptySet (l : list (string * type))
| ESetInsert (r : rexpr) (e : expr)
(* relational algebra *)
| EFilter (e : expr) (x : string) (p : list pexpr) (* Select a subset of rows from table *)
| EJoin (e1 e2 : expr) (x y : string) (p : list pexpr) (r : rexpr) (* Join two tables *)
| EProj (e : expr) (x : string) (r : rexpr) (* Generalized projection *).

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

  Section WithEnv.
    Context (env : locals).

    Definition default_value := VBool false.

    Fixpoint interp_aexpr (e : aexpr) : value :=
      match e with
      | ABool b => VBool b
      | AInt n => VInt n
      | AString s => VString s
      | ANot e => match interp_aexpr e with
                  | VBool b => VBool (negb b)
                  | _ => default_value
                  end
      | AAnd e1 e2 => match interp_aexpr e1, interp_aexpr e2 with
                      | VBool b1, VBool b2 => VBool (andb b1 b2)
                      | _, _ => default_value
                      end
      | APlus e1 e2 => match interp_aexpr e1, interp_aexpr e2 with
                       | VInt n1, VInt n2 => VInt (n1 + n2)
                       | _, _ => default_value
                       end
      | AStringConcat e1 e2 => match interp_aexpr e1, interp_aexpr e2 with
                               | VString s1, VString s2 => VString (s1 ++ s2)
                               | _, _ => default_value
                               end
      | AStringLength e => match interp_aexpr e with
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

    Definition interp_pexpr (e : pexpr) : bool :=
      match e with
      | PLt e1 e2 => match interp_aexpr e1, interp_aexpr e2 with
                     | VInt n1, VInt n2 => Z.ltb n1 n2
                     | _, _ => false
                     end
      | PEq e1 e2 => value_eqb (interp_aexpr e1) (interp_aexpr e2)
      end.

    Definition interp_rexpr (e : rexpr) : list (string * value) :=
      match e with
      | RRecord l => List.map (fun '(s, a) => (s, interp_aexpr a)) (record_sort l)
      end.
  End WithEnv.

  Fixpoint set_insert (v : value) (l : list value) :=
    match l with
    | nil => v :: nil
    | v' :: l' => if value_ltb v v' then v :: v' :: l'
                  else if value_eqb v v' then l
                       else v' :: set_insert v l'
    end.
  Fixpoint interp_expr (env : locals) (e : expr) : value :=
    match e with
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

  Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
  Section WithGenv.
    Context (Genv : tenv).

    Definition tenv_wf :=
      forall x t, map.get Genv x = Some t -> type_wf t.

    Inductive type_of_aexpr : aexpr -> type -> Prop :=
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
                        type_of_aexpr (AAccess x attr) t.

    Inductive well_typed_pexpr : pexpr -> Prop :=
    | TPLt e1 e2 : type_of_aexpr e1 TInt ->
                   type_of_aexpr e2 TInt ->
                   well_typed_pexpr (PLt e1 e2)
    | TPEq e1 e2 t : type_of_aexpr e1 t ->
                     type_of_aexpr e2 t ->
                     well_typed_pexpr (PEq e1 e2).

    Inductive type_of_expr : expr -> Prop :=
    | TEEmptySet tl : type_wf (TRecord tl) ->
                      type_of_expr (EEmptySet tl).
    (* ??? can avoid "set type" if expr can only be evaluated to sets of records *)
    End WithGenv.
End WithMap.
