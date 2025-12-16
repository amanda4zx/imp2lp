From Stdlib Require Import String ZArith List Bool.
Require Import imp2lp.Value. (* import for the record_sort function *)

Import ListNotations.
Open Scope list_scope.

(* Fiat2 types *)
Inductive type : Type :=
| TInt
| TBool
| TString.

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

(* Datalog *)
(* Values from evaluating Datalog expressions *)
Inductive obj : Set :=
  Bobj : bool -> obj | Zobj : Z -> obj | Sobj : string -> obj.

(* Functions on Datalog expressions *)
Variant fn : Set :=
  fn_Not | fn_And | fn_Plus | fn_StringConcat | fn_StringLength | fn_BLit (_ : bool) | fn_ZLit (_ : Z) | fn_SLit (_ : string).

(* Datalog variables *)
Variant var : Set := DVar (n : nat).

(* Datalog expressions *)
Inductive dexpr :=
| var_dexpr (v : var)
| fun_dexpr (f : fn) (args : list dexpr).

(* Datalog propositions that can appear as clauses on the RHS of a rule *)
Variant dprop :=
| DProp_Lt (e1 e2 : dexpr) | DProp_Eq (e1 e2 : dexpr).

(* Datalog relation names *)
Variant rel : Set :=
  nat_rel (n : nat).

Record fact :=
  { fact_R : rel;
    fact_args : list dexpr }.
Unset Elimination Schemes.

(* Datalog base types *)
Variant dtype := DBool | DNumber | DSymbol.

Record decl := { decl_R : rel; decl_sig : list (string * dtype) }.

Record rule := { rule_head : fact; rule_body : list fact; rule_prop : list dprop }.

Definition stmt : Type := decl + rule.

Section WithMap.
  Definition varenv := list (string * string * var * dtype).
  Fixpoint varenv_lookup (m : varenv) (x attr : string) : option (var * dtype) :=
    match m with
    | [] => None
    | (x', attr', v, t) :: m => if (x =? x')%string && (attr =? attr')%string then Some (v, t) else varenv_lookup m x attr
    end.

  Fixpoint lower_aexpr (m : varenv) (e : aexpr) : dexpr :=
    match e with
    | ABool b => fun_dexpr (fn_BLit b) []
    | AInt n => fun_dexpr (fn_ZLit n) []
    | AString s => fun_dexpr (fn_SLit s) []
    | ANot e => fun_dexpr fn_Not [lower_aexpr m e]
    | AAnd e1 e2 => fun_dexpr fn_And [lower_aexpr m e1; lower_aexpr m e2]
    | APlus e1 e2 => fun_dexpr fn_Plus [lower_aexpr m e1; lower_aexpr m e2]
    | AStringConcat e1 e2 => fun_dexpr fn_StringConcat [lower_aexpr m e1; lower_aexpr m e2]
    | AStringLength e => fun_dexpr fn_StringLength [lower_aexpr m e]
    | AAccess x attr => match varenv_lookup m x attr with
                        | Some (v, _) => var_dexpr v
                        | None => var_dexpr (DVar 0) (* unreachable *)
                        end
    end.

  Definition lower_pexpr (m : varenv) (e : pexpr) : dprop :=
    match e with
    | PLt e1 e2 => DProp_Lt (lower_aexpr m e1) (lower_aexpr m e2)
    | PEq e1 e2 => DProp_Eq (lower_aexpr m e1) (lower_aexpr m e2)
    end.

  Definition type_of_aexpr (m : varenv) (e : aexpr) : dtype :=
    match e with
    | ABool _ | ANot _ | AAnd _ _ => DBool
    | AInt _ | APlus _ _ | AStringLength _ => DNumber
    | AString _ | AStringConcat _ _ => DSymbol
    | AAccess x attr => match varenv_lookup m x attr with
                        | Some (_, t) => t
                        | _ => DBool (* unreachable *)
                        end
    end.

  Definition lower_rexpr (m : varenv) (e : rexpr) : list dexpr * list (string * dtype) :=
    match e with
      RRecord l =>
        ( List.map (fun '(_, a) => lower_aexpr m a) (record_sort l),
          List.map (fun '(s, a) => (s, type_of_aexpr m a)) (record_sort l))
    end.

  Fixpoint mk_vars (name : nat) (len : nat) : list var :=
    match len with
    | O => []
    | S l => DVar name :: (mk_vars (S name) l)
    end.

  Fixpoint put_attr_bindings (m : varenv) (x : string) (attr_tys : list (string * dtype)) (vars : list var) : varenv :=
    match attr_tys, vars with
    | [], _ | _, [] => m
    | (attr, t) :: attr_tys, v :: vars =>
        put_attr_bindings ((x, attr, v, t) :: m) x attr_tys vars
    end.

  Definition lower_type (t : type) : dtype :=
    match t with
    | TBool => DBool
    | TInt => DNumber
    | TString => DSymbol
    end.

  Definition default_dexpr : dexpr :=
    fun_dexpr (fn_BLit false) [].

  Fixpoint lower_expr (out : rel) (next_rel : nat) (e : expr) : list stmt * nat * list (string * dtype) :=
  match e with
  | EEmptySet l => ([], next_rel, map (fun '(s, t) => (s, lower_type t)) l)
  | ESetInsert r s =>
      let '(r', _) := lower_rexpr [] r in
      let aux := nat_rel next_rel in
      let '(rls, next_rel', attr_tys) := lower_expr aux (S next_rel) s in
      let vs := List.map var_dexpr (mk_vars 0 (List.length attr_tys)) in
      (inl {| decl_R := aux; decl_sig := attr_tys |} ::
         rls ++
         [ inr {| rule_head := {| fact_R := out; fact_args := r' |};
                 rule_body := [];
                 rule_prop := [] |};
           inr {| rule_head := {| fact_R := out; fact_args := vs |};
            rule_body := [ {| fact_R := aux; fact_args := vs |} ];
            rule_prop := [] |}],
        next_rel',
        attr_tys)
  | EFilter s x p =>
      (* out vs :- aux vs, p *)
      let aux := nat_rel next_rel in
      let '(rls, next_rel', attr_tys) := lower_expr aux (S next_rel) s in
      let vars := mk_vars 0 (List.length attr_tys) in
      let p' := List.map (lower_pexpr (put_attr_bindings [] x attr_tys vars)) p in
      let vs := List.map var_dexpr vars in
      (inl {| decl_R := aux; decl_sig := attr_tys |} ::
         rls ++
         [ inr {| rule_head := {| fact_R := out; fact_args := vs |};
                 rule_body := [ {| fact_R := aux; fact_args := vs |} ];
                 rule_prop := p' |}],
        next_rel',
        attr_tys)
  | EJoin s1 s2 x1 x2 p r =>
      (* out (lower_rexpr m r) :- aux1 vs1, aux2 vs2, lower_aexpr m p *)
      let aux1 := nat_rel next_rel in
      let '(rls1, next_rel1, attr_tys1) := lower_expr aux1 (S next_rel) s1 in
      let aux2 := nat_rel next_rel1 in
      let '(rls2, next_rel2, attr_tys2) := lower_expr aux2 (S next_rel1) s2 in
      let vars1 := mk_vars 0 (List.length attr_tys1) in
      let vars2 := mk_vars (List.length attr_tys1) (List.length attr_tys2) in
      let m := put_attr_bindings (put_attr_bindings [] x1 attr_tys1 vars1) x2 attr_tys2 vars2 in
      let vs1 := List.map var_dexpr vars1 in
      let vs2 := List.map var_dexpr vars2 in
      let p' := List.map (lower_pexpr m) p in
      let '(r', attr_tys) := lower_rexpr m r in
      (inl {| decl_R := aux1; decl_sig := attr_tys1 |} :: rls1 ++
         inl {| decl_R := aux2; decl_sig := attr_tys2 |} :: rls2 ++
         [ inr {| rule_head := {| fact_R := out; fact_args := r' |} ;
                 rule_body :=
                   [ {| fact_R := aux1; fact_args := vs1 |};
                     {| fact_R := aux2; fact_args := vs2 |} ];
                 rule_prop := p' |} ],
        next_rel2,
        attr_tys)
  | EProj s x r =>
      (* out rs :- aux vs *)
      let aux := nat_rel next_rel in
      let '(rls, next_rel', attr_tys) := lower_expr aux (S next_rel) s in
      let vars := mk_vars 0 (List.length attr_tys) in
      let '(r', out_attr_tys) := lower_rexpr (put_attr_bindings [] x attr_tys vars) r in
      let vs := List.map var_dexpr vars in
      (inl {| decl_R := aux; decl_sig := attr_tys |} ::
         rls ++
         [ inr {| rule_head := {| fact_R := out; fact_args := r' |};
                 rule_body := [ {| fact_R := aux; fact_args := vs |} ];
                 rule_prop := [] |}],
        next_rel',
        out_attr_tys)
  end.

  Fixpoint concat_strings_with (delim : string) (l : list string) : string :=
    match l with
    | [] => ""
    | [x] => x
    | s :: l => s ++ delim ++ concat_strings_with delim l
    end.

  Require Import Coq.Strings.BinaryString.

  Fixpoint print_dexpr (e : dexpr) : string :=
    match e with
    | var_dexpr (DVar n) => "x_" ++ of_nat n
    | fun_dexpr fn_Not [e] => "! " ++ print_dexpr e
    | fun_dexpr fn_And [e1; e2] => print_dexpr e1 ++ " land " ++ print_dexpr e2
    | fun_dexpr fn_Plus [e1; e2] => print_dexpr e1 ++ " + " ++ print_dexpr e2
    | fun_dexpr (fn_BLit b) [] => if b then "1" else "0"
    | fun_dexpr (fn_ZLit n) [] => of_Z n
    | fun_dexpr (fn_SLit s) [] => "'" ++ s ++ "'"
    | _ => "error"
    end.

  Definition print_prop (p : dprop) : string :=
    match p with
    | DProp_Lt e1 e2 => print_dexpr e1 ++ " < " ++ print_dexpr e2
    | DProp_Eq e1 e2 => print_dexpr e1 ++ " = " ++ print_dexpr e2
    end.

  Definition print_rel (r : rel) : string :=
    match r with
      nat_rel n => "R_" ++ of_nat n
    end.

  Definition print_fact (f : fact) : string :=
    print_rel (fact_R f) ++ "( " ++ concat_strings_with ", " (map print_dexpr (fact_args f)) ++ " )".

  Definition print_type (t : dtype) : string :=
    match t with
    | DBool => "number"
    | DNumber => "number"
    | DSymbol => "symbol"
    end.

  Definition print_rule (r : rule) : string :=
    print_fact (rule_head r) ++
      match rule_body r with
      | [] => ""
      | fs => " :- " ++ concat_strings_with ", " (map print_fact fs)
      end ++
      match rule_prop r with
      | [] => ""
      | ps => ", " ++ concat_strings_with ", " (List.map (fun p => print_prop p) ps)
      end ++ ".".

  Definition print_decl (d : decl) : string :=
    ".decl " ++ print_rel (decl_R d) ++ "( " ++
      concat_strings_with ", " (map (fun '(s, t) => s ++ ":" ++ print_type t)%string (decl_sig d)) ++ " )".

  Definition print_stmt (st : stmt) : string :=
    match st with
    | inl d => print_decl d
    | inr r => print_rule r
    end.

  Definition print_compiled_query (out : rel) (next_rel : nat) (e : expr) : string :=
    let '(rls, _, sig) := lower_expr out next_rel e in
    print_decl {| decl_R := out; decl_sig := sig |} ++
      "\n.output " ++ print_rel out ++ "\n" ++
      concat_strings_with "\n" (map print_stmt rls).

  Local Open Scope string_scope.

  (*
  Ex1:
    Names(id, name)
    Ages(id, age)

    Names JOIN Ages WITH age < 30 RET (id, name, age)
   *)
  Definition names_tbl := ESetInsert (RRecord [("id", AInt 2); ("name", AString "A")])
                            (ESetInsert (RRecord [("id", AInt 0); ("name", AString "B")])
                               (ESetInsert (RRecord [("id", AInt 1); ("name", AString "C")])
                                  (EEmptySet [("id", TInt); ("name", TString)]))).

  Definition ages_tbl := ESetInsert (RRecord [("id", AInt 0); ("age", AInt 23)])
                            (ESetInsert (RRecord [("id", AInt 2); ("age", AInt 39)])
                               (ESetInsert (RRecord [("id", AInt 1); ("age", AInt 14)])
                                  (EEmptySet [("age", TInt); ("id", TInt)]))).

  Definition join_query := EJoin names_tbl ages_tbl "name_row" "age_row" [PEq (AAccess "name_row" "age")(AAccess "age_row" "id")]
                         (RRecord [("id", AAccess "name_row" "id"); ("name", AAccess "name_row" "name"); ("age", AAccess "age_row" "age")]).
  Compute print_compiled_query (nat_rel 0) 1 join_query.


(*
  Ex2:
  Persons(id, name, is_female)

  PROJ (FILTER Persons WITH is_female = false) (id, name)
 *)
  Definition persons_tbl := ESetInsert (RRecord [("id", AInt 2); ("name", AString "A"); ("is_female", ABool false)])
                            (ESetInsert (RRecord [("id", AInt 0); ("name", AString "B"); ("is_female", ABool true)])
                               (ESetInsert (RRecord [("id", AInt 1); ("name", AString "C"); ("is_female", ABool false)])
                                  (EEmptySet [("id", TInt); ("is_female", TBool); ("name", TString)]))).

  Definition bool_query := EProj (EFilter persons_tbl "person" [PEq (AAccess "person" "is_female") (ABool false)]) "person" (RRecord [("id", AAccess "person" "id"); ("name", AAccess "person" "name")]).
  Compute print_compiled_query (nat_rel 0) 1 bool_query.
End WithMap.
