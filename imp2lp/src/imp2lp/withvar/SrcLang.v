From Stdlib Require Import String ZArith List Bool Sorted Permutation.
From imp2lp Require Import MyTactics.

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
(* | AVar (x : string) *)
| ALoc (x : nat)
| ABool (b : bool)
| AInt (n : Z)
| AString (s : string)
(* | ALet (a1 : aexpr) (x : string) (a2 : aexpr) *)
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
| ELoc (x : nat)
| EEmptySet (l : list (string * type))
| ESetInsert (r : rexpr) (e : expr)
(* relational algebra *)
| EFilter (e : expr) (x : string) (p : list pexpr) (* Select a subset of rows from table *)
| EJoin (e1 e2 : expr) (x y : string) (p : list pexpr) (r : rexpr) (* Join two tables *)
| EProj (e : expr) (x : string) (r : rexpr) (* Generalized projection *).


Variant flow : Type :=
  | FGoto (next_blk : nat)
  | FIf (e : expr) (next_blk1 : nat) (next_blk2 : nat)
  | FRet.

Variant block : Type :=
  Blk (asgns : list expr) (fl : flow).

Require Import coqutil.Map.Interface coqutil.Datatypes.Result.
Require Import imp2lp.Value.
Require Import coqutil.Tactics.case_match.

(* Use a list to represent the store so the compilation is simpler later *)
(* First declare all mutable variables, each annotated with its schema *)
Record cfg_static := { sig : list type; blks : list block }.
(* Store and an optional pointer to the next block *)
Record cfg_dynamic := { str : list value; ptr : option nat }.
Record cfg := { sig_blks : cfg_static; str_ptr : cfg_dynamic }.

(* Semantics *)
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
                 Forall (fun p => is_atomic_type (snd p)) tl ->
                 type_wf (TRecord tl)
| WFTSet tl : type_wf (TRecord tl) ->
             type_wf (TSet (TRecord tl)).

Inductive type_of_value : value -> type -> Prop :=
| TVInt n : type_of_value (VInt n) TInt
| TVBool b : type_of_value (VBool b) TBool
| TVString s : type_of_value (VString s) TString
| TVRecord tl vl :
  map fst tl = map fst vl ->
  Forall2 (fun tp vp => type_of_value (snd vp) (snd tp)) tl vl ->
  type_of_value (VRecord vl) (TRecord tl)
| TVSet l t : Forall (fun v => type_of_value v t) l ->
              type_of_value (VSet l) (TSet t).

Section WithMap.
  Context {venv: map.map string value} {venv_ok: map.ok venv}.
  Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.

  Definition default_value := VBool false.

  Section WithGstr.
    Context (g_str : list value).

    Fixpoint interp_aexpr (env : venv) (e : aexpr) : value :=
      match e with
      | ALoc x => match nth_error g_str x with
                  | Some v => v
                  | _ => default_value
                  end
      | ABool b => VBool b
      | AInt n => VInt n
      | AString s => VString s
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
      | ELoc x => match nth_error g_str x with
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

    Definition flow_step (fl : flow) : option nat :=
      match fl with
      | FGoto n => Some n
      | FIf p n1 n2 => Some match interp_expr p with
                         | VBool true => n1
                         | _ => n2
                         end
      | FRet => None
      end.
  End WithGstr.

  Definition cfg_step (g_s : cfg_static) (g_d : cfg_dynamic) : option cfg_dynamic :=
    match g_d.(ptr) with
    | Some n =>
        match nth_error g_s.(blks) n with
        | Some (Blk asgns fl) =>
            let str' := List.map (interp_expr g_d.(str)) asgns in
            let ptr' := flow_step g_d.(str) fl in
            Some {| str := str'; ptr := ptr' |}
        | None => None
        end
    | None => None
    end.

  Fixpoint cfg_steps (g_s : cfg_static) (g_d : cfg_dynamic) (t : nat) : option cfg_dynamic :=
    match t with
    | O => Some g_d
    | S t => match cfg_steps g_s g_d t with
             | Some g_d' => cfg_step g_s g_d'
             | None => None
             end
    end.

  Section WithGsig.
    Context (g_sig : list type).

    Definition tenv_wf (G : tenv) :=
      forall x t, map.get G x = Some t ->
                  type_wf t.

    Inductive type_of_aexpr (Genv : tenv) : aexpr -> type -> Prop :=
    | TALoc x t : nth_error g_sig x = Some t ->
                  is_atomic_type t ->
                  type_of_aexpr Genv (ALoc x) t
    | TABool b : type_of_aexpr Genv (ABool b) TBool
    | TAInt n : type_of_aexpr Genv (AInt n) TInt
    | TAString s : type_of_aexpr Genv (AString s) TString
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
    | TELoc x t : nth_error g_sig x = Some (TSet (TRecord t)) ->
                  type_of_expr (ELoc x) (TSet (TRecord t))
    | TEEmptySet tl : type_wf (TRecord tl) ->
                      type_of_expr (EEmptySet tl) (TSet (TRecord tl))
    | TESetInsert r e t : type_of_rexpr map.empty r t ->
                          type_of_expr e (TSet t) ->
                          type_of_expr (ESetInsert r e) (TSet t)
    | TEFilter e x ps t : type_of_expr e (TSet t) ->
                          Forall (well_typed_pexpr (map.put map.empty x t)) ps ->
                          type_of_expr (EFilter e x ps) (TSet t)
    | TEJoin e1 e2 x1 x2 ps r t1 t2 t :
      x1 <> x2 ->
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
      | ALoc x => match nth_error g_sig x with
                  | Some t => Success t
                  | _ => error:(x "is not in scope")
                  end
      | ABool _ => Success TBool
      | AInt _ => Success TInt
      | AString _ => Success TString
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

    Definition well_typed_asgns (asgns : list expr) : Prop :=
      Forall2 type_of_expr asgns g_sig.

    Variant well_typed_flow (num_blks : nat) : flow -> Prop :=
      | WTFGoto n :
        n < num_blks ->
        well_typed_flow num_blks (FGoto n)
      | WTFIf p n1 n2 :
        n1 < num_blks ->
        n2 < num_blks ->
        type_of_expr p TBool ->
        well_typed_flow num_blks (FIf p n1 n2)
      | WTFRet :
        well_typed_flow num_blks FRet.

    Definition well_typed_block (num_blks : nat) (blk : block) : Prop :=
      match blk with
        Blk asgns fl =>
          well_typed_asgns asgns /\ well_typed_flow num_blks fl
      end.
  End WithGsig.

  Definition venv_wf (Genv : tenv) (env : venv) : Prop :=
    forall x t, map.get Genv x = Some t ->
                match map.get env x with
                | Some v => type_of_value v t
                | None => False
                end.

  Definition sig_wf : list type -> Prop :=
    Forall type_wf.

  Definition str_wf (g_sig : list type) (g_str : list value) : Prop :=
    Forall2 type_of_value g_str g_sig.

  Definition well_typed_cfg (g : cfg) : Prop :=
    let num_blks := List.length g.(sig_blks).(blks) in
    let g_sig := g.(sig_blks).(sig) in
    let g_blks := g.(sig_blks).(blks) in
    let g_str := g.(str_ptr).(str) in
    let g_ptr := g.(str_ptr).(ptr) in
    sig_wf g_sig /\
    Forall (well_typed_block g_sig num_blks) g_blks /\
      str_wf g_sig g_str /\
      match g_ptr with
      | Some n => n < num_blks
      | None => True
      end.

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

  Lemma type_of_aexpr__type_wf : forall g_sig Genv a t,
      type_of_aexpr g_sig Genv a t ->
      sig_wf g_sig -> tenv_wf Genv ->
      type_wf t.
  Proof.
    induction 1; try now constructor.
    all: try (intros; destruct t; cbn in *; intuition idtac; constructor).
    (* intros. apply IHtype_of_aexpr2; eauto using tenv_wf_step. *)
  Qed.

  Lemma access_record_Forall_snd : forall A l x (a : A) P,
      access_record l x = Success a ->
      Forall P (map snd l) ->
      P a.
  Proof.
    induction l; cbn; try discriminate.
    intros; repeat destruct_match_hyp; cbn in *; invert_Forall.
    1:{ do_injection. assumption. }
    1:{ eapply IHl; eauto. }
  Qed.

  Lemma type_of_expr__type_wf : forall g_sig e t,
      type_of_expr g_sig e t ->
      sig_wf g_sig ->
      type_wf t.
  Proof.
    induction 1; eauto using type_of_aexpr__type_wf, tenv_wf_empty.
    1: constructor; auto.
    all: unfold sig_wf in *; intuition idtac.
    1:{ lazymatch goal with
        H: nth_error _ _ = _ |- _ =>
          apply nth_error_In in H
      end.
        lazymatch goal with
        | H:Forall _ ?l, _:In _ ?l |- _ => eapply List.Forall_In in H
        end; [ | eauto ].
        lazymatch goal with
          H: type_wf (_ ?t) |- type_wf ?t =>
            inversion H; subst
        end. assumption. }
    1:{ constructor; auto. }
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

  Lemma Forall2_nth_error_r : forall A B (P : A -> B -> Prop) l1 l2,
      Forall2 P l1 l2 ->
      forall n v2,
        nth_error l2 n = Some v2 ->
        exists v1, P v1 v2 /\ nth_error l1 n = Some v1.
  Proof.
    induction 1; cbn; intros.
    1:{ rewrite nth_error_nil in *; discriminate. }
    1:{ destruct n; cbn in *; auto.
        do_injection.
        eexists; eauto. }
  Qed.

  Ltac apply_Forall2_nth_error :=
    lazymatch goal with
      H: nth_error _ _ = Some _ |- _ =>
        eapply Forall2_nth_error_r in H
    end.

  Lemma Forall2_access_record : forall A B vl tl attr t (P : A -> B -> Prop),
      Forall2 (fun tp vp => P (snd vp) (snd tp)) tl vl ->
      map fst tl = map fst vl ->
      access_record tl attr = Success t ->
      match access_record vl attr with
      | Success v => P v t
      | _ => False
      end.
  Proof.
    induction 1; cbn; intros; try discriminate.
    do 2 destruct_match_hyp;
    invert_cons; case_match; cbn in *; subst.
    1:{ rewrite String.eqb_eq in *.
        do_injection. rewrite String.eqb_refl.
        assumption. }
    1:{ rewrite_asm. apply IHForall2 in H5; auto. }
  Qed.

  Lemma aexpr_type_sound : forall g_sig Genv e t,
      type_of_aexpr g_sig Genv e t ->
      sig_wf g_sig -> tenv_wf Genv ->
      forall g_str env,
      str_wf g_sig g_str ->
      venv_wf Genv env ->
      type_of_value (interp_aexpr g_str env e) t.
  Proof.
    induction 1; intros; cbn; try constructor.
    1:{ unfold str_wf in *; intuition idtac.
        apply_Forall2_nth_error; eauto.
        destruct_exists; intuition idtac.
        rewrite_asm. assumption. }
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
        inversion H; subst; clear H
    end.

  Lemma Forall2_map_l : forall A B C P (f : A -> B) l (l' : list C),
      Forall2 (fun x y => P (f x) y) l l' -> Forall2 P (map f l) l'.
  Proof.
    induction 1; cbn; auto.
  Qed.

  Lemma rexpr_type_sound : forall g_sig Genv e t g_str env,
      type_of_rexpr g_sig Genv e t ->
      sig_wf g_sig -> tenv_wf Genv ->
      str_wf g_sig g_str -> venv_wf Genv env ->
      type_of_value (VRecord (interp_rexpr g_str env e)) t.
  Proof.
    destruct 1; cbn; intros.
    remember (record_sort el) as l.
    constructor.
    1:{ rewrite map_map. revert H0. clear.
        induction 1; cbn; auto.
        case_match; cbn in *. congruence. }
    1:{ revert H1. clear Heql H H0.
        induction 1; cbn; constructor; auto.
        case_match; cbn in *; auto;
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
    | IH: context[_ -> type_of_value (_ _ ?e) _] |- type_of_value (_ _ ?e) _ =>
        eapply IH; eauto
    | IH: context[type_of_value (interp_expr _ ?e) _],
        H: str_wf _ _ |-
        context[interp_expr _ ?e] =>
        let H' := fresh "H'" in
        eapply IH in H as H'; eauto
    end.

  Theorem expr_type_sound : forall e g_sig t g_str,
      type_of_expr g_sig e t ->
      sig_wf g_sig ->
      str_wf g_sig g_str ->
      type_of_value (interp_expr g_str e) t.
  Proof.
    induction e; cbn; intros;
      lazymatch goal with
       H: context[type_of_expr] |- _ =>
         inversion H; subst
      end.
    1:{ eapply aexpr_type_sound; eauto using tenv_wf_empty, venv_wf_empty. }
    1:{ unfold sig_wf, str_wf in *; intuition idtac.
        apply_Forall2_nth_error; eauto.
        destruct_exists; intuition idtac.
        rewrite_asm; assumption. }
    1:{ constructor; auto. }
    1:{ apply_type_sound_IH. invert_type_of_value. constructor.
        rewrite Forall_forall; intros ? H_in.
        apply set_insert_incl in H_in; intuition subst.
        2: apply_Forall_In.
        eapply rexpr_type_sound; eauto using tenv_wf_step, tenv_wf_empty, venv_wf_empty. }
    1:{ apply_type_sound_IH.  invert_type_of_value. constructor.
        eapply incl_Forall; try eassumption.
        apply incl_filter. }
    1:{ repeat (apply_type_sound_IH; invert_type_of_value). constructor.
        erewrite <- Permuted_value_sort.
        rewrite Forall_flat_map.
        rewrite Forall_forall; intros.
        rewrite Forall_flat_map.
        rewrite Forall_forall; intros.
        case_match; constructor; auto.
        eapply rexpr_type_sound; eauto.
        1: prove_tenv_wf.
        1: prove_venv_wf. }
    1:{ apply_type_sound_IH. invert_type_of_value. constructor.
        erewrite <- Permuted_value_sort.
        rewrite Forall_map.
        rewrite Forall_forall; intros.
        eapply rexpr_type_sound; eauto.
        1: prove_tenv_wf.
        1: prove_venv_wf. }
  Qed.

  Lemma Forall2_snd_combine : forall A (l1 : list (A * type)) (l2 : list A) l3,
      length l2 = length l3 ->
      Forall2 (fun tp vp => type_of_value (snd vp) (snd tp)) l1 (combine l2 l3) <->
        Forall2 (fun tp vp => type_of_value vp (snd tp)) l1 l3.
  Proof.
    induction l1; split; intros; invert_Forall2;
      destruct l2; try destruct l3; try discriminate;
      auto; cbn in *.
    1:{ constructor; invert_cons; auto.
        eapply IHl1; eauto. }
    1:{ constructor; cbn; auto.
        rewrite IHl1; auto. }
  Qed.

  Lemma Forall2_map_r: forall A B C P (f : C -> B) (l : list A) (l' : list C),
      Forall2 (fun (x : A) (y : C) => P x (f y)) l l' ->
      Forall2 P l (map f l').
  Proof.
    induction 1; cbn; auto.
  Qed.

  Ltac apply_Forall2_length :=
    lazymatch goal with
      H: Forall2 _ _ _ |- _ =>
        apply Forall2_length in H
    end.

  Lemma asgns_type_sound' : forall sig sig' str asgns,
      str_wf sig str ->
      sig_wf sig ->
      Forall2 (type_of_expr sig) asgns sig' ->
      str_wf sig' (List.map (interp_expr str) asgns).
  Proof.
    unfold str_wf; induction 3; cbn; auto.
    constructor; auto.
    eapply expr_type_sound; eauto.
  Qed.

  Lemma asgns_type_sound : forall sig str asgns,
      str_wf sig str ->
      sig_wf sig ->
      well_typed_asgns sig asgns ->
      str_wf sig (List.map (interp_expr str) asgns).
  Proof.
    unfold well_typed_asgns; intros.
    eapply asgns_type_sound'; eauto.
  Qed.

  Lemma flow_type_sound : forall sig num_blks fl str,
      str_wf sig str ->
      sig_wf sig ->
      well_typed_flow sig num_blks fl ->
      match flow_step str fl with
      | Some n => n < num_blks
      | None => True
      end.
  Proof.
    inversion 3; subst; cbn; auto.
    eapply expr_type_sound in H4; eauto.
    invert_type_of_value.
    case_match; auto.
  Qed.

  Ltac invert_well_typed_block :=
    lazymatch goal with
      H: well_typed_block _ _ _ |- _ =>
        inversion H; subst; clear H
    end.

  Ltac apply_nth_error_In :=
    lazymatch goal with
      H: nth_error _ _ = Some _ |- _ =>
        apply nth_error_In in H
    end.

  Lemma cfg_step_preservation : forall g_s g_d g_d',
      well_typed_cfg {| sig_blks := g_s; str_ptr := g_d |} ->
      cfg_step g_s g_d = Some g_d' ->
      well_typed_cfg {| sig_blks := g_s; str_ptr := g_d' |}.
  Proof.
    inversion 1; cbn in *.
    unfold cfg_step; intros.
    repeat destruct_match_hyp; try discriminate.
    do_injection; clear_refl.
    constructor; cbn; intuition idtac.
    all:
      apply_nth_error_In;
      apply_Forall_In;
      invert_well_typed_block.
    1:{ apply asgns_type_sound; assumption. }
    1:{ eapply flow_type_sound; eassumption. }
  Qed.

  Theorem cfg_steps_preservation : forall g_s ts g_d g_d',
      well_typed_cfg {| sig_blks := g_s; str_ptr := g_d |} ->
      cfg_steps g_s g_d ts = Some g_d' ->
      well_typed_cfg {| sig_blks := g_s; str_ptr := g_d' |}.
  Proof.
    induction ts; cbn; intros.
    1:{ do_injection; assumption. }
    1:{ destruct_match_hyp; try discriminate.
        eapply cfg_step_preservation.
        2: eauto.
        1: eapply IHts; eauto. }
  Qed.

  Lemma lt_length__nth_error : forall A (l : list A) n,
      n < List.length l ->
      exists a, In a l /\ nth_error l n = Some a.
  Proof.
    induction l; cbn; intros.
    1: apply Nat.nlt_0_r in H; intuition fail.
    destruct n.
    1: eexists; eauto.
    apply Nat.succ_lt_mono in H.
    apply IHl in H.
    destruct_exists. intuition eauto.
  Qed.

  Theorem cfg_step_progress : forall g_s g_d b,
      well_typed_cfg {| sig_blks := g_s; str_ptr := g_d |} ->
      g_d.(ptr) = Some b ->
      exists g_d', cfg_step g_s g_d = Some g_d'.
  Proof.
    inversion 1; cbn in *; subst.
    unfold cfg_step.
    intros; repeat rewrite_l_to_r.
    intuition idtac.
    lazymatch goal with
      H: _ < _ |- _ =>
        apply nth_error_Some in H
    end.
    case_match; intuition idtac.
    apply_nth_error_In; apply_Forall_In.
    case_match; invert_well_typed_block.
    eauto.
  Qed.
End WithMap.
