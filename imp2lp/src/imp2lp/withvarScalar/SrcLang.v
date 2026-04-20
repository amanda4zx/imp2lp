From Stdlib Require Import String ZArith List Bool Sorted Permutation.
From imp2lp Require Import MyTactics.

Import ListNotations.
Open Scope list_scope.

(* Fiat2 types *)
Inductive type : Type :=
| TInt
| TBool.

Scheme Boolean Equality for type. (* creates type_beq *)

Declare Scope fiat2_scope. Local Open Scope fiat2_scope.
Notation "t1 =? t2" := (type_beq t1 t2) (at level 70) : fiat2_scope.

(* Simple expressions *)
Inductive expr : Type :=
| ALoc (x : nat)
| ABool (b : bool)
| AInt (n : Z)
| ANot (a : expr)
| AAnd (a1 a2 : expr)
| APlus (a1 a2 : expr)
| ALt (a1 a2 : expr)
| AEq (a1 a2 : expr).

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

Inductive type_of_value : value -> type -> Prop :=
| TVInt n : type_of_value (VInt n) TInt
| TVBool b : type_of_value (VBool b) TBool.

Section WithMap.
  Definition default_value := VBool false.

  Section WithGstr.
    Context (g_str : list value).

    Fixpoint interp_expr (e : expr) : value :=
      match e with
      | ALoc x => match nth_error g_str x with
                  | Some v => v
                  | _ => default_value
                  end
      | ABool b => VBool b
      | AInt n => VInt n
      | ANot e => match interp_expr e with
                  | VBool b => VBool (negb b)
                  | _ => default_value
                  end
      | AAnd e1 e2 => match interp_expr e1, interp_expr e2 with
                      | VBool b1, VBool b2 => VBool (andb b1 b2)
                      | _, _ => default_value
                      end
      | APlus e1 e2 => match interp_expr e1, interp_expr e2 with
                       | VInt n1, VInt n2 => VInt (n1 + n2)
                       | _, _ => default_value
                       end
      | ALt e1 e2 => match interp_expr e1, interp_expr e2 with
                     | VInt n1, VInt n2 => VBool (Z.ltb n1 n2)
                     | _, _ => VBool false
                     end
      | AEq e1 e2 => VBool (value_eqb (interp_expr e1) (interp_expr e2))
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

  Variant cfg_step (g_s : cfg_static) (g_d : cfg_dynamic) : cfg_dynamic -> Prop :=
    | CS_mk n asgns fl str' ptr' :
      g_d.(ptr) = Some n ->
      nth_error g_s.(blks) n = Some (Blk asgns fl) ->
      str' = List.map (interp_expr g_d.(str)) asgns ->
      ptr' = flow_step g_d.(str) fl ->
      cfg_step g_s g_d {| str:=str'; ptr:=ptr' |}.

    Inductive cfg_steps (g_s : cfg_static) : cfg_dynamic -> cfg_dynamic -> Prop :=
    | CSS_refl g_d : cfg_steps g_s g_d g_d
    | CSS_trans g_d0 g_d1 g_d2 :
      cfg_steps g_s g_d0 g_d1 ->
      cfg_step g_s g_d1 g_d2 ->
      cfg_steps g_s g_d0 g_d2.
  Section WithGsig.
    Context (g_sig : list type).

    Inductive type_of_expr : expr -> type -> Prop :=
    | TALoc x t : nth_error g_sig x = Some t ->
                  type_of_expr (ALoc x) t
    | TABool b : type_of_expr (ABool b) TBool
    | TAInt n : type_of_expr (AInt n) TInt
    | TANot e : type_of_expr e TBool ->
                type_of_expr (ANot e) TBool
    | TAAnd e1 e2 : type_of_expr e1 TBool ->
                    type_of_expr e2 TBool ->
                    type_of_expr (AAnd e1 e2) TBool
    | TAPlus e1 e2 : type_of_expr e1 TInt ->
                     type_of_expr e2 TInt ->
                     type_of_expr (APlus e1 e2) TInt.

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

  Definition str_wf (g_sig : list type) (g_str : list value) : Prop :=
    Forall2 type_of_value g_str g_sig.

  Definition well_typed_cfg (g : cfg) : Prop :=
    let num_blks := List.length g.(sig_blks).(blks) in
    let g_sig := g.(sig_blks).(sig) in
    let g_blks := g.(sig_blks).(blks) in
    let g_str := g.(str_ptr).(str) in
    let g_ptr := g.(str_ptr).(ptr) in
    Forall (well_typed_block g_sig num_blks) g_blks /\
      str_wf g_sig g_str /\
      match g_ptr with
      | Some n => n < num_blks
      | None => True
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

  Lemma expr_type_sound : forall g_sig e t,
      type_of_expr g_sig e t ->
      forall g_str,
      str_wf g_sig g_str ->
      type_of_value (interp_expr g_str e) t.
  Proof.
    induction 1; intros; cbn; try constructor.
    1:{ unfold str_wf in *; intuition idtac.
        lazymatch goal with
          H: nth_error ?l _ = Some _,
            _: Forall2 _ _ ?l |- _ =>
            eapply Forall2_nth_error_r in H
        end; eauto.
        destruct_exists; intuition idtac.
        rewrite_l_to_r. assumption. }
    all: repeat lazymatch goal with
        IH: context[str_wf _ _ -> _],
          H: str_wf _ _ |- _ =>
          let H' := fresh "H'" in
          apply IH in H as H';
          clear IH; inversion H'; subst
           end; constructor.
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
      Forall2 (type_of_expr sig) asgns sig' ->
      str_wf sig' (List.map (interp_expr str) asgns).
  Proof.
    unfold str_wf; induction 2; cbn; auto.
    constructor; auto.
    eapply expr_type_sound; eauto.
  Qed.

  Lemma asgns_type_sound : forall sig str asgns,
      str_wf sig str ->
      well_typed_asgns sig asgns ->
      str_wf sig (List.map (interp_expr str) asgns).
  Proof.
    unfold well_typed_asgns; intros.
    eapply asgns_type_sound'; eauto.
  Qed.

  Lemma flow_type_sound : forall sig num_blks fl str,
      str_wf sig str ->
      well_typed_flow sig num_blks fl ->
      match flow_step str fl with
      | Some n => n < num_blks
      | None => True
      end.
  Proof.
    inversion 2; subst; cbn; auto.
    eapply expr_type_sound in H3; eauto.
    invert_type_of_value.
    case_match; auto.
  Qed.

  Theorem cfg_type_preservation : forall g_s g_d g_d',
      well_typed_cfg {| sig_blks := g_s; str_ptr := g_d |} ->
      cfg_steps g_s g_d g_d' ->
      well_typed_cfg {| sig_blks := g_s; str_ptr := g_d' |}.
  Proof.
    unfold well_typed_cfg; intros.
    induction H0; intuition idtac.
    all: destruct g_s, g_d1, g_d2; cbn in *.
    all: lazymatch goal with
           H: context[cfg_step] |- _ =>
             inversion H; subst
         end.
    all: lazymatch goal with
           H: nth_error _ _ = _ |- _ =>
             apply nth_error_In in H
         end; apply_Forall_In.
    all: cbn in *; subst; intuition idtac.
    1:{ apply asgns_type_sound; assumption. }
    1:{ eapply flow_type_sound; eassumption. }
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

  Theorem cfg_type_progress : forall g_s g_d,
      well_typed_cfg {| sig_blks := g_s; str_ptr := g_d |} ->
      match g_d.(ptr) with
      | Some _ => True
      | _ => False
      end ->
      exists g_d', cfg_step g_s g_d g_d'.
  Proof.
    destruct 1; subst; cbn in *; intuition idtac.
    destruct_match_hyp; intuition idtac.
    eapply lt_length__nth_error in H3; destruct_exists.
    intuition idtac. destruct x.
    eexists. econstructor; eauto.
  Qed.
End WithMap.
