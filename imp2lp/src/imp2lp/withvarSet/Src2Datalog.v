From imp2lp.withvarSet Require Import SrcLang Intermediate Utils Src2IR IR2Datalog.
From imp2lp Require Import Value.
From Stdlib Require Import List String.
From Datalog Require Import Pftree Datalog.
From coqutil Require Import Map.Interface.

Import ListNotations.

(* Composition of the two phases: from the CFG source language to plain
   Datalog.  This is the only file that depends on both phases.

   Definitions and correctness criteria only; no proofs yet. *)

(* The arity of each mutable variable's relation, read off the source signature *)
Definition arities_of (g_sig : list type) : list nat :=
  List.map (fun t => List.length (args_of_type t)) g_sig.

Section WithMap.
  Context {context : map.map dvar dvalue} {context_ok : map.ok context}.
  Context {context' : map.map var' dvalue} {context'_ok : map.ok context'}.
  Context {tenv : map.map String.string type} {tenv_ok : map.ok tenv}.
  Context {venv : map.map String.string Value.value} {venv_ok : map.ok venv}.

  Definition compile (g : cfg) : program :=
    tgt_program (lower_dprog (arities_of g.(sig_blks).(sig)) (lower_cfg g.(sig_blks).(sig) g)).

  (* Phase 1 produces a well-formed IR program, so that phase 2's criteria apply
     to it.  The witness is the assembled family of auxiliary-relation arities. *)
  Lemma lower_cfg_dprog_wf :
    forall (g : cfg),
      well_typed_cfg g ->
      exists aux,
        dprog_wf (arities_of g.(sig_blks).(sig)) aux (lower_cfg g.(sig_blks).(sig) g).
  Admitted.

  (* ===== End-to-end criteria =====

     A global fact derived at timestamp [ts] by the compiled Datalog program
     corresponds to the source state after [ts] steps. *)

  Theorem compile_sound :
    forall (g : cfg),
      well_typed_cfg g ->
      forall (r : global_rel) (us : list dvalue) (ts : nat),
        program.interp (compile g) (fun _ => False)
          (fact.normal {| normal_fact.rel := glob_rel' r;
                          normal_fact.args := DVNat ts :: us |}) ->
        match cfg_steps (venv:=venv) g.(sig_blks) g.(str_ptr) ts with
        | Some g_d => lower_state g_d (mk_fact (glob_rel r) us)
        | None => False
        end.
  Proof.
    intros g Hwt r us ts H.
    destruct (lower_cfg_dprog_wf _ Hwt) as [aux Hwf].
    unfold compile in H.
    apply (lower_dprog_sound _ aux _ Hwf) in H.
    apply (lower_cfg_sound _ ts Hwt) in H.
    unfold lower_option_state in H.
    destruct (cfg_steps _ _ _); assumption.
  Qed.

  Theorem compile_complete :
    forall (g : cfg) (ts : nat) (g_d : cfg_dynamic),
      well_typed_cfg g ->
      cfg_steps (venv:=venv) g.(sig_blks) g.(str_ptr) ts = Some g_d ->
      forall (r : global_rel) (us : list dvalue),
        lower_state g_d (mk_fact (glob_rel r) us) ->
        program.interp (compile g) (fun _ => False)
          (fact.normal {| normal_fact.rel := glob_rel' r;
                          normal_fact.args := DVNat ts :: us |}).
  Proof.
    intros g ts g_d Hwt Hsteps r us Hst.
    destruct (lower_cfg_dprog_wf _ Hwt) as [aux Hwf].
    unfold compile.
    apply (lower_dprog_complete _ aux _ Hwf).
    eapply lower_cfg_complete; eauto.
  Qed.
End WithMap.
