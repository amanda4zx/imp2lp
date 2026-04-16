From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Arith.PeanoNat. Import Nat.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Reals.Reals. Import Rdefinitions. Import RIneq.
From Stdlib Require Import ZArith.Int.
From Stdlib Require Import ZArith.Znat.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List.

Import ListNotations.

(*relations, variables, functions, and "aggregator functions" (e.g. min, max, sum, prod)*)
(* A datalog program talks about facts R(x1, ..., xn), where (R : rel) and (x1 : T), (x2 : T), etc. *)
Class signature {fn aggregator T : Type} : Type :=
  {
    (*returning None means inputs not in domain (e.g., number of args was wrong)*)
    interp_fun : fn -> list T -> option T;
    (*if x represents a finite set, then get_set x = Some ([x1; ...; xn]), where x1, ..., xn are the elements of the set*)
    get_set : T -> option (list T);
    (*agg_id sum = O, agg_id prod = 1, agg_id min = inf, etc*)
    agg_id : aggregator -> T;
    (*interp_agg takes an aggregator and returns the corresponding binop...
    arguably type should be aggregator -> T -> T -> option T,
    but i dont want to bother with that*)
    interp_agg : aggregator -> T -> T -> T; }.
Arguments signature : clear implicits.

Class query_signature {rel : Type} :=
  { outs : rel -> nat }.
Arguments query_signature : clear implicits.

Section __.
  Context {rel var fn aggregator T : Type}.
  Context `{sig : signature fn aggregator T} `{query_sig : query_signature rel}.
  Context {context : map.map var T} {context_ok : map.ok context}.
  Context {var_eqb : var -> var -> bool} {var_eqb_spec :  forall x0 y0 : var, BoolSpec (x0 = y0) (x0 <> y0) (var_eqb x0 y0)}.

  (*avoid generating useless induction principle*)
  Unset Elimination Schemes.
  Inductive expr :=
  | var_expr (v : var)
  | fun_expr (f : fn) (args : list expr).
  Set Elimination Schemes.

  Record fact :=
    { fact_R : rel;
      fact_args : list expr }.

  Unset Elimination Schemes.
  (*semantics of expressions*)
  Inductive interp_expr (ctx : context) : expr -> T -> Prop :=
  | interp_var_expr x v :
    map.get ctx x = Some v ->
    interp_expr ctx (var_expr x) v
  | interp_fun_expr f args args' x :
    Forall2 (interp_expr ctx) args args' ->
    interp_fun f args' = Some x ->
    interp_expr ctx (fun_expr f args) x.
  Set Elimination Schemes.

  (*semantics of facts*)
  Inductive interp_fact (ctx: context) : fact -> rel * list T -> Prop :=
  | mk_interp_fact f args' :
    Forall2 (interp_expr ctx) f.(fact_args) args' ->
    interp_fact ctx f (f.(fact_R), args').

  Record agg_expr :=
    { agg_agg : aggregator; agg_i : var; agg_vs : list var; agg_s: expr; agg_body: expr; agg_hyps: list fact }.

  Inductive interp_agg_expr (ctx : context) : agg_expr -> T -> list (list (rel * list T)) -> Prop :=.

  Record rule := { rule_agg : option (var * agg_expr); rule_concls : list fact; rule_hyps : list fact; rule_set_hyps : list (expr * expr) }.

  Inductive interp_option_agg_expr : _ -> _ -> _ -> _ -> Prop :=
  | ioae_None ctx :
    interp_option_agg_expr ctx None ctx []
  | ioae_Some ctx ctx' res res' aexpr agg_hyps's :
    ctx' = map.put ctx res res' ->
    interp_agg_expr ctx aexpr res' agg_hyps's ->
    interp_option_agg_expr ctx (Some (res, aexpr)) ctx' agg_hyps's.

  Definition x_in_S ctx (x_S : expr * expr) :=
    let (x, s) := x_S in
    exists x' s' l,
      interp_expr ctx x x' /\
        interp_expr ctx s s' /\
        get_set s' = Some l /\
        In x' l.

  (*semantics of rules*)
  Inductive rule_impl' : context -> rule -> rel * list T -> list (rel * list T) -> list (list (rel * list T)) -> Prop :=
  | mk_rule_impl' r agg_hyps's ctx' f' hyps' ctx :
    interp_option_agg_expr ctx r.(rule_agg) ctx' agg_hyps's ->
    Exists (fun c => interp_fact ctx' c f') r.(rule_concls) ->
    Forall2 (interp_fact ctx) r.(rule_hyps) hyps' ->
    Forall (x_in_S ctx) r.(rule_set_hyps) ->
    rule_impl' ctx r f' hyps' agg_hyps's.

  Hint Constructors rule_impl' interp_option_agg_expr : core.

  Definition rule_impl r f hyps'_agg_hyps's :=
    exists ctx hyps' agg_hyps's,
      hyps'_agg_hyps's = hyps' ++ concat agg_hyps's /\ rule_impl' ctx r f hyps' agg_hyps's.

  Lemma normal_rule_impl hyps concls f' hyps' ctx :
    Exists (fun c => interp_fact ctx c f') concls ->
    Forall2 (interp_fact ctx) hyps hyps' ->
    rule_impl {| rule_agg := None; rule_hyps := hyps; rule_set_hyps := []; rule_concls := concls|} f' hyps'.
  Proof.
    intros. cbv [rule_impl]. exists ctx, hyps', nil. rewrite app_nil_r. intuition.
    econstructor; simpl; eauto.
  Qed.

  Unset Elimination Schemes.
  Inductive pftree {T : Type} (P : T -> list T -> Prop) : T -> Prop :=
  | mkpftree x l :
    P x l ->
    Forall (pftree P) l ->
    pftree P x.
  Set Elimination Schemes.
  Hint Constructors pftree : core.

  (*semantics of programs*)
  Definition prog_impl_fact (p : list rule) : rel * list T -> Prop :=
    pftree (fun f' hyps' => Exists (fun r => rule_impl r f' hyps') p).

  Unset Elimination Schemes.
  Inductive partial_pftree {T : Type} (P : T -> list T -> Prop) (Q : T -> Prop) : T -> Prop :=
  | partial_in x :
    Q x ->
    partial_pftree _ _ x
  | partial_step x l :
    P x l ->
    Forall (partial_pftree _ _) l ->
    partial_pftree _ _ x.
  Set Elimination Schemes.

  Hint Constructors partial_pftree : core.

  Lemma pftree_ind {U : Type} (P : U -> list U -> Prop) Q :
    (forall x l,
        P x l ->
        Forall (pftree P) l ->
        Forall Q l ->
        Q x) ->
    forall x, pftree P x -> Q x.
  Proof.
    intros H. fix self 2.
    (*i find using fix to be hacky ( e.g. i can't use Forall_impl here :( )
      but i don't know an easy way to get around it.
      trick with expr below doesn't easily work, since pftree goes to Prop.
     *)
    intros x Hx. inversion Hx; subst. eapply H; eauto.
    clear -self H1. induction H1; eauto.
  Qed.

  Lemma pftree_weaken_strong {T1 T2 : Type}
    (P1 : T1 -> list T1 -> Prop) (P2 : T2 -> list T2 -> Prop) x f :
    pftree P1 x ->
    (forall x l, P1 x l -> P2 (f x) (map f l)) ->
    pftree P2 (f x).
  Proof.
    intros H1 H. induction H1. econstructor.
    2: { eapply Forall_map. eassumption. }
    apply H. assumption.
  Qed.

  Lemma partial_pftree_ind {U : Type} (P : U -> list U -> Prop) Q R :
    (forall x, Q x -> R x) ->
    (forall x l,
        P x l ->
        Forall (partial_pftree P Q) l ->
        Forall R l ->
        R x) ->
    forall x, partial_pftree P Q x -> R x.
  Proof.
    intros H1 H2. fix self 2.
    intros x Hx. inversion Hx; subst. 1: auto. eapply H2. 1,2: eassumption.
    clear -H0 self. induction H0; eauto.
  Qed.

  Lemma pftree_partial_pftree {U : Type} P1 P2 Q (x : U) :
    pftree P1 x ->
    (forall y l, P1 y l -> P2 y l \/ Q y) ->
    partial_pftree P2 Q x.
  Proof.
    intros H1 H2. induction H1; eauto. apply H2 in H. destruct H; eauto.
  Qed.

  Lemma partial_pftree_pftree {U : Type} P (x : U) :
    partial_pftree P (fun y => False) x ->
    pftree P x.
  Proof. induction 1; eauto. contradiction. Qed.

  Lemma partial_pftree_trans {U : Type} P (x : U) Q :
    partial_pftree P (partial_pftree P Q) x ->
    partial_pftree P Q x.
  Proof. induction 1; eauto. Qed.

  Definition prog_impl_implication (p : list rule) : (rel * list T -> Prop) -> rel * list T -> Prop :=
    partial_pftree (fun f' hyps' => Exists (fun r => rule_impl r f' hyps') p).

  Lemma prog_impl_step p Q f hyps' :
    Exists (fun r : rule => rule_impl r f hyps') p ->
    Forall (prog_impl_implication p Q) hyps' ->
    prog_impl_implication p Q f.
  Proof. intros. eapply partial_step; eauto. Qed.

  Lemma prog_impl_fact_prog_impl_implication p1 p2 Q f :
    prog_impl_fact p1 f ->
    (forall r f hyps, In r p1 ->
                 rule_impl r f hyps ->
                 In r p2 \/ Q f) ->
    prog_impl_implication p2 Q f.
  Proof.
    intros. eapply pftree_partial_pftree; [eassumption|]. simpl.
    intros y l Hy. apply Exists_exists in Hy. fwd.
    eapply H0 in Hyp0; eauto. rewrite Exists_exists. destruct Hyp0 as [H'|H']; eauto.
  Qed.

  Lemma prog_impl_implication_prog_impl_fact p f :
    prog_impl_implication p (fun _ => False) f ->
    prog_impl_fact p f.
  Proof.
    cbv [prog_impl_implication prog_impl_fact].
    eauto using partial_pftree_pftree.
  Qed.

  Lemma partial_pftree_weaken_hyp {U : Type} P (x : U) Q1 Q2 :
    partial_pftree P Q1 x ->
    (forall y, Q1 y -> Q2 y) ->
    partial_pftree P Q2 x.
  Proof. intros H1 H2. induction H1; eauto. Qed.

  Lemma prog_impl_implication_weaken_hyp p x Q1 Q2 :
    prog_impl_implication p Q1 x ->
    (forall y, Q1 y -> Q2 y) ->
    prog_impl_implication p Q2 x.
  Proof. cbv [prog_impl_implication]. eauto using partial_pftree_weaken_hyp. Qed.

  Definition F p Q Px :=
    let '(P, x) := Px in
    P x \/ Q (P, x) \/ exists hyps', Exists (fun r => rule_impl r x hyps') p /\ Forall (fun x => Q (P, x)) hyps'.

  Lemma F_mono p S1 S2 :
    (forall x, S1 x -> S2 x) ->
    (forall x, F p S1 x -> F p S2 x).
  Proof.
    cbv [F]. intros Hle [P x] H. intuition auto. fwd. right. right. eexists.
    split; [eassumption|]. eapply Forall_impl; eauto. simpl. auto.
  Qed.

  Definition S_sane {U : Type} (S : (U -> Prop) * U -> Prop) :=
    (forall P x, P x -> S (P, x)) /\
      (forall P1 x P2,
          S (P1, x) ->
          (forall y, P1 y -> S (P2, y)) ->
          S (P2, x)).

  Hint Unfold prog_impl_implication : core.

  Hint Extern 2 => eapply Forall_impl; [|eassumption]; cbv beta : core.
  Hint Extern 2 => eapply Forall2_impl; [|eassumption]; cbv beta : core.

  Lemma partial_pftree_weaken {U : Type} P Q1 Q2 (x : U) :
    partial_pftree P Q1 x ->
    (forall y, Q1 y -> Q2 y) ->
    partial_pftree P Q2 x.
  Proof. induction 1; eauto. Qed.

  Fixpoint expr_size (e : expr) :=
    match e with
    | var_expr _ => O
    | fun_expr _ args => S (fold_right Nat.max O (map expr_size args))
    end.

  (*This is stupid.  how do people normally do it?*)
  Lemma expr_ind P :
    (forall v, P (var_expr v)) ->
    (forall f args,
        Forall P args ->
        P (fun_expr f args)) ->
    forall e, P e.
  Proof.
    intros. remember (expr_size e) as sz eqn:E.
    assert (He: (expr_size e < Datatypes.S sz)%nat) by lia.
    clear E. revert e He. induction (Datatypes.S sz); intros.
    - lia.
    - destruct e; simpl in He; auto.
      + apply H0. clear -IHn He. induction args; [constructor|].
        simpl in *. constructor; [|apply IHargs; lia]. apply IHn. lia.
  Qed.

  Lemma pftree_weaken {U : Type} (P1 P2 : U -> list U -> Prop) x :
    pftree P1 x ->
    (forall x l, P1 x l -> P2 x l) ->
    pftree P2 x.
  Proof. intros H0 H. induction H0; econstructor; eauto. Qed.

  Lemma prog_impl_fact_subset (p1 p2 : list rule) f :
    (forall x, In x p1 -> In x p2) ->
    prog_impl_fact p1 f ->
    prog_impl_fact p2 f.
  Proof.
    intros H H0. eapply pftree_weaken; simpl; eauto. simpl.
    intros. apply Exists_exists in H1. apply Exists_exists. fwd. eauto.
  Qed.

  Fixpoint vars_of_expr (e : expr) : list var :=
    match e with
    | fun_expr _ args => flat_map vars_of_expr args
    | var_expr v => [v]
    end.

  Definition vars_of_fact (f : fact) : list var :=
    flat_map vars_of_expr f.(fact_args).

  Definition appears_in_agg_expr v ae :=
    In v (vars_of_expr ae.(agg_s)) \/
      ~In v (ae.(agg_i) :: ae.(agg_vs)) /\
        (In v (vars_of_expr ae.(agg_body)) \/ In v (flat_map vars_of_fact ae.(agg_hyps))).

  Definition good_agg_expr ae :=
    Forall (fun v => In (var_expr v) (flat_map fact_args ae.(agg_hyps))) ae.(agg_vs).

  Hint Unfold appears_in_agg_expr : core.
End __.
Arguments fact : clear implicits.
Arguments rule : clear implicits.
Arguments expr : clear implicits.
Arguments agg_expr : clear implicits.
