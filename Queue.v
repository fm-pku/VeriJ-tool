Require Import Spec.
Require Import List.

(*  Example Queue  *)

Definition null := Ref.rnull.
Definition rtrue := Ref.rtrue.
Definition rfalse := Ref.rfalse.
Definition Bool := RType.Bool.
Definition Null := RType.Null.
Definition ref := Ref.ref.
Definition add_lv := TEnv.update_method_locvars.
Definition state := State.state.
Definition init_state := State.init_state.
Definition pred := HProp.hprop.

Open Scope string_scope.
Open Scope lang_scope.
Open Scope hprop_scope.
Open Scope spec_scope.

Variable (r : ref) (alpha : list ref).

Definition no_lv := TEnv.method_no_locvar.

Module Node. (* Class Node *)
 Definition fields f := RType.update_field_type "val" Bool
                        (RType.update_field_type "nxt" "Node" f).
 Definition Node_cmd := Lang.fwrite "this" "val" (^"b");
                        Lang.fwrite "this" "nxt" Expr.null.
 
 (* public predicate *)
 Definition node : pred := .\(fun this => .\(fun n => .\(fun v =>
     this`"val" |-> v * this`"nxt" |-> n))).
 
 Definition Node_spec :=
     (HProp.emp,
      node&^"this"&null&^"b").
 
 Definition declare (s : state) : state :=
     State.build_method "Node" "Node" (Bool::nil, Null) ("b"::nil) no_lv Node_cmd
     (State.build_class "Node" (RType.Object::nil) fields s).
End Node.

Module Queue. (* Class Queue *)
 Definition fields      := RType.update_field_type "hd" "Node".
 Definition Queue_lv    := add_lv "x" "Node" no_lv.
 Definition enqueue_lv  := add_lv "p" "Node" (add_lv "q" "Node"
                          (add_lv "n" "Node" no_lv)).
 Definition dequeue_lv  := add_lv "p" "Node" (add_lv "h" "Node"
                          (add_lv "x" "Bool" no_lv)).
 Definition empty_lv    := add_lv "p" "Node" (add_lv "b" "Bool" no_lv).
 
 Definition Queue_cmd   := Lang.calloc "x" "Node" (Expr.fals::nil);
                           Lang.fwrite "this" "hd" (^"x").
 Definition enqueue_cmd := Lang.fread "p" "this" "hd";
                           Lang.fread "q" "p" "nxt";
                           Lang.cwhile (BExpr.bneg (BExpr.bequal (^"q") Expr.null))
                               (Lang.assign "p" (^"q");
                                Lang.fread "q" "p" "nxt");
                           Lang.calloc "n" "Node" (^"b"::nil);
                           Lang.fwrite "p" "nxt" (^"n").
 Definition dequeue_cmd := Lang.fread "h" "this" "hd";
                           Lang.fread "p" "h" "nxt";
                           Lang.fread "x" "p" "val";
                           Lang.fread "p" "p" "nxt";
                           Lang.fwrite "h" "nxt" (^"p");
                           Lang.creturn (^"x").
 Definition empty_cmd   := Lang.fread "p" "this" "hd";
                           Lang.fread "p" "p" "nxt";
                           Lang.assignb "b" (BExpr.bequal (^"p") Expr.null);
                           Lang.creturn (^"b").
 
 (* predicates *)
 Fixpoint plist_def (this r1 r2 : ref) (alpha : list ref) : pred :=
     match alpha with
     | nil => r1 ~= r2 /.\ HProp.emp
     | b :: beta => =| (fun r3 => Node.node&r1&r3&b * plist_def this r3 r2 beta)
     end.
 Definition plist : pred := 
     .\(fun this => .\(fun r1 => .\(fun r2 => ,\(fun alpha =>
         plist_def this r1 r2 alpha)))).
 Definition queue : pred := .\(fun this => ,\(fun alpha =>
     =|(fun r_h => this`"hd" |-> r_h * plist&this&r_h&null&`(rfalse::alpha)))).
 
 Definition Queue_spec :=
     (HProp.emp,
      |P|"queue"@"this"&`nil).
 Definition enqueue_spec :=
     (|P|"queue"@"this"&`alpha,
      =|(fun r => |P|"queue"@"this"&`(alpha++r::nil) /.\ "b" +-> r)).
 Definition dequeue_spec :=
     (|P|"queue"@"this"&`(r::alpha),
      |P|"queue"@"this"&`alpha * HProp.htrue /.\ "res" +-> r).
 Definition empty_spec :=
     (|P|"queue"@"this"&`alpha,
      |P|"queue"@"this"&`alpha /.\
          match alpha with | nil => "res" +-> rtrue
                           |  _  => "res" +-> rfalse end).
 
 Definition declare (s : state) : state :=
     State.build_method "Queue" "dequeue" (nil, Bool) nil dequeue_lv dequeue_cmd
     (State.build_method "Queue" "enqueue" (Bool::nil, Null) ("b"::nil) enqueue_lv enqueue_cmd
     (State.build_method "Queue" "empty" (nil, Bool) nil empty_lv empty_cmd
     (State.build_method "Queue" "Queue" (nil, "Queue") nil Queue_lv Queue_cmd
     (State.build_class "Queue" (RType.Object::nil) fields s)))).
End Queue.

Module EQueue. (* Class EQueue *)
 Definition fields      := RType.update_field_type "tl" "Node".
 Definition EQueue_lv   := add_lv "x" "Node" no_lv.
 Definition enqueue_lv  := add_lv "p" "Node" (add_lv "n" "Node" no_lv).
 Definition dequeue_lv  := add_lv "p" "Node" (add_lv "h" "Node"
                          (add_lv "x" "Bool" no_lv)).
 
 Definition EQueue_cmd  := Lang.calloc "x" "Node" (Expr.fals::nil);
                           Lang.fwrite "this" "hd" (^"x");
                           Lang.fwrite "this" "tl" (^"x").
 Definition enqueue_cmd := Lang.fread "p" "this" "tl";
                           Lang.calloc "n" "Node" (^"b"::nil);
                           Lang.fwrite "p" "nxt" (^"n");
                           Lang.fwrite "this" "tl" (^"n").
 Definition dequeue_cmd := Lang.fread "h" "this" "hd";
                           Lang.fread "p" "h" "nxt";
                           Lang.fread "x" "p" "val";
                           Lang.fread "p" "p" "nxt";
                           Lang.fwrite "h" "nxt" (^"p");
                           Lang.cif (BExpr.bequal (^"p") Expr.null)
                               (Lang.fwrite "this" "tl" (^"h"))
                               (Lang.skip);
                           Lang.creturn (^"x").
 
 (* predicates *)
 Definition plist : pred := Queue.plist.
 Definition queue : pred := .\(fun this => ,\(fun alpha =>
     =|(fun r_h => =|(fun r_t => this`"hd" |-> r_h * this`"tl" |-> r_t *
     plist&this&r_h&r_t&`(removelast (rfalse::alpha)) *
     Node.node&r_t&null&(last (rfalse::alpha) rfalse))))).
 
 Definition EQueue_spec := Queue.Queue_spec.
 
 Definition declare (s : state) : state :=
     State.build_method "EQueue" "dequeue" (nil, Bool) nil dequeue_lv dequeue_cmd
     (State.build_method "EQueue" "enqueue" (Bool::nil, Null) ("b"::nil) enqueue_lv enqueue_cmd
     (State.build_method "EQueue" "EQueue" (nil, "EQueue") nil EQueue_lv EQueue_cmd
     (State.build_class "EQueue" ("Queue"::nil) fields s))).
End EQueue.

(* Class Declarations *)
Definition program := EQueue.declare (Queue.declare (Node.declare init_state)).

(* Private Predicates' Environment *)
Definition preds : Spec.pred_env :=
    Spec.update_pred "queue" "EQueue" EQueue.queue
    (Spec.update_pred "plist" "EQueue" EQueue.plist
    (Spec.update_pred "queue" "Queue" Queue.queue
    (Spec.update_pred "plist" "Queue" Queue.plist Spec.init_pred_env))).

(* Specification *)
Definition spec :=
    Spec.add_spec "EQueue" "empty" Queue.empty_spec
    (Spec.add_spec "EQueue" "dequeue" Queue.dequeue_spec
    (Spec.add_spec "EQueue" "enqueue" Queue.enqueue_spec
    (Spec.add_spec "EQueue" "EQueue" EQueue.EQueue_spec
    (Spec.add_spec "Queue" "empty" Queue.empty_spec
    (Spec.add_spec "Queue" "dequeue" Queue.dequeue_spec
    (Spec.add_spec "Queue" "enqueue" Queue.enqueue_spec
    (Spec.add_spec "Queue" "Queue" Queue.Queue_spec
    (Spec.add_spec "Node" "Node" Node.Node_spec Spec.init_program_spec)))))))).

(* Tactics *)
Ltac unfPred := unfold EQueue.plist; unfold Queue.plist; param2;
                unfold Queue.plist_def; param2.
Ltac unfNode := unfold Node.node; param2.
Ltac Unfold  := unfold Spec.program_satisfy; unfold program at 1;
                unfold EQueue.declare; unfold Queue.declare; unfold Node.declare.

(* prove the properties of the predicates *)
Lemma node_this_not_null : forall this r1 r2 : ref,
    Node.node&this&r1&r2 = ~` this ~= null /.\ Node.node&this&r1&r2.
Proof.
  intros this r1 r2; unfNode; simpl.
  apply HProp.equal_1; unfold HProp.eeq; unfEval.
  intros h s se; split. intro H. split; [|assumption].
  destruct H as [h1 [h2 [H [H0 [H1 H2]]]]]. intro H3.
  rewrite H3 in H1. rewrite <- Heap.equal_3 in H1.
  assert (Heap.pin null "val" r2 h1).
  rewrite H1; apply Heap.in_update_1.
  apply Heap.not_in_null in H4; elim H4.
  intros [H H0]; assumption.
Qed.

Lemma plist_cons : forall (this r1 r2 a : ref) (l : list ref),
    Queue.plist&this&r1&r2&`(a::l) =
    =|(fun r3 => Node.node&r1&r3&a * Queue.plist&this&r3&r2&`l).
Proof.
  intros this r1 r2 a l. unfPred.
  apply HProp.func_ext1; intro.
  param2; reflexivity.
Qed.

Lemma plist_app : forall (this r1 r2 : ref) (a b : list ref),
    Queue.plist&this&r1&r2&`(a++b) =
    =|(fun r3 => Queue.plist&this&r1&r3&`a * Queue.plist&this&r3&r2&`b).
Proof.
  intros this r1 r2 a. generalize r1 r2.
  induction a. clear r1 r2; intros r1 r2 b.
  unfold Queue.plist. param2.
  assert (Queue.plist_def this r1 r2 (nil ++ b) = =| (fun r3 =>
    Queue.plist_def this r1 r3 nil * Queue.plist_def this r3 r2 b)).
  apply HProp.equal_1; unfold HProp.eeq.
  unfold HProp.eval; fold HProp.eval. rewrite app_nil_l.
  intros h s se; split. intro H.
  exists r1; exists {}%heap; exists h.
  split. apply Heap.pdisjoint_sym; apply Heap.pdisjoint_empty.
  split. apply Heap.equal_3; apply Heap.union_emp.
  split; [split; [reflexivity|apply Heap.eq_refl] | assumption].
  intros [r [h1 [h2 [H [H0 [[H1 H2] H3]]]]]].
  apply Heap.equal_3 in H2. rewrite H2 in H0.
  assert (h = h2). rewrite H0. apply Heap.equal_3.
  apply Heap.union_emp. rewrite H4.
  rewrite H1; assumption. rewrite H; clear H.
  apply HProp.func_ext1; intro.
  param2; reflexivity.
  clear r1 r2; intros r1 r2 b; rewrite <- app_comm_cons.
  assert (=|(fun r3 => Queue.plist&this&r1&r3&`(a :: a0) *
                       Queue.plist&this&r3&r2&`b)
        = =|fun r3 => (=|(fun r4 => Node.node&r1&r4&a * Queue.plist&this&r4&r3&`a0)) *
                       Queue.plist&this&r3&r2&`b).
  apply HProp.func_ext1.
  intro; rewrite plist_cons; reflexivity.
  rewrite H; clear H. rewrite plist_cons.
  assert (=|(fun r3 => Node.node&r1&r3&a * Queue.plist&this&r3&r2&`(a0 ++ b))
  = =|(fun r3 => Node.node&r1&r3&a * =| (fun r4 =>
      Queue.plist&this&r3&r4&`a0 * Queue.plist&this&r4&r2&`b))).
  apply HProp.func_ext1; intro. rewrite IHa. reflexivity.
  rewrite H; clear H; clear IHa.
  assert (=|(fun r3 => Node.node&r1&r3&a * (=| (fun r4 =>
    Queue.plist&this&r3&r4&`a0 * Queue.plist&this&r4&r2&`b))) =
    =|(fun r3 => (=| (fun r4 => Node.node&r1&r3&a *
    Queue.plist&this&r3&r4&`a0 * Queue.plist&this&r4&r2&`b)))).
  apply HProp.func_ext1; intro; exc. apply HProp.func_ext1.
  intro r3; assoSC. reflexivity.
  rewrite H; clear H. rewrite HProp.exist_comm.
  do 2 (apply HProp.func_ext1; intro; exc). reflexivity.
Qed.

Lemma plist_nil : forall (r1 : ref) (a : list ref),
    Queue.plist&r1&null&null&`a = (HProp.list_eq a nil) /.\ HProp.emp.
Proof.
  intros r1 a; case a. unfPred.
  rewrite HProp.list_eq_refl.
  apply HProp.equal_1; unfold HProp.eeq; intros h s se.
  simpl; split; intros [H H0];
  try split; (assumption||reflexivity).
  intros r0 l; unfPred.
  apply HProp.equal_1; unfold HProp.eeq.
  intros h s se; split; simpl.
  intro H. repeat destruct H.
  destruct H0 as [H0 [H1 H2]]; elim H1.
  intros [H H0]. case l in H; elim H.
Qed.

Lemma plist_false : forall (r1 r2 r3 : ref) (p : HProp.hprop),
    ~` (r2 ~= r3) /.\ p * Queue.plist&r1&r2&r3&`nil = HProp.hfalse.
Proof.
  intros r1 r2 r3 p. unfPred.
  apply HProp.equal_1; unfold HProp.eeq; intros h s se.
  simpl; split. intros [H0 [h1 [h2 [H1 [H2 [H3 [H4 H5]]]]]]].
  elim H0; assumption.
  intro H0; elim H0.
Qed.

(* the predicates "node" and "plist" contain no free variable *)
Lemma node_dsj : forall (this r1 r2 : ref) (md : Sset.t),
    sset_dsj md (HProp.fv (Node.node&this&r1&r2)).
Proof.
  unfold Node.node; unfold HProp.fv.
  intros; rewrite sset_dsj_union. split; freevar.
Qed.

Lemma plist_dsj : forall (l : list ref) (this r1 r2 : ref) (md : Sset.t),
    sset_dsj md (HProp.fv (Queue.plist_def this r1 r2 l)).
Proof.
  induction l. unfold Queue.plist_def; unfold HProp.fv.
  intros; rewrite sset_dsj_union. split; freevar.
  unfold Queue.plist_def; fold Queue.plist_def.
  unfold HProp.fv; fold HProp.fv. intros;
  rewrite sset_dsj_union. split; [|apply IHl].
  unfold Node.node. unfold HProp.fv.
  rewrite sset_dsj_union. split; freevar.
Qed.

Lemma equeue_not_null : forall x y r1 r2 r3,
    Queue.plist&r1&r2&r3&`x * Node.node&r3&null&y
  = ~` (r2 ~= null) /.\ Queue.plist&r1&r2&r3&`x * Node.node&r3&null&y.
Proof.
  intros x y r1 r2 r3; case x. unfPred.
  repeat rewrite <- HProp.stack_sep_conj1; sprop.
  rewrite HProp.sep_conj_emp2. commC; assoC.
  rewrite HProp.eqref_subst with (rhp := fun r =>
    ~` r ~= null /.\ Node.node&r3&null&y).
  rewrite <- node_this_not_null; reflexivity.
  intros r0 l. rewrite plist_cons. exc.
  apply HProp.func_ext1; intro r4. sepconj.
  rewrite <- node_this_not_null; reflexivity.
Qed.

(* Method Node.Node(b) satisfies its specification *)
Lemma node_node_valid : program + preds |> spec # "Node","Node".
Proof.
  (* Unfold the predicate *)
  Simpl. repeat param2. rewrite HProp.sep_conj_emp2.
  (* Prove the method body satisfies its specification *)
  apply Spec.h_seq with (q := "b" +-> r0 /.\ "this" +-> r1 /.\
    r1`"val" |-> r0 * r1`"nxt" |-> null). commSC; frame.
  apply (Spec.h_cons_2 ("b" +-> r0 /.\ "this" +-> r1 /.\ r1`"val" |-> rfalse)).
  impConj. do 2 (commC1 ("b" +-> r0)). do 2 assoC'. mut "b".
  commSC; frame. commC1 ("b" +-> r0); frame'.
  assert (r1`"nxt" |-> null = r1`"nxt" |-> null /.\ Expr.null |=> null).
  apply HProp.equal_1; unfold HProp.eeq; simpl.
  intros; split; intro. split; [assumption|reflexivity].
  destruct H; assumption.
  rewrite H; apply Spec.h_mut.
Qed.

Lemma new_node1 : forall (t : RType.rtype) (x : Name.name),
    program + preds, t |- (HProp.emp, Node.node&^x&null&rfalse)
    # Lang.calloc x "Node" (Expr.fals::nil).
Proof.
  intros t x.
  assert ((HProp.emp, Node.node&^x&null&rfalse)
      <<= (Spec.subst_args2 HProp.emp (MEnv.get_args ("b"::nil, MEnv.no_locvars,
            Some Node.Node_cmd)) (Expr.fals::nil), HProp.subst_name_3 "this" x
              (Spec.subst_args2 (Node.node&^"this"&null&^"b") (MEnv.get_args
                ("b"::nil, MEnv.no_locvars, Some Node.Node_cmd)) (Expr.fals::nil)))).
  unfNode; simpl. param2. apply Spec.refine_cons1. eximpl1.
  rewrite HProp.param_arg. case (Ref.eq_dec r0 rfalse).
  intro; subst. impConj.
  intro. assert (Expr.fals |=> r0 = HProp.hfalse).
  apply HProp.equal_1; unfold HProp.eeq; unfEval.
  intros. split. intro; elim n; assumption.
  intro H; elim H. rewrite H. rewrite HProp.conj_false_l.
  apply HProp.false_impl. apply H; clear H.
  apply Spec.h_new with (ps := spec).
  apply Spec.spec_get_add_2; left; discriminate.
  Unfold; do 9 mbody. apply State.find_mbody_1.
Qed.

Lemma new_node2 : forall (t : RType.rtype) (x y : Name.name),
    y <> "this" ->
    program + preds, t |- (HProp.emp, Node.node&^x&null&^y)
    # Lang.calloc x "Node" (^y::nil).
Proof.
  intros t x y H.
  assert ((HProp.emp, Node.node&^x&null&^y)
      <<= (Spec.subst_args2 HProp.emp (MEnv.get_args ("b"::nil, MEnv.no_locvars,
            Some Node.Node_cmd)) (^y::nil), HProp.subst_name_3 "this" x
              (Spec.subst_args2 (Node.node&^"this"&null&^"b") (MEnv.get_args
                ("b"::nil, MEnv.no_locvars, Some Node.Node_cmd)) (^y::nil)))).
  unfNode; simpl. rewrite <- Name.equal_1 in H.
  rewrite Bool.not_true_iff_false in H.
  rewrite H. param2. apply Spec.refine_cons1.
  eximpl1; eximpl2 r0; param2.
  eximpl1; eximpl2 r1.
  rewrite HProp.var_exp; apply HProp.eimpl_refl.
  apply H0; clear H0.
  apply Spec.h_new with (ps := spec).
  apply Spec.spec_get_add_2; left; discriminate.
  Unfold; do 9 mbody. apply State.find_mbody_1.
Qed.

Lemma queue_queue_valid : program + preds |> spec # "Queue","Queue".
Proof.
  Simpl. unfold Queue.queue; param2. rewrite HProp.sep_conj_emp2.
  apply (Spec.h_cons_2 ("this" +-> r0 /.\ r0`"hd" |-> null)). impConj.
  apply Spec.h_seq with (q := "this" +-> r0 /.\ r0`"hd" |-> null *
                              Node.node&^"x"&null&rfalse).
  rewrite <- (HProp.sep_conj_emp1 ("this" +-> r0 /.\ r0`"hd" |-> null)).
  sepconj. do 2 (commSC1 ("this" +-> r0 /.\ r0`"hd" |-> null)).
  apply Spec.h_frame. apply sset_dsj_card; eauto.
  apply new_node1. unfPred. unfNode; repeat param2. exconj2 null.
  rewrite HProp.eqref_refl. rewrite HProp.conj_true_l.
  rewrite HProp.sep_conj_emp1. unfNode.
  rewrite HProp.stack_sep_conj3; sepconj. frame. commC1 ("x" +-> r1).
  apply Spec.h_cons_1 with (p2 := "this" +-> r0 /.\ r0`"hd" |-> r1 /.\ "x" +-> r1).
  impConj. mut "x".
Qed.

Lemma queue_enqueue_valid : program + preds |> spec # "Queue","enqueue".
Proof.
  Simpl. unfold Queue.queue; repeat param2. unfold Queue.enqueue_cmd.
  apply Spec.h_seq with (q := "b" +-> r0 /.\ "this" +-> r1 /.\ "p" +-> r2 /.\
    r1`"hd" |-> r2 * Queue.plist&r1&r2&null&`(rfalse::alpha)). frame.
  do 2 (commC1 ("b" +-> r0)); frame'. commC1 ("p" +-> r2); lkp.
  apply Spec.h_seq with (q := =|(fun r3 => "b" +-> r0 /.\
    "this" +-> r1 /.\ "p" +-> r2 /.\ "q" +-> r3 /.\
    r1`"hd" |-> r2 * Node.node&r2&r3&rfalse * Queue.plist&r1&r3&null&`alpha)).
  rewrite plist_cons. exconj. do 2 (commC1 ("b" +-> r0)); frame'.
  do 2 (commC1 ("this" +-> r1)); frame'. sepconj. assoSC; frame.
  do 2 (commSC2 (Node.node&r2&r3&rfalse)); frame.
  unfNode. commSC; frame. commC1 ("q" +-> r3); assoC'; lkp.
  assert (~` ' BExpr.bneg (BExpr.bequal (^"q") Expr.null) = "q" +-> null) as HB.
  apply HProp.equal_1; unfold HProp.eeq; unfEval.
  intros h s se; split. case (Stack.get "q" s).
  intro r3; rewrite Bool.not_true_iff_false.
  intro H; apply Bool.negb_false_iff in H.
  apply Ref.equal_1 in H; apply Ref.equal_2 in H; rewrite <- H; reflexivity.
  intro H; elim H; eauto. intro H; rewrite H.
  apply Bool.not_true_iff_false; apply Bool.negb_false_iff; apply Ref.beq_refl.
  apply Spec.h_seq with (q := =|(fun rp => E|(fun beta => =|(fun c =>
    "b" +-> r0 /.\ "this" +-> r1 /.\ "p" +-> rp /.\ "q" +-> null /.\ 
    (HProp.list_eq (rfalse::alpha) (beta++(c::nil))) /.\
    r1`"hd" |-> r2 * Queue.plist&r1&r2&rp&`beta * Node.node&rp&null&c)))).
  apply (Spec.h_cons_2 (=|(fun rp => =|(fun rq => =|(fun c => E|(fun beta =>
    E|(fun gamma => "b" +-> r0 /.\ "this" +-> r1 /.\ "p" +-> rp /.\ "q" +-> rq /.\
    (HProp.list_eq (rfalse::alpha) (beta++(c::gamma))) /.\ r1 ` "hd" |-> r2 *
    Queue.plist&r1&r2&rp&`beta * Node.node&rp&rq&c * Queue.plist&r1&rq&null&`gamma))))))).
  eximpl1; eximpl2 r2; eximpl2 r3; eximpl2 rfalse;
  eximpl4 (nil (A := ref)); eximpl4 alpha.
  impConj. rewrite app_nil_l. rewrite HProp.list_eq_refl.
  rewrite HProp.conj_true_l.
  unfold Queue.plist at 2; param2;
  unfold Queue.plist_def; param2.
  rewrite HProp.eqref_refl. rewrite HProp.conj_true_l.
  rewrite HProp.sep_conj_emp1. apply HProp.eimpl_refl.
  apply Spec.h_cons_1 with (p2 := (=|(fun rp => =|(fun rq => =|(fun c => E|(fun beta =>
    E|(fun gamma => "b" +-> r0 /.\ "this" +-> r1 /.\ "p" +-> rp /.\ "q" +-> rq /.\
    (HProp.list_eq (rfalse::alpha) (beta++(c::gamma))) /.\ r1 ` "hd" |-> r2 *
    Queue.plist&r1&r2&rp&`beta * Node.node&rp&rq&c * Queue.plist&r1&rq&null&`gamma))))))
    /.\ ~` '(BExpr.bneg (BExpr.bequal (^"q") Expr.null))).
  do 3 eximpl1; eximpl2 r3; do 2 eximpl3;
  eximpl4 (removelast (rfalse :: alpha));
  eximpl2 (last (rfalse :: alpha) rfalse).
  rewrite <- app_removelast_last. 2 : discriminate.
  rewrite HProp.list_eq_refl. rewrite HProp.conj_true_l.
  rewrite HB. repeat assoC'. impConj. commC1 ("q" +-> r4).
  repeat assoC'. rewrite HProp.eqvar_eqref. repeat assoC.
  rewrite <- HProp.eqref_subst with (rhp := fun r =>
    ((HProp.list_eq (rfalse :: alpha) (l ++ r5 :: l0) /.\ r1`"hd" |-> r2 *
    Queue.plist&r1&r2&r3&`l * Node.node&r3&r&r5 * Queue.plist&r1&r&null&`l0)
     /.\ "q" +-> null)).
  apply HProp.eimpl_trans with (hp2 := (HProp.list_eq (rfalse :: alpha)
    (l ++ r5 :: l0) /.\ r1`"hd" |-> r2 * Queue.plist&r1&r2&r3&`l *
    Node.node&r3&null&r5 * Queue.plist&r1&null&null&`l0) /.\ "q" +-> null).
  impConj. commC2 ("q" +-> null).
  impConj. apply HProp.list_eq_ext; intro H.
  rewrite plist_nil. rewrite HProp.stack_sep_conj3; sprop.
  apply HProp.list_eq_ext; intro H0.
  rewrite HProp.sep_conj_emp1. rewrite H0 in H.
  rewrite H. rewrite removelast_app. unfold removelast.
  rewrite app_nil_r. assert (forall l, last (l++r5::nil) rfalse = r5).
  induction l1. simpl; reflexivity. rewrite <- app_comm_cons.
  rewrite <- IHl1 at 2. unfold last at 1; fold last.
  assert (exists x y, l1 ++ r5 :: nil = x :: y).
  case l1. exists r5; exists nil; reflexivity.
  intros r6 l2; exists r6; exists (l2 ++ r5 :: nil).
  apply app_comm_cons. destruct H1 as [x [y H1]]; rewrite H1 at 1.
  reflexivity. rewrite H1; apply HProp.eimpl_refl. discriminate.
  apply Spec.h_iter. do 3 exconj1; exconj2 r4; do 2 exconj3.
  assert ((exists x y, l0 = x :: y) \/ l0 = nil).
  case l0; eauto. destruct H as [[x [y H]] | H].
  rewrite H. unfold Queue.plist at 2; param2.
  unfold Queue.plist_def; fold Queue.plist_def.
  exconj1; exconj2 r6; exconj2 x; exconj4 (l++r5::nil); exconj4 y.
  apply (Spec.h_cons_2 ("b" +-> r0 /.\ "this" +-> r1 /.\ "p" +-> r3 /.\
    "q" +-> r4 /.\ HProp.list_eq (rfalse :: alpha) (l ++ r5 :: x :: y) /.\
    r1`"hd" |-> r2 * Queue.plist&r1&r2&r3&`l * Node.node&r3&r4&r5 *
    (Node.node&r4&r6&x * Queue.plist_def r1 r6 null y))). impConj.
  do 2 (commC1 ("b" +-> r0)); frame'.
  do 2 (commC1 ("this" +-> r1)); frame'. sepconj; assoSC.
  unfold Queue.plist at 3; param2.
  apply Spec.h_frame. apply plist_dsj.
  rewrite plist_app. exconj2 r3.
  unfold Queue.plist at 3; param2.
  unfold Queue.plist_def; param2. exconj2 r4.
  rewrite HProp.eqref_refl. rewrite HProp.conj_true_l.
  rewrite HProp.sep_conj_emp1. do 2 (commSC2 (Node.node&r4&r6&x)).
  repeat assoSC. apply Spec.h_frame. apply node_dsj.
  apply Spec.h_frame. unfold Queue.plist; param2; apply plist_dsj.
  rewrite <- app_assoc. rewrite <- app_comm_cons.
  rewrite app_nil_l. frame.
  do 2 (commC1 (HProp.list_eq (rfalse::alpha) (l++r5::x::y))).
  apply Spec.h_frame'; try apply HProp.list_eq_dsj; sprop.
  unfNode; commSC; frame.
  apply Spec.h_seq with (q := "q" +-> r4 /.\ "p" +-> r4 /.\ r4`"nxt" |-> r6).
  apply Spec.h_asn; simpl. rewrite HProp.var_exp.
  repeat assoC; rewrite HProp.conj_refl; impConj.
  apply (Spec.h_cons_2 ("p" +-> r4 /.\ r4 ` "nxt" |-> r6)). impConj.
  commC1 ("q" +-> r6); assoC'; lkp. rewrite H.
  apply eq_sym in HB; apply HProp.neg_sym in HB.
  rewrite HB. apply (Spec.h_cons_2 (("q" +-> r4 /.\ HProp.list_eq (rfalse::alpha)
    (l ++ r5 :: nil) /.\ r1`"hd" |-> r2 * Queue.plist&r1&r2&r3&`l *
    Node.node&r3&r4&r5 * Queue.plist&r1&r4&null&`nil) /.\ ~` "q" +-> null)).
  repeat assoC'; do 2 assoC; commC; impConj.
  commC; repeat assoC; rewrite HProp.eqvar_eqref2.
  apply (Spec.h_cons_2 (~` null ~= r4 /.\ r1`"hd" |-> r2 * Queue.plist&r1&r2&r3&`l
    * Node.node&r3&r4&r5 * Queue.plist&r1&r4& null&`nil)).
  impConj; assoC'; impConj. rewrite HProp.eqref_sym.
  rewrite plist_false. apply Spec.h_contrad.
  exconj1; exconj3; exconj1.
  commC1 (HProp.list_eq (rfalse::alpha) (l++r4::nil)).
  repeat assoC; apply Spec.list_eq_ext; intro H; repeat assoC'.
  rewrite app_comm_cons.
  apply Spec.h_cons_1 with (p2 := "this" +-> r1 /.\ r1`"hd" |-> r2 *
    Queue.plist&r1&r2&null&`((l++r4::nil)++r0::nil) /.\ "b" +-> r0).
  impConj. rewrite <- H. apply HProp.eimpl_refl. clear H.
  rewrite <- app_assoc. rewrite <- app_comm_cons.
  rewrite app_nil_l. rewrite plist_app. exconj2 r3.
  commC2 ("b" +-> r0); assoSC'.
  do 2 (commSC1 (Queue.plist&r1&r2&r3&`l)); sepconj.
  repeat assoSC; frame. assoC; commC1 ("b" +-> r0).
  repeat assoC'; sepsep.
  do 2 (commC1 ("this" +-> r1)); frame'.
  do 2 (commSC1 (r1`"hd" |-> r2)); frame.
  apply (Spec.h_cons_2 ("b" +-> r0 /.\ "p" +-> r3 /.\ Node.node&r3&null&r4)).
  impConj. rewrite plist_cons.
  apply Spec.h_seq with (q := ("b" +-> r0 /.\ "p" +-> r3 /.\
    Node.node&r3&null&r4) * Node.node&^"n"&null&^"b").
  apply (Spec.h_cons_2 (("b" +-> r0 /.\ "p" +-> r3 /.\ Node.node&r3&null&r4) * HProp.emp)).
  rewrite HProp.sep_conj_emp1; apply HProp.eimpl_refl.
  do 2 (commSC1 ("b" +-> r0 /.\ "p" +-> r3 /.\ Node.node&r3&null&r4)).
  apply Spec.h_frame; try apply sset_dsj_card; eauto.
  apply new_node2; discriminate.
  assert (Node.node &^"n"&null&^"b" = =|(fun r1 => =|(fun r2 =>
    "n" +-> r1 /.\ "b" +-> r2 /.\ Node.node&r1&null&r2))).
  unfNode; rewrite HProp.param_ext.
  rewrite HProp.param_arg2. rewrite HProp.exist_comm.
  apply HProp.func_ext1; intro. exc.
  apply HProp.func_ext1; intro. param2.
  assoC; commC1 ("b" +-> r5); assoC'; reflexivity.
  rewrite H; clear H. exconj; exconj1.
  rewrite plist_cons. param2. exconj2 null.
  rewrite plist_nil. rewrite HProp.list_eq_refl.
  rewrite HProp.conj_true_l. rewrite HProp.sep_conj_emp1.
  sepconj. do 2 assoC; commC2 ("b" +-> r0); repeat assoC.
  rewrite HProp.eqvar_eqref; commC2 (r0 ~= r6).
  repeat assoC'; commSC; rewrite HProp.stack_sep_conj3; sprop. commC.
  rewrite <- HProp.eqref_subst with (rhp := fun r => Node.node&r5&null&r *
    ("b" +-> r0 /.\ "n" +-> r5 /.\ "p" +-> r3 /.\ Node.node&r3&null&r4)).
  apply (Spec.h_cons_2 (Node.node&r5&null&r0 * ("b" +-> r0 /.\ "n" +-> r5
    /.\ "p" +-> r3 /.\ Node.node&r3&null&r4))). impConj.
  commSC; frame. do 2 (commC1 ("b" +-> r0)); frame'.
  unfNode; do 2 (commSC1 (r3`"val" |-> r4)); frame. commC; assoC'.
  apply Spec.h_cons_1 with (p2 := "p" +-> r3 /.\ r3`"nxt" |-> r5 /.\ "n" +-> r5).
  commC; assoC'; impConj. mut "n". bs.
Qed.

Lemma queue_dequeue_valid : program + preds |> spec # "Queue","dequeue".
Proof.
  Simpl. unfold Queue.queue; repeat param2. unfold Queue.dequeue_cmd.
  apply Spec.h_seq with (q := "this" +-> r0 /.\ "h" +-> r1 /.\ r0`"hd" |-> r1
    * Queue.plist&r0&r1&null&`(rfalse::r::alpha)). frame.
  commC1 ("h" +-> r1); lkp.
  rewrite plist_cons. exconj1. sepsep; assoC'.
  do 2 (commC1 ("this" +-> r0)); frame'.
  assoSC'; do 2 (commSC1 (r0`"hd" |-> r1)); frame.
  apply Spec.h_seq with (q := "h" +-> r1 /.\ "p" +-> r2 /.\
    Node.node&r1&r2&rfalse * Queue.plist&r0&r2&null&`(r::alpha)).
  frame. unfNode; commSC; frame. commC1 ("p" +-> r2); lkp.
  rewrite plist_cons; exconj1; assoSC.
  commSC1 (Node.node&r1&r2&rfalse); assoSC'.
  apply Spec.h_seq with (q := "h" +-> r1 /.\ "p" +-> r2 /.\
    "x" +-> r /.\ Node.node&r2&r3&r *
    (Node.node&r1&r2&rfalse * Queue.plist&r0&r3&null&`alpha)).
  frame. do 2 (commC1 ("h" +-> r1)); frame'.
  unfNode. frame. commC1 ("x" +-> r); lkp.
  rewrite plist_cons; exconj2 r3. commSC2 HProp.htrue.
  sepconj; repeat assoSC. apply Spec.h_frame; freevar.
  apply Spec.h_seq with (q := ("h" +-> r1 /.\ "p" +-> r3 /.\
    "x" +-> r /.\ Node.node&r2&r3&r) * Node.node&r1&r2&rfalse).
  frame. do 2 (commC1 ("h" +-> r1)); frame'.
  commC1 ("x" +-> r); do 2 assoC; frame'.
  unfNode; commSC; frame. apply Spec.h_lkp'.
  apply Spec.h_cons_1 with (p2 := Node.node&r2&r3&r * (Node.node&r1&r3&rfalse
    /.\ "res" +-> r)). impConj; apply HProp.impl_true.
  sepsep. do 2 (commSC1 (Node.node&r2&r3&r)); frame.
  commC2 ("res" +-> r); unfNode.
  do 2 (commSC1 (r1`"val" |-> rfalse)); frame.
  apply Spec.h_seq with (q := "h" +-> r1 /.\ "p" +-> r3 /.\
    "x" +-> r /.\ r1`"nxt" |-> r3).
  do 2 (commC1 ("x" +-> r)); repeat assoC; frame'.
  do 2 assoC'; do 2 (commC1 ("p" +-> r3)). mut "p".
  apply Spec.h_res; simpl. rewrite HProp.var_exp; assoC; impConj. bs.
Qed.

Lemma queue_empty_valid : program + preds |> spec # "Queue","empty".
Proof.
  Simpl. unfold Queue.queue; repeat param2. unfold Queue.empty_cmd.
  apply Spec.h_seq with (q := "this" +-> r0 /.\ "p" +-> r1 /.\
    r0`"hd" |-> r1 * Queue.plist&r0&r1&null&`(rfalse::alpha)).
  frame. commC1 ("p" +-> r1); lkp.
  assoC'; do 2 (commC1 ("this" +-> r0)); frame'.
  rewrite plist_cons; exconj; commSC.
  commC1 (Node.node&r1&r2&rfalse * Queue.plist&r0&r2&null&`alpha * r0`"hd" |-> r1).
  sepconj; try (case alpha; intros; sprop; fail). frame.
  apply Spec.h_seq with (q := ("p" +-> r2 /.\
    Node.node&r1&r2&rfalse) * Queue.plist&r0&r2&null&`alpha).
  frame. unfNode; commSC; frame. apply Spec.h_lkp'.
  case alpha; simpl. unfPred.
  do 2 try rewrite HProp.stack_sep_conj3; sprop.
  do 2 (commC1 (r2 ~= null)); do 2 rewrite HProp.sep_conj_emp1.
  rewrite HProp.eqref_subst with (rhp := fun r =>
    "p" +-> r /.\ Node.node&r1&r&rfalse).
  rewrite HProp.eqref_subst with (rhp := fun r =>
    "res" +-> rtrue /.\ Node.node&r1&r&rfalse). frame'.
  apply Spec.h_seq with (q := "b" +-> rtrue /.\ Node.node&r1&null&rfalse).
  apply Spec.h_asnb; unfNode; simpl; impConj.
  unfold HProp.eimpl; unfEval;
  intros h s se H; rewrite H; apply Ref.beq_refl.
  apply Spec.h_res; unfNode; simpl.
  rewrite HProp.var_exp; impConj.
  intros r3 l. rewrite plist_cons; exconj. do 2 assoSC; frame.
  sepsep; commSC; frame.
  apply Spec.h_seq with (q := "b" +-> rfalse /.\ Node.node&r2&r4&r3).
  apply Spec.h_asnb; rewrite node_this_not_null.
  unfNode; simpl; do 2 assoC; apply HProp.impl_conj1.
  unfold HProp.eimpl; unfEval;
  intros h s se [H H0]; split; [|assumption].
  rewrite H; apply Bool.negb_true_iff;
  apply Bool.not_true_iff_false; intro H1; elim H0.
  apply eq_sym; apply Ref.equal_2; apply Ref.equal_1; assumption.
  apply Spec.h_res; unfNode; simpl. rewrite HProp.var_exp; impConj. bs.
Qed.

Lemma equeue_equeue_valid : program + preds |> spec # "EQueue","EQueue".
Proof.
  Simpl. unfold EQueue.queue; param2. rewrite HProp.sep_conj_emp2.
  apply (Spec.h_cons_2 ("this" +-> r0 /.\ r0`"hd" |-> null *
    r0`"tl" |-> Ref.rnull)). impConj.
  apply Spec.h_seq with (q := "this" +-> r0 /.\ r0`"hd" |-> null *
    r0`"tl" |-> null * Node.node&^"x"&null&rfalse).
  rewrite <- (HProp.sep_conj_emp1 ("this" +-> r0 /.\
    r0`"hd" |-> null * r0`"tl" |-> Ref.rnull)). sepconj.
  do 2 (commSC1 (("this" +-> r0 /.\ r0`"hd" |-> null) * r0`"tl" |-> Ref.rnull)).
  apply Spec.h_frame. apply sset_dsj_card; eauto.
  apply new_node1. unfold last; unfold removelast.
  unfNode. rewrite HProp.param_ext. param2. exconj2 r1; param2.
  unfPred. rewrite HProp.eqref_refl. rewrite HProp.conj_true_l.
  rewrite HProp.sep_conj_emp1. rewrite HProp.stack_sep_conj3; frame.
  apply Spec.h_seq with (q := ("this" +-> r0 /.\ "x" +-> r1 /.\ r0`"hd" |-> r1) *
    r0`"tl" |-> null). frame.
  do 2 (commC1 ("x" +-> r1)). mut "x".
  sepsep; do 2 (commSC1 (r0`"hd" |-> r1)); frame. commC1 ("x" +-> r1).
  apply Spec.h_cons_1 with (p2 := "this" +-> r0 /.\ r0`"tl" |-> r1 /.\ "x" +-> r1).
  impConj. mut "x".
Qed.

Lemma equeue_enqueue_valid : program + preds |> spec # "EQueue","enqueue".
Proof.
  Simpl. unfold EQueue.queue; do 3 param2; exconj1.
  apply Spec.h_seq with (q := "b" +-> r0 /.\ "p" +-> r3 /.\ "this" +-> r1 /.\
    r1`"hd" |-> r2 * r1`"tl" |-> r3 * EQueue.plist&r1&r2&r3&`removelast
    (rfalse::alpha) * Node.node&r3&null&last (rfalse::alpha) rfalse).
  commSC1 (r1`"hd" |-> r2); repeat frame.
  do 2 (commC1 ("b" +-> r0)); frame'. commC1 ("p" +-> r3); assoC'; lkp.
  apply Spec.h_seq with (q := ("b" +-> r0 /.\ "p" +-> r3 /.\ "this" +-> r1 /.\
    r1`"hd" |-> r2 * r1`"tl" |-> r3 * EQueue.plist&r1&r2&r3&`removelast (rfalse::alpha) *
    Node.node&r3&null&last (rfalse::alpha) rfalse) * Node.node&^"n"&null&^"b").
  apply (Spec.h_cons_2 (("b" +-> r0 /.\ "p" +-> r3 /.\ "this" +-> r1 /.\
    r1`"hd" |-> r2 * r1`"tl" |-> r3 * EQueue.plist&r1&r2&r3&`removelast (rfalse::alpha) *
    Node.node&r3&null&last (rfalse::alpha) rfalse) * HProp.emp)).
  rewrite HProp.sep_conj_emp1; apply HProp.eimpl_refl.
  commSC; commSC2 (Node.node&^"n"&null&^"b").
  apply Spec.h_frame; try apply sset_dsj_card; eauto.
  apply new_node2; discriminate.
  assert (Node.node &^"n"&null&^"b" = =|(fun r1 => =|(fun r2 =>
    "n" +-> r1 /.\ "b" +-> r2 /.\ Node.node&r1&null&r2))).
  unfNode; rewrite HProp.param_ext; rewrite HProp.param_arg2.
  rewrite HProp.exist_comm.
  apply HProp.func_ext1; intro. exc.
  apply HProp.func_ext1; intro. param2.
  assoC; commC1 ("b" +-> r4); assoC'; reflexivity.
  rewrite H; clear H. exconj; exconj1.
  rewrite app_comm_cons; rewrite removelast_app; try discriminate.
  unfold removelast at 2; rewrite app_nil_r.
  sepconj; do 2 assoC; do 2 (commC2 ("b" +-> r0)).
  repeat assoC; rewrite HProp.eqvar_eqref; commC1 ("b" +-> r0).
  repeat assoC'; sepsep. commC.
  rewrite <- HProp.eqref_subst with (rhp := fun r => "b" +-> r0 /.\ "n" +-> r4 /.\
    "p" +-> r3 /.\ "this" +-> r1 /.\ r1`"hd" |-> r2 * r1`"tl" |-> r3 *
    EQueue.plist&r1&r2&r3&`removelast (rfalse::alpha) *
    Node.node&r3&null&last (rfalse::alpha) rfalse *  Node.node&r4&null&r).
  apply (Spec.h_cons_2 ("b" +-> r0 /.\ "n" +-> r4 /.\ "p" +-> r3 /.\
    "this" +-> r1 /.\ r1`"hd" |-> r2 * r1`"tl" |-> r3 *
    EQueue.plist&r1&r2&r3&`removelast (rfalse::alpha) *
    Node.node&r3&null&last (rfalse::alpha) rfalse * Node.node&r4&null&r0)).
  impConj. do 2 (commC1 ("b" +-> r0)); frame'.
  assert (forall a b : list ref, b <> nil -> last (a++b) = last b).
  induction a; intro b. rewrite app_nil_l. reflexivity.
  assert (forall c, c <> nil -> last (a :: c) = last c).
  intros c H. unfold last. generalize H; case c;
  [intro H0; elim H0|]; reflexivity.
  rewrite <- app_comm_cons. intro H0.
  apply eq_trans with (y := last (a0 ++ b)).
  apply H. intro H1; elim H0. apply app_eq_nil in H1.
  destruct H1; assumption. apply IHa; assumption.
  rewrite H; clear H; try discriminate. unfold last at 2. frame.
  apply Spec.h_cons_1 with (p2 := ("this" +-> r1 /.\ r1`"hd" |-> r2) *
    r1`"tl" |-> r4 * EQueue.plist&r1&r2&r4&`(removelast (rfalse::alpha) ++
    (last (rfalse::alpha) rfalse)::nil)).
  rewrite <- app_removelast_last. impConj. discriminate.
  rewrite plist_app. exconj2 r3.
  unfold Queue.plist at 2; param2.
  unfold Queue.plist_def; param2. exconj2 r4.
  rewrite HProp.eqref_refl; rewrite HProp.conj_true_l;
  rewrite HProp.sep_conj_emp1. assoSC'.
  do 2 (commSC1 (Queue.plist&r1&r2&r3&`removelast (rfalse::alpha))).
  sepconj; repeat assoSC; frame. unfNode.
  do 2 (commSC1 (r3`"val" |-> last (rfalse::alpha) rfalse)).
  repeat assoSC; frame. sepsep; do 2 assoSC'.
  do 2 (commSC1 (r1`"hd" |-> r2)); frame.
  apply Spec.h_seq with (q := ("n" +-> r4 /.\ "this" +-> r1 /.\ r1`"tl" |-> r3)
    * r3`"nxt" |-> r4). sepsep. do 2 (commSC1 (r1`"tl" |-> r3)); frame.
  do 2 (commC1 ("this" +-> r1)); repeat assoC; frame'.
  assoC'; commC; assoC'; commC1 ("n" +-> r4).
  apply Spec.h_cons_1 with (p2 := "p" +-> r3 /.\ r3`"nxt" |-> r4 /.\ "n" +-> r4).
  impConj. mut "n". frame.
  apply Spec.h_cons_1 with (p2 := "n" +-> r4 /.\ "this" +-> r1 /.\ r1`"tl" |-> r4).
  impConj. do 2 (commC1 ("n" +-> r4)); do 2 assoC'. mut "n". bs.
Qed.

Lemma equeue_dequeue_valid : program + preds |> spec # "EQueue","dequeue".
Proof.
  Simpl. case alpha; [|intros r0 l]; unfold EQueue.queue; do 2 param2;
  unfold EQueue.dequeue_cmd. exconj1; exconj2 r1.
  unfold removelast; unfold last. unfPred. exconj1.
  rewrite HProp.eqref_refl. rewrite HProp.conj_true_l.
  rewrite HProp.stack_sep_conj3; sprop.
  do 2 rewrite HProp.sep_conj_emp1. sepconj.
  assoC'; commC1 (r0`"hd" |-> r1); sepsep; commC.
  rewrite HProp.eqref_subst with (rhp := fun r' => "this" +-> r0 /.\ r0`"hd" |-> r1
    * r0`"tl" |-> r2 * Node.node&r1&r'&rfalse * Node.node&r2&null&r).
  apply (Spec.h_cons_2 ("this" +-> r0 /.\ r0`"hd" |-> r1 * r0`"tl" |-> r2
    * Node.node&r1&r2&rfalse * Node.node&r2&null&r)). impConj.
  apply Spec.h_seq with (q := "this" +-> r0 /.\ "h" +-> r1 /.\ r0`"hd" |-> r1 *
    r0`"tl" |-> r2 * Node.node&r1&r2&rfalse * Node.node&r2&null&r).
  repeat frame. commC1 ("h" +-> r1); lkp.
  repeat assoSC'; do 2 (commSC1 (r0`"hd" |-> r1)); frame.
  apply Spec.h_seq with (q := ("this" +-> r0 /.\ "h" +-> r1 /.\ "p" +-> r2 /.\
    r0`"tl" |-> r2) * (Node.node&r1&r2&rfalse * Node.node&r2&null&r)).
  do 2 assoSC; frame. unfNode; sepsep; repeat assoSC.
  commSC2 (r1`"nxt" |-> r2); frame.
  do 2 (commC1 ("this" +-> r0)); frame'. commC1 ("p" +-> r2); lkp.
  apply Spec.h_seq with (q := ("this" +-> r0 /.\ "h" +-> r1 /.\ "p" +-> r2 /.\
    "x" +-> r /.\ r0`"tl" |-> r2) * (Node.node&r1&r2&rfalse * Node.node&r2&null&r)).
  sepsep; assoSC; commSC; frame. unfNode; frame.
  do 2 (commC1 ("this" +-> r0)); frame'.
  do 2 (commC1 ("h" +-> r1)); frame'. commC1 ("x" +-> r); lkp.
  apply Spec.h_seq with (q := ("this" +-> r0 /.\ "h" +-> r1 /.\ "p" +-> null /.\
    "x" +-> r /.\ r0`"tl" |-> r2) * (Node.node&r1&r2&rfalse * Node.node&r2&null&r)).
  sepsep; assoSC; commSC; frame. unfNode; commSC; frame.
  do 2 (commC1 ("this" +-> r0)); frame'.
  do 2 (commC1 ("h" +-> r1)); frame'.
  commC1 ("x" +-> r); do 2 assoC; frame'. apply Spec.h_lkp'.
  apply (Spec.h_cons_2 (("this" +-> r0 /.\ "h" +-> r1 /.\ "p" +-> null /.\
    "x" +-> r /.\ r0`"tl" |-> r2) * (Node.node&r1&r2&rfalse * HProp.htrue))).
  impConj; apply HProp.impl_true. sepsep; do 2 assoSC; frame.
  unfNode; do 2 (commSC1 (r1`"val" |-> rfalse)); do 2 assoSC; frame.
  apply Spec.h_seq with (q := ("this" +-> r0 /.\ "h" +-> r1 /.\ "p" +-> null /.\
    "x" +-> r /.\ r0`"tl" |-> r2) * r1`"nxt" |-> null).
  sepsep; do 2 (commC1 ("this" +-> r0)); frame'.
  do 2 (commSC1 (r0`"tl" |-> r2)); frame.
  do 2 (commC1 ("x" +-> r)); repeat assoC; frame'.
  do 2 assoC'; do 2 (commC1 ("p" +-> null)); mut "p". frame.
  apply Spec.h_seq with (q := "this" +-> r0 /.\ "x" +-> r /.\ r0`"tl" |-> r1).
  do 2 (commC1 ("x" +-> r)); repeat assoC; frame'.
  assoC'; commC1 ("p" +-> null); apply Spec.h_cond1.
  unfold HProp.eimpl; unfEval; intros.
  destruct H as [H0 [H1 H2]]; rewrite H2; apply Ref.beq_refl.
  apply (Spec.h_cons_2 (("this" +-> r0 /.\ "h" +-> r1) /.\ r0`"tl" |-> r2)).
  impConj. assoC'; commC1 ("h" +-> r1).
  apply Spec.h_cons_1 with (p2 := "this" +-> r0 /.\ r0`"tl" |-> r1 /.\ "h" +-> r1).
  impConj. mut "h".
  apply Spec.h_res; simpl. rewrite HProp.var_exp. impConj.
  
  assert (forall (x y : ref) z, removelast (x::y::z) = x::removelast (y::z)).
  unfold removelast; reflexivity. repeat rewrite H; clear H.
  assert (forall (x y : ref) z, last (x::y::z) = last (y::z)).
  unfold last; reflexivity. repeat rewrite H; clear H.
  param2. sepconj. assoC'; commC1 (r1`"hd" |-> r2); sepsep.
  commSC2 HProp.htrue; repeat assoSC.
  do 2 (rewrite plist_cons; exconj1).
  rewrite plist_cons; exconj2 r5. repeat assoSC'.
  rewrite equeue_not_null. repeat assoSC.
  repeat rewrite HProp.stack_sep_conj3; sprop. frame.
  do 3 assoSC'; do 2 (commSC1 (r1`"tl" |-> r3)); repeat assoSC; frame. sepsep.
  apply Spec.h_seq with (q := "this" +-> r1 /.\ ~` r5 ~= null /.\ "h" +-> r2 /.\
    r1`"hd" |-> r2 * Node.node&r2&r4&rfalse * Node.node&r4&r5&r).
  repeat frame. do 2 (commC1 (~` r5 ~= null)); do 2 assoC; frame'.
  commC1 ("h" +-> r2); lkp.
  repeat assoSC'; do 2 (commSC1 (r1`"hd" |-> r2)); repeat assoSC; frame.
  sepsep; do 2 (commC1 ("this" +-> r1)); frame'.
  apply Spec.h_seq with (q := ~` r5 ~= null /.\ "h" +-> r2 /.\
    "p" +-> r4 /.\ Node.node&r2&r4&rfalse * Node.node&r4&r5&r).
  do 2 (commC1 (~` r5 ~= null)); frame'. unfNode.
  commSC1 (r2`"val" |-> rfalse); repeat frame. commC1 ("p" +-> r4); lkp.
  apply Spec.h_seq with (q := ~` r5 ~= null /.\ "h" +-> r2 /.\ "p" +-> r4 /.\
    "x" +-> r /.\ Node.node&r2&r4&rfalse * Node.node&r4&r5&r).
  commSC; unfNode; repeat frame. do 2 (commC1 (~` r5 ~= null)); frame'.
  do 2 (commC1 ("h" +-> r2)); frame'. commC1 ("x" +-> r); lkp.
  apply Spec.h_seq with (q := ~` r5 ~= null /.\ "h" +-> r2 /.\ "p" +-> r5 /.\
    "x" +-> r /.\ Node.node&r2&r4&rfalse * Node.node&r4&r5&r).
  commSC; frame. unfNode; commSC; frame.
  do 2 (commC1 (~` r5 ~= null)); frame'.
  do 2 (commC1 ("h" +-> r2)); frame'.
  commC1 ("x" +-> r); do 2 assoC; frame'. apply Spec.h_lkp'.
  apply (Spec.h_cons_2 (~` r5 ~= null /.\ "h" +-> r2 /.\ "p" +-> r5 /.\
    "x" +-> r /.\ Node.node&r2&r4&rfalse * HProp.htrue)).
  impConj; apply HProp.impl_true. commSC1 HProp.htrue; frame.
  unfNode; do 2 (commSC1 (r2`"val" |-> rfalse)); frame.
  apply Spec.h_seq with (q := ~` r5 ~= null /.\ "h" +-> r2 /.\ "p" +-> r5 /.\
    "x" +-> r /.\ r2`"nxt" |-> r5).
  do 2 (commC1 (~` r5 ~= null)); frame'.
  do 2 (commC1 ("x" +-> r)); repeat assoC; frame'.
  do 2 assoC'; do 2 (commC1 ("p" +-> r5)); mut "p".
  apply (Spec.h_cons_2 (~` r5 ~= null /.\ "p" +-> r5 /.\ "x" +-> r /.\
    r2`"nxt" |-> r5)). impConj.
  apply Spec.h_seq with (q := ~` r5 ~= null /.\ "x" +-> r /.\ r2`"nxt" |-> r5).
  apply Spec.h_cond2. unfold HProp.eimpl; unfEval; intros;
  destruct H as [H [H0 H1]]; rewrite H0; intro H2; elim H.
  apply eq_sym; apply Ref.equal_2; apply Ref.equal_1; assumption.
  apply (Spec.h_cons_2 (~` r5 ~= null /.\ "x" +-> r /.\ r2`"nxt" |-> r5)).
  impConj. apply Spec.h_skip. apply Spec.h_res; simpl.
  rewrite HProp.var_exp; do 2 assoC; commC1 ("x" +-> r); impConj. bs.
Qed.

Lemma equeue_empty_valid : program + preds |> spec # "EQueue","empty".
Proof.
  Simpl. unfold EQueue.queue; repeat param2. unfold Queue.empty_cmd.
  case alpha. simpl. commC2 ("res" +-> rtrue). unfPred.
  rewrite HProp.stack_sep_conj3; sprop. rewrite HProp.sep_conj_emp1.
  sepsep; commC1 (r1 ~= r2); do 2 assoC.
  rewrite HProp.eqref_subst with (rhp := fun r => "this" +-> r0 /.\
    r0`"hd" |-> r * r0`"tl" |-> r2 * Node.node&r2&null&rfalse).
  rewrite HProp.eqref_subst with (rhp := fun r => "res" +-> rtrue /.\
    "this" +-> r0 /.\ r0`"hd" |-> r * r0`"tl" |-> r2 * Node.node&r2&null&rfalse).
  frame'. assoSC'; commSC1 (r0`"tl" |-> r2); assoSC; frame.
  sepsep; commC1 ("res" +-> rtrue); assoC'.
  apply Spec.h_seq with (q := "this" +-> r0 /.\ "p" +-> r2 /.\
    r0`"hd" |-> r2 * Node.node&r2&null&rfalse).
  frame. commC1 ("p" +-> r2); lkp.
  commC2 ("res" +-> rtrue); do 2 (commC1 ("this" +-> r0)); frame'.
  commSC; frame. unfNode; commSC; frame.
  apply Spec.h_seq with (q := "p" +-> null /.\ r2`"nxt" |-> null).
  apply Spec.h_lkp'.
  apply Spec.h_seq with (q := "b" +-> rtrue /.\ r2`"nxt" |-> null).
  apply Spec.h_asnb; simpl.
  unfold HProp.eimpl; unfEval; intros h s se [H H0];
  rewrite H; split; [apply Ref.beq_refl | assumption].
  apply Spec.h_res; simpl; rewrite HProp.var_exp; impConj.
  
  intros r3 l. unfold Spec.evalP. commC2 ("res" +-> rfalse).
  assert (forall (x y : ref) z, removelast (x::y::z) = x::removelast (y::z)).
  unfold removelast; reflexivity. repeat rewrite H; clear H.
  assert (forall (x y : ref) z, last (x::y::z) = last (y::z)).
  unfold last; reflexivity. repeat rewrite H; clear H.
  rewrite plist_cons; exconj. repeat assoSC'.
  rewrite equeue_not_null. repeat rewrite HProp.stack_sep_conj3; sprop.
  do 2 assoSC; frame. repeat assoSC'; commSC1 (r0`"tl" |-> r2).
  repeat assoSC; frame. sepsep.
  apply Spec.h_seq with (q := "this" +-> r0 /.\ "p" +-> r1 /.\
    ~` r4 ~= null /.\ r0`"hd" |-> r1 * Node.node&r1&r4&rfalse).
  frame. commC1 (~` r4 ~= null); repeat assoC; frame'.
  assoC'; commC1 ("p" +-> r1); lkp. commSC; frame.
  repeat assoC; commC1 ("res" +-> rfalse); repeat assoC';
  do 2 (commC1 ("this" +-> r0)); frame'. unfNode; commSC; frame.
  apply Spec.h_seq with (q := "p" +-> r4 /.\ ~` r4 ~= null /.\ r1`"nxt" |-> r4).
  commC1 (~` r4 ~= null); repeat assoC; frame'. apply Spec.h_lkp'.
  apply Spec.h_seq with (q := "b" +-> rfalse /.\ ~` r4 ~= null /.\ r1`"nxt" |-> r4).
  apply Spec.h_asnb; simpl.
  unfold HProp.eimpl; unfEval; intros h s se [H H0];
  rewrite H; split; [| assumption]. apply Bool.negb_true_iff;
  apply Bool.not_true_is_false; destruct H0; intro H2; elim H0.
  apply eq_sym; apply Ref.equal_2; apply Ref.equal_1; assumption.
  apply Spec.h_res; simpl; rewrite HProp.var_exp; impConj. bs.
Qed.

Lemma ON : "Object" = "Node" <-> False.
Proof. split; [discriminate | intro H; elim H]. Qed.
Lemma QN : "Queue" = "Node" <-> False.
Proof. split; [discriminate | intro H; elim H]. Qed.
Lemma QQ : "Queue" = "Queue" <-> True.
Proof. split; eauto. Qed.
Lemma dQ : "dequeue" = "Queue" <-> False.
Proof. split; [discriminate | intro H; elim H]. Qed.
Lemma eQ : "enqueue" = "Queue" <-> False.
Proof. split; [discriminate | intro H; elim H]. Qed.
Lemma emQ : "empty" = "Queue" <-> False.
Proof. split; [discriminate | intro H; elim H]. Qed.
Lemma nQQ : "Queue" <> "Queue" <-> False.
Proof. split; eauto. Qed.

(* The whole program satisfies its specification *)
Lemma verify_queue : program + preds |= spec.
Proof.
  Unfold; mlist. rewrite ON in H;
  rewrite QN in H; rewrite QQ in H. propSimp H.
  rewrite dQ in H; rewrite eQ in H;
  rewrite emQ in H; rewrite nQQ in H. propSimp H.
  mtdSpec equeue_dequeue_valid.
  mtdSpec equeue_enqueue_valid.
  mtdSpec equeue_equeue_valid.
  mtdSpec equeue_empty_valid.
  mtdSpec queue_dequeue_valid.
  mtdSpec queue_enqueue_valid.
  mtdSpec queue_empty_valid.
  mtdSpec queue_queue_valid.
  mtdSpec node_node_valid.
Qed.

Close Scope spec_scope.
Close Scope hprop_scope.
Close Scope lang_scope.
Close Scope string_scope.