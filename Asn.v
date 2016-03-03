Require Export Heap.
Require Export Env.
Require Import Bool.
Require Import Classical_Prop.
Require Import Classical_Pred_Type.
Require Import FunctionalExtensionality.

(*-----  Abstract Data Type  -----*)

(*  HeapAsn Type  *)

Module Type HPROP.

Parameter heap : Type.
Parameter stack : Type.
Parameter name : Type.
Parameter rtype : Type.
Parameter ref : Type.
Parameter expr : Type.
Parameter bexpr : Type.
Parameter dtype : Type.
Parameter super_env : Type.
Parameter fields_env : Type.
Parameter empty_heap : heap.
Parameter union : heap -> heap -> heap.
Parameter free_var : Type.

Inductive hprop : Type :=
| htrue : hprop
| hfalse : hprop
(* | prop : Prop -> hprop 
   这个构造子是否有必要？
   优点：有的谓词可能无法用下面的构造子表示，自定义谓词之类也可以归入这个构造子。
   缺点：加入该形式后可以引入的命题过于宽泛，可以用这个构造子做下面的很多事情。
        变量替换的时候也难以触及Prop内提到的变量。*)
| eqref : ref -> ref -> hprop
| eqvar : name -> ref -> hprop
| exp : expr -> ref -> hprop
| bexp : bexpr -> hprop (* 这里出现的bexpr中仅包括或且非三种运算符 *)
| vtype : ref -> rtype -> hprop
| vsubtype : ref -> rtype -> hprop
| emp : hprop
| pointTo : ref -> name -> ref -> hprop
| singleAttr : ref -> name -> ref -> hprop
| wholeObj : ref -> fields_env -> hprop
| neg : hprop -> hprop
| conj : hprop -> hprop -> hprop
| disj : hprop -> hprop -> hprop
| impl : hprop -> hprop -> hprop
| sep_conj : hprop -> hprop -> hprop
| sep_impl : hprop -> hprop -> hprop
| hexist : (ref -> hprop) -> hprop
| hforall : (ref -> hprop) -> hprop
| add_param : (ref -> hprop) -> hprop (* for defining predicates *)
| pass_arg : hprop -> ref -> hprop (* pass an argument to the predicate *)
| pass_arg2 : hprop -> name -> hprop
| abs_pred : name -> name -> hprop (* abstract predicate, with first parameter *)
| list_param : (list ref -> hprop) -> hprop
| list_arg : hprop -> (list ref) -> hprop
| exist_list : (list ref -> hprop) -> hprop.

Parameter subst_name_1 : name -> expr -> hprop -> hprop.
Parameter subst_name_2 : name -> bexpr -> hprop -> hprop.
Parameter subst_name_3 : name -> name -> hprop -> hprop.

Parameter eval : hprop -> heap -> stack -> super_env -> Prop.
Parameter fv : hprop -> free_var.
Parameter list_eq : list ref -> list ref -> hprop.

Parameter separate : hprop -> hprop -> Prop.
Parameter stack_hprop : hprop -> Prop.

Parameter eeq : hprop -> hprop -> Prop.
Parameter eimpl : hprop -> hprop -> Prop.

Infix "==" := eeq (at level 70) : hprop_scope.
Infix "==>" := eimpl (at level 75) : hprop_scope.
Infix "_|_" := separate (at level 40) : hprop_scope.

Infix "~=" := eqref (at level 20) : hprop_scope.
Infix "+->" := eqvar (at level 20) : hprop_scope.
Infix "=:" := vtype (at level 20) : hprop_scope.
Infix "<:" := vsubtype (at level 20) : hprop_scope.
Notation "o ` x |-> r" := (singleAttr o x r) (at level 25) : hprop_scope.
Notation "o ` x ~-> r" := (pointTo o x r) (at level 25) : hprop_scope.
Infix "|=>" := exp (at level 20) : hprop_scope.
Notation "' b" := (bexp b) (at level 20) : hprop_scope.
Notation "~` hp" := (neg hp) (at level 40) : hprop_scope.
Infix "/.\" := conj (at level 60, right associativity) : hprop_scope.
Infix "\./" := disj (at level 60, right associativity) : hprop_scope.
Infix "-->" := impl (at level 65, right associativity) : hprop_scope.
Infix "*" := sep_conj : hprop_scope.
Infix "*->" := sep_impl (at level 65, right associativity) : hprop_scope.
Notation "=| hp" := (hexist hp) (at level 60, right associativity) : hprop_scope.
Notation "\-/ hp" := (hforall hp) (at level 60, right associativity) : hprop_scope.
Notation ".\ p" := (add_param p) (at level 5, right associativity) : hprop_scope.
Infix "&" := pass_arg (at level 15, left associativity) : hprop_scope.
Infix "&^" := pass_arg2 (at level 15, left associativity) : hprop_scope.
Notation "|P| n @ a" := (abs_pred n a) (at level 5) : hprop_scope.
Notation ",\ p" := (list_param p) (at level 5, right associativity) : hprop_scope.
Infix "&`" := list_arg (at level 15, left associativity) : hprop_scope.
Notation "E| hp" := (exist_list hp) (at level 60, right associativity) : hprop_scope.

Open Scope hprop_scope.

Axiom eeq_refl : forall hp : hprop, hp == hp.
Axiom eeq_sym : forall hp1 hp2 : hprop, hp1 == hp2 -> hp2 == hp1.
Axiom eeq_trans : forall hp1 hp2 hp3 : hprop, hp1 == hp2 -> hp2 == hp3 -> hp1 == hp3.

Axiom equal_1 : forall hp1 hp2 : hprop, hp1 == hp2 <-> hp1 = hp2.

Axiom eimpl_refl : forall hp : hprop, hp ==> hp.
Axiom eimpl_asym : forall hp1 hp2 : hprop, hp1 ==> hp2 -> hp2 ==> hp1 -> hp1 == hp2.
Axiom eimpl_trans : forall hp1 hp2 hp3 : hprop, hp1 ==> hp2 -> hp2 ==> hp3 -> hp1 ==> hp3.

Axiom list_equal_1 : forall h s se (l1 l2 : list ref),
    eval (list_eq l1 l2) h s se <-> l1 = l2.
Axiom list_eq_refl : forall l : list ref, list_eq l l = htrue.
Axiom list_eq_ext : forall (l1 l2 : list ref) (hp1 hp2 : hprop),
    (l1 = l2 -> hp1 ==> hp2) ->
    (list_eq l1 l2) /.\ hp1 ==> hp2.
Axiom eqref_refl : forall r : ref, r ~= r = htrue.
Axiom eqref_sym : forall r1 r2 : ref, r1 ~= r2 = r2 ~= r1.
Axiom eqvar_eqref : forall (n : name) (r1 r2 : ref),
    n +-> r1 /.\ n +-> r2 = n +-> r1 /.\ r1 ~= r2.
Axiom eqvar_eqref2 : forall (n : name) (r1 r2 : ref),
    ~` (n +-> r1) /.\ n +-> r2 = ~` (r1 ~= r2) /.\ n +-> r2.
Axiom eqref_subst : forall (r1 r2 : ref) (rhp : ref -> hprop),
    rhp r1 /.\ r1 ~= r2 = rhp r2 /.\ r1 ~= r2.

Axiom empty : forall (h : heap) (s : stack) (se : super_env),
                  eval emp h s se -> h = empty_heap.

Axiom singleAttr_pointTo : forall (r r1 : ref) (n : name),
    r`n |-> r1 * htrue = r`n ~-> r1.
Axiom sep_singleAttr : forall (r r1 r2 : ref) (n : name) (hp1 hp2 : hprop),
    r`n |-> r1 * (r`n |-> r2 *-> hp1) * hp2 ==>
    r`n |-> r1 * (r`n |-> r2 *-> hp1 * hp2).

Axiom stack_hprop_1 : forall (r1 r2 : ref), stack_hprop (r1 ~= r2).
Axiom stack_hprop_2 : forall (n : name) (r : ref), stack_hprop (n +-> r).
Axiom stack_hprop_3 : forall (r : ref) (t : rtype), stack_hprop (r =: t).
Axiom stack_hprop_4 : forall (r : ref) (t : rtype), stack_hprop (r <: t).
Axiom stack_hprop_5 : forall (e : expr) (r : ref), stack_hprop (e |=> r).
Axiom stack_hprop_6 : forall (b : bexpr), stack_hprop (' b).
Axiom stack_hprop_7 : forall l1 l2 : list ref, stack_hprop (list_eq l1 l2).
Axiom stack_hprop_disj : forall hp1 hp2 : hprop,
    stack_hprop hp1 /\ stack_hprop hp2 -> stack_hprop (hp1 \./ hp2).
Axiom stack_hprop_conj : forall hp1 hp2 : hprop,
    stack_hprop hp1 /\ stack_hprop hp2 -> stack_hprop (hp1 /.\ hp2).
Axiom stack_hprop_neg : forall hp : hprop,
    stack_hprop hp -> stack_hprop (~` hp).

Axiom sep_emp : forall hp : hprop, hp _|_ emp.
Axiom sep_sym : forall hp1 hp2 : hprop, hp1 _|_ hp2 -> hp2 _|_ hp1.
Axiom sep_1 : forall (r r1 r2 : ref) (a b : name), a <> b -> r`a |-> r1 _|_ r`b |-> r2.
Axiom sep_2 : forall (r0 r1 r2 r3 : ref) (a b : name), r0 <> r1 -> r0`a |-> r2 _|_ r1`b |-> r3.
Axiom sep_union : forall (hp hp' : hprop) (h h' : heap) (s : stack) (se : super_env),
    hp _|_ hp' -> eval hp h s se -> eval hp' h' s se -> eval (hp * hp') (union h h') s se.
Axiom sep_break : forall (hp hp' : hprop) (h : heap) (s : stack) (se : super_env),
    hp _|_ hp' -> eval (hp * hp') h s se ->
        exists (h1 h2 : heap), eval hp h1 s se /\ eval hp' h2 s se /\ h = union h1 h2.
Axiom sep_break_unique : forall (h1 h2 h3 h4 : heap) (hp1 hp2 : hprop) (s : stack) (se : super_env),
    hp1 _|_ hp2 -> eval hp1 h1 s se -> eval hp2 h2 s se -> eval hp1 h3 s se ->
        eval hp2 h4 s se -> union h1 h2 = union h3 h4 -> h1 = h3 /\ h2 = h4.
Axiom sep_sep_conj : forall hp1 hp2 hp3 : hprop,
    hp1 _|_ hp3 -> hp1 /.\ (hp2 * hp3) ==> (hp1 /.\ hp2) * hp3.
Axiom stack_conj : forall hp1 hp2 : hprop,
    stack_hprop hp1 -> hp1 /.\ hp2 ==> hp1 * hp2.
Axiom stack_sep_conj1 : forall hp1 hp2 hp3 : hprop,
    stack_hprop hp1 -> hp1 /.\ (hp2 * hp3) = (hp1 /.\ hp2) * hp3.
Axiom stack_sep_conj2 : forall hp1 hp2 hp3 : hprop,
    stack_hprop hp3 -> (hp1 * hp2) /.\ hp3 = (hp1 /.\ hp3) * hp2.
Axiom stack_sep_conj3 : forall hp1 hp2 hp3 : hprop,
    stack_hprop hp2 -> hp1 * (hp2 /.\ hp3) = hp2 /.\ hp1 * hp3.
Axiom sep_conj_sep : forall hp1 hp2 hp3 : hprop,
    hp1 _|_ hp2 /\ hp1 _|_ hp3 -> hp1 _|_ (hp2 * hp3).
Axiom sep_impl_exc : forall hp1 hp2 hp3 : hprop,
    hp1 _|_ hp2 -> hp1 * (hp2 *-> hp3) ==> hp2 *-> (hp1 * hp3).

Axiom impl_conj1 : forall hp1 hp2 hp3 : hprop,
    hp1 ==> hp2 -> hp1 /.\ hp3 ==> hp2 /.\ hp3.
Axiom impl_conj2 : forall hp1 hp2 hp3 : hprop,
    hp1 ==> hp2 -> hp3 /.\ hp1 ==> hp3 /.\ hp2.
Axiom impl_sep_conj1 : forall hp1 hp2 hp3 : hprop,
    hp1 ==> hp2 -> hp1 * hp3 ==> hp2 * hp3.
Axiom impl_sep_conj2 : forall hp1 hp2 hp3 : hprop,
    hp1 ==> hp2 -> hp3 * hp1 ==> hp3 * hp2.

Axiom neg_disj : forall hp1 hp2 : hprop, ~` (hp1 \./ hp2) = ~` hp1 /.\ ~` hp2.
Axiom neg_conj : forall hp1 hp2 : hprop, ~` (hp1 /.\ hp2) = ~` hp1 \./ ~` hp2.

Axiom neg_involutive : forall hp : hprop, (~` ~` hp) = hp.
Axiom neg_involutive_reverse : forall hp : hprop, hp = (~` ~` hp).
Axiom neg_sym : forall hp hp' : hprop, hp' = (~` hp) -> hp = (~` hp').
Axiom eq_neg1 : forall hp : hprop, ~ ((~` hp) = hp).
Axiom eq_neg2 : forall hp : hprop, ~ (hp = (~` hp)).

Axiom disj_true_iff : forall (hp1 hp2 : hprop) (h : heap) (s : stack) (se : super_env),
      (eval (hp1 \./ hp2) h s se) <-> eval hp1 h s se \/ eval hp2 h s se.
Axiom disj_false_iff : forall (hp1 hp2 : hprop) (h : heap) (s : stack) (se : super_env),
      ~ (eval (hp1 \./ hp2) h s se) <-> ~ eval hp1 h s se /\ ~ eval hp2 h s se.
Axiom disj_true_r : forall hp : hprop, (hp \./ htrue) = htrue.
Axiom disj_true_l : forall hp : hprop, (htrue \./ hp) = htrue.
Axiom disj_false_r : forall hp : hprop, (hp \./ hfalse) = hp.
Axiom disj_false_l : forall hp : hprop, (hfalse \./ hp) = hp.
Axiom disj_neg_r : forall hp : hprop, (hp \./ ~` hp) = htrue.
Axiom disj_refl : forall hp : hprop, hp \./ hp = hp.
Axiom disj_comm : forall hp1 hp2 : hprop, (hp1 \./ hp2) = (hp2 \./ hp1).
Axiom disj_asso : forall hp1 hp2 hp3 : hprop, (hp1 \./ (hp2 \./ hp3)) = ((hp1 \./ hp2) \./ hp3).

Axiom conj_true_iff : forall (hp1 hp2 : hprop) (h : heap) (s : stack) (se : super_env),
      (eval (hp1 /.\ hp2) h s se) <-> eval hp1 h s se /\ eval hp2 h s se.
Axiom conj_false_iff : forall (hp1 hp2 : hprop) (h : heap) (s : stack) (se : super_env),
      ~ (eval (hp1 /.\ hp2) h s se) <-> ~ eval hp1 h s se \/ ~ eval hp2 h s se.
Axiom conj_true_r : forall hp : hprop, (hp /.\ htrue) = hp.
Axiom conj_true_l : forall hp : hprop, (htrue /.\ hp) = hp.
Axiom conj_false_r : forall hp : hprop, (hp /.\ hfalse) = hfalse.
Axiom conj_false_l : forall hp : hprop, (hfalse /.\ hp) = hfalse.
Axiom conj_neg_r : forall hp : hprop, (hp /.\ ~` hp) = hfalse.
Axiom conj_refl : forall hp : hprop, hp /.\ hp = hp.
Axiom conj_comm : forall hp1 hp2 : hprop, (hp1 /.\ hp2) = (hp2 /.\ hp1).
Axiom conj_asso : forall hp1 hp2 hp3 : hprop, (hp1 /.\ (hp2 /.\ hp3)) = ((hp1 /.\ hp2) /.\ hp3).

Axiom conj_impl: forall hp1 hp2 : hprop, (hp1 /.\ hp2) ==> hp1.
Axiom disj_impl: forall hp1 hp2 : hprop, hp1 ==> (hp1 \./ hp2).
Axiom conj_disj_distrib_r : forall hp1 hp2 hp3 : hprop,
    hp1 /.\ (hp2 \./ hp3) = (hp1 /.\ hp2) \./ (hp1 /.\ hp3).
Axiom conj_disj_distrib_l : forall hp1 hp2 hp3 : hprop,
    (hp1 \./ hp2) /.\ hp3 = (hp1 /.\ hp3) \./ (hp2 /.\ hp3).
Axiom disj_conj_distrib_r : forall hp1 hp2 hp3 : hprop,
    hp1 \./ (hp2 /.\ hp3) = (hp1 \./ hp2) /.\ (hp1 \./ hp3).
Axiom disj_conj_distrib_l : forall hp1 hp2 hp3 : hprop,
    (hp1 /.\ hp2) \./ hp3 = (hp1 \./ hp3) /.\ (hp2 \./ hp3).
Axiom absoption_conj : forall hp1 hp2 : hprop, hp1 /.\ (hp1 \./ hp2) = hp1.
Axiom absoption_disj : forall hp1 hp2 : hprop, hp1 \./ (hp1 /.\ hp2) = hp1.

Axiom sep_conj_emp1 : forall hp : hprop, hp * emp = hp.
Axiom sep_conj_emp2 : forall hp : hprop, emp * hp = hp.
Axiom sep_conj_comm : forall hp1 hp2 : hprop, hp1 * hp2 = hp2 * hp1.
Axiom sep_conj_asso : forall hp1 hp2 hp3 : hprop,
    hp1 * (hp2 * hp3) = (hp1 * hp2) * hp3.

Axiom sep_conj_impl_1 : forall hp1 hp2 : hprop, hp1 * (hp1 *-> hp2) ==> hp2.
(* 文章里写的是 eeq 而非 eimpl，但是它的逆命题是错的，考虑 hp1 = false 的情形。 *)
Axiom sep_conj_impl_2 : forall hp1 hp2 : hprop, hp2 ==> (hp1 *-> (hp1 * hp2)).
Axiom sep_conj_impl_3 : forall hp1 hp2 hp3 : hprop,
    hp1 * hp2 ==> hp3 -> hp1 ==> (hp2 *-> hp3).
Axiom sep_conj_impl_4 : forall hp1 hp2 hp3 hp : hprop,
    hp1 * hp2 ==> hp3 -> hp1 * hp ==> (hp2 *-> (hp3 * hp)).
Axiom sep_conj_impl_5 : forall hp1 hp2 hp3 hp : hprop,
    hp1 ==> (hp2 *-> hp3) -> hp1 * hp ==> (hp2 *-> (hp3 * hp)).
(* 上面三条引理需要注意的是 ==> 和 -> 的区别。
   -> 的左右两端表示的堆可能不同，而 ==> 左右两端的堆一定是相同的。 *)

Axiom sep_impl_conj : forall hp1 hp2 hp3 : hprop,
    hp1 *-> (hp2 /.\ hp3) = (hp1 *-> hp2) /.\ (hp1 *-> hp3).
Axiom sep_impl_impl : forall hp1 hp2 hp3 : hprop,
    hp1 *-> (hp2 *-> hp3) = (hp1 * hp2) *-> hp3.

Axiom exist_forall : forall (rhp : ref -> hprop),
    (~` =| rhp) = \-/ (fun r => ~` rhp r).
Axiom forall_exist : forall (rhp : ref -> hprop),
    (~` \-/ rhp) = =| (fun r => ~` rhp r).

Axiom exist_conj : forall (rhp : ref -> hprop) (hp : hprop),
    (=| rhp) /.\ hp = =| (fun r => rhp r /.\ hp).
Axiom exist_disj : forall (rhp : ref -> hprop) (hp : hprop),
    (=| rhp) \./ hp = =| (fun r => rhp r \./ hp).
Axiom existl_conj : forall (rhp : list ref -> hprop) (hp : hprop),
    (E| rhp) /.\ hp = E| (fun l => rhp l /.\ hp).
Axiom existl_conj' : forall (rhp : list ref -> hprop) (hp : hprop),
    hp /.\ (E| rhp) = E| (fun l => hp /.\ rhp l).
Axiom exist_sep_conj : forall (rhp : ref -> hprop) (hp : hprop),
    (=| rhp) * hp = =| (fun r => rhp r * hp).
Axiom forall_conj : forall (rhp : ref -> hprop) (hp : hprop),
    (\-/ rhp) /.\ hp = \-/ (fun r => rhp r /.\ hp).
Axiom forall_disj : forall (rhp : ref -> hprop) (hp : hprop),
    (\-/ rhp) \./ hp ==> \-/ (fun r => rhp r \./ hp).
Axiom forall_sep_conj : forall (rhp : ref -> hprop) (hp : hprop),
    (\-/ rhp) * hp ==> \-/ (fun r => rhp r * hp).
Axiom impl_exist : forall (r : ref) (rhp : ref -> hprop),
    rhp r ==> (=| rhp).
Axiom forall_impl : forall (r : ref) (rhp : ref -> hprop),
    (\-/ rhp) ==> rhp r.

Axiom forall_exist_impl : forall (rhp : ref -> hprop) (hp : hprop),
    (forall r, rhp r ==> hp) -> (=| rhp) ==> hp.
Axiom exist_exist_impl : forall (rhp : ref -> hprop) (hp : hprop),
    (exists r, hp ==> rhp r) -> hp ==> =| rhp.
Axiom forall_exist_impl2 : forall (rhp : list ref -> hprop) (hp : hprop),
    (forall l, rhp l ==> hp) -> (E| rhp) ==> hp.
Axiom exist_exist_impl2 : forall (rhp : list ref -> hprop) (hp : hprop),
    (exists l, hp ==> rhp l) -> hp ==> E| rhp.
Axiom false_impl : forall hp : hprop, hfalse ==> hp.
Axiom impl_true : forall hp : hprop, hp ==> htrue.

Axiom param_arg : forall  (r : ref) (rhp : ref -> hprop),
    .\ rhp &r = rhp r.
Axiom param_arg2 : forall (n : name) (rhp : ref -> hprop),
    .\ rhp &^n = hexist (fun r => n +-> r /.\ rhp r).
Axiom param_arg3 : forall (l : list ref) (rhp : list ref -> hprop),
    ,\ rhp &`l = rhp l.
Axiom param_ext : forall (rhp1 : (ref -> hprop)) (rhp2 : (ref -> ref -> hprop)),
    =| (fun r => (rhp1 r /.\ .\ fun v => (rhp2 v) r)) =
    .\ (fun v => =| (fun r => rhp1 r /.\ (rhp2 v) r)).
Axiom param_ext2 : forall (rhp1 : ref -> hprop) (rhp2 : list ref -> ref -> hprop),
    =| (fun r => (rhp1 r /.\ ,\ fun v => (rhp2 v) r)) =
    ,\ (fun v => =| (fun r => rhp1 r /.\ (rhp2 v) r)).

Axiom func_ext1 : forall rhp1 rhp2,
    (forall r, rhp1 r = rhp2 r) ->
    =| (fun r => rhp1 r) = =| (fun r => rhp2 r).
Axiom func_ext2 : forall rhp1 rhp2,
    (forall r, rhp1 r = rhp2 r) ->
    \-/ (fun r => rhp1 r) = \-/ (fun r => rhp2 r).
Axiom func_ext3 : forall rhp1 rhp2,
    (forall r, rhp1 r = rhp2 r) ->
    .\ (fun r => rhp1 r) = .\ (fun r => rhp2 r).
Axiom func_ext4 : forall rhp1 rhp2,
    (forall r, rhp1 r = rhp2 r) ->
    ,\ (fun r => rhp1 r) = ,\ (fun r => rhp2 r).

Axiom lemma3_26: forall (r r1 r2 : ref) (hp1 hp2 : hprop) (a : name),
    r`a |-> r1 * ((r`a |-> r2 *-> hp1) * hp2) ==>
    r`a |-> r1 * (r`a |-> r2 *-> (hp1 * hp2)).

Close Scope hprop_scope.

End HPROP.


(*-----  Data  -----*)

(*  HeapAsn  *)

Module HProp <: HPROP.

Definition heap := Heap.heap.
Definition stack := Stack.stack.
Definition name := Name.name.
Definition rtype := RType.rtype.
Definition ref := Ref.ref.
Definition expr := Expr.expr.
Definition bexpr := BExpr.bexpr.
Definition dtype := DType.dtype.
Definition super_env := TEnv.super_env.
Definition fields_env := TEnv.fields_env.
Definition empty_heap := Heap.empty_heap.
Definition union := Heap.union.

Definition free_var := Sset.t.
Definition no_fv : free_var := Sset.empty.

Inductive atomic : Prop :=
    | atom1 : name -> name -> atomic
    | atom2 : atomic -> name -> atomic.
(* For abstract predicates. 
   If the first argument of a predicate is not "this",
   the predicate can only be seen as an atomic assertion. *)

Parameter asrt : atomic -> Prop.

Inductive hprop : Type :=
| htrue : hprop
| hfalse : hprop
| eqref : ref -> ref -> hprop
| eqvar : name -> ref -> hprop
| exp : expr -> ref -> hprop
| bexp : bexpr -> hprop (* 这里出现的bexpr中仅包括或且非三种运算符 *)
| vtype : ref -> rtype -> hprop
| vsubtype : ref -> rtype -> hprop
| emp : hprop
| pointTo : ref -> name -> ref -> hprop
| singleAttr : ref -> name -> ref -> hprop
| wholeObj : ref -> fields_env -> hprop
| neg : hprop -> hprop
| conj : hprop -> hprop -> hprop
| disj : hprop -> hprop -> hprop
| impl : hprop -> hprop -> hprop
| sep_conj : hprop -> hprop -> hprop
| sep_impl : hprop -> hprop -> hprop
| hexist : (ref -> hprop) -> hprop
| hforall : (ref -> hprop) -> hprop
| add_param : (ref -> hprop) -> hprop
| pass_arg : hprop -> ref -> hprop
| pass_arg2 : hprop -> name -> hprop
| abs_pred : name -> name -> hprop
| list_param : (list ref -> hprop) -> hprop
| list_arg : hprop -> (list ref) -> hprop
| exist_list : (list ref -> hprop) -> hprop.

Bind Scope hprop_scope with hprop.
Delimit Scope hprop_scope with hprop.
Open Scope hprop_scope.
Open Scope heap_scope.
Open Scope lang_scope.

Infix "~=" := eqref (at level 20) : hprop_scope.
Infix "+->" := eqvar (at level 20) : hprop_scope.
Infix "=:" := vtype (at level 20) : hprop_scope.
Infix "<:" := vsubtype (at level 20) : hprop_scope.
Notation "o ` x |-> r" := (singleAttr o x r) (at level 25) : hprop_scope.
Notation "o ` x ~-> r" := (pointTo o x r) (at level 25) : hprop_scope.
Infix "|=>" := exp (at level 20) : hprop_scope.
Notation "' b" := (bexp b) (at level 20) : hprop_scope.
Notation "~` hp" := (neg hp) (at level 40) : hprop_scope.
Infix "/.\" := conj (at level 60, right associativity) : hprop_scope.
Infix "\./" := disj (at level 60, right associativity) : hprop_scope.
Infix "-->" := impl (at level 65, right associativity) : hprop_scope.
Infix "*" := sep_conj : hprop_scope.
Infix "*->" := sep_impl (at level 65, right associativity) : hprop_scope.
Notation "=| hp" := (hexist hp) (at level 60, right associativity) : hprop_scope.
Notation "\-/ hp" := (hforall hp) (at level 60, right associativity) : hprop_scope.
Notation ".\ p" := (add_param p) (at level 5, right associativity) : hprop_scope.
Infix "&" := pass_arg (at level 15, left associativity) : hprop_scope.
Infix "&^" := pass_arg2 (at level 15, left associativity) : hprop_scope.
Notation "|P| n @ a" := (abs_pred n a) (at level 5) : hprop_scope.
Notation ",\ p" := (list_param p) (at level 5, right associativity) : hprop_scope.
Infix "&`" := list_arg (at level 15, left associativity) : hprop_scope.
Notation "E| hp" := (exist_list hp) (at level 60, right associativity) : hprop_scope.

Fixpoint subst_name_1 (n : name) (e : expr) (hp : hprop) : hprop :=
match hp with
| n' +-> r => if Name.beq n' n then e |=> r
                else hp
| e' |=> r => match e' with
              | ^ n' =>
                  if Name.beq n' n then
                      e |=> r
                  else hp
              | _ => hp
              end
| ~` hp' => ~` (subst_name_1 n e hp')
| hp1 /.\ hp2 => (subst_name_1 n e hp1) /.\ (subst_name_1 n e hp2)
| hp1 \./ hp2 => (subst_name_1 n e hp1) \./ (subst_name_1 n e hp2)
| hp1 --> hp2 => (subst_name_1 n e hp1) --> (subst_name_1 n e hp2)
| hp1 * hp2 => (subst_name_1 n e hp1) * (subst_name_1 n e hp2)
| hp1 *-> hp2 => (subst_name_1 n e hp1) *-> (subst_name_1 n e hp2)
| =| hp' => =| (fun r => subst_name_1 n e (hp' r))
| \-/ hp' => \-/ (fun r => subst_name_1 n e (hp' r))
| .\ hp' => .\ (fun r => subst_name_1 n e (hp' r))
| hp' & r => (subst_name_1 n e hp') & r
| hp' &^ n' => if Name.beq n' n then =| (fun r => e |=> r /.\
                       (subst_name_1 n e hp') & r)
                       else (subst_name_1 n e hp') &^ n'
| ,\ hp' => ,\ (fun l => subst_name_1 n e (hp' l))
| hp' &` l => (subst_name_1 n e hp') &` l
| E| hp' => E| (fun l => subst_name_1 n e (hp' l))
| _ => hp
end.

Fixpoint subst_name_2 (n : name) (b : bexpr) (hp : hprop) : hprop :=
match hp with
| n' +-> r => if Name.beq n' n then
                    if Ref.beq r Ref.rtrue then 'b
                    else '(BExpr.bneg b) (* r应该是Ref.rfalse，否则类型错误 *)
                else hp
| e |=> r => match e with
             | ^ n' =>
                 if Name.beq n' n then
                     if Ref.beq r Ref.rtrue then 'b
                     else '(BExpr.bneg b) (* r应该是Ref.rfalse，否则类型错误 *)
                 else hp
             | _ => hp
             end
| ~` hp' => ~` (subst_name_2 n b hp')
| hp1 /.\ hp2 => (subst_name_2 n b hp1) /.\ (subst_name_2 n b hp2)
| hp1 \./ hp2 => (subst_name_2 n b hp1) \./ (subst_name_2 n b hp2)
| hp1 --> hp2 => (subst_name_2 n b hp1) --> (subst_name_2 n b hp2)
| hp1 * hp2 => (subst_name_2 n b hp1) * (subst_name_2 n b hp2)
| hp1 *-> hp2 => (subst_name_2 n b hp1) *-> (subst_name_2 n b hp2)
| =| hp' => =| (fun r => subst_name_2 n b (hp' r))
| \-/ hp' => \-/ (fun r => subst_name_2 n b (hp' r))
| .\ hp' => .\ (fun r => subst_name_2 n b (hp' r))
| hp' & r => (subst_name_2 n b hp') & r
| hp' &^ n' => if Name.beq n' n then (((n +-> Ref.rtrue) /.\ 'b)
                        \./ ((n +-> Ref.rfalse) /.\ ~` 'b)) /.\
                        (subst_name_2 n b hp') &^ n
                        else (subst_name_2 n b hp') &^ n'
| ,\ hp' => ,\ (fun l => subst_name_2 n b (hp' l))
| hp' &` l => (subst_name_2 n b hp') &` l
| E| hp' => E| (fun l => subst_name_2 n b (hp' l))
| _ => hp
end.

Fixpoint subst_name_3 (n1 n2 : name) (hp : hprop) : hprop :=
match hp with
| n' +-> r => if Name.beq n' n1 then n2 +-> r
                else hp
| e' |=> r => match e' with
              | ^ n' =>
                  if Name.beq n' n1 then
                      n2 +-> r
                  else hp
              | _ => hp
              end
| ~` hp' => ~` (subst_name_3 n1 n2 hp')
| hp1 /.\ hp2 => (subst_name_3 n1 n2 hp1) /.\ (subst_name_3 n1 n2 hp2)
| hp1 \./ hp2 => (subst_name_3 n1 n2 hp1) \./ (subst_name_3 n1 n2 hp2)
| hp1 --> hp2 => (subst_name_3 n1 n2 hp1) --> (subst_name_3 n1 n2 hp2)
| hp1 * hp2 => (subst_name_3 n1 n2 hp1) * (subst_name_3 n1 n2 hp2)
| hp1 *-> hp2 => (subst_name_3 n1 n2 hp1) *-> (subst_name_3 n1 n2 hp2)
| =| hp' => =| (fun r => subst_name_3 n1 n2 (hp' r))
| \-/ hp' => \-/ (fun r => subst_name_3 n1 n2 (hp' r))
| .\ hp' => .\ (fun r => subst_name_3 n1 n2 (hp' r))
| hp' & r => (subst_name_3 n1 n2 hp') & r
| hp' &^ n' => if Name.beq n' n1
                  then (subst_name_3 n1 n2 hp') &^ n2
                  else (subst_name_3 n1 n2 hp') &^ n'
| ,\ hp' => ,\ (fun l => subst_name_3 n1 n2 (hp' l))
| hp' &` l => (subst_name_3 n1 n2 hp') &` l
| E| hp' => E| (fun l => subst_name_3 n1 n2 (hp' l))
| _ => hp
end.

Definition acc (t : Type) (s : name) (e : t) (n : nat) : nat := n+1.

Definition count (t : Type) (m : Smap.t t) : nat :=
    Smap.fold (acc t) m 0.

Fixpoint eval (hp : hprop) (h : heap) (s : stack) (se : super_env) : Prop :=
match hp with
| htrue => True
| hfalse => False
| r1 ~= r2 => r1 = r2
| n +-> r => Stack.get n s = Some r
| e |=> r => match e with
             | Expr.tru => r = Ref.rtrue
             | Expr.fals => r = Ref.rfalse
             | Expr.null => r = Ref.rnull
             | Expr.var n => Stack.get n s = Some r
             end
| 'b => BExpr.eval b s = true
| r =: t => RType.peq (Ref.get_type r) t
| r <: t => TEnv.subtype (Ref.get_type r) t se
| emp => Heap.eq h {}
| r`n ~-> r1 => Heap.get r n h = Some r1
| r`n |-> r1 => h |=| Heap.update r n r1 {}
| wholeObj r f => exists ft o, Smap.find (Ref.get_type r) f = Some ft /\
                               Rmap.find r h = Some o /\
                               (count ref o) = (count rtype ft)
| ~` hp' => ~ (eval hp' h s se)
| hp1 /.\ hp2 => (eval hp1 h s se) /\ (eval hp2 h s se)
| hp1 \./ hp2 => (eval hp1 h s se) \/ (eval hp2 h s se)
| hp1 --> hp2 => (eval hp1 h s se) -> (eval hp2 h s se)
| hp1 * hp2 => exists h1 h2 : heap,
                   h1 |*| h2 /\ (h = h1 |+| h2) /\
                   eval hp1 h1 s se /\ eval hp2 h2 s se
| hp1 *-> hp2 => forall h1 : heap,
                     (eval hp1 h1 s se /\ h |*| h1) ->
                     eval hp2 (h |+| h1) s se
| =| hp' => exists r : ref, eval (hp' r) h s se
| \-/ hp' => forall r : ref, eval (hp' r) h s se
| .\ hp' => exists r : ref, eval (hp' r) h s se
| hp' & r => match hp' with
             | .\ hp0 => eval (hp0 r) h s se
             | _ => False
             end
| hp' &^ n => match hp' with
             | .\ hp0 => exists r : ref, Stack.get n s = Some r
                                      /\ eval (hp0 r) h s se
             | _ => False
             end
| |P| n @ a => asrt (atom1 n a)
| ,\ hp' => exists lr, eval (hp' lr) h s se
| hp' &` lr => match hp' with
               | ,\ hp0 => eval (hp0 lr) h s se
               | _ => False
               end
| E| hp' => exists lr, eval (hp' lr) h s se
end.

Fixpoint list_eq (l1 l2 : list ref) : hprop :=
    match l1, l2 with
    | nil, nil => htrue
    | cons r1 nil, cons r2 nil => r1 ~= r2
    | cons r1 t1, cons r2 t2 => r1 ~= r2 /.\ list_eq t1 t2
    | _, _ => hfalse
    end.

Definition fv_e (e : expr) : free_var :=
    match e with
    | ^ n => Sset.add n no_fv
    | _ => no_fv
    end.

Fixpoint fv_b (b : bexpr) : free_var :=
    match b with
    | BExpr.bequal e1 e2 => Sset.union (fv_e e1) (fv_e e2)
    | BExpr.band b1 b2 => Sset.union (fv_b b1) (fv_b b2)
    | BExpr.bor b1 b2 => Sset.union (fv_b b1) (fv_b b2)
    | BExpr.bneg b => fv_b b
    | _ => no_fv
    end.

Fixpoint fv (hp : hprop) : free_var :=
match hp with
| n +-> _ => Sset.add n no_fv
| e |=> _ => fv_e e
| 'b => fv_b b
| ~` hp' => fv hp'
| hp1 /.\ hp2 => Sset.union (fv hp1) (fv hp2)
| hp1 \./ hp2 => Sset.union (fv hp1) (fv hp2)
| hp1 --> hp2 => Sset.union (fv hp1) (fv hp2)
| hp1 * hp2 => Sset.union (fv hp1) (fv hp2)
| hp1 *-> hp2 => Sset.union (fv hp1) (fv hp2)
| =| hp' => fv (hp' Ref.rtrue)
| \-/ hp' => fv (hp' Ref.rtrue)
| .\ hp' => fv (hp' Ref.rtrue)
| hp' & r => fv hp'
| hp' &^ n => Sset.add n (fv hp')
| |P| n @ a => Sset.add a (no_fv)
| ,\ hp' => fv (hp' nil)
| hp' &` r => fv hp'
| E| hp' => fv (hp' nil)
| _ => no_fv
end.

Definition separate (hp1 hp2 : hprop) : Prop :=
    forall (h1 h2 : heap) (s : stack) (se : super_env),
    (eval hp1 h1 s se /\ eval hp2 h2 s se) -> h1 |*| h2.

Definition stack_hprop (hp : hprop) : Prop :=
    forall (h1 h2 : heap) (s : stack) (se : super_env),
    eval hp h1 s se -> eval hp h2 s se.

Definition eeq (hp1 hp2 : hprop) : Prop :=
           forall (h : heap) (s : stack) (se : super_env),
           (eval hp1 h s se) <-> (eval hp2 h s se).

Definition eimpl (hp1 hp2 : hprop) : Prop :=
           forall (h : heap) (s : stack) (se : super_env),
           (eval hp1 h s se) -> (eval hp2 h s se).

Infix "==" := eeq (at level 70, no associativity) : hprop_scope.
Infix "==>" := eimpl (at level 75, no associativity) : hprop_scope.
Infix "_|_" := separate (at level 40, no associativity) : hprop_scope.

Lemma eeq_refl : forall hp : hprop, hp == hp.
Proof.
  unfold eeq; reflexivity.
Qed.

Lemma eeq_sym : forall hp1 hp2 : hprop, hp1 == hp2 -> hp2 == hp1.
Proof.
  unfold eeq; intros hp1 hp2 H h s se.
  rewrite H; reflexivity.
Qed.
  
Lemma eeq_trans : forall hp1 hp2 hp3 : hprop, hp1 == hp2 -> hp2 == hp3 -> hp1 == hp3.
Proof.
  unfold eeq; intros hp1 hp2 hp3 H H' h s se.
  rewrite H; apply H'.
Qed.

Axiom equal_1 : forall hp1 hp2 : hprop, hp1 == hp2 <-> hp1 = hp2.

Lemma eimpl_refl : forall hp : hprop, hp ==> hp.
Proof.
  unfold eimpl.
  intros; assumption.
Qed.

Lemma eimpl_asym : forall hp1 hp2 : hprop, hp1 ==> hp2 -> hp2 ==> hp1 -> hp1 == hp2.
Proof.
  unfold eimpl; unfold eeq.
  intros hp1 hp2 H H' h s se.
  split; [apply H | apply H'].
Qed.

Lemma eimpl_trans : forall hp1 hp2 hp3 : hprop, hp1 ==> hp2 -> hp2 ==> hp3 -> hp1 ==> hp3.
Proof.
  unfold eimpl.
  intros hp1 hp2 hp3 H H' h s se H0.
  apply H'; apply H; assumption.
Qed.

Lemma list_eq_refl : forall l : list ref, list_eq l l = htrue.
Proof.
  induction l; apply equal_1.
  unfold list_eq; apply eeq_refl.
  unfold eeq; simpl; rewrite IHl.
  case l; unfold eval; repeat split; reflexivity.
Qed.

Lemma list_equal_1 : forall h s se (l1 l2 : list ref),
    eval (list_eq l1 l2) h s se <-> l1 = l2.
Proof.
  induction l1, l2.
  unfold list_eq; unfold eval; split; auto.
  unfold list_eq; unfold eval; split; try discriminate.
  intro H; elim H.
  unfold list_eq; unfold eval; fold eval; split; try discriminate.
  case l1; unfold eval; intros; elim H.
  unfold list_eq; fold list_eq; unfold eval; fold eval.
  assert ((exists a1 b1, l1 = cons a1 b1) \/ l1 = nil).
  case l1; eauto.
  destruct H. do 2 destruct H. rewrite H at 1; clear H.
  simpl; split. intros [H0 H1]. apply IHl1 in H1.
  subst; reflexivity.
  intro H; inversion H. split; [|rewrite list_eq_refl]; reflexivity.
  rewrite H. case l2.
  split; simpl; intro H0; [rewrite H0|inversion H0]; reflexivity.
  intros; split; simpl. intros [H0 H1]; elim H1.
  intro H0; inversion H0.
Qed.

Lemma list_eq_ext : forall (l1 l2 : list ref) (hp1 hp2 : hprop),
    (l1 = l2 -> hp1 ==> hp2) ->
    (list_eq l1 l2) /.\ hp1 ==> hp2.
Proof.
  intros l1 l2 hp1 hp2 H.
  unfold eimpl; simpl.
  intros h s se [H0 H1].
  apply list_equal_1 in H0.
  apply H in H0; apply H0; assumption.
Qed.

Lemma list_eq_dsj : forall (l1 l2 : list ref) (md : Sset.t),
    sset_dsj md (fv (list_eq l1 l2)).
Proof.
  induction l1, l2; intro md; unfold fv;
  unfold list_eq; try apply sset_dsj_empty;
  fold fv; fold list_eq. case l1;
  intros; apply sset_dsj_empty.
  assert ((exists x y, l1 = cons x y) \/ l1 = nil).
  case l1; eauto. destruct H as [[x [y H]] | H]; rewrite H.
  rewrite <- H. apply sset_dsj_union; split;
  [apply sset_dsj_empty | apply IHl1].
  case l2. apply sset_dsj_empty.
  intros; apply sset_dsj_union.
  unfold list_eq; split; apply sset_dsj_empty.
Qed.

Lemma eqref_refl : forall r : ref, r ~= r = htrue.
Proof.
  intro r; apply equal_1; unfold eeq; simpl.
  split; auto.
Qed.

Lemma eqref_sym : forall r1 r2 : ref, r1 ~= r2 = r2 ~= r1.
Proof.
  intros r1 r2; apply equal_1; unfold eeq; simpl.
  split; auto.
Qed.

Lemma eqvar_eqref : forall (n : name) (r1 r2 : ref),
    n +-> r1 /.\ n +-> r2 = n +-> r1 /.\ r1 ~= r2.
Proof.
  intros n r1 r2; apply equal_1.
  unfold eeq; unfold eval.
  intros h s se; split; intros [H H0].
  split. assumption. rewrite H in H0.
  inversion H0; reflexivity.
  split; [|rewrite <- H0]; assumption.
Qed.

Lemma eqvar_eqref2 : forall (n : name) (r1 r2 : ref),
    ~` (n +-> r1) /.\ n +-> r2 = ~` (r1 ~= r2) /.\ n +-> r2.
Proof.
  intros n r1 r2; apply equal_1.
  unfold eeq; unfold eval.
  intros h s se; split; intros [H H0].
  split; [rewrite H0 in H|assumption].
  intro H1; elim H; rewrite H1; reflexivity.
  split; [rewrite H0|assumption].
  intro H1; elim H; inversion H1; reflexivity.
Qed.

Lemma eqref_subst : forall (r1 r2 : ref) (rhp : ref -> hprop),
    rhp r1 /.\ r1 ~= r2 = rhp r2 /.\ r1 ~= r2.
Proof.
  intros r1 r2 rhp; apply equal_1.
  unfold eeq; simpl. intros h s se; split;
  intros [H H0]; split; try assumption.
  rewrite <- H0; assumption.
  rewrite H0; assumption.
Qed.

Lemma empty : forall (h : heap) (s : stack) (se : super_env),
              eval emp h s se -> h = {}.
Proof.
  intros h s se.
  unfold eval.
  intro H.
  apply Heap.equal_3.
  assumption.
Qed.

Lemma singleAttr_pointTo : forall (r r1 : ref) (n : name),
    r`n |-> r1 * htrue = r`n ~-> r1.
Proof.
  intros r r1 n.
  apply equal_1. unfold eeq.
  intros h s se.
  unfold eval; fold eval.
  split. intros [h1 [h2 [H [H0 [H1 _]]]]].
  apply Heap.equal_3 in H1.
  assert (Heap.pin r n r1 h).
  rewrite H0. apply Heap.in_union_1.
  left; rewrite H1. apply Heap.in_update_1.
  apply Heap.in_get in H2. assumption.
  intro H.
  exists (Heap.update r n r1 {}).
  exists (Heap.remove r n h).
  split. apply Heap.pdisjoint_sym.
  apply Heap.disjoint_remove.
  split. apply Heap.equal_3.
  unfold Heap.eq.
  intros r0 r2 n0.
  split. intro H0.
  apply Heap.in_union_1.
  case (Ref.eq_dec r0 r).
  intro H1. rewrite H1. rewrite H1 in H0.
  case (Name.eq_dec n0 n).
  intro H2. rewrite H2.
  left. apply Heap.in_get in H0.
  rewrite H2 in H0.
  rewrite H0 in H. inversion H.
  apply Heap.in_update_1.
  intro H2. right.
  apply Heap.in_remove_2.
  right; assumption. assumption.
  intro H1. right.
  apply Heap.in_remove_2.
  left; assumption. assumption.
  intro. apply Heap.in_union_1 in H0.
  destruct H0.
  case Ref.eq_dec with (x := r0) (y := r).
  intro H1. rewrite H1. rewrite H1 in H0.
  case String.string_dec with (s1 := n0) (s2 := n).
  intro H2. rewrite H2. rewrite H2 in H0.
  inductS (Heap.get r n h); rewrite H3 in H. inversion H.
  rewrite H5 in H3. apply Heap.in_get in H3.
  assert (r1 = r2).
  apply Heap.in_equal with (r := r) (n := n) (h := Heap.update r n r1 {}).
  apply Heap.in_update_1. assumption.
  rewrite H4 in H3. assumption. inversion H.
  intro H2. apply Heap.in_update_3 in H0.
  apply Heap.not_in_empty_1 in H0. elim H0.
  right; assumption.
  intro H1. apply Heap.in_update_3 in H0.
  apply Heap.not_in_empty_1 in H0. elim H0.
  left; assumption.
  apply Heap.in_remove_3 in H0.
  assumption. split.
  apply Heap.eq_refl. reflexivity.
Qed.

Lemma sep_singleAttr : forall (r r1 r2 : ref) (n : name) (hp1 hp2 : hprop),
    r`n |-> r1 * (r`n |-> r2 *-> hp1) * hp2 ==>
    r`n |-> r1 * (r`n |-> r2 *-> hp1 * hp2).
Proof.
  unfold eimpl. unfold eval; fold eval.
  intros r r1 r2 n hp1 hp2 h s se [h1 [h2 [H [H0 H1]]]].
  try repeat destruct H1.
  destruct H3. destruct H4.
  exists x. exists (x0 |+| h2).
  split. apply Heap.pdisjoint_union.
  split. assumption.
  rewrite H3 in H.
  apply Heap.pdisjoint_sym in H.
  apply Heap.pdisjoint_union in H.
  destruct H. apply Heap.pdisjoint_sym.
  assumption.
  split. rewrite H3 in H0.
  rewrite H0.
  apply Heap.equal_3.
  apply Heap.eq_sym.
  apply Heap.union_asso.
  split. assumption.
  intros h0 [H6 H7].
  exists (x0 |+| h0). exists h2.
  split. apply Heap.pdisjoint_sym.
  apply Heap.pdisjoint_union.
  split. rewrite H3 in H.
  apply Heap.pdisjoint_sym in H.
  apply Heap.pdisjoint_union in H.
  destruct H. assumption.
  apply Heap.pdisjoint_sym in H7.
  apply Heap.pdisjoint_union in H7.
  destruct H7.
  apply Heap.pdisjoint_sym.
  assumption.
  split.
  replace ((x0 |+| h2) |+| h0) with (x0 |+| (h2 |+| h0)).
  replace (h2 |+| h0) with (h0 |+| h2).
  apply Heap.equal_3; apply Heap.union_asso.
  apply Heap.equal_3; apply Heap.union_comm.
  apply Heap.equal_3; apply Heap.union_asso.
  split. apply H5.
  split. assumption.
  apply Heap.pdisjoint_sym in H7.
  apply Heap.pdisjoint_union in H7.
  destruct H7.
  apply Heap.pdisjoint_sym.
  assumption. assumption.
Qed.

Lemma stack_hprop_1 : forall r1 r2 : ref, stack_hprop (r1 ~= r2).
Proof.
  unfold stack_hprop.
  intros; assumption.
Qed.

Lemma stack_hprop_2 : forall (n : name) (r : ref), stack_hprop (n +-> r).
Proof.
  unfold stack_hprop.
  intros; assumption.
Qed.

Lemma stack_hprop_3 : forall (r : ref) (t : rtype), stack_hprop (r =: t).
Proof.
  unfold stack_hprop.
  intros; assumption.
Qed.

Lemma stack_hprop_4 : forall (r : ref) (t : rtype), stack_hprop (r <: t).
Proof.
  unfold stack_hprop.
  intros; assumption.
Qed.

Lemma stack_hprop_5 : forall (e : expr) (r : ref), stack_hprop (e |=> r).
Proof.
  unfold stack_hprop.
  intros; assumption.
Qed.

Lemma stack_hprop_6 : forall b : bexpr, stack_hprop ('b).
Proof.
  unfold stack_hprop.
  intros; assumption.
Qed.

Lemma stack_hprop_7 : forall l1 l2 : list ref, stack_hprop (list_eq l1 l2).
Proof.
  unfold stack_hprop. induction l1, l2;
  unfold eval; fold eval; unfold list_eq; simpl; eauto.
  case l1; eauto. fold list_eq.
  assert ((exists x y, l1 = cons x y) \/ l1 = nil).
  case l1; eauto.
  destruct H as [[x [y H]] | H]; rewrite H; rewrite <- H.
  simpl; intros h1 h2 s se [H0 H1]; split;
  [|apply IHl1 with (h1 := h1)]; assumption.
  assert ((exists x y, l2 = cons x y) \/ l2 = nil).
  case l2; eauto.
  destruct H0 as [[x [y H0]] | H0]; rewrite H0; try rewrite <- H0.
  simpl; intros h1 h2 s se [H1 H2]; split;
  [|apply IHl1 with (h1 := h1)]; assumption.
  intros; assumption.
Qed.

Lemma stack_hprop_disj : forall hp1 hp2 : hprop,
    stack_hprop hp1 /\ stack_hprop hp2 -> stack_hprop (hp1 \./ hp2).
Proof.
  unfold stack_hprop.
  intros hp1 hp2 H h1 h2 s se H0.
  destruct H.
  unfold eval in H0; fold eval in H0.
  unfold eval; fold eval.
  destruct H0.
  left. apply H with (h1 := h1).
  assumption.
  right. apply H1 with (h1 := h1).
  assumption.
Qed.

Lemma stack_hprop_conj : forall hp1 hp2 : hprop,
    stack_hprop hp1 /\ stack_hprop hp2 -> stack_hprop (hp1 /.\ hp2).
Proof.
  unfold stack_hprop.
  intros hp1 hp2 H h1 h2 s se H0.
  destruct H.
  unfold eval in H0; fold eval in H0.
  destruct H0.
  unfold eval; fold eval.
  split. apply H with (h1 := h1).
  assumption.
  apply H1 with (h1 := h1).
  assumption.
Qed.

Lemma stack_hprop_neg : forall hp : hprop,
    stack_hprop hp -> stack_hprop (~` hp).
Proof.
  unfold stack_hprop; simpl.
  intros hp H h1 h2 s se H0 H1.
  elim H0; apply (H h2); assumption.
Qed.

Lemma sep_emp : forall hp : hprop, hp _|_ emp.
Proof.
  unfold separate.
  intros hp h1 h2 s se H.
  destruct H.
  apply empty in H0.
  rewrite H0.
  apply Heap.pdisjoint_empty.
Qed.

Lemma sep_sym : forall hp1 hp2 : hprop, hp1 _|_ hp2 -> hp2 _|_ hp1.
Proof.
  unfold separate.
  intros hp1 hp2 H h1 h2 s se [H0 H1].
  apply Heap.pdisjoint_sym;
  apply H with (s := s) (se := se).
  split; assumption.
Qed.

Lemma sep_1 : forall (r r1 r2 : ref) (a b : name),
     a <> b -> r`a |-> r1 _|_ r`b |-> r2.
Proof.
  unfold separate; unfold Heap.pdisjoint.
  unfold eval; fold eval.
  intros r r1 r2 a b H h1 h2 s se [H0 H1] r0 r3 r4 n [H2 H3].
  apply Heap.equal_3 in H0; apply Heap.equal_3 in H1. subst.
  case (Ref.eq_dec r0 r). intro; subst.
  case (Name.eq_dec n a). intro; subst.
  apply Heap.in_update_3 in H3; try (right; assumption).
  apply Heap.not_in_empty_1 in H3; elim H3.
  intro H0; apply Heap.in_update_3 in H2; try (right; assumption).
  apply Heap.not_in_empty_1 in H2; elim H2.
  intro H0; apply Heap.in_update_3 in H2; try (left; assumption).
  apply Heap.not_in_empty_1 in H2; elim H2.
Qed.

Lemma sep_2 : forall (r0 r1 r2 r3 : ref) (a b : name),
    r0 <> r1 -> r0`a |-> r2 _|_ r1`b |-> r3.
Proof.
  unfold separate; unfold Heap.pdisjoint.
  unfold eval; fold eval.
  intros r0 r1 r2 r3 a b H h1 h2 s se [H0 H1] r4 r5 r6 n [H2 H3].
  apply Heap.equal_3 in H0; apply Heap.equal_3 in H1. subst.
  case (Ref.eq_dec r4 r0). intro; subst.
  apply Heap.in_update_3 in H3; try (left; assumption).
  apply Heap.not_in_empty_1 in H3; elim H3.
  intro H0; apply Heap.in_update_3 in H2; try (left; assumption).
  apply Heap.not_in_empty_1 in H2; elim H2.
Qed.

Lemma sep_union : forall (hp hp' : hprop) (h h' : heap) (s : stack) (se : super_env),
    hp _|_ hp' -> eval hp h s se -> eval hp' h' s se -> eval (hp * hp') (h |+| h') s se.
Proof.
  unfold separate. unfold eval; fold eval.
  intros hp hp' h h' s se H H0 H1.
  exists h; exists h'.
  split. apply H with (s := s) (se := se).
  split; assumption.
  repeat split; assumption.
Qed.

Lemma sep_break : forall (hp hp' : hprop) (h : heap) (s : stack) (se : super_env),
    hp _|_ hp' -> eval (hp * hp') h s se
        -> exists (h1 h2 : heap), eval hp h1 s se /\ eval hp' h2 s se /\ h = h1 |+| h2.
Proof.
  unfold separate. unfold eval; fold eval.
  intros hp hp' h s se H [h1 [h2 [H0 [H1 [H2 H3]]]]].
  exists h1; exists h2.
  repeat split; assumption.
Qed.

Lemma sep_break_unique : forall (h1 h2 h3 h4 : heap) (hp1 hp2 : hprop) (s : stack) (se : super_env),
    hp1 _|_ hp2 -> eval hp1 h1 s se -> eval hp2 h2 s se -> eval hp1 h3 s se ->
        eval hp2 h4 s se -> h1 |+| h2 = h3 |+| h4 -> h1 = h3 /\ h2 = h4.
Proof.
  unfold separate. unfold Heap.pdisjoint.
  intros h1 h2 h3 h4 hp1 hp2 s se H H0 H1 H2 H3 H4.
  split; apply Heap.equal_3; unfold Heap.eq;
  apply Heap.equal_3 in H4; unfold Heap.eq in H4;
  intros r1 r2 n; destruct (H4 r1 r2 n);
  do 2 rewrite Heap.in_union_1 in H5;
  do 2 rewrite Heap.in_union_1 in H6;
  split; intro H7.
  assert (~ Heap.pin r1 n r2 h4).
  assert (~ (Heap.pin r1 n r2 h1 /\ Heap.pin r1 n r2 h4)).
  apply H with (s := s) (se := se).
  split; assumption.
  intro; elim H8; split; assumption.
  assert (Heap.pin r1 n r2 h1 \/ Heap.pin r1 n r2 h2).
  left; assumption.
  apply H5 in H9. destruct H9; [|elim H8]; assumption.
  assert (~ Heap.pin r1 n r2 h2).
  assert (~ (Heap.pin r1 n r2 h3 /\ Heap.pin r1 n r2 h2)).
  apply H with (s := s) (se := se).
  split; assumption.
  intro; elim H8; split; assumption.
  assert (Heap.pin r1 n r2 h3 \/ Heap.pin r1 n r2 h4).
  left; assumption.
  apply H6 in H9. destruct H9; [|elim H8]; assumption.
  assert (~ Heap.pin r1 n r2 h3).
  assert (~ (Heap.pin r1 n r2 h3 /\ Heap.pin r1 n r2 h2)).
  apply H with (s := s) (se := se).
  split; assumption.
  intro; elim H8; split; assumption.
  assert (Heap.pin r1 n r2 h1 \/ Heap.pin r1 n r2 h2).
  right; assumption.
  apply H5 in H9. destruct H9; [elim H8|]; assumption.
  assert (~ Heap.pin r1 n r2 h1).
  assert (~ (Heap.pin r1 n r2 h1 /\ Heap.pin r1 n r2 h4)).
  apply H with (s := s) (se := se).
  split; assumption.
  intro; elim H8; split; assumption.
  assert (Heap.pin r1 n r2 h3 \/ Heap.pin r1 n r2 h4).
  right; assumption.
  apply H6 in H9. destruct H9; [elim H8|]; assumption.
Qed.

Lemma sep_sep_conj : forall hp1 hp2 hp3 : hprop,
    hp1 _|_ hp3 -> hp1 /.\ (hp2 * hp3) ==> (hp1 /.\ hp2) * hp3.
Proof.
  intros hp1 hp2 hp3 H.
  unfold separate in H.
  unfold eimpl.
  intros h s se.
  unfold eval; fold eval.
  intro H0. destruct H0.
  try repeat destruct H1.
  destruct H2. destruct H3.
  assert (eval hp1 h s se /\ eval hp3 x0 s se).
  split. assumption. assumption.
  apply H in H5.
  rewrite H2 in H5.
  apply Heap.pdisjoint_sym in H5.
  apply Heap.pdisjoint_union in H5.
  destruct H5.
  apply Heap.pdisjoint_self in H6.
  apply Heap.equal_3 in H6.
  assert (h = x).
  rewrite H6 in H2.
  assert (x |+| {} = {} |+| x).
  apply Heap.equal_3.
  apply Heap.union_comm.
  rewrite H7 in H2.
  assert ({} |+| x = x).
  apply Heap.equal_3.
  apply Heap.union_emp.
  rewrite H8 in H2; apply H2.
  exists x. exists x0.
  split. assumption.
  split. assumption.
  split. split. rewrite <- H7; assumption.
  assumption. assumption.
Qed.

Lemma stack_conj : forall (hp1 hp2 : hprop),
    stack_hprop hp1 -> hp1 /.\ hp2 ==> hp1 * hp2.
Proof.
  unfold eimpl.
  intros hp1 hp2 H h s se.
  unfold stack_hprop in H.
  unfold eval. fold eval.
  intro H0. destruct H0.
  exists {}; exists h.
  split. apply Heap.pdisjoint_sym. apply Heap.pdisjoint_empty.
  split. apply Heap.equal_3. apply Heap.eq_sym. apply Heap.union_emp.
  split. apply H with (h1 := h). assumption. assumption.
Qed.

Lemma stack_sep_conj1 : forall hp1 hp2 hp3 : hprop,
    stack_hprop hp1 -> hp1 /.\ (hp2 * hp3) = (hp1 /.\ hp2) * hp3.
Proof.
  intros hp1 hp2 hp3 H.
  unfold stack_hprop in H.
  apply equal_1. unfold eeq.
  intros h s se.
  unfold eval; fold eval.
  split. intros [H0 [h1 [h2 [H1 [H2 [H3 H4]]]]]].
  exists h1; exists h2.
  repeat split; try apply (H h); assumption.
  intros [h1 [h2 [H0 [H1 [[H2 H3] H4]]]]].
  split. apply (H h1); assumption.
  exists h1; exists h2.
  repeat split; assumption.
Qed.

Lemma stack_sep_conj2 : forall hp1 hp2 hp3 : hprop,
    stack_hprop hp3 -> (hp1 * hp2) /.\ hp3 = (hp1 /.\ hp3) * hp2.
Proof.
  intros hp1 hp2 hp3 H.
  unfold stack_hprop in H.
  apply equal_1. unfold eeq.
  intros h s se.
  unfold eval; fold eval.
  split. intros [[h1 [h2 [H0 [H1 [H2 H3]]]]] H4].
  exists h1; exists h2.
  repeat split; try apply (H h); assumption.
  intros [h1 [h2 [H0 [H1 [[H2 H3] H4]]]]].
  split; [exists h1; exists h2|apply (H h1)];
  repeat split; assumption.
Qed.

Lemma stack_sep_conj3 : forall hp1 hp2 hp3 : hprop,
    stack_hprop hp2 -> hp1 * (hp2 /.\ hp3) = hp2 /.\ hp1 * hp3.
Proof.
  intros hp1 hp2 hp3 H.
  unfold stack_hprop in H.
  apply equal_1; unfold eeq.
  intros h s se.
  unfold eval; fold eval.
  split. intros [h1 [h2 [H0 [H1 [H2 [H3 H4]]]]]].
  split. apply (H h2); assumption.
  exists h1; exists h2.
  repeat split; assumption.
  intros [H0 [h1 [h2 [H1 [H2 [H3 H4]]]]]].
  exists h1; exists h2.
  repeat split; try apply (H h); assumption.
Qed.

Lemma sep_conj_sep : forall hp1 hp2 hp3 : hprop,
    hp1 _|_ hp2 /\ hp1 _|_ hp3 -> hp1 _|_ (hp2 * hp3).
Proof.
  unfold separate.
  intros hp1 hp2 hp3 H. destruct H.
  intros h1 h2 s se H1. destruct H1.
  unfold eval in H2; fold eval in H2.
  try repeat destruct H2.
  destruct H3. destruct H4.
  rewrite H3. apply Heap.pdisjoint_union.
  split. apply H with (s := s) (se := se).
  split; assumption.
  apply H0 with (s := s) (se := se).
  split; assumption.
Qed.

Lemma sep_impl_exc : forall hp1 hp2 hp3 : hprop,
    hp1 _|_ hp2 -> hp1 * (hp2 *-> hp3) ==> hp2 *-> (hp1 * hp3).
Proof.
  unfold separate.
  intros hp1 hp2 hp3 H.
  unfold eimpl.
  intros h s se.
  unfold eval; fold eval.
  intro H0. try repeat destruct H0.
  destruct H1. destruct H2.
  intros h1 H4. destruct H4.
  exists x. exists (x0 |+| h1).
  rewrite H1 in H5. apply Heap.pdisjoint_sym in H5.
  apply Heap.pdisjoint_union in H5. destruct H5.
  split. apply Heap.pdisjoint_union.
  split. assumption.
  apply Heap.pdisjoint_sym. assumption.
  split. rewrite H1. apply eq_sym.
  apply Heap.equal_3. apply Heap.union_asso.
  split. assumption.
  apply H3. split. assumption.
  apply Heap.pdisjoint_sym. assumption.
Qed.

Lemma impl_conj1 : forall hp1 hp2 hp3 : hprop,
    hp1 ==> hp2 -> hp1 /.\ hp3 ==> hp2 /.\ hp3.
Proof.
  intros hp1 hp2 hp3; unfold eimpl; simpl.
  intros H h s se [H0 H1].
  split; [apply H|]; assumption.
Qed.

Lemma impl_conj2 : forall hp1 hp2 hp3 : hprop,
    hp1 ==> hp2 -> hp3 /.\ hp1 ==> hp3 /.\ hp2.
Proof.
  intros hp1 hp2 hp3; unfold eimpl; simpl.
  intros H h s se [H0 H1].
  split; [|apply H]; assumption.
Qed.

Lemma impl_sep_conj1 : forall hp1 hp2 hp3 : hprop,
    hp1 ==> hp2 -> hp1 * hp3 ==> hp2 * hp3.
Proof.
  intros hp1 hp2 hp3; unfold eimpl; simpl.
  intros H h s se [h1 [h2 [H0 [H1 [H2 H3]]]]].
  exists h1; exists h2; repeat split; try apply H; assumption.
Qed.

Lemma impl_sep_conj2 : forall hp1 hp2 hp3 : hprop,
    hp1 ==> hp2 -> hp3 * hp1 ==> hp3 * hp2.
Proof.
  intros hp1 hp2 hp3; unfold eimpl; simpl.
  intros H h s se [h1 [h2 [H0 [H1 [H2 H3]]]]].
  exists h1; exists h2; repeat split; try apply H; assumption.
Qed.

Ltac Tauto := intros; try apply equal_1; unfold eeq; intros; simpl; tauto.

Lemma neg_disj : forall hp1 hp2 : hprop, ~` (hp1 \./ hp2) = ~` hp1 /.\ ~` hp2.
Proof. Tauto. Qed.

Lemma neg_conj : forall hp1 hp2 : hprop, ~` (hp1 /.\ hp2) = ~` hp1 \./ ~` hp2.
Proof. Tauto. Qed.

Lemma neg_involutive : forall hp : hprop, (~` ~` hp) = hp.
Proof. Tauto. Qed.

Lemma neg_involutive_reverse : forall hp : hprop, hp = (~` ~` hp).
Proof. Tauto. Qed.

Lemma neg_sym : forall hp hp' : hprop, hp' = (~` hp) -> hp = (~` hp').
Proof.
  intros hp hp' H.
  apply equal_1. unfold eeq.
  apply equal_1 in H. unfold eeq in H.
  intros; simpl.
  assert (forall P Q : Prop, (P <-> ~Q) -> (Q <-> ~P)).
  split; tauto.
  apply H0; apply H.
Qed.
  
Lemma eq_neg1 : forall hp : hprop, ~ ((~` hp) = hp).
Proof.
  intros hp H.
  apply equal_1 in H.
  unfold eeq in H.
  assert (forall P : Prop, ~ (~ P -> P) \/ ~ (P -> ~ P)).
  intros; tauto.
  unfold eval in H; fold eval in H.
  elim H with (h := {}) (s := Stack.init_stack) (se := TEnv.init_super_env).
  intros H2 H3.
  case H0 with (P := eval hp {} Stack.init_stack TEnv.init_super_env);
  intro H4; elim H4; assumption.
Qed.

Lemma eq_neg2 : forall hp : hprop, ~ (hp = (~` hp)).
Proof.
  intros hp H.
  apply eq_sym in H.
  apply eq_neg1 in H.
  assumption.
Qed.

Lemma disj_true_iff : forall (hp1 hp2 : hprop) (h : heap) (s : stack) (se : super_env),
      (eval (hp1 \./ hp2) h s se) <-> eval hp1 h s se \/ eval hp2 h s se.
Proof. Tauto. Qed.

Lemma disj_false_iff : forall (hp1 hp2 : hprop) (h : heap) (s : stack) (se : super_env),
      ~ (eval (hp1 \./ hp2) h s se) <-> ~ eval hp1 h s se /\ ~ eval hp2 h s se.
Proof. Tauto. Qed.

Lemma disj_true_r : forall hp : hprop, (hp \./ htrue) = htrue.
Proof. Tauto. Qed.

Lemma disj_true_l : forall hp : hprop, (htrue \./ hp) = htrue.
Proof. Tauto. Qed.
  
Lemma disj_false_r : forall hp : hprop, (hp \./ hfalse) = hp.
Proof. Tauto. Qed.

Lemma disj_false_l : forall hp : hprop, (hfalse \./ hp) = hp.
Proof. Tauto. Qed.

Lemma disj_neg_r : forall hp : hprop, (hp \./ ~` hp) = htrue.
Proof. Tauto. Qed.

Lemma disj_refl : forall hp : hprop, hp \./ hp = hp.
Proof. Tauto. Qed.

Lemma disj_comm : forall hp1 hp2 : hprop, (hp1 \./ hp2) = (hp2 \./ hp1).
Proof. Tauto. Qed.

Lemma disj_asso : forall hp1 hp2 hp3 : hprop, (hp1 \./ (hp2 \./ hp3)) = ((hp1 \./ hp2) \./ hp3).
Proof. Tauto. Qed.

Lemma conj_true_iff : forall (hp1 hp2 : hprop) (h : heap) (s : stack) (se : super_env),
      (eval (hp1 /.\ hp2) h s se) <-> eval hp1 h s se /\ eval hp2 h s se.
Proof. Tauto. Qed.

Lemma conj_false_iff : forall (hp1 hp2 : hprop) (h : heap) (s : stack) (se : super_env),
      ~ (eval (hp1 /.\ hp2) h s se) <-> ~ eval hp1 h s se \/ ~ eval hp2 h s se.
Proof. Tauto. Qed.

Lemma conj_true_r : forall hp : hprop, (hp /.\ htrue) = hp.
Proof. Tauto. Qed.

Lemma conj_true_l : forall hp : hprop, (htrue /.\ hp) = hp.
Proof. Tauto. Qed.

Lemma conj_false_r : forall hp : hprop, (hp /.\ hfalse) = hfalse.
Proof. Tauto. Qed.

Lemma conj_false_l : forall hp : hprop, (hfalse /.\ hp) = hfalse.
Proof. Tauto. Qed.

Lemma conj_neg_r : forall hp : hprop, (hp /.\ ~` hp) = hfalse.
Proof. Tauto. Qed.

Lemma conj_refl : forall hp : hprop, hp /.\ hp = hp.
Proof. Tauto. Qed.

Lemma conj_comm : forall hp1 hp2 : hprop, (hp1 /.\ hp2) = (hp2 /.\ hp1).
Proof. Tauto. Qed.

Lemma conj_asso : forall hp1 hp2 hp3 : hprop, (hp1 /.\ (hp2 /.\ hp3)) = ((hp1 /.\ hp2) /.\ hp3).
Proof. Tauto. Qed.

Lemma conj_impl: forall hp1 hp2 : hprop, (hp1 /.\ hp2) ==> hp1.
Proof.
  intros; unfold eimpl; intros h s se; simpl; tauto.
Qed.

Lemma disj_impl: forall hp1 hp2 : hprop, hp1 ==> (hp1 \./ hp2).
Proof.
  intros; unfold eimpl; intros h s se; simpl; tauto.
Qed.

Lemma conj_disj_distrib_r : forall hp1 hp2 hp3 : hprop,
    hp1 /.\ (hp2 \./ hp3) = (hp1 /.\ hp2) \./ (hp1 /.\ hp3).
Proof. Tauto. Qed.

Lemma conj_disj_distrib_l : forall hp1 hp2 hp3 : hprop,
    (hp1 \./ hp2) /.\ hp3 = (hp1 /.\ hp3) \./ (hp2 /.\ hp3).
Proof. Tauto. Qed.

Lemma disj_conj_distrib_r : forall hp1 hp2 hp3 : hprop,
    hp1 \./ (hp2 /.\ hp3) = (hp1 \./ hp2) /.\ (hp1 \./ hp3).
Proof. Tauto. Qed.

Lemma disj_conj_distrib_l : forall hp1 hp2 hp3 : hprop,
    (hp1 /.\ hp2) \./ hp3 = (hp1 \./ hp3) /.\ (hp2 \./ hp3).
Proof. Tauto. Qed.

Lemma absoption_conj : forall hp1 hp2 : hprop, hp1 /.\ (hp1 \./ hp2) = hp1.
Proof. Tauto. Qed.

Lemma absoption_disj : forall hp1 hp2 : hprop, hp1 \./ (hp1 /.\ hp2) = hp1.
Proof. Tauto. Qed.
  
Lemma sep_conj_comm : forall hp1 hp2 : hprop, hp1 * hp2 = hp2 * hp1.
Proof.
  intros hp1 hp2. apply equal_1.
  unfold eeq. unfold eval; fold eval.
  intros h s se.
  assert (forall h1 h2 : heap, h1 |+| h2 = h2 |+| h1).
  intros; apply Heap.equal_3; apply Heap.union_comm.
  split; intros [h1 [h2 [H0 [H1 [H2 H3]]]]];
  exists h2; exists h1; repeat split;
  try apply Heap.pdisjoint_sym; try rewrite H;
  assumption.
Qed.
  
Lemma sep_conj_asso : forall hp1 hp2 hp3 : hprop,
    hp1 * (hp2 * hp3) = (hp1 * hp2) * hp3.
Proof.
  intros hp1 hp2 hp3. apply equal_1.
  unfold eeq; simpl.
  intros h s se; split.
  intros [h1 [h2 [H [H0 [H1 [h3 [h4 [H2 [H3 [H4 H5]]]]]]]]]].
  exists (h1 |+| h3); exists h4.
  split. apply Heap.pdisjoint_sym.
  apply Heap.pdisjoint_union.
  rewrite H3 in H.
  apply Heap.pdisjoint_union in H.
  destruct H. split;
  apply Heap.pdisjoint_sym; assumption.
  split. rewrite H0. rewrite H3.
  apply Heap.equal_3.
  apply Heap.union_asso.
  split. exists h1; exists h3;
  split. rewrite H3 in H.
  apply Heap.pdisjoint_union in H.
  destruct H; assumption.
  repeat split; assumption. assumption.
  intros [h1 [h2 [H [H0 [[h3 [h4 [H2 [H3 [H4 H5]]]]] H6]]]]].
  exists h3; exists (h4 |+| h2).
  split. apply Heap.pdisjoint_union.
  rewrite H3 in H.
  apply Heap.pdisjoint_sym in H.
  apply Heap.pdisjoint_union in H.
  destruct H. split;
  [|apply Heap.pdisjoint_sym]; assumption.
  split. rewrite H0. rewrite H3.
  apply Heap.equal_3.
  apply Heap.eq_sym.
  apply Heap.union_asso.
  split. assumption.
  exists h4; exists h2.
  split. rewrite H3 in H.
  apply Heap.pdisjoint_sym in H.
  apply Heap.pdisjoint_union in H.
  destruct H.
  apply Heap.pdisjoint_sym.
  assumption.
  repeat split; assumption.
Qed.

Lemma sep_conj_emp1 : forall hp : hprop, hp * emp = hp.
Proof.
  intro hp. apply equal_1.
  unfold eeq. unfold eval; fold eval.
  intros h s se.
  assert (forall h1 h2 : heap, h1 |+| h2 = h2 |+| h1).
  intros; apply Heap.equal_3;
  apply Heap.union_comm.
  split. intro H0. do 3 destruct H0.
  destruct H1. destruct H2.
  apply Heap.equal_3 in H3.
  rewrite H3 in H1.
  rewrite H in H1.
  assert (x = {} |+| x).
  apply Heap.equal_3.
  apply Heap.eq_sym.
  apply Heap.union_emp.
  rewrite <- H4 in H1.
  rewrite H1. assumption.
  exists h. exists {}.
  split. apply Heap.pdisjoint_empty.
  split. rewrite H.
  apply Heap.equal_3.
  apply Heap.union_emp.
  split. apply H0.
  apply Heap.eq_refl.
Qed.

Lemma sep_conj_emp2 : forall hp : hprop, emp * hp = hp.
Proof.
  intro hp; rewrite sep_conj_comm; apply sep_conj_emp1.
Qed.

Lemma sep_conj_impl_1 : forall hp1 hp2 : hprop, hp1 * (hp1 *-> hp2) ==> hp2.
Proof.
  unfold eimpl; simpl.
  intros hp1 hp2 h s se [h1 [h2 [H [H0 [H1 H2]]]]].
  assert (h = h2 |+| h1).
  rewrite H0.
  apply Heap.equal_3.
  apply Heap.union_comm.
  rewrite H3. apply H2.
  split; [|apply Heap.pdisjoint_sym];
  assumption.
Qed.
(* 它的逆命题是错的，例如 hp1 = false 的情形。 *)

Lemma sep_conj_impl_2 : forall hp1 hp2 : hprop, hp2 ==> (hp1 *-> (hp1 * hp2)).
Proof.
  unfold eimpl; simpl.
  intros hp1 hp2 h s se H h1 [H0 H1].
  exists h1; exists h.
  split. apply Heap.pdisjoint_sym.
  assumption.
  split. apply Heap.equal_3.
  apply Heap.union_comm.
  split; assumption.
Qed.

Lemma sep_conj_impl_3 : forall hp1 hp2 hp3 : hprop,
    hp1 * hp2 ==> hp3 -> hp1 ==> (hp2 *-> hp3).
Proof.
  unfold eimpl; simpl.
  intros hp1 hp2 hp3 H h s se H0 h1 [H1 H2].
  apply H. exists h; exists h1.
  repeat split; assumption.
Qed.
  
Lemma sep_conj_impl_4 : forall hp1 hp2 hp3 hp : hprop,
    hp1 * hp2 ==> hp3 -> hp1 * hp ==> (hp2 *-> (hp3 * hp)).
Proof.
  unfold eimpl; simpl.
  intros hp1 hp2 hp3 hp H h s se [h1 [h2 [H0 [H1 [H2 H3]]]]] h3 [H4 H5].
  exists (h1 |+| h3); exists h2. split.
  apply Heap.pdisjoint_sym.
  apply Heap.pdisjoint_union.
  rewrite H1 in H5.
  apply Heap.pdisjoint_sym in H5.
  apply Heap.pdisjoint_union in H5.
  destruct H5. split;
  apply Heap.pdisjoint_sym; assumption.
  split. rewrite H1.
  assert ((h1 |+| h2) |+| h3 = h3 |+| (h1 |+| h2)).
  apply Heap.equal_3; apply Heap.union_comm.
  assert (h1 |+| h3 = h3 |+| h1).
  apply Heap.equal_3; apply Heap.union_comm.
  rewrite H6. rewrite H7.
  apply Heap.equal_3; apply Heap.union_asso.
  split. apply H. exists h1; exists h3.
  split. rewrite H1 in H5.
  apply Heap.pdisjoint_sym in H5.
  apply Heap.pdisjoint_union in H5.
  destruct H5. apply Heap.pdisjoint_sym.
  assumption.
  repeat split; assumption.
  assumption.
Qed.

Lemma sep_conj_impl_5 : forall hp1 hp2 hp3 hp : hprop,
    hp1 ==> (hp2 *-> hp3) -> hp1 * hp ==> (hp2 *-> (hp3 * hp)).
Proof.
  unfold eimpl; simpl.
  intros hp1 hp2 hp3 hp H h s se [h1 [h2 [H0 [H1 [H2 H3]]]]] h3 [H4 H5].
  exists (h1 |+| h3); exists h2. split.
  apply Heap.pdisjoint_sym.
  apply Heap.pdisjoint_union.
  rewrite H1 in H5.
  apply Heap.pdisjoint_sym in H5.
  apply Heap.pdisjoint_union in H5.
  destruct H5. split;
  apply Heap.pdisjoint_sym; assumption.
  split. rewrite H1.
  assert ((h1 |+| h2) |+| h3 = h3 |+| (h1 |+| h2)).
  apply Heap.equal_3; apply Heap.union_comm.
  assert (h1 |+| h3 = h3 |+| h1).
  apply Heap.equal_3; apply Heap.union_comm.
  rewrite H6. rewrite H7.
  apply Heap.equal_3; apply Heap.union_asso.
  split; [apply H; try split|]; try assumption.
  rewrite H1 in H5.
  apply Heap.pdisjoint_sym in H5.
  apply Heap.pdisjoint_union in H5.
  destruct H5. apply Heap.pdisjoint_sym.
  assumption.
Qed.

Lemma sep_impl_conj : forall hp1 hp2 hp3 : hprop,
    hp1 *-> (hp2 /.\ hp3) = (hp1 *-> hp2) /.\ (hp1 *-> hp3).
Proof.
  intros hp1 hp2 hp3. apply equal_1.
  unfold eeq; simpl.
  intros; split; intro H.
  split; intros h1 [H0 H1];
  apply H; split; assumption.
  destruct H. intros h1 [H1 H2].
  split; [apply H | apply H0]; split; assumption.
Qed.

Lemma sep_impl_impl : forall hp1 hp2 hp3 : hprop,
    hp1 *-> (hp2 *-> hp3) = (hp1 * hp2) *-> hp3.
Proof.
  intros hp1 hp2 hp3. apply equal_1.
  unfold eeq; simpl.
  intros; split. intros H h1 [[h2 [h3 [H0 [H1 [H2 H3]]]]] H4].
  assert (eval hp1 h2 s se /\ h |*| h2 ->
    eval hp2 h3 s se /\ (h |+| h2) |*| h3 ->
    eval hp3 ((h |+| h2) |+| h3) s se).
  intro H5; apply H with (h1 := h2); assumption.
  rewrite H1. rewrite H1 in H4.
  apply Heap.pdisjoint_union in H4.
  destruct H4.
  assert (h |+| h2 |+| h3 = (h |+| h2) |+| h3).
  apply Heap.equal_3.
  apply Heap.union_asso.
  rewrite H7. apply H5.
  split; assumption.
  split. assumption.
  apply Heap.pdisjoint_sym.
  apply Heap.pdisjoint_union.
  split; apply Heap.pdisjoint_sym;
  assumption.
  intros H h1 [H0 H1] h0 [H2 H3].
  assert ((exists h2 h3 : heap, h2 |*| h3 /\ h1 |+| h0 = h2 |+| h3 /\
    eval hp1 h2 s se /\ eval hp2 h3 s se) /\ h |*| (h1 |+| h0) ->
    eval hp3 (h |+| (h1 |+| h0)) s se).
  apply H with (h1 := h1 |+| h0).
  assert ((h |+| h1) |+| h0 = h |+| (h1 |+| h0)).
  apply Heap.equal_3.
  apply Heap.eq_sym.
  apply Heap.union_asso.
  rewrite H5. apply H4.
  split. exists h1. exists h0.
  split. apply Heap.pdisjoint_sym in H3.
  apply Heap.pdisjoint_union in H3.
  destruct H3.
  apply Heap.pdisjoint_sym.
  assumption.
  repeat split; assumption.
  apply Heap.pdisjoint_union.
  apply Heap.pdisjoint_sym in H3.
  apply Heap.pdisjoint_union in H3.
  destruct H3. split;
  [|apply Heap.pdisjoint_sym]; assumption.
Qed.

Lemma exist_forall : forall (rhp : ref -> hprop),
    (~` =| rhp) = \-/ (fun r => ~` rhp r).
Proof.
  intro rhp. apply equal_1.
  unfold eeq. unfold eval; fold eval.
  intros h s se.
  split. apply not_ex_all_not.
  apply all_not_not_ex.
Qed.

Lemma forall_exist : forall (rhp : ref -> hprop),
    (~` \-/ rhp) = =| (fun r => ~` rhp r).
Proof.
  intro rhp. apply equal_1.
  unfold eeq. unfold eval; fold eval.
  intros h s se.
  split. apply not_all_ex_not.
  apply ex_not_not_all.
Qed.

Lemma exist_comm : forall rhp : ref -> ref -> hprop,
    =|(fun r1 => =|(fun r2 => rhp r1 r2)) =
    =|(fun r2 => =|(fun r1 => rhp r1 r2)).
Proof.
  intro rhp; apply equal_1;
  unfold eeq; unfold eval; fold eval.
  intros h s se. split; intros [r1 [r2 H]];
  exists r2; exists r1; assumption.
Qed.

Lemma forall_comm : forall rhp : ref -> ref -> hprop,
    \-/(fun r1 => \-/(fun r2 => rhp r1 r2)) =
    \-/(fun r2 => \-/(fun r1 => rhp r1 r2)).
Proof.
  intro rhp; apply equal_1;
  unfold eeq; unfold eval; fold eval.
  intros h s se. split; intros H r1 r2; apply H.
Qed.

Lemma exist_conj : forall (rhp : ref -> hprop) (hp : hprop),
    (=| rhp) /.\ hp = =| (fun r => rhp r /.\ hp).
Proof.
  intros rhp hp. apply equal_1.
  unfold eeq. unfold eval; fold eval.
  intros h s se.
  split. intros [[r H] H0].
  exists r; split; assumption.
  intros [r [H H0]].
  split; [exists r|]; assumption.
Qed.

Lemma exist_conj' : forall (rhp : ref -> hprop) (hp : hprop),
    hp /.\ (=| rhp) = =| (fun r => hp /.\ rhp r).
Proof.
  intros rhp hp. apply equal_1.
  unfold eeq. unfold eval; fold eval.
  intros h s se. split.
  intros [H [r H0]].
  exists r; split; assumption.
  intros [r [H H0]].
  split; [|exists r]; assumption.
Qed.

Lemma existl_conj : forall (rhp : list ref -> hprop) (hp : hprop),
    (E| rhp) /.\ hp = E| (fun l => rhp l /.\ hp).
Proof.
  intros rhp hp. apply equal_1.
  unfold eeq. unfold eval; fold eval.
  intros h s se.
  split. intros [[l H] H0].
  exists l; split; assumption.
  intros [l [H H0]].
  split; [exists l|]; assumption.
Qed.

Lemma existl_conj' : forall (rhp : list ref -> hprop) (hp : hprop),
    hp /.\ (E| rhp) = E| (fun l => hp /.\ rhp l).
Proof.
  intros rhp hp. apply equal_1.
  unfold eeq. unfold eval; fold eval.
  intros h s se. split.
  intros [H [l H0]].
  exists l; split; assumption.
  intros [l [H H0]].
  split; [|exists l]; assumption.
Qed.

Lemma exist_disj : forall (rhp : ref -> hprop) (hp : hprop),
    (=| rhp) \./ hp = =| (fun r => rhp r \./ hp).
Proof.
  intros rhp hp. apply equal_1.
  unfold eeq. unfold eval; fold eval.
  intros h s se.
  split. intro H. do 2 try destruct H.
  exists x; left; assumption.
  exists Ref.rnull; right; assumption.
  intro H. do 2 try destruct H.
  left; exists x; assumption.
  right; assumption.
Qed.

Lemma exist_sep_conj : forall (rhp : ref -> hprop) (hp : hprop),
    (=| rhp) * hp = =| (fun r => rhp r * hp).
Proof.
  intros rhp hp. apply equal_1.
  unfold eeq. unfold eval; fold eval.
  intros h s se.
  split. intros [h1 [h2 [H [H0 [[r H1] H2]]]]].
  exists r. exists h1. exists h2.
  repeat split; assumption.
  intros [r [h1 [h2 [H [H0 [H1 H2]]]]]].
  exists h1. exists h2.
  repeat split; try exists r; assumption.
Qed.

Lemma exist_sep_conj' : forall (rhp : ref -> hprop) (hp : hprop),
    hp * (=| rhp) = =| (fun r => hp * rhp r).
Proof.
  intros rhp hp. apply equal_1.
  unfold eeq. unfold eval; fold eval.
  intros h s se.
  split. intros [h1 [h2 [H [H0 [H1 [r H2]]]]]].
  exists r. exists h1. exists h2.
  repeat split; assumption.
  intros [r [h1 [h2 [H [H0 [H1 H2]]]]]].
  exists h1. exists h2.
  repeat split; try exists r; assumption.
Qed.

Lemma forall_conj : forall (rhp : ref -> hprop) (hp : hprop),
    (\-/ rhp) /.\ hp = \-/ (fun r => rhp r /.\ hp).
Proof.
  intros rhp hp. apply equal_1.
  unfold eeq. unfold eval; fold eval.
  intros h s se.
  split. intros H r. destruct H.
  split. apply H. assumption.
  intro H. split. intro r.
  destruct H with (r := r).
  assumption.
  destruct H with (r := Ref.rnull).
  assumption.
Qed.

Lemma forall_disj : forall (rhp : ref -> hprop) (hp : hprop),
    (\-/ rhp) \./ hp ==> \-/ (fun r => rhp r \./ hp).
Proof.
  unfold eimpl. unfold eval; fold eval.
  intros rhp hp h s se.
  intros H r. destruct H.
  left. apply H.
  right. assumption.
Qed.

Lemma forall_sep_conj : forall (rhp : ref -> hprop) (hp : hprop),
    (\-/ rhp) * hp ==> \-/ (fun r => rhp r * hp).
Proof.
  unfold eimpl. unfold eval; fold eval.
  intros rhp hp h s se.
  intros H r. try repeat destruct H.
  destruct H0. destruct H1.
  exists x. exists x0.
  split. assumption.
  split. assumption.
  split. apply H1.
  assumption.
Qed.

Lemma impl_exist : forall (r : ref) (rhp : ref -> hprop),
    rhp r ==> =| rhp.
Proof.
  unfold eimpl. unfold eval; fold eval.
  intros r rhp h s se H.
  exists r; assumption.
Qed.

Lemma forall_impl : forall (r : ref) (rhp : ref -> hprop),
    \-/ rhp ==> rhp r.
Proof.
  unfold eimpl. unfold eval; fold eval.
  intros r rhp h s se H.
  apply H.
Qed.

Lemma false_impl : forall hp : hprop, hfalse ==> hp.
Proof.
  unfold eimpl. unfold eval; fold eval.
  intros; elim H.
Qed.

Lemma impl_true : forall hp : hprop, hp ==> htrue.
Proof.
  unfold eimpl; intros; reflexivity.
Qed.

Lemma forall_exist_impl : forall (rhp : ref -> hprop) (hp : hprop),
    (forall r, rhp r ==> hp) -> (=| rhp) ==> hp.
Proof.
  unfold eimpl; intros rhp hp H h s se H0.
  unfold eval in H0; fold eval in H0.
  destruct H0; apply H in H0; assumption.
Qed.

Lemma exist_exist_impl : forall (rhp : ref -> hprop) (hp : hprop),
    (exists r, hp ==> rhp r) -> hp ==> =| rhp.
Proof.
  unfold eimpl; intros rhp hp [r H] h s se H0.
  unfold eval; fold eval.
  exists r; apply H; assumption.
Qed.

Lemma forall_exist_impl2 : forall (rhp : list ref -> hprop) (hp : hprop),
    (forall l, rhp l ==> hp) -> (E| rhp) ==> hp.
Proof.
  unfold eimpl; intros rhp hp H h s se H0.
  unfold eval in H0; fold eval in H0.
  destruct H0 as [l H0]; apply (H l); assumption.
Qed.

Lemma exist_exist_impl2 : forall (rhp : list ref -> hprop) (hp : hprop),
    (exists l, hp ==> rhp l) -> hp ==> E| rhp.
Proof.
  unfold eimpl; intros rhp hp [l H] h s se H0.
  unfold eval; fold eval.
  exists l; apply H; assumption.
Qed.

Lemma param_arg : forall (r : ref) (rhp : ref -> hprop),
    .\ rhp &r = rhp r.
Proof.
  intros r rhp. apply equal_1.
  unfold eeq. intros h s se.
  unfold eval; fold eval. reflexivity.
Qed.

Lemma param_arg2 : forall (n : name) (rhp : ref -> hprop),
    .\ rhp &^n = =| (fun r => n +-> r /.\ rhp r).
Proof.
  intros n rhp. apply equal_1.
  unfold eeq. intros h s se.
  unfold eval; fold eval.
  reflexivity.
Qed.

Lemma param_arg3 : forall (l : list ref) (rhp : list ref -> hprop),
    ,\ rhp &`l = rhp l.
Proof.
  intros l rhp. apply equal_1.
  unfold eeq. intros h s se.
  unfold eval; fold eval.
  reflexivity.
Qed.

Lemma param_ext : forall (rhp1 : ref -> hprop) (rhp2 : ref -> ref -> hprop),
    =| (fun r => (rhp1 r /.\ .\ fun v => (rhp2 v) r)) =
    .\ (fun v => =| (fun r => rhp1 r /.\ (rhp2 v) r)).
Proof.
  intros rhp1 rhp2. apply equal_1.
  unfold eeq. intros h s se.
  unfold eval; fold eval.
  split. intros [r [H [r0 H0]]].
  exists r0; exists r; split; assumption.
  intros [r [r0 [H H0]]]. exists r0.
  split; [|exists r]; assumption.
Qed.

Lemma param_ext2 : forall (rhp1 : ref -> hprop) (rhp2 : list ref -> ref -> hprop),
    =| (fun r => (rhp1 r /.\ ,\ fun v => (rhp2 v) r)) =
    ,\ (fun v => =| (fun r => rhp1 r /.\ (rhp2 v) r)).
Proof.
  intros rhp1 rhp2. apply equal_1.
  unfold eeq. intros h s se.
  unfold eval; fold eval.
  split. intros [r [H [lr H0]]].
  exists lr. exists r. split; assumption.
  intros [lr [r [H H0]]]. exists r.
  split; [|exists lr]; assumption.
Qed.

Lemma func_ext1 : forall rhp1 rhp2,
    (forall r, rhp1 r = rhp2 r) ->
    =| (fun r => rhp1 r) = =| (fun r => rhp2 r).
Proof.
  intros rhp1 rhp2 H.
  apply functional_extensionality in H.
  rewrite H; reflexivity.
Qed.

Lemma func_ext2 : forall rhp1 rhp2,
    (forall r, rhp1 r = rhp2 r) ->
    \-/ (fun r => rhp1 r) = \-/ (fun r => rhp2 r).
Proof.
  intros rhp1 rhp2 H.
  apply functional_extensionality in H.
  rewrite H; reflexivity.
Qed.

Lemma func_ext3 : forall rhp1 rhp2,
    (forall r, rhp1 r = rhp2 r) ->
    .\ (fun r => rhp1 r) = .\ (fun r => rhp2 r).
Proof.
  intros rhp1 rhp2 H.
  apply functional_extensionality in H.
  rewrite H; reflexivity.
Qed.

Lemma func_ext4 : forall rhp1 rhp2,
    (forall r, rhp1 r = rhp2 r) ->
    ,\ (fun r => rhp1 r) = ,\ (fun r => rhp2 r).
Proof.
  intros rhp1 rhp2 H.
  apply functional_extensionality in H.
  rewrite H; reflexivity.
Qed.

Lemma var_exp : forall (n : name) (r : ref), ^n |=> r = (n +-> r).
Proof.
  intros n r. apply equal_1.
  unfold eeq. intros h s se.
  unfold eval.
  reflexivity.
Qed.

Lemma lemma3_23: forall (hp : hprop) (e : expr) (a : name) (h : heap) (s : stack) (se : super_env),
    (eval (subst_name_1 a e hp) h s se)
    <-> (eval hp h (Stack.update a (Expr.eval e s) s) se).
Proof.
  intros hp e a h s se.
  split.
  intro H.
Admitted.

Lemma lemma3_23': forall (hp : hprop) (b : bexpr) (a : name) (h : heap) (s : stack) (se : super_env),
    (eval (subst_name_2 a b hp) h s se)
    <-> (eval hp h (Stack.update a (BExpr.bool2ref (BExpr.eval b s)) s) se).
Proof.
  intros hp b a h s se.
  split.
  intro H.
Admitted. 

Lemma lemma3_26: forall (r r1 r2 : ref) (hp1 hp2 : hprop) (a : name),
    r`a |-> r1 * ((r`a |-> r2 *-> hp1) * hp2) ==>
    r`a |-> r1 * (r`a |-> r2 *-> (hp1 * hp2)).
Proof.
  unfold eimpl. intros r r1 r2 hp1 hp2 a h s se.
  unfold eval; fold eval. intro H.
  do 3 destruct H. destruct H0. destruct H1.
  do 3 destruct H2. destruct H3. destruct H4.
  exists x. exists x0.
  split. assumption.
  split. assumption.
  split. assumption.
  intros h1 H6. destruct H6.
  exists (x1 |+| h1). exists x2.
  rewrite H3 in H7.
  apply Heap.pdisjoint_sym in H7.
  apply Heap.pdisjoint_union in H7.
  destruct H7. split.
  apply Heap.pdisjoint_sym.
  apply Heap.pdisjoint_union.
  split. apply Heap.pdisjoint_sym.
  assumption. apply Heap.pdisjoint_sym.
  assumption. split. rewrite H3.
  apply Heap.equal_3.
  assert (((x1 |+| x2) |+| h1) |=| (h1 |+| (x1 |+| x2))).
  apply Heap.union_comm.
  apply Heap.equal_3 in H9.
  rewrite H9.
  assert ((x1 |+| h1) |=| (h1 |+| x1)).
  apply Heap.union_comm.
  apply Heap.equal_3 in H10.
  rewrite H10. apply Heap.union_asso.
  split. apply H4.
  split. assumption.
  apply Heap.pdisjoint_sym.
  assumption. assumption.
Qed.

Close Scope lang_scope.
Close Scope heap_scope.
Close Scope hprop_scope.

End HProp.

Bind Scope hprop_scope with HProp.hprop.
Delimit Scope hprop_scope with hprop.

Infix "==" := HProp.eeq (at level 70) : hprop_scope.
Infix "==>" := HProp.eimpl (at level 75) : hprop_scope.
Infix "_|_" := HProp.separate (at level 40) : hprop_scope.

Infix "~=" := HProp.eqref (at level 20) : hprop_scope.
Infix "+->" := HProp.eqvar (at level 20) : hprop_scope.
Infix "=:" := HProp.vtype (at level 20) : hprop_scope.
Infix "<:" := HProp.vsubtype (at level 20) : hprop_scope.
Notation "o ` x |-> r" := (HProp.singleAttr o x r) (at level 25) : hprop_scope.
Notation "o ` x ~-> r" := (HProp.pointTo o x r) (at level 25) : hprop_scope.
Infix "|=>" := HProp.exp (at level 20) : hprop_scope.
Notation "' b" := (HProp.bexp b) (at level 20) : hprop_scope.
Notation "~` hp" := (HProp.neg hp) (at level 40) : hprop_scope.
Infix "/.\" := HProp.conj (at level 60, right associativity) : hprop_scope.
Infix "\./" := HProp.disj (at level 60, right associativity) : hprop_scope.
Infix "-->" := HProp.impl (at level 65, right associativity) : hprop_scope.
Infix "*" := HProp.sep_conj : hprop_scope.
Infix "*->" := HProp.sep_impl (at level 65, right associativity) : hprop_scope.
Notation "=| hp" := (HProp.hexist hp) (at level 60, right associativity) : hprop_scope.
Notation "\-/ hp" := (HProp.hforall hp) (at level 60, right associativity) : hprop_scope.
Notation ".\ p" := (HProp.add_param p) (at level 5, right associativity) : hprop_scope.
Infix "&" := HProp.pass_arg (at level 15, left associativity) : hprop_scope.
Infix "&^" := HProp.pass_arg2 (at level 15, left associativity) : hprop_scope.
Notation "|P| n @ a" := (HProp.abs_pred n a) (at level 5) : hprop_scope.
Notation ",\ p" := (HProp.list_param p) (at level 5, right associativity) : hprop_scope.
Infix "&`" := HProp.list_arg (at level 15, left associativity) : hprop_scope.
Notation "E| hp" := (HProp.exist_list hp) (at level 60, right associativity) : hprop_scope.
