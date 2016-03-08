Require Export Asn.
Require Export Sem.

(*-----  Abstract Data Type  -----*)

(*  Specification Type  *)

Module Type SPEC.

Parameter heap : Type.
Parameter stack : Type.
Definition name := Name.name.
Definition method := Method.method.
Definition rtype := RType.rtype.
Definition ref := Ref.ref.
Definition bexpr := BExpr.bexpr.
Definition expr := Expr.expr.
Definition cmd := Lang.cmd.
Definition hprop := HProp.hprop.
Definition state := State.state.

Definition spec := (hprop * hprop)%type.
Parameter program_spec : Type.
Parameter init_program_spec : program_spec.

Parameter pred_env : Type.
Parameter init_pred_env : pred_env.

Parameter update_pred : name -> rtype -> hprop -> pred_env -> pred_env.
Parameter get_pred : name -> rtype -> pred_env -> option hprop.
Parameter pred_in : name -> rtype -> hprop -> pred_env -> Prop.
Parameter evalP : rtype -> pred_env -> hprop -> hprop.
(* bind the predicate families in specifications to the entries of the class *)

Parameter cmd_satisfy : state -> rtype -> cmd -> pred_env -> spec -> Prop.
Parameter bs : state -> rtype -> method -> program_spec -> Prop.
Parameter method_satisfy : state -> rtype -> method -> pred_env -> program_spec -> Prop.
Parameter program_satisfy : state -> pred_env -> program_spec -> Prop.

Parameter spec_in : rtype -> method -> spec -> program_spec -> Prop.
Parameter add_spec : rtype -> method -> spec -> program_spec -> program_spec.
Parameter get_spec : rtype -> method -> program_spec -> option spec.

Parameter refine : spec -> spec -> Prop.

Axiom pred_update_1 : forall n t p e, pred_in n t p (update_pred n t p e).
Axiom pred_update_2 : forall n1 n2 t1 t2 p1 p2 e,
    (t1 <> t2 \/ n1 <> n2) -> pred_in n1 t1 p1 e ->
        pred_in n1 t1 p1 (update_pred n2 t2 p2 e).
Axiom pred_update_3 : forall n1 n2 t1 t2 p1 p2 e,
    (t1 <> t2 \/ n1 <> n2) -> pred_in n1 t1 p1 (update_pred n2 t2 p2 e) ->
        pred_in n1 t1 p1 e.
Axiom pred_get : forall n t p e, pred_in n t p e <-> get_pred n t e = Some p.
Axiom pred_not_get : forall n t e,
    (forall p, ~ pred_in n t p e) <-> get_pred n t e = None.

Axiom spec_add_1 : forall t m s ps, spec_in t m s (add_spec t m s ps).
Axiom spec_add_2 : forall t1 t2 m1 m2 s1 s2 ps,
    (t1 <> t2 \/ m1 <> m2) -> spec_in t1 m1 s1 ps ->
        spec_in t1 m1 s1 (add_spec t2 m2 s2 ps).
Axiom spec_add_3 : forall t1 t2 m1 m2 s1 s2 ps,
    (t1 <> t2 \/ m1 <> m2) -> spec_in t1 m1 s1 (add_spec t2 m2 s2 ps) ->
        spec_in t1 m1 s1 ps.
Axiom spec_get : forall t m s ps, spec_in t m s ps <-> get_spec t m ps = Some s.
Axiom spec_not_get : forall t m ps,
    (forall s, ~ spec_in t m s ps) <-> get_spec t m ps = None.

Axiom spec_get_add_1 : forall t m s ps, get_spec t m (add_spec t m s ps) = Some s.
Axiom spec_get_add_2 : forall t1 t2 m1 m2 s ps, (t1 <> t2 \/ m1 <> m2) ->
    get_spec t1 m1 (add_spec t2 m2 s ps) = get_spec t1 m1 ps.

Notation "S + e , t |- sp # c" := (cmd_satisfy S t c e sp) (at level 30) : spec_scope.
Notation "S + e |> ps # t , m" := (method_satisfy S t m e ps) (at level 30) : spec_scope.
Notation "S + e |= ps" := (program_satisfy S e ps) (at level 30) : spec_scope.
Infix "<<=" := refine (at level 70) : spec_scope.

Open Scope spec_scope.
Open Scope hprop_scope.
Open Scope string_scope.

Axiom prog_satis_init : forall (S : state) (e : pred_env), S + e |= init_program_spec.

Axiom refine_refl : forall sp : spec, sp <<= sp.
Axiom refine_trans : forall sp1 sp2 sp3 : spec,
    sp1 <<= sp2 -> sp2 <<= sp3 -> sp1 <<= sp3.
Axiom refine_cons1 : forall p1 p2 p3 : hprop, p3 ==> p2 -> (p1, p2) <<= (p1, p3).
Axiom refine_cons2 : forall p1 p2 p3 : hprop, p1 ==> p3 -> (p1, p2) <<= (p3, p2).

(* verification rules *)
(* {P} skip {P} *)
Axiom h_skip : forall (p : hprop) (S : state) (t : rtype) (e : pred_env),
    S + e, t |- (p, p) # Lang.skip.
(* {P[e/n]} n := e {P} *)
Axiom h_asn : forall (p1 p2 : hprop) (n : name) (e : expr) (S : state)
                     (t : rtype) (pe : pred_env),
    p1 ==> HProp.subst_name_1 n e p2 ->
    S + pe,t |- (p1, p2) # Lang.assign n e.
(* {P[b/n]} n := b {P} *)
Axiom h_asnb : forall (p1 p2 : hprop) (n : name) (b : bexpr) (S : state)
                      (t : rtype) (e : pred_env),
               p1 ==> HProp.subst_name_2 n b p2 -> 
               S + e, t |- (p1, p2) # Lang.assignb n b.

(* {v = r1 /\ r1.a |-> - /\ e = r2} v.a := e {v = r1 /\ r1.a |-> r2 /\ e = r2} *)
Axiom h_mut : forall (v a : name) (e : expr) (S : state) (r1 r2 r3: ref)
                     (t : rtype) (pe : pred_env),
    S + pe, t |- (v +-> r1 /.\ r1`a |-> r3 /.\ e |=> r2,
                 v +-> r1 /.\ r1`a |-> r2 /.\ e |=> r2) # Lang.fwrite v a e.
(* x <> v -> {v = r1 /\ r1.a |-> r2} x := v.a {v = r1 /\ r1.a |-> r2 /\ x = r2} *)
Axiom h_lkp : forall (x v a: name) (S : state) (r1 r2: ref) (t : rtype) (e : pred_env),
    x <> v ->
    S + e, t |- (v +-> r1 /.\ r1`a |-> r2,
                 v +-> r1 /.\ r1`a |-> r2 /.\ x +-> r2) # Lang.fread x v a.
(* {v = r1 /\ r1.a |-> r2} x := x.a {x = r2 /\ r1.a |-> r2} *)
Axiom h_lkp' : forall (x a: name) (S : state) (r1 r2: ref) (t : rtype) (e : pred_env),
    S + e, t |- (x +-> r1 /.\ r1`a |-> r2,
                 x +-> r2 /.\ r1`a |-> r2) # Lang.fread x x a.

(* {v = r /\ r <: C} x := (C)v {x = r} *)
Axiom h_cast : forall (x v: name) (C : rtype) (S : state) (r: ref)
                      (t : rtype) (e : pred_env),
    S + e, t |- (v +-> r /.\ r <: C, x +-> r) # Lang.cast x C v.

(* {P[e/"res"]} return e {P} *)
Axiom h_res : forall (p1 p2 : hprop) (e : expr) (S : state) (t : rtype) (pe : pred_env),
    p1 ==> HProp.subst_name_1 "res" e p2 ->
    S + pe, t |- (p1, p2) # (Lang.creturn e).

(* {P} c1 {Q} -> {Q} c2 {R} -> {P} c1; c2 {R} *)
Axiom h_seq : forall (p q r: hprop) (c1 c2 : cmd) (S : state)
                     (t : rtype) (e : pred_env),
    S + e, t |- (p, q) # c1 -> S + e, t |- (q, r) # c2 ->
    S + e, t |- (p, r) # (Lang.cseq c1 c2).

Parameter subst_args1 : hprop -> name -> name -> list name -> list expr -> hprop.
Parameter subst_args2 : hprop -> list name -> list expr -> hprop.

(* {P} C.m(args) {Q} -> v : C ->
   {P[v/this][le/args]} x := v.m(le) {Q[x/res][v/this][le/args]}*)
Axiom h_dinv : forall S e v t t' m p1 p2 mb ps x le,
    get_spec t m ps = Some (p1, p2) ->
    MEnv.find_mbody (State.get_mbody_env S) t m = Some mb ->
    DType.get_dtype v (State.get_dtype S) = Some t ->
    S + e, t' |- (subst_args1 p1 x v (MEnv.get_args mb) le,
                  subst_args1 p2 x v (MEnv.get_args mb) le) # Lang.dcall x v m le.

(* {P} C.m(args) {Q} ->
   {P[v/this][le/args]} x := v.C::m(le) {Q[x/res][v/this][le/args]}*)
Axiom h_sinv : forall S e v t t' m p1 p2 mb ps x le,
    get_spec t m ps = Some (p1, p2) ->
    MEnv.find_mbody (State.get_mbody_env S) t m = Some mb ->
    S + e, t' |- (subst_args1 p1 x v (MEnv.get_args mb) le,
                  subst_args1 p2 x v (MEnv.get_args mb) le) # Lang.scall x v t m le.

(* {P} C(args) {Q} ->
   {P[le/args]} x := new C(le) {Q[x/this][le/args]}*)
Axiom h_new : forall S e p1 p2 mb ps x t t' le,
    get_spec t t ps = Some (p1, p2) ->
    MEnv.find_mbody (State.get_mbody_env S) t t = Some mb ->
    S + e, t' |- (subst_args2 p1 (MEnv.get_args mb) le,
                  HProp.subst_name_3 "this" x
                    (subst_args2 p2 (MEnv.get_args mb) le)) # Lang.calloc x t le.

(* (l1 = l2 -> {P} c {Q}) -> {P /\ l1 = l2} c {Q} *)
Axiom list_eq_ext : forall S e t c (l1 l2 : list ref) (hp1 hp2 : hprop),
    (l1 = l2 -> S + e, t |- (hp1, hp2) # c) ->
     S + e, t |- (hp1 /.\ HProp.list_eq l1 l2, hp2) # c.

(* "the variables c modifies" is disjoint with "the free variables in R"
   -> {P} c {Q} -> {P * R} c {Q * R} *)
Axiom h_frame : forall (p q r: hprop) (c : cmd) (S : state) (t : rtype) (e : pred_env),
    sset_dsj (Lang.md c) (HProp.fv r) ->
    S + e, t |- (p, q) # c -> S + e, t |- (p * r, q * r) # c.
(* "the variables c modifies" is disjoint with "the free variables in R"
   -> "R is an assertion independent of the heap"
   -> {P} c {Q} -> {P /\ R} c {Q /\ R} *)
Axiom h_frame' : forall (p q r: hprop) (c : cmd) (S : state)
                        (t : rtype) (e : pred_env),
    sset_dsj (Lang.md c) (HProp.fv r) -> HProp.stack_hprop r ->
        S + e, t |- (p, q) # c -> S + e, t |- (p /.\ r, q /.\ r) # c.

(* {P} c {Q /\ R} <-> {P} c {Q} /\ {P} c {R} *)
Axiom h_div1 : forall (p q r: hprop) (c : cmd) (S : state)
                     (t : rtype) (e : pred_env),
    S + e, t |- (p, q /.\ r) # c <->
    S + e, t |- (p, q) # c /\ S + e, t |- (p, r) # c.
(* {P \/ R} c {Q} <-> {P} c {Q} /\ {R} c {Q} *)
Axiom h_div2 : forall (p q r: hprop) (c : cmd) (S : state)
                     (t : rtype) (e : pred_env),
    S + e, t |- (p \./ r, q) # c <->
    S + e, t |- (p, q) # c /\ S + e, t |- (r, q) # c.

(* {P /\ b} c1 {Q} -> {P /\ ~b} c2 {Q} ->
   {P} if b then c1 else c2 {Q} *)
Axiom h_cond : forall (p q : hprop) (b : BExpr.bexpr) (c1 c2 : cmd) (S : state)
                      (t : rtype) (e : pred_env),
              S + e, t |- (p /.\ 'b, q) # c1
           -> S + e, t |- (p /.\ ~` 'b, q) # c2
           -> S + e, t |- (p, q) # Lang.cif b c1 c2.
(* (P -> b) -> {P} c1 {Q} -> {P} if b then c1 else c2 {Q} *)
Axiom h_cond1 : forall (p q : hprop) (b : BExpr.bexpr) (c1 c2 : cmd) (S : state)
                      (t : rtype) (e : pred_env),
    p ==> 'b -> S + e, t |- (p, q) # c1
    -> S + e, t |- (p, q) # Lang.cif b c1 c2.
(* (P -> ~b) -> {P} c2 {Q} -> {P} if b then c1 else c2 {Q} *)
Axiom h_cond2 : forall (p q : hprop) (b : BExpr.bexpr) (c1 c2 : cmd) (S : state)
                      (t : rtype) (e : pred_env),
    p ==> ~` 'b -> S + e, t |- (p, q) # c2
    -> S + e, t |- (p, q) # Lang.cif b c1 c2.

(* {P /\ b} c {P} -> {P} while b c {P /\ ~b} *)
Axiom h_iter : forall (p : hprop) (b : BExpr.bexpr) (c : cmd) (S : state)
                      (t : rtype) (e : pred_env),
    S + e, t |- (p /.\ 'b, p) # c ->
    S + e, t |- (p, p /.\ ~` 'b) # (Lang.cwhile b c).
Proof.

(* (P2 -> P3) -> {P1} c {P2} -> {P1} c {P3} *)
Axiom h_cons_1 : forall (p1 p2 p3 : hprop) (c : cmd) (S : state)
                        (t : rtype) (e : pred_env),
    p2 ==> p3 -> S + e, t |- (p1, p2) # c -> S + e, t |- (p1, p3) # c.
(* (P3 -> P1) -> {P1} c {P2} -> {P3} c {P2} *)
Axiom h_cons_2 : forall (p1 p2 p3 : hprop) (c : cmd) (S : state)
                        (t : rtype) (e : pred_env),
    p3 ==> p1 -> S + e, t |- (p1, p2) # c -> S + e, t |- (p3, p2) # c.

(* (forall r, {P r} c {Q r}) -> {exists r, P r} c {exists r, Q r} *)
Axiom h_ex : forall (p q: ref -> hprop) (c : cmd) (S : state)
                    (t : rtype) (e : pred_env),
    (forall r : ref, S + e, t |- (p r, q r) # c) -> S + e, t |- (=| p, =| q) # c.
(* (forall r, {P r} c {Q}) -> {exists r, P r} c {Q} *)
Axiom h_ex1 : forall (p : ref -> hprop) (q : hprop) (c : cmd) (S : state)
                     (t : rtype) (e : pred_env),
    (forall r : ref, S + e, t |- (p r, q) # c) -> S + e, t |- (=| p, q) # c.
(* {P} c {Q r} -> {P} c {exists r, Q r} *)
Axiom h_ex2 : forall (p : hprop) (q : ref -> hprop) (r : ref) (c : cmd)
                     (S : state) (t : rtype) (e : pred_env),
    S + e, t |- (p, q r) # c -> S + e, t |- (p, =| q) # c.
(* (forall l, {P l} c {Q}) -> {exists l, P l} c {Q} *)
Axiom h_ex3 : forall (p : list ref -> hprop) (q : hprop) (c : cmd) (S : state)
                     (t : rtype) (e : pred_env),
    (forall l, S + e, t |- (p l, q) # c) -> S + e, t |- (E| p, q) # c.
(* {P} c {Q l} -> {P} c {exists l, Q l} *)
Axiom h_ex4 : forall (p : hprop) (q : list ref -> hprop) (l : list ref)
                     (c : cmd) (S : state) (t : rtype) (e : pred_env),
    S + e, t |- (p, q l) # c -> S + e, t |- (p, E| q) # c.

(* {False} c {P} *)
Axiom h_contrad : forall (p : hprop) (c : cmd) (S : state) (t : rtype) (e : pred_env),
    S + e, t |- (HProp.hfalse, p) # c.
(* "R has no free variable" -> {P} {Q} refines {P * R} {Q * R} *)
Axiom refine_frame : forall p q r : hprop,
    HProp.fv r = Sset.empty -> (p * r, q * r) <<= (p, q).
(* (forall r, {P2} {Q2} refines {P1 r} {Q1 r}) ->
   {P2} {Q2} refines {exists r, P1 r} {exists r, Q1 r} *)
Axiom refine_exist : forall (p1 q1 : ref -> hprop) (p2 q2 : hprop) (r : ref),
    (forall r, (p1 r, q1 r) <<= (p2, q2)) -> (=|p1, =|q1) <<= (p2, q2).

Close Scope string_scope.
Close Scope hprop_scope.
Close Scope spec_scope.

End SPEC.


(*-----  Data  -----*)

(*  Specification  *)

Module Spec <: SPEC.

Definition name := Name.name.
Definition rtype := RType.rtype.
Definition ref := Ref.ref.
Definition expr := Expr.expr.
Definition bexpr := BExpr.bexpr.
Definition heap := Heap.heap.
Definition stack := Stack.stack.
Definition cmd := Lang.cmd.
Definition method := Method.method.
Definition hprop := HProp.hprop.
Definition state := State.state.
Definition conf := Sem.conf.

Open Scope string_scope.

Definition spec := (hprop * hprop)%type.
Definition program_spec := Smap.t (Smap.t spec).
Definition no_spec := Smap.empty spec.
Definition init_program_spec := Smap.empty (Smap.t spec).

Definition pred_env := Smap.t (Smap.t hprop).
Definition init_pred_env := Smap.empty (Smap.t hprop).
Definition no_pred := Smap.empty hprop.

Definition update_pred (n : name) (t : rtype) (p : hprop) (e : pred_env) :=
    match Smap.find n e with
    | Some o => Smap.add n (Smap.add t p o) e
    | None => Smap.add n (Smap.add t p no_pred) e
    end.

Definition get_pred (n : name) (t : rtype) (e : pred_env) : option hprop :=
    match Smap.find n e with
    | Some o => Smap.find t o
    | None => None
    end.

Definition pred_in (n : name) (t : rtype) (p : hprop) (e : pred_env) :=
    exists o, Smap.MapsTo n o e /\ Smap.MapsTo t p o.

Open Scope hprop_scope.

Fixpoint evalP (t : rtype) (e : pred_env) (hp : hprop) : hprop :=
    match hp with
    | ~` hp' => ~` (evalP t e hp')
    | hp1 /.\ hp2 => (evalP t e hp1) /.\ (evalP t e hp2)
    | hp1 \./ hp2 => (evalP t e hp1) \./ (evalP t e hp2)
    | hp1 --> hp2 => (evalP t e hp1) --> (evalP t e hp2)
    | hp1 * hp2 => (evalP t e hp1) * (evalP t e hp2)
    | hp1 *-> hp2 => (evalP t e hp1) *-> (evalP t e hp2)
    | =| hp' => =| (fun r => evalP t e (hp' r))
    | \-/ hp' => \-/ (fun r => evalP t e (hp' r))
    | .\ hp' => .\ (fun r => evalP t e (hp' r))
    | hp' & r => (evalP t e hp') & r
    | hp' &^ n => (evalP t e hp') &^ n
    | |P| n @ a => if Name.beq a "this" then
                       match get_pred n t e with
                       | Some hp' => hp' &^ "this"
                       | None => HProp.hfalse
                       end
                   else hp
    | ,\ hp' => ,\ (fun l => evalP t e (hp' l))
    | hp' &` l => (evalP t e hp') &` l
    | _ => hp
    end.

(* A command $c$ in class $t$ satisfies the specification $sp$ *)
Definition cmd_satisfy (S : state) (t : rtype) (c : cmd) (e : pred_env)
                       (sp : spec) : Prop :=
    forall (h : heap) (s : stack) (S' : state),
    let S0 := State.update_heap h (State.update_stack s S) in
    let h' := State.get_heap S' in
    let s' := State.get_stack S' in
    let se := State.get_super_env S in
    match sp with (hp1, hp2) =>
        Sem.sem S0 c S' -> HProp.eval hp1 h s se -> HProp.eval hp2 h' s' se
    end.

Notation "S + e , t |- sp # c" := (cmd_satisfy S t c e sp) (at level 30) : spec_scope.
Open Scope spec_scope.

Definition add_spec (t : rtype) (m : method) (s : spec) (ps : program_spec) : program_spec :=
    match Smap.find t ps with
    | None => Smap.add t (Smap.add m s no_spec) ps
    | Some cs => Smap.add t (Smap.add m s cs) ps
    end.

Definition get_spec (t : rtype) (m : method) (ps : program_spec) : option spec :=
    match Smap.find t ps with
    | None => None
    | Some cs => Smap.find m cs
    end.

(* s2 refines s1 *)
Definition refine (s1 s2 : spec) : Prop :=
    forall S t c e, S + e, t |- s2 # c -> S + e, t |- s1 # c.

Infix "<<=" := refine (at level 70) : spec_scope.

Fixpoint bs2 (t : rtype) (l : list rtype) (m : method) (ps : program_spec) : Prop :=
    match l with
    | nil => True
    | cons s l' =>
        match get_spec t m ps, get_spec s m ps with
        | Some sp, Some sp' => sp' <<= sp /\ bs2 t l' m ps
        | None, Some sp' => sp' <<= (HProp.htrue, HProp.htrue) /\ bs2 t l' m ps
        | _, None => bs2 t l' m ps
        end
    end.

(* behavioral subtyping *)
Definition bs (S : state) (t : rtype) (m : method) (ps : program_spec) : Prop :=
    match RType.get_super t (State.get_super_env S) with
    | None => True
    | Some l => bs2 t l m ps
    end.

Fixpoint add_args (args : list name) (hp : hprop) : hprop :=
    match args with
    | nil => hp
    | cons a b => add_args b (=| (fun r => a +-> r /.\ hp))
    end.

Definition mbody_satisfy S t e (mb : MEnv.method_body) (sp : spec) :=
  match mb with
  | (a, l, Some c) => 
    match sp with (hp1, hp2) =>
      S + e, t |- (add_args a hp1, hp2) # c
    end
  | _ => True
  end.

Definition raw2 (r : ref) (n : name) (t : rtype) (p : hprop) : hprop :=
  if RType.beq t "Bool"
    then p * (r`n |-> Ref.rfalse)
    else p * (r`n |-> Ref.rnull).

Definition raw (t : rtype) (fe : TEnv.fields_env) : hprop :=
  match TEnv.get_fields t fe with
  | None => HProp.emp
  | Some f => =| (fun r => "this" +-> r /.\ r =: t /.\
                  Smap.fold (raw2 r) f HProp.emp)
  end.

Definition constructor_satisfy S t e (mb : MEnv.method_body) (sp : spec) :=
  match mb with
  | (a, l, Some c) => 
    match sp with (hp1, hp2) =>
      S + e, t |- (add_args a (hp1 * (raw t (State.get_fields_env S))), hp2) # c
    end
  | _ => True
  end.

Definition method_satisfy (S : state) (t : rtype) (m : method) (e : pred_env)
                          (ps : program_spec) : Prop :=
  if RType.beq t m then
    match get_spec t t ps with
    | Some sp =>
        match MEnv.find_mbody (State.get_mbody_env S) t t with
        | None => False
        | Some mb => constructor_satisfy S t e mb sp
        end
    | None => True
    end
  else
    match get_spec t m ps with
    | Some sp =>
        match MEnv.find_mbody (State.get_mbody_env S) t m with
        | None => False
        | Some mb => mbody_satisfy S t e mb sp /\ bs S t m ps
        end
    | None => bs S t m ps
    end.

Notation "S + e |> ps # t , m" := (method_satisfy S t m e ps) (at level 30) : spec_scope.

Definition spec_in (t : rtype) (m : method) (s : spec) (ps : program_spec) :=
    exists o, Smap.MapsTo t o ps /\ Smap.MapsTo m s o.

Definition program_satisfy (S : state) (e : pred_env) (ps : program_spec) : Prop :=
    forall t m, MEnv.In t m (State.get_mbody_env S) -> S + e |> ps # t,m.

Notation "S + e |= ps" := (program_satisfy S e ps) (at level 30) : spec_scope.

Lemma pred_update_1 : forall n t p e, pred_in n t p (update_pred n t p e).
Proof.
  intros n t p e. unfold update_pred.
  case (Smap.find n e).
  intro o. unfold pred_in.
  exists (Smap.add t p o). split.
  apply Smap.add_1; reflexivity.
  apply Smap.add_1; reflexivity.
  unfold pred_in.
  exists (Smap.add t p no_pred).
  split.
  apply Smap.add_1; reflexivity.
  apply Smap.add_1; reflexivity.
Qed.

Lemma pred_update_2 : forall n1 n2 t1 t2 p1 p2 e,
    (t1 <> t2 \/ n1 <> n2) -> pred_in n1 t1 p1 e ->
        pred_in n1 t1 p1 (update_pred n2 t2 p2 e).
Proof.
  intros n1 n2 t1 t2 p1 p2 e H H0.
  unfold update_pred. unfold pred_in in H0.
  do 2 destruct H0. case (Name.eq_dec n1 n2).
  intro H2. destruct H.
  rewrite <- H2. apply Smap.find_1 in H0.
  rewrite H0. exists (Smap.add t2 p2 x).
  split. apply Smap.add_1. reflexivity.
  apply Smap.add_2. auto.
  assumption. elim H; assumption. intro H2.
  unfold pred_in. exists x.
  split. case (Smap.find n2 e).
  intro o. apply Smap.add_2. auto.
  assumption. apply Smap.add_2. auto.
  assumption. assumption.
Qed.

Lemma pred_update_3 : forall n1 n2 t1 t2 p1 p2 e,
    (t1 <> t2 \/ n1 <> n2) -> pred_in n1 t1 p1 (update_pred n2 t2 p2 e) ->
        pred_in n1 t1 p1 e.
Proof.
  intros n1 n2 t1 t2 p1 p2 e H H0.
  unfold update_pred in H0; unfold pred_in in H0.
  do 2 destruct H0. case (Name.eq_dec n1 n2).
  intro H2. destruct H. rewrite <- H2 in H0.
  inductS (Smap.find n1 e); rewrite H3 in H0.
  assert (x = Smap.add t2 p2 x0).
  apply smap_add in H0. assumption.
  exists x0. split.
  apply Smap.find_2 in H3. assumption.
  rewrite H4 in H1.
  apply Smap.add_3 in H1. assumption. auto.
  assert (x = Smap.add t2 p2 no_pred).
  assert (Smap.MapsTo n1 (Smap.add t2 p2 no_pred)
    (Smap.add n1 (Smap.add t2 p2 no_pred) e)).
  apply Smap.add_1. reflexivity.
  apply smap_inject with (k := n1)
    (m := (Smap.add n1 (Smap.add t2 p2 no_pred) e)).
  assumption. assumption.
  rewrite H4 in H1.
  apply Smap.add_3 in H1.
  apply Smap.empty_1 in H1. elim H1. auto.
  elim H; assumption. intro H2.
  inductS (Smap.find n2 e); rewrite H3 in H0;
  apply Smap.add_3 in H0; unfold pred_in;
  try (exists x; split; assumption); auto.
Qed.

Lemma pred_get : forall n t p e, pred_in n t p e <-> get_pred n t e = Some p.
Proof.
  intros n t p e. split. intro H.
  unfold pred_in in H.
  do 2 destruct H.
  unfold get_pred.
  apply Smap.find_1 in H.
  rewrite H.
  apply Smap.find_1 in H0.
  rewrite H0; reflexivity.
  intro H. unfold get_pred in H.
  unfold pred_in.
  inductS (Smap.find n e); rewrite H0 in H.
  apply Smap.find_2 in H.
  apply Smap.find_2 in H0.
  exists x; split; assumption.
  inversion H.
Qed.

Lemma pred_not_get : forall n t e,
    (forall p, ~ pred_in n t p e) <-> get_pred n t e = None.
Proof.
  intros n t e. split. intro H.
  unfold pred_in in H. unfold get_pred.
  inductS (Smap.find n e).
  apply Smap.find_2 in H0.
  assert (forall p, ~ Smap.MapsTo t p x).
  intros p H1. elim H with (p := p).
  exists x; split. assumption. assumption.
  inductS (Smap.find t x).
  apply Smap.find_2 in H2.
  elim H1 with (p := x0). assumption.
  reflexivity. reflexivity.
  intros H p H0. unfold get_pred in H.
  do 2 destruct H0.
  inductS (Smap.find n e); rewrite H2 in H.
  apply Smap.find_1 in H0. rewrite H2 in H0.
  inversion H0. rewrite <- H4 in H1.
  apply Smap.find_1 in H1. rewrite H1 in H.
  inversion H. apply Smap.find_1 in H0.
  rewrite H2 in H0. inversion H0.
Qed.

Axiom unf_pred : forall S t c e p1 p2,
    cmd_satisfy S t c e (p1, p2) <-> cmd_satisfy S t c e (evalP t e p1, evalP t e p2).

Lemma spec_add_1 : forall t m s ps, spec_in t m s (add_spec t m s ps).
Proof.
  intros t m s ps. unfold add_spec.
  case (Smap.find t ps).
  intro o. unfold spec_in.
  exists (Smap.add m s o). split.
  apply Smap.add_1; reflexivity.
  apply Smap.add_1; reflexivity.
  unfold spec_in.
  exists (Smap.add m s no_spec).
  split.
  apply Smap.add_1; reflexivity.
  apply Smap.add_1; reflexivity.
Qed.

Lemma spec_add_2 : forall t1 t2 m1 m2 s1 s2 ps,
    (t1 <> t2 \/ m1 <> m2) -> spec_in t1 m1 s1 ps ->
        spec_in t1 m1 s1 (add_spec t2 m2 s2 ps).
Proof.
  intros t1 t2 m1 m2 s1 s2 ps H H0.
  unfold add_spec. unfold spec_in in H0.
  do 2 destruct H0.
  case RType.eq_dec with (s1 := t1) (s2 := t2).
  intro H2.
  destruct H. elim H; assumption.
  rewrite <- H2. apply Smap.find_1 in H0.
  rewrite H0. exists (Smap.add m2 s2 x).
  split. apply Smap.add_1. reflexivity.
  apply Smap.add_2. auto.
  assumption. intro H2.
  unfold spec_in. exists x.
  split. case (Smap.find t2 ps).
  intro o. apply Smap.add_2. auto.
  assumption. apply Smap.add_2. auto.
  assumption. assumption.
Qed.

Lemma spec_add_3 : forall t1 t2 m1 m2 s1 s2 ps,
    (t1 <> t2 \/ m1 <> m2) -> spec_in t1 m1 s1 (add_spec t2 m2 s2 ps) ->
        spec_in t1 m1 s1 ps.
Proof.
  intros t1 t2 m1 m2 s1 s2 ps H H0.
  unfold add_spec in H0; unfold spec_in in H0.
  do 2 destruct H0.
  case RType.eq_dec with (s1 := t1) (s2 := t2).
  intro H2. destruct H. elim H; assumption.
  rewrite <- H2 in H0.
  inductS (Smap.find t1 ps); rewrite H3 in H0.
  assert (x = Smap.add m2 s2 x0).
  apply smap_add in H0. assumption.
  exists x0. split.
  apply Smap.find_2 in H3. assumption.
  rewrite H4 in H1.
  apply Smap.add_3 in H1. assumption. auto.
  assert (x = Smap.add m2 s2 no_spec).
  assert (Smap.MapsTo t1 (Smap.add m2 s2 no_spec)
    (Smap.add t1 (Smap.add m2 s2 no_spec) ps)).
  apply Smap.add_1. reflexivity.
  apply smap_inject with (k := t1)
    (m := (Smap.add t1 (Smap.add m2 s2 no_spec) ps)).
  assumption. assumption.
  rewrite H4 in H1.
  apply Smap.add_3 in H1.
  apply Smap.empty_1 in H1. elim H1. auto.
  intro H2. inductS (Smap.find t2 ps);
  rewrite H3 in H0; apply Smap.add_3 in H0;
  try (exists x; split; assumption); auto.
Qed.

Lemma spec_get : forall t m s ps, spec_in t m s ps <-> get_spec t m ps = Some s.
Proof.
  intros t m s ps. split. intro H.
  unfold spec_in in H.
  do 2 destruct H.
  unfold get_spec.
  apply Smap.find_1 in H.
  rewrite H.
  apply Smap.find_1 in H0.
  rewrite H0; reflexivity.
  intro H. unfold get_spec in H.
  unfold spec_in.
  inductS (Smap.find t ps); rewrite H0 in H.
  apply Smap.find_2 in H.
  apply Smap.find_2 in H0.
  exists x; split; assumption.
  inversion H.
Qed.

Lemma spec_not_get : forall t m ps,
    (forall s, ~ spec_in t m s ps) <-> get_spec t m ps = None.
Proof.
  intros t m ps. split. intro H.
  unfold spec_in in H. unfold get_spec.
  inductS (Smap.find t ps).
  apply Smap.find_2 in H0.
  assert (forall s, ~ Smap.MapsTo m s x).
  intros s H1. elim H with (s := s).
  exists x; split; assumption.
  inductS (Smap.find m x).
  apply Smap.find_2 in H2.
  elim H1 with (s := x0). assumption.
  reflexivity. reflexivity.
  intros H s H0. unfold get_spec in H.
  do 2 destruct H0.
  inductS (Smap.find t ps); rewrite H2 in H.
  apply Smap.find_1 in H0. rewrite H2 in H0.
  inversion H0. rewrite <- H4 in H1.
  apply Smap.find_1 in H1. rewrite H1 in H.
  inversion H. apply Smap.find_1 in H0.
  rewrite H2 in H0; inversion H0.
Qed.

Lemma spec_get_add_1 : forall t m s ps, get_spec t m (add_spec t m s ps) = Some s.
Proof.
  intros t m s ps. apply spec_get.
  apply spec_add_1.
Qed.

Lemma spec_get_add_2 : forall t1 t2 m1 m2 s ps, (t1 <> t2 \/ m1 <> m2) ->
    get_spec t1 m1 (add_spec t2 m2 s ps) = get_spec t1 m1 ps.
Proof.
  intros t1 t2 m1 m2 s ps H.
  inductS (get_spec t1 m1 ps).
  apply spec_get.
  apply spec_add_2. assumption.
  apply spec_get. assumption.
  apply spec_not_get.
  intros s0 H1. apply spec_add_3 in H1.
  apply spec_get in H1. rewrite H1 in H0.
  discriminate. assumption.
Qed.

Lemma spec_init : forall t m, get_spec t m init_program_spec = None.
Proof.
  intros t m. unfold get_spec.
  inductS (Smap.find t init_program_spec).
  apply Smap.find_2 in H.
  apply Smap.empty_1 in H. elim H.
  reflexivity.
Qed.

Lemma prog_satis_init : forall (S : state) (e : pred_env), S + e |= init_program_spec.
Proof.
  intros S e. unfold program_satisfy.
  unfold init_program_spec.
  intros t m H. unfold method_satisfy.
  assert (forall t m, get_spec t m (Smap.empty (Smap.t spec)) = None).
  intros t0 m0. apply spec_not_get. intros s H0.
  apply spec_get in H0. unfold get_spec in H0.
  inductS (Smap.find t0 (Smap.empty (Smap.t spec))).
  apply Smap.find_2 in H1.
  apply Smap.empty_1 in H1. elim H1.
  rewrite H1 in H0. discriminate.
  do 2 rewrite H0. unfold bs.
  case (RType.beq t m); [reflexivity|].
  induction (RType.get_super t (State.get_super_env S)).
  induction a. unfold bs2. reflexivity.
  unfold bs2. rewrite H0. rewrite H0. apply IHa.
  reflexivity.
Qed.

Open Scope heap_scope.
Open Scope lang_scope.
Open Scope state_scope.

Lemma refine_refl : forall sp : spec, sp <<= sp.
Proof.
  unfold refine. intros; assumption.
Qed.

Lemma refine_trans : forall sp1 sp2 sp3 : spec, sp1 <<= sp2 -> sp2 <<= sp3 -> sp1 <<= sp3.
Proof.
  unfold refine. intros.
  apply H. apply H0.
  assumption.
Qed.

Lemma refine_cons1 : forall p1 p2 p3 : hprop, p3 ==> p2 -> (p1, p2) <<= (p1, p3).
Proof.
  intros p1 p2 p3 H.
  unfold refine. unfold cmd_satisfy.
  intros. apply H. apply H0 with (h := h) (s := s);
  assumption.
Qed.

Lemma refine_cons2 : forall p1 p2 p3 : hprop, p1 ==> p3 -> (p1, p2) <<= (p3, p2).
Proof.
  intros p1 p2 p3 H.
  unfold refine. unfold cmd_satisfy.
  intros. apply H0 with (h := h) (s := s);
  [ | apply H]; assumption.
Qed.

Lemma refine_inh : forall t1 t2 S e m ps,
    S + e |> ps # t2,m ->
    match get_spec t1 m ps, get_spec t2 m ps with
    | Some (hp1, hp2), Some (hp3, hp4) =>
        match MEnv.find_mbody (State.get_mbody_env S) t1 m,
              MEnv.find_mbody (State.get_mbody_env S) t2 m with
        | Some mb1, Some mb2 =>
            (hp1, hp2) = (hp3, hp4) /\ mb1 = mb2 /\
            (add_args (MEnv.get_args mb1) (evalP t1 e hp1), evalP t1 e hp2)
        <<= (add_args (MEnv.get_args mb2) (evalP t2 e hp3), evalP t2 e hp4)
                       
        | _, _ => False
        end
    | _, _ => False
    end -> S + e |> ps # t1,m.
Proof.
  intros. inductS (get_spec t1 m ps); rewrite H1 in H0.
  induction x.
(* induction a.
  induction (get_spec t2 m ps) in H0. induction a0.
  induction (MEnv.find_mbody (State.get_mbody_env S) t1 m) in H0.
  induction (MEnv.find_mbody (State.get_mbody_env S) t2 m) in H0.
  do 2 destruct H0.
  apply H0. assumption.*)
Admitted.

Lemma h_skip : forall (p : hprop) (S : state) (t : rtype) (e : pred_env),
    S + e, t |- (p, p) # Lang.skip.
Proof.
  intros p S t e. unfold cmd_satisfy.
  intros h s S' H0 H1. inversion H0.
  rewrite State.get_after_update_00.
  rewrite State.update_comm_01.
  rewrite State.get_after_update_11.
  assumption.
Qed.

Lemma h_asn : forall (p1 p2 : hprop) (n : name) (e : expr) (S : state)
                     (t : rtype) (pe : pred_env),
    p1 ==> HProp.subst_name_1 n e p2 ->
    S + pe,t |- (p1, p2) # Lang.assign n e.
Proof.
  intros p1 p2 n e S t pe H.
  apply refine_cons2 with (p2 := p2) in H.
  apply H. unfold cmd_satisfy.
  intros h s S' H0 H1. inversion H0.
  rewrite State.update_comm_01.
  rewrite State.get_after_update_11.
  rewrite State.get_after_map_01.
  rewrite <- State.update_comm_01.
  rewrite State.get_after_update_00.
  rewrite State.get_after_map_11.
  rewrite State.update_comm_01.
  rewrite State.get_after_update_11.
  rewrite HProp.lemma3_23 in H1.
  assumption.
Qed.

Lemma h_asnb : forall (p1 p2 : hprop) (n : name) (b : bexpr) (S : state)
                      (t : rtype) (e : pred_env),
               p1 ==> HProp.subst_name_2 n b p2 -> 
               S + e, t |- (p1, p2) # Lang.assignb n b.
Proof.
  intros p1 p2 n b S t e H.
  apply refine_cons2 with (p2 := p2) in H.
  apply H. unfold cmd_satisfy.
  intros h s S' H0 H1. inversion H0.
  rewrite State.update_comm_01.
  rewrite State.get_after_update_11.
  rewrite State.get_after_map_01.
  rewrite <- State.update_comm_01.
  rewrite State.get_after_update_00.
  rewrite State.get_after_map_11.
  rewrite State.update_comm_01.
  rewrite State.get_after_update_11.
  rewrite HProp.lemma3_23' in H1.
  assumption.
Qed.

Lemma h_mut : forall (v a : name) (e : expr) (S : state) (r1 r2 r3: ref)
                     (t : rtype) (pe : pred_env),
    S + pe, t |- (v +-> r1 /.\ r1`a |-> r3 /.\ e |=> r2,
                 v +-> r1 /.\ r1`a |-> r2 /.\ e |=> r2) # Lang.fwrite v a e.
Proof.
  intros v a e S r1 r2 r3 t pe.
  unfold cmd_satisfy. intros h s S' H H0.
  inversion H.
  rewrite State.get_after_map_00.
  rewrite State.get_after_update_10.
  rewrite State.get_after_update_11.
  rewrite State.get_after_update_00.
  rewrite State.get_after_map_10.
  rewrite State.get_after_update_10.
  rewrite State.get_after_update_11.
  unfold HProp.eval in H0. destruct H0. destruct H8.
  unfold HProp.eval; split. assumption.
  split. apply Heap.equal_3 in H8; rewrite H8.
  rewrite State.get_after_update_10 in H6.
  rewrite State.get_after_update_11 in H6.
  rewrite H0 in H6. inversion H6.
  rewrite <- Heap.update_update.
  induction e; unfold Expr.eval; rewrite H9; apply Heap.eq_refl.
  assumption.
Qed.

Lemma h_lkp : forall (x v a: name) (S : state) (r1 r2: ref) (t : rtype) (e : pred_env),
    x <> v ->
    S + e, t |- (v +-> r1 /.\ r1`a |-> r2,
                 v +-> r1 /.\ r1`a |-> r2 /.\ x +-> r2) # Lang.fread x v a.
Proof.
  intros x v a S r1 r2 t e H.
  unfold cmd_satisfy. simpl.
  intros. destruct H1. inversion H0.
  rewrite State.get_after_map_11.
  rewrite State.get_after_update_10.
  rewrite State.get_after_update_11.
  rewrite State.get_after_map_01.
  rewrite State.get_after_update_00.
  split. apply Stack.in_get. apply Stack.in_update_2.
  auto. apply Stack.in_get in H1; assumption.
  split. assumption.
  rewrite State.get_after_update_10 in H8.
  rewrite State.get_after_update_11 in H8.
  rewrite H1 in H8. inversion H8.
  rewrite State.get_after_update_00 in H9.
  apply Heap.equal_3 in H2; rewrite H2 in H9.
  rewrite H11 in H9. apply Heap.in_get in H9. assert (r' = r2).
  apply Heap.in_equal with (r := r) (n := a) (h := Heap.update r a r2 {}).
  assumption. apply Heap.in_update_1.
  rewrite H10. apply Stack.in_get.
  apply Stack.in_update_1.
Qed.

Lemma h_lkp' : forall (x a: name) (S : state) (r1 r2: ref) (t : rtype) (e : pred_env),
    S + e, t |- (x +-> r1 /.\ r1`a |-> r2,
                 x +-> r2 /.\ r1`a |-> r2) # Lang.fread x x a.
Proof.
  intros x a S r1 r2 t e.
  unfold cmd_satisfy. simpl.
  intros h s S' H [H0 H1]. inversion H.
  rewrite State.get_after_map_11.
  rewrite State.get_after_update_10.
  rewrite State.get_after_update_11.
  rewrite State.get_after_map_01.
  rewrite State.get_after_update_00.
  split. apply Stack.in_get.
  rewrite State.get_after_update_00 in H8.
  apply Heap.equal_3 in H1; rewrite H1 in H8.
  rewrite State.get_after_update_10 in H7.
  rewrite State.get_after_update_11 in H7.
  rewrite H7 in H0; inversion H0. rewrite H10 in H8.
  assert (r' = r2). apply Heap.in_equal with (r := r1) (n := a)
    (h := Heap.update r1 a r2 {}). apply Heap.in_get in H8.
  assumption. apply Heap.in_update_1.
  rewrite H9. apply Stack.in_update_1.
  assumption.
Qed.

Lemma h_cast : forall (x v: name) (C : rtype) (S : state) (r: ref)
                      (t : rtype) (e : pred_env),
    S + e, t |- (v +-> r /.\ r <: C, x +-> r) # Lang.cast x C v.
Proof.
  intros x v C S r t e.
  unfold cmd_satisfy. simpl.
  intros h s S' H [H0 H1].
  inversion H.
  rewrite State.get_after_map_11.
  rewrite State.get_after_update_10.
  rewrite State.get_after_update_11.
  rewrite State.get_after_update_10 in H7.
  rewrite State.get_after_update_11 in H7.
  rewrite H7 in H0; inversion H0.
  apply Stack.in_get; apply Stack.in_update_1.
Qed.

Lemma h_res : forall (p1 p2 : hprop) (e : expr) (S : state) (t : rtype) (pe : pred_env),
    p1 ==> HProp.subst_name_1 "res" e p2 ->
    S + pe, t |- (p1, p2) # (Lang.creturn e).
Proof.
  intros p1 p2 e S t pe H.
  apply refine_cons2 with (p2 := p2) in H.
  apply H. unfold cmd_satisfy.
  intros h s S' H0 H1. inversion H0.
  rewrite State.update_comm_01.
  rewrite State.get_after_update_11.
  rewrite State.get_after_map_01.
  rewrite <- State.update_comm_01.
  rewrite State.get_after_update_00.
  rewrite State.get_after_map_11.
  rewrite State.update_comm_01.
  rewrite State.get_after_update_11.
  rewrite HProp.lemma3_23 in H1.
  assumption.
Qed.

Lemma h_seq : forall (p q r: hprop) (c1 c2 : cmd) (S : state)
                     (t : rtype) (e : pred_env),
    S + e, t |- (p, q) # c1 -> S + e, t |- (q, r) # c2 ->
    S + e, t |- (p, r) # (c1; c2).
Proof.
  unfold cmd_satisfy; intros. inversion H1.
  apply H0 with (h := State.get_heap s2) (s := State.get_stack s2).
  apply Sem.sem_seq in H6.
  apply State.seq_update_heap in H6.
  apply State.seq_update_stack in H6.
  apply State.seq_subst in H6.
  rewrite H6. assumption.
  apply H with (h := h) (s := s); assumption.
Qed.

(* For method invocation *)
Fixpoint subst_args1 (p : hprop) (x v : name) (arg : list name) (le : list expr) : hprop :=
    match arg, le with
    | nil, nil => HProp.subst_name_3 "res" x (HProp.subst_name_3 "this" v p)
    | cons a0 a, cons e0 e => subst_args1 (HProp.subst_name_1 a0 e0 p) x v a e
    | _, _ => p (* Error: argument number mismatch *)
    end.

(* For creating new objects *)
Fixpoint subst_args2 (p : hprop) (arg : list name) (le : list expr) : hprop :=
    match arg, le with
    | nil, nil => p
    | cons a0 a, cons e0 e => subst_args2 (HProp.subst_name_1 a0 e0 p) a e
    | _, _ => p (* Error: argument number mismatch *)
    end.

(* spec of "x := v.m(le)" *)
Axiom h_dinv : forall S e v t t' m p1 p2 mb ps x le,
    get_spec t m ps = Some (p1, p2) ->
    MEnv.find_mbody (State.get_mbody_env S) t m = Some mb ->
    DType.get_dtype v (State.get_dtype S) = Some t ->
    S + e, t' |- (subst_args1 p1 x v (MEnv.get_args mb) le,
                  subst_args1 p2 x v (MEnv.get_args mb) le) # Lang.dcall x v m le.

(* spec of "x := v.t::m(le)" *)
Axiom h_sinv : forall S e v t t' m p1 p2 mb ps x le,
    get_spec t m ps = Some (p1, p2) ->
    MEnv.find_mbody (State.get_mbody_env S) t m = Some mb ->
    S + e, t' |- (subst_args1 p1 x v (MEnv.get_args mb) le,
                  subst_args1 p2 x v (MEnv.get_args mb) le) # Lang.scall x v t m le.

(* spec of "x := new t(le)" *)
Axiom h_new : forall S e p1 p2 mb ps x t t' le,
    get_spec t t ps = Some (p1, p2) ->
    MEnv.find_mbody (State.get_mbody_env S) t t = Some mb ->
    S + e, t' |- (subst_args2 p1 (MEnv.get_args mb) le,
                  HProp.subst_name_3 "this" x
                    (subst_args2 p2 (MEnv.get_args mb) le)) # Lang.calloc x t le.

Lemma list_eq_ext : forall S e t c (l1 l2 : list ref) (hp1 hp2 : hprop),
    (l1 = l2 -> S + e, t |- (hp1, hp2) # c) ->
     S + e, t |- (hp1 /.\ HProp.list_eq l1 l2, hp2) # c.
Proof.
  intros S e t c l1 l2 hp1 hp2 H.
  unfold cmd_satisfy; simpl.
  intros h s se H0 [H1 H2].
  apply HProp.list_equal_1 in H2.
  apply H in H2; unfold cmd_satisfy in H2;
  apply (H2 h s); assumption.
Qed.

(* "the variables $c$ modifies" is disjoint with "the free variables in $r$"
   -> {p} c {q} -> {p * r} c {q * r} *)
Axiom h_frame : forall (p q r: hprop) (c : cmd) (S : state) (t : rtype) (e : pred_env),
    sset_dsj (Lang.md c) (HProp.fv r) ->
    S + e, t |- (p, q) # c -> S + e, t |- (p * r, q * r) # c.
(*Proof.
  unfold cmd_satisfy. induction c.
  unfold HProp.eval; fold HProp.eval.
  intros S t pe H H0 h s S' H1 H2.
  unfold evalP; fold evalP.
  do 3 destruct H2. destruct H3. destruct H4.
  unfold Sem.sem in H1. unfold Sem.peq in H1. apply State.equal_3 in H1.
  (*assert (exists h3, h3 |*| x0 /\ State.get_heap S' |=| h3 |+| x0).
  apply Heap.exist_pdisjoint. rewrite <- H1.
  rewrite State.get_after_map_01.
  rewrite State.get_after_update_00.
  rewrite H3. apply Heap.subheap_union.*)
  exists x. exists x0. assert (State.get_heap S' = x |+| x0).
  rewrite <- H1.
  rewrite State.get_after_map_01.
  rewrite State.get_after_update_00.
  assumption. split. assumption.
  split. assumption. split.
  rewrite <- State.get_after_update_00 with (s := S') (h := x).
  rewrite <- State.get_after_update_10 with (s := S') (h := x).
  apply H0 with (h := x)(s := s).
  unfold Sem.sem; unfold Sem.peq; apply State.equal_3.
  induction S'. do 8 induction a. inversion H1.
  apply State.equal_3. induction S. do 8 induction a0.
  unfold State.peq. split. apply Heap.eq_refl.
  split. rewrite State.get_after_update_10.
  rewrite State.get_after_update_11.
  rewrite State.get_after_update_10.
  rewrite State.get_after_update_11.
  apply Stack.eq_refl.
  split. apply Ref.alloc_eq_refl.
  split. apply DType.eq_refl.
  split. apply TEnv.fields_eq_refl.
  split. apply TEnv.super_eq_refl.
  split. apply TEnv.cnames_eq_refl.
  split. apply TEnv.methods_eq_refl.
  split. apply TEnv.locvars_eq_refl.
  apply MEnv.eq_refl. assumption.
  rewrite <- H1.
  rewrite State.get_after_map_11.
  rewrite State.get_after_update_10.
  rewrite State.get_after_update_11.
Admitted.*)

(* "the variables $c$ modifies" is disjoint with "the free variables in $r$"
   -> "$r$ is an assertion independent of the heap"
   -> {p} c {q} -> {p /\ r} c {q /\ r} *)
Axiom h_frame' : forall (p q r: hprop) (c : cmd) (S : state)
                        (t : rtype) (e : pred_env),
    sset_dsj (Lang.md c) (HProp.fv r) -> HProp.stack_hprop r ->
        S + e, t |- (p, q) # c -> S + e, t |- (p /.\ r, q /.\ r) # c.

Lemma h_div1 : forall (p q r: hprop) (c : cmd) (S : state)
                     (t : rtype) (e : pred_env),
    S + e, t |- (p, q /.\ r) # c <->
    S + e, t |- (p, q) # c /\ S + e, t |- (p, r) # c.
Proof.
  intros p q r c S t e.
  split. intro H. split;
  generalize H; apply refine_cons1;
  [|rewrite HProp.conj_comm]; apply HProp.conj_impl.
  unfold cmd_satisfy; intros [H H0]; simpl.
  intros; split; [apply (H h s)|apply (H0 h s)]; assumption.
Qed.

Lemma h_div2 : forall (p q r: hprop) (c : cmd) (S : state)
                     (t : rtype) (e : pred_env),
    S + e, t |- (p \./ r, q) # c <->
    S + e, t |- (p, q) # c /\ S + e, t |- (r, q) # c.
Proof.
  intros p q r c S t e.
  split. intro H. split;
  generalize H; apply refine_cons2;
  [|rewrite HProp.disj_comm]; apply HProp.disj_impl.
  unfold cmd_satisfy; intros [H H0]; simpl.
  intros h s S' H1 [H2|H3];
  [apply (H h s)|apply (H0 h s)]; assumption.
Qed.

Lemma h_cond : forall (p q : hprop) (b : BExpr.bexpr) (c1 c2 : cmd) (S : state)
                      (t : rtype) (e : pred_env),
              S + e, t |- (p /.\ 'b, q) # c1
           -> S + e, t |- (p /.\ ~` 'b, q) # c2
           -> S + e, t |- (p, q) # Lang.cif b c1 c2.
Proof.
  unfold cmd_satisfy. simpl. intros.
  inversion H1; [apply H in H9 | apply H0 in H9];
  try split; try rewrite State.get_after_update_10 in H8;
  try rewrite State.get_after_update_11 in H8;
  try assumption. rewrite H8; discriminate.
Qed.

Lemma h_cond1 : forall (p q : hprop) (b : BExpr.bexpr) (c1 c2 : cmd) (S : state)
                      (t : rtype) (e : pred_env),
    p ==> 'b -> S + e, t |- (p, q) # c1
    -> S + e, t |- (p, q) # Lang.cif b c1 c2.
Proof.
  unfold cmd_satisfy; intros.
  inversion H1. apply H0 in H9; assumption.
  apply H in H2. unfold HProp.eval in H2.
  rewrite State.get_after_update_10 in H8.
  rewrite State.get_after_update_11 in H8.
  rewrite H2 in H8; discriminate.
Qed.

Lemma h_cond2 : forall (p q : hprop) (b : BExpr.bexpr) (c1 c2 : cmd) (S : state)
                      (t : rtype) (e : pred_env),
    p ==> ~` 'b -> S + e, t |- (p, q) # c2
    -> S + e, t |- (p, q) # Lang.cif b c1 c2.
Proof.
  unfold cmd_satisfy; intros.
  inversion H1. apply H in H2. unfold HProp.eval in H2.
  rewrite State.get_after_update_10 in H8.
  rewrite State.get_after_update_11 in H8.
  elim H2; assumption.
  apply H0 with (S' := S') in H2; assumption.
Qed.

Lemma h_iter : forall (p : hprop) (b : BExpr.bexpr) (c : cmd) (S : state)
                      (t : rtype) (e : pred_env),
    S + e, t |- (p /.\ 'b, p) # c ->
    S + e, t |- (p, p /.\ ~` 'b) # (Lang.cwhile b c).
Proof.
  unfold cmd_satisfy. simpl. intros p b c S t e H h s S'.
  cut (forall c0, Sem.sem (State.update_heap h (State.update_stack s S)) c0 S' ->
    c0 = Lang.cwhile b c -> HProp.eval p h s (State.get_super_env S) ->
  HProp.eval p (State.get_heap S') (State.get_stack S') (State.get_super_env S) /\
  BExpr.eval b (State.get_stack S') <> true); eauto.
  assert (exists S0, S0 = State.update_heap h (State.update_stack s S)).
  exists (State.update_heap h (State.update_stack s S)); reflexivity.
  destruct H0. rewrite <- H0.
  assert (h = State.get_heap x).
  rewrite H0; rewrite State.get_after_update_00; reflexivity.
  assert (s = State.get_stack x).
  rewrite H0; rewrite State.get_after_update_10;
  rewrite State.get_after_update_11; reflexivity.
  assert (State.get_super_env S = State.get_super_env x).
  rewrite H0; rewrite State.get_after_update_50;
  rewrite State.get_after_update_51; reflexivity.
  rewrite H1; rewrite H2; rewrite H3.
  intros c0 Hsem; elim Hsem; try (intros; discriminate).
  intros. inversion H9.
  assert (State.get_super_env s1 = State.get_super_env s2).
  apply Sem.sem_seq in H5. apply State.seq_subst in H5.
  induction s1; do 8 induction a;
  induction s2; do 8 induction a0; repeat destruct H5 as [?HQ H5];
  unfold State.get_super_env; reflexivity. rewrite H11.
  apply H8; try assumption.
  
  Focus 2. intros; split; try assumption.
  inversion H5. rewrite <- H8; rewrite H4; discriminate.
Admitted.

Lemma h_cons_1 : forall (p1 p2 p3 : hprop) (c : cmd) (S : state)
                        (t : rtype) (e : pred_env),
    p2 ==> p3 -> S + e, t |- (p1, p2) # c -> S + e, t |- (p1, p3) # c.
Proof.
  intros p1 p2 p3 c S t e H.
  apply refine_cons1; assumption.
Qed.

Lemma h_cons_2 : forall (p1 p2 p3 : hprop) (c : cmd) (S : state)
                        (t : rtype) (e : pred_env),
    p3 ==> p1 -> S + e, t |- (p1, p2) # c -> S + e, t |- (p3, p2) # c.
Proof.
  intros p1 p2 p3 c S t e H.
  apply refine_cons2; assumption.
Qed.

Lemma h_ex : forall (p q: ref -> hprop) (c : cmd) (S : state)
                    (t : rtype) (e : pred_env),
    (forall r : ref, S + e, t |- (p r, q r) # c) -> S + e, t |- (=| p, =| q) # c.
Proof.
  unfold cmd_satisfy. simpl.
  intros. destruct H1.
  exists x. apply H with (h := h) (s := s); assumption.
Qed.

Lemma h_ex1 : forall (p : ref -> hprop) (q : hprop) (c : cmd) (S : state)
                     (t : rtype) (e : pred_env),
    (forall r : ref, S + e, t |- (p r, q) # c) -> S + e, t |- (=| p, q) # c.
Proof.
  unfold cmd_satisfy. simpl.
  intros. destruct H1.
  apply H with (r := x) (h := h) (s := s); assumption.
Qed.

Lemma h_ex2 : forall (p : hprop) (q : ref -> hprop) (r : ref) (c : cmd)
                     (S : state) (t : rtype) (e : pred_env),
    S + e, t |- (p, q r) # c -> S + e, t |- (p, =| q) # c.
Proof.
  intros p q r c S t e. apply h_cons_1.
  apply HProp.impl_exist.
Qed.

Lemma h_ex3 : forall (p : list ref -> hprop) (q : hprop) (c : cmd) (S : state)
                     (t : rtype) (e : pred_env),
    (forall l, S + e, t |- (p l, q) # c) -> S + e, t |- (E| p, q) # c.
Proof.
  unfold cmd_satisfy. simpl.
  intros. destruct H1.
  apply H with (l := x) (h := h) (s := s); assumption.
Qed.

Lemma h_ex4 : forall (p : hprop) (q : list ref -> hprop) (l : list ref)
                     (c : cmd) (S : state) (t : rtype) (e : pred_env),
    S + e, t |- (p, q l) # c -> S + e, t |- (p, E| q) # c.
Proof.
  intros p q l c S t e. apply h_cons_1.
  unfold HProp.eimpl; simpl; intros.
  exists l; assumption.
Qed.

Lemma h_contrad : forall (p : hprop) (c : cmd) (S : state) (t : rtype) (e : pred_env),
    S + e, t |- (HProp.hfalse, p) # c.
Proof.
  unfold cmd_satisfy; intros.
  unfold HProp.eval in H0; elim H0.
Qed.

Lemma refine_frame : forall p q r : hprop,
    HProp.fv r = Sset.empty -> (p * r, q * r) <<= (p, q).
Proof.
  intros p q r H; unfold refine.
  intros S t c e. apply h_frame.
  rewrite H; apply sset_dsj_empty.
Qed.

Lemma refine_exist : forall (p1 q1 : ref -> hprop) (p2 q2 : hprop) (r : ref),
    (forall r, (p1 r, q1 r) <<= (p2, q2)) -> (=|p1, =|q1) <<= (p2, q2).
Proof.
  unfold refine; unfold cmd_satisfy.
  simpl; intros. destruct H2. exists x.
  apply H with (c := c) (h := h) (s := s); try assumption.
Qed.

Close Scope state_scope.
Close Scope lang_scope.
Close Scope heap_scope.
Close Scope hprop_scope.
Close Scope spec_scope.
Close Scope string_scope.

End Spec.

Bind Scope spec_scope with Spec.spec.
Delimit Scope spec_scope with spec.

Notation "S + e , t |- sp # c" := (Spec.cmd_satisfy S t c e sp) (at level 30) : spec_scope.
Notation "S + e |> ps # t , m" := (Spec.method_satisfy S t m e ps) (at level 30) : spec_scope.
Notation "S + e |= ps" := (Spec.program_satisfy S e ps) (at level 30) : spec_scope.
Infix "<<=" := Spec.refine (at level 70) : spec_scope.

Ltac trivBS  := repeat (reflexivity || (split; [apply Spec.refine_refl|]) ||
                        (split; [|trivBS; fail])).
Ltac bs      := unfold Spec.bs; simpl; trivBS.
Ltac exc     := repeat (rewrite HProp.exist_conj || rewrite HProp.exist_conj'
                || rewrite HProp.existl_conj || rewrite HProp.existl_conj'
                || rewrite HProp.exist_sep_conj || rewrite HProp.exist_sep_conj').
Ltac exconj  := exc; try (apply Spec.h_ex; intro).
Ltac exconj1 := exc; try (apply Spec.h_ex1; intro).
Ltac exconj2 v := exc; apply Spec.h_ex2 with (r := v).
Ltac exconj3 := exc; try (apply Spec.h_ex3; intro).
Ltac exconj4 v := exc; apply Spec.h_ex4 with (l := v).
Ltac eximpl1 := exc; try (apply HProp.forall_exist_impl; intro).
Ltac eximpl2 v := exc; apply HProp.exist_exist_impl; exists v.
Ltac eximpl3 := exc; try (apply HProp.forall_exist_impl2; intro).
Ltac eximpl4 v := exc; apply HProp.exist_exist_impl2; exists v.
Ltac impConj := repeat (apply HProp.impl_conj1 || apply HProp.impl_conj2 ||
                        apply HProp.impl_sep_conj1 || apply HProp.impl_sep_conj2);
                try (apply HProp.conj_impl || apply HProp.eimpl_refl ||
                     rewrite HProp.conj_comm; apply HProp.conj_impl).
Ltac param   := (rewrite HProp.param_arg || rewrite HProp.param_arg2 ||
                 rewrite HProp.param_arg3).
Ltac param2  := repeat param;
                repeat (rewrite HProp.param_ext || rewrite HProp.param_ext2);
                repeat param; exconj.
Ltac Simpl   := unfold Spec.method_satisfy; simpl;
                try rewrite Spec.unf_pred; param2;
                repeat rewrite HProp.sep_conj_emp2; simpl; try split.
Ltac unfEval := unfold HProp.eval; fold HProp.eval;
                unfold BExpr.eval; unfold Expr.beeq.
Ltac mbody   := try (rewrite State.find_mbody_comm1 ||
                     rewrite State.find_mbody_comm2);
                try (discriminate || left; discriminate || right; discriminate).
Ltac commC   := rewrite HProp.conj_comm.
Ltac commC1 x := rewrite HProp.conj_comm with (hp1 := x).
Ltac commC2 x := rewrite HProp.conj_comm with (hp2 := x).
Ltac assoC   := rewrite HProp.conj_asso.
Ltac assoC'  := rewrite <- HProp.conj_asso.
Ltac commSC  := rewrite HProp.sep_conj_comm.
Ltac commSC1 x := rewrite HProp.sep_conj_comm with (hp1 := x).
Ltac commSC2 x := rewrite HProp.sep_conj_comm with (hp2 := x).
Ltac assoSC  := rewrite HProp.sep_conj_asso.
Ltac assoSC' := rewrite <- HProp.sep_conj_asso.
Ltac sprop   := repeat (apply HProp.stack_hprop_conj; split);
                try apply HProp.stack_hprop_neg;
                try (apply HProp.stack_hprop_1 || apply HProp.stack_hprop_2 ||
                     apply HProp.stack_hprop_3 || apply HProp.stack_hprop_4 ||
                     apply HProp.stack_hprop_5 || apply HProp.stack_hprop_6 ||
                     apply HProp.stack_hprop_7).
Ltac sepconj := repeat try (rewrite HProp.stack_sep_conj1 ||
                            rewrite HProp.stack_sep_conj2 ||
                            rewrite HProp.stack_sep_conj3); sprop.
Ltac sepsep  := repeat rewrite <- HProp.stack_sep_conj1; sprop.
Ltac freevar := try (unfold HProp.fv; apply sset_dsj_empty ||
                     apply sset_dsj_sym; apply sset_dsj_empty).
Ltac frame   := sepconj; apply Spec.h_frame; freevar.
Ltac frame'  := apply Spec.h_frame'; try apply sset_dsj_card; eauto; sprop.
Ltac lkp     := apply Spec.h_lkp; discriminate.
Ltac mut x   := rewrite <- HProp.var_exp with (n := x); apply Spec.h_mut.
Ltac mlist   := let t := fresh "t" in
                let m := fresh "m" in
                let H := fresh "H" in
                intros t m H;
                repeat (rewrite <- State.in_mbody_env_1 in H ||
                        rewrite State.in_mbody_env_2 in H ||
                        rewrite State.in_mbody_env_3 in H ||
                        rewrite State.in_mbody_env_4 in H ||
                        rewrite State.in_mbody_env_init in H);
                unfold List.hd in H; propSimp H.
Ltac mtdSpec L :=
    let H := fresh "H" in
    let H0 := fresh "H" in
    match goal with
    | [id : _ /\ _ \/ _ |- _] => destruct id; [destruct id as [H H0];
                                   rewrite H; rewrite H0; apply L|]
    | [id : _ /\ _ |- _] => destruct id as [H H0]; rewrite H;
                              rewrite H0; apply L
    end.
