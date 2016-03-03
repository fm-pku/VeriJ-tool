Require Export Lang.
Require Import List.
Require Import Bool.

(*-----  Abstract Data Type  -----*)

(*  Type Environment Type  *)

Module Type TENV.

Parameter name : Type.
Parameter method : Type.
Parameter rtype : Type.

Parameter cnames : Type.
Parameter init_cnames : cnames.

Parameter super_env : Type.
Parameter init_super_env : super_env.

Parameter method_type : Type.
Parameter class_methods : Type.
Parameter methods_env : Type.
Parameter init_methods_env : methods_env.

Parameter field_type : Type.
Parameter fields_env : Type.
Parameter init_fields_env : fields_env.

Parameter method_locvars : Type.
Parameter method_no_locvar : method_locvars.
Parameter class_locvars : Type.
Parameter locvars_env : Type.
Parameter init_locvars_env : locvars_env.

Parameter cnames_beq : cnames -> cnames -> bool.
Parameter cnames_peq : cnames -> cnames -> Prop.
Parameter super_beq : super_env -> super_env -> bool.
Parameter super_peq : super_env -> super_env -> Prop.
Parameter methods_beq : methods_env -> methods_env -> bool.
Parameter methods_peq : methods_env -> methods_env -> Prop.
Parameter locvars_beq : locvars_env -> locvars_env -> bool.
Parameter locvars_peq : locvars_env -> locvars_env -> Prop.
Parameter fields_beq : fields_env -> fields_env -> bool.
Parameter fields_peq : fields_env -> fields_env -> Prop.

Parameter cnames_add : rtype -> cnames -> cnames.
Parameter cnames_find : rtype -> cnames -> bool.
Parameter update_super : rtype -> list rtype -> super_env -> super_env.
Parameter subtype : rtype -> rtype -> super_env -> Prop.
Parameter update_fields : rtype -> field_type -> fields_env -> fields_env.
Parameter get_fields : rtype -> fields_env -> option field_type.
Parameter map_fields : rtype -> (field_type -> field_type) -> fields_env -> fields_env.
Parameter update_class_methods : rtype -> class_methods -> methods_env -> methods_env.
Parameter find_class_methods : rtype -> methods_env -> option class_methods.
Parameter update_method : rtype -> method -> method_type -> methods_env -> methods_env.
Parameter find_method : methods_env -> rtype -> method -> option method_type.
Parameter update_method_locvars : name -> rtype -> method_locvars -> method_locvars.
Parameter update_class_locvars : method -> method_locvars -> class_locvars -> class_locvars.
Parameter update_locvars_env : rtype -> class_locvars -> locvars_env -> locvars_env.
Parameter update_a_locvar : rtype -> method -> method_locvars -> locvars_env -> locvars_env.
Parameter find_locvars : method_locvars -> name -> option rtype.
Parameter find_locvars_2 : class_locvars -> method -> name -> option rtype.
Parameter find_locvars_3 : locvars_env -> rtype -> method -> name -> option rtype.

Axiom cnames_eq_refl : forall x : cnames, cnames_peq x x.
Axiom cnames_eq_sym : forall x y : cnames, cnames_peq x y -> cnames_peq y x.
Axiom cnames_eq_trans : forall x y z : cnames,
    cnames_peq x y -> cnames_peq y z -> cnames_peq x z.
Axiom super_eq_refl : forall x : super_env, super_peq x x.
Axiom super_eq_sym : forall x y : super_env, super_peq x y -> super_peq y x.
Axiom super_eq_trans : forall x y z : super_env,
    super_peq x y -> super_peq y z -> super_peq x z.
Axiom methods_eq_refl : forall x : methods_env, methods_peq x x.
Axiom methods_eq_sym : forall x y : methods_env, methods_peq x y -> methods_peq y x.
Axiom methods_eq_trans : forall x y z : methods_env,
    methods_peq x y -> methods_peq y z -> methods_peq x z.
Axiom locvars_eq_refl : forall x : locvars_env, locvars_peq x x.
Axiom locvars_eq_sym : forall x y : locvars_env, locvars_peq x y -> locvars_peq y x.
Axiom locvars_eq_trans : forall x y z : locvars_env,
    locvars_peq x y -> locvars_peq y z -> locvars_peq x z.
Axiom fields_eq_refl : forall x : fields_env, fields_peq x x.
Axiom fields_eq_sym : forall x y : fields_env, fields_peq x y -> fields_peq y x.
Axiom fields_eq_trans : forall x y z : fields_env,
    fields_peq x y -> fields_peq y z -> fields_peq x z.

End TENV.

(*  Method Environment Type  *)

Module Type MENV.

Parameter name : Type.
Parameter rtype : Type.
Parameter method : Type.
Parameter cmd : Type.
Parameter method_locvars : Type.

Parameter args : Type.
Parameter locvars : Type.

Parameter no_args : args.
Parameter no_locvars : locvars.

Parameter method_body : Type.
Parameter mbody_env : Type.
Parameter init_mbody_env : mbody_env.

Parameter beq : mbody_env -> mbody_env -> bool.
Parameter peq : mbody_env -> mbody_env -> Prop.
Parameter pin : rtype -> method -> method_body -> mbody_env -> Prop.

Parameter get_args : method_body -> args.
Parameter update_args : args -> method_body -> method_body.
Parameter map_args : (args -> args) -> method_body -> method_body.
Parameter get_locvars : method_body -> locvars.
Parameter update_locvars : locvars -> method_body -> method_body.
Parameter map_locvars : (locvars -> locvars) -> method_body -> method_body.
Parameter get_cmd : method_body -> option cmd.
Parameter update_cmd : option cmd -> method_body -> method_body.
Parameter map_cmd : (option cmd -> option cmd) -> method_body -> method_body.

Parameter add_locvar : name -> locvars -> locvars.
Parameter add_locvar_2 : name -> rtype -> locvars -> locvars.
Parameter update_mbody_env : rtype -> method -> method_body -> mbody_env -> mbody_env.
Parameter find_mbody : mbody_env -> rtype -> method -> option method_body.

Parameter make_locvars : method_locvars -> locvars.

Axiom equal_1 : forall x y : mbody_env, beq x y = true <-> peq x y.

Axiom eq_refl : forall x : mbody_env, peq x x.
Axiom eq_sym : forall x y : mbody_env, peq x y -> peq y x.
Axiom eq_trans : forall x y z : mbody_env, peq x y -> peq y z -> peq x z.

Axiom in_update_1 : forall (t : rtype) (m : method) (b : method_body) (e : mbody_env),
    pin t m b (update_mbody_env t m b e).
Axiom in_update_2 : forall (t1 t2 : rtype) (m1 m2 : method) (b1 b2 : method_body) (e : mbody_env),
    (t1 <> t2 \/ m1 <> m2) -> pin t1 m1 b1 e -> pin t1 m1 b1 (update_mbody_env t2 m2 b2 e).
Axiom in_update_3 : forall (t1 t2 : rtype) (m1 m2 : method) (b1 b2 : method_body) (e : mbody_env),
    (t1 <> t2 \/ m1 <> m2) -> pin t1 m1 b1 (update_mbody_env t2 m2 b2 e) -> pin t1 m1 b1 e.
Axiom in_find : forall (t : rtype) (m : method) (b : method_body) (e : mbody_env),
    pin t m b e <-> find_mbody e t m = Some b.
Axiom not_in_find : forall (t : rtype) (m : method) (e : mbody_env),
    (forall b, ~ pin t m b e) <-> find_mbody e t m = None.

End MENV.


(*-----  Data  -----*)

Open Scope string_scope.

(*  Type Environment  *)

Module TEnv <: TENV.

Definition name := Name.name.
Definition method := Method.method.
Definition rtype := RType.rtype.

Definition cnames := Sset.t.
Definition init_cnames := Sset.add RType.Object
                         (Sset.add RType.Bool
                         (Sset.add RType.Null Sset.empty)).

Definition super_env := RType.super_env.
Definition init_super_env := RType.init_super_env.

Definition method_type := ((list rtype) * rtype)%type.
Definition class_methods := Smap.t method_type.
Definition methods_env := Smap.t class_methods.
Definition no_method := Smap.empty method_type.
Definition empty_methods_env := Smap.empty (Smap.t method_type).
Definition init_methods_env :=
    Smap.add "Object" no_method
    (Smap.add "Bool" no_method
    (Smap.add "Null" no_method empty_methods_env)).

Definition field_type := RType.field_type.
Definition fields_env := RType.type_env.
Definition init_fields_env := RType.init_type_env.

Definition method_locvars := Smap.t rtype.
Definition method_no_locvar := Smap.empty rtype.
Definition class_locvars := Smap.t method_locvars.
Definition locvars_env := Smap.t class_locvars.
Definition no_locvar := Smap.empty method_locvars.
Definition empty_locvars_env := Smap.empty class_locvars.
Definition init_locvars_env :=
    Smap.add "Object" no_locvar
    (Smap.add "Bool" no_locvar
    (Smap.add "Null" no_locvar empty_locvars_env)).

Definition cnames_beq (c1 c2 : cnames) : bool :=
    Sset.equal c1 c2.

Definition cnames_peq (c1 c2 : cnames) : Prop :=
    Sset.equal c1 c2 = true.

Fixpoint list_beq (l1 l2 : list rtype) : bool :=
    match l1, l2 with
        | nil, nil => true
        | a1::b1, a2::b2 => RType.beq a1 a2 && list_beq b1 b2
        | _, _ => false
    end.

Fixpoint list_peq (l1 l2 : list rtype) : Prop :=
    match l1, l2 with
        | nil, nil => True
        | a1::b1, a2::b2 => RType.peq a1 a2 /\ list_peq b1 b2
        | _, _ => False
    end.

Definition super_beq (s1 s2 : super_env) : bool :=
    Smap.equal list_beq s1 s2.
Definition super_peq (s1 s2 : super_env) : Prop :=
    Smap.Equivb list_beq s1 s2.

Definition method_type_beq (mt1 mt2 : method_type) : bool :=
    match mt1, mt2 with (l1, t1), (l2, t2) =>
        andb (list_beq l1 l2) (RType.beq t1 t2)
    end.
Definition method_type_peq (mt1 mt2 : method_type) : Prop :=
    match mt1, mt2 with (l1, t1), (l2, t2) =>
        (list_peq l1 l2) /\ (RType.peq t1 t2)
    end.

Definition methods_beq (m1 m2 : methods_env) : bool :=
    Smap.equal (Smap.equal method_type_beq) m1 m2.
Definition methods_peq (m1 m2 : methods_env) : Prop :=
    Smap.Equivb (Smap.equal method_type_beq) m1 m2.

Definition locvars_beq (l1 l2 : locvars_env) : bool :=
    Smap.equal (Smap.equal (Smap.equal RType.beq)) l1 l2.
Definition locvars_peq (l1 l2 : locvars_env) : Prop :=
    Smap.Equivb (Smap.equal (Smap.equal RType.beq)) l1 l2.

Definition fields_beq (f1 f2 : fields_env) : bool :=
    Smap.equal (Smap.equal RType.beq) f1 f2.
Definition fields_peq (f1 f2 : fields_env) : Prop :=
    Smap.Equivb (Smap.equal RType.beq) f1 f2.

Definition cnames_add (t : rtype) (c : cnames) : cnames :=
    Sset.add t c.
Definition cnames_find (t : rtype) (c : cnames) : bool :=
    Sset.mem t c.

Definition update_super := RType.update_super_env.
Definition subtype := RType.subtype.

Definition update_fields := RType.update_type_env.
Definition get_fields := RType.get_fields.
Definition map_fields (t : rtype) (mf : field_type -> field_type)
                      (e : fields_env) : fields_env :=
    match get_fields t e with
    | Some f => update_fields t (mf f) e
    | None => e
    end.

Definition update_class_methods (t : rtype) (c : class_methods) (e : methods_env) : methods_env :=
    Smap.add t c e.
(* subclasses inherit all the methods of superclasses *)

Definition update_method (rt : rtype) (m : method) (t : method_type) (e : methods_env) : methods_env :=
    match Smap.find rt e with
        | Some c => Smap.add rt (Smap.add m t c) e
        | None => Smap.add rt (Smap.add m t no_method) e
    end.

Definition find_class_methods (t : rtype) (e : methods_env) : option class_methods :=
    Smap.find t e.
Definition find_method (e : methods_env) (t : rtype) (m : method) : option method_type :=
    match Smap.find t e with
        | Some c => Smap.find m c
        | None => None
    end.

Definition update_method_locvars (n : name) (t : rtype) (l : method_locvars) : method_locvars :=
    Smap.add n t l.
Definition update_class_locvars (m : method) (l : method_locvars) (c : class_locvars) : class_locvars :=
    Smap.add m l c.
Definition update_locvars_env (t : rtype) (c : class_locvars) (e : locvars_env) : locvars_env :=
    Smap.add t c e.
Definition update_a_locvar (t : rtype) (m : method) (l : method_locvars) (e : locvars_env) : locvars_env :=
    match Smap.find t e with
        | Some c => update_locvars_env t (update_class_locvars m l c) e
        | None => update_locvars_env t (update_class_locvars m l no_locvar) e
    end.

Definition find_locvars (l : method_locvars) (n : name) : option rtype :=
    Smap.find n l.
Definition find_locvars_2 (c : class_locvars) (m : method) (n : name) : option rtype :=
    match Smap.find m c with
        | Some l => find_locvars l n
        | None => None
    end.
Definition find_locvars_3 (e : locvars_env) (t : rtype) (m : method) (n : name) : option rtype :=
    match Smap.find t e with
        | Some c => find_locvars_2 c m n
        | None => None
    end.

Lemma cnames_eq_refl : forall x : cnames, cnames_peq x x.
Proof.
  unfold cnames_peq. apply sset_refl.
Qed.
Lemma cnames_eq_sym : forall x y : cnames, cnames_peq x y -> cnames_peq y x.
Proof.
  unfold cnames_peq. apply sset_sym.
Qed.
Lemma cnames_eq_trans : forall x y z : cnames,
    cnames_peq x y -> cnames_peq y z -> cnames_peq x z.
Proof.
  unfold cnames_peq. apply sset_trans.
Qed.

Lemma list_beq_refl : forall x : list rtype, list_beq x x = true.
Proof.
  induction x. unfold list_beq; reflexivity.
  unfold list_beq; fold list_beq.
  apply andb_true_iff. split.
  apply RType.beq_refl. apply IHx.
Qed.
Lemma list_beq_sym : forall x y : list rtype, list_beq x y = true -> list_beq y x = true.
Proof.
  induction x, y. intro; assumption.
  unfold list_beq; intro; assumption.
  unfold list_beq; intro; assumption.
  unfold list_beq; fold list_beq. intro H.
  apply andb_true_iff in H. destruct H.
  apply andb_true_iff. split.
  apply RType.beq_sym; assumption.
  apply IHx; assumption.
Qed.
Lemma list_beq_trans : forall x y z : list rtype,
    list_beq x y = true -> list_beq y z = true -> list_beq x z = true.
Proof.
  induction x. induction y. induction z.
  intros; assumption.
  intros; assumption.
  intros z H; inversion H.
  induction z. induction y.
  intro H; inversion H.
  intros H H0; inversion H0.
  induction y. intro H; inversion H.
  unfold list_beq; fold list_beq. intros H H0.
  apply andb_true_iff in H. destruct H.
  apply andb_true_iff in H0. destruct H0.
  apply andb_true_iff. split.
  apply RType.beq_trans with (y := a1).
  assumption. assumption.
  apply IHx with (y := y).
  assumption. assumption.
Qed.

Lemma super_eq_refl : forall x : super_env, super_peq x x.
Proof.
  unfold super_peq. intro.
  apply smap_refl_1. apply list_beq_refl.
Qed.
Lemma super_eq_sym : forall x y : super_env, super_peq x y -> super_peq y x.
Proof.
  unfold super_peq. intros x y.
  apply smap_sym_1. apply list_beq_sym.
Qed.
Lemma super_eq_trans : forall x y z : super_env,
    super_peq x y -> super_peq y z -> super_peq x z.
Proof.
  unfold super_peq. intros x y z.
  apply smap_trans_1. apply list_beq_trans.
Qed.

Lemma method_type_beq_refl : forall x : method_type, method_type_beq x x = true.
Proof.
  intro x. unfold method_type_beq.
  induction x. apply andb_true_iff. split.
  apply list_beq_refl.
  apply RType.beq_refl.
Qed.
Lemma method_type_beq_sym : forall x y : method_type,
    method_type_beq x y = true -> method_type_beq y x = true.
Proof.
  unfold method_type_beq. intros x y H.
  induction x, y. apply andb_true_iff in H.
  destruct H. apply andb_true_iff. split.
  apply list_beq_sym; assumption.
  apply RType.beq_sym; assumption.
Qed.
Lemma method_type_beq_trans : forall x y z : method_type,
    method_type_beq x y = true -> method_type_beq y z = true -> method_type_beq x z = true.
Proof.
  unfold method_type_beq. intros x y z H H0.
  induction x, y, z. apply andb_true_iff in H.
  destruct H. apply andb_true_iff in H0.
  destruct H0. apply andb_true_iff. split.
  apply list_beq_trans with (y := l).
  assumption. assumption.
  apply RType.beq_trans with (y := r).
  assumption. assumption.
Qed.

Lemma methods_eq_refl : forall x : methods_env, methods_peq x x.
Proof.
  unfold methods_peq. intro.
  apply smap_refl_1. intro.
  apply smap_refl_2. apply method_type_beq_refl.
Qed.
Lemma methods_eq_sym : forall x y : methods_env, methods_peq x y -> methods_peq y x.
Proof.
  unfold methods_peq. intros x y.
  apply smap_sym_1. intros t1 t2.
  apply smap_sym_2. apply method_type_beq_sym.
Qed.
Lemma methods_eq_trans : forall x y z : methods_env,
    methods_peq x y -> methods_peq y z -> methods_peq x z.
Proof.
  unfold methods_peq. intros x y z.
  apply smap_trans_1. intros t1 t2 t3.
  apply smap_trans_2. apply method_type_beq_trans.
Qed.

Lemma locvars_eq_refl : forall x : locvars_env, locvars_peq x x.
Proof.
  unfold locvars_peq. intro.
  apply smap_refl_1. intro.
  apply smap_refl_2. intro.
  apply smap_refl_2. apply RType.beq_refl.
Qed.
Lemma locvars_eq_sym : forall x y : locvars_env, locvars_peq x y -> locvars_peq y x.
Proof.
  unfold locvars_peq. intros x y.
  apply smap_sym_1. intros t1 t2.
  apply smap_sym_2. intros t0 t3.
  apply smap_sym_2. apply RType.beq_sym.
Qed.
Lemma locvars_eq_trans : forall x y z : locvars_env,
    locvars_peq x y -> locvars_peq y z -> locvars_peq x z.
Proof.
  unfold locvars_peq. intros x y z.
  apply smap_trans_1. intros t1 t2 t3.
  apply smap_trans_2. intros t0 t4 t5.
  apply smap_trans_2. apply RType.beq_trans.
Qed.

Lemma fields_eq_refl : forall x : fields_env, fields_peq x x.
Proof.
  unfold fields_peq. intro.
  apply smap_refl_1. intro.
  apply smap_refl_2. apply RType.beq_refl.
Qed.
Lemma fields_eq_sym : forall x y : fields_env, fields_peq x y -> fields_peq y x.
Proof.
  unfold fields_peq. intros x y.
  apply smap_sym_1. intros t1 t2.
  apply smap_sym_2. apply RType.beq_sym.
Qed.
Lemma fields_eq_trans : forall x y z : fields_env,
    fields_peq x y -> fields_peq y z -> fields_peq x z.
Proof.
  unfold fields_peq. intros x y z.
  apply smap_trans_1. intros t1 t2 t3.
  apply smap_trans_2. apply RType.beq_trans.
Qed.

End TEnv.

(*  Method Environment  *)

Module MEnv <: MENV.

Definition name := Name.name.
Definition rtype := RType.rtype.
Definition method := Method.method.
Definition cmd := Lang.cmd.
Definition method_locvars := TEnv.method_locvars.

(* 方法体包含参数列表，局部变量列表，以及一条命令。
   直接用list实现参数列表，以记录参数之间的顺序。 *)
Definition args := list name.
Definition locvars := Sset.t.

Definition no_args := nil (A := name).
Definition no_locvars := Sset.empty.

Definition method_body := (args * locvars * (option cmd))%type.
Definition mbody_env := Smap.t (Smap.t method_body).

Definition no_method := Smap.empty method_body.
Definition init_mbody_env :=
    Smap.add "Object" no_method
    (Smap.add "Bool" no_method
    (Smap.add "Null" no_method (Smap.empty (Smap.t method_body)))).

Fixpoint args_beq (a1 a2 : args) : bool :=
    match a1, a2 with
        | nil, nil => true
        | b1::c1, b2::c2 => andb (Name.beq b1 b2) (args_beq c1 c2)
        | _, _ => false
    end.

Fixpoint args_peq (a1 a2 : args) : Prop :=
    match a1, a2 with
        | nil, nil => True
        | b1::c1, b2::c2 => (Name.peq b1 b2) /\ (args_peq c1 c2)
        | _, _ => False
    end.

Definition method_body_beq (m1 m2 : method_body) : bool :=
    match m1, m2 with (a1, l1, oc1), (a2, l2, oc2) =>
        andb (args_beq a1 a2) (andb (Sset.equal l1 l2)
        match oc1, oc2 with
        | Some c1, Some c2 => Lang.beq c1 c2
        | None, None => true
        | _, _ => false
        end)
    end.

Definition method_body_peq (m1 m2 : method_body) : Prop :=
    match m1, m2 with (a1, l1, oc1), (a2, l2, oc2) =>
        args_peq a1 a2 /\ Sset.equal l1 l2 = true /\
        match oc1, oc2 with
        | Some c1, Some c2 => Lang.peq c1 c2
        | None, None => True
        | _, _ => False
        end
    end.

Definition beq (m1 m2 : mbody_env) : bool :=
    Smap.equal (Smap.equal method_body_beq) m1 m2.

Definition peq (m1 m2 : mbody_env) : Prop :=
    Smap.Equivb (Smap.equal method_body_beq) m1 m2.

Definition pin (t : rtype) (m : method) (mb : method_body) (me : mbody_env) :=
    exists i, Smap.MapsTo t i me /\ Smap.MapsTo m mb i.

Definition In (t : rtype) (m : method) (me : mbody_env) :=
    exists mb, pin t m mb me /\ snd mb <> None.

Definition get_args (m : method_body) : args :=
    fst (fst m).
Definition update_args (l : args) (m : method_body) : method_body :=
    match m with (A, B, C) => (l, B, C) end.
Definition map_args (l : args -> args) (m : method_body) : method_body :=
    match m with (A, B, C) => (l A, B, C) end.
Definition get_locvars (m : method_body) : locvars :=
    snd (fst m).
Definition update_locvars (l : locvars) (m : method_body) : method_body :=
    match m with (A, B, C) => (A, l, C) end.
Definition map_locvars (l : locvars -> locvars) (m : method_body) : method_body :=
    match m with (A, B, C) => (A, l B, C) end.
Definition get_cmd (m : method_body) : option cmd :=
    snd m.
Definition update_cmd (c : option cmd) (m : method_body) : method_body :=
    match m with (A, B, C) => (A, B, c) end.
Definition map_cmd (c : option cmd -> option cmd) (m : method_body) : method_body :=
    match m with (A, B, C) => (A, B, c C) end.

Definition add_locvar (n : name) (l : locvars) : locvars :=
    Sset.add n l.
Definition add_locvar_2 (n : name) (t : rtype) (l : locvars) : locvars :=
    Sset.add n l.

Definition update_class_mbody (t : rtype) (c : Smap.t method_body)
                              (e : mbody_env) : mbody_env :=
    Smap.add t c e.
Definition find_class_mbody (t : rtype) (e : mbody_env) : option (Smap.t method_body) :=
    Smap.find t e.

Definition update_mbody_env (t : rtype) (m : method) (b : method_body)
                            (e : mbody_env) : mbody_env :=
    match Smap.find t e with
        | Some i => Smap.add t (Smap.add m b i) e
        | None => Smap.add t (Smap.add m b no_method) e
    end.
Definition find_mbody (e : mbody_env) (t : rtype) (m : method) : option method_body :=
    match Smap.find t e with
        | Some i => Smap.find m i
        | None => None
    end.

Definition make_locvars (m : method_locvars) : locvars :=
    Smap.fold add_locvar_2 m no_locvars.

Lemma equal_1 : forall x y : mbody_env, beq x y = true <-> peq x y.
Proof.
  intros x y. unfold beq; unfold peq.
  split. apply Smap.equal_2. apply Smap.equal_1.
Qed.

Lemma args_beq_refl : forall x : args, args_beq x x = true.
Proof.
  intro x. induction x.
  unfold args_beq; reflexivity.
  unfold args_beq; fold args_beq.
  apply andb_true_iff. split.
  apply Name.beq_refl. apply IHx.
Qed.
Lemma args_beq_sym : forall x y : args, args_beq x y = true -> args_beq y x = true.
Proof.
  induction x, y. intro; assumption.
  intro H; inversion H.
  intro H; inversion H.
  unfold args_beq; fold args_beq. intro H.
  apply andb_true_iff in H. destruct H.
  apply andb_true_iff. split.
  apply Name.beq_sym; assumption.
  apply IHx; assumption.
Qed.
Lemma args_beq_trans : forall x y z : args,
    args_beq x y = true -> args_beq y z = true -> args_beq x z = true.
Proof.
  induction x, y. intros; assumption.
  intros z H; inversion H.
  intros z H; inversion H.
  induction z. intros H H0; inversion H0.
  unfold args_beq; fold args_beq. intros H H0.
  apply andb_true_iff in H. destruct H.
  apply andb_true_iff in H0. destruct H0.
  apply andb_true_iff. split.
  apply Name.beq_trans with (y := n).
  assumption. assumption.
  apply IHx with (y := y).
  assumption. assumption.
Qed.

Lemma method_body_beq_refl : forall x : method_body, method_body_beq x x = true.
Proof.
  intro x. induction x. induction a.
  unfold method_body_beq. apply andb_true_iff.
  split. apply args_beq_refl.
  apply andb_true_iff. split.
  apply sset_refl. induction b.
  apply Lang.beq_refl. reflexivity.
Qed.
Lemma method_body_beq_sym : forall x y : method_body,
    method_body_beq x y = true -> method_body_beq y x = true.
Proof.
  induction x, y. induction a, p.
  unfold method_body_beq. intro H.
  apply andb_true_iff in H. destruct H.
  apply andb_true_iff in H0. destruct H0.
  apply andb_true_iff. split.
  apply args_beq_sym. assumption.
  apply andb_true_iff. split.
  apply sset_sym. assumption.
  induction b. induction o.
  apply Lang.beq_sym. assumption.
  assumption. assumption.
Qed.
Lemma method_body_beq_trans : forall x y z : method_body,
    method_body_beq x y = true -> method_body_beq y z = true -> method_body_beq x z = true.
Proof.
  induction x, y, z. induction a, p, p0.
  unfold method_body_beq. intros H H0.
  apply andb_true_iff in H. destruct H.
  apply andb_true_iff in H1. destruct H1.
  apply andb_true_iff in H0. destruct H0.
  apply andb_true_iff in H3. destruct H3.
  apply andb_true_iff. split.
  apply args_beq_trans with (y := a0).
  assumption. assumption.
  apply andb_true_iff. split.
  apply sset_trans with (e2 := l).
  assumption. assumption.
  induction b, o. induction o0.
  apply Lang.beq_trans with (c2 := c).
  assumption. assumption. assumption.
  discriminate. discriminate. assumption.
Qed.

Lemma eq_refl : forall x : mbody_env, peq x x.
Proof.
  unfold peq. intro.
  apply smap_refl_1. intro.
  apply smap_refl_2. apply method_body_beq_refl.
Qed.
Lemma eq_sym : forall x y : mbody_env, peq x y -> peq y x.
Proof.
  unfold peq. intros x y.
  apply smap_sym_1. intros t1 t2.
  apply smap_sym_2. apply method_body_beq_sym.
Qed.
Lemma eq_trans : forall x y z : mbody_env, peq x y -> peq y z -> peq x z.
Proof.
  unfold peq. intros x y z.
  apply smap_trans_1. intros t1 t2 t3.
  apply smap_trans_2. apply method_body_beq_trans.
Qed.

Lemma in_update_1 : forall (t : rtype) (m : method) (b : method_body) (e : mbody_env),
    pin t m b (update_mbody_env t m b e).
Proof.
  intros t m b e. unfold update_mbody_env.
  case (Smap.find t e).
  intro m0. unfold pin.
  exists (Smap.add m b m0). split.
  apply Smap.add_1; reflexivity.
  apply Smap.add_1; reflexivity.
  unfold pin. exists (Smap.add m b no_method).
  split.
  apply Smap.add_1; reflexivity.
  apply Smap.add_1; reflexivity.
Qed.

Lemma in_update_2 : forall (t1 t2 : rtype) (m1 m2 : method) (b1 b2 : method_body) (e : mbody_env),
    (t1 <> t2 \/ m1 <> m2) -> pin t1 m1 b1 e -> pin t1 m1 b1 (update_mbody_env t2 m2 b2 e).
Proof.
  intros t1 t2 m1 m2 b1 b2 e H H0.
  unfold update_mbody_env; unfold pin in H0.
  do 2 destruct H0.
  case RType.eq_dec with (s1 := t1) (s2 := t2).
  intro H2.
  destruct H. elim H; assumption.
  rewrite <- H2. apply Smap.find_1 in H0.
  rewrite H0. unfold pin.
  exists (Smap.add m2 b2 x).
  split. apply Smap.add_1. reflexivity.
  apply Smap.add_2. auto.
  assumption. intro H2.
  unfold pin. exists x.
  split. case (Smap.find t2 e).
  intro m. apply Smap.add_2. auto.
  assumption. apply Smap.add_2. auto.
  assumption. assumption.
Qed.

Lemma in_update_3 : forall (t1 t2 : rtype) (m1 m2 : method) (b1 b2 : method_body) (e : mbody_env),
    (t1 <> t2 \/ m1 <> m2) -> pin t1 m1 b1 (update_mbody_env t2 m2 b2 e) -> pin t1 m1 b1 e.
Proof.
  intros t1 t2 m1 m2 b1 b2 e H H0.
  unfold update_mbody_env in H0; unfold pin in H0.
  do 2 destruct H0.
  case RType.eq_dec with (s1 := t1) (s2 := t2).
  intro H2. destruct H. elim H; assumption.
  rewrite <- H2 in H0.
  inductS (Smap.find t1 e); rewrite H3 in H0.
  assert (x = Smap.add m2 b2 x0).
  apply smap_add in H0. assumption.
  exists x0. split.
  apply Smap.find_2 in H3. assumption.
  rewrite H4 in H1.
  apply Smap.add_3 in H1. assumption. auto.
  assert (x = Smap.add m2 b2 no_method).
  assert (Smap.MapsTo t1 (Smap.add m2 b2 no_method)
    (Smap.add t1 (Smap.add m2 b2 no_method) e)).
  apply Smap.add_1. reflexivity.
  apply smap_inject with (k := t1)
    (m := (Smap.add t1 (Smap.add m2 b2 no_method) e)).
  assumption. assumption.
  rewrite H4 in H1.
  apply Smap.add_3 in H1.
  apply Smap.empty_1 in H1. elim H1. auto.
  intro H2. inductS (Smap.find t2 e);
  rewrite H3 in H0; apply Smap.add_3 in H0;
  try (exists x; split; assumption); auto.
Qed.

Lemma in_find : forall (t : rtype) (m : method) (b : method_body) (e : mbody_env),
    pin t m b e <-> find_mbody e t m = Some b.
Proof.
  intros t m b e. split. intro H.
  unfold pin in H. do 2 destruct H.
  unfold find_mbody.
  apply Smap.find_1 in H. rewrite H.
  apply Smap.find_1 in H0.
  unfold find_mbody. assumption.
  intro H. unfold find_mbody in H.
  unfold pin.
  inductS (Smap.find t e); rewrite H0 in H.
  apply Smap.find_2 in H.
  apply Smap.find_2 in H0.
  exists x; split; assumption.
  inversion H.
Qed.

Lemma not_in_find : forall (t : rtype) (m : method) (e : mbody_env),
    (forall b, ~ pin t m b e) <-> find_mbody e t m = None.
Proof.
  intros t m e. split. intro H.
  unfold pin in H. unfold find_mbody.
  inductS (Smap.find t e).
  apply Smap.find_2 in H0.
  assert (forall b, ~ Smap.MapsTo m b x).
  intros b H1. elim H with (b := b).
  exists x; split; assumption.
  unfold find_mbody. inductS (Smap.find m x).
  apply Smap.find_2 in H2.
  elim H1 with (b := x0). assumption.
  reflexivity. reflexivity.
  intros H b H0. unfold find_mbody in H.
  inductS (Smap.find t e); rewrite H1 in H.
  do 2 destruct H0.
  apply Smap.find_1 in H0. rewrite H1 in H0.
  inversion H0. rewrite <- H4 in H2.
  apply Smap.find_1 in H2.
  rewrite H2 in H. inversion H.
  do 2 destruct H0. apply Smap.find_1 in H0.
  rewrite H1 in H0. inversion H0.
Qed.

End MEnv.

Close Scope string_scope.