Require Import String.
Require Import Arith.
Require Import EqNat.
Require Import Bool.
Require Import FMapWeakList.
Require Import MSetWeakList.
Require Import DecidableTypeEx.

(*-----  Abstract Data Type  -----*)

(*  Name Type  *)

Module Type NAME.

Parameter name : Set.

Parameter Ntrue : name.
Parameter Nfalse : name.
Parameter Nnull : name.
Parameter Nres : name.
Parameter Nthis : name.

Parameter beq : name -> name -> bool.
Parameter peq : name -> name -> Prop.
Parameter eq_dec : forall x y : name, {x = y} + {x <> y}.

Axiom equal_1 : forall x y, beq x y = true <-> peq x y.

Axiom beq_refl : forall x : name, beq x x = true.
Axiom beq_sym : forall x y : name, beq x y = true <-> beq y x = true.
Axiom beq_trans : forall x y z : name, beq x y = true -> beq y z = true -> beq x z = true.

Axiom eq_refl : forall x : name, peq x x.
Axiom eq_sym : forall x y : name, peq x y -> peq y x.
Axiom eq_trans : forall x y z : name, peq x y -> peq y z -> peq x z.

End NAME.

(*  Method Type  *)

Module Type METHOD.

Parameter method : Set.

Parameter beq : method -> method -> bool.
Parameter peq : method -> method -> Prop.
Parameter eq_dec : forall x y : method, {x = y} + {x <> y}.

Axiom equal_1 : forall x y, beq x y = true <-> peq x y.

Axiom beq_refl : forall x : method, beq x x = true.
Axiom beq_sym : forall x y : method, beq x y = true <-> beq y x = true.
Axiom beq_trans : forall x y z : method, beq x y = true -> beq y z = true -> beq x z = true.

Axiom eq_refl : forall x : method, peq x x.
Axiom eq_sym : forall x y : method, peq x y -> peq y x.
Axiom eq_trans : forall x y z : method, peq x y -> peq y z -> peq x z.

End METHOD.

(*  RType Type  *)

Module Type RTYPE.

Parameter name : Set.

Parameter rtype : Set.
Parameter Object : rtype.
Parameter Null : rtype.
Parameter Bool : rtype.
Parameter Int : rtype.

Parameter field_type : Type.
Parameter empty_field_type : field_type.
Parameter type_env : Type.
Parameter init_type_env : type_env.

Parameter super_env : Type.
Parameter init_super_env : super_env.

Parameter beq : rtype -> rtype -> bool.
Parameter peq : rtype -> rtype -> Prop.
Parameter eq_dec : forall x y : rtype, {x = y} + {x <> y}.
Parameter update_type_env : rtype -> field_type -> type_env -> type_env.
Parameter update_field_type : name -> rtype -> field_type -> field_type.
Parameter update_super_env : rtype -> list rtype -> super_env -> super_env.
Parameter get_super : rtype -> super_env -> option (list rtype).
Parameter get_fields : rtype -> type_env -> option field_type.

Inductive subtype : rtype -> rtype -> super_env -> Prop :=
    | null_subt   : forall x y s, x = Null -> subtype x y s
    | self_subt   : forall x s, subtype x x s
    | direct_subt : forall x y z s, get_super x s = Some z -> List.In y z ->
                                      subtype x y s
    | trans_subt  : forall x y s, (exists z, subtype x z s /\ subtype z y s) ->
                                      subtype x y s.

Axiom equal_1 : forall x y, beq x y = true <-> peq x y.

Axiom beq_refl : forall x : rtype, beq x x = true.
Axiom beq_sym : forall x y : rtype, beq x y = true <-> beq y x = true.
Axiom beq_trans : forall x y z : rtype, beq x y = true -> beq y z = true -> beq x z = true.

Axiom eq_refl : forall x : rtype, peq x x.
Axiom eq_sym : forall x y : rtype, peq x y -> peq y x.
Axiom eq_trans : forall x y z : rtype, peq x y -> peq y z -> peq x z.

End RTYPE.

(*  Reference Type  *)

Module Type REF.

Parameter rtype : Set.

Parameter ref : Set.
Parameter rtrue : ref.
Parameter rfalse : ref.
Parameter rnull : ref.

Parameter alloc : Set.
Parameter init_alloc : alloc.

Parameter alloc_count : alloc -> nat. 
Parameter new : rtype -> alloc -> alloc.
Parameter get_new : alloc -> ref.
Parameter beq : ref -> ref -> bool.
Parameter peq : ref -> ref -> Prop.
Parameter alloc_beq : alloc -> alloc -> bool.
Parameter alloc_peq : alloc -> alloc -> Prop.

Parameter eq_dec : forall x y : ref, {x = y} + {x <> y}.
Parameter get_type : ref -> rtype.
Parameter get_id : ref -> nat.

Axiom equal_1 : forall x y, beq x y = true <-> peq x y.
Axiom equal_2 : forall x y, peq x y <-> x = y.

Axiom beq_refl : forall x : ref, beq x x = true.
Axiom beq_sym : forall x y : ref, beq x y = true <-> beq y x = true.
Axiom beq_trans : forall x y z : ref, beq x y = true -> beq y z = true -> beq x z = true.

Axiom eq_refl : forall x : ref, peq x x.
Axiom eq_sym : forall x y : ref, peq x y -> peq y x.
Axiom eq_trans : forall x y z : ref, peq x y -> peq y z -> peq x z.

Axiom alloc_eq_refl : forall a : alloc, alloc_peq a a.
Axiom alloc_eq_sym : forall a1 a2 : alloc, alloc_peq a1 a2 -> alloc_peq a2 a1.
Axiom alloc_eq_trans : forall a1 a2 a3 : alloc,
    alloc_peq a1 a2 -> alloc_peq a2 a3 -> alloc_peq a1 a3.

End REF.


(*-----  Data  -----*)

(*  string_map  *)

Module string_DT' <: MiniDecidableType.
Definition t := string.
Definition eq_dec := string_dec.
End string_DT'.

Module string_DT <: UsualDecidableType := Make_UDT string_DT'.

Module Smap := FMapWeakList.Make string_DT.

Lemma smap_refl_1 : forall (t : Type) (eq : t -> t -> bool) e1, 
    (forall t1, eq t1 t1 = true) -> Smap.Equivb eq e1 e1.
Proof.
  intros t eq e1 H.
  unfold Smap.Equivb.
  unfold Smap.Raw.Equivb.
  split. intro k. split.
  intro; assumption.
  intro; assumption.
  intros k e e' H0 H1.
  apply Smap.find_1 in H0.
  apply Smap.find_1 in H1.
  rewrite H1 in H0. inversion H0.
  apply H.
Qed.
Lemma smap_sym_1 : forall (t : Type) (eq : t -> t -> bool) e1 e2, 
    (forall t1 t2, eq t1 t2 = true -> eq t2 t1 = true)
        -> Smap.Equivb eq e1 e2 -> Smap.Equivb eq e2 e1.
Proof.
  intros t eq e1 e2 H H0.
  unfold Smap.Equivb.
  unfold Smap.Raw.Equivb.
  unfold Smap.Equivb in H0.
  unfold Smap.Raw.Equivb in H0.
  destruct H0.
  split. intro k. split.
  intro; apply H0; assumption.
  intro; apply H0; assumption.
  intros k e e' H2 H3.
  assert (eq e' e = true).
  apply H1 with (k := k).
  assumption. assumption.
  apply H; assumption.
Qed.
Lemma smap_trans_1 : forall (t : Type) (eq : t -> t -> bool) e1 e2 e3, 
    (forall t1 t2 t3, eq t1 t2 = true -> eq t2 t3 = true -> eq t1 t3 = true)
        -> Smap.Equivb eq e1 e2 -> Smap.Equivb eq e2 e3 -> Smap.Equivb eq e1 e3.
Proof.
  intros t eq e1 e2 e3 H H0 H1.
  unfold Smap.Equivb.
  unfold Smap.Raw.Equivb.
  unfold Smap.Equivb in H0.
  unfold Smap.Raw.Equivb in H0.
  unfold Smap.Equivb in H1.
  unfold Smap.Raw.Equivb in H1.
  destruct H0. destruct H1.
  split. intro k. split.
  intro; apply H1; apply H0; assumption.
  intro; apply H0; apply H1; assumption.
  intros k e e' H4 H5.
  assert (Smap.Raw.PX.In k (Smap.this e2)).
  apply H1. exists e'. assumption.
  destruct H6. assert (eq e x = true).
  apply H2 with (k := k).
  assumption. assumption.
  assert (eq x e' = true).
  apply H3 with (k := k).
  assumption. assumption.
  apply H with (t2 := x).
  assumption. assumption.
Qed.

Lemma smap_refl_2 : forall (t : Type) (eq : t -> t -> bool) e1, 
    (forall t1, eq t1 t1 = true) -> Smap.equal eq e1 e1 = true.
Proof.
  intros t eq e1 H.
  apply Smap.equal_1.
  apply smap_refl_1.
  assumption.
Qed.
Lemma smap_sym_2 : forall (t : Type) (eq : t -> t -> bool) e1 e2, 
    (forall t1 t2, eq t1 t2 = true -> eq t2 t1 = true)
        -> Smap.equal eq e1 e2 = true -> Smap.equal eq e2 e1 = true.
Proof.
  intros t eq e1 e2 H H0.
  apply Smap.equal_1.
  apply Smap.equal_2 in H0.
  apply smap_sym_1.
  assumption. assumption.
Qed.
Lemma smap_trans_2 : forall (t : Type) (eq : t -> t -> bool) e1 e2 e3, 
  (forall t1 t2 t3, eq t1 t2 = true -> eq t2 t3 = true -> eq t1 t3 = true)
    -> Smap.equal eq e1 e2 = true -> Smap.equal eq e2 e3 = true -> Smap.equal eq e1 e3 = true.
Proof.
  intros t eq e1 e2 e3 H H0 H1.
  apply Smap.equal_1.
  apply Smap.equal_2 in H0.
  apply Smap.equal_2 in H1.
  apply smap_trans_1 with (e2 := e2).
  assumption. assumption. assumption.
Qed.
Lemma smap_equal: forall (t : Type) (eq : t -> t -> bool),
    (forall e1 e2, eq e1 e2 = true <-> e1 = e2) -> 
    (forall m1 m2, Smap.equal eq m1 m2 = true <-> m1 = m2).
Proof.
  intros t eq H m1 m2.
Admitted.
Lemma smap_inject: forall (t : Type) k (e1 e2 : t) m,
    Smap.MapsTo k e1 m -> Smap.MapsTo k e2 m -> e1 = e2.
Proof.
  intros t k e1 e2 m H H0.
  apply Smap.find_1 in H.
  apply Smap.find_1 in H0.
  rewrite H in H0. inversion H0.
  reflexivity.
Qed.
Lemma smap_add: forall (t : Type) k (e1 e2 : t) m,
    Smap.MapsTo k e1 (Smap.add k e2 m) -> e1 = e2.
Proof.
  intros t k e1 e2 m H.
  assert (Smap.MapsTo k e2 (Smap.add k e2 m)).
  apply Smap.add_1. reflexivity.
  apply smap_inject with (k := k) (m := Smap.add k e2 m).
  assumption. assumption.
Qed.

(*  string_set  *)

Module Sset := MSetWeakList.Make string_DT.

Lemma sset_refl : forall e1, Sset.equal e1 e1 = true.
Proof.
  intro e1. apply Sset.equal_spec.
  unfold Sset.Equal. intro a. split.
  intro; assumption.
  intro; assumption.
Qed.
Lemma sset_sym : forall e1 e2, Sset.equal e1 e2 = true -> Sset.equal e2 e1 = true.
Proof.
  intros e1 e2 H.
  apply Sset.equal_spec.
  apply Sset.equal_spec in H.
  unfold Sset.Equal.
  unfold Sset.Equal in H.
  intro; split.
  apply H. apply H.
Qed.
Lemma sset_trans : forall e1 e2 e3, 
    Sset.equal e1 e2 = true -> Sset.equal e2 e3 = true -> Sset.equal e1 e3 = true.
Proof.
  intros e1 e2 e3 H H0.
  apply Sset.equal_spec.
  apply Sset.equal_spec in H.
  apply Sset.equal_spec in H0.
  unfold Sset.Equal.
  unfold Sset.Equal in H.
  unfold Sset.Equal in H0.
  intro; split.
  intro; apply H0; apply H; assumption.
  intro; apply H; apply H0; assumption.
Qed.

Definition sset_dsj (s1 s2 : Sset.t) := forall x,
    (Sset.In x s1 -> ~ Sset.In x s2) /\ (Sset.In x s2 -> ~ Sset.In x s1).

Lemma sset_dsj_empty : forall s, sset_dsj s Sset.empty.
Proof.
  unfold sset_dsj. intros s x. split.
  intro; apply Sset.empty_spec.
  intro H; apply Sset.empty_spec in H; elim H.
Qed.
Lemma sset_dsj_sym : forall s1 s2, sset_dsj s1 s2 -> sset_dsj s2 s1.
Proof.
  unfold sset_dsj. intros s1 s2 H x.
  destruct H with (x := x).
  split. assumption. assumption.
Qed.
Lemma sset_dsj_union : forall s1 s2 s3,
    sset_dsj s1 (Sset.union s2 s3) <-> sset_dsj s1 s2 /\ sset_dsj s1 s3.
Proof.
  unfold sset_dsj. intros s1 s2 s3.
  split. intro H. split. intro x.
  destruct H with (x := x). split.
  intros H2 H3. apply H0 in H2; elim H2.
  apply Sset.union_spec. left; assumption.
  intros H2 H3. apply H0 in H3; elim H3.
  apply Sset.union_spec. left; assumption.
  intro x. destruct H with (x := x). split.
  intros H2 H3. apply H0 in H2; elim H2.
  apply Sset.union_spec. right; assumption.
  intros H2 H3. apply H0 in H3; elim H3.
  apply Sset.union_spec. right; assumption.
  intros H x. destruct H. destruct H with (x := x).
  destruct H0 with (x := x). split.
  intros H5 H6. apply Sset.union_spec in H6.
  destruct H6. apply H2 in H6; elim H6; assumption.
  apply H4 in H6; elim H6; assumption.
  intros H5 H6. apply Sset.union_spec in H5.
  destruct H5. apply H2 in H5; elim H5; assumption.
  apply H4 in H5; elim H5; assumption.
Qed.
Lemma sset_dsj_self : forall s, sset_dsj s s -> Sset.Empty s.
Proof.
  unfold Sset.Empty; unfold sset_dsj.
  intros s H a H0. destruct H with (x := a).
  elim H1. assumption. assumption.
Qed.
Lemma sset_dsj_left : forall s1 s2 e,
    sset_dsj (Sset.add e s1) s2 <-> ~ Sset.In e s2 /\ sset_dsj s1 s2.
Proof.
  unfold sset_dsj. intros s1 s2 e. split.
  intro H. split. destruct H with (x := e).
  intro H2. apply H1 in H2; elim H2.
  apply Sset.add_spec. left; reflexivity.
  intro x. destruct H with (x := x). split.
  intros H2 H3. apply H1 in H3; elim H3.
  apply Sset.add_spec. right; assumption.
  intros H2 H3. apply H1 in H2; elim H2.
  apply Sset.add_spec. right; assumption.
  intros H x. destruct H. split.
  intros H1 H2. apply Sset.add_spec in H1.
  destruct H1. elim H; rewrite <- H1; assumption.
  apply H0 in H1. assumption. assumption.
  intros H1 H2. apply Sset.add_spec in H2.
  destruct H2. elim H; rewrite <- H2; assumption.
  apply H0 in H2. assumption. assumption.
Qed.
Lemma sset_dsj_right : forall s1 s2 e,
    sset_dsj s1 (Sset.add e s2) <-> ~ Sset.In e s1 /\ sset_dsj s1 s2.
Proof.
  intros s1 s2 e. split.
  intro H. apply sset_dsj_sym in H.
  apply sset_dsj_left in H. destruct H.
  split. assumption. apply sset_dsj_sym; assumption.
  intro H. destruct H. apply sset_dsj_sym in H0.
  apply sset_dsj_sym. apply sset_dsj_left.
  split. assumption. assumption.
Qed.
Lemma sset_dsj_card : forall s1 s2,
    Sset.cardinal (Sset.union s1 s2) = Sset.cardinal s1 + Sset.cardinal s2
    -> sset_dsj s1 s2.
Proof.
  intro s1. case (eq_nat_dec (Sset.cardinal s1) (Sset.cardinal s1)).
  pattern (Sset.cardinal s1) at -1.
  induction (Sset.cardinal s1).
  intros H s2 H0.
Admitted.

Open Scope string_scope.

(*  Name  *)

Module Name <: NAME.

Definition name := string.

Definition Ntrue := "true".
Definition Nfalse := "false".
Definition Nnull := "null".
Definition Nres := "res".
Definition Nthis := "this".

Definition beq x y := andb (prefix x y) (prefix y x).
Definition peq (x y : name) := x = y.
Definition eq_dec := string_dec.

Lemma prefix_refl : forall x, prefix x x = true.
Proof.
  induction x. auto.
  unfold prefix; fold prefix.
  case (Ascii.ascii_dec a a).
  intro; assumption.
  intro H; elim H; reflexivity.
Qed.

Lemma equal_1 : forall x y, beq x y = true <-> peq x y.
Proof.
  unfold beq; unfold peq. induction x, y.
  simpl. tauto. simpl. split.
  intro; discriminate.
  intro; discriminate.
  simpl. split.
  intro; discriminate.
  intro; discriminate.
  unfold prefix; fold prefix.
  case (Ascii.ascii_dec a a0).
  intro H. rewrite H. split.
  intro H0. apply Bool.andb_true_iff in H0.
  destruct H0. case (Ascii.ascii_dec a0 a0) in H1.
  assert (x = y). apply IHx.
  apply Bool.andb_true_iff. split.
  assumption. assumption.
  rewrite H2; reflexivity.
  discriminate. intro H0.
  inversion H0.
  apply Bool.andb_true_iff. split.
  apply prefix_refl.
  rewrite prefix_refl.
  case (Ascii.ascii_dec a0 a0).
  intro; reflexivity.
  intro H1; elim H1; reflexivity.
  intro H. split. intro H0.
  apply Bool.andb_true_iff in H0. destruct H0.
  discriminate. intro H0.
  inversion H0. elim H. assumption.
Qed.

Lemma eq_refl : forall x : name, peq x x.
Proof.
  unfold peq.
  reflexivity.
Qed.
Lemma eq_sym : forall x y : name, peq x y -> peq y x.
Proof.
  unfold peq.
  intros x y H.
  rewrite H; reflexivity.
Qed.
Lemma eq_trans : forall x y z : name, peq x y -> peq y z -> peq x z.
Proof.
  unfold peq.
  intros x y z H0 H1.
  rewrite H0; assumption.
Qed.

Lemma beq_refl : forall x : name, beq x x = true.
Proof.
  intro x. apply equal_1.
  reflexivity.
Qed.
Lemma beq_sym : forall x y : name, beq x y = true <-> beq y x = true.
Proof.
  intros x y. split.
  intro H. apply equal_1 in H.
  rewrite H. apply beq_refl.
  intro H. apply equal_1 in H.
  rewrite H. apply beq_refl.
Qed.
Lemma beq_trans : forall x y z : name,
    beq x y = true -> beq y z = true -> beq x z = true.
Proof.
  intros x y z H H0.
  apply equal_1 in H.
  apply equal_1 in H0.
  rewrite H. rewrite H0.
  apply beq_refl.
Qed.

End Name.

(*  Method  *)

Module Method <: METHOD.

Definition method := string.

Definition beq x y := andb (prefix x y) (prefix y x).
Definition peq (x y : method) := x = y.
Definition eq_dec := string_dec.

Lemma equal_1 : forall x y, beq x y = true <-> peq x y.
Proof.
  apply Name.equal_1.
Qed.

Lemma eq_refl : forall x : method, peq x x.
Proof.
  unfold peq.
  reflexivity.
Qed.
Lemma eq_sym : forall x y : method, peq x y -> peq y x.
Proof.
  unfold peq.
  intros x y H.
  rewrite H; reflexivity.
Qed.
Lemma eq_trans : forall x y z : method, peq x y -> peq y z -> peq x z.
Proof.
  unfold peq.
  intros x y z H0 H1.
  rewrite H0; assumption.
Qed.

Lemma beq_refl : forall x : method, beq x x = true.
Proof.
  intro x. apply equal_1.
  reflexivity.
Qed.
Lemma beq_sym : forall x y : method, beq x y = true <-> beq y x = true.
Proof.
  intros x y. split.
  intro H. apply equal_1 in H.
  rewrite H. apply beq_refl.
  intro H. apply equal_1 in H.
  rewrite H. apply beq_refl.
Qed.
Lemma beq_trans : forall x y z : method,
    beq x y = true -> beq y z = true -> beq x z = true.
Proof.
  intros x y z H H0.
  apply equal_1 in H.
  apply equal_1 in H0.
  rewrite H. rewrite H0.
  apply beq_refl.
Qed.

End Method.

(*  RType  *)

Module RType <: RTYPE.

Definition name := Name.name.

Definition rtype := string.

Definition Object := "Object".
Definition Null := "Null".
Definition Bool := "Bool".
Definition Int := "Int".

Definition field_type := Smap.t rtype.
Definition empty_field_type := Smap.empty rtype.
Definition type_env := Smap.t field_type.
Definition empty_type_env := Smap.empty field_type.
Definition init_type_env :=
    Smap.add "Object" empty_field_type 
    (Smap.add "Bool" empty_field_type
    (Smap.add "Null" empty_field_type empty_type_env)).

Definition beq x y := andb (prefix x y) (prefix y x).
Definition peq (x y : rtype) := x = y.

Definition eq_dec := string_dec.

Definition super_env := Smap.t (list rtype).
Definition init_super_env := Smap.add "Bool" (cons "Object" nil) (Smap.empty (list rtype)).

Definition update_super_env (t : rtype) (super : list rtype) (s : super_env) :=
    Smap.add t super s.

Definition get_super (t : rtype) (s : super_env) := Smap.find t s.

Inductive subtype : rtype -> rtype -> super_env -> Prop :=
    | null_subt   : forall x y s, x = Null -> subtype x y s
    | self_subt   : forall x s, subtype x x s
    | direct_subt : forall x y z s, get_super x s = Some z -> List.In y z ->
                                      subtype x y s
    | trans_subt  : forall x y s, (exists z, subtype x z s /\ subtype z y s) ->
                                      subtype x y s.

Definition update_type_env (t : rtype) (f : field_type) (e : type_env) : type_env :=
    Smap.add t f e.

Definition update_field_type (n : name) (t : rtype) (f : field_type) : field_type :=
    Smap.add n t f.

Definition get_fields (t : rtype) (e : type_env) : option field_type :=
    Smap.find t e.

Lemma equal_1 : forall x y, beq x y = true <-> peq x y.
Proof.
  apply Name.equal_1.
Qed.

Lemma eq_refl : forall x : rtype, peq x x.
Proof.
  unfold peq.
  reflexivity.
Qed.
Lemma eq_sym : forall x y : rtype, peq x y -> peq y x.
Proof.
  unfold peq.
  intros x y H.
  rewrite H; reflexivity.
Qed.
Lemma eq_trans : forall x y z : rtype, peq x y -> peq y z -> peq x z.
Proof.
  unfold peq.
  intros x y z H0 H1.
  rewrite H0; assumption.
Qed.

Lemma beq_refl : forall x : rtype, beq x x = true.
Proof.
  intro x. apply equal_1.
  reflexivity.
Qed.
Lemma beq_sym : forall x y : rtype, beq x y = true <-> beq y x = true.
Proof.
  intros x y. split.
  intro H. apply equal_1 in H.
  rewrite H. apply beq_refl.
  intro H. apply equal_1 in H.
  rewrite H. apply beq_refl.
Qed.
Lemma beq_trans : forall x y z : rtype,
    beq x y = true -> beq y z = true -> beq x z = true.
Proof.
  intros x y z H H0.
  apply equal_1 in H.
  apply equal_1 in H0.
  rewrite H. rewrite H0.
  apply beq_refl.
Qed.

End RType.

Open Scope list_scope.

(*  Reference  *)

Module Ref <: REF.

Definition rtype := RType.rtype.

Definition ref := (nat * rtype)%type.
Definition rfalse := (0, RType.Bool).
Definition rtrue := (1, RType.Bool).
Definition rnull := (2, RType.Null).

Definition alloc := list ref.
Definition init_alloc := rnull :: rtrue :: rfalse :: nil.

Definition alloc_count (a : alloc) := 
    match a with
        | nil => 0
        | (n, _) :: _ => n
    end.

Definition new (t : rtype) (a : alloc) : alloc :=
    match a with
        | nil => (0, t) :: nil
        | (n, _) :: _ => (n+1, t) :: a
    end.

Definition get_new (a : alloc) : ref :=
    match a with
        | nil => rnull (* Impossible *)
        | r :: _ => r
    end.

Definition beq (r1 r2 : ref) :=
    match r1 with (n1, t1) =>
        match r2 with (n2, t2) =>
            andb (beq_nat n1 n2) (RType.beq t1 t2)
        end
    end.

Definition peq (r1 r2 : ref) :=
    match r1 with (n1, t1) =>
        match r2 with (n2, t2) =>
            (eq_nat n1 n2) /\ (RType.peq t1 t2)
        end
    end.

Fixpoint alloc_beq (a1 a2 : alloc) : bool :=
    match a1, a2 with
        | nil, nil => true
        | b1::c1, b2::c2 => andb (Ref.beq b1 b2) (alloc_beq c1 c2)
        | _, _ => false
    end.

Fixpoint alloc_peq (a1 a2 : alloc) : Prop :=
    match a1, a2 with
        | nil, nil => True
        | b1::c1, b2::c2 => (Ref.peq b1 b2) /\ (alloc_peq c1 c2)
        | _, _ => False
    end.

Definition eq_dec : forall x y : ref, {x = y} + {x <> y}.
Proof.
  induction x, y.
  decide equality; (apply eq_nat_dec || apply RType.eq_dec).
Qed.

Definition get_type (r : ref) := snd r.

Definition get_id (r : ref) := fst r.

Lemma equal_1 : forall x y, beq x y = true <-> peq x y.
Proof.
  intros x y.
  induction x, y.
  split. intro H.
  unfold beq in H.
  apply andb_true_iff in H.
  destruct H. unfold peq.
  split. apply beq_nat_true in H.
  apply eq_eq_nat. assumption.
  apply RType.equal_1. assumption.
  unfold peq. unfold beq.
  intro H. destruct H.
  apply andb_true_iff.
  split. apply eq_nat_eq in H.
  rewrite H. apply eq_sym.
  apply beq_nat_refl.
  apply RType.equal_1. assumption.
Qed.

Lemma equal_2 : forall x y, peq x y <-> x = y.
Proof.
  intros x y.
  induction x, y.
  unfold peq.
  split. intro H.
  destruct H.
  apply eq_nat_eq in H.
  rewrite H. rewrite H0.
  reflexivity.
  intro H. inversion H.
  split. apply eq_nat_refl.
  apply RType.eq_refl.
Qed.

Lemma beq_nat_sym : forall n n' : nat, beq_nat n n' = beq_nat n' n.
Proof.
  induction n, n'.
  reflexivity.
  unfold beq_nat; reflexivity.
  unfold beq_nat; reflexivity.
  unfold beq_nat; fold beq_nat. apply IHn.
Qed.

Lemma beq_nat_trans : forall n1 n2 n3 : nat, beq_nat n1 n2 = true ->
    beq_nat n2 n3 = true -> beq_nat n1 n3 = true.
Proof.
  induction n1, n2, n3.
  intros H H0; assumption.
  intros H H0; assumption.
  intros H H0; unfold beq_nat in H; elim H; discriminate H.
  intros H H0; unfold beq_nat in H; elim H; discriminate H.
  intros H H0; unfold beq_nat in H; elim H; discriminate H.
  intros H H0; unfold beq_nat in H; elim H; discriminate H.
  intros H H0; unfold beq_nat in H0; elim H0; discriminate H0.
  intros H H0. apply IHn1 with (n2 := n2).
  assumption. assumption.
Qed.

Lemma beq_refl : forall x : ref, beq x x = true.
Proof.
  intro x.
  unfold beq.
  induction x.
  apply andb_true_iff.
  split.
  apply eq_sym.
  apply beq_nat_refl.
  apply RType.beq_refl.
Qed.
  
Lemma beq_sym : forall x y : ref, beq x y = true <-> beq y x = true.
Proof.
  induction x, y.
  unfold beq.
  assert (beq_nat a n = true \/ beq_nat a n = false).
  case (beq_nat a n).
  left; reflexivity.
  right; reflexivity.
  assert (RType.beq b r = true \/ RType.beq b r = false).
  case (RType.beq b r).
  left; reflexivity.
  right; reflexivity.
  destruct H. rewrite H.
  rewrite beq_nat_sym in H.
  rewrite H. simpl.
  destruct H0. rewrite H0.
  apply RType.beq_sym in H0.
  rewrite H0. reflexivity.
  rewrite H0. split.
  intro H1; inversion H1.
  intro H1. apply RType.beq_sym in H1.
  rewrite H0 in H1; inversion H1.
  rewrite beq_nat_sym with (n := n).
  rewrite H. simpl. reflexivity.
Qed.

Lemma beq_trans : forall x y z : ref, beq x y = true -> beq y z = true -> beq x z = true.
Proof.
  unfold beq.
  intros x y z H H'.
  induction x, y, z.
  apply Bool.andb_true_iff.
  apply Bool.andb_true_iff in H.
  apply Bool.andb_true_iff in H'.
  destruct H. destruct H'.
  split. apply beq_nat_trans with (n2 := n).
  assumption. assumption.
  apply RType.beq_trans with (y := r).
  assumption. assumption.
Qed.

Lemma eq_refl : forall r : ref, peq r r.
Proof.
  intro r.
  induction r.
  unfold peq.
  split.
  apply eq_nat_refl.
  unfold RType.peq.
  reflexivity.
Qed.

Lemma eq_sym : forall r1 r2 : ref, peq r1 r2 -> peq r2 r1.
Proof.
  intros r1 r2 H.
  induction r1.
  induction r2.
  unfold peq.
  unfold peq in H.
  destruct H.
  split.
  apply eq_nat_is_eq.
  apply eq_nat_is_eq in H.
  apply eq_sym.
  assumption.
  unfold RType.peq.
  unfold RType.peq in H0.
  apply eq_sym.
  assumption.
Qed.

Lemma eq_trans : forall r1 r2 r3 : ref, peq r1 r2 -> peq r2 r3 -> peq r1 r3.
Proof.
  intros r1 r2 r3 H H0.
  induction r1.
  induction r2.
  induction r3.
  unfold peq.
  unfold peq in H.
  destruct H.
  unfold peq in H0.
  destruct H0.
  split.
  apply eq_nat_is_eq.
  apply eq_nat_is_eq in H.
  apply eq_nat_is_eq in H0.
  rewrite H.
  assumption.
  unfold RType.peq.
  unfold RType.peq in H1.
  unfold RType.peq in H2.
  rewrite H1.
  assumption.
Qed.

Lemma alloc_eq_refl : forall a : alloc, alloc_peq a a.
Proof.
  intro a.
  induction a.
  unfold alloc_peq.
  auto.
  unfold alloc_peq.
  split.
  apply eq_refl.
  apply IHa.
Qed.

Lemma alloc_eq_sym : forall a1 a2 : alloc, alloc_peq a1 a2 -> alloc_peq a2 a1.
Proof.
  induction a1, a2.
  intro H; assumption.
  intro H; unfold alloc_peq in H; elim H.
  intro H; unfold alloc_peq in H; elim H.
  unfold alloc_peq.
  fold alloc_peq.
  intro H. destruct H.
  split.
  apply eq_sym.
  assumption.
  apply IHa1.
  assumption.
Qed.

Lemma alloc_eq_trans : forall a1 a2 a3 : alloc,
    alloc_peq a1 a2 -> alloc_peq a2 a3 -> alloc_peq a1 a3.
Proof.
  induction a1, a2, a3.
  intros H H0; assumption.
  intros H H0; assumption.
  intros H H0; apply alloc_eq_refl.
  intros H H0; unfold alloc_peq in H; elim H.
  intros H H0; unfold alloc_peq in H; elim H.
  intros H H0; unfold alloc_peq in H; elim H.
  intros H H0; unfold alloc_peq in H0; elim H0.
  unfold alloc_peq.
  fold alloc_peq.
  intros H H0. destruct H. destruct H0.
  split.
  apply eq_trans with (r2 := r).
  assumption. assumption.
  apply IHa1 with (a2 := a2).
  assumption. assumption.
Qed.

End Ref.

(*  ref_map  *)

Module ref_DT <: UsualDecidableType.
Definition t := Ref.ref.
Definition eq := @eq t. (*Ref.peq.*)
Definition eq_refl := @eq_refl t.
Definition eq_sym := @eq_sym t.
Definition eq_trans := @eq_trans t.
Definition eq_dec := Ref.eq_dec.
End ref_DT.

Module Rmap := FMapWeakList.Make ref_DT.

Lemma rmap_refl_1 : forall (t : Type) (eq : t -> t -> bool) e1, 
    (forall t1, eq t1 t1 = true) -> Rmap.Equivb eq e1 e1.
Proof.
  intros t eq e1 H.
  unfold Smap.Equivb.
  unfold Smap.Raw.Equivb.
  split. intro k. split.
  intro; assumption.
  intro; assumption.
  intros k e e' H0 H1.
  apply Rmap.find_1 in H0.
  apply Rmap.find_1 in H1.
  rewrite H1 in H0. inversion H0.
  apply H.
Qed.
Lemma rmap_sym_1 : forall (t : Type) (eq : t -> t -> bool) e1 e2, 
    (forall t1 t2, eq t1 t2 = true -> eq t2 t1 = true)
        -> Rmap.Equivb eq e1 e2 -> Rmap.Equivb eq e2 e1.
Proof.
  intros t eq e1 e2 H H0.
  unfold Smap.Equivb.
  unfold Smap.Raw.Equivb.
  unfold Smap.Equivb in H0.
  unfold Smap.Raw.Equivb in H0.
  destruct H0.
  split. intro k. split.
  intro; apply H0; assumption.
  intro; apply H0; assumption.
  intros k e e' H2 H3.
  assert (eq e' e = true).
  apply H1 with (k := k).
  assumption. assumption.
  apply H; assumption.
Qed.
Lemma rmap_trans_1 : forall (t : Type) (eq : t -> t -> bool) e1 e2 e3, 
    (forall t1 t2 t3, eq t1 t2 = true -> eq t2 t3 = true -> eq t1 t3 = true)
        -> Rmap.Equivb eq e1 e2 -> Rmap.Equivb eq e2 e3 -> Rmap.Equivb eq e1 e3.
Proof.
  intros t eq e1 e2 e3 H H0 H1.
  unfold Smap.Equivb.
  unfold Smap.Raw.Equivb.
  unfold Smap.Equivb in H0.
  unfold Smap.Raw.Equivb in H0.
  unfold Smap.Equivb in H1.
  unfold Smap.Raw.Equivb in H1.
  destruct H0. destruct H1.
  split. intro k. split.
  intro; apply H1; apply H0; assumption.
  intro; apply H0; apply H1; assumption.
  intros k e e' H4 H5.
  assert (Rmap.Raw.PX.In k (Rmap.this e2)).
  apply H1. exists e'. assumption.
  destruct H6. assert (eq e x = true).
  apply H2 with (k := k).
  assumption. assumption.
  assert (eq x e' = true).
  apply H3 with (k := k).
  assumption. assumption.
  apply H with (t2 := x).
  assumption. assumption.
Qed.

Lemma rmap_refl_2 : forall (t : Type) (eq : t -> t -> bool) e1, 
    (forall t1, eq t1 t1 = true) -> Rmap.equal eq e1 e1 = true.
Proof.
  intros t eq e1 H.
  apply Rmap.equal_1.
  apply rmap_refl_1.
  assumption.
Qed.
Lemma rmap_sym_2 : forall (t : Type) (eq : t -> t -> bool) e1 e2, 
    (forall t1 t2, eq t1 t2 = true -> eq t2 t1 = true)
        -> Rmap.equal eq e1 e2 = true -> Rmap.equal eq e2 e1 = true.
Proof.
  intros t eq e1 e2 H H0.
  apply Rmap.equal_1.
  apply Rmap.equal_2 in H0.
  apply rmap_sym_1.
  assumption. assumption.
Qed.
Lemma rmap_trans_2 : forall (t : Type) (eq : t -> t -> bool) e1 e2 e3, 
  (forall t1 t2 t3, eq t1 t2 = true -> eq t2 t3 = true -> eq t1 t3 = true)
    -> Rmap.equal eq e1 e2 = true -> Rmap.equal eq e2 e3 = true -> Rmap.equal eq e1 e3 = true.
Proof.
  intros t eq e1 e2 e3 H H0 H1.
  apply Rmap.equal_1.
  apply Rmap.equal_2 in H0.
  apply Rmap.equal_2 in H1.
  apply rmap_trans_1 with (e2 := e2).
  assumption. assumption. assumption.
Qed.

Lemma rmap_equal: forall (t : Type) (eq : t -> t -> bool),
    (forall e1 e2, eq e1 e2 = true <-> e1 = e2) -> 
    (forall m1 m2, Rmap.equal eq m1 m2 = true <-> m1 = m2).
Proof.
  intros t eq H m1 m2.
Admitted.
Lemma rmap_inject: forall (t : Type) k (e1 e2 : t) m,
    Rmap.MapsTo k e1 m -> Rmap.MapsTo k e2 m -> e1 = e2.
Proof.
  intros t k e1 e2 m H H0.
  apply Rmap.find_1 in H.
  apply Rmap.find_1 in H0.
  rewrite H in H0. inversion H0.
  reflexivity.
Qed.
Lemma rmap_add: forall (t : Type) k (e1 e2 : t) m,
    Rmap.MapsTo k e1 (Rmap.add k e2 m) -> e1 = e2.
Proof.
  intros t k e1 e2 m H.
  assert (Rmap.MapsTo k e2 (Rmap.add k e2 m)).
  apply Rmap.add_1. reflexivity.
  apply rmap_inject with (k := k) (m := Rmap.add k e2 m).
  assumption. assumption.
Qed.

Close Scope list_scope.
Close Scope string_scope.

(*  Lemmas  *)

Lemma lr_trans : forall a b c, (a <-> b) -> (b <-> c) -> (a <-> c).
Proof. tauto. Qed.
Lemma notF_T : ~ False <-> True.
Proof. tauto. Qed.
Lemma conjl_T : forall P, True /\ P <-> P.
Proof. tauto. Qed.
Lemma conjr_T : forall P, P /\ True <-> P.
Proof. tauto. Qed.
Lemma conjl_F : forall P, False /\ P <-> False.
Proof. tauto. Qed.
Lemma conjr_F : forall P, P /\ False <-> False.
Proof. tauto. Qed.
Lemma disjl_F : forall P, False \/ P <-> P.
Proof. tauto. Qed.
Lemma disjr_F : forall P, P \/ False <-> P.
Proof. tauto. Qed.
Lemma conj_disj : forall P Q R, P /\ (Q \/ R) <-> P /\ Q \/ P /\ R.
Proof. tauto. Qed.
Lemma disj_asso : forall P Q R, (P \/ Q) \/ R <-> P \/ Q \/ R.
Proof. tauto. Qed.
Lemma disj_abs : forall P Q, P \/ P \/ Q <-> P \/ Q.
Proof. tauto. Qed.
Lemma disj_abs2 : forall P Q R, P \/ Q \/ P \/ R <-> P \/ Q \/ R.
Proof. tauto. Qed.
Lemma disj_abs3 : forall P Q R S, P \/ Q \/ R \/ P \/ S <-> P \/ Q \/ R \/ S.
Proof. tauto. Qed.
Lemma neq_eq : forall m s t : Method.method, m <> s /\ m = t <-> t <> s /\ m = t.
Proof. split; intros [H H0]; (split; [subst|]; assumption). Qed.

(*  Ltacs  *)

Ltac inductS i := let x := fresh "x" in let H := fresh "H" in
    assert ((exists Fv, i = Some Fv) \/ i = None) as H;
    [case i; [intro x; left; exists x; reflexivity | right; reflexivity] |
     destruct H as [H|H]; [destruct H as [x H]|]; try rewrite H].
Ltac propSimp H := repeat (rewrite neq_eq in H || rewrite notF_T in H ||
    rewrite conjl_T in H || rewrite conjr_T in H || rewrite conjl_F in H ||
    rewrite conjr_F in H || rewrite disjl_F in H || rewrite disjr_F in H ||
    rewrite conj_disj in H || rewrite disj_asso in H || rewrite disj_abs in H ||
    rewrite disj_abs2 in H || rewrite disj_abs3 in H).