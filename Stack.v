Require Export Util.

(*-----  Abstract Data Type  -----*)

(*  DType Type  *)

Module Type DTYPE.

Parameter name : Set.
Parameter rtype : Set.
Parameter dtype : Type.
Parameter init_dtype : dtype.

Parameter beq : dtype -> dtype -> bool.
Parameter peq : dtype -> dtype -> Prop.
Parameter get_dtype : name -> dtype -> option rtype.
Parameter update_dtype : name -> rtype -> dtype -> dtype.

Axiom equal_1 : forall x y: dtype, beq x y = true <-> peq x y.

Axiom beq_refl : forall x : dtype, beq x x = true.
Axiom beq_sym : forall x y : dtype, beq x y = true <-> beq y x = true.
Axiom beq_trans : forall x y z : dtype, beq x y = true -> beq y z = true -> beq x z = true.

Axiom eq_refl : forall x : dtype, peq x x.
Axiom eq_sym : forall x y : dtype, peq x y -> peq y x.
Axiom eq_trans : forall x y z : dtype, peq x y -> peq y z -> peq x z.

End DTYPE.

(*  Stack Type  *)

Module Type STACK.

Parameter name : Set.
Parameter ref : Set.
Parameter rtype : Set.
Parameter super_env : Type.
Parameter dtype : Type.

Parameter stack : Type.
Parameter init_stack : stack.

Parameter pin : name -> ref -> stack -> Prop.
Parameter beq : stack -> stack -> bool.
Parameter peq : stack -> stack -> Prop.
Parameter get : name -> stack -> option ref.
Parameter update : name -> ref -> stack -> stack.
Parameter update_null : name -> stack -> stack.

Parameter well_formed : super_env -> stack -> dtype -> Prop.

Axiom beq_refl : forall x : stack, beq x x = true.
Axiom beq_sym : forall x y : stack, beq x y = true <-> beq y x = true.
Axiom beq_trans : forall x y z : stack, beq x y = true -> beq y z = true -> beq x z = true.

Axiom eq_refl : forall x : stack, peq x x.
Axiom eq_sym : forall x y : stack, peq x y -> peq y x.
Axiom eq_trans : forall x y z : stack, peq x y -> peq y z -> peq x z.

Axiom in_update_1 : forall n r s, pin n r (update n r s).
Axiom in_update_2 : forall n1 n2 r1 r2 s,
    n1 <> n2 -> pin n1 r1 s -> pin n1 r1 (update n2 r2 s).
Axiom in_update_3 : forall n1 n2 r1 r2 s,
    n1 <> n2 -> pin n1 r1 (update n2 r2 s) -> pin n1 r1 s.
Axiom in_get : forall n r s, pin n r s <-> get n s = Some r.
Axiom not_in_get : forall n s, (forall r, ~ pin n r s) <-> get n s = None.

End STACK.


(*-----  Data  -----*)

Open Scope string_scope.

(*  DType  *)

Module DType <: DTYPE.

Definition name := Name.name.
Definition rtype := RType.rtype.
Definition dtype := Smap.t rtype.
Definition empty_dtype := Smap.empty rtype.
Definition init_dtype :=
    Smap.add "this" "Object"
    (Smap.add "res" "Object"
    (Smap.add "true" "Bool" 
    (Smap.add "false" "Bool"
    (Smap.add "null" "Null" empty_dtype)))).

Definition beq (d1 d2 : dtype) : bool :=
    Smap.equal RType.beq d1 d2.

Definition peq (d1 d2 : dtype) : Prop :=
    Smap.Equivb RType.beq d1 d2.

Definition get_dtype (n : name) (d : dtype) : option rtype :=
    Smap.find n d.

Definition update_dtype (n : name) (t : rtype) (d : dtype) : dtype :=
    Smap.add n t d.

Lemma equal_1 : forall x y: dtype, beq x y = true <-> peq x y.
Proof.
  unfold beq. unfold peq.
  intros x y. split.
  apply Smap.equal_2.
  apply Smap.equal_1.
Qed.

Lemma beq_refl : forall x : dtype, beq x x = true.
Proof.
  unfold beq. intro.
  apply smap_refl_2. apply RType.beq_refl.
Qed.
Lemma beq_sym : forall x y : dtype, beq x y = true <-> beq y x = true.
Proof.
  unfold beq. intros. split.
  apply smap_sym_2. apply RType.beq_sym.
  apply smap_sym_2. apply RType.beq_sym.
Qed.
Lemma beq_trans : forall x y z : dtype, beq x y = true -> beq y z = true -> beq x z = true.
Proof.
  unfold beq. intros x y z.
  apply smap_trans_2. apply RType.beq_trans.
Qed.

Lemma eq_refl : forall x : dtype, peq x x.
Proof.
  intro x. apply equal_1.
  apply beq_refl.
Qed.
Lemma eq_sym : forall x y : dtype, peq x y -> peq y x.
Proof.
  intros x y H. apply equal_1.
  apply equal_1 in H.
  apply beq_sym. assumption.
Qed.
Lemma eq_trans : forall x y z : dtype, peq x y -> peq y z -> peq x z.
Proof.
  intros x y z H H0.
  apply equal_1.
  apply equal_1 in H.
  apply equal_1 in H0.
  apply beq_trans with (y := y).
  assumption. assumption.
Qed.

End DType.

(*  Stack  *)

Module Stack <: STACK.

Definition name := Name.name.
Definition ref := Ref.ref.
Definition rtype := RType.rtype.
Definition super_env := RType.super_env.
Definition dtype := DType.dtype.

Definition stack := Smap.t ref.
Definition empty_stack := Smap.empty ref.
Definition init_stack :=
    Smap.add "this" Ref.rnull
    (Smap.add "res" Ref.rnull
    (Smap.add "true" Ref.rtrue 
    (Smap.add "false" Ref.rfalse
    (Smap.add "null" Ref.rnull empty_stack)))).

Definition pin (n : name) (r : ref) (s : stack) : Prop :=
    Smap.MapsTo n r s.

Definition beq (s1 s2 : stack) : bool :=
    Smap.equal Ref.beq s1 s2.

Definition peq (s1 s2 : stack) : Prop :=
    forall n r, pin n r s1 <-> pin n r s2.

Definition get (n : name) (s : stack) : option ref :=
    Smap.find n s.

Definition update (n : name) (r : ref) (s : stack) : stack :=
    Smap.add n r s.

Definition update_null (n : name) (s : stack) : stack :=
    Smap.add n Ref.rnull s.

Definition check_type (se : super_env) (d : dtype) (n : name) (r : ref) (p : Prop) : Prop :=
    match Smap.find n d with
        | None => False
        | Some t => RType.subtype (Ref.get_type r) t se /\ p
    end.
Definition well_formed (se : super_env) (s : stack) (d : dtype) : Prop :=
    Smap.fold (check_type se d) s True.

Lemma equal_1 : forall s1 s2 : stack, peq s1 s2 -> beq s1 s2 = true.
Proof.
  unfold peq. unfold beq.
  intros s1 s2 H. apply Smap.equal_1.
  unfold Smap.Equivb.
  unfold Smap.Raw.Equivb.
  split. intro k. split.
  unfold Smap.Raw.PX.In.
  intro H0. destruct H0.
  apply H in H0. exists x.
  assumption.
  unfold Smap.Raw.PX.In.
  intro H0. destruct H0.
  apply H in H0. exists x.
  assumption.
  intros k e e' H0 H1.
  apply Ref.equal_1.
  apply Ref.equal_2.
  apply smap_inject with (k := k) (m := s2).
  apply H in H0. assumption. assumption.
Qed.
Lemma equal_2 : forall s1 s2 : stack, beq s1 s2 = true -> peq s1 s2.
Proof.
  unfold peq. unfold beq.
  intros s1 s2 H n r.
  apply Smap.equal_2 in H.
  unfold Smap.Equivb in H.
  unfold Smap.Raw.Equivb in H.
  destruct H. unfold Smap.Raw.PX.In in H.
  destruct H with (k := n).
  split. unfold pin. intro H3.
  assert (exists e, Smap.Raw.PX.MapsTo n e (Smap.this s1)).
  exists r; assumption.
  apply H1 in H4.
  clear H1; clear H2.
  destruct H4.
  assert (Ref.beq r x = true).
  apply H0 with (k := n).
  assumption. assumption.
  apply Ref.equal_1 in H2.
  apply Ref.equal_2 in H2.
  rewrite H2. assumption.
  unfold pin. intro H3.
  assert (exists e, Smap.Raw.PX.MapsTo n e (Smap.this s2)).
  exists r; assumption.
  apply H2 in H4.
  clear H1; clear H2.
  destruct H4.
  assert (Ref.beq x r = true).
  apply H0 with (k := n).
  assumption. assumption.
  apply Ref.equal_1 in H2.
  apply Ref.equal_2 in H2.
  rewrite <- H2. assumption.
Qed.
Axiom equal_3 : forall s1 s2 : stack, s1 = s2 <-> peq s1 s2.

Lemma beq_refl : forall x : stack, beq x x = true.
Proof.
  unfold beq. intro.
  apply smap_refl_2. apply Ref.beq_refl.
Qed.
Lemma beq_sym : forall x y : stack, beq x y = true <-> beq y x = true.
Proof.
  unfold beq. intros. split.
  apply smap_sym_2. apply Ref.beq_sym.
  apply smap_sym_2. apply Ref.beq_sym.
Qed.
Lemma beq_trans : forall x y z : stack, beq x y = true -> beq y z = true -> beq x z = true.
Proof.
  unfold beq. intros x y z.
  apply smap_trans_2. apply Ref.beq_trans.
Qed.

Lemma eq_refl : forall x : stack, peq x x.
Proof.
  unfold peq. intros; split.
  intro; assumption.
  intro; assumption.
Qed.
Lemma eq_sym : forall x y : stack, peq x y -> peq y x.
Proof.
  unfold peq. intros; split.
  apply H. apply H.
Qed.
Lemma eq_trans : forall x y z : stack, peq x y -> peq y z -> peq x z.
Proof.
  unfold peq. intros; split.
  intro; apply H0; apply H; assumption.
  intro; apply H; apply H0; assumption.
Qed.

Lemma in_update_1 : forall n r s, pin n r (update n r s).
Proof.
  intros n r s. unfold update.
  apply Smap.add_1; reflexivity.
Qed.

Lemma in_update_2 : forall n1 n2 r1 r2 s,
    n1 <> n2 -> pin n1 r1 s -> pin n1 r1 (update n2 r2 s).
Proof.
  intros n1 n2 r1 r2 s H H0.
  unfold update. unfold pin in H0.
  apply Smap.add_2. auto.
  assumption.
Qed.

Lemma in_update_3 : forall n1 n2 r1 r2 s,
    n1 <> n2 -> pin n1 r1 (update n2 r2 s) -> pin n1 r1 s.
Proof.
  intros n1 n2 r1 r2 s H H0.
  unfold update in H0. unfold pin in H0.
  apply Smap.add_3 with (x := n2) (e' := r2). auto.
  assumption.
Qed.

Lemma in_get : forall n r s, pin n r s <-> get n s = Some r.
Proof.
  intros n r s.
  split. intro H.
  unfold pin in H.
  apply Smap.find_1 in H.
  unfold get. assumption.
  intro H. unfold get in H.
  apply Smap.find_2 in H.
  assumption.
Qed.

Lemma not_in_get : forall n s, (forall r, ~ pin n r s) <-> get n s = None.
Proof.
  intros n s. split. intro H.
  unfold pin in H. unfold get.
  inductS (Smap.find n s).
  apply Smap.find_2 in H0.
  elim H with (r := x). assumption. reflexivity.
  intros H r H0. unfold get in H.
  apply Smap.find_1 in H0. rewrite H0 in H.
  inversion H.
Qed.

End Stack.

Close Scope string_scope.
