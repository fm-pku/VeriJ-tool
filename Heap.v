Require Export Util.

(*-----  Abstract Data Type  -----*)

(*  Heap Type  *)

Module Type HEAP.

Parameter name : Set.
Parameter rtype : Set.
Parameter ref : Set.
Parameter alloc : Set.
Parameter super_env : Type.
Parameter field_type : Type.
Parameter type_env : Type.

Parameter heap : Type.
Parameter empty_heap : heap.

Parameter get : ref -> name -> heap -> option ref.
Parameter update : ref -> name -> ref -> heap -> heap.
Parameter new : ref -> field_type -> heap -> heap.
Parameter remove : ref -> name -> heap -> heap.
Parameter pin : ref -> name -> ref -> heap -> Prop.

Parameter pdisjoint : heap -> heap -> Prop.
Parameter union : heap -> heap -> heap. (* the two heaps should be disjoint *)
Parameter beq : heap -> heap -> bool.
Parameter eq : heap -> heap -> Prop.
Parameter subheap : heap -> heap -> Prop.

Parameter well_formed : super_env -> type_env -> heap -> Prop.

Infix "|=|" := eq (at level 70) : heap_scope.
Infix "|+|" := union (at level 60, right associativity) : heap_scope.
Infix "|*|" := pdisjoint (at level 50) : heap_scope.
Infix "|<|" := subheap (at level 70) : heap_scope.
Notation "{}" := empty_heap : heap_scope.

Open Scope heap_scope.

Axiom beq_refl : forall x : heap, beq x x = true.
Axiom beq_sym : forall x y : heap, beq x y = true <-> beq y x = true.
Axiom beq_trans : forall x y z : heap, beq x y = true -> beq y z = true -> beq x z = true.

Axiom eq_refl : forall x : heap, x |=| x.
Axiom eq_sym : forall x y : heap, x |=| y -> y |=| x.
Axiom eq_trans : forall x y z : heap, x |=| y -> y |=| z -> x |=| z.

Axiom subheap_refl : forall h : heap, h |<| h.
Axiom subheap_asym : forall h1 h2 : heap, h1 |<| h2 -> h2 |<| h1 -> h1 |=| h2.
Axiom subheap_trans : forall h1 h2 h3 : heap, h1 |<| h2 -> h2 |<| h3 -> h1 |<| h3.
Axiom subheap_union : forall h1 h2 : heap, h1 |<| h2 |+| h1.

Axiom update_update : forall r1 n r2 r3 h,
    update r1 n r2 h = update r1 n r2 (update r1 n r3 h).

Axiom in_update_1 : forall r1 n r2 h, pin r1 n r2 (update r1 n r2 h).
Axiom in_update_2 : forall r1 r2 r3 r4 n1 n2 h,
    (r1 <> r2 \/ n1 <> n2) -> pin r1 n1 r3 h -> pin r1 n1 r3 (update r2 n2 r4 h).
Axiom in_update_3 : forall r1 r2 r3 r4 n1 n2 h,
    (r1 <> r2 \/ n1 <> n2) -> pin r1 n1 r3 (update r2 n2 r4 h) -> pin r1 n1 r3 h.
Axiom in_get : forall r1 r2 n h, pin r1 n r2 h <-> get r1 n h = Some r2.
Axiom not_in_get : forall r1 n h, (forall r2, ~ pin r1 n r2 h) <-> get r1 n h = None.

Axiom in_union_1 : forall r1 n r2 h1 h2,
    pin r1 n r2 (h1 |+| h2) <-> pin r1 n r2 h1 \/ pin r1 n r2 h2.
Axiom in_union_2 : forall r1 n r2 h1 h2,
    ~ pin r1 n r2 h1 -> (pin r1 n r2 h2 <-> pin r1 n r2 (h1 |+| h2)).
Axiom not_in_empty_1 : forall r1 n r2, ~ pin r1 n r2 {}.
Axiom in_equal : forall (r r1 r2 : ref) (n : name) (h : heap),
    pin r n r1 h -> pin r n r2 h -> r1 = r2.

Axiom pdisjoint_empty : forall x : heap, x |*| {}.
Axiom pdisjoint_sym : forall x y : heap, x |*| y -> y |*| x.
Axiom pdisjoint_union : forall h1 h2 h3 : heap,
    h1 |*| (h2 |+| h3) <-> h1 |*| h2 /\ h1 |*| h3.
Axiom pdisjoint_self : forall h : heap, h |*| h -> h |=| {}.

Axiom equal_1 : forall h1 h2 : heap, h1 |=| h2 -> beq h1 h2 = true.
Axiom equal_2 : forall h1 h2 : heap, beq h1 h2 = true -> h1 |=| h2.
Axiom equal_3 : forall h1 h2 : heap, h1 = h2 <-> h1 |=| h2.
Axiom union_emp : forall h : heap, {} |+| h |=| h.
Axiom union_comm : forall h1 h2 : heap, h1 |+| h2 |=| h2 |+| h1.
Axiom union_asso : forall h1 h2 h3 : heap,
    h1 |+| h2 |+| h3 |=| (h1 |+| h2) |+| h3.

Axiom not_in_remove_1 : forall r1 n r2 h, ~ pin r1 n r2 (remove r1 n h).
Axiom in_remove_2 : forall r1 r2 r3 n1 n2 h,
    (r1 <> r2 \/ n1 <> n2) -> pin r1 n1 r3 h -> pin r1 n1 r3 (remove r2 n2 h).
Axiom in_remove_3 : forall r1 r2 r3 n1 n2 h,
    pin r1 n1 r3 (remove r2 n2 h) -> pin r1 n1 r3 h.
Axiom disjoint_remove : forall r1 n r2 h,
    remove r1 n h |*| update r1 n r2 {}.

Close Scope heap_scope.

End HEAP.


(*-----  Data  -----*)

(*  Heap  *)

Module Heap <: HEAP.

Definition name := Name.name.
Definition rtype := RType.rtype.
Definition ref := Ref.ref.
Definition alloc := Ref.alloc.
Definition super_env := RType.super_env.
Definition field_type := RType.field_type.
Definition type_env := RType.type_env.

Definition obj := Smap.t ref.
Definition heap := Rmap.t obj.
Definition empty_heap := Rmap.empty obj.

Definition get (r : ref) (n : name) (h : heap) : option ref :=
    match Rmap.find r h with
        | None => None
        | Some o => Smap.find n o
    end.

Definition update (r : ref) (n : name) (r1 : ref) (h : heap) : heap :=
    match Rmap.find r h with
        | None => Rmap.add r (Smap.add n r1 (Smap.empty ref)) h
        | Some o => Rmap.add r (Smap.add n r1 o) h
    end.

Definition remove (r : ref) (n : name) (h : heap) : heap :=
    match Rmap.find r h with
        | None => h
        | Some o => Rmap.add r (Smap.remove n o) h
    end.

Definition pin (r : ref) (n : name) (r1 : ref) (h : heap) : Prop :=
    exists o, Rmap.MapsTo r o h /\ Smap.MapsTo n r1 o.

Definition new (r : ref) (f : field_type) (h : heap) : heap :=
    Rmap.add r (Smap.map (fun _ => Ref.rnull) f) h.

Definition pdisjoint (h1 h2 : heap) : Prop :=
    forall (r1 r2 r3 : ref) (n : name), ~ (pin r1 n r2 h1 /\ pin r1 n r3 h2).

Definition union1 (r : ref) (o : obj) (h : heap) : heap :=
    match Rmap.find r h with
        | None => Rmap.add r o h
        | Some o1 => Rmap.add r (Smap.fold (Smap.add (elt:=ref)) o1 o) h
    end.
Definition union (h1 h2 : heap) : heap :=
    Rmap.fold union1 h1 h2.

Definition beq (h1 h2 : heap) : bool :=
    Rmap.equal (Smap.equal Ref.beq) h1 h2.

(* 如果 h1 与 h2 相差一个空对象，eq h1 h2 仍成立 *)
Definition eq (h1 h2 : heap) : Prop :=
    forall (r1 r2 : ref) (n : name), pin r1 n r2 h1 <-> pin r1 n r2 h2.

Definition subheap (h1 h2 : heap) : Prop :=
    forall (r1 r2 : ref) (n : name), pin r1 n r2 h1 -> pin r1 n r2 h2.

Bind Scope heap_scope with heap.
Delimit Scope heap_scope with heap.

Infix "|=|" := eq (at level 70) : heap_scope.
Infix "|+|" := union (at level 60, right associativity) : heap_scope.
Infix "|*|" := pdisjoint (at level 50) : heap_scope.
Infix "|<|" := subheap (at level 70) : heap_scope.
Notation "{}" := empty_heap : heap_scope.

Open Scope heap_scope.

Definition check_attr (s : super_env) (f : field_type) (n : name) (r : ref) (p : Prop) : Prop :=
    match Smap.find n f with
        | None => False
        | Some t => 
            (RType.subtype (Ref.get_type r) t s) /\ p
    end.
Definition check_obj (s : super_env) (te : type_env) (r : ref) (o : obj) (p : Prop) : Prop :=
    match Smap.find (Ref.get_type r) te with
        | None => False
        | Some f => 
            (o <> Smap.empty ref \/ f = Smap.empty rtype) /\
            (Smap.fold (check_attr s f) o p)
    end.
Definition well_formed (s : super_env) (te : type_env) (h : heap) : Prop :=
    Rmap.fold (check_obj s te) h True.

Axiom equal_1 : forall h1 h2 : heap, h1 |=| h2 -> beq h1 h2 = true.
Lemma equal_2 : forall h1 h2 : heap, beq h1 h2 = true -> h1 |=| h2.
Proof.
  unfold beq; unfold eq. intros h1 h2 H r1 r2 n.
  apply Rmap.equal_2 in H.
  unfold Rmap.Equivb in H.
  unfold Rmap.Raw.Equivb in H.
  assert (forall r1 r2, Ref.beq r1 r2 = true <-> r1 = r2).
  intros r0 r3. apply lr_trans with (b := Ref.peq r0 r3).
  apply Ref.equal_1. apply Ref.equal_2.
  destruct H. unfold pin. split. intro H2.
  do 2 destruct H2. exists x. split.
  assert (Rmap.Raw.PX.In r1 (Rmap.this h1)).
  unfold Rmap.Raw.PX.In. exists x; apply H2.
  apply H in H4. unfold Rmap.Raw.PX.In in H4.
  destruct H4. apply H1 with (e' := x0) in H2.
  apply smap_equal with (m1 := x) (m2 := x0) in H0.
  apply H0 in H2. rewrite H2. assumption.
  assumption. assumption. intro H2.
  do 2 destruct H2. exists x. split.
  assert (Rmap.Raw.PX.In r1 (Rmap.this h2)).
  unfold Rmap.Raw.PX.In. exists x; apply H2.
  apply H in H4. unfold Rmap.Raw.PX.In in H4.
  destruct H4. assert (x0 = x).
  apply H1 with (e' := x) in H4.
  apply smap_equal with (m1 := x0) (m2 := x) in H0.
  apply H0; assumption. assumption.
  rewrite <- H5. assumption. assumption.
Qed.
Lemma equal_3 : forall h1 h2 : heap, h1 = h2 <-> h1 |=| h2.
Proof.
  unfold eq. intros h1 h2. split.
  intros H r1 r2 n. apply equal_2.
  apply rmap_equal. intros e1 e2.
  apply smap_equal. intros e0 e3.
  apply lr_trans with (b := Ref.peq e0 e3).
  apply Ref.equal_1. apply Ref.equal_2. assumption.
  intro H. apply equal_1 in H. unfold beq in H.
  assert (forall r1 r2, Ref.beq r1 r2 = true <-> r1 = r2).
  intros r1 r2. apply lr_trans with (b := Ref.peq r1 r2).
  apply Ref.equal_1. apply Ref.equal_2.
  assert (forall o1 o2, (Smap.equal Ref.beq) o1 o2 = true <-> o1 = o2).
  apply smap_equal. assumption.
  apply rmap_equal with (m1 := h1) (m2 := h2) in H1.
  apply H1; assumption.
Qed.

Lemma beq_refl : forall x : heap, beq x x = true.
Proof.
  intro x. unfold beq.
  apply rmap_refl_2. intro.
  apply smap_refl_2. intro.
  apply Ref.beq_refl.
Qed.
Lemma beq_sym : forall x y : heap, beq x y = true <-> beq y x = true.
Proof.
  intros x y. unfold beq. split.
  apply rmap_sym_2. intros.
  apply smap_sym_2. intros.
  apply Ref.beq_sym.
  assumption. assumption.
  apply rmap_sym_2. intros.
  apply smap_sym_2. intros.
  apply Ref.beq_sym.
  assumption. assumption.
Qed.
Lemma beq_trans : forall x y z : heap, beq x y = true -> beq y z = true -> beq x z = true.
Proof.
  unfold beq. intros x y z.
  apply rmap_trans_2 with (e2 := y). intros.
  apply smap_trans_2 with (e2 := t2). intros.
  apply Ref.beq_trans with (y := t4).
  assumption. assumption.
  assumption. assumption.
Qed.

Lemma eq_refl : forall x : heap, x |=| x.
Proof.
  unfold eq. intros. split.
  intro; assumption.
  intro; assumption.
Qed.

Lemma eq_sym : forall x y : heap, x |=| y -> y |=| x.
Proof.
  unfold eq. intros; split.
  apply H. apply H.
Qed.

Lemma eq_trans : forall x y z : heap, x |=| y -> y |=| z -> x |=| z.
Proof.
  unfold eq. intros. split.
  intro; apply H0; apply H; assumption.
  intro; apply H; apply H0; assumption.
Qed.

Lemma subheap_refl : forall h : heap, h |<| h.
Proof.
  unfold subheap.
  intros h r1 r2 n H.
  assumption.
Qed.

Lemma subheap_asym : forall h1 h2 : heap, h1 |<| h2 -> h2 |<| h1 -> h1 |=| h2.
Proof.
  unfold subheap. unfold eq.
  intros h1 h2 H H0 r1 r2 n.
  split. apply H. apply H0.
Qed.

Lemma subheap_trans : forall h1 h2 h3 : heap, h1 |<| h2 -> h2 |<| h3 -> h1 |<| h3.
Proof.
  unfold subheap.
  intros h1 h2 h3 H H0 r1 r2 n H1.
  apply H0. apply H. assumption.
Qed.

Lemma in_update_1 : forall r1 n r2 h, pin r1 n r2 (update r1 n r2 h).
Proof.
  intros r1 n r2 h. unfold update.
  case (Rmap.find r1 h).
  intro o. unfold pin.
  exists (Smap.add n r2 o). split.
  apply Rmap.add_1; reflexivity.
  apply Smap.add_1; reflexivity.
  unfold pin.
  exists (Smap.add n r2 (Smap.empty ref)).
  split.
  apply Rmap.add_1; reflexivity.
  apply Smap.add_1; reflexivity.
Qed.

Lemma in_update_2 : forall r1 r2 r3 r4 n1 n2 h,
    (r1 <> r2 \/ n1 <> n2) -> pin r1 n1 r3 h -> pin r1 n1 r3 (update r2 n2 r4 h).
Proof.
  intros r1 r2 r3 r4 n1 n2 h H H0.
  unfold update. unfold pin in H0.
  do 2 destruct H0.
  case Ref.eq_dec with (x := r1) (y := r2).
  intro H2.
  destruct H. elim H; assumption.
  rewrite <- H2. apply Rmap.find_1 in H0.
  rewrite H0. exists (Smap.add n2 r4 x).
  split. apply Rmap.add_1. reflexivity.
  apply Smap.add_2. auto.
  assumption. intro H2.
  unfold pin. exists x.
  split. case (Rmap.find r2 h).
  intro o. apply Rmap.add_2. auto.
  assumption. apply Rmap.add_2. auto.
  assumption. assumption.
Qed.

Lemma in_update_3 : forall r1 r2 r3 r4 n1 n2 h,
    (r1 <> r2 \/ n1 <> n2) -> pin r1 n1 r3 (update r2 n2 r4 h) -> pin r1 n1 r3 h.
Proof.
  intros r1 r2 r3 r4 n1 n2 h H H0.
  unfold update in H0; unfold pin in H0.
  do 2 destruct H0.
  case Ref.eq_dec with (x := r1) (y := r2).
  intro H2. destruct H. elim H; assumption.
  rewrite <- H2 in H0.
  inductS (Rmap.find r1 h); rewrite H3 in H0. unfold pin.
  assert (x = Smap.add n2 r4 x0).
  apply rmap_add in H0. assumption.
  exists x0. split.
  apply Rmap.find_2 in H3. assumption.
  rewrite H4 in H1.
  apply Smap.add_3 in H1. assumption. auto.
  assert (x = Smap.add n2 r4 (Smap.empty ref)).
  assert (Rmap.MapsTo r1 (Smap.add n2 r4 (Smap.empty ref))
    (Rmap.add r1 (Smap.add n2 r4 (Smap.empty ref)) h)).
  apply Rmap.add_1. reflexivity.
  apply rmap_inject with (k := r1)
    (m := (Rmap.add r1 (Smap.add n2 r4 (Smap.empty ref)) h));
  assumption. rewrite H4 in H1.
  apply Smap.add_3 in H1.
  apply Smap.empty_1 in H1. elim H1. auto.
  intro H2. inductS (Rmap.find r2 h); rewrite H3 in H0;
  apply Rmap.add_3 in H0; unfold pin;
  try (exists x; split; assumption); auto.
Qed.

Lemma in_get : forall r1 r2 n h, pin r1 n r2 h <-> get r1 n h = Some r2.
Proof.
  intros r1 r2 n h.
  split. intro H.
  unfold pin in H.
  do 2 destruct H.
  unfold get.
  apply Rmap.find_1 in H.
  rewrite H.
  apply Smap.find_1 in H0.
  rewrite H0; reflexivity.
  intro H. unfold get in H.
  unfold pin.
  inductS (Rmap.find r1 h); rewrite H0 in H.
  apply Smap.find_2 in H.
  apply Rmap.find_2 in H0.
  exists x; split; assumption.
  inversion H.
Qed.

Lemma not_in_get : forall r1 n h, (forall r2, ~ pin r1 n r2 h) <-> get r1 n h = None.
Proof.
  intros r1 n h. split. intro H.
  unfold pin in H. unfold get.
  inductS (Rmap.find r1 h).
  apply Rmap.find_2 in H0.
  assert (forall r2, ~ Smap.MapsTo n r2 x).
  intros r2 H1. elim H with (r2 := r2).
  exists x; split; assumption.
  inductS (Smap.find n x).
  apply Smap.find_2 in H2.
  elim H1 with (r2 := x0); assumption.
  reflexivity. reflexivity.
  intros H r2 H0. unfold get in H.
  inductS (Rmap.find r1 h); rewrite H1 in H.
  unfold pin in H0. do 2 destruct H0.
  apply Rmap.find_1 in H0. rewrite H1 in H0.
  inversion H0. rewrite <- H4 in H2.
  apply Smap.find_1 in H2. rewrite H2 in H; inversion H.
  do 2 destruct H0. apply Rmap.find_1 in H0.
  rewrite H1 in H0; inversion H0.
Qed.

Lemma in_union_1 : forall r1 n r2 h1 h2,
    pin r1 n r2 (h1 |+| h2) <-> pin r1 n r2 h1 \/ pin r1 n r2 h2.
Proof.
  unfold union.
  intros r1 n r2 h1 h2.
  split. intro H.
Admitted.

Lemma in_union_2 : forall r1 n r2 h1 h2, ~ pin r1 n r2 h1 ->
    (pin r1 n r2 h2 <-> pin r1 n r2 (h1 |+| h2)).
Proof.
  intros r1 n r2 h1 h2 H.
  split. intro H0.
  apply in_union_1.
  right. assumption.
  intro H0.
  apply in_union_1 in H0.
  case H0. intro H1.
  elim H. assumption.
  intro H1. assumption.
Qed.

(* rnull/rtrue/rfalse has no field. *)
Axiom not_in_null : forall n r h, ~ pin Ref.rnull n r h.
Axiom not_in_true : forall n r h, ~ pin Ref.rtrue n r h.
Axiom not_in_false : forall n r h, ~ pin Ref.rfalse n r h.

Lemma subheap_union : forall h1 h2 : heap, h1 |<| h2 |+| h1.
Proof.
  unfold subheap. intros h1 h2 r1 r2 n H.
  apply in_union_1. right; assumption.
Qed.

Lemma not_in_empty_1 : forall r1 n r2, ~ pin r1 n r2 {}.
Proof.
  intros r1 n r2 H.
  unfold pin in H.
  destruct H; destruct H.
  apply Rmap.empty_1 in H.
  assumption.
Qed.

Lemma not_in_empty_2 : forall k, ~ Rmap.In k {}.
Proof.
  intros k.
  unfold Rmap.In.
  unfold Rmap.Raw.PX.In.
  intro H.
  elim H.
  intros x H0.
  apply Rmap.empty_1 in H0.
  assumption.
Qed.

Lemma pdisjoint_empty : forall x : heap, x |*| {}.
Proof.
  unfold pdisjoint.
  intros x r1 r2 r3 n H.
  destruct H. unfold pin in H0.
  destruct H0. destruct H0.
  apply Rmap.empty_1 in H0.
  elim H0.
Qed.

Lemma pdisjoint_sym : forall x y : heap, x |*| y -> y |*| x.
Proof.
  unfold pdisjoint.
  intros x y H r1 r2 r3 n H0.
  elim H with (r1 := r1) (r2 := r3) (r3 := r2) (n := n).
  destruct H0. split.
  assumption. assumption.
Qed.

Lemma pdisjoint_union : forall h1 h2 h3 : heap,
    h1 |*| (h2 |+| h3) <-> h1 |*| h2 /\ h1 |*| h3.
Proof.
  unfold pdisjoint.
  intros h1 h2 h3.
  split. intro H.
  split. intros r1 r2 r3 n H0.
  destruct H0.
  elim H with (r1 := r1) (r2 := r2) (r3 := r3) (n := n).
  split. assumption.
  apply in_union_1.
  left; assumption.
  intros r1 r2 r3 n H0.
  destruct H0.
  elim H with (r1 := r1) (r2 := r2) (r3 := r3) (n := n).
  split. assumption.
  apply in_union_1.
  right; assumption.
  intros H r1 r2 r3 n H0.
  destruct H. destruct H0.
  apply in_union_1 in H2.
  destruct H2.
  elim H with (r1 := r1) (r2 := r2) (r3 := r3) (n := n).
  split. assumption. assumption.
  elim H1 with (r1 := r1) (r2 := r2) (r3 := r3) (n := n).
  split. assumption. assumption.
Qed.

Lemma pdisjoint_self : forall h : heap, h |*| h -> h |=| {}.
Proof.
  unfold eq; unfold pdisjoint.
  intros h H r1 r2 n. split.
  intro H0. 
  elim H with (r1 := r1) (r2 := r2) (r3 := r2) (n := n).
  split. assumption. assumption.
  intro H0. apply not_in_empty_1 in H0.
  elim H0.
Qed.

Lemma exist_pdisjoint : forall h1 h2 : heap,
    h1 |<| h2 -> exists h3 : heap, h3 |*| h1 /\ h2 |=| h3 |+| h1.
Proof.
(*
  intros h1 h2 H. unfold subheap in H.
  exists (diff_heap h1 h2). unfold diff_heap. split.
  unfold pdisjoint. intros r1 r2 r3 n H0.
  destruct H0. unfold pin in H1. do 2 destruct H1.
  unfold pin in H0. do 2 destruct H0.
  rewrite Rmap.fold_1 in H1.
*)
Admitted.

Lemma in_equal : forall (r r1 r2 : ref) (n : name) (h : heap),
    pin r n r1 h -> pin r n r2 h -> r1 = r2.
Proof.
  unfold pin.
  intros r r1 r2 n h H H0.
  destruct H. destruct H0.
  destruct H. destruct H0.
  apply Rmap.find_1 in H.
  apply Rmap.find_1 in H0.
  rewrite H in H0.
  inversion H0.
  rewrite H4 in H1.
  apply Smap.find_1 in H1.
  apply Smap.find_1 in H2.
  rewrite H1 in H2.
  inversion H2.
  reflexivity.
Qed.

Lemma update_update : forall r1 n r2 r3 h,
    update r1 n r2 h = update r1 n r2 (update r1 n r3 h).
Proof.
  intros r1 n r2 r3 h.
  apply equal_3. unfold eq.
  intros r0 r4 n0.
  split. intro H.
  case Ref.eq_dec with (x := r0) (y := r1).
  case String.string_dec with (s1 := n0) (s2 := n).
  intros H0 H1. rewrite H0. rewrite H1.
  rewrite H0 in H. rewrite H1 in H.
  assert (pin r1 n r2 (update r1 n r2 h)).
  apply in_update_1.
  assert (r2 = r4).
  apply in_equal with (r := r1) (n := n) (h := update r1 n r2 h).
  assumption. assumption.
  rewrite H3. apply in_update_1.
  intros H0 H1. apply in_update_3 in H.
  apply in_update_2.
  right; assumption.
  apply in_update_2.
  right; assumption. assumption.
  right; assumption.
  intro H0. apply in_update_3 in H.
  apply in_update_2.
  left; assumption.
  apply in_update_2.
  left; assumption. assumption.
  left; assumption.
  intro H.
  case Ref.eq_dec with (x := r0) (y := r1).
  case String.string_dec with (s1 := n0) (s2 := n).
  intros H0 H1. rewrite H0. rewrite H1.
  rewrite H0 in H. rewrite H1 in H.
  assert (pin r1 n r2 (update r1 n r2 (update r1 n r3 h))).
  apply in_update_1.
  assert (r2 = r4).
  apply in_equal with (r := r1) (n := n) (h := update r1 n r2 (update r1 n r3 h)).
  assumption. assumption.
  rewrite H3. apply in_update_1.
  intros H0 H1. apply in_update_3 in H.
  apply in_update_2.
  right; assumption.
  apply in_update_3 in H. assumption.
  right; assumption.
  right; assumption.
  intro H0. apply in_update_3 in H.
  apply in_update_2.
  left; assumption.
  apply in_update_3 in H. assumption.
  left; assumption.
  left; assumption.
Qed.

Lemma union_emp : forall h : heap, {} |+| h |=| h.
Proof.
  unfold eq; unfold union.
  intros h r1 r2 n.
  split. intro H.
  apply in_union_1 in H.
  destruct H.
  assert (~ pin r1 n r2 empty_heap).
  apply not_in_empty_1 in H. elim H.
  elim H0. assumption.
  assumption.
  intro H.
  apply in_union_1.
  right. assumption.
Qed.

Lemma union_comm : forall h1 h2 : heap, h1 |+| h2 |=| h2 |+| h1.
Proof.
  unfold eq; unfold union.
  assert (forall (h1 h2 : heap) (r1 r2 : ref) (n : name),
    pin r1 n r2 (Rmap.fold union1 h1 h2) -> pin r1 n r2 (Rmap.fold union1 h2 h1)).
  intros h1 h2 r1 r2 n H.
  apply in_union_1 in H.
  apply in_union_1.
  destruct H.
  right; assumption.
  left; assumption.
  split. apply H. apply H.
Qed.

Lemma union_asso : forall h1 h2 h3 : heap,
    h1 |+| h2 |+| h3 |=| (h1 |+| h2) |+| h3.
Proof.
  unfold eq; unfold union.
  intros h1 h2 h3 r1 r2 n.
  split. intro H.
  apply in_union_1 in H.
  apply in_union_1.
  destruct H. left.
  apply in_union_1.
  left; assumption.
  apply in_union_1 in H.
  destruct H. left.
  apply in_union_1.
  right; assumption.
  right; assumption.
  intro H.
  apply in_union_1 in H.
  apply in_union_1.
  destruct H.
  apply in_union_1 in H.
  destruct H.
  left; assumption.
  right; apply in_union_1.
  left; assumption.
  right; apply in_union_1.
  right; assumption.
Qed.

Lemma not_in_remove_1 : forall r1 n r2 h, ~ pin r1 n r2 (remove r1 n h).
Proof.
  intros r1 n r2 h H.
  unfold remove in H.
  inductS (Rmap.find r1 h); rewrite H0 in H.
  unfold pin in H. do 2 destruct H.
  assert (x0 = Smap.remove n x).
  apply rmap_add in H. assumption.
  rewrite H2 in H1.
  assert (Smap.In n (Smap.remove n x)).
  exists r2. assumption.
  apply Smap.remove_1 in H3.
  elim H3. reflexivity.
  unfold pin in H. do 2 destruct H.
  apply Rmap.find_1 in H.
  rewrite H0 in H. inversion H.
Qed.

Lemma in_remove_2 : forall r1 r2 r3 n1 n2 h,
    (r1 <> r2 \/ n1 <> n2) -> pin r1 n1 r3 h -> pin r1 n1 r3 (remove r2 n2 h).
Proof.
  intros r1 r2 r3 n1 n2 h H H0.
  unfold remove.
  inductS (Rmap.find r2 h).
  do 2 destruct H0.
  destruct H. exists x0. split.
  apply Rmap.add_2. auto.
  assumption. assumption.
  case (Ref.eq_dec r1 r2).
  intro H3. rewrite <- H3.
  rewrite <- H3 in H1.
  apply Rmap.find_2 in H1.
  exists (Smap.remove (elt:=ref) n2 x).
  split. apply Rmap.add_1. reflexivity.
  apply Smap.remove_2. auto.
  assert (x0 = x).
  apply rmap_inject with (k := r1) (m := h).
  assumption. assumption.
  rewrite <- H4. assumption.
  intro H3. exists x0. split.
  apply Rmap.add_2. auto.
  assumption. assumption. assumption.
Qed.

Lemma in_remove_3 : forall r1 r2 r3 n1 n2 h,
    pin r1 n1 r3 (remove r2 n2 h) -> pin r1 n1 r3 h.
Proof.
  intros r1 r2 r3 n1 n2 h H.
  unfold remove in H.
  inductS (Rmap.find r2 h); rewrite H0 in H.
  do 2 destruct H.
  case (Ref.eq_dec r1 r2).
  intro H2. rewrite <- H2 in H.
  assert (x0 = Smap.remove n2 x).
  apply rmap_add in H. assumption.
  exists x. split. rewrite <- H2 in H0.
  apply Rmap.find_2 in H0. assumption.
  rewrite H3 in H1.
  apply Smap.remove_3 with (x := n2).
  assumption.
  intro H2. exists x0. split.
  apply Rmap.add_3 in H. assumption.
  auto. assumption. assumption.
Qed.

Lemma disjoint_remove : forall r1 n r2 h, remove r1 n h |*| update r1 n r2 {}.
Proof.
  unfold pdisjoint.
  intros r1 n r2 h r0 r3 r4 n0 H.
  destruct H.
  case Ref.eq_dec with (x := r0) (y := r1).
  intro H1. rewrite H1 in H.
  case String.string_dec with (s1 := n0) (s2 := n).
  intro H2. rewrite H2 in H.
  apply not_in_remove_1 in H. elim H.
  intro H2.
  apply in_update_3 in H0.
  apply not_in_empty_1 in H0.
  elim H0. right; assumption.
  intro H1.
  case String.string_dec with (s1 := n0) (s2 := n).
  intro H2. apply in_update_3 in H0.
  apply not_in_empty_1 in H0.
  elim H0. left; assumption.
  intro H2. apply in_update_3 in H0.
  apply not_in_empty_1 in H0.
  elim H0. left; assumption.
Qed.

Close Scope heap_scope.
End Heap.

Bind Scope heap_scope with Heap.heap.
Delimit Scope heap_scope with heap.

Infix "|=|" := Heap.eq (at level 70) : heap_scope.
Infix "|+|" := Heap.union (at level 60, right associativity) : heap_scope.
Infix "|*|" := Heap.pdisjoint (at level 50) : heap_scope.
Infix "|<|" := Heap.subheap (at level 70) : heap_scope.
Notation "{}" := Heap.empty_heap : heap_scope.
