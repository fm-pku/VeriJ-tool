Require Export Expr.
Require Import List.

(*-----  Abstract Data Type  -----*)

(*  Language Type  *)

Module Type LANG.

Parameter name : Set.
Parameter method : Set.
Parameter rtype : Set.
Parameter expr : Set.
Parameter bexpr : Set.

Parameter md_set : Type.

Inductive cmd : Set :=
| assign  : name -> expr -> cmd
| assignb : name -> bexpr -> cmd (* 这里出现的bexpr中仅包括或且非三种运算符 *)
| fread   : name -> name -> name -> cmd
| fwrite  : name -> name -> expr -> cmd
| cast    : name -> rtype -> name -> cmd
| skip    : cmd
| cseq    : cmd -> cmd -> cmd
| cif     : bexpr -> cmd -> cmd -> cmd
| cwhile  : bexpr -> cmd -> cmd
| calloc  : name -> rtype -> list expr -> cmd
| dcall   : name -> name -> method -> list expr -> cmd
| scall   : name -> rtype -> name -> method -> list expr -> cmd
| creturn : expr -> cmd.
(* 为了保证这里的cmd是Set类型的，需要把上面的几个参数name等等都定义为Set类型的。 *)

Parameter beq : cmd -> cmd -> bool.
Parameter peq : cmd -> cmd -> Prop.

Parameter md : cmd -> md_set.

Axiom peq_refl : forall c : cmd, peq c c.
Axiom peq_sym : forall c1 c2 : cmd, peq c1 c2 -> peq c2 c1.
Axiom peq_trans : forall c1 c2 c3 : cmd, peq c1 c2 -> peq c2 c3 -> peq c1 c3.
Axiom beq_refl : forall c : cmd, beq c c = true.
Axiom beq_sym : forall c1 c2 : cmd, beq c1 c2 = true -> beq c2 c1 = true.
Axiom beq_trans : forall c1 c2 c3 : cmd,
    beq c1 c2 = true -> beq c2 c3 = true -> beq c1 c3 = true.

End LANG.


(*-----  Data  -----*)

Open Scope string_scope.

(*  Language  *)

Module Lang <: LANG.

Definition name := Name.name.
Definition method := Method.method.
Definition rtype := RType.rtype.
Definition expr := Expr.expr.
Definition bexpr := BExpr.bexpr.

Definition md_set := Sset.t.
Definition md_nth : md_set := Sset.empty.

Inductive cmd : Set :=
| assign  : name -> expr -> cmd (* x := e *)
| assignb : name -> bexpr -> cmd (* x := b *) (* 这里出现的bexpr中仅包括或且非三种运算符 *)
| fread   : name -> name -> name -> cmd (* x := v.a *)
| fwrite  : name -> name -> expr -> cmd (* v.a := e *)
| cast    : name -> rtype -> name -> cmd (* x := (C)v *)
| skip    : cmd
| cseq    : cmd -> cmd -> cmd
| cif     : bexpr -> cmd -> cmd -> cmd
| cwhile  : bexpr -> cmd -> cmd
| calloc  : name -> rtype -> list expr -> cmd (* x := new C(e...) *)
| dcall   : name -> name -> method -> list expr -> cmd (* x := v.m(e...) *)
| scall   : name -> rtype -> name -> method -> list expr -> cmd (* x := v.C::m(e...) *)
| creturn : expr -> cmd.

Fixpoint list_beq (a b : list expr) : bool :=
match a,b with
| nil,nil => true
| a1::a2,b1::b2 => andb (Expr.beq a1 b1) (list_beq a2 b2)
| _,_ => false
end.

Fixpoint list_peq (a b : list expr) : Prop :=
match a,b with
| nil,nil => True
| a1::a2,b1::b2 => (Expr.peq a1 b1) /\ (list_peq a2 b2)
| _,_ => False
end.

Fixpoint beq (c1 c2 : cmd) : bool :=
    match c1, c2 with
    | assign x1 e1, assign x2 e2 =>
        andb (Name.beq x1 x2) (Expr.beq e1 e2)
    | assignb x1 b1, assignb x2 b2 =>
        andb (Name.beq x1 x2) (BExpr.beq b1 b2)
    | fread x1 v1 a1, fread x2 v2 a2 =>
        andb (Name.beq x1 x2) (andb (Name.beq v1 v2) (Name.beq a1 a2))
    | fwrite v1 a1 e1, fwrite v2 a2 e2 =>
        andb (Name.beq v1 v2) (andb (Name.beq a1 a2) (Expr.beq e1 e2))
    | cast x1 c1 v1, cast x2 c2 v2 =>
        andb (Name.beq x1 x2) (andb (RType.beq c1 c2) (Name.beq v1 v2))
    | skip, skip => true
    | cseq c1 c2, cseq c3 c4 =>
        andb (beq c1 c3) (beq c2 c4)
    | cif b1 t1 e1, cif b2 t2 e2 =>
        andb (BExpr.beq b1 b2) (andb (beq t1 t2) (beq e1 e2))
    | cwhile b1 c1, cwhile b2 c2 =>
        andb (BExpr.beq b1 b2) (beq c1 c2)
    | calloc x1 c1 l1, calloc x2 c2 l2 =>
        andb (Name.beq x1 x2) (andb (RType.beq c1 c2) (list_beq l1 l2))
    | dcall x1 v1 m1 l1, dcall x2 v2 m2 l2 =>
        andb (Name.beq x1 x2)
       (andb (Name.beq v1 v2)
       (andb (Method.beq m1 m2)
             (list_beq l1 l2)))
    | scall x1 t1 v1 m1 l1, scall x2 t2 v2 m2 l2 =>
        andb (Name.beq x1 x2)
       (andb (RType.beq t1 t2)
       (andb (Name.beq v1 v2)
       (andb (Method.beq m1 m2)
             (list_beq l1 l2))))
    | creturn e1, creturn e2 =>
        Expr.beq e1 e2
    | _, _ => false
    end.

Fixpoint peq (c1 c2 : cmd) : Prop :=
    match c1, c2 with
    | assign x1 e1, assign x2 e2 =>
        (Name.peq x1 x2) /\ (Expr.peq e1 e2)
    | assignb x1 b1, assignb x2 b2 =>
        (Name.peq x1 x2) /\ (BExpr.peq b1 b2)
    | fread x1 v1 a1, fread x2 v2 a2 =>
        (Name.peq x1 x2) /\ (Name.peq v1 v2) /\ (Name.peq a1 a2)
    | fwrite v1 a1 e1, fwrite v2 a2 e2 =>
        (Name.peq v1 v2) /\ (Name.peq a1 a2) /\ (Expr.peq e1 e2)
    | cast x1 c1 v1, cast x2 c2 v2 =>
        (Name.peq x1 x2) /\ (RType.peq c1 c2) /\ (Name.peq v1 v2)
    | skip, skip => True
    | cseq c1 c2, cseq c3 c4 =>
        (peq c1 c3) /\ (peq c2 c4)
    | cif b1 t1 e1, cif b2 t2 e2 =>
        (BExpr.peq b1 b2) /\ (peq t1 t2) /\ (peq e1 e2)
    | cwhile b1 c1, cwhile b2 c2 =>
        (BExpr.peq b1 b2) /\ (peq c1 c2)
    | calloc x1 c1 l1, calloc x2 c2 l2 =>
        (Name.peq x1 x2) /\ (RType.peq c1 c2) /\ (list_peq l1 l2)
    | dcall x1 v1 m1 l1, dcall x2 v2 m2 l2 =>
        (Name.peq x1 x2) /\ (Name.peq v1 v2) /\
        (Method.peq m1 m2) /\ (list_peq l1 l2)
    | scall x1 t1 v1 m1 l1, scall x2 t2 v2 m2 l2 =>
        (Name.peq x1 x2) /\ (RType.peq t1 t2) /\ (Name.peq v1 v2) /\
        (Method.peq m1 m2) /\ (list_peq l1 l2)
    | creturn e1, creturn e2 =>
        Expr.peq e1 e2
    | _, _ => False
    end.

Fixpoint md (c : cmd) : md_set :=
    match c with
    | assign x _ => Sset.add x md_nth
    | assignb x _ => Sset.add x md_nth
    | fread x _ _ => Sset.add x md_nth
    | cast x _ _ => Sset.add x md_nth
    | cseq c1 c2 => Sset.union (md c1) (md c2)
    | cif _ c1 c2 => Sset.union (md c1) (md c2)
    | cwhile _ c => md c
    | calloc x _ _ => Sset.add x md_nth
    | dcall x _ _ _ => Sset.add x md_nth
    | scall x _ _ _ _ => Sset.add x md_nth
    | creturn _ => Sset.add "res" md_nth
    | _ => md_nth
    end.

Lemma list_beq_refl : forall x : list expr, list_beq x x = true.
Proof.
  induction x. unfold list_beq; reflexivity.
  unfold list_beq; fold list_beq.
  apply Bool.andb_true_iff. split.
  apply Expr.beq_refl. apply IHx.
Qed.
Lemma list_beq_sym : forall x y : list expr, list_beq x y = true -> list_beq y x = true.
Proof.
  induction x, y; try (intros; assumption).
  unfold list_beq; fold list_beq.
  do 2 rewrite Bool.andb_true_iff.
  intros [H H0]; split;
  [apply Expr.beq_sym | apply IHx]; assumption.
Qed.
Lemma list_beq_trans : forall x y z : list expr,
    list_beq x y = true -> list_beq y z = true -> list_beq x z = true.
Proof.
  induction x, y, z; unfold list_beq; fold list_beq;
  repeat rewrite Bool.andb_true_iff;
  repeat (intros || assumption || discriminate).
  destruct H; destruct H0. split.
  apply Expr.beq_trans with (e2 := e); assumption.
  apply IHx with (y := y); assumption.
Qed.

Lemma list_peq_refl : forall x : list expr, list_peq x x.
Proof.
  induction x. unfold list_peq; reflexivity.
  unfold list_peq; fold list_peq. split.
  apply Expr.peq_refl. apply IHx.
Qed.
Lemma list_peq_sym : forall x y : list expr, list_peq x y -> list_peq y x.
Proof.
  induction x, y; try (intros; assumption).
  unfold list_peq; fold list_peq.
  intros [H H0]; split;
  [apply Expr.peq_sym | apply IHx]; assumption.
Qed.
Lemma list_peq_trans : forall x y z : list expr,
    list_peq x y -> list_peq y z -> list_peq x z.
Proof.
  induction x, y, z; unfold list_peq; fold list_peq;
  try (intros; (elim H || assumption)).
  elim H0. destruct H; destruct H0.
  intros H3 H4; split.
  apply Expr.peq_trans with (e2 := e); assumption.
  apply IHx with (y := y); assumption.
Qed.

Lemma peq_refl : forall c : cmd, peq c c.
Proof.
  induction c; unfold peq; fold peq;
  repeat (split || apply Name.eq_refl ||
  apply Expr.peq_refl || apply BExpr.peq_refl ||
  apply list_peq_refl || assumption).
Qed.
Lemma peq_sym : forall c1 c2 : cmd, peq c1 c2 -> peq c2 c1.
Proof.
  induction c1, c2; unfold peq; fold peq;
  try repeat (intros [* *] || intro || split ||
  (apply Name.eq_sym; assumption) || (apply Expr.peq_sym; assumption) ||
  (apply BExpr.peq_sym; assumption) || (apply IHc1_1; assumption) ||
  (apply IHc1_2; assumption) || (apply IHc1; assumption) ||
  (apply list_peq_sym; assumption) || assumption).
Qed.
Lemma peq_trans : forall c1 c2 c3 : cmd, peq c1 c2 -> peq c2 c3 -> peq c1 c3.
Proof.
  induction c1, c2, c3; unfold peq; fold peq;
  try repeat (intros [* *] || intro || split ||
  (apply Name.eq_trans with (y := n0); assumption) ||
  (apply Expr.peq_trans with (e2 := e0); assumption) ||
  (apply BExpr.peq_trans with (e2 := b0); assumption) ||
  (apply IHc1_1 with (c2 := c2_1); assumption) ||
  (apply IHc1_2 with (c2 := c2_2); assumption) ||
  (apply IHc1 with (c2 := c2); assumption) ||
  (apply list_peq_trans with (y := l0); assumption) ||
  (elim H; fail) || assumption).
Qed.
Lemma beq_refl : forall c : cmd, beq c c = true.
Proof.
  induction c; unfold beq; fold beq;
  repeat rewrite Bool.andb_true_iff;
  repeat (split || apply Name.beq_refl ||
  apply Expr.beq_refl || apply BExpr.beq_refl ||
  apply list_beq_refl || assumption).
Qed.
Lemma beq_sym : forall c1 c2 : cmd, beq c1 c2 = true -> beq c2 c1 = true.
Proof.
  induction c1, c2; unfold beq; fold beq;
  repeat rewrite Bool.andb_true_iff; intros;
  repeat match goal with
  | [id : (_ /\ _) |- _] => destruct id
  end;
  repeat (discriminate || split ||
  (apply Name.beq_sym; assumption) || (apply Expr.beq_sym; assumption) ||
  (apply BExpr.beq_sym; assumption) || (apply IHc1_1; assumption) ||
  (apply IHc1_2; assumption) || (apply IHc1; assumption) ||
  (apply list_beq_sym; assumption) || assumption).
Qed.
Lemma beq_trans : forall c1 c2 c3 : cmd,
    beq c1 c2 = true -> beq c2 c3 = true -> beq c1 c3 = true.
Proof.
  induction c1, c2, c3; unfold beq; fold beq;
  repeat rewrite Bool.andb_true_iff; intros;
  repeat match goal with
  | [id : (_ /\ _) |- _] => destruct id
  end;
  repeat (discriminate || split ||
  (apply Name.beq_trans with (y := n0); assumption) ||
  (apply Expr.beq_trans with (e2 := e0); assumption) ||
  (apply BExpr.beq_trans with (e2 := b0); assumption) ||
  (apply IHc1_1 with (c2 := c2_1); assumption) ||
  (apply IHc1_2 with (c2 := c2_2); assumption) ||
  (apply IHc1 with (c2 := c2); assumption) ||
  (apply list_beq_trans with (y := l0); assumption) || assumption).
  apply Name.beq_trans with (y := n2); assumption.
  apply Name.beq_trans with (y := n3); assumption.
  apply Name.beq_trans with (y := n4); assumption.
  apply Name.beq_trans with (y := n1); assumption.
  apply Name.beq_trans with (y := n2); assumption.
  apply Name.beq_trans with (y := n1); assumption.
  apply RType.beq_trans with (y := r0); assumption.
  apply Name.beq_trans with (y := n2); assumption.
  apply RType.beq_trans with (y := r0); assumption.
  apply Name.beq_trans with (y := n1); assumption.
  apply Name.beq_trans with (y := n2); assumption.
  apply Method.beq_trans with (y := m0); assumption.
  apply Name.beq_trans with (y := n1); assumption.
  apply RType.beq_trans with (y := r0); assumption.
  apply Name.beq_trans with (y := n2); assumption.
  apply Method.beq_trans with (y := m0); assumption.
Qed.

End Lang.

Close Scope string_scope.

Bind Scope lang_scope with Lang.cmd.
Delimit Scope lang_scope with lang.

Infix ";" := Lang.cseq (at level 90, right associativity) : lang_scope.
