Require Import Bool.
Require Export Stack.

(*-----  Abstract Data Type  -----*)

(*  Expression Type  *)

Module Type EXPR.

Parameter name : Set.
Parameter stack : Type.
Parameter ref : Type.

Inductive expr : Set :=
    | tru  : expr
    | fals : expr
    | null : expr
    | var  : name -> expr.

Parameter beq : expr -> expr -> bool.
Parameter peq : expr -> expr -> Prop.
Parameter beeq : expr -> expr -> stack -> bool.
Parameter peeq : expr -> expr -> stack -> Prop.

Parameter expr2name : expr -> name.

Parameter eval : expr -> stack -> ref.

Axiom beq_refl : forall e : expr, beq e e = true.
Axiom beq_sym : forall e1 e2 : expr, beq e1 e2 = true -> beq e2 e1 = true.
Axiom beq_trans : forall e1 e2 e3 : expr,
    beq e1 e2 = true -> beq e2 e3 = true -> beq e1 e3 = true.
Axiom peq_refl : forall e : expr, peq e e.
Axiom peq_sym : forall e1 e2 : expr, peq e1 e2 -> peq e2 e1.
Axiom peq_trans : forall e1 e2 e3 : expr, peq e1 e2 -> peq e2 e3 -> peq e1 e3.

End EXPR.

(*  Bool Expression Type  *)

Module Type BEXPR.

Parameter name : Type.
Parameter ref : Type.
Parameter stack : Type.
Parameter expr : Set.

Inductive bexpr : Set := 
    | bequal : expr -> expr -> bexpr
    | band   : bexpr -> bexpr -> bexpr
    | bor    : bexpr -> bexpr -> bexpr
    | bneg   : bexpr -> bexpr
    | btrue  : bexpr
    | bfalse : bexpr.

Parameter name2bool : name -> stack -> option bool.
Parameter ref2bool : ref -> option bool.
Parameter bool2ref : bool -> ref.
Parameter eval : bexpr -> stack -> bool.
Parameter beq : bexpr -> bexpr -> bool.
Parameter peq : bexpr -> bexpr -> Prop.
Parameter eeq : bexpr -> bexpr -> Prop.

Axiom beq_refl : forall e : bexpr, beq e e = true.
Axiom beq_sym : forall e1 e2 : bexpr, beq e1 e2 = true -> beq e2 e1 = true.
Axiom beq_trans : forall e1 e2 e3 : bexpr,
    beq e1 e2 = true -> beq e2 e3 = true -> beq e1 e3 = true.
Axiom peq_refl : forall e : bexpr, peq e e.
Axiom peq_sym : forall e1 e2 : bexpr, peq e1 e2 -> peq e2 e1.
Axiom peq_trans : forall e1 e2 e3 : bexpr, peq e1 e2 -> peq e2 e3 -> peq e1 e3.

Axiom eeq_refl : forall e : bexpr, eeq e e.
Axiom eeq_sym : forall e1 e2 : bexpr, eeq e1 e2 -> eeq e2 e1.
Axiom eeq_trans : forall e1 e2 e3 : bexpr, eeq e1 e2 -> eeq e2 e3 -> eeq e1 e3.

Axiom neg_or : forall (e1 e2 : bexpr), eeq (bneg (bor e1 e2)) (band (bneg e1) (bneg e2)).
Axiom neg_and : forall (e1 e2 : bexpr), eeq (bneg (band e1 e2)) (bor (bneg e1) (bneg e2)).

Axiom neg_involutive : forall e : bexpr, eeq (bneg (bneg e)) e.
Axiom neg_involutive_reverse : forall e : bexpr, eeq e (bneg (bneg e)).
Axiom neg_sym : forall e e' : bexpr, eeq e' (bneg e) -> eeq e (bneg e').
Axiom eq_neg1 : forall e : bexpr, ~ (eeq (bneg e) e).
Axiom eq_neg2 : forall e : bexpr, ~ (eeq e (bneg e)).

Axiom or_true_iff : forall (e1 e2 : bexpr) (s : stack),
      (eval (bor e1 e2) s) = true <-> eval e1 s = true \/ eval e2 s = true.
Axiom or_false_iff : forall (e1 e2 : bexpr) (s : stack),
      (eval (bor e1 e2) s) = false <-> eval e1 s = false /\ eval e2 s = false.
Axiom or_true_r : forall e : bexpr, eeq (bor e btrue) btrue.
Axiom or_true_l : forall e : bexpr, eeq (bor btrue e) btrue.
Axiom or_false_r : forall e : bexpr, eeq (bor e bfalse) e.
Axiom or_false_l : forall e : bexpr, eeq (bor bfalse e) e.
Axiom or_neg_r : forall e : bexpr, eeq (bor e (bneg e)) btrue.
Axiom or_comm : forall e1 e2 : bexpr, eeq (bor e1 e2) (bor e2 e1).
Axiom or_asso : forall e1 e2 e3 : bexpr, eeq (bor e1 (bor e2 e3)) (bor (bor e1 e2) e3).

Axiom and_true_iff : forall (e1 e2 : bexpr) (s : stack),
      (eval (band e1 e2) s) = true <-> eval e1 s = true /\ eval e2 s = true.
Axiom and_false_iff : forall (e1 e2 : bexpr) (s : stack),
      (eval (band e1 e2) s) = false <-> eval e1 s = false \/ eval e2 s = false.
Axiom and_true_r : forall e : bexpr, eeq (band e btrue) e.
Axiom and_true_l : forall e : bexpr, eeq (band btrue e) e.
Axiom and_false_r : forall e : bexpr, eeq (band e bfalse) bfalse.
Axiom and_false_l : forall e : bexpr, eeq (band bfalse e) bfalse.
Axiom and_neg_r : forall e : bexpr, eeq (band e (bneg e)) bfalse.
Axiom and_comm : forall e1 e2 : bexpr, eeq (band e1 e2) (band e2 e1).
Axiom and_asso : forall e1 e2 e3 : bexpr, eeq (band e1 (band e2 e3)) (band (band e1 e2) e3).

Axiom and_or_distrib_r : forall e1 e2 e3 : bexpr,
                         eeq (band e1 (bor e2 e3)) (bor (band e1 e2) (band e1 e3)).
Axiom and_or_distrib_l : forall e1 e2 e3 : bexpr,
                         eeq (band (bor e1 e2) e3) (bor (band e1 e3) (band e2 e3)).
Axiom or_and_distrib_r : forall e1 e2 e3 : bexpr,
                         eeq (bor e1 (band e2 e3)) (band (bor e1 e2) (bor e1 e3)).
Axiom or_and_distrib_l : forall e1 e2 e3 : bexpr,
                         eeq (bor (band e1 e2) e3) (band (bor e1 e3) (bor e2 e3)).
Axiom absoption_and : forall e1 e2 : bexpr, eeq (band e1 (bor e1 e2)) e1.
Axiom absoption_or : forall e1 e2 : bexpr, eeq (bor e1 (band e1 e2)) e1.

End BEXPR.


(*-----  Data  -----*)

(*  Expr  *)

Module Expr <: EXPR.

Definition name := Name.name.
Definition stack := Stack.stack.
Definition ref := Ref.ref.

Inductive expr : Set :=
    | tru  : expr
    | fals : expr
    | null : expr
    | var  : name -> expr.

Definition beq (a b : expr) : bool :=
    match a, b with
    | tru, tru => true
    | fals, fals => true
    | null, null => true
    | var u, var v => Name.beq u v
    | _, _ => false
    end.

Definition peq (a b : expr) : Prop :=
    match a, b with
    | tru, tru => True
    | fals, fals => True
    | null, null => True
    | var u, var v => Name.peq u v
    | _, _ => False
    end.

Definition beeq (a b : expr) (s : stack) : bool :=
    match a, b with
    | tru, tru => true
    | fals, fals => true
    | null, null => true
    | var u, var v => match Stack.get u s, Stack.get v s with
                      | Some r, Some r' => Ref.beq r r'
                      | _, _ => false
                      end
    | var u, tru => match Stack.get u s with
                    | Some r => Ref.beq Ref.rtrue r
                    | None => false
                    end
    | tru, var u => match Stack.get u s with
                    | Some r => Ref.beq Ref.rtrue r
                    | None => false
                    end
    | var u, fals => match Stack.get u s with
                     | Some r => Ref.beq Ref.rfalse r
                     | None => false
                     end
    | fals, var u => match Stack.get u s with
                     | Some r => Ref.beq Ref.rfalse r
                     | None => false
                     end
    | var u, null => match Stack.get u s with
                     | Some r => Ref.beq Ref.rnull r
                     | None => false
                     end
    | null, var u => match Stack.get u s with
                     | Some r => Ref.beq Ref.rnull r
                     | None => false
                     end
    | _, _ => false
    end.

Definition peeq (a b : expr) (s : stack) : Prop :=
    match a, b with
    | tru, tru => True
    | fals, fals => True
    | null, null => True
    | var u, var v => match Stack.get u s, Stack.get v s with
                      | Some r, Some r' => r = r'
                      | _, _ => False
                      end
    | var u, tru => match Stack.get u s with
                    | Some r => Ref.rtrue = r
                    | None => False
                    end
    | tru, var u => match Stack.get u s with
                    | Some r => Ref.rtrue = r
                    | None => False
                    end
    | var u, fals => match Stack.get u s with
                     | Some r => Ref.rfalse = r
                     | None => False
                     end
    | fals, var u => match Stack.get u s with
                     | Some r => Ref.rfalse = r
                     | None => False
                     end
    | var u, null => match Stack.get u s with
                     | Some r => Ref.rnull = r
                     | None => False
                     end
    | null, var u => match Stack.get u s with
                     | Some r => Ref.rnull = r
                     | None => False
                     end
    | _, _ => False
    end.

Definition expr2name (e : expr) : name :=
    match e with
        | tru => Name.Ntrue
        | fals => Name.Nfalse
        | null => Name.Nnull
        | var n => n
    end.

Definition eval (e : expr) (s : stack) : ref :=
    match e with
        | tru => Ref.rtrue
        | fals => Ref.rfalse
        | null => Ref.rnull
        | var n => match Stack.get n s with
                       | Some r => r
                       | None => Ref.rnull
                   end
    end.

Lemma beq_refl : forall e : expr, beq e e = true.
Proof.
  unfold beq. induction e; try reflexivity.
  apply Name.beq_refl.
Qed.
Lemma beq_sym : forall e1 e2 : expr, beq e1 e2 = true -> beq e2 e1 = true.
Proof.
  unfold beq. induction e1, e2; auto.
  apply Name.beq_sym.
Qed.
Lemma beq_trans : forall e1 e2 e3 : expr,
    beq e1 e2 = true -> beq e2 e3 = true -> beq e1 e3 = true.
Proof.
  unfold beq. induction e1, e2, e3; try tauto;
  try (intros; discriminate).
  apply Name.beq_trans.
Qed.

Lemma peq_refl : forall e : expr, peq e e.
Proof.
  unfold peq. induction e; try reflexivity.
Qed.
Lemma peq_sym : forall e1 e2 : expr, peq e1 e2 -> peq e2 e1.
Proof.
  unfold peq. induction e1, e2; auto.
  apply Name.eq_sym.
Qed.
Lemma peq_trans : forall e1 e2 e3 : expr, peq e1 e2 -> peq e2 e3 -> peq e1 e3.
Proof.
  unfold peq. induction e1, e2; try tauto.
  induction e3; auto. apply Name.eq_trans.
Qed.

End Expr.

(*  Bool Expression  *)

Module BExpr <: BEXPR.

Definition name := Name.name.
Definition ref := Ref.ref.
Definition stack := Stack.stack.
Definition expr := Expr.expr.

Inductive bexpr : Set := 
    | bequal : expr -> expr -> bexpr
    | band   : bexpr -> bexpr -> bexpr
    | bor    : bexpr -> bexpr -> bexpr
    | bneg   : bexpr -> bexpr
    | btrue  : bexpr
    | bfalse : bexpr.

Definition name2bool (n : name) (s : stack) : option bool :=
    match (Stack.get n s) with
    | Some r => if (Ref.beq r Ref.rtrue) then Some true
                else if (Ref.beq r Ref.rfalse) then Some false
                else None
    | None => None
    end.

Definition ref2bool (r : ref) : option bool :=
    if (Ref.beq r Ref.rtrue) then Some true
    else if (Ref.beq r Ref.rfalse) then Some false
    else None.

Definition bool2ref (b : bool) : ref :=
    if b then Ref.rtrue
    else Ref.rfalse.

Definition eqbo (a b : option bool) : option bool :=
    match a with
    | Some a' =>
        match b with
        | Some b' => Some (eqb a' b')
        | None => None
        end
    | None => None
    end.

Definition andbo (a b : option bool) : option bool :=
    match a with
    | Some a' =>
        match b with
        | Some b' => Some (andb a' b')
        | None => None
        end
    | None => None
    end.

Definition orbo (a b : option bool) : option bool :=
    match a with
    | Some a' =>
        match b with
        | Some b' => Some (orb a' b')
        | None => None
        end
    | None => None
    end.

Definition negbo (a : option bool) : option bool :=
    match a with
    | Some a' => Some (negb a')
    | None => None
    end.

Fixpoint eval (e : bexpr) (s : stack) : bool :=
    match e with
        | bequal a b => Expr.beeq a b s
        | band a b => andb (eval a s) (eval b s)
        | bor a b => orb (eval a s) (eval b s)
        | bneg a => negb (eval a s)
        | btrue => true
        | bfalse => false
    end.

(* 所以问题就是，引入异常后所有返回值和参数前都要加option。
   处理起来非常繁琐。 *)

Fixpoint beq (e1 e2 : bexpr) : bool :=
    match e1, e2 with
        | bequal a1 b1, bequal a2 b2 =>
            andb (Expr.beq a1 a2) (Expr.beq b1 b2)
        | band a1 b1, band a2 b2 =>
            andb (beq a1 a2) (beq b1 b2)
        | bor a1 b1, bor a2 b2 =>
            andb (beq a1 a2) (beq b1 b2)
        | bneg a1, bneg a2 =>
            beq a1 a2
        | btrue, btrue => true
        | bfalse, bfalse => true
        | _, _ => false
    end.

Fixpoint peq (e1 e2 : bexpr) : Prop :=
    match e1, e2 with
        | bequal a1 b1, bequal a2 b2 =>
            (Expr.peq a1 a2) /\ (Expr.peq b1 b2)
        | band a1 b1, band a2 b2 =>
            (peq a1 a2) /\ (peq b1 b2)
        | bor a1 b1, bor a2 b2 =>
            (peq a1 a2) /\ (peq b1 b2)
        | bneg a1, bneg a2 =>
            peq a1 a2
        | btrue, btrue => True
        | bfalse, bfalse => True
        | _, _ => False
    end.

Definition eeq (e1 e2 : bexpr) : Prop :=
           forall (s : stack), (eval e1 s) = (eval e2 s).

Lemma beq_refl : forall e : bexpr, beq e e = true.
Proof.
  unfold beq. induction e; try rewrite andb_true_iff; try tauto.
  split; apply Expr.beq_refl.
Qed.
Lemma beq_sym : forall e1 e2 : bexpr, beq e1 e2 = true -> beq e2 e1 = true.
Proof.
  induction e1, e2; unfold beq; fold beq; try tauto;
  repeat rewrite andb_true_iff.
  intros [H H0]; split; apply Expr.beq_sym; assumption.
  intros [H H0]; split;
  [apply IHe1_1 | apply IHe1_2]; assumption.
  intros [H H0]; split;
  [apply IHe1_1 | apply IHe1_2]; assumption.
  apply IHe1.
Qed.
Lemma beq_trans : forall e1 e2 e3 : bexpr,
    beq e1 e2 = true -> beq e2 e3 = true -> beq e1 e3 = true.
Proof.
  induction e1, e2, e3; unfold beq; fold beq;
  repeat rewrite andb_true_iff; try tauto;
  try (intros; discriminate).
  intros [H H0] [H1 H2]; split;
  [apply Expr.beq_trans with (e2 := e1) |
   apply Expr.beq_trans with (e2 := e2)];
  assumption.
  intros [H H0] [H1 H2]; split;
  [apply IHe1_1 with (e2 := e2_1) |
   apply IHe1_2 with (e2 := e2_2)];
  assumption.
  intros [H H0] [H1 H2]; split;
  [apply IHe1_1 with (e2 := e2_1) |
   apply IHe1_2 with (e2 := e2_2)];
  assumption. apply IHe1.
Qed.

Lemma peq_refl : forall e : bexpr, peq e e.
Proof.
  unfold peq. induction e; try tauto.
  split; apply Expr.peq_refl.
Qed.
Lemma peq_sym : forall e1 e2 : bexpr, peq e1 e2 -> peq e2 e1.
Proof.
  induction e1, e2; unfold peq; fold peq; try tauto.
  intros [H H0]; split; apply Expr.peq_sym; assumption.
  intros [H H0]; split;
  [apply IHe1_1 | apply IHe1_2]; assumption.
  intros [H H0]; split;
  [apply IHe1_1 | apply IHe1_2]; assumption.
  apply IHe1.
Qed.
Lemma peq_trans : forall e1 e2 e3 : bexpr, peq e1 e2 -> peq e2 e3 -> peq e1 e3.
Proof.
  induction e1, e2, e3; unfold peq; fold peq; try tauto.
  intros [H H0] [H1 H2]; split;
  [apply Expr.peq_trans with (e2 := e1) |
   apply Expr.peq_trans with (e2 := e2)];
  assumption.
  intros [H H0] [H1 H2]; split;
  [apply IHe1_1 with (e2 := e2_1) |
   apply IHe1_2 with (e2 := e2_2)];
  assumption.
  intros [H H0] [H1 H2]; split;
  [apply IHe1_1 with (e2 := e2_1) |
   apply IHe1_2 with (e2 := e2_2)];
  assumption. apply IHe1.
Qed.

Lemma eeq_refl : forall e : bexpr, eeq e e.
Proof.
  unfold eeq. intros e s.
  reflexivity.
Qed.
  
Lemma eeq_sym : forall e1 e2 : bexpr, eeq e1 e2 -> eeq e2 e1.
Proof.
  intros e1 e2 H.
  unfold eeq. unfold eeq in H.
  intros s. apply eq_sym.
  apply H.
Qed.

Lemma eeq_trans : forall e1 e2 e3 : bexpr, eeq e1 e2 -> eeq e2 e3 -> eeq e1 e3.
Proof.
  intros e1 e2 e3. unfold eeq.
  intros H H' s.
  rewrite H with (s := s).
  apply H'.
Qed.

Lemma neg_or : forall (e1 e2 : bexpr), eeq (bneg (bor e1 e2)) (band (bneg e1) (bneg e2)).
Proof.
  unfold eeq. intros e1 e2 s.
  unfold eval; fold eval.
  apply negb_orb.
Qed.

Lemma neg_and : forall (e1 e2 : bexpr), eeq (bneg (band e1 e2)) (bor (bneg e1) (bneg e2)).
Proof.
  unfold eeq. intros e1 e2 s.
  unfold eval; fold eval.
  apply negb_andb.
Qed.

Lemma neg_involutive : forall e : bexpr, eeq (bneg (bneg e)) e.
Proof.
  unfold eeq. intros e s.
  unfold eval; fold eval.
  apply negb_involutive.
Qed.

Lemma neg_involutive_reverse : forall e : bexpr, eeq e (bneg (bneg e)).
Proof.
  unfold eeq. intros e s.
  unfold eval; fold eval.
  apply negb_involutive_reverse.
Qed.

Lemma neg_sym : forall e e' : bexpr, eeq e' (bneg e) -> eeq e (bneg e').
Proof.
  unfold eeq.
  unfold eval; fold eval.
  intros e e' H s.
  apply negb_sym.
  apply H.
Qed.

Lemma eq_neg1 : forall e : bexpr, ~ (eeq (bneg e) e).
Proof.
  unfold eeq. intros e H.
  unfold eval in H; fold eval in H.
  apply no_fixpoint_negb with (b := eval e Stack.init_stack) in H.
  elim H.
Qed.

Lemma eq_neg2 : forall e : bexpr, ~ (eeq e (bneg e)).
Proof.
  intros e H.
  apply eeq_sym in H.
  apply eq_neg1 in H.
  assumption.
Qed.

Lemma or_true_iff : forall (e1 e2 : bexpr) (s : stack),
      (eval (bor e1 e2) s) = true <-> eval e1 s = true \/ eval e2 s = true.
Proof.
  intros e1 e2 s.
  unfold eval; fold eval.
  split. apply orb_true_iff.
  apply orb_true_iff.
Qed.

Lemma or_false_iff : forall (e1 e2 : bexpr) (s : stack),
      (eval (bor e1 e2) s) = false <-> eval e1 s = false /\ eval e2 s = false.
Proof.
  intros e1 e2 s.
  unfold eval; fold eval.
  split. apply orb_false_iff.
  apply orb_false_iff.
Qed.

Lemma or_true_r : forall e : bexpr, eeq (bor e btrue) btrue.
Proof.
  unfold eeq. intros e s.
  unfold eval; fold eval.
  apply orb_true_r.
Qed.

Lemma or_true_l : forall e : bexpr, eeq (bor btrue e) btrue.
Proof.
  unfold eeq. intros e s.
  unfold eval; fold eval.
  apply orb_true_l.
Qed.

Lemma or_false_r : forall e : bexpr, eeq (bor e bfalse) e.
Proof.
  unfold eeq. intros e s.
  unfold eval; fold eval.
  apply orb_false_r.
Qed.

Lemma or_false_l : forall e : bexpr, eeq (bor bfalse e) e.
Proof.
  unfold eeq. intros e s.
  unfold eval; fold eval.
  apply orb_false_l.
Qed.

Lemma or_neg_r : forall e : bexpr, eeq (bor e (bneg e)) btrue.
Proof.
  unfold eeq. intros e s.
  unfold eval; fold eval.
  apply orb_negb_r.
Qed.

Lemma or_comm : forall e1 e2 : bexpr, eeq (bor e1 e2) (bor e2 e1).
Proof.
  unfold eeq. intros e1 e2 s.
  unfold eval; fold eval.
  apply orb_comm.
Qed.

Lemma or_asso : forall e1 e2 e3 : bexpr, eeq (bor e1 (bor e2 e3)) (bor (bor e1 e2) e3).
Proof.
  unfold eeq. intros e1 e2 e3 s.
  unfold eval; fold eval.
  apply orb_assoc.
Qed.

Lemma and_true_iff : forall (e1 e2 : bexpr) (s : stack),
      (eval (band e1 e2) s) = true <-> eval e1 s = true /\ eval e2 s = true.
Proof.
  intros e1 e2 s.
  unfold eval; fold eval.
  split. apply andb_true_iff.
  apply andb_true_iff.
Qed.

Lemma and_false_iff : forall (e1 e2 : bexpr) (s : stack),
      (eval (band e1 e2) s) = false <-> eval e1 s = false \/ eval e2 s = false.
Proof.
  intros e1 e2 s.
  unfold eval; fold eval.
  split. apply andb_false_iff.
  apply andb_false_iff.
Qed.

Lemma and_true_r : forall e : bexpr, eeq (band e btrue) e.
Proof.
  unfold eeq. intros e s.
  unfold eval; fold eval.
  apply andb_true_r.
Qed.

Lemma and_true_l : forall e : bexpr, eeq (band btrue e) e.
Proof.
  unfold eeq. intros e s.
  unfold eval; fold eval.
  apply andb_true_l.
Qed.

Lemma and_false_r : forall e : bexpr, eeq (band e bfalse) bfalse.
Proof.
  unfold eeq. intros e s.
  unfold eval; fold eval.
  apply andb_false_r.
Qed.

Lemma and_false_l : forall e : bexpr, eeq (band bfalse e) bfalse.
Proof.
  unfold eeq. intros e s.
  unfold eval; fold eval.
  apply andb_false_l.
Qed.

Lemma and_neg_r : forall e : bexpr, eeq (band e (bneg e)) bfalse.
Proof.
  unfold eeq; intros e s.
  unfold eval; fold eval.
  apply andb_negb_r.
Qed.

Lemma and_comm : forall e1 e2 : bexpr, eeq (band e1 e2) (band e2 e1).
Proof.
  unfold eeq. intros e1 e2 s.
  unfold eval; fold eval.
  apply andb_comm.
Qed.

Lemma and_asso : forall e1 e2 e3 : bexpr, eeq (band e1 (band e2 e3)) (band (band e1 e2) e3).
Proof.
  unfold eeq. intros e1 e2 e3 s.
  unfold eval; fold eval.
  apply andb_assoc.
Qed.

Lemma and_or_distrib_r : forall e1 e2 e3 : bexpr,
    eeq (band e1 (bor e2 e3)) (bor (band e1 e2) (band e1 e3)).
Proof.
  unfold eeq. intros e1 e2 e3 s.
  unfold eval; fold eval.
  apply andb_orb_distrib_r.
Qed.

Lemma and_or_distrib_l : forall e1 e2 e3 : bexpr,
    eeq (band (bor e1 e2) e3) (bor (band e1 e3) (band e2 e3)).
Proof.
  unfold eeq. intros e1 e2 e3 s.
  unfold eval; fold eval.
  apply andb_orb_distrib_l.
Qed.

Lemma or_and_distrib_r : forall e1 e2 e3 : bexpr,
    eeq (bor e1 (band e2 e3)) (band (bor e1 e2) (bor e1 e3)).
Proof.
  unfold eeq. intros e1 e2 e3 s.
  unfold eval; fold eval.
  apply orb_andb_distrib_r.
Qed.

Lemma or_and_distrib_l : forall e1 e2 e3 : bexpr,
                         eeq (bor (band e1 e2) e3) (band (bor e1 e3) (bor e2 e3)).
Proof.
  unfold eeq. intros e1 e2 e3 s.
  unfold eval; fold eval.
  apply orb_andb_distrib_l.
Qed.

Lemma absoption_and : forall e1 e2 : bexpr, eeq (band e1 (bor e1 e2)) e1.
Proof.
  unfold eeq. intros e1 e2 s.
  unfold eval; fold eval.
  apply absoption_andb.
Qed.

Lemma absoption_or : forall e1 e2 : bexpr, eeq (bor e1 (band e1 e2)) e1.
Proof.
  unfold eeq. intros e1 e2 s.
  unfold eval; fold eval.
  apply absoption_orb.
Qed.

End BExpr.

Notation "^ v" := (Expr.var v) (at level 10) : lang_scope.