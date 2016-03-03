Require Export State.
Require Import List.

(*-----  Abstract Data Type  -----*)

(*  Semantic Type  *)

Module Type SEM.

Definition state := State.state.
Definition cmd := Lang.cmd.

Inductive conf : Type :=
| cmd_st : cmd -> state -> conf
| end_st : state -> conf
| ab     : conf.

Parameter beq : conf -> conf -> bool.
Parameter peq : conf -> conf -> Prop.

End SEM.


(*-----  Data  -----*)

(*  Semantic  *)

Module Sem <: SEM.

Definition state := State.state.
Definition heap := Heap.heap.
Definition stack := Stack.stack.
Definition cmd := Lang.cmd.
Definition name := Name.name.
Definition method := Method.method.
Definition rtype := RType.rtype.
Definition ref := Ref.ref.
Definition expr := Lang.expr.
Definition locvars := MEnv.locvars.
Definition args := MEnv.args.

Inductive conf :=
| cmd_st : cmd -> state -> conf
| end_st : state -> conf
| ab     : conf.

Open Scope string_scope.

Definition treat_locvars (l : locvars) (c : conf) : conf :=
match c with
| ab => ab
| end_st s => end_st (State.map_stack (Sset.fold Stack.update_null l) s)
| cmd_st c s => cmd_st c (State.map_stack (Sset.fold Stack.update_null l) s)
end.

Definition update_null_field (r : ref) (n : name) (t : rtype) (h : heap) : heap :=
    Heap.update r n Ref.rnull h.

Definition treat_fields (r : ref) (c : conf) : conf :=
match c with
| ab => ab
| end_st s => match TEnv.get_fields (Ref.get_type r) (State.get_fields_env s) with
              | None => ab
              | Some f => end_st (State.map_heap (Smap.fold (update_null_field r) f) s)
              end
| cmd_st c s => match TEnv.get_fields (Ref.get_type r) (State.get_fields_env s) with
                | None => ab
                | Some f => cmd_st c (State.map_heap (Smap.fold (update_null_field r) f) s)
                end
end.

Fixpoint treat_args (le : list expr) (a : args) (S : stack) (C : conf) : conf :=
match C with
| ab => ab
| end_st s => match le, a with
    | nil, nil => C
    | x :: y, x0 :: y0 =>
        treat_args y y0 S (end_st (State.map_stack (Stack.update x0 (Expr.eval x S)) s))
    | _, _ => ab
    end
| cmd_st c s => match le, a with
    | nil, nil => C
    | x :: y, x0 :: y0 =>
        treat_args y y0 S (cmd_st c (State.map_stack (Stack.update x0 (Expr.eval x S)) s))
    | _, _ => ab
    end
end.

Definition alloc_pretreat (x : name) (t : rtype) (le : list expr) (s : state) : conf :=
let r := (Ref.alloc_count (State.get_alloc s) + 1, t) in
    match MEnv.find_mbody (State.get_mbody_env s) t t with
    | Some (a, l, Some c) =>
        treat_locvars l
        (treat_fields r
        (treat_args le a (State.get_stack s)
        (cmd_st c
        (State.update_stack (Stack.update "this" r Stack.empty_stack) s))))
    | _ => ab
    end.

Definition dcall_pretreat (x : name) (v : name) (m : method) (le : list expr)
                          (s : state) : conf :=
match Stack.get v (State.get_stack s) with
| None => ab
| Some r =>
    match MEnv.find_mbody (State.get_mbody_env s) (Ref.get_type r) m with
    | Some (a, l, Some c) =>
        treat_locvars l
        (treat_args le a (State.get_stack s)
        (cmd_st c
        (State.update_stack (Stack.update "res" Ref.rnull
                            (Stack.update "this" r Stack.empty_stack)) s)))
    | _ => ab
    end
end.

Definition scall_pretreat (x : name) (v : name) (t : rtype) (m : method)
                          (le : list expr) (s : state) : conf :=
match Stack.get v (State.get_stack s) with
| None => ab
| Some r =>
    match MEnv.find_mbody (State.get_mbody_env s) t m with
    | Some (a, l, Some c) =>
        treat_locvars l
        (treat_args le a (State.get_stack s)
        (cmd_st c
        (State.update_stack (Stack.update "res" Ref.rnull
                            (Stack.update "this" r Stack.empty_stack)) s)))
    | _ => ab
    end
end.

Definition beq (c1 c2 : conf) : bool :=
    match c1, c2 with
    | cmd_st c s, cmd_st c' s' => andb (Lang.beq c c') (State.beq s s')
    | end_st s, end_st s' => State.beq s s'
    | ab, ab => true
    | _, _ => false
    end.
Definition peq (c1 c2 : conf) : Prop :=
    match c1, c2 with
    | cmd_st c s, cmd_st c' s' => (Lang.peq c c') /\ (State.peq s s')
    | end_st s, end_st s' => State.peq s s'
    | ab, ab => True
    | _, _ => False
    end.

Inductive sem : state -> cmd -> state -> Prop :=
| Skip : forall s, sem s Lang.skip s
| AsnE : forall x e s, sem s (Lang.assign x e)
  (State.map_stack (Stack.update x (Expr.eval e (State.get_stack s))) s)
| AsnB : forall x b s, sem s (Lang.assignb x b)
  (State.map_stack (Stack.update x (BExpr.bool2ref
    (BExpr.eval b (State.get_stack s)))) s)
| FldR : forall x v a r r' s, Stack.get v (State.get_stack s) = Some r
  -> Heap.get r a (State.get_heap s) = Some r'
    -> sem s (Lang.fread x v a) (State.map_stack (Stack.update x r') s)
| FldW : forall v a e r r' s, Stack.get v (State.get_stack s) = Some r
  -> Heap.get r a (State.get_heap s) = Some r'
    -> sem s (Lang.fwrite v a e) (State.map_heap
      (Heap.update r a (Expr.eval e (State.get_stack s))) s)
| Cast : forall x t v r s, Stack.get v (State.get_stack s) = Some r
  -> RType.subtype (Ref.get_type r) t (State.get_super_env s)
    -> sem s (Lang.cast x t v) (State.map_stack (Stack.update x r) s)
| CSeq : forall c1 c2 s1 s2 s3, sem s1 c1 s2 -> sem s2 c2 s3
  -> sem s1 (Lang.cseq c1 c2) s3
| CIf1 : forall b c1 c2 s1 s2, BExpr.eval b (State.get_stack s1) = true
  -> sem s1 c1 s2 -> sem s1 (Lang.cif b c1 c2) s2
| CIf2 : forall b c1 c2 s1 s2, BExpr.eval b (State.get_stack s1) = false
  -> sem s1 c2 s2 -> sem s1 (Lang.cif b c1 c2) s2
| Whl1 : forall b c s1 s2 s3, BExpr.eval b (State.get_stack s1) = true
  -> sem s1 c s2 -> sem s2 (Lang.cwhile b c) s3 -> sem s1 (Lang.cwhile b c) s3
| Whl2 : forall b c s1, BExpr.eval b (State.get_stack s1) = false
  -> sem s1 (Lang.cwhile b c) s1
| Allc : forall x t le c s1 s2 s3, alloc_pretreat x t le s1 = cmd_st c s2
  -> sem (State.map_stack (Stack.update x (Ref.get_new (State.get_alloc s1))) s2) c s3
    -> sem s1 (Lang.calloc x t le) s3
| DCal : forall x v m le c s1 s2 s3 r, dcall_pretreat x v m le s1 = cmd_st c s2
  -> Stack.get "res" (State.get_stack s2) = Some r
    -> sem (State.map_stack (Stack.update x r) s2) c s3
      -> sem s1 (Lang.dcall x v m le) s3
| SCal : forall x v t m le c s1 s2 s3 r, scall_pretreat x v t m le s1 = cmd_st c s2
  -> Stack.get "res" (State.get_stack s2) = Some r
    -> sem (State.map_stack (Stack.update x r) s2) c s3
      -> sem s1 (Lang.scall x v t m le) s3
| Ret  : forall e s, sem s (Lang.creturn e)
  (State.map_stack (Stack.update "res" (Expr.eval e (State.get_stack s))) s).

Open Scope state_scope.

(*
Lemma alloc_seq : forall x t le s c s',
    alloc_pretreat x t le s = cmd_st c s' -> s `=` s'.
Proof.
  intros x t le s c s' H.
  unfold alloc_pretreat in H.
  case (MEnv.find_mbody (State.get_mbody_env s) t t) in H.
  induction m as [[a l] oc]. induction oc.
Admitted.

Axiom mcall_seq : forall n n0 m l s c s',
    mcall_pretreat n n0 m l s = cmd_st c s' -> s `=` s'.
*)

Lemma sem_seq : forall (c : cmd) (s s' : state), sem s c s' -> s `=` s'.
Proof.
  induction c; try
  (intros s s' H; inversion H; apply State.seq_sym;
    (rewrite <- State.seq_map_stack || rewrite <- State.seq_map_heap);
    apply State.seq_refl).
  intros s s' H; inversion H. apply State.seq_refl.
  intros s s' H; inversion H.
  apply IHc1 in H3; apply IHc2 in H5.
  apply State.seq_trans with (y := s2); assumption.
  intros s s' H; inversion H.
  apply IHc1 in H6; assumption.
  apply IHc2 in H6; assumption.
  cut (forall c' s s', sem s c' s' -> c' = Lang.cwhile b c -> s `=` s'); eauto.
  intros c' s s' H.
  elim H; try (intros; discriminate).
  intros. inversion H5. rewrite H8 in H1.
  apply IHc in H1. apply H4 in H5.
  apply State.seq_trans with (y := s2); assumption.
  intros; inversion H1; apply State.seq_refl.
  intros s s' H; inversion H.
Admitted.

Close Scope state_scope.
Close Scope string_scope.

End Sem.