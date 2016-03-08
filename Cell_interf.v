Require Import Spec.
Require Import List.

(*  Example Cell with interface  *)

Definition Int := RType.Int.
Definition Null := RType.Null.
Definition state := State.state.
Definition init_state := State.init_state.
Definition pred := HProp.hprop.

Open Scope string_scope.
Open Scope lang_scope.
Open Scope hprop_scope.
Open Scope spec_scope.

Variable r : Ref.ref.

Definition no_locvar := TEnv.method_no_locvar.
Definition locvars := TEnv.update_method_locvars "c" Int no_locvar.

Module Cell. (* Class Cell *)
 (* fields declaration *)
 Definition fields := RType.update_field_type "x" Int.
 
 (* predicates declaration *)
 Definition cell : pred := .\(fun this => .\(fun v => this`"x" |-> v)).
 
 (* method get() *)
 Definition get_spec :=
     (|P|"cell"@"this"&r,
      |P|"cell"@"this"&r /.\ "res" +-> r).
 Definition get_cmd  := Lang.fread "c" "this" "x";
                       Lang.creturn (^"c").
 
 (* method set(v) *)
 Definition set_spec :=
     (|P|"cell"@"this"&r,
      |P|"cell"@"this"&^"v").
 Definition set_cmd  := Lang.fwrite "this" "x" (^"v").
 
 Definition declare (s : state) : state :=
     State.build_method "Cell" "get" (nil, Int) MEnv.no_args locvars get_cmd
     (State.build_method "Cell" "set" (Int::nil, Null) ("v"::nil) no_locvar set_cmd
     (State.build_class "Cell" (RType.Object::nil) fields s)).
End Cell.

Module Undoable. (* Interface Undoable *)
 Definition get_spec :=
     (|P|"cell"@"this"&r,
      |P|"cell"@"this"&r /.\ "res" +-> r).
 Definition set_spec :=
     (|P|"cell"@"this"&r,
      |P|"bak"@"this"&r /.\ |P|"cell"@"this"&^"v").
 Definition undo_spec :=
     (|P|"bak"@"this"&r,
      |P|"cell"@"this"&r).
 
 Definition declare (s : state) : state :=
     State.build_msign "Undoable" "undo" (nil, Null) MEnv.no_args
     (State.build_msign "Undoable" "get" (nil, Null) ("v"::nil)
     (State.build_msign "Undoable" "set" (Int::nil, Null) ("v"::nil)
     (State.build_interf "Undoable" None s))).
End Undoable.

Module ReCell. (* Class ReCell *)
 Definition fields := RType.update_field_type "y" Int.
 
 Definition cell : pred := .\(fun this => .\(fun v => 
     =| (fun r' => this`"x" |-> v * this`"y" |-> r'))).
 Definition bak : pred  := .\(fun this => .\(fun v => 
     =| (fun r' => this`"x" |-> r' * this`"y" |-> v))).
 
 Definition set_cmd  := Lang.fread "c" "this" "x";
                        Lang.fwrite "this" "y" (^"c");
                        Lang.fwrite "this" "x" (^"v").
 Definition undo_cmd := Lang.fread "c" "this" "y";
                        Lang.fwrite "this" "x" (^"c").
 
 Definition declare (s : state) : state :=
     State.build_method "ReCell" "undo" (nil, Null) MEnv.no_args locvars undo_cmd
     (State.build_method "ReCell" "set" (Int::nil, Null) ("v"::nil) locvars set_cmd
     (State.build_class "ReCell" ("Cell"::"Undoable"::nil) fields s)).
End ReCell.

(* Class Declarations *)
Definition program := ReCell.declare (Undoable.declare (Cell.declare init_state)).

(* Predicate Environment *)
Definition preds : Spec.pred_env :=
    Spec.update_pred "bak" "ReCell" ReCell.bak
    (Spec.update_pred "cell" "ReCell" ReCell.cell
    (Spec.update_pred "cell" "Cell" Cell.cell Spec.init_pred_env)).

(* Specification *)
Definition spec :=
    Spec.add_spec "ReCell" "undo" Undoable.undo_spec
    (Spec.add_spec "ReCell" "set" Undoable.set_spec
    (Spec.add_spec "ReCell" "get" Undoable.get_spec
    (Spec.add_spec "Undoable" "undo" Undoable.undo_spec
    (Spec.add_spec "Undoable" "set" Undoable.set_spec
    (Spec.add_spec "Undoable" "get" Undoable.get_spec
    (Spec.add_spec "Cell" "set" Cell.set_spec
    (Spec.add_spec "Cell" "get" Cell.get_spec Spec.init_program_spec))))))).

Ltac Unfold := unfold Spec.program_satisfy; unfold program at 1;
               unfold ReCell.declare; unfold Undoable.declare; unfold Cell.declare.

(* The only non-trivial behavioral subtype relation *)
Lemma recell_set_bs : Cell.set_spec <<= Undoable.set_spec.
Proof.
  unfold Undoable.set_spec; unfold Cell.set_spec.
  apply Spec.refine_cons1. impConj.
Qed.

(* Method Cell.get() satisfies its specification *)
Lemma cell_get_valid : program + preds |> spec # "Cell","get".
Proof.
  (* Unfold the predicate *)
  Simpl. unfold Cell.cell; param2. assoC'.
  (* Prove the method body satisfies its specification *)
  apply Spec.h_seq with (q := "this" +-> r0 /.\ r0`"x" |-> r /.\ "c" +-> r).
  lkp. apply Spec.h_res; simpl.
  rewrite HProp.var_exp; impConj.
  (* Prove the behavioral subtyping *)
  bs.
Qed.

Lemma cell_set_valid : program + preds |> spec # "Cell","set".
Proof.
  Simpl. unfold Cell.cell; param2; exconj.
  do 2 (commC1 ("v" +-> r0)); do 2 assoC'; mut "v". bs.
Qed.

Lemma recell_get_valid : program + preds |> spec # "ReCell","get".
Proof.
  Simpl. unfold ReCell.cell; param2; exconj. frame. assoC'.
  apply Spec.h_seq with (q := "this" +-> r0 /.\ r0`"x" |-> r /.\ "c" +-> r).
  lkp. apply Spec.h_res; simpl.
  rewrite HProp.var_exp; impConj. bs.
Qed.

Lemma recell_set_valid : program + preds |> spec # "ReCell","set".
Proof.
  Simpl. unfold ReCell.cell; unfold ReCell.bak;
  exconj1; param2. exconj1; exconj2 r0; exconj2 r0;
  exconj2 r1; exconj2 r. do 2 (commC1 ("v" +-> r0)).
  assoC; rewrite HProp.conj_refl; do 2 assoC'.
  apply Spec.h_seq with (q := "c" +-> r /.\ "this" +-> r1 /.\ r1`"x" |-> r
    * r1`"y" |-> r2 /.\ "v" +-> r0).
  frame. do 2 assoC; frame'.
  commC1 ("c" +-> r); assoC'; lkp.
  apply Spec.h_seq with (q := "this" +-> r1 /.\ r1`"x" |-> r * r1`"y" |-> r
    /.\ "v" +-> r0). do 3 assoC; frame'.
  assoC'; do 2 (commSC1 (r1 ` "x" |-> r)); frame. commC.
  apply Spec.h_cons_1 with (p2 := ("this" +-> r1 /.\ r1`"y" |-> r) /.\ "c" +-> r).
  impConj. do 2 rewrite <- HProp.conj_asso; mut "c". frame. mut "v".
  bs. apply recell_set_bs.
Qed.

Lemma recell_undo_valid : program + preds |> spec # "ReCell", "undo".
Proof.
  Simpl. unfold ReCell.cell; unfold ReCell.bak; param2.
  exconj1; exconj2 r.
  apply Spec.h_seq with (q := "this" +-> r0 /.\ r0`"x" |-> r1 * r0`"y" |-> r
    /.\ "c" +-> r). commSC; frame. lkp. frame.
  apply Spec.h_cons_1 with (p2 := "this" +-> r0 /.\ r0`"x" |-> r /.\ "c" +-> r).
  assoC; impConj. mut "c". bs.
Qed.

Lemma CC : "Cell" = "Cell" <-> True.
Proof. split; eauto. Qed.
Lemma gC : "get" <> "Cell" <-> True.
Proof. split; [eauto | discriminate]. Qed.
Lemma sC : "set" <> "Cell" <-> True.
Proof. split; [eauto | discriminate]. Qed.

(* The whole program satisfies its specification *)
Lemma verify_cell : program + preds |= spec.
Proof.
  Unfold; mlist. rewrite CC in H. propSimp H.
  rewrite gC in H; rewrite sC in H; propSimp H.
  mtdSpec recell_undo_valid.
  mtdSpec recell_set_valid.
  mtdSpec recell_get_valid.
  mtdSpec cell_get_valid.
  mtdSpec cell_set_valid.
Qed.

Close Scope spec_scope.
Close Scope hprop_scope.
Close Scope lang_scope.
Close Scope string_scope.