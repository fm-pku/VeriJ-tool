Require Export Heap.
Require Export Env.

(*-----  Abstract Data Type  -----*)

(*  State  *)

Module Type STATE.

Parameter heap : Type.
Parameter stack : Type.
Parameter alloc : Type.

Parameter dtype : Type.
Parameter fields_env : Type.
Parameter super_env : Type.
Parameter cnames : Type.
Parameter methods_env : Type.
Parameter locvars_env : Type.
Parameter mbody_env : Type.

Parameter name : Type.
Parameter method : Type.
Parameter method_type : Type.
Parameter method_locvars : Type.
Parameter rtype : Type.
Parameter field_type : Type.
Parameter args : Type.
Parameter locvars : Type.
Parameter cmd : Type.

Parameter state : Type.
Parameter init_state : state.

Parameter get_heap : state -> heap.
Parameter update_heap : heap -> state -> state.
Parameter map_heap : (heap -> heap) -> state -> state.
Parameter get_stack : state -> stack.
Parameter update_stack : stack -> state -> state.
Parameter map_stack : (stack -> stack) -> state -> state.
Parameter get_alloc : state -> alloc.
Parameter update_alloc : alloc -> state -> state.
Parameter map_alloc : (alloc -> alloc) -> state -> state.
Parameter get_dtype : state -> dtype.
Parameter update_dtype : dtype -> state -> state.
Parameter map_dtype : (dtype -> dtype) -> state -> state.
Parameter get_fields_env : state -> fields_env.
Parameter update_fields_env : fields_env -> state -> state.
Parameter map_fields_env : (fields_env -> fields_env) -> state -> state.
Parameter get_super_env : state -> super_env.
Parameter update_super_env : super_env -> state -> state.
Parameter map_super_env : (super_env -> super_env) -> state -> state.
Parameter get_cnames : state -> cnames.
Parameter update_cnames : cnames -> state -> state.
Parameter map_cnames : (cnames -> cnames) -> state -> state.
Parameter get_methods_env : state -> methods_env.
Parameter update_methods_env : methods_env -> state -> state.
Parameter map_methods_env : (methods_env -> methods_env) -> state -> state.
Parameter get_locvars_env : state -> locvars_env.
Parameter update_locvars_env : locvars_env -> state -> state.
Parameter map_locvars_env : (locvars_env -> locvars_env) -> state -> state.
Parameter get_mbody_env : state -> mbody_env.
Parameter update_mbody_env : mbody_env -> state -> state.
Parameter map_mbody_env : (mbody_env -> mbody_env) -> state -> state.

Parameter build_class : rtype -> list rtype -> (field_type -> field_type) ->
                        state -> state.
Parameter build_method : rtype -> method -> method_type -> args ->
                         method_locvars -> cmd -> state -> state.
Parameter build_interf : rtype -> option rtype -> state -> state.
Parameter build_msign : rtype -> method -> method_type -> args -> state -> state.
Parameter new_obj : name -> rtype -> state -> state.

Parameter beq : state -> state -> bool.
Parameter peq : state -> state -> Prop.
Parameter seq : state -> state -> Prop.

Axiom seq_peq : forall s1 s2 : state, peq s1 s2 -> seq s1 s2.

Axiom seq_subst : forall s1 s2 : state, seq s1 s2 ->
    (update_heap (get_heap s2) (update_stack (get_stack s2) s1)) = s2.
Axiom seq_update_heap : forall (h : heap) (s1 s2 : state),
    seq s1 s2 <-> seq (update_heap h s1) s2.
Axiom seq_update_stack : forall (st : stack) (s1 s2 : state),
    seq s1 s2 <-> seq (update_stack st s1) s2.
Axiom seq_map_heap : forall (mh : heap -> heap) (s1 s2 : state),
    seq s1 s2 <-> seq (map_heap mh s1) s2.
Axiom seq_map_stack : forall (ms : stack -> stack) (s1 s2 : state),
    seq s1 s2 <-> seq (map_stack ms s1) s2.

Axiom seq_refl : forall x : state, seq x x.
Axiom seq_sym : forall x y : state, seq x y -> seq y x.
Axiom seq_trans : forall x y z : state, seq x y -> seq y z -> seq x z.

Axiom equal_1 : forall s1 s2 : state, peq s1 s2 -> beq s1 s2 = true.
Axiom equal_2 : forall s1 s2 : state, beq s1 s2 = true -> peq s1 s2.
Axiom equal_3 : forall s1 s2 : state, s1 = s2 <-> peq s1 s2.

Axiom get_after_map_00 : forall (mh : heap -> heap) (s : state),
                           get_heap (map_heap mh s) = mh (get_heap s).
Axiom get_after_map_01 : forall (ms : stack -> stack) (s : state),
                           get_heap (map_stack ms s) = get_heap s.
Axiom get_after_map_02 : forall (ma : alloc -> alloc) (s : state),
                           get_heap (map_alloc ma s) = get_heap s.
Axiom get_after_map_03 : forall (md : dtype -> dtype) (s : state),
                           get_heap (map_dtype md s) = get_heap s.
Axiom get_after_map_04 : forall (mf : fields_env -> fields_env) (s : state),
                           get_heap (map_fields_env mf s) = get_heap s.
Axiom get_after_map_05 : forall (ms : super_env -> super_env) (s : state),
                           get_heap (map_super_env ms s) = get_heap s.
Axiom get_after_map_06 : forall (mc : cnames -> cnames) (s : state),
                           get_heap (map_cnames mc s) = get_heap s.
Axiom get_after_map_07 : forall (mm : methods_env -> methods_env) (s : state),
                           get_heap (map_methods_env mm s) = get_heap s.
Axiom get_after_map_08 : forall (ml : locvars_env -> locvars_env) (s : state),
                           get_heap (map_locvars_env ml s) = get_heap s.
Axiom get_after_map_09 : forall (mm : mbody_env -> mbody_env) (s : state),
                           get_heap (map_mbody_env mm s) = get_heap s.
Axiom get_after_map_10 : forall (mh : heap -> heap) (s : state),
                           get_stack (map_heap mh s) = get_stack s.
Axiom get_after_map_11 : forall (ms : stack -> stack) (s : state),
                           get_stack (map_stack ms s) = ms (get_stack s).
Axiom get_after_map_12 : forall (ma : alloc -> alloc) (s : state),
                           get_stack (map_alloc ma s) = get_stack s.
Axiom get_after_map_13 : forall (md : dtype -> dtype) (s : state),
                           get_stack (map_dtype md s) = get_stack s.
Axiom get_after_map_14 : forall (mf : fields_env -> fields_env) (s : state),
                           get_stack (map_fields_env mf s) = get_stack s.
Axiom get_after_map_15 : forall (ms : super_env -> super_env) (s : state),
                           get_stack (map_super_env ms s) = get_stack s.
Axiom get_after_map_16 : forall (mc : cnames -> cnames) (s : state),
                           get_stack (map_cnames mc s) = get_stack s.
Axiom get_after_map_17 : forall (mm : methods_env -> methods_env) (s : state),
                           get_stack (map_methods_env mm s) = get_stack s.
Axiom get_after_map_18 : forall (ml : locvars_env -> locvars_env) (s : state),
                           get_stack (map_locvars_env ml s) = get_stack s.
Axiom get_after_map_19 : forall (mm : mbody_env -> mbody_env) (s : state),
                           get_stack (map_mbody_env mm s) = get_stack s.
Axiom get_after_map_20 : forall (mh : heap -> heap) (s : state),
                           get_alloc (map_heap mh s) = get_alloc s.
Axiom get_after_map_21 : forall (ms : stack -> stack) (s : state),
                           get_alloc (map_stack ms s) = get_alloc s.
Axiom get_after_map_22 : forall (ma : alloc -> alloc) (s : state),
                           get_alloc (map_alloc ma s) = ma (get_alloc s).
Axiom get_after_map_23 : forall (md : dtype -> dtype) (s : state),
                           get_alloc (map_dtype md s) = get_alloc s.
Axiom get_after_map_24 : forall (mf : fields_env -> fields_env) (s : state),
                           get_alloc (map_fields_env mf s) = get_alloc s.
Axiom get_after_map_25 : forall (ms : super_env -> super_env) (s : state),
                           get_alloc (map_super_env ms s) = get_alloc s.
Axiom get_after_map_26 : forall (mc : cnames -> cnames) (s : state),
                           get_alloc (map_cnames mc s) = get_alloc s.
Axiom get_after_map_27 : forall (mm : methods_env -> methods_env) (s : state),
                           get_alloc (map_methods_env mm s) = get_alloc s.
Axiom get_after_map_28 : forall (ml : locvars_env -> locvars_env) (s : state),
                           get_alloc (map_locvars_env ml s) = get_alloc s.
Axiom get_after_map_29 : forall (mm : mbody_env -> mbody_env) (s : state),
                           get_alloc (map_mbody_env mm s) = get_alloc s.
Axiom get_after_map_30 : forall (mh : heap -> heap) (s : state),
                           get_dtype (map_heap mh s) = get_dtype s.
Axiom get_after_map_31 : forall (ms : stack -> stack) (s : state),
                           get_dtype (map_stack ms s) = get_dtype s.
Axiom get_after_map_32 : forall (ma : alloc -> alloc) (s : state),
                           get_dtype (map_alloc ma s) = get_dtype s.
Axiom get_after_map_33 : forall (md : dtype -> dtype) (s : state),
                           get_dtype (map_dtype md s) = md (get_dtype s).
Axiom get_after_map_34 : forall (mf : fields_env -> fields_env) (s : state),
                           get_dtype (map_fields_env mf s) = get_dtype s.
Axiom get_after_map_35 : forall (ms : super_env -> super_env) (s : state),
                           get_dtype (map_super_env ms s) = get_dtype s.
Axiom get_after_map_36 : forall (mc : cnames -> cnames) (s : state),
                           get_dtype (map_cnames mc s) = get_dtype s.
Axiom get_after_map_37 : forall (mm : methods_env -> methods_env) (s : state),
                           get_dtype (map_methods_env mm s) = get_dtype s.
Axiom get_after_map_38 : forall (ml : locvars_env -> locvars_env) (s : state),
                           get_dtype (map_locvars_env ml s) = get_dtype s.
Axiom get_after_map_39 : forall (mm : mbody_env -> mbody_env) (s : state),
                           get_dtype (map_mbody_env mm s) = get_dtype s.
Axiom get_after_map_40 : forall (mh : heap -> heap) (s : state),
                           get_fields_env (map_heap mh s) = get_fields_env s.
Axiom get_after_map_41 : forall (ms : stack -> stack) (s : state),
                           get_fields_env (map_stack ms s) = get_fields_env s.
Axiom get_after_map_42 : forall (ma : alloc -> alloc) (s : state),
                           get_fields_env (map_alloc ma s) = get_fields_env s.
Axiom get_after_map_43 : forall (md : dtype -> dtype) (s : state),
                           get_fields_env (map_dtype md s) = get_fields_env s.
Axiom get_after_map_44 : forall (mf : fields_env -> fields_env) (s : state),
                           get_fields_env (map_fields_env mf s) = mf (get_fields_env s).
Axiom get_after_map_45 : forall (ms : super_env -> super_env) (s : state),
                           get_fields_env (map_super_env ms s) = get_fields_env s.
Axiom get_after_map_46 : forall (mc : cnames -> cnames) (s : state),
                           get_fields_env (map_cnames mc s) = get_fields_env s.
Axiom get_after_map_47 : forall (mm : methods_env -> methods_env) (s : state),
                           get_fields_env (map_methods_env mm s) = get_fields_env s.
Axiom get_after_map_48 : forall (ml : locvars_env -> locvars_env) (s : state),
                           get_fields_env (map_locvars_env ml s) = get_fields_env s.
Axiom get_after_map_49 : forall (mm : mbody_env -> mbody_env) (s : state),
                           get_fields_env (map_mbody_env mm s) = get_fields_env s.
Axiom get_after_map_50 : forall (mh : heap -> heap) (s : state),
                           get_super_env (map_heap mh s) = get_super_env s.
Axiom get_after_map_51 : forall (ms : stack -> stack) (s : state),
                           get_super_env (map_stack ms s) = get_super_env s.
Axiom get_after_map_52 : forall (ma : alloc -> alloc) (s : state),
                           get_super_env (map_alloc ma s) = get_super_env s.
Axiom get_after_map_53 : forall (md : dtype -> dtype) (s : state),
                           get_super_env (map_dtype md s) = get_super_env s.
Axiom get_after_map_54 : forall (mf : fields_env -> fields_env) (s : state),
                           get_super_env (map_fields_env mf s) = get_super_env s.
Axiom get_after_map_55 : forall (ms : super_env -> super_env) (s : state),
                           get_super_env (map_super_env ms s) = ms (get_super_env s).
Axiom get_after_map_56 : forall (mc : cnames -> cnames) (s : state),
                           get_super_env (map_cnames mc s) = get_super_env s.
Axiom get_after_map_57 : forall (mm : methods_env -> methods_env) (s : state),
                           get_super_env (map_methods_env mm s) = get_super_env s.
Axiom get_after_map_58 : forall (ml : locvars_env -> locvars_env) (s : state),
                           get_super_env (map_locvars_env ml s) = get_super_env s.
Axiom get_after_map_59 : forall (mm : mbody_env -> mbody_env) (s : state),
                           get_super_env (map_mbody_env mm s) = get_super_env s.
Axiom get_after_map_60 : forall (mh : heap -> heap) (s : state),
                           get_cnames (map_heap mh s) = get_cnames s.
Axiom get_after_map_61 : forall (ms : stack -> stack) (s : state),
                           get_cnames (map_stack ms s) = get_cnames s.
Axiom get_after_map_62 : forall (ma : alloc -> alloc) (s : state),
                           get_cnames (map_alloc ma s) = get_cnames s.
Axiom get_after_map_63 : forall (md : dtype -> dtype) (s : state),
                           get_cnames (map_dtype md s) = get_cnames s.
Axiom get_after_map_64 : forall (mf : fields_env -> fields_env) (s : state),
                           get_cnames (map_fields_env mf s) = get_cnames s.
Axiom get_after_map_65 : forall (ms : super_env -> super_env) (s : state),
                           get_cnames (map_super_env ms s) = get_cnames s.
Axiom get_after_map_66 : forall (mc : cnames -> cnames) (s : state),
                           get_cnames (map_cnames mc s) = mc (get_cnames s).
Axiom get_after_map_67 : forall (mm : methods_env -> methods_env) (s : state),
                           get_cnames (map_methods_env mm s) = get_cnames s.
Axiom get_after_map_68 : forall (ml : locvars_env -> locvars_env) (s : state),
                           get_cnames (map_locvars_env ml s) = get_cnames s.
Axiom get_after_map_69 : forall (mm : mbody_env -> mbody_env) (s : state),
                           get_cnames (map_mbody_env mm s) = get_cnames s.
Axiom get_after_map_70 : forall (mh : heap -> heap) (s : state),
                           get_methods_env (map_heap mh s) = get_methods_env s.
Axiom get_after_map_71 : forall (ms : stack -> stack) (s : state),
                           get_methods_env (map_stack ms s) = get_methods_env s.
Axiom get_after_map_72 : forall (ma : alloc -> alloc) (s : state),
                           get_methods_env (map_alloc ma s) = get_methods_env s.
Axiom get_after_map_73 : forall (md : dtype -> dtype) (s : state),
                           get_methods_env (map_dtype md s) = get_methods_env s.
Axiom get_after_map_74 : forall (mf : fields_env -> fields_env) (s : state),
                           get_methods_env (map_fields_env mf s) = get_methods_env s.
Axiom get_after_map_75 : forall (ms : super_env -> super_env) (s : state),
                           get_methods_env (map_super_env ms s) = get_methods_env s.
Axiom get_after_map_76 : forall (mc : cnames -> cnames) (s : state),
                           get_methods_env (map_cnames mc s) = get_methods_env s.
Axiom get_after_map_77 : forall (mm : methods_env -> methods_env) (s : state),
                           get_methods_env (map_methods_env mm s) = mm (get_methods_env s).
Axiom get_after_map_78 : forall (ml : locvars_env -> locvars_env) (s : state),
                           get_methods_env (map_locvars_env ml s) = get_methods_env s.
Axiom get_after_map_79 : forall (mm : mbody_env -> mbody_env) (s : state),
                           get_methods_env (map_mbody_env mm s) = get_methods_env s.
Axiom get_after_map_80 : forall (mh : heap -> heap) (s : state),
                           get_locvars_env (map_heap mh s) = get_locvars_env s.
Axiom get_after_map_81 : forall (ms : stack -> stack) (s : state),
                           get_locvars_env (map_stack ms s) = get_locvars_env s.
Axiom get_after_map_82 : forall (ma : alloc -> alloc) (s : state),
                           get_locvars_env (map_alloc ma s) = get_locvars_env s.
Axiom get_after_map_83 : forall (md : dtype -> dtype) (s : state),
                           get_locvars_env (map_dtype md s) = get_locvars_env s.
Axiom get_after_map_84 : forall (mf : fields_env -> fields_env) (s : state),
                           get_locvars_env (map_fields_env mf s) = get_locvars_env s.
Axiom get_after_map_85 : forall (ms : super_env -> super_env) (s : state),
                           get_locvars_env (map_super_env ms s) = get_locvars_env s.
Axiom get_after_map_86 : forall (mc : cnames -> cnames) (s : state),
                           get_locvars_env (map_cnames mc s) = get_locvars_env s.
Axiom get_after_map_87 : forall (mm : methods_env -> methods_env) (s : state),
                           get_locvars_env (map_methods_env mm s) = get_locvars_env s.
Axiom get_after_map_88 : forall (ml : locvars_env -> locvars_env) (s : state),
                           get_locvars_env (map_locvars_env ml s) = ml (get_locvars_env s).
Axiom get_after_map_89 : forall (mm : mbody_env -> mbody_env) (s : state),
                           get_locvars_env (map_mbody_env mm s) = get_locvars_env s.
Axiom get_after_map_90 : forall (mh : heap -> heap) (s : state),
                           get_mbody_env (map_heap mh s) = get_mbody_env s.
Axiom get_after_map_91 : forall (ms : stack -> stack) (s : state),
                           get_mbody_env (map_stack ms s) = get_mbody_env s.
Axiom get_after_map_92 : forall (ma : alloc -> alloc) (s : state),
                           get_mbody_env (map_alloc ma s) = get_mbody_env s.
Axiom get_after_map_93 : forall (md : dtype -> dtype) (s : state),
                           get_mbody_env (map_dtype md s) = get_mbody_env s.
Axiom get_after_map_94 : forall (mf : fields_env -> fields_env) (s : state),
                           get_mbody_env (map_fields_env mf s) = get_mbody_env s.
Axiom get_after_map_95 : forall (ms : super_env -> super_env) (s : state),
                           get_mbody_env (map_super_env ms s) = get_mbody_env s.
Axiom get_after_map_96 : forall (mc : cnames -> cnames) (s : state),
                           get_mbody_env (map_cnames mc s) = get_mbody_env s.
Axiom get_after_map_97 : forall (mm : methods_env -> methods_env) (s : state),
                           get_mbody_env (map_methods_env mm s) = get_mbody_env s.
Axiom get_after_map_98 : forall (ml : locvars_env -> locvars_env) (s : state),
                           get_mbody_env (map_locvars_env ml s) = get_mbody_env s.
Axiom get_after_map_99 : forall (mm : mbody_env -> mbody_env) (s : state),
                           get_mbody_env (map_mbody_env mm s) = mm (get_mbody_env s).

Axiom get_after_update_00 : forall (h : heap) (s : state),
                           get_heap (update_heap h s) = h.
Axiom get_after_update_01 : forall (s' : stack) (s : state),
                           get_heap (update_stack s' s) = get_heap s.
Axiom get_after_update_02 : forall (a : alloc) (s : state),
                           get_heap (update_alloc a s) = get_heap s.
Axiom get_after_update_03 : forall (d : dtype) (s : state),
                           get_heap (update_dtype d s) = get_heap s.
Axiom get_after_update_04 : forall (f : fields_env) (s : state),
                           get_heap (update_fields_env f s) = get_heap s.
Axiom get_after_update_05 : forall (s' : super_env) (s : state),
                           get_heap (update_super_env s' s) = get_heap s.
Axiom get_after_update_06 : forall (c : cnames) (s : state),
                           get_heap (update_cnames c s) = get_heap s.
Axiom get_after_update_07 : forall (m : methods_env) (s : state),
                           get_heap (update_methods_env m s) = get_heap s.
Axiom get_after_update_08 : forall (l : locvars_env) (s : state),
                           get_heap (update_locvars_env l s) = get_heap s.
Axiom get_after_update_09 : forall (m : mbody_env) (s : state),
                           get_heap (update_mbody_env m s) = get_heap s.
Axiom get_after_update_10 : forall (h : heap) (s : state),
                           get_stack (update_heap h s) = get_stack s.
Axiom get_after_update_11 : forall (s' : stack) (s : state),
                           get_stack (update_stack s' s) = s'.
Axiom get_after_update_12 : forall (a : alloc) (s : state),
                           get_stack (update_alloc a s) = get_stack s.
Axiom get_after_update_13 : forall (d : dtype) (s : state),
                           get_stack (update_dtype d s) = get_stack s.
Axiom get_after_update_14 : forall (f : fields_env) (s : state),
                           get_stack (update_fields_env f s) = get_stack s.
Axiom get_after_update_15 : forall (s' : super_env) (s : state),
                           get_stack (update_super_env s' s) = get_stack s.
Axiom get_after_update_16 : forall (c : cnames) (s : state),
                           get_stack (update_cnames c s) = get_stack s.
Axiom get_after_update_17 : forall (m : methods_env) (s : state),
                           get_stack (update_methods_env m s) = get_stack s.
Axiom get_after_update_18 : forall (l : locvars_env) (s : state),
                           get_stack (update_locvars_env l s) = get_stack s.
Axiom get_after_update_19 : forall (m : mbody_env) (s : state),
                           get_stack (update_mbody_env m s) = get_stack s.
Axiom get_after_update_20 : forall (h : heap) (s : state),
                           get_alloc (update_heap h s) = get_alloc s.
Axiom get_after_update_21 : forall (s' : stack) (s : state),
                           get_alloc (update_stack s' s) = get_alloc s.
Axiom get_after_update_22 : forall (a : alloc) (s : state),
                           get_alloc (update_alloc a s) = a.
Axiom get_after_update_23 : forall (d : dtype) (s : state),
                           get_alloc (update_dtype d s) = get_alloc s.
Axiom get_after_update_24 : forall (f : fields_env) (s : state),
                           get_alloc (update_fields_env f s) = get_alloc s.
Axiom get_after_update_25 : forall (s' : super_env) (s : state),
                           get_alloc (update_super_env s' s) = get_alloc s.
Axiom get_after_update_26 : forall (c : cnames) (s : state),
                           get_alloc (update_cnames c s) = get_alloc s.
Axiom get_after_update_27 : forall (m : methods_env) (s : state),
                           get_alloc (update_methods_env m s) = get_alloc s.
Axiom get_after_update_28 : forall (l : locvars_env) (s : state),
                           get_alloc (update_locvars_env l s) = get_alloc s.
Axiom get_after_update_29 : forall (m : mbody_env) (s : state),
                           get_alloc (update_mbody_env m s) = get_alloc s.
Axiom get_after_update_30 : forall (h : heap) (s : state),
                           get_dtype (update_heap h s) = get_dtype s.
Axiom get_after_update_31 : forall (s' : stack) (s : state),
                           get_dtype (update_stack s' s) = get_dtype s.
Axiom get_after_update_32 : forall (a : alloc) (s : state),
                           get_dtype (update_alloc a s) = get_dtype s.
Axiom get_after_update_33 : forall (d : dtype) (s : state),
                           get_dtype (update_dtype d s) = d.
Axiom get_after_update_34 : forall (f : fields_env) (s : state),
                           get_dtype (update_fields_env f s) = get_dtype s.
Axiom get_after_update_35 : forall (s' : super_env) (s : state),
                           get_dtype (update_super_env s' s) = get_dtype s.
Axiom get_after_update_36 : forall (c : cnames) (s : state),
                           get_dtype (update_cnames c s) = get_dtype s.
Axiom get_after_update_37 : forall (m : methods_env) (s : state),
                           get_dtype (update_methods_env m s) = get_dtype s.
Axiom get_after_update_38 : forall (l : locvars_env) (s : state),
                           get_dtype (update_locvars_env l s) = get_dtype s.
Axiom get_after_update_39 : forall (m : mbody_env) (s : state),
                           get_dtype (update_mbody_env m s) = get_dtype s.
Axiom get_after_update_40 : forall (h : heap) (s : state),
                           get_fields_env (update_heap h s) = get_fields_env s.
Axiom get_after_update_41 : forall (s' : stack) (s : state),
                           get_fields_env (update_stack s' s) = get_fields_env s.
Axiom get_after_update_42 : forall (a : alloc) (s : state),
                           get_fields_env (update_alloc a s) = get_fields_env s.
Axiom get_after_update_43 : forall (d : dtype) (s : state),
                           get_fields_env (update_dtype d s) = get_fields_env s.
Axiom get_after_update_44 : forall (f : fields_env) (s : state),
                           get_fields_env (update_fields_env f s) = f.
Axiom get_after_update_45 : forall (s' : super_env) (s : state),
                           get_fields_env (update_super_env s' s) = get_fields_env s.
Axiom get_after_update_46 : forall (c : cnames) (s : state),
                           get_fields_env (update_cnames c s) = get_fields_env s.
Axiom get_after_update_47 : forall (m : methods_env) (s : state),
                           get_fields_env (update_methods_env m s) = get_fields_env s.
Axiom get_after_update_48 : forall (l : locvars_env) (s : state),
                           get_fields_env (update_locvars_env l s) = get_fields_env s.
Axiom get_after_update_49 : forall (m : mbody_env) (s : state),
                           get_fields_env (update_mbody_env m s) = get_fields_env s.
Axiom get_after_update_50 : forall (h : heap) (s : state),
                           get_super_env (update_heap h s) = get_super_env s.
Axiom get_after_update_51 : forall (s' : stack) (s : state),
                           get_super_env (update_stack s' s) = get_super_env s.
Axiom get_after_update_52 : forall (a : alloc) (s : state),
                           get_super_env (update_alloc a s) = get_super_env s.
Axiom get_after_update_53 : forall (d : dtype) (s : state),
                           get_super_env (update_dtype d s) = get_super_env s.
Axiom get_after_update_54 : forall (f : fields_env) (s : state),
                           get_super_env (update_fields_env f s) = get_super_env s.
Axiom get_after_update_55 : forall (s' : super_env) (s : state),
                           get_super_env (update_super_env s' s) = s'.
Axiom get_after_update_56 : forall (c : cnames) (s : state),
                           get_super_env (update_cnames c s) = get_super_env s.
Axiom get_after_update_57 : forall (m : methods_env) (s : state),
                           get_super_env (update_methods_env m s) = get_super_env s.
Axiom get_after_update_58 : forall (l : locvars_env) (s : state),
                           get_super_env (update_locvars_env l s) = get_super_env s.
Axiom get_after_update_59 : forall (m : mbody_env) (s : state),
                           get_super_env (update_mbody_env m s) = get_super_env s.
Axiom get_after_update_60 : forall (h : heap) (s : state),
                           get_cnames (update_heap h s) = get_cnames s.
Axiom get_after_update_61 : forall (s' : stack) (s : state),
                           get_cnames (update_stack s' s) = get_cnames s.
Axiom get_after_update_62 : forall (a : alloc) (s : state),
                           get_cnames (update_alloc a s) = get_cnames s.
Axiom get_after_update_63 : forall (d : dtype) (s : state),
                           get_cnames (update_dtype d s) = get_cnames s.
Axiom get_after_update_64 : forall (f : fields_env) (s : state),
                           get_cnames (update_fields_env f s) = get_cnames s.
Axiom get_after_update_65 : forall (s' : super_env) (s : state),
                           get_cnames (update_super_env s' s) = get_cnames s.
Axiom get_after_update_66 : forall (c : cnames) (s : state),
                           get_cnames (update_cnames c s) = c.
Axiom get_after_update_67 : forall (m : methods_env) (s : state),
                           get_cnames (update_methods_env m s) = get_cnames s.
Axiom get_after_update_68 : forall (l : locvars_env) (s : state),
                           get_cnames (update_locvars_env l s) = get_cnames s.
Axiom get_after_update_69 : forall (m : mbody_env) (s : state),
                           get_cnames (update_mbody_env m s) = get_cnames s.
Axiom get_after_update_70 : forall (h : heap) (s : state),
                           get_methods_env (update_heap h s) = get_methods_env s.
Axiom get_after_update_71 : forall (s' : stack) (s : state),
                           get_methods_env (update_stack s' s) = get_methods_env s.
Axiom get_after_update_72 : forall (a : alloc) (s : state),
                           get_methods_env (update_alloc a s) = get_methods_env s.
Axiom get_after_update_73 : forall (d : dtype) (s : state),
                           get_methods_env (update_dtype d s) = get_methods_env s.
Axiom get_after_update_74 : forall (f : fields_env) (s : state),
                           get_methods_env (update_fields_env f s) = get_methods_env s.
Axiom get_after_update_75 : forall (s' : super_env) (s : state),
                           get_methods_env (update_super_env s' s) = get_methods_env s.
Axiom get_after_update_76 : forall (c : cnames) (s : state),
                           get_methods_env (update_cnames c s) = get_methods_env s.
Axiom get_after_update_77 : forall (m : methods_env) (s : state),
                           get_methods_env (update_methods_env m s) = m.
Axiom get_after_update_78 : forall (l : locvars_env) (s : state),
                           get_methods_env (update_locvars_env l s) = get_methods_env s.
Axiom get_after_update_79 : forall (m : mbody_env) (s : state),
                           get_methods_env (update_mbody_env m s) = get_methods_env s.
Axiom get_after_update_80 : forall (h : heap) (s : state),
                           get_locvars_env (update_heap h s) = get_locvars_env s.
Axiom get_after_update_81 : forall (s' : stack) (s : state),
                           get_locvars_env (update_stack s' s) = get_locvars_env s.
Axiom get_after_update_82 : forall (a : alloc) (s : state),
                           get_locvars_env (update_alloc a s) = get_locvars_env s.
Axiom get_after_update_83 : forall (d : dtype) (s : state),
                           get_locvars_env (update_dtype d s) = get_locvars_env s.
Axiom get_after_update_84 : forall (f : fields_env) (s : state),
                           get_locvars_env (update_fields_env f s) = get_locvars_env s.
Axiom get_after_update_85 : forall (s' : super_env) (s : state),
                           get_locvars_env (update_super_env s' s) = get_locvars_env s.
Axiom get_after_update_86 : forall (c : cnames) (s : state),
                           get_locvars_env (update_cnames c s) = get_locvars_env s.
Axiom get_after_update_87 : forall (m : methods_env) (s : state),
                           get_locvars_env (update_methods_env m s) = get_locvars_env s.
Axiom get_after_update_88 : forall (l : locvars_env) (s : state),
                           get_locvars_env (update_locvars_env l s) = l.
Axiom get_after_update_89 : forall (m : mbody_env) (s : state),
                           get_locvars_env (update_mbody_env m s) = get_locvars_env s.
Axiom get_after_update_90 : forall (h : heap) (s : state),
                           get_mbody_env (update_heap h s) = get_mbody_env s.
Axiom get_after_update_91 : forall (s' : stack) (s : state),
                           get_mbody_env (update_stack s' s) = get_mbody_env s.
Axiom get_after_update_92 : forall (a : alloc) (s : state),
                           get_mbody_env (update_alloc a s) = get_mbody_env s.
Axiom get_after_update_93 : forall (d : dtype) (s : state),
                           get_mbody_env (update_dtype d s) = get_mbody_env s.
Axiom get_after_update_94 : forall (f : fields_env) (s : state),
                           get_mbody_env (update_fields_env f s) = get_mbody_env s.
Axiom get_after_update_95 : forall (s' : super_env) (s : state),
                           get_mbody_env (update_super_env s' s) = get_mbody_env s.
Axiom get_after_update_96 : forall (c : cnames) (s : state),
                           get_mbody_env (update_cnames c s) = get_mbody_env s.
Axiom get_after_update_97 : forall (m : methods_env) (s : state),
                           get_mbody_env (update_methods_env m s) = get_mbody_env s.
Axiom get_after_update_98 : forall (l : locvars_env) (s : state),
                           get_mbody_env (update_locvars_env l s) = get_mbody_env s.
Axiom get_after_update_99 : forall (m : mbody_env) (s : state),
                           get_mbody_env (update_mbody_env m s) = m.

Axiom map_comm_01 : forall (mh : heap -> heap) (ms : stack -> stack) (s : state),
                    map_heap mh (map_stack ms s) = map_stack ms (map_heap mh s).
Axiom map_comm_02 : forall (mh : heap -> heap) (ma : alloc -> alloc) (s : state),
                    map_heap mh (map_alloc ma s) = map_alloc ma (map_heap mh s).
Axiom map_comm_03 : forall (mh : heap -> heap) (md : dtype -> dtype) (s : state),
                    map_heap mh (map_dtype md s) = map_dtype md (map_heap mh s).
Axiom map_comm_04 : forall (mh : heap -> heap) (mf : fields_env -> fields_env) (s : state),
                    map_heap mh (map_fields_env mf s) = map_fields_env mf (map_heap mh s).
Axiom map_comm_05 : forall (mh : heap -> heap) (ms : super_env -> super_env) (s : state),
                    map_heap mh (map_super_env ms s) = map_super_env ms (map_heap mh s).
Axiom map_comm_06 : forall (mh : heap -> heap) (mc : cnames -> cnames) (s : state),
                    map_heap mh (map_cnames mc s) = map_cnames mc (map_heap mh s).
Axiom map_comm_07 : forall (mh : heap -> heap) (mm : methods_env -> methods_env) (s : state),
                    map_heap mh (map_methods_env mm s) = map_methods_env mm (map_heap mh s).
Axiom map_comm_08 : forall (mh : heap -> heap) (ml : locvars_env -> locvars_env) (s : state),
                    map_heap mh (map_locvars_env ml s) = map_locvars_env ml (map_heap mh s).
Axiom map_comm_09 : forall (mh : heap -> heap) (mm : mbody_env -> mbody_env) (s : state),
                    map_heap mh (map_mbody_env mm s) = map_mbody_env mm (map_heap mh s).
Axiom map_comm_12 : forall (ms : stack -> stack) (ma : alloc -> alloc) (s : state),
                    map_stack ms (map_alloc ma s) = map_alloc ma (map_stack ms s).
Axiom map_comm_13 : forall (ms : stack -> stack) (md : dtype -> dtype) (s : state),
                    map_stack ms (map_dtype md s) = map_dtype md (map_stack ms s).
Axiom map_comm_14 : forall (ms : stack -> stack) (mf : fields_env -> fields_env) (s : state),
                    map_stack ms (map_fields_env mf s) = map_fields_env mf (map_stack ms s).
Axiom map_comm_15 : forall (ms : stack -> stack) (ms' : super_env -> super_env) (s : state),
                    map_stack ms (map_super_env ms' s) = map_super_env ms' (map_stack ms s).
Axiom map_comm_16 : forall (ms : stack -> stack) (mc : cnames -> cnames) (s : state),
                    map_stack ms (map_cnames mc s) = map_cnames mc (map_stack ms s).
Axiom map_comm_17 : forall (ms : stack -> stack) (mm : methods_env -> methods_env) (s : state),
                    map_stack ms (map_methods_env mm s) = map_methods_env mm (map_stack ms s).
Axiom map_comm_18 : forall (ms : stack -> stack) (ml : locvars_env -> locvars_env) (s : state),
                    map_stack ms (map_locvars_env ml s) = map_locvars_env ml (map_stack ms s).
Axiom map_comm_19 : forall (ms : stack -> stack) (mm : mbody_env -> mbody_env) (s : state),
                    map_stack ms (map_mbody_env mm s) = map_mbody_env mm (map_stack ms s).
Axiom map_comm_23 : forall (ma : alloc -> alloc) (md : dtype -> dtype) (s : state),
                    map_alloc ma (map_dtype md s) = map_dtype md (map_alloc ma s).
Axiom map_comm_24 : forall (ma : alloc -> alloc) (mf : fields_env -> fields_env) (s : state),
                    map_alloc ma (map_fields_env mf s) = map_fields_env mf (map_alloc ma s).
Axiom map_comm_25 : forall (ma : alloc -> alloc) (ms : super_env -> super_env) (s : state),
                    map_alloc ma (map_super_env ms s) = map_super_env ms (map_alloc ma s).
Axiom map_comm_26 : forall (ma : alloc -> alloc) (mc : cnames -> cnames) (s : state),
                    map_alloc ma (map_cnames mc s) = map_cnames mc (map_alloc ma s).
Axiom map_comm_27 : forall (ma : alloc -> alloc) (mm : methods_env -> methods_env) (s : state),
                    map_alloc ma (map_methods_env mm s) = map_methods_env mm (map_alloc ma s).
Axiom map_comm_28 : forall (ma : alloc -> alloc) (ml : locvars_env -> locvars_env) (s : state),
                    map_alloc ma (map_locvars_env ml s) = map_locvars_env ml (map_alloc ma s).
Axiom map_comm_29 : forall (ma : alloc -> alloc) (mm : mbody_env -> mbody_env) (s : state),
                    map_alloc ma (map_mbody_env mm s) = map_mbody_env mm (map_alloc ma s).
Axiom map_comm_34 : forall (md : dtype -> dtype) (mf : fields_env -> fields_env) (s : state),
                    map_dtype md (map_fields_env mf s) = map_fields_env mf (map_dtype md s).
Axiom map_comm_35 : forall (md : dtype -> dtype) (ms : super_env -> super_env) (s : state),
                    map_dtype md (map_super_env ms s) = map_super_env ms (map_dtype md s).
Axiom map_comm_36 : forall (md : dtype -> dtype) (mc : cnames -> cnames) (s : state),
                    map_dtype md (map_cnames mc s) = map_cnames mc (map_dtype md s).
Axiom map_comm_37 : forall (md : dtype -> dtype) (mm : methods_env -> methods_env) (s : state),
                    map_dtype md (map_methods_env mm s) = map_methods_env mm (map_dtype md s).
Axiom map_comm_38 : forall (md : dtype -> dtype) (ml : locvars_env -> locvars_env) (s : state),
                    map_dtype md (map_locvars_env ml s) = map_locvars_env ml (map_dtype md s).
Axiom map_comm_39 : forall (md : dtype -> dtype) (mm : mbody_env -> mbody_env) (s : state),
                    map_dtype md (map_mbody_env mm s) = map_mbody_env mm (map_dtype md s).
Axiom map_comm_45 : forall (mf : fields_env -> fields_env) (ms : super_env -> super_env) (s : state),
                    map_fields_env mf (map_super_env ms s) = map_super_env ms (map_fields_env mf s).
Axiom map_comm_46 : forall (mf : fields_env -> fields_env) (mc : cnames -> cnames) (s : state),
                    map_fields_env mf (map_cnames mc s) = map_cnames mc (map_fields_env mf s).
Axiom map_comm_47 : forall (mf : fields_env -> fields_env) (mm : methods_env -> methods_env) (s : state),
                    map_fields_env mf (map_methods_env mm s) = map_methods_env mm (map_fields_env mf s).
Axiom map_comm_48 : forall (mf : fields_env -> fields_env) (ml : locvars_env -> locvars_env) (s : state),
                    map_fields_env mf (map_locvars_env ml s) = map_locvars_env ml (map_fields_env mf s).
Axiom map_comm_49 : forall (mf : fields_env -> fields_env) (mm : mbody_env -> mbody_env) (s : state),
                    map_fields_env mf (map_mbody_env mm s) = map_mbody_env mm (map_fields_env mf s).
Axiom map_comm_56 : forall (ms : super_env -> super_env) (mc : cnames -> cnames) (s : state),
                    map_super_env ms (map_cnames mc s) = map_cnames mc (map_super_env ms s).
Axiom map_comm_57 : forall (ms : super_env -> super_env) (mm : methods_env -> methods_env) (s : state),
                    map_super_env ms (map_methods_env mm s) = map_methods_env mm (map_super_env ms s).
Axiom map_comm_58 : forall (ms : super_env -> super_env) (ml : locvars_env -> locvars_env) (s : state),
                    map_super_env ms (map_locvars_env ml s) = map_locvars_env ml (map_super_env ms s).
Axiom map_comm_59 : forall (ms : super_env -> super_env) (mm : mbody_env -> mbody_env) (s : state),
                    map_super_env ms (map_mbody_env mm s) = map_mbody_env mm (map_super_env ms s).
Axiom map_comm_67 : forall (mc : cnames -> cnames) (mm : methods_env -> methods_env) (s : state),
                    map_cnames mc (map_methods_env mm s) = map_methods_env mm (map_cnames mc s).
Axiom map_comm_68 : forall (mc : cnames -> cnames) (ml : locvars_env -> locvars_env) (s : state),
                    map_cnames mc (map_locvars_env ml s) = map_locvars_env ml (map_cnames mc s).
Axiom map_comm_69 : forall (mc : cnames -> cnames) (mm : mbody_env -> mbody_env) (s : state),
                    map_cnames mc (map_mbody_env mm s) = map_mbody_env mm (map_cnames mc s).
Axiom map_comm_78 : forall (mm : methods_env -> methods_env) (ml : locvars_env -> locvars_env) (s : state),
                    map_methods_env mm (map_locvars_env ml s) = map_locvars_env ml (map_methods_env mm s).
Axiom map_comm_79 : forall (mm : methods_env -> methods_env) (mm' : mbody_env -> mbody_env) (s : state),
                    map_methods_env mm (map_mbody_env mm' s) = map_mbody_env mm' (map_methods_env mm s).
Axiom map_comm_89 : forall (ml : locvars_env -> locvars_env) (mm' : mbody_env -> mbody_env) (s : state),
                    map_locvars_env ml (map_mbody_env mm' s) = map_mbody_env mm' (map_locvars_env ml s).

Axiom update_comm_01 : forall (h : heap) (s' : stack) (s : state),
                    update_heap h (update_stack s' s) = update_stack s' (update_heap h s).
Axiom update_comm_02 : forall (h : heap) (a : alloc) (s : state),
                    update_heap h (update_alloc a s) = update_alloc a (update_heap h s).
Axiom update_comm_03 : forall (h : heap) (d : dtype) (s : state),
                    update_heap h (update_dtype d s) = update_dtype d (update_heap h s).
Axiom update_comm_04 : forall (h : heap) (f : fields_env) (s : state),
                    update_heap h (update_fields_env f s) = update_fields_env f (update_heap h s).
Axiom update_comm_05 : forall (h : heap) (s' : super_env) (s : state),
                    update_heap h (update_super_env s' s) = update_super_env s' (update_heap h s).
Axiom update_comm_06 : forall (h : heap) (c : cnames) (s : state),
                    update_heap h (update_cnames c s) = update_cnames c (update_heap h s).
Axiom update_comm_07 : forall (h : heap) (m : methods_env) (s : state),
                    update_heap h (update_methods_env m s) = update_methods_env m (update_heap h s).
Axiom update_comm_08 : forall (h : heap) (l : locvars_env) (s : state),
                    update_heap h (update_locvars_env l s) = update_locvars_env l (update_heap h s).
Axiom update_comm_09 : forall (h : heap) (m : mbody_env) (s : state),
                    update_heap h (update_mbody_env m s) = update_mbody_env m (update_heap h s).
Axiom update_comm_12 : forall (s' : stack) (a : alloc) (s : state),
                    update_stack s' (update_alloc a s) = update_alloc a (update_stack s' s).
Axiom update_comm_13 : forall (s' : stack) (d : dtype) (s : state),
                    update_stack s' (update_dtype d s) = update_dtype d (update_stack s' s).
Axiom update_comm_14 : forall (s' : stack) (f : fields_env) (s : state),
                    update_stack s' (update_fields_env f s) = update_fields_env f (update_stack s' s).
Axiom update_comm_15 : forall (s' : stack) (s'' : super_env) (s : state),
                    update_stack s' (update_super_env s'' s) = update_super_env s'' (update_stack s' s).
Axiom update_comm_16 : forall (s' : stack) (c : cnames) (s : state),
                    update_stack s' (update_cnames c s) = update_cnames c (update_stack s' s).
Axiom update_comm_17 : forall (s' : stack) (m : methods_env) (s : state),
                    update_stack s' (update_methods_env m s) = update_methods_env m (update_stack s' s).
Axiom update_comm_18 : forall (s' : stack) (l : locvars_env) (s : state),
                    update_stack s' (update_locvars_env l s) = update_locvars_env l (update_stack s' s).
Axiom update_comm_19 : forall (s' : stack) (m : mbody_env) (s : state),
                    update_stack s' (update_mbody_env m s) = update_mbody_env m (update_stack s' s).
Axiom update_comm_23 : forall (a : alloc) (d : dtype) (s : state),
                    update_alloc a (update_dtype d s) = update_dtype d (update_alloc a s).
Axiom update_comm_24 : forall (a : alloc) (f : fields_env) (s : state),
                    update_alloc a (update_fields_env f s) = update_fields_env f (update_alloc a s).
Axiom update_comm_25 : forall (a : alloc) (s' : super_env) (s : state),
                    update_alloc a (update_super_env s' s) = update_super_env s' (update_alloc a s).
Axiom update_comm_26 : forall (a : alloc) (c : cnames) (s : state),
                    update_alloc a (update_cnames c s) = update_cnames c (update_alloc a s).
Axiom update_comm_27 : forall (a : alloc) (m : methods_env) (s : state),
                    update_alloc a (update_methods_env m s) = update_methods_env m (update_alloc a s).
Axiom update_comm_28 : forall (a : alloc) (l : locvars_env) (s : state),
                    update_alloc a (update_locvars_env l s) = update_locvars_env l (update_alloc a s).
Axiom update_comm_29 : forall (a : alloc) (m : mbody_env) (s : state),
                    update_alloc a (update_mbody_env m s) = update_mbody_env m (update_alloc a s).
Axiom update_comm_34 : forall (d : dtype) (f : fields_env) (s : state),
                    update_dtype d (update_fields_env f s) = update_fields_env f (update_dtype d s).
Axiom update_comm_35 : forall (d : dtype) (s' : super_env) (s : state),
                    update_dtype d (update_super_env s' s) = update_super_env s' (update_dtype d s).
Axiom update_comm_36 : forall (d : dtype) (c : cnames) (s : state),
                    update_dtype d (update_cnames c s) = update_cnames c (update_dtype d s).
Axiom update_comm_37 : forall (d : dtype) (m : methods_env) (s : state),
                    update_dtype d (update_methods_env m s) = update_methods_env m (update_dtype d s).
Axiom update_comm_38 : forall (d : dtype) (l : locvars_env) (s : state),
                    update_dtype d (update_locvars_env l s) = update_locvars_env l (update_dtype d s).
Axiom update_comm_39 : forall (d : dtype) (m : mbody_env) (s : state),
                    update_dtype d (update_mbody_env m s) = update_mbody_env m (update_dtype d s).
Axiom update_comm_45 : forall (f : fields_env) (s' : super_env) (s : state),
                    update_fields_env f (update_super_env s' s) = update_super_env s' (update_fields_env f s).
Axiom update_comm_46 : forall (f : fields_env) (c : cnames) (s : state),
                    update_fields_env f (update_cnames c s) = update_cnames c (update_fields_env f s).
Axiom update_comm_47 : forall (f : fields_env) (m : methods_env) (s : state),
                    update_fields_env f (update_methods_env m s) = update_methods_env m (update_fields_env f s).
Axiom update_comm_48 : forall (f : fields_env) (l : locvars_env) (s : state),
                    update_fields_env f (update_locvars_env l s) = update_locvars_env l (update_fields_env f s).
Axiom update_comm_49 : forall (f : fields_env) (m : mbody_env) (s : state),
                    update_fields_env f (update_mbody_env m s) = update_mbody_env m (update_fields_env f s).
Axiom update_comm_56 : forall (s' : super_env) (c : cnames) (s : state),
                    update_super_env s' (update_cnames c s) = update_cnames c (update_super_env s' s).
Axiom update_comm_57 : forall (s' : super_env) (m : methods_env) (s : state),
                    update_super_env s' (update_methods_env m s) = update_methods_env m (update_super_env s' s).
Axiom update_comm_58 : forall (s' : super_env) (l : locvars_env) (s : state),
                    update_super_env s' (update_locvars_env l s) = update_locvars_env l (update_super_env s' s).
Axiom update_comm_59 : forall (s' : super_env) (m : mbody_env) (s : state),
                    update_super_env s' (update_mbody_env m s) = update_mbody_env m (update_super_env s' s).
Axiom update_comm_67 : forall (c : cnames) (m : methods_env) (s : state),
                    update_cnames c (update_methods_env m s) = update_methods_env m (update_cnames c s).
Axiom update_comm_68 : forall (c : cnames) (l : locvars_env) (s : state),
                    update_cnames c (update_locvars_env l s) = update_locvars_env l (update_cnames c s).
Axiom update_comm_69 : forall (c : cnames) (m : mbody_env) (s : state),
                    update_cnames c (update_mbody_env m s) = update_mbody_env m (update_cnames c s).
Axiom update_comm_78 : forall (m : methods_env) (l : locvars_env) (s : state),
                    update_methods_env m (update_locvars_env l s) = update_locvars_env l (update_methods_env m s).
Axiom update_comm_79 : forall (m : methods_env) (m' : mbody_env) (s : state),
                    update_methods_env m (update_mbody_env m' s) = update_mbody_env m' (update_methods_env m s).
Axiom update_comm_89 : forall (l : locvars_env) (m : mbody_env) (s : state),
                    update_locvars_env l (update_mbody_env m s) = update_mbody_env m (update_locvars_env l s).

End STATE.


(*-----  Data  -----*)

(*  State  *)

Module State <: STATE.

Definition heap := Heap.heap.
Definition stack := Stack.stack.
Definition alloc := Ref.alloc.

Definition dtype := DType.dtype.
Definition fields_env := TEnv.fields_env.
Definition super_env := TEnv.super_env.
Definition cnames := TEnv.cnames.
Definition methods_env := TEnv.methods_env.
Definition locvars_env := TEnv.locvars_env.
Definition mbody_env := MEnv.mbody_env.

Definition name := Name.name.
Definition method := Method.method.
Definition method_type := TEnv.method_type.
Definition method_locvars := TEnv.method_locvars.
Definition rtype := RType.rtype.
Definition field_type := RType.field_type.
Definition args := MEnv.args.
Definition locvars := MEnv.locvars.
Definition cmd := Lang.cmd.

Definition state := (heap * stack * alloc * dtype * fields_env * super_env
                    * cnames * methods_env * locvars_env * mbody_env)%type.
Definition init_state :=
    (Heap.empty_heap, Stack.init_stack, Ref.init_alloc, DType.init_dtype,
     TEnv.init_fields_env, TEnv.init_super_env, TEnv.init_cnames,
     TEnv.init_methods_env, TEnv.init_locvars_env, MEnv.init_mbody_env).

Definition get_heap (s : state) : heap :=
    match s with (a, b, c, d, e, f, g, h, i, j) => a end.
Definition update_heap (H : heap) (s : state) : state :=
    match s with (a, b, c, d, e, f, g, h, i, j) => (H, b, c, d, e, f, g, h, i, j) end.
Definition map_heap (m : heap -> heap) (s : state) : state :=
    match s with (a, b, c, d, e, f, g, h, i, j) => (m a, b, c, d, e, f, g, h, i, j) end.
Definition get_stack (s : state) : stack :=
    match s with (a, b, c, d, e, f, g, h, i, j) => b end.
Definition update_stack (S : stack) (s : state) : state :=
    match s with (a, b, c, d, e, f, g, h, i, j) => (a, S, c, d, e, f, g, h, i, j) end.
Definition map_stack (m : stack -> stack) (s : state) : state :=
    match s with (a, b, c, d, e, f, g, h, i, j) => (a, m b, c, d, e, f, g, h, i, j) end.
Definition get_alloc (s : state) : alloc :=
    match s with (a, b, c, d, e, f, g, h, i, j) => c end.
Definition update_alloc (A : alloc) (s : state) : state :=
    match s with (a, b, c, d, e, f, g, h, i, j) => (a, b, A, d, e, f, g, h, i, j) end.
Definition map_alloc (m : alloc -> alloc) (s : state) : state :=
    match s with (a, b, c, d, e, f, g, h, i, j) => (a, b, m c, d, e, f, g, h, i, j) end.
Definition get_dtype (s : state) : dtype :=
    match s with (a, b, c, d, e, f, g, h, i, j) => d end.
Definition update_dtype (D : dtype) (s : state) : state :=
    match s with (a, b, c, d, e, f, g, h, i, j) => (a, b, c, D, e, f, g, h, i, j) end.
Definition map_dtype (m : dtype -> dtype) (s : state) : state :=
    match s with (a, b, c, d, e, f, g, h, i, j) => (a, b, c, m d, e, f, g, h, i, j) end.
Definition get_fields_env (s : state) : fields_env :=
    match s with (a, b, c, d, e, f, g, h, i, j) => e end.
Definition update_fields_env (F : fields_env) (s : state) : state :=
    match s with (a, b, c, d, e, f, g, h, i, j) => (a, b, c, d, F, f, g, h, i, j) end.
Definition map_fields_env (m : fields_env -> fields_env) (s : state) : state :=
    match s with (a, b, c, d, e, f, g, h, i, j) => (a, b, c, d, m e, f, g, h, i, j) end.
Definition get_super_env (s : state) : super_env :=
    match s with (a, b, c, d, e, f, g, h, i, j) => f end.
Definition update_super_env (S : super_env) (s : state) : state :=
    match s with (a, b, c, d, e, f, g, h, i, j) => (a, b, c, d, e, S, g, h, i, j) end.
Definition map_super_env (m : super_env -> super_env) (s : state) : state :=
    match s with (a, b, c, d, e, f, g, h, i, j) => (a, b, c, d, e, m f, g, h, i, j) end.
Definition get_cnames (s : state) : cnames :=
    match s with (a, b, c, d, e, f, g, h, i, j) => g end.
Definition update_cnames (C : cnames) (s : state) : state :=
    match s with (a, b, c, d, e, f, g, h, i, j) => (a, b, c, d, e, f, C, h, i, j) end.
Definition map_cnames (m : cnames -> cnames) (s : state) : state :=
    match s with (a, b, c, d, e, f, g, h, i, j) => (a, b, c, d, e, f, m g, h, i, j) end.
Definition get_methods_env (s : state) : methods_env :=
    match s with (a, b, c, d, e, f, g, h, i, j) => h end.
Definition update_methods_env (M : methods_env) (s : state) : state :=
    match s with (a, b, c, d, e, f, g, h, i, j) => (a, b, c, d, e, f, g, M, i, j) end.
Definition map_methods_env (m : methods_env -> methods_env) (s : state) : state :=
    match s with (a, b, c, d, e, f, g, h, i, j) => (a, b, c, d, e, f, g, m h, i, j) end.
Definition get_locvars_env (s : state) : locvars_env :=
    match s with (a, b, c, d, e, f, g, h, i, j) => i end.
Definition update_locvars_env (L : locvars_env) (s : state) : state :=
    match s with (a, b, c, d, e, f, g, h, i, j) => (a, b, c, d, e, f, g, h, L, j) end.
Definition map_locvars_env (m : locvars_env -> locvars_env) (s : state) : state :=
    match s with (a, b, c, d, e, f, g, h, i, j) => (a, b, c, d, e, f, g, h, m i, j) end.
Definition get_mbody_env (s : state) : mbody_env :=
    match s with (a, b, c, d, e, f, g, h, i, j) => j end.
Definition update_mbody_env (M : mbody_env) (s : state) : state :=
    match s with (a, b, c, d, e, f, g, h, i, j) => (a, b, c, d, e, f, g, h, i, M) end.
Definition map_mbody_env (m : mbody_env -> mbody_env) (s : state) : state :=
    match s with (a, b, c, d, e, f, g, h, i, j) => (a, b, c, d, e, f, g, h, i, m j) end.

Definition build_class (new : rtype) (super : list rtype)
                       (mf : field_type -> field_type) (s : state) : state :=
  match super with
  | nil => s (* build class failed *)
  | cons c _ =>
    match TEnv.get_fields c (get_fields_env s) with
    | None => s (* build class failed *)
    | Some f =>
      match TEnv.find_class_methods c (get_methods_env s) with
      | None => s (* build class failed *)
      | Some cmt =>
        match MEnv.find_class_mbody c (get_mbody_env s) with
        | None => s (* build class failed *)
        | Some cmb =>
          map_super_env (TEnv.update_super new super)
          (map_methods_env (TEnv.update_class_methods new cmt) (* delete constructor *)
          (map_mbody_env (MEnv.update_class_mbody new cmb) (* delete constructor *)
          (map_fields_env (TEnv.map_fields new mf)
          (map_fields_env (TEnv.update_fields new f)
          (map_cnames (TEnv.cnames_add new) s)))))
  end end end end.

Definition build_method (rt : rtype) (m : method) (t : method_type) (a : args)
                        (l : method_locvars) (c : cmd) (s : state) : state :=
    map_methods_env (TEnv.update_method rt m t)
    (map_locvars_env (TEnv.update_a_locvar rt m l)
    (map_mbody_env (MEnv.update_mbody_env rt m (a, MEnv.make_locvars l, Some c)) s)).
(* 条件：method_type里的参数个数和args里的参数个数必须是一样的。 *)

Definition build_interf (new : rtype) (super : option rtype) (s : state) : state :=
  match super with
  | None =>
    map_super_env (TEnv.update_super new nil)
    (map_cnames (TEnv.cnames_add new) s)
  | Some i =>
    match TEnv.find_class_methods i (get_methods_env s) with
    | None => s (* build interface failed *)
    | Some imt =>
      match MEnv.find_class_mbody i (get_mbody_env s) with
      | None => s (* build interface failed *)
      | Some imb =>
        map_super_env (TEnv.update_super new (cons i nil))
        (map_methods_env (TEnv.update_class_methods new imt)
        (map_mbody_env (MEnv.update_class_mbody new imb)
        (map_cnames (TEnv.cnames_add new) s)))
  end end end.

Definition build_msign (rt : rtype) (m : method) (t : method_type) (a : args)
                       (s : state) : state :=
    map_methods_env (TEnv.update_method rt m t)
    (map_mbody_env (MEnv.update_mbody_env rt m (a, MEnv.no_locvars, None)) s).
(* 条件：method_type里的参数个数和args里的参数个数必须是一样的。 *)

Definition new_obj (n : name) (t : rtype) (s : state) : state :=
    let r := Ref.get_new (get_alloc s) in
        match RType.get_fields t (get_fields_env s) with
            | None => s
            | Some f =>
                map_alloc (Ref.new t)
                (map_heap (Heap.new r f)
                (map_dtype (DType.update_dtype n t)
                (map_stack (Stack.update n r) s)))
        end.
(* 这样写似乎有误。每次调用r时都会申请一个新的ref。 *)

Definition beq (s1 s2 : state) : bool :=
    match s1 with (a1, b1, c1, d1, e1, f1, g1, h1, i1, j1) =>
    match s2 with (a2, b2, c2, d2, e2, f2, g2, h2, i2, j2) =>
    andb (Heap.beq a1 a2)
    (andb (Stack.beq b1 b2)
    (andb (Ref.alloc_beq c1 c2)
    (andb (DType.beq d1 d2)
    (andb (TEnv.fields_beq e1 e2)
    (andb (TEnv.super_beq f1 f2)
    (andb (TEnv.cnames_beq g1 g2)
    (andb (TEnv.methods_beq h1 h2)
    (andb (TEnv.locvars_beq i1 i2)
          (MEnv.beq j1 j2)))))))))
    end end.

Definition peq (s1 s2 : state) : Prop :=
    match s1 with (a1, b1, c1, d1, e1, f1, g1, h1, i1, j1) =>
    match s2 with (a2, b2, c2, d2, e2, f2, g2, h2, i2, j2) =>
    (Heap.eq a1 a2)
    /\ (Stack.peq b1 b2)
    /\ (Ref.alloc_peq c1 c2)
    /\ (DType.peq d1 d2)
    /\ (TEnv.fields_peq e1 e2)
    /\ (TEnv.super_peq f1 f2)
    /\ (TEnv.cnames_peq g1 g2)
    /\ (TEnv.methods_peq h1 h2)
    /\ (TEnv.locvars_peq i1 i2)
    /\ (MEnv.peq j1 j2)
    end end.

Definition seq (s1 s2 : state) : Prop :=
    match s1 with (a1, b1, c1, d1, e1, f1, g1, h1, i1, j1) =>
    match s2 with (a2, b2, c2, d2, e2, f2, g2, h2, i2, j2) =>
    (Ref.alloc_peq c1 c2)
    /\ (DType.peq d1 d2)
    /\ (TEnv.fields_peq e1 e2)
    /\ (TEnv.super_peq f1 f2)
    /\ (TEnv.cnames_peq g1 g2)
    /\ (TEnv.methods_peq h1 h2)
    /\ (TEnv.locvars_peq i1 i2)
    /\ (MEnv.peq j1 j2)
    end end.

Lemma seq_peq : forall s1 s2 : state, peq s1 s2 -> seq s1 s2.
Proof.
  unfold peq; unfold seq.
  induction s1; do 8 induction a.
  induction s2; do 8 induction a0.
  intro H. do 2 destruct H as [_ H].
  assumption.
Qed.

Lemma peq_seq : forall s1 s2 : state, Heap.eq (get_heap s1) (get_heap s2) /\
     Stack.peq (get_stack s1) (get_stack s2) /\ seq s1 s2 -> peq s1 s2.
Proof.
  unfold peq; unfold seq.
  induction s1; do 8 induction a.
  induction s2; do 8 induction a0.
  intro H; apply H.
Qed.

Axiom equal_1 : forall s1 s2 : state, peq s1 s2 -> beq s1 s2 = true.
Axiom equal_2 : forall s1 s2 : state, beq s1 s2 = true -> peq s1 s2.
Axiom equal_3 : forall s1 s2 : state, s1 = s2 <-> peq s1 s2.

Lemma seq_subst : forall s1 s2 : state, seq s1 s2 ->
    (update_heap (get_heap s2) (update_stack (get_stack s2) s1)) = s2.
Proof.
  intros s1 s2 H. apply equal_3.
  induction s1; do 8 induction a.
  induction s2; do 8 induction a0.
  unfold get_heap; unfold update_heap;
  unfold get_stack; unfold update_stack.
  unfold seq in H; unfold peq.
  split. apply Heap.eq_refl.
  split. apply Stack.eq_refl.
  assumption.
Qed.

Lemma seq_update_heap : forall (h : heap) (s1 s2 : state),
    seq s1 s2 <-> seq (update_heap h s1) s2.
Proof.
  intros h s1 s2.
  induction s1; do 8 induction a.
  induction s2; do 8 induction a0.
  unfold update_heap; unfold seq.
  reflexivity.
Qed.

Lemma seq_update_stack : forall (st : stack) (s1 s2 : state),
    seq s1 s2 <-> seq (update_stack st s1) s2.
Proof.
  intros st s1 s2.
  induction s1; do 8 induction a.
  induction s2; do 8 induction a0.
  unfold update_stack; unfold seq.
  reflexivity.
Qed.

Lemma seq_map_heap : forall (mh : heap -> heap) (s1 s2 : state),
    seq s1 s2 <-> seq (map_heap mh s1) s2.
Proof.
  intros mh s1 s2.
  induction s1; do 8 induction a.
  induction s2; do 8 induction a0.
  unfold map_heap; unfold seq.
  reflexivity.
Qed.

Lemma seq_map_stack : forall (ms : stack -> stack) (s1 s2 : state),
    seq s1 s2 <-> seq (map_stack ms s1) s2.
Proof.
  intros ms s1 s2.
  induction s1; do 8 induction a.
  induction s2; do 8 induction a0.
  unfold map_stack; unfold seq.
  reflexivity.
Qed.

Lemma seq_refl : forall x : state, seq x x.
Proof.
  induction x; do 8 induction a.
  unfold seq.
  split. apply Ref.alloc_eq_refl.
  split. apply DType.eq_refl.
  split. apply TEnv.fields_eq_refl.
  split. apply TEnv.super_eq_refl.
  split. apply TEnv.cnames_eq_refl.
  split. apply TEnv.methods_eq_refl.
  split. apply TEnv.locvars_eq_refl.
  apply MEnv.eq_refl.
Qed.

Lemma seq_sym : forall x y : state, seq x y -> seq y x.
Proof.
  induction x; do 8 induction a.
  induction y; do 8 induction a0.
  unfold seq. intro H.
  destruct H. destruct H0. destruct H1. destruct H2.
  destruct H3. destruct H4. destruct H5.
  split. apply Ref.alloc_eq_sym; assumption.
  split. apply DType.eq_sym; assumption.
  split. apply TEnv.fields_eq_sym; assumption.
  split. apply TEnv.super_eq_sym; assumption.
  split. apply TEnv.cnames_eq_sym; assumption.
  split. apply TEnv.methods_eq_sym; assumption.
  split. apply TEnv.locvars_eq_sym; assumption.
  apply MEnv.eq_sym; assumption.
Qed.

Lemma seq_trans : forall x y z : state, seq x y -> seq y z -> seq x z.
Proof.
  induction x; do 8 induction a.
  induction y; do 8 induction a0.
  induction z; do 8 induction a1.
  unfold seq. intros H H0.
  destruct H. destruct H0. destruct H1. destruct H2.
  destruct H3. destruct H4. destruct H5. destruct H6.
  destruct H7. destruct H8. destruct H9. destruct H10.
  destruct H11. destruct H12.
  split. apply Ref.alloc_eq_trans with (a2 := b15); assumption; assumption.
  split. apply DType.eq_trans with (y := b14); assumption; assumption.
  split. apply TEnv.fields_eq_trans with (y := b13); assumption; assumption.
  split. apply TEnv.super_eq_trans with (y := b12); assumption; assumption.
  split. apply TEnv.cnames_eq_trans with (y := b11); assumption; assumption.
  split. apply TEnv.methods_eq_trans with (y := b10); assumption; assumption.
  split. apply TEnv.locvars_eq_trans with (y := b9); assumption; assumption.
  apply MEnv.eq_trans with (y := b8); assumption; assumption.
Qed.

Ltac ind s := intros; do 9 induction s as [s *]; reflexivity.

Lemma get_after_map_00 : forall (mh : heap -> heap) (s : state),
    get_heap (map_heap mh s) = mh (get_heap s).
Proof. ind s. Qed.
Lemma get_after_map_01 : forall (ms : stack -> stack) (s : state),
    get_heap (map_stack ms s) = get_heap s.
Proof. ind s. Qed.
Lemma get_after_map_02 : forall (ma : alloc -> alloc) (s : state),
    get_heap (map_alloc ma s) = get_heap s.
Proof. ind s. Qed.
Lemma get_after_map_03 : forall (md : dtype -> dtype) (s : state),
    get_heap (map_dtype md s) = get_heap s.
Proof. ind s. Qed.
Lemma get_after_map_04 : forall (mf : fields_env -> fields_env) (s : state),
    get_heap (map_fields_env mf s) = get_heap s.
Proof. ind s. Qed.
Lemma get_after_map_05 : forall (ms : super_env -> super_env) (s : state),
    get_heap (map_super_env ms s) = get_heap s.
Proof. ind s. Qed.
Lemma get_after_map_06 : forall (mc : cnames -> cnames) (s : state),
    get_heap (map_cnames mc s) = get_heap s.
Proof. ind s. Qed.
Lemma get_after_map_07 : forall (mm : methods_env -> methods_env) (s : state),
    get_heap (map_methods_env mm s) = get_heap s.
Proof. ind s. Qed.
Lemma get_after_map_08 : forall (ml : locvars_env -> locvars_env) (s : state),
    get_heap (map_locvars_env ml s) = get_heap s.
Proof. ind s. Qed.
Lemma get_after_map_09 : forall (mm : mbody_env -> mbody_env) (s : state),
    get_heap (map_mbody_env mm s) = get_heap s.
Proof. ind s. Qed.
Lemma get_after_map_10 : forall (mh : heap -> heap) (s : state),
    get_stack (map_heap mh s) = get_stack s.
Proof. ind s. Qed.
Lemma get_after_map_11 : forall (ms : stack -> stack) (s : state),
    get_stack (map_stack ms s) = ms (get_stack s).
Proof. ind s. Qed.
Lemma get_after_map_12 : forall (ma : alloc -> alloc) (s : state),
    get_stack (map_alloc ma s) = get_stack s.
Proof. ind s. Qed.
Lemma get_after_map_13 : forall (md : dtype -> dtype) (s : state),
    get_stack (map_dtype md s) = get_stack s.
Proof. ind s. Qed.
Lemma get_after_map_14 : forall (mf : fields_env -> fields_env) (s : state),
    get_stack (map_fields_env mf s) = get_stack s.
Proof. ind s. Qed.
Lemma get_after_map_15 : forall (ms : super_env -> super_env) (s : state),
    get_stack (map_super_env ms s) = get_stack s.
Proof. ind s. Qed.
Lemma get_after_map_16 : forall (mc : cnames -> cnames) (s : state),
    get_stack (map_cnames mc s) = get_stack s.
Proof. ind s. Qed.
Lemma get_after_map_17 : forall (mm : methods_env -> methods_env) (s : state),
    get_stack (map_methods_env mm s) = get_stack s.
Proof. ind s. Qed.
Lemma get_after_map_18 : forall (ml : locvars_env -> locvars_env) (s : state),
    get_stack (map_locvars_env ml s) = get_stack s.
Proof. ind s. Qed.
Lemma get_after_map_19 : forall (mm : mbody_env -> mbody_env) (s : state),
    get_stack (map_mbody_env mm s) = get_stack s.
Proof. ind s. Qed.
Lemma get_after_map_20 : forall (mh : heap -> heap) (s : state),
    get_alloc (map_heap mh s) = get_alloc s.
Proof. ind s. Qed.
Lemma get_after_map_21 : forall (ms : stack -> stack) (s : state),
    get_alloc (map_stack ms s) = get_alloc s.
Proof. ind s. Qed.
Lemma get_after_map_22 : forall (ma : alloc -> alloc) (s : state),
    get_alloc (map_alloc ma s) = ma (get_alloc s).
Proof. ind s. Qed.
Lemma get_after_map_23 : forall (md : dtype -> dtype) (s : state),
    get_alloc (map_dtype md s) = get_alloc s.
Proof. ind s. Qed.
Lemma get_after_map_24 : forall (mf : fields_env -> fields_env) (s : state),
    get_alloc (map_fields_env mf s) = get_alloc s.
Proof. ind s. Qed.
Lemma get_after_map_25 : forall (ms : super_env -> super_env) (s : state),
    get_alloc (map_super_env ms s) = get_alloc s.
Proof. ind s. Qed.
Lemma get_after_map_26 : forall (mc : cnames -> cnames) (s : state),
    get_alloc (map_cnames mc s) = get_alloc s.
Proof. ind s. Qed.
Lemma get_after_map_27 : forall (mm : methods_env -> methods_env) (s : state),
    get_alloc (map_methods_env mm s) = get_alloc s.
Proof. ind s. Qed.
Lemma get_after_map_28 : forall (ml : locvars_env -> locvars_env) (s : state),
    get_alloc (map_locvars_env ml s) = get_alloc s.
Proof. ind s. Qed.
Lemma get_after_map_29 : forall (mm : mbody_env -> mbody_env) (s : state),
    get_alloc (map_mbody_env mm s) = get_alloc s.
Proof. ind s. Qed.
Lemma get_after_map_30 : forall (mh : heap -> heap) (s : state),
    get_dtype (map_heap mh s) = get_dtype s.
Proof. ind s. Qed.
Lemma get_after_map_31 : forall (ms : stack -> stack) (s : state),
    get_dtype (map_stack ms s) = get_dtype s.
Proof. ind s. Qed.
Lemma get_after_map_32 : forall (ma : alloc -> alloc) (s : state),
    get_dtype (map_alloc ma s) = get_dtype s.
Proof. ind s. Qed.
Lemma get_after_map_33 : forall (md : dtype -> dtype) (s : state),
    get_dtype (map_dtype md s) = md (get_dtype s).
Proof. ind s. Qed.
Lemma get_after_map_34 : forall (mf : fields_env -> fields_env) (s : state),
    get_dtype (map_fields_env mf s) = get_dtype s.
Proof. ind s. Qed.
Lemma get_after_map_35 : forall (ms : super_env -> super_env) (s : state),
    get_dtype (map_super_env ms s) = get_dtype s.
Proof. ind s. Qed.
Lemma get_after_map_36 : forall (mc : cnames -> cnames) (s : state),
    get_dtype (map_cnames mc s) = get_dtype s.
Proof. ind s. Qed.
Lemma get_after_map_37 : forall (mm : methods_env -> methods_env) (s : state),
    get_dtype (map_methods_env mm s) = get_dtype s.
Proof. ind s. Qed.
Lemma get_after_map_38 : forall (ml : locvars_env -> locvars_env) (s : state),
    get_dtype (map_locvars_env ml s) = get_dtype s.
Proof. ind s. Qed.
Lemma get_after_map_39 : forall (mm : mbody_env -> mbody_env) (s : state),
    get_dtype (map_mbody_env mm s) = get_dtype s.
Proof. ind s. Qed.
Lemma get_after_map_40 : forall (mh : heap -> heap) (s : state),
    get_fields_env (map_heap mh s) = get_fields_env s.
Proof. ind s. Qed.
Lemma get_after_map_41 : forall (ms : stack -> stack) (s : state),
    get_fields_env (map_stack ms s) = get_fields_env s.
Proof. ind s. Qed.
Lemma get_after_map_42 : forall (ma : alloc -> alloc) (s : state),
    get_fields_env (map_alloc ma s) = get_fields_env s.
Proof. ind s. Qed.
Lemma get_after_map_43 : forall (md : dtype -> dtype) (s : state),
    get_fields_env (map_dtype md s) = get_fields_env s.
Proof. ind s. Qed.
Lemma get_after_map_44 : forall (mf : fields_env -> fields_env) (s : state),
    get_fields_env (map_fields_env mf s) = mf (get_fields_env s).
Proof. ind s. Qed.
Lemma get_after_map_45 : forall (ms : super_env -> super_env) (s : state),
    get_fields_env (map_super_env ms s) = get_fields_env s.
Proof. ind s. Qed.
Lemma get_after_map_46 : forall (mc : cnames -> cnames) (s : state),
    get_fields_env (map_cnames mc s) = get_fields_env s.
Proof. ind s. Qed.
Lemma get_after_map_47 : forall (mm : methods_env -> methods_env) (s : state),
    get_fields_env (map_methods_env mm s) = get_fields_env s.
Proof. ind s. Qed.
Lemma get_after_map_48 : forall (ml : locvars_env -> locvars_env) (s : state),
    get_fields_env (map_locvars_env ml s) = get_fields_env s.
Proof. ind s. Qed.
Lemma get_after_map_49 : forall (mm : mbody_env -> mbody_env) (s : state),
    get_fields_env (map_mbody_env mm s) = get_fields_env s.
Proof. ind s. Qed.
Lemma get_after_map_50 : forall (mh : heap -> heap) (s : state),
    get_super_env (map_heap mh s) = get_super_env s.
Proof. ind s. Qed.
Lemma get_after_map_51 : forall (ms : stack -> stack) (s : state),
    get_super_env (map_stack ms s) = get_super_env s.
Proof. ind s. Qed.
Lemma get_after_map_52 : forall (ma : alloc -> alloc) (s : state),
    get_super_env (map_alloc ma s) = get_super_env s.
Proof. ind s. Qed.
Lemma get_after_map_53 : forall (md : dtype -> dtype) (s : state),
    get_super_env (map_dtype md s) = get_super_env s.
Proof. ind s. Qed.
Lemma get_after_map_54 : forall (mf : fields_env -> fields_env) (s : state),
    get_super_env (map_fields_env mf s) = get_super_env s.
Proof. ind s. Qed.
Lemma get_after_map_55 : forall (ms : super_env -> super_env) (s : state),
    get_super_env (map_super_env ms s) = ms (get_super_env s).
Proof. ind s. Qed.
Lemma get_after_map_56 : forall (mc : cnames -> cnames) (s : state),
    get_super_env (map_cnames mc s) = get_super_env s.
Proof. ind s. Qed.
Lemma get_after_map_57 : forall (mm : methods_env -> methods_env) (s : state),
    get_super_env (map_methods_env mm s) = get_super_env s.
Proof. ind s. Qed.
Lemma get_after_map_58 : forall (ml : locvars_env -> locvars_env) (s : state),
    get_super_env (map_locvars_env ml s) = get_super_env s.
Proof. ind s. Qed.
Lemma get_after_map_59 : forall (mm : mbody_env -> mbody_env) (s : state),
    get_super_env (map_mbody_env mm s) = get_super_env s.
Proof. ind s. Qed.
Lemma get_after_map_60 : forall (mh : heap -> heap) (s : state),
    get_cnames (map_heap mh s) = get_cnames s.
Proof. ind s. Qed.
Lemma get_after_map_61 : forall (ms : stack -> stack) (s : state),
    get_cnames (map_stack ms s) = get_cnames s.
Proof. ind s. Qed.
Lemma get_after_map_62 : forall (ma : alloc -> alloc) (s : state),
    get_cnames (map_alloc ma s) = get_cnames s.
Proof. ind s. Qed.
Lemma get_after_map_63 : forall (md : dtype -> dtype) (s : state),
    get_cnames (map_dtype md s) = get_cnames s.
Proof. ind s. Qed.
Lemma get_after_map_64 : forall (mf : fields_env -> fields_env) (s : state),
    get_cnames (map_fields_env mf s) = get_cnames s.
Proof. ind s. Qed.
Lemma get_after_map_65 : forall (ms : super_env -> super_env) (s : state),
    get_cnames (map_super_env ms s) = get_cnames s.
Proof. ind s. Qed.
Lemma get_after_map_66 : forall (mc : cnames -> cnames) (s : state),
    get_cnames (map_cnames mc s) = mc (get_cnames s).
Proof. ind s. Qed.
Lemma get_after_map_67 : forall (mm : methods_env -> methods_env) (s : state),
    get_cnames (map_methods_env mm s) = get_cnames s.
Proof. ind s. Qed.
Lemma get_after_map_68 : forall (ml : locvars_env -> locvars_env) (s : state),
    get_cnames (map_locvars_env ml s) = get_cnames s.
Proof. ind s. Qed.
Lemma get_after_map_69 : forall (mm : mbody_env -> mbody_env) (s : state),
    get_cnames (map_mbody_env mm s) = get_cnames s.
Proof. ind s. Qed.
Lemma get_after_map_70 : forall (mh : heap -> heap) (s : state),
    get_methods_env (map_heap mh s) = get_methods_env s.
Proof. ind s. Qed.
Lemma get_after_map_71 : forall (ms : stack -> stack) (s : state),
    get_methods_env (map_stack ms s) = get_methods_env s.
Proof. ind s. Qed.
Lemma get_after_map_72 : forall (ma : alloc -> alloc) (s : state),
    get_methods_env (map_alloc ma s) = get_methods_env s.
Proof. ind s. Qed.
Lemma get_after_map_73 : forall (md : dtype -> dtype) (s : state),
    get_methods_env (map_dtype md s) = get_methods_env s.
Proof. ind s. Qed.
Lemma get_after_map_74 : forall (mf : fields_env -> fields_env) (s : state),
    get_methods_env (map_fields_env mf s) = get_methods_env s.
Proof. ind s. Qed.
Lemma get_after_map_75 : forall (ms : super_env -> super_env) (s : state),
    get_methods_env (map_super_env ms s) = get_methods_env s.
Proof. ind s. Qed.
Lemma get_after_map_76 : forall (mc : cnames -> cnames) (s : state),
    get_methods_env (map_cnames mc s) = get_methods_env s.
Proof. ind s. Qed.
Lemma get_after_map_77 : forall (mm : methods_env -> methods_env) (s : state),
    get_methods_env (map_methods_env mm s) = mm (get_methods_env s).
Proof. ind s. Qed.
Lemma get_after_map_78 : forall (ml : locvars_env -> locvars_env) (s : state),
    get_methods_env (map_locvars_env ml s) = get_methods_env s.
Proof. ind s. Qed.
Lemma get_after_map_79 : forall (mm : mbody_env -> mbody_env) (s : state),
    get_methods_env (map_mbody_env mm s) = get_methods_env s.
Proof. ind s. Qed.
Lemma get_after_map_80 : forall (mh : heap -> heap) (s : state),
    get_locvars_env (map_heap mh s) = get_locvars_env s.
Proof. ind s. Qed.
Lemma get_after_map_81 : forall (ms : stack -> stack) (s : state),
    get_locvars_env (map_stack ms s) = get_locvars_env s.
Proof. ind s. Qed.
Lemma get_after_map_82 : forall (ma : alloc -> alloc) (s : state),
    get_locvars_env (map_alloc ma s) = get_locvars_env s.
Proof. ind s. Qed.
Lemma get_after_map_83 : forall (md : dtype -> dtype) (s : state),
    get_locvars_env (map_dtype md s) = get_locvars_env s.
Proof. ind s. Qed.
Lemma get_after_map_84 : forall (mf : fields_env -> fields_env) (s : state),
    get_locvars_env (map_fields_env mf s) = get_locvars_env s.
Proof. ind s. Qed.
Lemma get_after_map_85 : forall (ms : super_env -> super_env) (s : state),
    get_locvars_env (map_super_env ms s) = get_locvars_env s.
Proof. ind s. Qed.
Lemma get_after_map_86 : forall (mc : cnames -> cnames) (s : state),
    get_locvars_env (map_cnames mc s) = get_locvars_env s.
Proof. ind s. Qed.
Lemma get_after_map_87 : forall (mm : methods_env -> methods_env) (s : state),
    get_locvars_env (map_methods_env mm s) = get_locvars_env s.
Proof. ind s. Qed.
Lemma get_after_map_88 : forall (ml : locvars_env -> locvars_env) (s : state),
    get_locvars_env (map_locvars_env ml s) = ml (get_locvars_env s).
Proof. ind s. Qed.
Lemma get_after_map_89 : forall (mm : mbody_env -> mbody_env) (s : state),
    get_locvars_env (map_mbody_env mm s) = get_locvars_env s.
Proof. ind s. Qed.
Lemma get_after_map_90 : forall (mh : heap -> heap) (s : state),
    get_mbody_env (map_heap mh s) = get_mbody_env s.
Proof. ind s. Qed.
Lemma get_after_map_91 : forall (ms : stack -> stack) (s : state),
    get_mbody_env (map_stack ms s) = get_mbody_env s.
Proof. ind s. Qed.
Lemma get_after_map_92 : forall (ma : alloc -> alloc) (s : state),
    get_mbody_env (map_alloc ma s) = get_mbody_env s.
Proof. ind s. Qed.
Lemma get_after_map_93 : forall (md : dtype -> dtype) (s : state),
    get_mbody_env (map_dtype md s) = get_mbody_env s.
Proof. ind s. Qed.
Lemma get_after_map_94 : forall (mf : fields_env -> fields_env) (s : state),
    get_mbody_env (map_fields_env mf s) = get_mbody_env s.
Proof. ind s. Qed.
Lemma get_after_map_95 : forall (ms : super_env -> super_env) (s : state),
    get_mbody_env (map_super_env ms s) = get_mbody_env s.
Proof. ind s. Qed.
Lemma get_after_map_96 : forall (mc : cnames -> cnames) (s : state),
    get_mbody_env (map_cnames mc s) = get_mbody_env s.
Proof. ind s. Qed.
Lemma get_after_map_97 : forall (mm : methods_env -> methods_env) (s : state),
    get_mbody_env (map_methods_env mm s) = get_mbody_env s.
Proof. ind s. Qed.
Lemma get_after_map_98 : forall (ml : locvars_env -> locvars_env) (s : state),
    get_mbody_env (map_locvars_env ml s) = get_mbody_env s.
Proof. ind s. Qed.
Lemma get_after_map_99 : forall (mm : mbody_env -> mbody_env) (s : state),
    get_mbody_env (map_mbody_env mm s) = mm (get_mbody_env s).
Proof. ind s. Qed.

Lemma get_after_update_00 : forall (h : heap) (s : state),
    get_heap (update_heap h s) = h.
Proof. ind s. Qed.
Lemma get_after_update_01 : forall (s' : stack) (s : state),
    get_heap (update_stack s' s) = get_heap s.
Proof. ind s. Qed.
Lemma get_after_update_02 : forall (a : alloc) (s : state),
    get_heap (update_alloc a s) = get_heap s.
Proof. ind s. Qed.
Lemma get_after_update_03 : forall (d : dtype) (s : state),
    get_heap (update_dtype d s) = get_heap s.
Proof. ind s. Qed.
Lemma get_after_update_04 : forall (f : fields_env) (s : state),
    get_heap (update_fields_env f s) = get_heap s.
Proof. ind s. Qed.
Lemma get_after_update_05 : forall (s' : super_env) (s : state),
    get_heap (update_super_env s' s) = get_heap s.
Proof. ind s. Qed.
Lemma get_after_update_06 : forall (c : cnames) (s : state),
    get_heap (update_cnames c s) = get_heap s.
Proof. ind s. Qed.
Lemma get_after_update_07 : forall (m : methods_env) (s : state),
    get_heap (update_methods_env m s) = get_heap s.
Proof. ind s. Qed.
Lemma get_after_update_08 : forall (l : locvars_env) (s : state),
    get_heap (update_locvars_env l s) = get_heap s.
Proof. ind s. Qed.
Lemma get_after_update_09 : forall (m : mbody_env) (s : state),
    get_heap (update_mbody_env m s) = get_heap s.
Proof. ind s. Qed.
Lemma get_after_update_10 : forall (h : heap) (s : state),
    get_stack (update_heap h s) = get_stack s.
Proof. ind s. Qed.
Lemma get_after_update_11 : forall (s' : stack) (s : state),
    get_stack (update_stack s' s) = s'.
Proof. ind s. Qed.
Lemma get_after_update_12 : forall (a : alloc) (s : state),
    get_stack (update_alloc a s) = get_stack s.
Proof. ind s. Qed.
Lemma get_after_update_13 : forall (d : dtype) (s : state),
    get_stack (update_dtype d s) = get_stack s.
Proof. ind s. Qed.
Lemma get_after_update_14 : forall (f : fields_env) (s : state),
    get_stack (update_fields_env f s) = get_stack s.
Proof. ind s. Qed.
Lemma get_after_update_15 : forall (s' : super_env) (s : state),
    get_stack (update_super_env s' s) = get_stack s.
Proof. ind s. Qed.
Lemma get_after_update_16 : forall (c : cnames) (s : state),
    get_stack (update_cnames c s) = get_stack s.
Proof. ind s. Qed.
Lemma get_after_update_17 : forall (m : methods_env) (s : state),
    get_stack (update_methods_env m s) = get_stack s.
Proof. ind s. Qed.
Lemma get_after_update_18 : forall (l : locvars_env) (s : state),
    get_stack (update_locvars_env l s) = get_stack s.
Proof. ind s. Qed.
Lemma get_after_update_19 : forall (m : mbody_env) (s : state),
    get_stack (update_mbody_env m s) = get_stack s.
Proof. ind s. Qed.
Lemma get_after_update_20 : forall (h : heap) (s : state),
    get_alloc (update_heap h s) = get_alloc s.
Proof. ind s. Qed.
Lemma get_after_update_21 : forall (s' : stack) (s : state),
    get_alloc (update_stack s' s) = get_alloc s.
Proof. ind s. Qed.
Lemma get_after_update_22 : forall (a : alloc) (s : state),
    get_alloc (update_alloc a s) = a.
Proof. ind s. Qed.
Lemma get_after_update_23 : forall (d : dtype) (s : state),
    get_alloc (update_dtype d s) = get_alloc s.
Proof. ind s. Qed.
Lemma get_after_update_24 : forall (f : fields_env) (s : state),
    get_alloc (update_fields_env f s) = get_alloc s.
Proof. ind s. Qed.
Lemma get_after_update_25 : forall (s' : super_env) (s : state),
    get_alloc (update_super_env s' s) = get_alloc s.
Proof. ind s. Qed.
Lemma get_after_update_26 : forall (c : cnames) (s : state),
    get_alloc (update_cnames c s) = get_alloc s.
Proof. ind s. Qed.
Lemma get_after_update_27 : forall (m : methods_env) (s : state),
    get_alloc (update_methods_env m s) = get_alloc s.
Proof. ind s. Qed.
Lemma get_after_update_28 : forall (l : locvars_env) (s : state),
    get_alloc (update_locvars_env l s) = get_alloc s.
Proof. ind s. Qed.
Lemma get_after_update_29 : forall (m : mbody_env) (s : state),
    get_alloc (update_mbody_env m s) = get_alloc s.
Proof. ind s. Qed.
Lemma get_after_update_30 : forall (h : heap) (s : state),
    get_dtype (update_heap h s) = get_dtype s.
Proof. ind s. Qed.
Lemma get_after_update_31 : forall (s' : stack) (s : state),
    get_dtype (update_stack s' s) = get_dtype s.
Proof. ind s. Qed.
Lemma get_after_update_32 : forall (a : alloc) (s : state),
    get_dtype (update_alloc a s) = get_dtype s.
Proof. ind s. Qed.
Lemma get_after_update_33 : forall (d : dtype) (s : state),
    get_dtype (update_dtype d s) = d.
Proof. ind s. Qed.
Lemma get_after_update_34 : forall (f : fields_env) (s : state),
    get_dtype (update_fields_env f s) = get_dtype s.
Proof. ind s. Qed.
Lemma get_after_update_35 : forall (s' : super_env) (s : state),
    get_dtype (update_super_env s' s) = get_dtype s.
Proof. ind s. Qed.
Lemma get_after_update_36 : forall (c : cnames) (s : state),
    get_dtype (update_cnames c s) = get_dtype s.
Proof. ind s. Qed.
Lemma get_after_update_37 : forall (m : methods_env) (s : state),
    get_dtype (update_methods_env m s) = get_dtype s.
Proof. ind s. Qed.
Lemma get_after_update_38 : forall (l : locvars_env) (s : state),
    get_dtype (update_locvars_env l s) = get_dtype s.
Proof. ind s. Qed.
Lemma get_after_update_39 : forall (m : mbody_env) (s : state),
    get_dtype (update_mbody_env m s) = get_dtype s.
Proof. ind s. Qed.
Lemma get_after_update_40 : forall (h : heap) (s : state),
    get_fields_env (update_heap h s) = get_fields_env s.
Proof. ind s. Qed.
Lemma get_after_update_41 : forall (s' : stack) (s : state),
    get_fields_env (update_stack s' s) = get_fields_env s.
Proof. ind s. Qed.
Lemma get_after_update_42 : forall (a : alloc) (s : state),
    get_fields_env (update_alloc a s) = get_fields_env s.
Proof. ind s. Qed.
Lemma get_after_update_43 : forall (d : dtype) (s : state),
    get_fields_env (update_dtype d s) = get_fields_env s.
Proof. ind s. Qed.
Lemma get_after_update_44 : forall (f : fields_env) (s : state),
    get_fields_env (update_fields_env f s) = f.
Proof. ind s. Qed.
Lemma get_after_update_45 : forall (s' : super_env) (s : state),
    get_fields_env (update_super_env s' s) = get_fields_env s.
Proof. ind s. Qed.
Lemma get_after_update_46 : forall (c : cnames) (s : state),
    get_fields_env (update_cnames c s) = get_fields_env s.
Proof. ind s. Qed.
Lemma get_after_update_47 : forall (m : methods_env) (s : state),
    get_fields_env (update_methods_env m s) = get_fields_env s.
Proof. ind s. Qed.
Lemma get_after_update_48 : forall (l : locvars_env) (s : state),
    get_fields_env (update_locvars_env l s) = get_fields_env s.
Proof. ind s. Qed.
Lemma get_after_update_49 : forall (m : mbody_env) (s : state),
    get_fields_env (update_mbody_env m s) = get_fields_env s.
Proof. ind s. Qed.
Lemma get_after_update_50 : forall (h : heap) (s : state),
    get_super_env (update_heap h s) = get_super_env s.
Proof. ind s. Qed.
Lemma get_after_update_51 : forall (s' : stack) (s : state),
    get_super_env (update_stack s' s) = get_super_env s.
Proof. ind s. Qed.
Lemma get_after_update_52 : forall (a : alloc) (s : state),
    get_super_env (update_alloc a s) = get_super_env s.
Proof. ind s. Qed.
Lemma get_after_update_53 : forall (d : dtype) (s : state),
    get_super_env (update_dtype d s) = get_super_env s.
Proof. ind s. Qed.
Lemma get_after_update_54 : forall (f : fields_env) (s : state),
    get_super_env (update_fields_env f s) = get_super_env s.
Proof. ind s. Qed.
Lemma get_after_update_55 : forall (s' : super_env) (s : state),
    get_super_env (update_super_env s' s) = s'.
Proof. ind s. Qed.
Lemma get_after_update_56 : forall (c : cnames) (s : state),
    get_super_env (update_cnames c s) = get_super_env s.
Proof. ind s. Qed.
Lemma get_after_update_57 : forall (m : methods_env) (s : state),
    get_super_env (update_methods_env m s) = get_super_env s.
Proof. ind s. Qed.
Lemma get_after_update_58 : forall (l : locvars_env) (s : state),
    get_super_env (update_locvars_env l s) = get_super_env s.
Proof. ind s. Qed.
Lemma get_after_update_59 : forall (m : mbody_env) (s : state),
    get_super_env (update_mbody_env m s) = get_super_env s.
Proof. ind s. Qed.
Lemma get_after_update_60 : forall (h : heap) (s : state),
    get_cnames (update_heap h s) = get_cnames s.
Proof. ind s. Qed.
Lemma get_after_update_61 : forall (s' : stack) (s : state),
    get_cnames (update_stack s' s) = get_cnames s.
Proof. ind s. Qed.
Lemma get_after_update_62 : forall (a : alloc) (s : state),
    get_cnames (update_alloc a s) = get_cnames s.
Proof. ind s. Qed.
Lemma get_after_update_63 : forall (d : dtype) (s : state),
    get_cnames (update_dtype d s) = get_cnames s.
Proof. ind s. Qed.
Lemma get_after_update_64 : forall (f : fields_env) (s : state),
    get_cnames (update_fields_env f s) = get_cnames s.
Proof. ind s. Qed.
Lemma get_after_update_65 : forall (s' : super_env) (s : state),
    get_cnames (update_super_env s' s) = get_cnames s.
Proof. ind s. Qed.
Lemma get_after_update_66 : forall (c : cnames) (s : state),
    get_cnames (update_cnames c s) = c.
Proof. ind s. Qed.
Lemma get_after_update_67 : forall (m : methods_env) (s : state),
    get_cnames (update_methods_env m s) = get_cnames s.
Proof. ind s. Qed.
Lemma get_after_update_68 : forall (l : locvars_env) (s : state),
    get_cnames (update_locvars_env l s) = get_cnames s.
Proof. ind s. Qed.
Lemma get_after_update_69 : forall (m : mbody_env) (s : state),
    get_cnames (update_mbody_env m s) = get_cnames s.
Proof. ind s. Qed.
Lemma get_after_update_70 : forall (h : heap) (s : state),
    get_methods_env (update_heap h s) = get_methods_env s.
Proof. ind s. Qed.
Lemma get_after_update_71 : forall (s' : stack) (s : state),
    get_methods_env (update_stack s' s) = get_methods_env s.
Proof. ind s. Qed.
Lemma get_after_update_72 : forall (a : alloc) (s : state),
    get_methods_env (update_alloc a s) = get_methods_env s.
Proof. ind s. Qed.
Lemma get_after_update_73 : forall (d : dtype) (s : state),
    get_methods_env (update_dtype d s) = get_methods_env s.
Proof. ind s. Qed.
Lemma get_after_update_74 : forall (f : fields_env) (s : state),
    get_methods_env (update_fields_env f s) = get_methods_env s.
Proof. ind s. Qed.
Lemma get_after_update_75 : forall (s' : super_env) (s : state),
    get_methods_env (update_super_env s' s) = get_methods_env s.
Proof. ind s. Qed.
Lemma get_after_update_76 : forall (c : cnames) (s : state),
    get_methods_env (update_cnames c s) = get_methods_env s.
Proof. ind s. Qed.
Lemma get_after_update_77 : forall (m : methods_env) (s : state),
    get_methods_env (update_methods_env m s) = m.
Proof. ind s. Qed.
Lemma get_after_update_78 : forall (l : locvars_env) (s : state),
    get_methods_env (update_locvars_env l s) = get_methods_env s.
Proof. ind s. Qed.
Lemma get_after_update_79 : forall (m : mbody_env) (s : state),
    get_methods_env (update_mbody_env m s) = get_methods_env s.
Proof. ind s. Qed.
Lemma get_after_update_80 : forall (h : heap) (s : state),
    get_locvars_env (update_heap h s) = get_locvars_env s.
Proof. ind s. Qed.
Lemma get_after_update_81 : forall (s' : stack) (s : state),
    get_locvars_env (update_stack s' s) = get_locvars_env s.
Proof. ind s. Qed.
Lemma get_after_update_82 : forall (a : alloc) (s : state),
    get_locvars_env (update_alloc a s) = get_locvars_env s.
Proof. ind s. Qed.
Lemma get_after_update_83 : forall (d : dtype) (s : state),
    get_locvars_env (update_dtype d s) = get_locvars_env s.
Proof. ind s. Qed.
Lemma get_after_update_84 : forall (f : fields_env) (s : state),
    get_locvars_env (update_fields_env f s) = get_locvars_env s.
Proof. ind s. Qed.
Lemma get_after_update_85 : forall (s' : super_env) (s : state),
    get_locvars_env (update_super_env s' s) = get_locvars_env s.
Proof. ind s. Qed.
Lemma get_after_update_86 : forall (c : cnames) (s : state),
    get_locvars_env (update_cnames c s) = get_locvars_env s.
Proof. ind s. Qed.
Lemma get_after_update_87 : forall (m : methods_env) (s : state),
    get_locvars_env (update_methods_env m s) = get_locvars_env s.
Proof. ind s. Qed.
Lemma get_after_update_88 : forall (l : locvars_env) (s : state),
    get_locvars_env (update_locvars_env l s) = l.
Proof. ind s. Qed.
Lemma get_after_update_89 : forall (m : mbody_env) (s : state),
    get_locvars_env (update_mbody_env m s) = get_locvars_env s.
Proof. ind s. Qed.
Lemma get_after_update_90 : forall (h : heap) (s : state),
    get_mbody_env (update_heap h s) = get_mbody_env s.
Proof. ind s. Qed.
Lemma get_after_update_91 : forall (s' : stack) (s : state),
    get_mbody_env (update_stack s' s) = get_mbody_env s.
Proof. ind s. Qed.
Lemma get_after_update_92 : forall (a : alloc) (s : state),
    get_mbody_env (update_alloc a s) = get_mbody_env s.
Proof. ind s. Qed.
Lemma get_after_update_93 : forall (d : dtype) (s : state),
    get_mbody_env (update_dtype d s) = get_mbody_env s.
Proof. ind s. Qed.
Lemma get_after_update_94 : forall (f : fields_env) (s : state),
    get_mbody_env (update_fields_env f s) = get_mbody_env s.
Proof. ind s. Qed.
Lemma get_after_update_95 : forall (s' : super_env) (s : state),
    get_mbody_env (update_super_env s' s) = get_mbody_env s.
Proof. ind s. Qed.
Lemma get_after_update_96 : forall (c : cnames) (s : state),
    get_mbody_env (update_cnames c s) = get_mbody_env s.
Proof. ind s. Qed.
Lemma get_after_update_97 : forall (m : methods_env) (s : state),
    get_mbody_env (update_methods_env m s) = get_mbody_env s.
Proof. ind s. Qed.
Lemma get_after_update_98 : forall (l : locvars_env) (s : state),
    get_mbody_env (update_locvars_env l s) = get_mbody_env s.
Proof. ind s. Qed.
Lemma get_after_update_99 : forall (m : mbody_env) (s : state),
    get_mbody_env (update_mbody_env m s) = m.
Proof. ind s. Qed.

Lemma map_comm_01 : forall (mh : heap -> heap) (ms : stack -> stack) (s : state),
    map_heap mh (map_stack ms s) = map_stack ms (map_heap mh s).
Proof. ind s. Qed.
Lemma map_comm_02 : forall (mh : heap -> heap) (ma : alloc -> alloc) (s : state),
    map_heap mh (map_alloc ma s) = map_alloc ma (map_heap mh s).
Proof. ind s. Qed.
Lemma map_comm_03 : forall (mh : heap -> heap) (md : dtype -> dtype) (s : state),
    map_heap mh (map_dtype md s) = map_dtype md (map_heap mh s).
Proof. ind s. Qed.
Lemma map_comm_04 : forall (mh : heap -> heap) (mf : fields_env -> fields_env) (s : state),
    map_heap mh (map_fields_env mf s) = map_fields_env mf (map_heap mh s).
Proof. ind s. Qed.
Lemma map_comm_05 : forall (mh : heap -> heap) (ms : super_env -> super_env) (s : state),
    map_heap mh (map_super_env ms s) = map_super_env ms (map_heap mh s).
Proof. ind s. Qed.
Lemma map_comm_06 : forall (mh : heap -> heap) (mc : cnames -> cnames) (s : state),
    map_heap mh (map_cnames mc s) = map_cnames mc (map_heap mh s).
Proof. ind s. Qed.
Lemma map_comm_07 : forall (mh : heap -> heap) (mm : methods_env -> methods_env) (s : state),
    map_heap mh (map_methods_env mm s) = map_methods_env mm (map_heap mh s).
Proof. ind s. Qed.
Lemma map_comm_08 : forall (mh : heap -> heap) (ml : locvars_env -> locvars_env) (s : state),
    map_heap mh (map_locvars_env ml s) = map_locvars_env ml (map_heap mh s).
Proof. ind s. Qed.
Lemma map_comm_09 : forall (mh : heap -> heap) (mm : mbody_env -> mbody_env) (s : state),
    map_heap mh (map_mbody_env mm s) = map_mbody_env mm (map_heap mh s).
Proof. ind s. Qed.
Lemma map_comm_12 : forall (ms : stack -> stack) (ma : alloc -> alloc) (s : state),
    map_stack ms (map_alloc ma s) = map_alloc ma (map_stack ms s).
Proof. ind s. Qed.
Lemma map_comm_13 : forall (ms : stack -> stack) (md : dtype -> dtype) (s : state),
    map_stack ms (map_dtype md s) = map_dtype md (map_stack ms s).
Proof. ind s. Qed.
Lemma map_comm_14 : forall (ms : stack -> stack) (mf : fields_env -> fields_env) (s : state),
    map_stack ms (map_fields_env mf s) = map_fields_env mf (map_stack ms s).
Proof. ind s. Qed.
Lemma map_comm_15 : forall (ms : stack -> stack) (ms' : super_env -> super_env) (s : state),
    map_stack ms (map_super_env ms' s) = map_super_env ms' (map_stack ms s).
Proof. ind s. Qed.
Lemma map_comm_16 : forall (ms : stack -> stack) (mc : cnames -> cnames) (s : state),
    map_stack ms (map_cnames mc s) = map_cnames mc (map_stack ms s).
Proof. ind s. Qed.
Lemma map_comm_17 : forall (ms : stack -> stack) (mm : methods_env -> methods_env) (s : state),
    map_stack ms (map_methods_env mm s) = map_methods_env mm (map_stack ms s).
Proof. ind s. Qed.
Lemma map_comm_18 : forall (ms : stack -> stack) (ml : locvars_env -> locvars_env) (s : state),
    map_stack ms (map_locvars_env ml s) = map_locvars_env ml (map_stack ms s).
Proof. ind s. Qed.
Lemma map_comm_19 : forall (ms : stack -> stack) (mm : mbody_env -> mbody_env) (s : state),
    map_stack ms (map_mbody_env mm s) = map_mbody_env mm (map_stack ms s).
Proof. ind s. Qed.
Lemma map_comm_23 : forall (ma : alloc -> alloc) (md : dtype -> dtype) (s : state),
    map_alloc ma (map_dtype md s) = map_dtype md (map_alloc ma s).
Proof. ind s. Qed.
Lemma map_comm_24 : forall (ma : alloc -> alloc) (mf : fields_env -> fields_env) (s : state),
    map_alloc ma (map_fields_env mf s) = map_fields_env mf (map_alloc ma s).
Proof. ind s. Qed.
Lemma map_comm_25 : forall (ma : alloc -> alloc) (ms : super_env -> super_env) (s : state),
    map_alloc ma (map_super_env ms s) = map_super_env ms (map_alloc ma s).
Proof. ind s. Qed.
Lemma map_comm_26 : forall (ma : alloc -> alloc) (mc : cnames -> cnames) (s : state),
    map_alloc ma (map_cnames mc s) = map_cnames mc (map_alloc ma s).
Proof. ind s. Qed.
Lemma map_comm_27 : forall (ma : alloc -> alloc) (mm : methods_env -> methods_env) (s : state),
    map_alloc ma (map_methods_env mm s) = map_methods_env mm (map_alloc ma s).
Proof. ind s. Qed.
Lemma map_comm_28 : forall (ma : alloc -> alloc) (ml : locvars_env -> locvars_env) (s : state),
    map_alloc ma (map_locvars_env ml s) = map_locvars_env ml (map_alloc ma s).
Proof. ind s. Qed.
Lemma map_comm_29 : forall (ma : alloc -> alloc) (mm : mbody_env -> mbody_env) (s : state),
    map_alloc ma (map_mbody_env mm s) = map_mbody_env mm (map_alloc ma s).
Proof. ind s. Qed.
Lemma map_comm_34 : forall (md : dtype -> dtype) (mf : fields_env -> fields_env) (s : state),
    map_dtype md (map_fields_env mf s) = map_fields_env mf (map_dtype md s).
Proof. ind s. Qed.
Lemma map_comm_35 : forall (md : dtype -> dtype) (ms : super_env -> super_env) (s : state),
    map_dtype md (map_super_env ms s) = map_super_env ms (map_dtype md s).
Proof. ind s. Qed.
Lemma map_comm_36 : forall (md : dtype -> dtype) (mc : cnames -> cnames) (s : state),
    map_dtype md (map_cnames mc s) = map_cnames mc (map_dtype md s).
Proof. ind s. Qed.
Lemma map_comm_37 : forall (md : dtype -> dtype) (mm : methods_env -> methods_env) (s : state),
    map_dtype md (map_methods_env mm s) = map_methods_env mm (map_dtype md s).
Proof. ind s. Qed.
Lemma map_comm_38 : forall (md : dtype -> dtype) (ml : locvars_env -> locvars_env) (s : state),
    map_dtype md (map_locvars_env ml s) = map_locvars_env ml (map_dtype md s).
Proof. ind s. Qed.
Lemma map_comm_39 : forall (md : dtype -> dtype) (mm : mbody_env -> mbody_env) (s : state),
    map_dtype md (map_mbody_env mm s) = map_mbody_env mm (map_dtype md s).
Proof. ind s. Qed.
Lemma map_comm_45 : forall (mf : fields_env -> fields_env) (ms : super_env -> super_env) (s : state),
    map_fields_env mf (map_super_env ms s) = map_super_env ms (map_fields_env mf s).
Proof. ind s. Qed.
Lemma map_comm_46 : forall (mf : fields_env -> fields_env) (mc : cnames -> cnames) (s : state),
    map_fields_env mf (map_cnames mc s) = map_cnames mc (map_fields_env mf s).
Proof. ind s. Qed.
Lemma map_comm_47 : forall (mf : fields_env -> fields_env) (mm : methods_env -> methods_env) (s : state),
    map_fields_env mf (map_methods_env mm s) = map_methods_env mm (map_fields_env mf s).
Proof. ind s. Qed.
Lemma map_comm_48 : forall (mf : fields_env -> fields_env) (ml : locvars_env -> locvars_env) (s : state),
    map_fields_env mf (map_locvars_env ml s) = map_locvars_env ml (map_fields_env mf s).
Proof. ind s. Qed.
Lemma map_comm_49 : forall (mf : fields_env -> fields_env) (mm : mbody_env -> mbody_env) (s : state),
    map_fields_env mf (map_mbody_env mm s) = map_mbody_env mm (map_fields_env mf s).
Proof. ind s. Qed.
Lemma map_comm_56 : forall (ms : super_env -> super_env) (mc : cnames -> cnames) (s : state),
    map_super_env ms (map_cnames mc s) = map_cnames mc (map_super_env ms s).
Proof. ind s. Qed.
Lemma map_comm_57 : forall (ms : super_env -> super_env) (mm : methods_env -> methods_env) (s : state),
    map_super_env ms (map_methods_env mm s) = map_methods_env mm (map_super_env ms s).
Proof. ind s. Qed.
Lemma map_comm_58 : forall (ms : super_env -> super_env) (ml : locvars_env -> locvars_env) (s : state),
    map_super_env ms (map_locvars_env ml s) = map_locvars_env ml (map_super_env ms s).
Proof. ind s. Qed.
Lemma map_comm_59 : forall (ms : super_env -> super_env) (mm : mbody_env -> mbody_env) (s : state),
    map_super_env ms (map_mbody_env mm s) = map_mbody_env mm (map_super_env ms s).
Proof. ind s. Qed.
Lemma map_comm_67 : forall (mc : cnames -> cnames) (mm : methods_env -> methods_env) (s : state),
    map_cnames mc (map_methods_env mm s) = map_methods_env mm (map_cnames mc s).
Proof. ind s. Qed.
Lemma map_comm_68 : forall (mc : cnames -> cnames) (ml : locvars_env -> locvars_env) (s : state),
    map_cnames mc (map_locvars_env ml s) = map_locvars_env ml (map_cnames mc s).
Proof. ind s. Qed.
Lemma map_comm_69 : forall (mc : cnames -> cnames) (mm : mbody_env -> mbody_env) (s : state),
    map_cnames mc (map_mbody_env mm s) = map_mbody_env mm (map_cnames mc s).
Proof. ind s. Qed.
Lemma map_comm_78 : forall (mm : methods_env -> methods_env) (ml : locvars_env -> locvars_env) (s : state),
    map_methods_env mm (map_locvars_env ml s) = map_locvars_env ml (map_methods_env mm s).
Proof. ind s. Qed.
Lemma map_comm_79 : forall (mm : methods_env -> methods_env) (mm' : mbody_env -> mbody_env) (s : state),
    map_methods_env mm (map_mbody_env mm' s) = map_mbody_env mm' (map_methods_env mm s).
Proof. ind s. Qed.
Lemma map_comm_89 : forall (ml : locvars_env -> locvars_env) (mm' : mbody_env -> mbody_env) (s : state),
    map_locvars_env ml (map_mbody_env mm' s) = map_mbody_env mm' (map_locvars_env ml s).
Proof. ind s. Qed.

Lemma update_comm_01 : forall (h : heap) (s' : stack) (s : state),
    update_heap h (update_stack s' s) = update_stack s' (update_heap h s).
Proof. ind s. Qed.
Lemma update_comm_02 : forall (h : heap) (a : alloc) (s : state),
    update_heap h (update_alloc a s) = update_alloc a (update_heap h s).
Proof. ind s. Qed.
Lemma update_comm_03 : forall (h : heap) (d : dtype) (s : state),
    update_heap h (update_dtype d s) = update_dtype d (update_heap h s).
Proof. ind s. Qed.
Lemma update_comm_04 : forall (h : heap) (f : fields_env) (s : state),
    update_heap h (update_fields_env f s) = update_fields_env f (update_heap h s).
Proof. ind s. Qed.
Lemma update_comm_05 : forall (h : heap) (s' : super_env) (s : state),
    update_heap h (update_super_env s' s) = update_super_env s' (update_heap h s).
Proof. ind s. Qed.
Lemma update_comm_06 : forall (h : heap) (c : cnames) (s : state),
    update_heap h (update_cnames c s) = update_cnames c (update_heap h s).
Proof. ind s. Qed.
Lemma update_comm_07 : forall (h : heap) (m : methods_env) (s : state),
    update_heap h (update_methods_env m s) = update_methods_env m (update_heap h s).
Proof. ind s. Qed.
Lemma update_comm_08 : forall (h : heap) (l : locvars_env) (s : state),
    update_heap h (update_locvars_env l s) = update_locvars_env l (update_heap h s).
Proof. ind s. Qed.
Lemma update_comm_09 : forall (h : heap) (m : mbody_env) (s : state),
    update_heap h (update_mbody_env m s) = update_mbody_env m (update_heap h s).
Proof. ind s. Qed.
Lemma update_comm_12 : forall (s' : stack) (a : alloc) (s : state),
    update_stack s' (update_alloc a s) = update_alloc a (update_stack s' s).
Proof. ind s. Qed.
Lemma update_comm_13 : forall (s' : stack) (d : dtype) (s : state),
    update_stack s' (update_dtype d s) = update_dtype d (update_stack s' s).
Proof. ind s. Qed.
Lemma update_comm_14 : forall (s' : stack) (f : fields_env) (s : state),
    update_stack s' (update_fields_env f s) = update_fields_env f (update_stack s' s).
Proof. ind s. Qed.
Lemma update_comm_15 : forall (s' : stack) (s'' : super_env) (s : state),
    update_stack s' (update_super_env s'' s) = update_super_env s'' (update_stack s' s).
Proof. ind s. Qed.
Lemma update_comm_16 : forall (s' : stack) (c : cnames) (s : state),
    update_stack s' (update_cnames c s) = update_cnames c (update_stack s' s).
Proof. ind s. Qed.
Lemma update_comm_17 : forall (s' : stack) (m : methods_env) (s : state),
    update_stack s' (update_methods_env m s) = update_methods_env m (update_stack s' s).
Proof. ind s. Qed.
Lemma update_comm_18 : forall (s' : stack) (l : locvars_env) (s : state),
    update_stack s' (update_locvars_env l s) = update_locvars_env l (update_stack s' s).
Proof. ind s. Qed.
Lemma update_comm_19 : forall (s' : stack) (m : mbody_env) (s : state),
    update_stack s' (update_mbody_env m s) = update_mbody_env m (update_stack s' s).
Proof. ind s. Qed.
Lemma update_comm_23 : forall (a : alloc) (d : dtype) (s : state),
    update_alloc a (update_dtype d s) = update_dtype d (update_alloc a s).
Proof. ind s. Qed.
Lemma update_comm_24 : forall (a : alloc) (f : fields_env) (s : state),
    update_alloc a (update_fields_env f s) = update_fields_env f (update_alloc a s).
Proof. ind s. Qed.
Lemma update_comm_25 : forall (a : alloc) (s' : super_env) (s : state),
    update_alloc a (update_super_env s' s) = update_super_env s' (update_alloc a s).
Proof. ind s. Qed.
Lemma update_comm_26 : forall (a : alloc) (c : cnames) (s : state),
    update_alloc a (update_cnames c s) = update_cnames c (update_alloc a s).
Proof. ind s. Qed.
Lemma update_comm_27 : forall (a : alloc) (m : methods_env) (s : state),
    update_alloc a (update_methods_env m s) = update_methods_env m (update_alloc a s).
Proof. ind s. Qed.
Lemma update_comm_28 : forall (a : alloc) (l : locvars_env) (s : state),
    update_alloc a (update_locvars_env l s) = update_locvars_env l (update_alloc a s).
Proof. ind s. Qed.
Lemma update_comm_29 : forall (a : alloc) (m : mbody_env) (s : state),
    update_alloc a (update_mbody_env m s) = update_mbody_env m (update_alloc a s).
Proof. ind s. Qed.
Lemma update_comm_34 : forall (d : dtype) (f : fields_env) (s : state),
    update_dtype d (update_fields_env f s) = update_fields_env f (update_dtype d s).
Proof. ind s. Qed.
Lemma update_comm_35 : forall (d : dtype) (s' : super_env) (s : state),
    update_dtype d (update_super_env s' s) = update_super_env s' (update_dtype d s).
Proof. ind s. Qed.
Lemma update_comm_36 : forall (d : dtype) (c : cnames) (s : state),
    update_dtype d (update_cnames c s) = update_cnames c (update_dtype d s).
Proof. ind s. Qed.
Lemma update_comm_37 : forall (d : dtype) (m : methods_env) (s : state),
    update_dtype d (update_methods_env m s) = update_methods_env m (update_dtype d s).
Proof. ind s. Qed.
Lemma update_comm_38 : forall (d : dtype) (l : locvars_env) (s : state),
    update_dtype d (update_locvars_env l s) = update_locvars_env l (update_dtype d s).
Proof. ind s. Qed.
Lemma update_comm_39 : forall (d : dtype) (m : mbody_env) (s : state),
    update_dtype d (update_mbody_env m s) = update_mbody_env m (update_dtype d s).
Proof. ind s. Qed.
Lemma update_comm_45 : forall (f : fields_env) (s' : super_env) (s : state),
    update_fields_env f (update_super_env s' s) = update_super_env s' (update_fields_env f s).
Proof. ind s. Qed.
Lemma update_comm_46 : forall (f : fields_env) (c : cnames) (s : state),
    update_fields_env f (update_cnames c s) = update_cnames c (update_fields_env f s).
Proof. ind s. Qed.
Lemma update_comm_47 : forall (f : fields_env) (m : methods_env) (s : state),
    update_fields_env f (update_methods_env m s) = update_methods_env m (update_fields_env f s).
Proof. ind s. Qed.
Lemma update_comm_48 : forall (f : fields_env) (l : locvars_env) (s : state),
    update_fields_env f (update_locvars_env l s) = update_locvars_env l (update_fields_env f s).
Proof. ind s. Qed.
Lemma update_comm_49 : forall (f : fields_env) (m : mbody_env) (s : state),
    update_fields_env f (update_mbody_env m s) = update_mbody_env m (update_fields_env f s).
Proof. ind s. Qed.
Lemma update_comm_56 : forall (s' : super_env) (c : cnames) (s : state),
    update_super_env s' (update_cnames c s) = update_cnames c (update_super_env s' s).
Proof. ind s. Qed.
Lemma update_comm_57 : forall (s' : super_env) (m : methods_env) (s : state),
    update_super_env s' (update_methods_env m s) = update_methods_env m (update_super_env s' s).
Proof. ind s. Qed.
Lemma update_comm_58 : forall (s' : super_env) (l : locvars_env) (s : state),
    update_super_env s' (update_locvars_env l s) = update_locvars_env l (update_super_env s' s).
Proof. ind s. Qed.
Lemma update_comm_59 : forall (s' : super_env) (m : mbody_env) (s : state),
    update_super_env s' (update_mbody_env m s) = update_mbody_env m (update_super_env s' s).
Proof. ind s. Qed.
Lemma update_comm_67 : forall (c : cnames) (m : methods_env) (s : state),
    update_cnames c (update_methods_env m s) = update_methods_env m (update_cnames c s).
Proof. ind s. Qed.
Lemma update_comm_68 : forall (c : cnames) (l : locvars_env) (s : state),
    update_cnames c (update_locvars_env l s) = update_locvars_env l (update_cnames c s).
Proof. ind s. Qed.
Lemma update_comm_69 : forall (c : cnames) (m : mbody_env) (s : state),
    update_cnames c (update_mbody_env m s) = update_mbody_env m (update_cnames c s).
Proof. ind s. Qed.
Lemma update_comm_78 : forall (m : methods_env) (l : locvars_env) (s : state),
    update_methods_env m (update_locvars_env l s) = update_locvars_env l (update_methods_env m s).
Proof. ind s. Qed.
Lemma update_comm_79 : forall (m : methods_env) (m' : mbody_env) (s : state),
    update_methods_env m (update_mbody_env m' s) = update_mbody_env m' (update_methods_env m s).
Proof. ind s. Qed.
Lemma update_comm_89 : forall (l : locvars_env) (m : mbody_env) (s : state),
    update_locvars_env l (update_mbody_env m s) = update_mbody_env m (update_locvars_env l s).
Proof. ind s. Qed.

Lemma find_mbody_1 : forall (r : rtype) (m : method) (mt : method_type) (a : args)
                            (lv : method_locvars) (c : cmd) (s : state), 
    MEnv.find_mbody (get_mbody_env (build_method r m mt a lv c s)) r m =
    Some (a, MEnv.make_locvars lv, Some c).
Proof.
  intros r m mt a lv c s.
  unfold build_method.
  rewrite get_after_map_97.
  rewrite get_after_map_98.
  rewrite get_after_map_99.
  assert (MEnv.pin r m (a, MEnv.make_locvars lv, Some c)
    (MEnv.update_mbody_env r m (a, MEnv.make_locvars lv, Some c) (get_mbody_env s))).
  apply MEnv.in_update_1.
  apply MEnv.in_find in H.
  rewrite H. reflexivity.
Qed.


Lemma find_mbody_comm1 : forall (r c : rtype) (l : list rtype) (m : method)
                                (mf : field_type -> field_type) (s : state), 
  c <> r -> MEnv.find_mbody (get_mbody_env (build_class c l mf s)) r m
  = MEnv.find_mbody (get_mbody_env s) r m.
Proof.
  intros r c l m mf s H.
  unfold build_class.
  case l. reflexivity. intros r0 l0.
  case (TEnv.get_fields r0 (get_fields_env s)).
  case (TEnv.find_class_methods r0 (get_methods_env s)).
  case (MEnv.find_class_mbody r0 (get_mbody_env s)).
  intros t c0 f. rewrite get_after_map_95.
  rewrite get_after_map_97.
  rewrite get_after_map_99.
  rewrite get_after_map_94.
  rewrite get_after_map_94.
  rewrite get_after_map_96.
  unfold MEnv.update_class_mbody.
  inductS (MEnv.find_mbody (get_mbody_env s) r m).
  rewrite <- MEnv.in_find. rewrite <- MEnv.in_find in H0.
  do 2 destruct H0. exists x0.
  split; [apply Smap.add_2|]; assumption.
  rewrite <- MEnv.not_in_find. rewrite <- MEnv.not_in_find in H0.
  intros b H1; do 2 destruct H1. apply Smap.add_3 in H1.
  elim H0 with (b := b); exists x; split; assumption.
  assumption. reflexivity. reflexivity. reflexivity.
Qed.

Lemma find_mbody_comm2 : forall (r1 r2 : rtype) (m1 m2 : method) (mt : method_type)
                         (a : args) (lv : method_locvars) (c : cmd) (s : state), 
    r1 <> r2 \/ m1 <> m2 -> MEnv.find_mbody (get_mbody_env (build_method r2 m2 mt a lv c s)) r1 m1
                          = MEnv.find_mbody (get_mbody_env s) r1 m1.
Proof.
  intros r1 r2 m1 m2 mt a lv c s H.
  unfold build_method.
  rewrite get_after_map_97.
  rewrite get_after_map_98.
  rewrite get_after_map_99.
  inductS (MEnv.find_mbody (get_mbody_env s) r1 m1).
  apply MEnv.in_find.
  apply MEnv.in_update_2. assumption.
  apply MEnv.in_find in H0. assumption.
  apply MEnv.not_in_find.
  intros b H1. apply MEnv.in_update_3 in H1.
  apply MEnv.in_find in H1. rewrite H1 in H0.
  inversion H0. assumption.
Qed.

Lemma in_mbody_env_1 : forall (r r1 : rtype) (m m1 : method) (mt : method_type)
                       (a : args) (lv : method_locvars) (c : cmd) (s : state),
    (r = r1 /\ m = m1) \/ MEnv.In r m (get_mbody_env s) <->
    MEnv.In r m (get_mbody_env (build_method r1 m1 mt a lv c s)).
Proof.
  intros r r1 m m1 mt a lv c s.
  split. intro H.
  unfold build_method.
  rewrite get_after_map_97.
  rewrite get_after_map_98.
  rewrite get_after_map_99.
  unfold MEnv.In. destruct H.
  exists (a, MEnv.make_locvars lv, Some c).
  destruct H. rewrite H. rewrite H0.
  split. apply MEnv.in_update_1. discriminate.
  case RType.eq_dec with (s1 := r) (s2 := r1).
  case Method.eq_dec with (s1 := m) (s2 := m1).
  intros H0 H1. exists (a, MEnv.make_locvars lv, Some c).
  rewrite H0. rewrite H1. split.
  apply MEnv.in_update_1. discriminate.
  intros H0 H1. do 2 destruct H. exists x.
  split; try apply MEnv.in_update_2; try right; assumption.
  intro H0. do 2 destruct H. exists x.
  split; try apply MEnv.in_update_2; try left; assumption.
  case RType.eq_dec with (s1 := r) (s2 := r1).
  case Method.eq_dec with (s1 := m) (s2 := m1).
  intros H H0 H1; left; split; assumption.
  intros H H0 [mb [H1 h2]]; right. exists mb.
  apply MEnv.in_find in H1. rewrite find_mbody_comm2 in H1.
  apply MEnv.in_find in H1. split; assumption.
  right; assumption.
  intros H [mb [H0 H1]]. right. exists mb.
  apply MEnv.in_find in H0. rewrite find_mbody_comm2 in H0.
  apply MEnv.in_find in H0. split; assumption.
  left; assumption.
Qed.

Lemma in_mbody_env_2' : forall (r c : rtype) (l : list rtype) (m : method)
                              (mf : field_type -> field_type) (s : state), 
    MEnv.In r m (get_mbody_env (build_class c l mf s)) ->
         r = c /\ MEnv.In (List.hd r l) m (get_mbody_env s)
      \/ MEnv.In r m (get_mbody_env s).
Proof.
  intros r c l; case l; unfold List.hd.
  unfold build_class; intro H.
  right; assumption.
  unfold build_class; intros.
  inductS (TEnv.get_fields r0 (get_fields_env s)); rewrite H0 in H.
  inductS (TEnv.find_class_methods r0 (get_methods_env s)); rewrite H1 in H.
  inductS (MEnv.find_class_mbody r0 (get_mbody_env s)); rewrite H2 in H.
  rewrite get_after_map_95 in H.
  rewrite get_after_map_97 in H.
  rewrite get_after_map_99 in H.
  rewrite get_after_map_94 in H.
  rewrite get_after_map_94 in H.
  rewrite get_after_map_96 in H.
  unfold MEnv.update_class_mbody in H.
  do 4 destruct H. case (RType.eq_dec r c).
  intro H5. rewrite H5 in H.
  apply smap_add in H. subst.
  left; split. reflexivity.
  apply Smap.find_2 in H2.
  exists x2. split; [exists x1; split|]; assumption.
  intro H5. right. apply Smap.add_3 in H.
  exists x2; split; [exists x3; split|]; assumption.
  auto. right; assumption.
  right; assumption.
  right; assumption.
Qed.

Axiom in_mbody_env_2 : forall (r c : rtype) (l : list rtype) (m : method)
                              (mf : field_type -> field_type) (s : state), 
    MEnv.In r m (get_mbody_env (build_class c l mf s)) <->
         r = c /\ m <> (List.hd r l) /\ MEnv.In (List.hd r l) m (get_mbody_env s)
      \/ MEnv.In r m (get_mbody_env s).

Lemma in_mbody_env_3' : forall (r r1 : rtype) (m m1 : method) (mt : method_type)
                              (a : args) (s : state),
    MEnv.In r m (get_mbody_env (build_msign r1 m1 mt a s))
    -> MEnv.In r m (get_mbody_env s).
Proof.
  unfold build_msign; intros.
  rewrite get_after_map_97 in H.
  rewrite get_after_map_99 in H.
  do 2 destruct H.
  case (RType.eq_dec r r1).
  case (RType.eq_dec m m1).
  exists x; split; [|assumption]. subst.
  assert (MEnv.pin r1 m1 (a, MEnv.no_locvars, None)
      (MEnv.update_mbody_env r1 m1 (a, MEnv.no_locvars, None)
         (get_mbody_env s))).
  apply MEnv.in_update_1.
  apply MEnv.in_find in H; apply MEnv.in_find in H1.
  rewrite H1 in H; inversion H.
  rewrite <- H3 in H0; elim H0; auto.
  intros; apply MEnv.in_update_3 in H.
  exists x; split; assumption.
  right; assumption.
  intro H1; apply MEnv.in_update_3 in H.
  exists x; split; assumption.
  left; assumption.
Qed.

Axiom in_mbody_env_3 : forall (r r1 : rtype) (m m1 : method) (mt : method_type)
                              (a : args) (s : state),
    MEnv.In r m (get_mbody_env (build_msign r1 m1 mt a s))
    <-> MEnv.In r m (get_mbody_env s).

Axiom in_mbody_env_4 : forall (r c : rtype) (t : option rtype) (m : method) (s : state), 
    MEnv.In r m (get_mbody_env (build_interf c t s))
    <-> MEnv.In r m (get_mbody_env s).

Open Scope string_scope.

Lemma in_mbody_env_init : forall (r : rtype) (m : method), 
    MEnv.In r m (get_mbody_env init_state) <-> False.
Proof.
  split. intro H. unfold init_state in H.
  unfold get_mbody_env in H. do 4 destruct H.
  assert (x0 = Smap.empty MEnv.method_body).
  unfold MEnv.init_mbody_env in H.
  case (RType.eq_dec r "Object").
  intro H2. rewrite <- H2 in H.
  apply smap_inject with (k := r) (m := Smap.add r MEnv.no_method
   (Smap.add "Bool" MEnv.no_method
    (Smap.add "Null" MEnv.no_method (Smap.empty (Smap.t MEnv.method_body))))).
  assumption. apply Smap.add_1. reflexivity.
  intro H2. apply Smap.add_3 in H.
  case (RType.eq_dec r "Bool").
  intro H3. rewrite <- H3 in H.
  apply smap_inject with (k := r) (m := Smap.add r MEnv.no_method
    (Smap.add "Null" MEnv.no_method (Smap.empty (Smap.t MEnv.method_body)))).
  assumption. apply Smap.add_1. reflexivity.
  intro H3. apply Smap.add_3 in H.
  case (RType.eq_dec r "Null").
  intro H4. rewrite <- H4 in H.
  apply smap_inject with (k := r) (m := Smap.add r MEnv.no_method
    (Smap.empty (Smap.t MEnv.method_body))).
  assumption. apply Smap.add_1. reflexivity.
  intro H4. apply Smap.add_3 in H.
  apply Smap.empty_1 in H. elim H.
  auto. auto. auto. rewrite H2 in H1.
  apply Smap.empty_1 in H1. elim H1.
  intro H; elim H.
Qed.

Close Scope string_scope.

(*
Lemma get_super_1 : forall (c : rtype) (l : list rtype) mf (s : state), 
    RType.get_super c (get_super_env (build_class c l mf s)) = Some l.
Proof.
  intros c l mf s.
  unfold build_class.
  rewrite get_after_map_55.
  unfold TEnv.update_super; unfold RType.get_super.
  unfold RType.update_subtype_env.
  apply Smap.find_1.
  apply Smap.add_1. reflexivity.
Qed.
*)

Lemma get_super_comm1 : forall (r c : rtype) l mf (s : state), 
    ~ (RType.peq c r) -> RType.get_super r (get_super_env (build_class c l mf s))
                       = RType.get_super r (get_super_env s).
Proof.
  intros r c l mf s H.
  unfold build_class.
  induction l. reflexivity.
  case (TEnv.get_fields a (get_fields_env s)).
  case (TEnv.find_class_methods a (get_methods_env s)).
  case (MEnv.find_class_mbody a (get_mbody_env s)).
  intros t c0 f.
  rewrite get_after_map_55.
  rewrite get_after_map_57.
  rewrite get_after_map_59.
  rewrite get_after_map_54.
  rewrite get_after_map_54.
  rewrite get_after_map_56.
  inductS (RType.get_super r (get_super_env s)).
  unfold RType.get_super. apply Smap.find_1.
  unfold RType.get_super in H0. apply Smap.find_2 in H0.
  apply Smap.add_2. assumption. assumption.
  unfold RType.get_super.
  inductS (Smap.find r (TEnv.update_super c (a::l) (get_super_env s))).
  apply Smap.find_2 in H1. apply Smap.add_3 in H1.
  apply Smap.find_1 in H1. unfold RType.get_super in H0.
  rewrite H1 in H0. discriminate. assumption.
  reflexivity. reflexivity.
  reflexivity. reflexivity.
Qed.

Lemma get_super_comm2 : forall (r r2 : rtype) (m : method) (mt : method_type)
                        (a : args) (lv : method_locvars) (c : cmd) (s : state), 
    RType.get_super r (get_super_env (build_method r2 m mt a lv c s))
  = RType.get_super r (get_super_env s).
Proof.
  intros r r2 m mt a lv c s.
  unfold build_method.
  rewrite get_after_map_57.
  rewrite get_after_map_58.
  rewrite get_after_map_59.
  reflexivity.
Qed.

(*
Lemma get_cnames_1 : forall (c1 c2 : rtype) (ft : field_type) (s : state), 
    get_cnames (build_class c1 c2 ft s) = TEnv.cnames_add c1 (get_cnames s).
Proof.
  intros c1 c2 ft s. unfold build_class.
  rewrite get_after_map_65.
  rewrite get_after_map_64.
  rewrite get_after_map_66.
  reflexivity.
Qed.

Lemma get_cnames_comm1 : forall (r : rtype) (m : method) (mt : method_type)
                         (a : args) (lv : method_locvars) (c : cmd) (s : state), 
    get_cnames (build_method r m mt a lv c s) = get_cnames s.
Proof.
  intros r m mt a lv c s.
  unfold build_method.
  rewrite get_after_map_67.
  rewrite get_after_map_68.
  rewrite get_after_map_69.
  reflexivity.
Qed.
*)

End State.

Bind Scope state_scope with State.state.
Delimit Scope state_scope with state.

Infix "`=`" := State.seq (at level 70, no associativity) : state_scope.
