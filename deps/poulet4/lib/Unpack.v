Require Import Coq.Numbers.BinNums.

Require Import Monads.Monad.
Require Import Monads.State.

Require String.
Require Import Syntax.
Require Import Environment.

Section Unpack.
  Context (tags_t: Type).
  Notation env_monad := (env_monad tags_t).
  Notation Value := (Value tags_t).
  Notation ValueBase := (ValueBase tags_t).
  Notation ValueLoc := (ValueLoc tags_t).
  Notation P4String := (P4String.t tags_t).
  Notation P4Int := (P4Int.t tags_t).
  Notation P4Parameter := (Typed.P4Parameter tags_t).
  Definition unpack_bool (wrapped: env_monad Value) : env_monad bool :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValBase _ (ValBaseBool _ b) => mret b
    | _ => state_fail Internal
    end.

  (* TODO: unpack_fixed_bit, unpack_var_bit; dependent types make things hard here *)
  Definition unpack_fixed_int (wrapped: env_monad Value) : env_monad (nat * Z) :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValBase _ (ValBaseInt _ w n) => (state_return (w, n):env_monad (nat*Z))
    | _ => state_fail Internal
    end.

  Definition unpack_inf_int (wrapped: env_monad Value) : env_monad Z :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValBase _ (ValBaseInteger _ n) => mret n
    | _ => state_fail Internal
    end.

  Definition unpack_string (wrapped: env_monad Value) : env_monad String.t :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValBase _ (ValBaseString _ s) => mret s.(P4String.str)
    | _ => state_fail Internal
    end.

  Definition unpack_array (wrapped: env_monad Value) : env_monad (list ValueBase) :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValBase _ (ValBaseTuple _ vals) => mret vals
    | _ => state_fail Internal
    end.

  Definition unpack_error (wrapped: env_monad Value) : env_monad P4String :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValBase _ (ValBaseError _ e) => mret e
    | _ => state_fail Internal
    end.

  Definition unpack_record (wrapped: env_monad Value) :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValBase _ (ValBaseRecord _ fs) => mret fs
    | _ => state_fail Internal
    end.

  Definition unpack_builtin_func (wrapped: env_monad Value) :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValObj _ (ValObjBuiltinFun _ name obj) => mret (name, obj)
    | _ => state_fail Internal
    end.

  Definition unpack_extern_func (wrapped: env_monad Value) : env_monad (P4String * option (ValueLoc * P4String) * list P4Parameter) :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValObj _ (ValObjExternFun _ name obj params) => mret (name, obj, params)
    | _ => state_fail Internal
    end.

  Definition unpack_extern_obj (wrapped: env_monad Value) : env_monad (list (P4String * list P4Parameter)) :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValCons _ (ValConsExternObj _ e) => mret e
    | _ => state_fail Internal
    end.

  Definition unpack_header (wrapped: env_monad Value) : env_monad (list (P4String * ValueBase) * bool) :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValBase _ (ValBaseHeader _ h v) => mret (h, v)
    | _ => state_fail Internal
    end.

  Definition unpack_header_stack (wrapped: env_monad Value) : env_monad (list ValueBase * nat * nat) :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValBase _ (ValBaseStack _ hdrs size next)  => mret (hdrs, size, next)
    | _ => state_fail Internal
    end.

End Unpack.