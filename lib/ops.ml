open Core_kernel
open Typed
open Prog

let bigint_to_bool_list (b: Bigint.t) : bool list =
  failwith "bigint_to_bool_list unimplemented"

let bool_list_to_bigint (b: bool list) :  Bigint.t =
  failwith "bool_list_to_bigint unimplemented"

let interp_binary_op (op: coq_OpBin) (l: coq_ValueBase) (r: coq_ValueBase) =
  Poulet4.Ops.Ops.eval_binary_op op l r

let interp_unary_op (op: coq_OpUni) (v: coq_ValueBase) =
  Poulet4.Ops.Ops.eval_unary_op op v

(*----------------------------------------------------------------------------*)
(* Cast evaluation                                                            *)
(*----------------------------------------------------------------------------*)

let bool_of_val (v : coq_ValueBase) : coq_ValueBase =
  failwith "unimplemented"

let bit_of_val (width : int) (v : coq_ValueBase) : coq_ValueBase =
  failwith "unimplemented"

let int_of_val (width : int) (v : coq_ValueBase) : coq_ValueBase =
  failwith "unimplemented"

let bigint_of_val (v : coq_Value) : Bigint.t =
  failwith "unimplemented"

let bits_of_val (v: coq_Value) : bool list =
  failwith "unimplemented"

let fields_for_cast (fields: Typed.coq_FieldType list) (value: coq_ValueBase) =
  match value with
  | ValBaseTuple vals ->
     let fields_vals = List.zip_exn fields vals in
     List.map ~f:(fun ((f, _), v) -> f, v) fields_vals
  | ValBaseRecord fields -> fields
  | _ -> failwith "cannot cast"

let interp_cast ~type_lookup:(type_lookup: P4name.t -> Typed.coq_P4Type)
      (new_type: coq_P4Type) (value: coq_ValueBase) : coq_ValueBase =
  failwith "unimplemented"
