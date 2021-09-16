open Core_kernel
open Typed
open Prog

let interp_binary_op (op: coq_OpBin) (l: coq_ValueBase) (r: coq_ValueBase) =
  Poulet4.Ops.eval_binop


let interp_unary_op (op: coq_OpUni) (v: coq_ValueBase) =
  match op with
  | Not    -> eval_not v
  | BitNot -> eval_bitnot v
  | UMinus -> eval_uminus v

(*----------------------------------------------------------------------------*)
(* Cast evaluation                                                            *)
(*----------------------------------------------------------------------------*)

let bool_of_val (v : coq_ValueBase) : coq_ValueBase =
  failwith "unimplemented"

let bit_of_val (width : int) (v : coq_ValueBase) : coq_ValueBase =
  failwith "unimplemented"

let int_of_val (width : int) (v : coq_ValueBase) : coq_ValueBase =
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
