open Typed
open Prog
    
val bool_list_to_bigint: bool list -> Bigint.t
val bigint_to_bool_list: Bigint.t -> bool list
val bigint_of_val: coq_Value -> Bigint.t
val interp_binary_op: coq_OpBin -> coq_ValueBase -> coq_ValueBase -> coq_ValueBase option
val interp_unary_op: coq_OpUni -> coq_ValueBase -> coq_ValueBase option
val interp_cast: type_lookup:(P4name.t -> coq_P4Type) -> coq_P4Type -> coq_ValueBase -> coq_ValueBase
