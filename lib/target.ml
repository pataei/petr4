module I = Info
open Typed
open Prog
open Env
open Bitstring
open Core_kernel
open Util
module Info = I
let (=) = Stdlib.(=)
let (<>) = Stdlib.(<>)

type env = Eval_env.t

type 'st pre_extern =
  env -> 'st -> coq_P4Type list -> (coq_Value * coq_P4Type) list ->
  env * 'st * signal * coq_Value

type 'st apply =
  ctrl -> env -> 'st -> signal -> coq_Value -> coq_Expression option list -> 'st * signal * coq_Value

module State = struct

  type 'a t = {
    externs : (string * 'a) list;
    heap : (string * coq_Value) list;
    packet : pkt;
  }

  let empty = {
    externs = [];
    heap = [];
    packet = {emitted = Cstruct.empty; main = Cstruct.empty; in_size = 0; }
  }

  let packet_location = "__PACKET__"

  let counter = ref 0

  let fresh_loc = fun () ->
    counter := !counter + 1;
    "__fresh_loc__" ^ (string_of_int (!counter)) ^ "__fresh_loc__"

  let reset_state st = counter := 0; { st with 
    packet = {emitted = Cstruct.empty; main = Cstruct.empty; in_size = 0; };
    heap = List.filter st.heap ~f:(fun (x,_) -> String.is_prefix x ~prefix:"__fresh_loc__");
  }

  let get_packet st = st.packet

  let set_packet pkt st = { st with packet = pkt }

  let insert_extern loc v st = {
    st with externs = (loc,v) :: st.externs }
  
  let find_extern loc st =
    let x = List.Assoc.find_exn st.externs loc ~equal:String.equal in
    x

  let insert_heap loc v st = { st with heap = (loc,v) :: st.heap }

  let find_heap loc st =
    List.Assoc.find_exn st.heap loc ~equal:String.equal

  let is_initialized loc st =
    List.exists st.externs ~f:(fun (x,_) -> String.equal x loc)

end

type 'a writer = bool -> (P4string.t * 'a) list -> P4string.t -> 'a -> coq_Value

type 'a reader = bool -> (P4string.t * 'a) list -> P4string.t -> 'a

let rec width_of_typ (env : env) (t : coq_P4Type) : Bigint.t =
  match t with
  | TypBool -> Bigint.one
  | TypInt width | TypBit width -> Bigint.of_int width
  | TypArray (typ, size) -> Bigint.(width_of_typ env typ * of_int size)
  | TypList types
  | TypTuple types ->
    types
    |> List.map ~f:(width_of_typ env)
    |> List.fold ~init:Bigint.zero ~f:Bigint.(+)
  | TypRecord fields | TypHeader fields | TypStruct fields ->
    fields
    |> List.map ~f:(fun (MkFieldType (name, typ)) -> typ)
    |> List.map ~f:(width_of_typ env)
    |> List.fold ~init:Bigint.zero ~f:Bigint.(+)
  | TypEnum (_, Some t, _) -> width_of_typ env t
  | TypTypeName n -> width_of_typ env (Eval_env.find_typ n env)
  | TypNewType (name, typ) -> width_of_typ env typ
  | _ -> raise_s [%message "not a fixed-width type" ~t:(t:coq_P4Type)]

let rec init_val_of_typ (env : env) (typ : coq_P4Type) : coq_Value =
  match typ with
  | TypBool
  | TypString
  | TypInteger
  | TypInt _
  | TypBit _ 
  | TypVarBit _
  | TypArray _
  | TypTuple _
  | TypList _
  | TypRecord _
  | TypSet _
  | TypError
  | TypMatchKind
  | TypHeader _
  | TypHeaderUnion _
  | TypStruct _
  | TypEnum _
    -> ValBase (init_val_of_base_typ env typ)
  | TypTypeName name                     -> init_val_of_typ env (Eval_env.find_typ name env)
  | TypNewType (n, typ)                  -> init_val_of_typ env typ
  | TypVoid                              -> ValBase ValBaseNull
  | TypSpecializedType (t, args)         -> init_val_of_specialized t args
  | TypPackage (t_ps, w_ps, ps)          -> init_val_of_pkg t_ps w_ps ps
  | TypControl ct                        -> init_val_of_ctrl ct
  | TypParser pt                         -> init_val_of_prsr pt
  | TypExtern et                         -> init_val_of_ext et
  | TypFunction ft                       -> init_val_of_func ft
  | TypAction (c_ps, d_ps)               -> init_val_of_act c_ps d_ps
  | TypConstructor (t_ps, w_ps, ps, ret) -> init_val_of_constr t_ps w_ps ps ret
  | TypTable tt                          -> init_val_of_table tt

and init_val_of_base_typ (env : env) (typ : coq_P4Type) : coq_ValueBase =
  match typ with
  | TypBool                              -> ValBaseBool false
  | TypString                            -> ValBaseString (P4string.dummy "")
  | TypInteger                           -> ValBaseInteger Bigint.zero
  | TypInt w                             -> ValBaseInt (w, Bigint.zero)
  | TypBit w                             -> ValBaseBit (w, Bigint.zero)
  | TypVarBit w                          -> ValBaseVarbit (w, 0, Bigint.zero)
  | TypArray (t, size)                   -> init_val_of_array env t size
  | TypTuple tup                         -> init_val_of_tuple env tup
  | TypList l                            -> init_val_of_tuple env l
  | TypRecord r                          -> init_val_of_record env r
  | TypSet s                             -> ValBaseSet ValSetUniversal
  | TypError                             -> ValBaseError (P4string.dummy "NoError")
  | TypMatchKind                         -> ValBaseMatchKind (P4string.dummy "exact")
  | _ -> ValBaseNull

and init_val_of_array (env : env) (typ: coq_P4Type) (size: int) : coq_ValueBase =
  let hdrs =
    size
    |> List.init ~f:string_of_int
    |> List.map ~f:(fun _ -> init_val_of_base_typ env typ) in
  ValBaseStack (hdrs, size, 0)

and init_val_of_tuple (env : env) (types : coq_P4Type list) : coq_ValueBase =
  let vs = List.map types ~f:(fun t -> init_val_of_base_typ env t) in
  ValBaseTuple vs

and init_val_of_field (env : env) (MkFieldType (name, typ): coq_FieldType) : P4string.t * coq_ValueBase =
  name, init_val_of_base_typ env typ

and init_val_of_record (env : env) (r : coq_FieldType list) : coq_ValueBase =
  let vs = List.map ~f:(init_val_of_field env) r in
  ValBaseRecord vs

and init_val_of_header (env : env) (rt : coq_FieldType list) : coq_ValueBase =
  let vs = List.map ~f:(init_val_of_field env) rt in
  ValBaseHeader (vs, false)

and init_val_of_union (env: env) (rt : coq_FieldType list) : coq_ValueBase =
  let fs = List.map ~f:(init_val_of_field env) rt in
  ValBaseUnion fs

and init_val_of_struct (env : env) (rt : coq_FieldType list) : coq_ValueBase =
  let fs = List.map ~f:(init_val_of_field env) rt in
  ValBaseStruct fs

and init_val_of_enum (env : env) name typ members : coq_ValueBase =
  match typ with
  | None ->
    ValBaseEnumField (name, List.hd_exn members)
  | Some t ->
    let v = init_val_of_base_typ env t in
    ValBaseSenumField (name, List.hd_exn members, v)

and init_val_of_specialized t args : coq_Value =
  failwith "init vals unimplemented for specialized types"

and init_val_of_pkg _ _ _ : coq_Value =
  failwith "init vals unimplemented for package types"

and init_val_of_ctrl ct : coq_Value =
  failwith "init vals unimplemented for control types"

and init_val_of_prsr pt : coq_Value =
  failwith "init vals unimplemented for parser types"

and init_val_of_ext et : coq_Value =
  failwith "init vals unimplemented for extern types"

and init_val_of_func ft : coq_Value =
  failwith "init vals unimplemented for function types"

and init_val_of_act c_ts p_ts : coq_Value =
  failwith "init vals unimplemented for action types"

and init_val_of_constr t_ps c_ps w_ps ret : coq_Value =
  failwith "init vals unimplemented for constructor types"

and init_val_of_table tt : coq_Value =
  failwith "init vals unimplemented for table  types"

let rec width_of_val (v: coq_ValueBase) =
  let field_width (name, value) =
    width_of_val value
  in
  match v with
  | ValBaseBit (w, _)
  | ValBaseInt (w, _)
  | ValBaseVarbit (w, _, _) ->
    w
  | ValBaseNull ->
    0
  | ValBaseBool _ ->
    1
  | ValBaseStruct fields
  | ValBaseHeader (fields, _) ->
    fields
    |> List.map ~f:field_width
    |> List.fold ~init:0 ~f:(+)
  | ValBaseSenumField (_, _, v) ->
      width_of_val v
  | ValBaseInteger _ -> failwith "width of VInteger"
  | ValBaseUnion _ -> failwith "width of header union unimplemented"
  | _ -> raise_s [%message "width of type unimplemented" ~v:(v: coq_ValueBase)]

let rec value_of_lvalue (reader : 'a reader) (env : env) (st : 'a State.t)
    (lv : coq_ValueLvalue) : signal * coq_Value =
  let (MkValueLvalue (lv, _)) = lv in
  match lv with
  | ValLeftName n -> SContinue, State.find_heap (Eval_env.find_val n env) st
  | ValLeftMember (lv, n) -> value_of_lmember reader st env lv n
  | ValLeftBitAccess (lv, hi, lo) -> value_of_lbit reader st env lv hi lo
  | ValLeftArrayAccess (lv, idx) -> value_of_larray reader st env lv idx

and value_of_lmember (reader : 'a reader) (st : 'a State.t) (env : env) (lv : coq_ValueLvalue)
    (n : P4string.t) : signal * coq_Value =
  let (s,v) = value_of_lvalue reader env st lv in
  let v' = match v with
    | ValBase (ValBaseHeader (l, is_valid)) -> reader is_valid l n 
    | ValBase (ValBaseStruct l)
    | ValBase (ValBaseUnion l) -> List.Assoc.find_exn ~equal:P4string.eq l n
    | ValBase (ValBaseStack (vs, s, i)) -> value_of_stack_mem_lvalue st n vs s i
    | _ -> failwith "no lcoq_Value member" in
  match s with
  | SContinue -> (s, ValBase v')
  | SReject _ -> (s, ValBase ValBaseNull)
  | _ -> failwith "unreachable"

and value_of_lbit (reader : 'a reader) (st : 'a State.t) (env : env) (lv : coq_ValueLvalue)
    (hi : int) (lo : int) : signal * coq_Value =
  let (signal, n) = value_of_lvalue reader env st lv in
  let n' = n |> Checker.bigint_of_value in
  match s with 
  | SContinue ->
    let width = hi - lo + 1 in
    let string = bitstring_slice n' (Bigint.of_int hi) (Bigint.of_int lo) in
    s, ValBase (ValBaseBit (width, string))
  | SReject _ | SReturn _ | SExit -> s, ValBase ValBaseNull

and value_of_larray (reader : 'a reader) (st : 'a State.t) (env : env) (lv : coq_ValueLvalue)
    (idx : int) : signal * coq_Value =
  let (s,v) = value_of_lvalue reader env st lv in
  match s with
  | SContinue ->
    begin match v with
      | ValBase (ValBaseStack (vs, s, i)) ->
        begin
          try (SContinue, ValBase (List.nth_exn vs (idx % s)))
          with Invalid_argument _ ->
            (SReject (P4string.dummy "StackOutOfBounds"),
             ValBase ValBaseNull)
        end
      | _ -> failwith "array access is not a header stack" end
  | SReject _ -> (s, ValBase ValBaseNull)
  | _ -> failwith "unreachable"

and value_of_stack_mem_lvalue (st : 'a State.t) (name : P4string.t) (ls : coq_ValueBase list)
(size : int) (next : int) : coq_ValueBase =
  match name.str with
  | "next" -> List.nth_exn ls (next % size)
  | _ -> failwith "not an lcoq_Value"

let rec assign_lvalue (reader : 'a reader) (writer : 'a writer) (st : 'a State.t) 
    (env : env) (lhs : coq_ValueLvalue) (rhs : coq_ValueBase) : 'a State.t * signal =
  match lhs with
  | LName {name} ->
    let l = EvalEnv.find_val name env in
    State.insert_heap l rhs st, SContinue
  | LMember{expr=lv;name=mname;} ->
    let signal1, record = coq_Value_of_lcoq_Value reader env st lv in
    let rhs', signal2 = update_member writer record mname rhs in
    let inc_next = String.equal mname "next" in
    let rhs' = match rhs' with
      | VStack{headers; size; next} -> Bigint.(VStack {headers; size; next = next + (if inc_next then one else zero)})
      | _ -> rhs' in
    begin match signal1, signal2 with
      | SContinue, SContinue ->
        assign_lcoq_Value reader writer st env lv rhs'
      | SContinue, _ -> st, signal2
      | _, _ -> st, signal1
    end
  | LBitAccess{expr=lv;msb;lsb;} ->
    let signal, bits = coq_Value_of_lcoq_Value reader env st lv in
    begin match signal with
      | SContinue -> 
        assign_lcoq_Value reader writer st env lv (update_slice bits msb lsb rhs)
      | _ -> st, signal
    end
  | LArrayAccess{expr=lv;idx;} ->
    let signal1, arr = coq_Value_of_lcoq_Value reader env st lv in
    let rhs', signal2 = update_idx arr idx rhs in
    begin match signal1, signal2 with
      | SContinue, SContinue -> 
        assign_lcoq_Value reader writer st env lv rhs'
      | SContinue, _ -> st, signal2
      | _, _ -> st, signal1  
    end

and update_member (writer : 'a writer) (value : coq_Value) (fname : P4string.t)
    (fvalue : coq_ValueBase) : coq_Value * signal =
  match value with
  | ValBase (ValBaseStruct fields) ->
    update_field fields fname fvalue, SContinue
  | ValBase (ValBaseHeader (fields, is_valid)) ->
    writer is_valid fields fname fvalue, SContinue
  | ValBase (ValBaseUnion fields) ->
    update_union_member fields fname fvalue
  | ValBase (ValBaseStack (hdrs, s, i)) ->
    let idx = 
      match fname.str with
      | "next" -> i
      | "last" -> i - 1
      | _ -> failwith "BUG: VStack has no such member"
    in
    update_idx value idx fvalue
  | _ -> failwith "member access undefined"

and update_union_member (fields : (P4string.t * coq_ValueBase) list)
    (member_name : P4string.t) (new_value : coq_ValueBase) : coq_ValueBase * signal =
  let new_fields, new_value_valid = assert_header new_value in
  let set_validity value validity =
    let value_fields, _ = Poulet4.Unpack.unpack_header value in
    ValBaseHeader (value_fields, validity)
  in
  let update_field (name, value) =
    if new_coq_Value_valid
    then if name = member_name
         then name, new_coq_Value
         else name, set_validity coq_Value false
    else name, set_validity coq_Value false
  in
  ValBaseUnion {fields = List.map ~f:update_field fields}, SContinue

and update_field (fields : (string * coq_Value) list) (field_name : string)
    (field_value : coq_Value) : coq_Value =
  let update (n, v) =
    if String.equal n field_name
    then n, field_coq_Value
    else n, v in
  ValBaseStruct {fields = List.map fields ~f:update}

and update_nth (l : coq_Value list) (n : Bigint.t)
    (x : coq_Value) : coq_Value list =
  let n = Bigint.to_int_exn n in
  let xs, ys = List.split_n l n in
  match ys with
  | y :: ys -> xs @ x :: ys
  | [] -> failwith "update_nth: out of bounds"

and update_idx (arr : coq_Value) (idx : Bigint.t)
    (value : coq_Value) : coq_Value * signal =
  match arr with
  | VStack{headers; size; next} ->
     if Bigint.(idx < zero || idx >= size)
     then VNull, SReject "StackOutOfBounds"
     else VStack {headers = update_nth headers idx coq_Value; next; size}, SContinue
  | _ -> failwith "BUG: update_idx: expected a stack"

and update_slice bits_val msb lsb rhs_val =
  let open Bigint in
  let width =
    match bits_val with
    | VBit { w; _ } -> w
    | _ -> failwith "BUG:expected bit<> type"
  in
  let bits = Checker.bigint_of_value bits_val in
  let rhs_shifted = bigint_of_val rhs_val lsl to_int_exn lsb in
  let mask = lnot ((power_of_two (msb + one) - one)
                   lxor (power_of_two lsb - one))
  in
  let new_bits = (bits land mask) lxor rhs_shifted in
  VBit { w = width; v = new_bits }

module type Target = sig

  type obj

  type state = obj State.t

  type extern = state pre_extern

  val write_header_field : obj writer

  val read_header_field : obj reader

  val eval_extern : 
    string -> env -> state -> coq_P4Type list -> (coq_Value * coq_P4Type) list ->
    env * state * signal * coq_Value

  val initialize_metadata : Bigint.t -> state -> state

  val check_pipeline : env -> unit

  val eval_pipeline : ctrl -> env -> state -> pkt ->
  state apply -> state * env * pkt option

  val get_outport : state -> env -> Bigint.t

end
