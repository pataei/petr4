open Poulet4.Typed
open Typed
open Poulet4.Syntax
open Prog
open Target
open Bitstring
module I = Info
open Core_kernel
module Info = I
let (=) = Stdlib.(=)
let (<>) = Stdlib.(<>)

module Corize (T : Target) : Target = struct

  type obj = T.obj

  type state = T.state

  type extern = state pre_extern

  let value_of_field (init_fs : (P4string.t * coq_ValueBase) list)
                     (f, t) : P4string.t * coq_ValueBase =
    f,
    List.Assoc.find_exn init_fs f ~equal:P4string.eq

  let nbytes_of_hdr (fs : (P4string.t * coq_ValueBase) list) : int =
    fs
    |> List.map ~f:snd
    |> List.map ~f:width_of_val
    |> List.fold ~init:0 ~f:(+)
    |> fun x -> x / 8

  let bytes_of_packet (pkt : buf) (nbytes : Bigint.t) : buf * Bigint.t * signal =
    let (c1,c2), signal =
      try Cstruct.split pkt (Bigint.to_int_exn nbytes), SContinue
      with Invalid_argument  _ -> (pkt, Cstruct.empty), SReject (P4string.dummy "PacketTooShort")
    in
    let s = Cstruct.to_string c1 in
    let chars = String.to_list s in
    let bytes = List.map chars ~f:Char.to_int in
    let bytes' = List.map bytes ~f:Bigint.of_int in
    let eight = Bigint.((one + one) * (one + one) * (one + one)) in
    let f a n = Bigint.(a * power_of_two eight + n) in
    let n = List.fold_left bytes' ~init:Bigint.zero ~f:f in
    (c2,n,signal)

  let rec extract_hdr_field (nvarbits : int)
      (n, s : (Bigint.t * Bigint.t) * signal)
      (v : coq_ValueBase) : ((Bigint.t * Bigint.t) * signal) * coq_ValueBase =
    match s with
    | SContinue ->
      begin match v with
        | ValBaseBit (w, _) -> extract_bit n w
        | ValBaseInt (w, _) -> extract_int n w
        | ValBaseVarbit (max, _, _) -> extract_varbit nvarbits n max
        | ValBaseBool b -> extract_bool n
        | ValBaseStruct fields ->
           let field_names = List.map ~f:fst fields in
           let (n, s), field_vals = extract_struct nvarbits (n, s) fields in
           let fields = List.zip_exn field_names field_vals in
           (n, s), ValBaseStruct fields
        | ValBaseSenumField (typ_name, enum_name, v) ->
          extract_senum typ_name enum_name v nvarbits (n, s)
        | _ -> failwith "invalid header field type"
      end
    | SReject _ -> ((n,s),ValBaseNull)
    | _ -> failwith "unreachable"

  and extract_bit (n : Bigint.t * Bigint.t) (w' : int)
    : ((Bigint.t * Bigint.t) * signal) * coq_ValueBase =
    let (nw,nv) = n in
    let w = Bigint.of_int w' in
    let x = bitstring_slice nv Bigint.(nw-one) Bigint.(nw-w) in
    let y = bitstring_slice nv Bigint.(nw-w-one) Bigint.zero in
    Bigint.(((nw-w, y), SContinue)), ValBaseBit (w', x)

  and extract_bool (buf : Bigint.t * Bigint.t) : ((Bigint.t * Bigint.t) * signal) * coq_ValueBase =
    let open Bigint in
    let (bufsize, buf) = buf in
    let x = bitstring_slice buf (bufsize-one) (bufsize-one) in
    let y = bitstring_slice buf (bufsize-of_int 2) zero in
    ((bufsize-one, y), SContinue), ValBaseBool (x <> zero)

  and extract_int (n : Bigint.t * Bigint.t)
      (w' : int) : ((Bigint.t * Bigint.t) * signal) * coq_ValueBase =
    let (nw,nv) = n in
    let w = Bigint.of_int w' in
    let x = bitstring_slice nv Bigint.(nw-one) Bigint.(nw-w) in
    let y = bitstring_slice nv Bigint.(nw-w-one) Bigint.zero in
    Bigint.(((nw-w, y), SContinue)), ValBaseInt (w', to_twos_complement x w)

  and extract_varbit (nbits' : int) (nw,nv : Bigint.t * Bigint.t)
      (w' : int) : ((Bigint.t * Bigint.t) * signal) * coq_ValueBase =
    let nbits = Bigint.of_int nbits' in
    if nbits' > w'
    then (((nw,nv),SReject (P4string.dummy "HeaderTooShort")),ValBaseNull)
    else if Bigint.(nbits > nw)
    then (((nw,nv), SReject (P4string.dummy "ParserInvalidArgument")), ValBaseNull)
    else
      let x = bitstring_slice nv Bigint.(nw-one) Bigint.(nw-nbits) in
      let y = bitstring_slice nv Bigint.(nw-nbits-one) Bigint.zero in
      Bigint.((nw-nbits, y), SContinue), ValBaseVarbit (w', nbits', x)

  and extract_struct
      (nvarbits : int)
      (n, s : (Bigint.t * Bigint.t) * signal)
      (fields : (P4string.t * coq_ValueBase) list)
    : ((Bigint.t * Bigint.t) * signal) * coq_ValueBase list =
    let (n, s), vs = List.fold_map (List.map ~f:snd fields)
      ~init:(n, s)
      ~f:(extract_hdr_field nvarbits) in
    (n,s), vs

  and extract_senum (typ_name : P4string.t) (enum_name : P4string.t) (v : coq_ValueBase)
      (nvarbits : int) (n, s) : ((Bigint.t * Bigint.t) * signal) * coq_ValueBase =
    let (x, v) = extract_hdr_field nvarbits (n, s) v in
    x, ValBaseSenumField (typ_name, enum_name, v)

  let rec reset_fields (env : env) (fs : (P4string.t * coq_ValueBase) list)
      (t : coq_P4Type) : (P4string.t * coq_ValueBase) list =
    match t with
    | TypStruct rt | TypHeader rt | TypHeaderUnion rt -> List.map rt ~f:(value_of_field fs)
    | TypTypeName n  -> reset_fields env fs (Eval_env.find_typ n env)
    | TypNewType (_, typ) -> reset_fields env fs typ
    | _ -> failwith "not resettable"

  let eval_extract' (env : env) (st : state)
      (t : coq_P4Type) (pkt : coq_Value) (_ : coq_Value) (w : int)
      (is_fixed : bool) : env * state * signal * coq_Value =
    let obj = State.get_packet st in
    let pkt = obj.main in
    let init_v = init_val_of_typ env t in
    let init_fs = match init_v with
      | ValBase (ValBaseHeader (fields, is_valid)) -> fields
      | _ -> failwith "extract expects header" in
    let nbytes = Bigint.of_int (nbytes_of_hdr init_fs + w / 8) in
    let (pkt', extraction, s) = bytes_of_packet pkt nbytes in
    let st' = State.set_packet {obj with main = pkt'} st in
    match s with
    | SReject _ | SExit | SReturn _ -> env, st, s, ValBase ValBaseNull
    | SContinue ->
      let (ns, vs) = List.unzip init_fs in
      try
        let (st'', _,s), vs' =
          List.fold_map vs
            ~init:(st', Bigint.(nbytes * of_int 8, extraction), SContinue)
            ~f:(fun (st, n, s) v ->
                let ((n,s), v) = extract_hdr_field w (n,s) v in
                (st, n,s), v) in
        begin match s with
        | SReject _ | SExit | SReturn _ -> env, st, s, ValBase ValBaseNull
        | SContinue ->
          let fs' = List.zip_exn ns vs' in
          let h: coq_Value = ValBase (ValBaseHeader (fs', true)) in
          let loc = State.fresh_loc () in
          let st''' = State.insert_heap loc h st'' in
          let env' =
            Eval_env.insert_val_bare
              (if is_fixed
               then P4string.dummy "hdr"
               else P4string.dummy "variableSizeHeader")
              loc env
          in
          env', st''', SContinue, ValBase ValBaseNull
        end
      with Invalid_argument _ ->
        env, st', SReject (P4string.dummy "PacketTooShort"), ValBase ValBaseNull

  let eval_advance : extern = fun env st _ args ->
    let (pkt_loc, v) = match args with
      | [ValObj (ValObjRuntime (loc, _)), _;
         ValBase (ValBaseBit (_, v)), _]
      | [ValObj (ValObjRuntime (loc, _)), _;
         ValBase (ValBaseInteger v), _] ->
        loc, v
      | _ -> failwith "unexpected args for advance" in
    let obj = State.get_packet st in
    let pkt = obj.main in
    try
      let x = (Bigint.to_int_exn v) / 8 in
      let pkt' = Cstruct.split pkt x |> snd in
      let st' = State.set_packet {obj with main = pkt'} st in
      env, st', SContinue, ValBase ValBaseNull
    with Invalid_argument _ ->
      env, st, SReject (P4string.dummy "PacketTooShort"), ValBase ValBaseNull

  let eval_extract : extern = fun env st targs args ->
    match args with
    | [(pkt, _);(v1, t)] ->
      begin match v1 with
        | ValBase ValBaseNull ->
          let targ = List.nth targs 0 |> Option.value_exn in
          eval_advance env st targs [(pkt, t); (ValBase (ValBaseBit (0, Bigint.of_int (width_of_typ env targ))), t)]
        | _ -> eval_extract' env st t pkt v1 0 true
      end
    | [(pkt,_); (v1,t); (ValBase v2, _)] ->
      let w = v2 |> Checker.bigint_of_value_base_exn |> Bigint.to_int_exn in
      eval_extract' env st t pkt v1 w false
    | _ -> failwith "wrong number of args for extract"

  let rec val_of_bigint (env : env) (t : coq_P4Type) (n : Bigint.t) : coq_ValueBase =
    let w = width_of_typ env t in
    let f (w,n) t =
      let w' = Bigint.of_int w in
      let rmax = width_of_typ env t in
      let rmax' = Bigint.of_int rmax in
      let v = val_of_bigint env t (bitstring_slice n Bigint.(w' - one) Bigint.(w'-rmax')) in
      (w - rmax, Bigint.(bitstring_slice n (w' - rmax') zero)), v in
    let fieldvals_of_recordtype (rt : coq_FieldType list) : (P4string.t * coq_ValueBase) list =
      let names = List.map ~f:fst rt in
      let types = List.map ~f:snd rt in
      let vs = List.fold_map types ~init:(w,n) ~f:f in
      List.zip_exn names (snd vs) in
    match t with
    | TypBool ->
      if Bigint.(n = zero)
      then ValBaseBool false
      else ValBaseBool true
    | TypInt width ->
      ValBaseInt (width, to_twos_complement n (Bigint.of_int width))
    | TypBit width ->
      ValBaseBit (width, to_twos_complement n (Bigint.of_int width))
    | TypArray (typ, size) ->
      let init = List.init size ~f:(fun x -> t) in
      let (_, hdrs) =
        List.fold_map init
        ~init:(w,n)
        ~f:f in
      ValBaseStack (hdrs, size, 0)
    | TypList types | TypTuple types ->
      let _, vs = List.fold_map types ~init:(w,n) ~f:f in
      ValBaseTuple vs
    | TypRecord rt -> ValBaseRecord (fieldvals_of_recordtype rt)
    | TypStruct rt -> ValBaseStruct (fieldvals_of_recordtype rt)
    | TypHeader rt -> ValBaseHeader (fieldvals_of_recordtype rt, true)
    | TypEnum (_, Some t, _) -> val_of_bigint env t n
    | TypTypeName name -> val_of_bigint env (Eval_env.find_typ name env) n
    | TypNewType (name, typ) -> val_of_bigint env typ n
    | _ -> raise_s [%message "not a fixed-width type"
                       ~t:Pretty.(fmt_string Typed.format_coq_P4Type t)]

  let eval_lookahead : extern = fun env st targs args ->
    let t = match targs with
      | [t] -> t
      | _ -> failwith "unexpected type args for lookahead" in
    let w = width_of_typ env t in
    let obj = State.get_packet st in
    let pkt = obj.main in
    try
      let (pkt_hd, _) = Cstruct.split ~start:0 pkt (w/8) in
      let (_, n, s) = bytes_of_packet pkt_hd (Bigint.of_int (w/8)) in
      begin match s with 
      | SContinue -> 
        let v = val_of_bigint env t n in
        env, st, SContinue, ValBase v
      | _ -> env, st, s, ValBase ValBaseNull end
    with Invalid_argument _ -> env, st, SReject (P4string.dummy "PacketTooShort"), ValBase ValBaseNull

  let eval_length : extern = fun env st _ args ->
    match args with
    | [(ValObj (ValObjRuntime (loc, _)), _)] ->
      let obj = State.get_packet st in
      let len = obj.in_size in
      env, st, SContinue, ValBase (ValBaseBit (32, Bigint.of_int len))
    | _ -> failwith "unexpected args for length"

  let packet_of_bytes (n : Bigint.t) (w : Bigint.t) : buf =
    let eight = Bigint.((one + one) * (one + one) * (one + one)) in
    let seven = Bigint.(eight - one) in
    if Bigint.(w % eight <> zero) then failwith "packet_of_bytes: len must be byte-aligned";
    let rec h acc n w =
      if Bigint.(w = zero) then acc else
        let lsbyte = bitstring_slice n seven Bigint.zero in
        let n' = bitstring_slice n Bigint.(w-one) eight in
        h (lsbyte :: acc) n' Bigint.(w-eight) in
    let bytes = h [] n w in
    let ints = List.map bytes ~f:Bigint.to_int_exn in
    let chars = List.map ints ~f:Char.of_int_exn in
    let s = String.of_char_list chars in
    Cstruct.of_string s

  let rec field_types_of_typ (env : env) (t : coq_P4Type) : coq_P4Type list =
    match t with
    | TypHeader rt | TypRecord rt | TypStruct rt | TypHeaderUnion rt ->
      List.map rt ~f:snd
    | TypTypeName n -> field_types_of_typ env (Eval_env.find_typ n env)
    | TypNewType (_, t) -> field_types_of_typ env t
    | _ -> failwith "type does not have fields"

  let rec packet_of_value (env : env) (t : coq_P4Type) (v : coq_ValueBase) : buf =
    match v with
    | ValBaseBit (w, v) -> packet_of_bit w v
    | ValBaseInt (w, v) -> packet_of_int w v
    | ValBaseVarbit (max, w, v) -> packet_of_bit w v
    | ValBaseStruct fields -> packet_of_struct env t fields
    | ValBaseHeader (fields, is_valid) -> packet_of_hdr env t fields is_valid
    | ValBaseUnion fields -> packet_of_struct env t fields
    | ValBaseStack (headers, _, _) -> packet_of_stack env t headers
    | ValBaseInteger _ -> failwith "it was integer"
    | _ -> failwith "emit undefined on type"

  and packet_of_bit (w : int) (v : Bigint.t) : buf =
    packet_of_bytes v (Bigint.of_int w)

  and packet_of_int (w : int) (v : Bigint.t) : buf =
    packet_of_bytes (of_twos_complement v (Bigint.of_int w)) (Bigint.of_int w)

  and packet_of_struct (env : env) (t : coq_P4Type)
      (fields : (P4string.t * coq_ValueBase) list) : buf =
    let fs = reset_fields env fields t in
    let fs' = List.map ~f:snd fs in
    let fts = field_types_of_typ env t in
    let pkts = List.map2_exn ~f:(fun v t -> packet_of_value env t v) fs' fts in
    List.fold ~init:Cstruct.empty ~f:Cstruct.append pkts

  and packet_of_hdr (env : env) (t : coq_P4Type)
      (fields : (P4string.t * coq_ValueBase) list) (is_valid : bool) : buf =
    let rec underlying_typ_of_enum env t =
      match t with
      | TypEnum (_, typ, _) -> Option.value_exn typ
      | TypTypeName n -> Eval_env.find_typ n env |> underlying_typ_of_enum env
      | TypNewType (_, typ) -> typ |> underlying_typ_of_enum env
      | _ -> failwith "no such underlying type" in
    let f = fun (accw, accv) (w,v) ->
      accw + w, Bigint.(shift_bitstring_left accv (of_int w) + v) in
    let rec wv_of_val (v, t) = match (v: coq_ValueBase) with
      | ValBaseBit (w, v) -> w, v
      | ValBaseInt (w, v) -> w, of_twos_complement v (Bigint.of_int w)
      | ValBaseVarbit (max, w, v)-> w, v
      | ValBaseBool true -> 1, Bigint.one
      | ValBaseBool false -> 1, Bigint.zero
      | ValBaseSenumField (_, _, v) -> wv_of_val (v, underlying_typ_of_enum env t)
      | ValBaseStruct fields ->
        let fs = reset_fields env fields t in
        let fs' = List.map ~f:snd fs in
        let fts = field_types_of_typ env t in
        List.zip_exn fs' fts |> List.map ~f:wv_of_val
        |> List.fold ~init:(0, Bigint.zero) ~f:f
      | _ -> failwith "invalid type for header field" in
    if not is_valid then Cstruct.empty else
    let fts = field_types_of_typ env t in
    let w, v = reset_fields env fields t
      |> List.map ~f:snd
      |> (fun a -> List.zip_exn a fts)
      |> List.map ~f:wv_of_val
      |> List.fold ~init:(0, Bigint.zero) ~f:f in
    packet_of_bit w v

  and packet_of_stack (env : env) (t : coq_P4Type) (hdrs : coq_ValueBase list) : buf =
    let t' = match t with
      | TypArray (t, _) -> t
      | _ -> failwith "expected array type" in
    let pkts = List.map ~f:(packet_of_value env t') hdrs in
    List.fold ~init:Cstruct.empty ~f:Cstruct.append pkts

  let eval_emit : extern = fun env st _ args ->
    let (pkt_loc, v, t) = match args with
      | [(ValObj (ValObjRuntime (loc, _)), _); (ValBase hdr, t)] -> loc, hdr, t
      | _ -> failwith "unexpected args for emit" in
    let obj = State.get_packet st in
    let (pkt_hd, pkt_tl) = obj.emitted, obj.main in
    let pkt_add = packet_of_value env t v in
    let emitted = Cstruct.append pkt_hd pkt_add in
    let st' = State.set_packet {obj with emitted = emitted} st in
    env, st', SContinue, ValBase ValBaseNull

  let eval_verify : extern = fun env st _ args ->
    let b, err = match args with
      | [(ValBase (ValBaseBool b), _); (ValBase (ValBaseError err),_)] -> b, err
      | _ -> failwith "unexpected args for verify" in
    if b then env, st, SContinue, ValBase ValBaseNull
    else env, st, SReject err, ValBase ValBaseNull

  let core_externs : (string * extern) list =
    [ ("extract", eval_extract);
      ("lookahead", eval_lookahead);
      ("advance", eval_advance);
      ("length", eval_length);
      ("emit", eval_emit);
      ("verify", eval_verify)]

  let write_header_field : Target.writer = T.write_header_field

  let read_header_field : Target.reader = T.read_header_field

  let eval_extern name =
    match name with
    | "extract" -> eval_extract
    | "lookahead" -> eval_lookahead
    | "advance" -> eval_advance
    | "length" -> eval_length
    | "emit" -> eval_emit
    | "verify" -> eval_verify
    | _ -> T.eval_extern name

  let initialize_metadata = T.initialize_metadata

  let check_pipeline = T.check_pipeline

  let eval_pipeline ctrl env st pkt app =
    let st = State.set_packet pkt st in
    T.eval_pipeline ctrl env st pkt app

  let get_outport = T.get_outport
end
