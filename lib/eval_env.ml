open Types
open Typed
open Poulet4.Syntax
module I = Info
open Core_kernel
module Info = I

type t = Prog.coq_Env_EvalEnv

let mk vals types ns =
  MkEnv_EvalEnv (vals, types, ns)

let empty_eval_env =
  MkEnv_EvalEnv
    ([[]],
     [[]],
     {tags = Info.dummy, []; str = ""})

let vals  ((MkEnv_EvalEnv (vals, types, ns)): t) = vals
let types ((MkEnv_EvalEnv (vals, types, ns)): t) = types
let ns    ((MkEnv_EvalEnv (vals, types, ns)): t) = ns

let get_val_firstlevel (env: t) =
  match vals env with
  | scope :: rest -> scope
  | [] -> Env.no_scopes ()

let get_toplevel (env : t) : t =
  let get_last l =
    match List.rev l with
    | [] -> raise @@ Env.BadEnvironment "no toplevel"
    | h :: _ -> [h] in
  mk (get_last (vals env))
    (get_last (types env))
    {tags = Info.dummy, []; str = ""}

let get_val_firstlevel env =
  env |> vals |> List.hd_exn

let get_namespace env =
  env |> ns

let set_namespace name env =
  mk (vals env) (types env) name

let insert_val name binding e =
  let v' = Env.insert name binding (vals e) in
  mk v' (types e) (ns e)

let insert_val_bare name binding e =
  let v' = Env.insert (BareName name) binding (vals e) in
  mk v' (types e) (ns e)

let insert_typ name binding e =
  mk (vals e) (Env.insert name binding (types e)) (ns e)

let insert_typ_bare name =
  insert_typ (BareName name)

let insert_vals (bindings: (P4name.t * P4string.t) list) (e: t) : t =
  List.fold_left bindings ~init:e ~f:(fun a (b,c) -> insert_val b c a)

let fix_bindings (bindings: (P4string.t * 'a) list) : (P4name.t * 'a) list =
  let mk_pair ((name, v): P4string.t * 'a) : P4name.t * 'a =
    BareName name, v
  in
  List.map ~f:mk_pair bindings

let insert_vals_bare bindings =
  insert_vals (fix_bindings bindings)

let insert_typs bindings e =
  List.fold_left bindings ~init:e ~f:(fun a (b,c) -> insert_typ b c a)

let insert_typs_bare bindings =
  insert_typs (fix_bindings bindings)

let find_val name e =
  Env.find name (vals e)

let find_val_opt name e =
  Env.find_opt name (vals e)

let find_typ name e =
  Env.find name (types e)

let push_scope (e : t) : t =
  mk (e |> vals |> Env.push)
    (e |> types |> Env.push)
    (e |> ns)

let pop_scope (e:t) : t =
  mk (e |> vals |> Env.pop)
    (e |> types |> Env.pop)
    (e |> ns)
