(* Copyright 2019-present Cornell University
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not
 * use this file except in compliance with the License. You may obtain a copy
 * of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations
 * under the License.
 *)

module StringMap : Core_kernel.Map.S with type Key.t = string

type ('a,'b) alternative =
    Left of 'a
  | Right of 'b
  [@@deriving sexp,show,yojson]

val option_map: ('a -> 'b) -> 'a option -> 'b option

val option_collapse: 'a option option -> 'a option

val opt_to_exn: exn -> 'a option -> 'a

val list_option_flip: 'a option list -> 'a list option

val uncurry: ('a -> 'b -> 'c) -> 'a * 'b -> 'c

val combine_opt: 'a list -> 'b list -> ('a option * 'b option) list

val zip_map_fold: f:('a * 'b -> 'c) -> merge:('d -> 'c -> 'd) -> init:'d -> 'a list -> 'b list -> 'd option

val eq_lists: f:('a * 'b -> bool) -> 'a list -> 'b list -> bool

val find_and_drop: f:('a -> bool) -> 'a list -> 'a option * 'a list

val find_map_and_drop: f:('a -> 'b option) -> 'a list -> 'b option * 'a list

val sorted_eq: 'a list -> 'a list -> compare:('a -> 'a -> int) -> bool

val sorted_eq_strings: string list -> string list -> bool

val eq_opt : f:('a -> 'a -> bool) -> 'a Option.t -> 'a Option.t -> bool

type bigint = Bigint.t [@@deriving sexp,show,yojson]
