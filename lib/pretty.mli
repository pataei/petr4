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

val fmt_string : (Format.formatter -> 'a -> unit) -> 'a -> string

val format_list : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a list -> unit
val format_list_nl : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a list -> unit
val format_list_sep : (Format.formatter -> 'a -> unit) -> string -> Format.formatter -> 'a list -> unit

module Types : sig

  val name_format_t : Format.formatter -> Types.P4name.t -> unit

  module P4Int : sig
    val format_t : Format.formatter -> Types.P4int.t -> unit
  end

  module P4String : sig
    val format_t : Format.formatter -> Types.P4string.t -> unit
  end

  module Expression : sig
    val format_t : Format.formatter -> Types.Expression.t -> unit
  end

  module MethodPrototype : sig
    val format_t : Format.formatter -> Types.MethodPrototype.t -> unit
  end

  module Statement : sig
    val format_t : Format.formatter -> Types.Statement.t -> unit
  end

  module Block : sig
    val format_t : Format.formatter -> Types.Block.t -> unit
  end

  module Argument : sig
    val format_pre_t : Format.formatter -> Types.Argument.pre_t -> unit
    val format_t : Format.formatter -> Types.Argument.t -> unit
  end

  module Type : sig
    val format_t : Format.formatter -> Types.Type.t -> unit
  end

  module Annotation : sig
    val format_t : Format.formatter -> Types.Annotation.t -> unit
  end

  module Direction : sig
    val format_t : Format.formatter -> Types.Direction.t -> unit
  end

  module Parameter : sig
    val format_t : Format.formatter -> Types.Parameter.t -> unit
  end

  module Match: sig
    val format_t : Format.formatter -> Types.Match.t -> unit
  end

  module Parser : sig
    val format_state : Format.formatter -> Types.Parser.state -> unit
    val format_states : Format.formatter -> Types.Parser.state list -> unit
  end

  module Table : sig
    val format_property : Format.formatter -> Types.Table.property -> unit
  end

  module Declaration : sig
    val format_field : Format.formatter -> Types.Declaration.field -> unit
    val format_t : Format.formatter -> Types.Declaration.t -> unit
  end

  val format_program : Format.formatter -> Types.program -> unit

end

module Typed : sig
  val format_coq_P4Type : Format.formatter -> Typed.coq_P4Type -> unit
  val format_coq_P4Parameter : Format.formatter -> Typed.coq_P4Parameter -> unit
end
  
