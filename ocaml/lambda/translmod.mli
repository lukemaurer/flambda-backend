(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*                                                                        *)
(*   Copyright 1996 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* Translation from typed abstract syntax to lambda terms,
   for the module language *)

open Typedtree
open Lambda

type compilation_unit_style =
  | Plain_block (* Flambda *)
  | Set_global_to_block (* Bytecode *)
  | Set_individual_fields (* Closure *)

val transl_implementation:
      Compilation_unit.t -> structure * module_coercion * module_coercion option
        -> style:compilation_unit_style -> Lambda.program
val transl_store_phrases: Compilation_unit.t -> structure -> int * lambda

val transl_toplevel_definition: structure -> lambda

val transl_package:
      Compilation_unit.t option list -> Compilation_unit.t -> module_coercion
        -> style:compilation_unit_style -> int * lambda

type runtime_arg =
  | (* An argument passed on the command line to fill a parameter of the module
       being instantiated *)
    Argument_block of {
      (* The compilation unit being passed as an argument *)
      ra_unit : Compilation_unit.t;
      (* The offset of its argument block, as advertised in its .cmo/.cmx *)
      ra_field : int;
    }
  | (* A parameterised dependency, which must therefore have already been
       instantiated so that the resulting instance can be passed along here *)
    Dependency of Compilation_unit.t
  | Unit

val transl_instance:
      Compilation_unit.t -> runtime_args:runtime_arg list
        -> main_module_block_size:int -> arg_block_field:int option
        -> style:compilation_unit_style -> Lambda.program

val toplevel_name: Ident.t -> string
val nat_toplevel_name: Ident.t -> Compilation_unit.t * int

val primitive_declarations: Primitive.description list ref

type unsafe_component =
  | Unsafe_module_binding
  | Unsafe_functor
  | Unsafe_non_function
  | Unsafe_typext
  | Unsafe_non_value_arg

type unsafe_info =
  | Unsafe of { reason:unsafe_component; loc:Location.t; subid:Ident.t }
  | Unnamed

type error =
  Circular_dependency of (Ident.t * unsafe_info) list
| Conflicting_inline_attributes
| Non_value_jkind of Types.type_expr * Jkind.sort
| Instantiating_packed of Compilation_unit.t

exception Error of Location.t * error

val report_error: Location.t -> error -> Location.error

val reset: unit -> unit
