(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*    Pierre Chambart and Guillaume Bury, OCamlPro                        *)
(*                                                                        *)
(*   Copyright 2021--2021 OCamlPro SAS                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(** An internal type for the data_flow graph *)
type t =
  { dummy_toplevel_cont : Continuation.t;
    callers : Continuation.Set.t Continuation.Map.t;
    parents : Continuation.t Continuation.Map.t;
    children : Continuation.Set.t Continuation.Map.t
  }

(** Create the data flow graph *)
val create : dummy_toplevel_cont:Continuation.t -> Flow_types.Acc.t -> t

val fixpoint :
  t ->
  init:Variable.Set.t Continuation.Map.t ->
  f:
    (caller:Continuation.t ->
    caller_set:Variable.Set.t ->
    callee:Continuation.t ->
    callee_set:Variable.Set.t ->
    Variable.Set.t) ->
  Variable.Set.t Continuation.Map.t

(** Run the required names analysis *)
val compute_continuation_extra_args_for_aliases :
  speculative:bool ->
  required_names:Name.Set.t ->
  source_info:Flow_types.Acc.t ->
  unboxed_blocks:Variable.Set.t ->
  Variable.t Variable.Map.t ->
  t ->
  Flow_types.Continuation_param_aliases.t Continuation.Map.t

module Dot : sig
  (** Printing function *)
  val print :
    ctx:int ->
    df:Flow_types.Acc.t ->
    print_name:string ->
    Format.formatter ->
    return_continuation:Continuation.t ->
    exn_continuation:Continuation.t ->
    ?pp_node:(Format.formatter -> Continuation.t -> unit) ->
    continuation_parameters:
      Flow_types.Continuation_param_aliases.t Continuation.Map.t ->
    t ->
    unit
end
