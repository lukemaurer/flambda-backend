(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2016 OCamlPro SAS                                    *)
(*   Copyright 2014--2016 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

(** See the Flambda manual chapter for an explanation in prose of the
    inlining decision procedure. *)

(** Try to inline a full application of a known function, guided by various
    heuristics. *)
val for_call_site
   : env:Inline_and_simplify_aux.Env.t
  -> r:Inline_and_simplify_aux.Result.t
  -> function_decls:Simple_value_approx.function_declarations
  -> lhs_of_application:Variable.t
  -> closure_id_being_applied:Closure_id.t
  -> function_decl:Simple_value_approx.function_declaration
  -> value_set_of_closures:Simple_value_approx.value_set_of_closures
  -> args:Variable.t list
  -> args_approxs:Simple_value_approx.t list
  -> dbg:Debuginfo.t
  -> reg_close:Lambda.region_close
  -> mode:Lambda.alloc_mode
  -> simplify:Inlining_decision_intf.simplify
  -> inlined_requested:Lambda.inlined_attribute
  -> specialise_requested:Lambda.specialise_attribute
  -> probe_requested:Lambda.probe
  -> Flambda.t * Inline_and_simplify_aux.Result.t

(** When a function declaration is encountered by [for_call_site], the body
    may be subject to inlining immediately, thus changing the declaration.
    This function must return [true] for that to be able to happen. *)
val should_inline_inside_declaration : Flambda.function_declaration -> bool
