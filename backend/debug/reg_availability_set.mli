(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                  Mark Shinwell, Jane Street Europe                     *)
(*                                                                        *)
(*   Copyright 2016--2017 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(** Register availability sets. *)

type t =
  | Ok of Reg_with_debug_info.Set.t
  | Unreachable

(** Intersection of availabilities. *)
val inter : t -> t -> t

(** Return a subset of the given availability set which contains no registers
    that are not associated with debug info (and holding values of
    non-persistent identifiers); and where no two registers share the same
    location. *)
val canonicalise : t -> t

val equal : t -> t -> bool

(** For debugging purposes only. *)
val print :
  print_reg:(Format.formatter -> Reg.t -> unit) -> Format.formatter -> t -> unit
