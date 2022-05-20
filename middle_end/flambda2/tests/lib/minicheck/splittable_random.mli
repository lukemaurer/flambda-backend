(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2015--2022 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-30-40-41-42"]

type t

(** Create a new [t] that will return identical results to any other [t] created
    with that integer. *)
val of_int : int -> t

(** [perturb t salt] adds the entropy of [salt] to [t]. *)
val perturb : t -> int -> unit

(** Create a copy of [t] that will return the same random samples as [t]. *)
val copy : t -> t

(** [split t] produces a new state that behaves deterministically (i.e. only
    depending on the state of [t]), but pseudo-independently from [t]. This
    operation mutates [t], i.e., [t] will return different values than if this
    hadn't been called. *)
val split : t -> t

val int : t -> int
