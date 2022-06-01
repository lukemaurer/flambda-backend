(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2015--2020 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-30-40-41-42"]

module Make (_ : sig
  val print : Format.formatter -> int -> unit
end) : sig
  module Set : sig
    include Container_types.Set with type elt = int

    val valid : t -> bool
  end

  module Map : sig
    include Container_types.Map with type key = int with module Set = Set

    val valid : _ t -> bool
  end
end
