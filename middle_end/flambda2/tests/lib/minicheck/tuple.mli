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

(** A list of values of specified types. For example, [[1; true; "hello"] : (int
    -> bool -> string -> 'r, 'r) t]. ['r] should be left polymorphic (a la
    [format3] and friends). *)
type ('a, 'r) t =
  | [] : ('r, 'r) t
  | ( :: ) : 'a * ('b, 'r) t -> ('a -> 'b, 'r) t

val nil : ('r, 'r) t

val cons : 'a -> ('b, 'r) t -> ('a -> 'b, 'r) t

(** Call a function with this tuple as arguments. *)
val call : ('a, 'r) t -> f:'a -> 'r

val of_pair : 'a * 'b -> ('a -> 'b -> 'c, 'c) t

val of_triple : 'a * 'b * 'c -> ('a -> 'b -> 'c -> 'd, 'd) t

val of_quad : 'a * 'b * 'c * 'd -> ('a -> 'b -> 'c -> 'd -> 'e, 'e) t

val to_pair : ('a -> 'b -> 'c, 'c) t -> 'a * 'b

val to_triple : ('a -> 'b -> 'c -> 'd, 'd) t -> 'a * 'b * 'c

val to_quad : ('a -> 'b -> 'c -> 'd -> 'e, 'e) t -> 'a * 'b * 'c * 'd

module Of (T : sig
  type 'a t
end) : sig
  (** A list of values, each of which has type ['a T.t] for different ['a]. This
      allows us to describe, say, a tuple of lists, without constraining the
      lists to have the same element type. For example, [[Some 1; Some true;
      None] : (int -> bool -> string -> 'r, 'r) Of(Option).t]. *)
  type ('a, 'r) t =
    | [] : ('r, 'r) t
    | ( :: ) : 'a T.t * ('b, 'r) t -> ('a -> 'b, 'r) t
end

module Map (From : sig
  type 'a t
end) (Into : sig
  type 'a t
end) : sig
  type t = { f : 'a. 'a From.t -> 'a Into.t }

  val map : ('a, 'r) Of(From).t -> f:t -> ('a, 'r) Of(Into).t
end

module Of2 (T : sig
  type ('a, 'b) t
end) : sig
  type ('a, 'b, 'r) t =
    | [] : ('r, 'r, 'r) t
    | ( :: ) : ('a, 'b) T.t * ('c, 'd, 'r) t -> ('a -> 'c, 'b -> 'd, 'r) t
end
