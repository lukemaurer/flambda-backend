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

type 'a t

val define :
  generator:'a Generator.t ->
  ?shrinker:'a Shrinker.t ->
  ?printer:'a Printer.t ->
  unit ->
  'a t

val define_with_repr :
  generator:'repr Generator.t ->
  ?shrinker:'repr Shrinker.t ->
  ?printer:'repr Printer.t ->
  get_value:('repr -> 'a) ->
  unit ->
  'a t

module Repr : sig
  type 'a t

  val value : 'a t -> 'a
  val shrink : 'a t -> 'a t Seq.t
  val print : Format.formatter -> 'a t -> unit
end

val generate : 'a t -> Splittable_random.t -> 'a Repr.t

val bool : bool t

val int : int t

val option : 'a t -> 'a option t

val unit : unit t

val pair : 'a t -> 'b t -> ('a * 'b) t

val triple : 'a t -> 'b t -> 'c t -> ('a * 'b * 'c) t

val quad : 'a t -> 'b t -> 'c t -> 'd t -> ('a * 'b * 'c * 'd) t

module T : sig
  type nonrec 'a t = 'a t
end

val tuple : ('a, 'b) Tuple.Of(T).t -> ('a, 'b) Tuple.t t

val list : 'a t -> length:int -> 'a list t

val fn : ?hash_arg:('a -> int) -> 'b t -> ('a -> 'b) t

val fn_w_id : ?hash_arg:('a -> int) -> 'a t -> ('a -> 'a) t

val fn2 : ?hash_args:('a * 'b -> int) -> 'c t -> ('a -> 'b -> 'c) t

val fn3 : ?hash_args:('a * 'b * 'c -> int) -> 'd t -> ('a -> 'b -> 'c -> 'd) t
