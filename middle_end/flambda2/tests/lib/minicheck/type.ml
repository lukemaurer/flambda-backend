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

module Impl = struct
  type 'a t = {
    generator : 'a Generator.t;
    shrinker : 'a Shrinker.t;
    printer : 'a Printer.t;
  }
end

type ('a, 'repr) t_with_repr = { impl : 'repr Impl.t ; get_value : 'repr -> 'a }

type 'a t = T : ('a, 'repr) t_with_repr -> 'a t [@@unboxed]

let define_with_repr ~generator ?(shrinker = Shrinker.atomic) ?(printer = Printer.opaque)
    ~get_value () =
  T { impl = { generator; shrinker; printer; }; get_value }

let define ~generator ?shrinker ?printer () =
  let get_value a = a in
  define_with_repr ~generator ?shrinker ?printer ~get_value ()

module Repr = struct
  type 'a t = T : {
      repr : 'repr;
      value : 'a;
      type_ : ('a, 'repr) t_with_repr;
    } -> 'a t

  let value (T t) = t.value
  let shrink (T t) = t.type_.impl.shrinker t.repr |> Seq.map (fun repr -> let value = t.type_.get_value repr in T {t with repr; value })
  let print ppf (T t) = t.type_.impl.printer ppf t.repr
end

let generate (T t) r =
  let repr = t.impl.generator r in
  let value = t.get_value repr in
  Repr.T { repr; value; type_ = t }

module G = Generator
module P = Printer
module S = Shrinker

let bool = define ~generator:G.bool ~printer:P.bool ()

let int = define ~generator:G.int ~printer:P.int ()

let option (T { impl = { generator; shrinker; printer; }; get_value }) =
  let generator = G.option generator in
  let shrinker = S.option shrinker in
  let printer = P.option printer in
  let get_value = Option.map get_value in
  T { impl = { generator; shrinker; printer; }; get_value }

let list (T { impl = { generator; shrinker; printer; }; get_value }) ~length =
  let generator = G.list generator ~length in
  let shrinker = S.list shrinker in
  let printer = P.list printer in
  let get_value = List.map get_value in
  T { impl = { generator; shrinker; printer; }; get_value }

let fn ?hash_arg (T { impl = { generator; shrinker; printer; }; get_value }) =
  let module Repr = struct
    type ('a, 'b) t =
      (* Pre-generate a constant in case we want to shrink this to a constant function *)
      { code : ('a, 'b) Code.t; const_for_shrinking : 'b }
  end
  in
  let generator =
    let open G.Let_syntax in
    let+ code = G.code ?hash_arg generator
    and+ const_for_shrinking = generator
    in
    Repr.{ code; const_for_shrinking }
  in
  let shrinker Repr.{ code; const_for_shrinking } =
    S.code shrinker ~const:const_for_shrinking code
    |> Seq.map (fun code -> Repr.{ code; const_for_shrinking })
  in
  let printer ppf Repr.{ code; _ } = P.code printer ppf code in
  let get_value Repr.{ code; _ } = (); fun a -> get_value (Code.call code a) in
  T { impl = { generator; shrinker; printer; }; get_value }

(* CR lmaurer: Do this properly. Probably needs a flag GADT so that I don't C+P everything. *)
let fn_w_id ?hash_arg t_ret = fn ?hash_arg t_ret

let map (T t) ~f =
  (* A moment of appreciation for polymorphic update. *)
  T { t with get_value = fun r -> f (t.get_value r) }

let fn2 ?hash_args ret_ty =
  fn ?hash_arg:hash_args ret_ty
  |> map ~f:(fun f a b -> f (a, b))

let fn3 ?hash_args ret_ty =
  fn ?hash_arg:hash_args ret_ty
  |> map ~f:(fun f a b c -> f (a, b, c))

let unit = 
  let generator = G.unit in
  let printer = P.unit in
  define ~generator ~printer ()

module T = struct
  type nonrec 'a t = 'a t
end

let tuple_impl impls =
  let generators impls = let open Tuple.Map(Impl)(G.T) in map impls ~f:{f = fun impl -> impl.generator} in
  let shrinkers impls = let open Tuple.Map(Impl)(S.T) in map impls ~f:{f = fun impl -> impl.shrinker } in
  let printers impls = let open Tuple.Map(Impl)(P.T) in map impls ~f:{f = fun impl -> impl.printer } in
let generator = G.tuple (generators impls) in
let shrinker = S.tuple (shrinkers impls) in
let printer = P.tuple (printers impls) in
  Impl.{ generator; shrinker; printer }

let tuple ts =
  let open struct
    type ('a, 'r) impls_and_getter_packed = Pack : ('b, 'r) Tuple.Of(Impl).t * (('b, 'r) Tuple.t -> ('a, 'r) Tuple.t) -> ('a, 'r) impls_and_getter_packed
  end
  in
  let rec impls_and_getter : type a r. (a, r) Tuple.Of(T).t -> (a, r) impls_and_getter_packed =
    function [] -> Pack ([], fun nil -> nil)
           | T { impl; get_value } :: ts ->
             let Pack (impls, get_values) = impls_and_getter ts in
             Pack (impl :: impls, function (a :: reprs) -> (get_value a :: get_values reprs) | [] -> assert false)
  in
  let Pack (impls, get_value) = impls_and_getter ts in
  let impl = tuple_impl impls in
  T { impl; get_value }

(* CR lmaurer: Special-case these, albeit painfully *)
let pair t_a t_b = tuple [t_a; t_b] |> map ~f:Tuple.to_pair

let triple t_a t_b t_c = tuple [t_a; t_b; t_c] |> map ~f:Tuple.to_triple

let quad t_a t_b t_c t_d = tuple [t_a; t_b; t_c; t_d] |> map ~f:Tuple.to_quad
