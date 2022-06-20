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
  type 'a t =
    { generator : 'a Generator.t;
      shrinker : 'a Shrinker.t;
      printer : 'a Printer.t
    }
end

type ('a, 'repr) t =
  { impl : 'repr Impl.t;
    get_value : 'repr -> 'a
  }

type 'a simple = ('a, 'a) t

let define ~generator ?(shrinker = Shrinker.atomic) ?(printer = Printer.opaque)
    ~get_value () =
  { impl = { generator; shrinker; printer }; get_value }

let define_simple ~generator ?shrinker ?printer () =
  define ~generator ?shrinker ?printer ~get_value:(fun a -> a) ()

let generate_repr t r = t.impl.generator r

let generate t r = generate_repr t r |> t.get_value

let shrink t repr : _ Seq.t = t.impl.shrinker repr

let print t ppf repr = t.impl.printer ppf repr

let value t repr = t.get_value repr

let with_repr_printer t ~printer = { t with impl = { t.impl with printer } }

let with_value_printer t ~printer =
  let printer ppf repr = printer ppf (t.get_value repr) in
  with_repr_printer t ~printer

let map t ~f =
  (* A moment of appreciation for polymorphic update. *)
  { t with get_value = (fun r -> f (t.get_value r)) }

let map_repr { impl = { generator; shrinker; printer }; get_value } ~f ~f_inv =
  let generator r = f (generator r) in
  let shrinker repr = Seq.map f (shrinker (f_inv repr)) in
  let printer ppf repr = printer ppf (f_inv repr) in
  let get_value a = get_value (f_inv a) in
  { impl = { generator; shrinker; printer }; get_value }

module Bound_repr = struct
  type nonrec ('a, 'repr) t =
    { repr : 'repr;
      type_ : ('a, 'repr) t
    }
end

let bind_generator generator ~f =
  let generator r =
    let type_ = f (generator r) in
    let repr = generate_repr type_ r in
    Bound_repr.{ repr; type_ }
  in
  let shrinker Bound_repr.{ repr; type_ } =
    Seq.map (fun repr -> Bound_repr.{ repr; type_ }) (shrink type_ repr)
  in
  let printer ppf Bound_repr.{ repr; type_ } = print type_ ppf repr in
  let get_value Bound_repr.{ repr; type_ } = value type_ repr in
  define ~generator ~shrinker ~printer ~get_value ()

let bind t ~f = bind_generator (generate t) ~f

module G = Generator
module P = Printer
module S = Shrinker

let bool = define_simple ~generator:G.bool ~printer:P.bool ()

let int = define_simple ~generator:G.int ~printer:P.int ()

let option { impl = { generator; shrinker; printer }; get_value } =
  let generator = G.option generator in
  let shrinker = S.option shrinker in
  let printer = P.option printer in
  let get_value = Option.map get_value in
  { impl = { generator; shrinker; printer }; get_value }

let list { impl = { generator; shrinker; printer }; get_value } ~length =
  let generator = G.list generator ~length in
  let shrinker = S.list shrinker in
  let printer = P.list printer in
  let get_value = List.map get_value in
  { impl = { generator; shrinker; printer }; get_value }

module Function_repr = struct
  type ('a, 'b) t =
    { (* Pre-generate a constant in case we want to shrink this to a constant
         function *)
      code : ('a, 'b) Code.t;
      const_for_shrinking : 'b
    }
end

let fn ?hash_arg { impl = { generator; shrinker; printer }; get_value } =
  let module Repr = Function_repr in
  let generator =
    let open G.Let_syntax in
    let+ code = G.code ?hash_arg generator
    and+ const_for_shrinking = generator in
    Repr.{ code; const_for_shrinking }
  in
  let shrinker Repr.{ code; const_for_shrinking } =
    S.code shrinker ~const:const_for_shrinking code
    |> Seq.map (fun code -> Repr.{ code; const_for_shrinking })
  in
  let printer ppf Repr.{ code; _ } = P.code printer ppf code in
  let get_value Repr.{ code; _ } =
    ();
    fun a -> get_value (Code.call code a)
  in
  { impl = { generator; shrinker; printer }; get_value }

(* CR lmaurer: Actually implement this with the ability to generate/shrink to
   the identity. Probably needs a flag GADT so that I don't C+P everything. *)
let fn_w_id ?hash_arg t_ret = fn ?hash_arg t_ret

let fn2 ?hash_args ret_ty =
  fn ?hash_arg:hash_args ret_ty |> map ~f:(fun f a b -> f (a, b))

let fn3 ?hash_args ret_ty =
  fn ?hash_arg:hash_args ret_ty |> map ~f:(fun f a b c -> f (a, b, c))

let unit =
  let generator = G.unit in
  let printer = P.unit in
  define_simple ~generator ~printer ()

module T = struct
  type nonrec ('a, 'repr) t = ('a, 'repr) t
end

let tuple_impl impls =
  let generators impls =
    let open Tuple.Map (Impl) (G.T) in
    map impls ~f:{ f = (fun impl -> impl.generator) }
  in
  let shrinkers impls =
    let open Tuple.Map (Impl) (S.T) in
    map impls ~f:{ f = (fun impl -> impl.shrinker) }
  in
  let printers impls =
    let open Tuple.Map (Impl) (P.T) in
    map impls ~f:{ f = (fun impl -> impl.printer) }
  in
  let generator = G.tuple (generators impls) in
  let shrinker = S.tuple (shrinkers impls) in
  let printer = P.tuple (printers impls) in
  Impl.{ generator; shrinker; printer }

let tuple (ts : ('a, 'reprs, 'r) Tuple.Of2(T).t) :
    (('a, 'r) Tuple.t, ('reprs, 'r) Tuple.t) t =
  let rec impls_and_getter :
      type a b r.
      (a, b, r) Tuple.Of2(T).t ->
      (b, r) Tuple.Of(Impl).t * ((b, r) Tuple.t -> (a, r) Tuple.t) = function
    | [] -> [], fun nil -> nil
    | { impl; get_value } :: ts -> (
      let impls, get_values = impls_and_getter ts in
      ( impl :: impls,
        function
        | a :: reprs -> get_value a :: get_values reprs | [] -> assert false ))
  in
  let impls, get_value = impls_and_getter ts in
  let impl = tuple_impl impls in
  { impl; get_value }

let pair t_a t_b =
  tuple [t_a; t_b]
  |> map ~f:Tuple.to_pair
  |> map_repr ~f:Tuple.to_pair ~f_inv:Tuple.of_pair

let triple t_a t_b t_c =
  tuple [t_a; t_b; t_c]
  |> map ~f:Tuple.to_triple
  |> map_repr ~f:Tuple.to_triple ~f_inv:Tuple.of_triple

let quad t_a t_b t_c t_d =
  tuple [t_a; t_b; t_c; t_d]
  |> map ~f:Tuple.to_quad
  |> map_repr ~f:Tuple.to_quad ~f_inv:Tuple.of_quad
