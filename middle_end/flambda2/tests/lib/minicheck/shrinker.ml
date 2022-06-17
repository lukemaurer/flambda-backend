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

type 'a t = 'a -> 'a Seq.t

let atomic _ = Seq.empty

module Seq = struct
  include Seq

  let singleton a = Seq.cons a Seq.empty

  let round_robin (type a) ts =
    let open struct
      type state =
        { next_round_rev : a t list;
          this_round : a t list
        }
    end in
    let rec step { next_round_rev; this_round } =
      match this_round with
      | [] -> begin
        match next_round_rev with
        | [] -> None
        | _ ->
          step { next_round_rev = []; this_round = List.rev next_round_rev }
      end
      | seq :: this_round -> (
        match (seq () : a Seq.node) with
        | Nil -> step { next_round_rev; this_round }
        | Cons (a, seq) ->
          let next_round_rev = seq :: next_round_rev in
          Some (a, { next_round_rev; this_round }))
    in
    Seq.unfold step { next_round_rev = []; this_round = ts }
end

let list t =
  let rec loop l =
    match l with
    | [] -> Seq.empty
    | a :: l ->
      Seq.round_robin
        [ Seq.singleton l;
          Seq.map (fun a -> a :: l) (t a);
          Seq.map (fun l -> a :: l) (fun () -> loop l ()) ]
  in
  loop

let const a _ = Seq.singleton a

let option t = function
  | None -> Seq.empty
  | Some a -> Seq.cons None (Seq.map Option.some (t a))

let code : type a b. ?const:b -> b t -> (a, b) Code.t t =
  fun ?const t code ->
  let shrink_as_const a = Seq.map (fun a -> Code.Const a) (t a) in
  match code with
  | Identity -> Seq.empty
  | Const a -> shrink_as_const a
  | Fun _ ->
    match const with
    | None -> Seq.empty
    | Some const -> Seq.cons (Code.Const const) (shrink_as_const const)

let code_w_id :type a. ?const:a -> a t -> (a, a) Code.t t =
  fun ?const t c ->
  match c with
  | Identity -> Seq.empty
  | _ -> Seq.cons Code.Identity (code ?const t c)

let pair s_a s_b (a, b) =
  Seq.round_robin
    [Seq.map (fun a -> a, b) (s_a a); Seq.map (fun b -> a, b) (s_b b)]

let triple s_a s_b s_c (a, b, c) =
  Seq.map (fun ((a, b), c) -> a, b, c) (pair (pair s_a s_b) s_c ((a, b), c))

let quad s_a s_b s_c s_d (a, b, c, d) =
  Seq.map
    (fun ((a, b), (c, d)) -> a, b, c, d)
    (pair (pair s_a s_b) (pair s_c s_d) ((a, b), (c, d)))

module T = struct
  type nonrec 'a t = 'a t
end

let rec tuple :
    type a b. (a, b) Tuple.Of(T).t -> (a, b) Tuple.t -> (a, b) Tuple.t Seq.t =
 fun shrinkers tup ->
  match shrinkers, tup with
  | [], [] -> Seq.empty
  | s :: shrinkers, a :: tup ->
    let shrink_a = Seq.map (fun a -> Tuple.cons a tup) (s a) in
    let shrink_tup =
      Seq.map (fun tup -> Tuple.cons a tup) (fun () -> tuple shrinkers tup ())
    in
    Seq.round_robin [shrink_a; shrink_tup]
  | _, _ -> assert false
