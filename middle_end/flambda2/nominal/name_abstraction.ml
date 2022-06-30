(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2019 OCamlPro SAS                                    *)
(*   Copyright 2014--2019 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-30-40-41-42"]

module type Term = sig
  type t

  val apply_renaming : t -> Renaming.t -> t

  include Contains_ids.S with type t := t
end

type ('bindable, 'term) t = 'bindable * 'term

let[@inline always] pattern_match (type bindable)
    (module Bindable : Bindable.S with type t = bindable) (bindable, term)
    ~apply_renaming_to_term ~f =
  let fresh_bindable = Bindable.rename bindable in
  let perm = Bindable.renaming bindable ~guaranteed_fresh:fresh_bindable in
  let fresh_term = apply_renaming_to_term term perm in
  f fresh_bindable fresh_term

let[@inline always] pattern_match_for_printing bindable_impl
    ((bindable, term) as t) ~apply_renaming_to_term ~f =
  if Flambda_features.freshen_when_printing ()
  then pattern_match bindable_impl t ~apply_renaming_to_term ~f
  else f bindable term

let[@inline always] pattern_match_pair (type bindable)
    (module Bindable : Bindable.S with type t = bindable) (bindable0, term0)
    (bindable1, term1) ~apply_renaming_to_term ~f =
  let fresh_bindable = Bindable.rename bindable0 in
  let perm0 = Bindable.renaming bindable0 ~guaranteed_fresh:fresh_bindable in
  let perm1 = Bindable.renaming bindable1 ~guaranteed_fresh:fresh_bindable in
  let fresh_term0 = apply_renaming_to_term term0 perm0 in
  let fresh_term1 = apply_renaming_to_term term1 perm1 in
  f fresh_bindable fresh_term0 fresh_term1

let apply_renaming (type bindable)
    (module Bindable : Bindable.S with type t = bindable)
    ((bindable, term) as t) perm ~apply_renaming_to_term =
  if Renaming.is_empty perm
  then t
  else
    let bindable' = Bindable.apply_renaming bindable perm in
    let term' = apply_renaming_to_term term perm in
    if bindable == bindable' && term == term' then t else bindable', term'

module Make_matching_and_renaming0
    (Bindable : Bindable.S) (Term : sig
      type t

      val apply_renaming : t -> Renaming.t -> t
    end) =
struct
  let[@inline always] pattern_match (bindable, term) ~f =
    pattern_match
      (module Bindable)
      (bindable, term) ~f ~apply_renaming_to_term:Term.apply_renaming

  let[@inline always] pattern_match_for_printing (bindable, term) ~f =
    pattern_match_for_printing
      (module Bindable)
      (bindable, term) ~f ~apply_renaming_to_term:Term.apply_renaming

  let[@inline always] pattern_match_pair (bindable0, term0) (bindable1, term1)
      ~f =
    pattern_match_pair
      (module Bindable)
      (bindable0, term0) (bindable1, term1) ~f
      ~apply_renaming_to_term:Term.apply_renaming

  let apply_renaming t perm =
    apply_renaming
      (module Bindable)
      t perm ~apply_renaming_to_term:Term.apply_renaming

  let[@inline always] ( let<> ) t f =
    pattern_match t ~f:(fun bindable term -> f (bindable, term))
end
[@@inline always]

module Make_ids_for_export0 (Bindable : Bindable.S) (Term : Contains_ids.S) =
struct
  let all_ids_for_export (bindable, term) =
    Ids_for_export.union
      (Bindable.all_ids_for_export bindable)
      (Term.all_ids_for_export term)
end
[@@inline always]

module Make (Bindable : Bindable.S) (Term : Term) = struct
  type nonrec t = (Bindable.t, Term.t) t

  let create bindable term = bindable, term

  include Make_matching_and_renaming0 (Bindable) (Term)
  include Make_ids_for_export0 (Bindable) (Term)
end
[@@inline always]

module Make_free_names
    (Bindable : Bindable.S) (Term : sig
      include Term

      val free_names : t -> Name_occurrences.t
    end) =
struct
  type nonrec t = (Bindable.t, Term.t) t

  let free_names (bindable, term) =
    Name_occurrences.diff (Term.free_names term) (Bindable.free_names bindable)
end
[@@inline always]

module Make_matching_and_renaming
    (Bindable : Bindable.S) (Term : sig
      type t

      val apply_renaming : t -> Renaming.t -> t
    end) =
struct
  type nonrec t = (Bindable.t, Term.t) t

  include Make_matching_and_renaming0 (Bindable) (Term)
end
[@@inline always]

module Make_ids_for_export (Bindable : Bindable.S) (Term : Contains_ids.S) =
struct
  type nonrec t = (Bindable.t, Term.t) t

  include Make_ids_for_export0 (Bindable) (Term)
end
[@@inline always]
