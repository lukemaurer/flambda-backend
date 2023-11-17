(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*          Jerome Vouillon, projet Cristal, INRIA Rocquencourt           *)
(*                                                                        *)
(*   Copyright 1996 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

open Asttypes
open Lambda

(* Get oo primitives identifiers *)

let oo_prim = Lambda.transl_prim "CamlinternalOO"

(* Share blocks *)

let consts : (structured_constant, Ident.t) Hashtbl.t = Hashtbl.create 17

let share c =
  match c with
    Const_block (_n, l) when l <> [] ->
      begin try
        Lvar (Hashtbl.find consts c)
      with Not_found ->
        let id = Ident.create_local "shared" in
        Hashtbl.add consts c id;
        Lvar id
      end
  | _ -> Lconst c

(* Collect labels *)

let cache_required = ref false
let method_cache = ref lambda_unit
let method_count = ref 0
let method_table = ref []

let meth_tag s = Lconst(Const_base(Const_int(Btype.hash_variant s)))

let next_cache tag =
  let n = !method_count in
  incr method_count;
  (tag, [!method_cache; Lconst(Const_base(Const_int n))])

let rec is_path = function
    Lvar _ | Lprim (Pgetglobal _, [], _) | Lconst _ -> true
  | Lprim (Pfield _, [lam], _) -> is_path lam
  | Lprim ((Parrayrefu _ | Parrayrefs _), [lam1; lam2], _) ->
      is_path lam1 && is_path lam2
  | _ -> false

let meth obj lab =
  let tag = meth_tag lab in
  if not (!cache_required && !Clflags.native_code) then (tag, []) else
  if not (is_path obj) then next_cache tag else
  try
    let r = List.assoc obj !method_table in
    try
      (tag, List.assoc tag !r)
    with Not_found ->
      let p = next_cache tag in
      r := p :: !r;
      p
  with Not_found ->
    let p = next_cache tag in
    method_table := (obj, ref [p]) :: !method_table;
    p

let reset_labels () =
  Hashtbl.clear consts;
  method_count := 0;
  method_table := []

(* Insert labels *)

let int n = Lconst (Const_base (Const_int n))

(* CR layouts v5: To change when we have arrays of other sorts *)
let prim_makearray =
  Primitive.simple_on_values ~name:"caml_make_vect" ~arity:2 ~alloc:true

(* Also use it for required globals *)
let transl_label_init_general f =
  let expr, size = f () in
  let expr =
    Hashtbl.fold
      (fun c id expr ->
         let layout = Lambda.structured_constant_layout c in
         let const =
           Lprim (Popaque layout, [Lconst c], Debuginfo.Scoped_location.Loc_unknown)
         in
         (* CR ncourant: this *should* not be too precise for the moment,
            but we should take care, or fix the underlying cause that led
            us to using [Popaque]. *)
         Llet(Alias, layout, id, const, expr))
      consts expr
  in
  (*let expr =
    List.fold_right
      (fun id expr -> Lsequence(Lprim(Pgetglobal id, [], Location.none), expr))
      (Env.get_required_globals ()) expr
  in
  Env.reset_required_globals ();*)
  reset_labels ();
  expr, size

let transl_label_init_flambda f =
  assert(Config.flambda || Config.flambda2);
  let method_cache_id = Ident.create_local "method_cache" in
  method_cache := Lvar method_cache_id;
  (* Calling f (usually Translmod.transl_struct) requires the
     method_cache variable to be initialised to be able to generate
     method accesses. *)
  let expr, size = f () in
  let expr =
    if !method_count = 0 then expr
    else
      Llet (Strict, Lambda.layout_array Pgenarray, method_cache_id,
        Lprim (Pccall prim_makearray,
               [int !method_count; int 0],
               Loc_unknown),
        expr)
  in
  transl_label_init_general (fun () -> expr, size)

let transl_store_label_init ~get_global size f arg =
  assert(not (Config.flambda || Config.flambda2));
  assert(!Clflags.native_code);
  let glob = get_global (Loc_unknown : scoped_location) in
  method_cache := Lprim(mod_field ~read_semantics:Reads_vary size,
                        (* XXX KC: conservative *)
                        [glob],
                        Loc_unknown);
  let expr = f arg in
  let (size, expr) =
    if !method_count = 0 then (size, expr) else
    (size+1,
     Lsequence(
     Lprim(mod_setfield size,
           [glob;
            Lprim (Pccall prim_makearray,
                   [int !method_count; int 0],
                   Loc_unknown)],
           Loc_unknown),
     expr))
  in
  let lam, size = transl_label_init_general (fun () -> (expr, size)) in
  size, lam

let transl_label_init f =
  if !Clflags.native_code then
    transl_label_init_flambda f
  else
    transl_label_init_general f

(* Share classes *)

let wrapping = ref false
let top_env = ref Env.empty
let classes = ref []
let method_ids = ref Ident.Set.empty

let oo_add_class id =
  classes := id :: !classes;
  (!top_env, !cache_required)

let oo_wrap env req f x =
  if !wrapping then
    if !cache_required then f x else
      Misc.protect_refs [Misc.R (cache_required, true)] (fun () ->
          f x
        )
  else
    Misc.protect_refs [Misc.R (wrapping, true); Misc.R (top_env, env)]
      (fun () ->
         cache_required := req;
         classes := [];
         method_ids := Ident.Set.empty;
         let lambda = f x in
         let lambda =
           List.fold_left
             (fun lambda id ->
                let cl =
                  Lprim(Pmakeblock(0, Mutable, None, alloc_heap),
                        [lambda_unit; lambda_unit; lambda_unit],
                        Loc_unknown)
                in
                Llet(StrictOpt, Lambda.layout_class, id,
                     Lprim (Popaque Lambda.layout_class, [cl], Loc_unknown),
                     lambda))
             lambda !classes
         in
         lambda
      )

let reset () =
  Hashtbl.clear consts;
  cache_required := false;
  method_cache := lambda_unit;
  method_count := 0;
  method_table := [];
  wrapping := false;
  top_env := Env.empty;
  classes := [];
  method_ids := Ident.Set.empty
