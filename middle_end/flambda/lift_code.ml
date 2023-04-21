(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2016 OCamlPro SAS                                    *)
(*   Copyright 2014--2016 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-9-30-40-41-42-66"]
open! Int_replace_polymorphic_compare

type lifter = Flambda.program -> Flambda.program

type def =
  | Immutable of Variable.t * Flambda.named Flambda.With_free_variables.t
  | Mutable of Mutable_variable.t * Variable.t * Lambda.layout
  | Region
  | Tail

let rebuild_let (defs : def list) (body : Flambda.t) =
  let module W = Flambda.With_free_variables in
  List.fold_left (fun body def ->
    match def with
    | Immutable(var, def) ->
        W.create_let_reusing_defining_expr var def body
    | Mutable(var, initial_value, contents_kind) ->
        Flambda.Let_mutable {var; initial_value; contents_kind; body}
    | Region ->
        Flambda.Region body
    | Tail ->
        Flambda.Tail body)
    body defs

(* Given something like [y = N; x = M], where we intend to produce [let x = M in
   let y = N in y], try and make [let x = M in N] instead by splitting out the
   innermost definition. If this isn't possible, instead just return the
   variable and the whole definition list. *)
let rec split_defs defs var =
  let module W = Flambda.With_free_variables in
  match defs with
  | Immutable (var', named) :: defs' when Variable.equal var var' -> begin
      match W.contents named with
      | Expr expr -> defs', expr
      | _ -> defs, Flambda.Var var
    end
  | Immutable (var', _) :: _ ->
    Misc.fatal_errorf "Expected binding for %a@ but found %a"
      Variable.print var Variable.print var'
  | Tail :: defs' ->
    (* Rewrite [let x = M in tail x] as simply [M] *)
    split_defs defs' var
  | (Mutable _ | Region) :: _ | [] ->
    Misc.fatal_errorf "Expected binding for %a"
      Variable.print var

let rebuild_expr defs var =
  let defs, body = split_defs defs var in
  rebuild_let defs body

let defs_close_region defs =
  let rec more_tails_than_regions defs tails regions =
    match defs with
    | [] -> tails > regions
    | Tail :: defs -> more_tails_than_regions defs (tails + 1) regions
    | Region :: defs -> more_tails_than_regions defs tails (regions + 1)
    | (Immutable _ | Mutable _) :: defs ->
        more_tails_than_regions defs tails regions
  in
  more_tails_than_regions defs 0 0

let rec tail_expr_in_expr0 (expr : Flambda.t) ~depth =
  match expr with
  | Tail expr -> depth = 0 || tail_expr_in_expr0 expr ~depth:(depth - 1)
  | Apply { reg_close = Rc_close_at_apply; _ }
  | Send { reg_close = Rc_close_at_apply; _ } -> depth = 0
  | Region expr ->
      tail_expr_in_expr0 expr ~depth:(depth + 1)
  | Let { body; _ }
  | Let_mutable { body; _ }
  | Let_rec (_, body) ->
      tail_expr_in_expr0 body ~depth
  | If_then_else (_, ifso, ifnot, _) ->
      tail_expr_in_expr0 ifso ~depth || tail_expr_in_expr0 ifnot ~depth
  | Switch (_, { consts; blocks; failaction; _ }) ->
      tail_expr_in_cases0 consts ~depth
      || tail_expr_in_cases0 blocks ~depth
      ||
      begin match failaction with
      | None -> false
      | Some expr -> tail_expr_in_expr0 expr ~depth
      end
  | String_switch (_, cases, failaction, _) ->
      tail_expr_in_cases0 cases ~depth
      ||
      begin match failaction with
      | None -> false
      | Some expr -> tail_expr_in_expr0 expr ~depth
      end
  | Static_catch (_, _, body, handler, _)
  | Try_with (body, _, handler, _) ->
      tail_expr_in_expr0 body ~depth || tail_expr_in_expr0 handler ~depth
  | Var _
  | Apply _
  | Send _
  | Assign _
  | Static_raise _
  | While _
  | For _
  | Proved_unreachable ->
    false

and tail_expr_in_cases0 : 'a. ('a * Flambda.t) list -> depth:int -> bool =
 fun cases ~depth ->
  List.exists (fun (_, expr) -> tail_expr_in_expr0 expr ~depth) cases

let tail_expr_in_expr expr = tail_expr_in_expr0 expr ~depth:0

(* Whether [let x = region ... M in N] can be rewritten as
   [region ... let x = M in tail N]. Only true if [M] has no [tail]
   expressions (besides those in lambdas). *)
let liftable_region_body expr = not (tail_expr_in_expr expr)

let rec extract_let_expr (acc:def list) dest let_expr =
  let module W = Flambda.With_free_variables in
  let acc =
    match (let_expr : Flambda.let_expr) with
    | { var = v1; defining_expr = Expr (Let let2); _ } ->
        extract_let_expr acc v1 let2
    | { var = v1; defining_expr = Expr (Let_mutable let_mut); _ } ->
        extract_let_mutable acc v1 let_mut
    | { var = v1; defining_expr = Expr (Region expr); _ } ->
        extract_region acc v1 expr
    | { var = v1;
        defining_expr = Expr (Apply ({ reg_close = Rc_close_at_apply; _ }
                                     as apply)) } ->
        extract_tail_call acc v1 apply
    | { var = v1;
        defining_expr = Expr (Send ({ reg_close = Rc_close_at_apply; _ }
                                    as send)) } ->
        extract_tail_send acc v1 send
    | { var = v; _ } ->
        Immutable(v, W.of_defining_expr_of_let let_expr) :: acc
  in
  let body = W.of_body_of_let let_expr in
  extract acc dest body

and extract_let_mutable acc dest let_mut =
  let module W = Flambda.With_free_variables in
  let { Flambda.var; initial_value; contents_kind; body } = let_mut in
  let acc = Mutable(var, initial_value, contents_kind) :: acc in
  extract acc dest (W.of_expr body)

and extract_region acc dest body =
  let module W = Flambda.With_free_variables in
  (* Ideally, we would recurse with the same [dest] since we're ultimately going
     to store there anyway. Unfortunately, if [body] has an unliftable tail,
     we're going to need [inner_dest] as an intermediary. *)
  let inner_dest = Variable.rename dest in
  let acc_expr = extract [] inner_dest (W.of_expr body) in
  (* If possible, recover the expression that gets assigned to [inner_dest] so
     we can directly assign [dest] to it instead *)
  match split_defs acc_expr inner_dest with
  | acc_expr, body when liftable_region_body body ->
    (* The accumulator must remain balanced between [Region] and [Tail], since
       it defines a scope into which [extract_let_expr] will move arbitrary
       computations - if there is a [Region] but no [Tail], this means we're
       moving those computations into a different region. It may be that
       [acc_expr] already has a [Tail] (because we lifted it out of [body]), but
       otherwise we need to add it. *)
    let need_tail = not (defs_close_region acc_expr) in
    List.concat
      [ if need_tail then [ Tail ] else [];
        [ Immutable (dest, W.expr (W.of_expr body)) ];
        acc_expr;
        [ Region ];
        acc ]
  | _ ->
    (* We can't lift it, so we just have to bundle everything back up in a
       region. *)
    let expr = Flambda.Region (rebuild_expr acc_expr inner_dest) in
    Immutable(dest, W.expr (W.of_expr expr)) :: acc

and extract_tail_call acc dest (apply : Flambda.apply) =
  let module W = Flambda.With_free_variables in
  (* Rewrite a close-at-apply call as a normal call in a [Tail] so that we can
     float the [Tail]. Note that it will still be a tail call in the normal
     sense (it replaces the old stack frame, etc.), it just no longer has the
     additional semantics of ending the region first. *)
  let apply =
    (* We can safely assume [Rc_normal] makes sense here because the original
       application was marked [Rc_close_at_apply], so it must be intended to be
       a tail call and marking it [Rc_nontail] would be silly. *)
    { apply with reg_close = Rc_normal }
  in
  Immutable (dest, W.expr (W.of_expr (Apply apply))) :: Tail :: acc

and extract_tail_send acc dest (send : Flambda.send) =
  let module W = Flambda.With_free_variables in
  (* Same as [extract_tail_call] but with sends *)
  let send = { send with reg_close = Rc_normal } in
  Immutable (dest, W.expr (W.of_expr (Send send))) :: Tail :: acc

and extract acc dest expr =
  let module W = Flambda.With_free_variables in
  match (W.contents expr : Flambda.t) with
  | Let let_expr ->
    extract_let_expr acc dest let_expr
  | Let_mutable let_mutable ->
    extract_let_mutable acc dest let_mutable
  | Region expr ->
    extract_region acc dest expr
  | Tail expr ->
    (* One might worry about just adding [Tail] to the accumulator, since in
       general the accumulator defines a scope into which we're moving arbitrary
       expressions. In [extract_region], we're careful to make sure the
       accumulator remains "balanced" between [Region] and [Tail] for this
       reason. Here we can get away with unconditionally tossing [Tail] onto the
       accumulator because one of the following must be true:

       1. We are in the tail of a [Region] being handled by [extract_region],
          which will see that we've added this [Tail] and not add one of
          its own.

       2. We are in the tail of the entire expression (that is, the argument to
          [lift_lets_expr]), and thus [expr] is the very last expression we're
          processing, so nothing else will be moved into this [Tail]. *)
    extract (Tail :: acc) dest (W.of_expr expr)
  | Apply ({ reg_close = Rc_close_at_apply; _ } as apply) ->
    extract_tail_call acc dest apply
  | Send ({ reg_close = Rc_close_at_apply; _ } as send) ->
    extract_tail_send acc dest send
  | _ ->
    Immutable (dest, W.expr expr) :: acc

let rec lift_lets_expr (expr:Flambda.t) ~toplevel : Flambda.t =
  match expr with
  | Let let_expr ->
    let dest = Variable.create Internal_variable_names.lifted_let in
    let defs = extract_let_expr [] dest let_expr in
    let rev_defs = List.rev_map (lift_lets_def ~toplevel) defs in
    rebuild_expr (List.rev rev_defs) dest
  | Let_mutable let_mut ->
    let dest = Variable.create Internal_variable_names.lifted_let in
    let defs = extract_let_mutable [] dest let_mut in
    let rev_defs = List.rev_map (lift_lets_def ~toplevel) defs in
    rebuild_expr (List.rev rev_defs) dest
  | e ->
    Flambda_iterators.map_subexpressions
      (lift_lets_expr ~toplevel)
      (lift_lets_named ~toplevel)
      e

and lift_lets_def def ~toplevel =
  let module W = Flambda.With_free_variables in
  match def with
  | Mutable _ -> def
  | Immutable(var, named) ->
    let named =
      match W.contents named with
      | Expr e -> W.expr (W.of_expr (lift_lets_expr e ~toplevel))
      | Set_of_closures set when not toplevel ->
        W.of_named
          (Set_of_closures
             (Flambda_iterators.map_function_bodies
                ~f:(lift_lets_expr ~toplevel) set))
      | Symbol _ | Const _ | Allocated_const _ | Read_mutable _
      | Read_symbol_field (_, _) | Project_closure _
      | Move_within_set_of_closures _ | Project_var _
      | Prim _ | Set_of_closures _ ->
        named
    in
    Immutable(var, named)
  | Region | Tail -> def

and lift_lets_named _var (named:Flambda.named) ~toplevel : Flambda.named =
  match named with
  | Expr e ->
    Expr (lift_lets_expr e ~toplevel)
  | Set_of_closures set when not toplevel ->
    Set_of_closures
      (Flambda_iterators.map_function_bodies ~f:(lift_lets_expr ~toplevel) set)
  | Symbol _ | Const _ | Allocated_const _ | Read_mutable _
  | Read_symbol_field (_, _) | Project_closure _ | Move_within_set_of_closures _
  | Project_var _ | Prim _ | Set_of_closures _ ->
    named

module Sort_lets = Strongly_connected_components.Make (Variable)

let rebuild_let_rec (defs:(Variable.t * Flambda.named) list) body =
  let map = Variable.Map.of_list defs in
  let graph =
    Variable.Map.map
      (fun named ->
         Variable.Set.filter (fun v -> Variable.Map.mem v map)
           (Flambda.free_variables_named named))
      map
  in
  let components =
    Sort_lets.connected_components_sorted_from_roots_to_leaf graph
  in
  Array.fold_left (fun body (component:Sort_lets.component) ->
      match component with
      | No_loop v ->
          let def = Variable.Map.find v map in
          Flambda.create_let v def body
      | Has_loop l ->
          Flambda.Let_rec
            (List.map (fun v -> v, Variable.Map.find v map) l,
             body))
    body components

let lift_let_rec program =
  Flambda_iterators.map_exprs_at_toplevel_of_program program
    ~f:(Flambda_iterators.map_expr
          (fun expr -> match expr with
             | Let_rec (defs, body) ->
                 rebuild_let_rec defs body
             | expr -> expr))

let lift_lets program =
  let program = lift_let_rec program in
  Flambda_iterators.map_exprs_at_toplevel_of_program program
    ~f:(lift_lets_expr ~toplevel:false)

let lifting_helper exprs ~evaluation_order ~create_body ~name =
  let vars, lets =
    (* [vars] corresponds elementwise to [exprs]; the order is unchanged. *)
    List.fold_right (fun (flam : Flambda.t) (vars, lets) ->
        match flam with
        | Var v ->
          (* Note that [v] is (statically) always an immutable variable. *)
          v::vars, lets
        | expr ->
          let v =
            Variable.create name ~current_compilation_unit:
                (Compilation_unit.get_current_exn ())
          in
          v::vars, (v, expr)::lets)
      exprs ([], [])
  in
  let lets =
    match evaluation_order with
    | `Right_to_left -> lets
    | `Left_to_right -> List.rev lets
  in
  List.fold_left (fun body (v, expr) ->
      Flambda.create_let v (Expr expr) body)
    (create_body vars) lets
