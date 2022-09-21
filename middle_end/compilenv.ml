(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Gallium, INRIA Rocquencourt           *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2010 Institut National de Recherche en Informatique et     *)
(*     en Automatique                                                     *)
(*   Copyright 2013--2016 OCamlPro SAS                                    *)
(*   Copyright 2014--2016 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* Compilation environments for compilation units *)

[@@@ocaml.warning "+a-4-9-40-41-42"]

open Config
open Cmx_format

module CU = Compilation_unit

type error =
    Not_a_unit_info of string
  | Corrupted_unit_info of string
  | Illegal_renaming of CU.Name.t * CU.Name.t * string

exception Error of error

let global_infos_table =
  (CU.Name.Tbl.create 17 : unit_infos option CU.Name.Tbl.t)
let export_infos_table =
  (CU.Name.Tbl.create 10 : Export_info.t CU.Name.Tbl.t)

let reset_info_tables () =
  CU.Name.Tbl.reset global_infos_table;
  CU.Name.Tbl.reset export_infos_table

let imported_sets_of_closures_table =
  (Set_of_closures_id.Tbl.create 10
   : Simple_value_approx.function_declarations option
       Set_of_closures_id.Tbl.t)

module CstMap =
  Map.Make(struct
    type t = Clambda.ustructured_constant
    let compare = Clambda.compare_structured_constants
    (* PR#6442: it is incorrect to use Stdlib.compare on values of type t
       because it compares "0.0" and "-0.0" equal. *)
  end)

module SymMap = Misc.Stdlib.String.Map

type structured_constants =
  {
    strcst_shared: string CstMap.t;
    strcst_all: Clambda.ustructured_constant SymMap.t;
  }

let structured_constants_empty  =
  {
    strcst_shared = CstMap.empty;
    strcst_all = SymMap.empty;
  }

let structured_constants = ref structured_constants_empty


let exported_constants = Hashtbl.create 17

let merged_environment = ref Export_info.empty

let default_ui_export_info =
  if Config.flambda then
    Cmx_format.Flambda1 Export_info.empty
  else if Config.flambda2 then
    Cmx_format.Flambda2 None
  else
    Cmx_format.Clambda Value_unknown

let current_unit =
  { ui_unit = CU.dummy;
    ui_defines = [];
    ui_imports_cmi = [];
    ui_imports_cmx = [];
    ui_generic_fns = { curry_fun = []; apply_fun = []; send_fun = [] };
    ui_force_link = false;
    ui_export_info = default_ui_export_info }

let reset compilation_unit =
  CU.Name.Tbl.clear global_infos_table;
  Set_of_closures_id.Tbl.clear imported_sets_of_closures_table;
  current_unit.ui_unit <- compilation_unit;
  current_unit.ui_defines <- [compilation_unit];
  current_unit.ui_imports_cmi <- [];
  current_unit.ui_imports_cmx <- [];
  current_unit.ui_generic_fns <-
    { curry_fun = []; apply_fun = []; send_fun = [] };
  current_unit.ui_force_link <- !Clflags.link_everything;
  Hashtbl.clear exported_constants;
  structured_constants := structured_constants_empty;
  current_unit.ui_export_info <- default_ui_export_info;
  merged_environment := Export_info.empty;
  CU.Name.Tbl.clear export_infos_table;
  Compilation_unit.set_current compilation_unit

let current_unit_infos () =
  current_unit

let read_unit_info filename =
  let ic = open_in_bin filename in
  try
    let buffer = really_input_string ic (String.length cmx_magic_number) in
    if buffer <> cmx_magic_number then begin
      close_in ic;
      raise(Error(Not_a_unit_info filename))
    end;
    let ui = (input_value ic : unit_infos) in
    let crc = Digest.input ic in
    close_in ic;
    (ui, crc)
  with End_of_file | Failure _ ->
    close_in ic;
    raise(Error(Corrupted_unit_info(filename)))

let read_library_info filename =
  let ic = open_in_bin filename in
  let buffer = really_input_string ic (String.length cmxa_magic_number) in
  if buffer <> cmxa_magic_number then
    raise(Error(Not_a_unit_info filename));
  let infos = (input_value ic : library_infos) in
  close_in ic;
  infos

(* Read and cache info on global identifiers *)

(* CR mshinwell: check all uses of this function *)
let get_unit_info modname =
  if CU.Name.equal modname (CU.name current_unit.ui_unit)
  then
    Some current_unit
  else begin
    try
      CU.Name.Tbl.find global_infos_table modname
    with Not_found ->
      let (infos, crc) =
        if Env.is_imported_opaque modname then (None, None)
        else begin
          try
            let filename =
              Load_path.find_uncap ((modname |> CU.Name.to_string) ^ ".cmx") in
            let (ui, crc) = read_unit_info filename in
            if not (CU.Name.equal (CU.name ui.ui_unit) modname)
            then
              raise(Error(Illegal_renaming(modname, CU.name ui.ui_unit, filename)));
            (Some ui, Some crc)
          with Not_found ->
            let warn = Warnings.No_cmx_file (modname |> CU.Name.to_string) in
              Location.prerr_warning Location.none warn;
              (None, None)
          end
      in
      current_unit.ui_imports_cmx <-
        (modname, crc) :: current_unit.ui_imports_cmx;
      CU.Name.Tbl.add global_infos_table modname infos;
      infos
  end

let get_unit_export_info modname =
  match get_unit_info modname with
  | None -> None
  | Some ui -> Some ui.ui_export_info

let get_global_info comp_unit =
  get_unit_info (CU.name comp_unit)

let get_global_export_info id =
  match get_global_info id with
  | None -> None
  | Some ui -> Some ui.ui_export_info

let cache_unit_info ui =
  CU.Name.Tbl.add global_infos_table (CU.name ui.ui_unit) (Some ui)

(* Return the approximation of a global identifier *)

let get_clambda_approx ui =
  assert(not Config.flambda);
  match ui.ui_export_info with
  | Flambda1 _ | Flambda2 _ -> assert false
  | Clambda approx -> approx

let toplevel_approx : Clambda.value_approximation CU.Tbl.t = CU.Tbl.create 16

let record_global_approx_toplevel () =
  CU.Tbl.add toplevel_approx current_unit.ui_unit (get_clambda_approx current_unit)

let global_approx comp_unit =
  try CU.Tbl.find toplevel_approx comp_unit
  with Not_found ->
    match get_global_info comp_unit with
      | None -> Clambda.Value_unknown
      | Some ui -> get_clambda_approx ui

(* Register the approximation of the module being compiled *)

let set_global_approx approx =
  assert(not Config.flambda);
  current_unit.ui_export_info <- Clambda approx

(* Exporting and importing cross module information (Flambda only) *)

let get_flambda_export_info ui =
  assert(Config.flambda);
  match ui.ui_export_info with
  | Clambda _ | Flambda2 _ -> assert false
  | Flambda1 ei -> ei

let set_export_info export_info =
  assert(Config.flambda);
  current_unit.ui_export_info <- Flambda1 export_info

let flambda2_set_export_info export_info =
  assert(Config.flambda2);
  current_unit.ui_export_info <- Flambda2 (Some export_info)

(* Determine which .cmx file to load for a given compilation unit.
   This is tricky in the case of packs.  It can be done by lining up the
   desired compilation unit's full path (i.e. pack prefix then unit name)
   against the current unit's full path and observing when/if they diverge. *)
let which_cmx_file desired_comp_unit =
  let desired_prefix = CU.for_pack_prefix desired_comp_unit in
  if CU.Prefix.is_empty desired_prefix then
    (* If the unit we're looking for is not in a pack, then the correct .cmx
       file is the one with the same name as the unit, irrespective of any
       current pack. *)
    CU.name desired_comp_unit
  else
    let current_comp_unit = Compilation_unit.get_current_exn () in
    (* This lines up the full paths as described above. *)
    let rec match_components ~current ~desired =
      match current, desired with
      | current_name::current, desired_name::desired ->
        if CU.Name.equal current_name desired_name then
          (* The full paths are equal up to the current point; keep going. *)
          match_components ~current ~desired
        else
          (* The paths have diverged.  The next component of the desired
             path is the .cmx file to load. *)
          desired_name
      | [], desired_name::_desired ->
        (* The whole of the current unit's full path (including the name of
           the unit itself) is now known to be a prefix of the desired unit's
           pack *prefix*.  This means we must be making a pack.  The .cmx
           file to load is named after the next component of the desired
           unit's path (which may in turn be a pack). *)
        desired_name
      | [], [] ->
        (* The paths were equal, so the desired compilation unit is just the
           current one. *)
        CU.name desired_comp_unit
      | _::_, [] ->
        (* The current path is longer than the desired unit's path, which
           means we're attempting to go back up the pack hierarchy.  This is
           an error. *)
        Misc.fatal_errorf "Compilation unit@ %a@ is inaccessible when \
            compiling compilation unit@ %a"
          CU.print desired_comp_unit
          CU.print current_comp_unit
    in
    match_components ~current:(CU.full_path current_comp_unit)
      ~desired:(CU.full_path desired_comp_unit)

let approx_for_global comp_unit =
  if CU.equal comp_unit CU.predef_exn
  then invalid_arg "approx_for_global with predef_exn compilation unit";
  let modname = which_cmx_file comp_unit in
  match CU.Name.Tbl.find export_infos_table modname with
  | otherwise -> Some otherwise
  | exception Not_found ->
    match get_unit_info modname with
    | None -> None
    | Some ui ->
      let exported = get_flambda_export_info ui in
      CU.Name.Tbl.add export_infos_table modname exported;
      merged_environment := Export_info.merge !merged_environment exported;
      Some exported

let approx_env () = !merged_environment

(* Record that a currying function or application function is needed *)

let need_curry_fun arity =
  let fns = current_unit.ui_generic_fns in
  if not (List.mem arity fns.curry_fun) then
    current_unit.ui_generic_fns <-
      { fns with curry_fun = arity :: fns.curry_fun }

let need_apply_fun n mode =
  assert(n > 0);
  let fns = current_unit.ui_generic_fns in
  if not (List.mem (n,mode) fns.apply_fun) then
    current_unit.ui_generic_fns <-
      { fns with apply_fun = (n,mode) :: fns.apply_fun }

let need_send_fun n mode =
  let fns = current_unit.ui_generic_fns in
  if not (List.mem (n,mode) fns.send_fun) then
    current_unit.ui_generic_fns <-
      { fns with send_fun = (n,mode) :: fns.send_fun }

(* Write the description of the current unit *)

let write_unit_info info filename =
  let oc = open_out_bin filename in
  output_string oc cmx_magic_number;
  output_value oc info;
  flush oc;
  let crc = Digest.file filename in
  Digest.output oc crc;
  close_out oc

let save_unit_info filename =
  current_unit.ui_imports_cmi <- Env.imports();
  write_unit_info current_unit filename

let snapshot () = !structured_constants
let backtrack s = structured_constants := s

let new_const_symbol () =
  Symbol.for_new_const_in_current_unit ()
  |> Symbol.linkage_name
  |> Linkage_name.to_string

let new_structured_constant cst ~shared =
  let {strcst_shared; strcst_all} = !structured_constants in
  if shared then
    try
      CstMap.find cst strcst_shared
    with Not_found ->
      let lbl = new_const_symbol() in
      structured_constants :=
        {
          strcst_shared = CstMap.add cst lbl strcst_shared;
          strcst_all = SymMap.add lbl cst strcst_all;
        };
      lbl
  else
    let lbl = new_const_symbol() in
    structured_constants :=
      {
        strcst_shared;
        strcst_all = SymMap.add lbl cst strcst_all;
      };
    lbl

let add_exported_constant s =
  Hashtbl.replace exported_constants s ()

let clear_structured_constants () =
  structured_constants := structured_constants_empty

let structured_constant_of_symbol s =
  SymMap.find_opt s (!structured_constants).strcst_all

let structured_constants () =
  let provenance : Clambda.usymbol_provenance =
    { original_idents = [];
      module_path =
        (* CR-someday lmaurer: Properly construct a [Path.t] from the module name
           with its pack prefix. *)
        Path.Pident (Ident.create_persistent (Compilation_unit.Name.to_string (
          Compilation_unit.name (Compilation_unit.get_current_exn ()))));
    }
  in
  SymMap.bindings (!structured_constants).strcst_all
  |> List.map
    (fun (symbol, definition) ->
       {
         Clambda.symbol;
         exported = Hashtbl.mem exported_constants symbol;
         definition;
         provenance = Some provenance;
        })

let require_global comp_unit =
  ignore (get_global_info comp_unit : Cmx_format.unit_infos option)

(* Error report *)

open Format

let report_error ppf = function
  | Not_a_unit_info filename ->
      fprintf ppf "%a@ is not a compilation unit description."
        Location.print_filename filename
  | Corrupted_unit_info filename ->
      fprintf ppf "Corrupted compilation unit description@ %a"
        Location.print_filename filename
  | Illegal_renaming(name, modname, filename) ->
      fprintf ppf "%a@ contains the description for unit\
                   @ %a when %a was expected"
        Location.print_filename filename
        CU.Name.print name
        CU.Name.print modname

let () =
  Location.register_error_of_exn
    (function
      | Error err -> Some (Location.error_of_printer_file report_error err)
      | _ -> None
    )
