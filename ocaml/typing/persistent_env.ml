(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*   Xavier Leroy, projet Gallium, INRIA Rocquencourt                     *)
(*   Gabriel Scherer, projet Parsifal, INRIA Saclay                       *)
(*                                                                        *)
(*   Copyright 2019 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* Persistent structure descriptions *)

open Misc
open Cmi_format

module CU = Compilation_unit
module Consistbl_data = Import_info.Intf.Nonalias.Kind
module Consistbl = Consistbl.Make (CU.Name) (Consistbl_data)

let add_delayed_check_forward = ref (fun _ -> assert false)

type error =
  | Illegal_renaming of CU.Name.t * CU.Name.t * filepath
  | Inconsistent_import of CU.Name.t * filepath * filepath
  | Need_recursive_types of CU.Name.t
  | Inconsistent_package_declaration_between_imports of
      filepath * CU.t * CU.t
  | Direct_reference_from_wrong_package of
      CU.t * filepath * CU.Prefix.t
  | Illegal_import_of_parameter of CU.Name.t * filepath
  | Not_compiled_as_parameter of CU.Name.t * filepath
  | Cannot_implement_parameter of CU.Name.t * filepath

exception Error of error
let error err = raise (Error err)

module Persistent_signature = struct
  type t =
    { filename : string;
      cmi : Cmi_format.cmi_infos_lazy;
      visibility : Load_path.visibility }

  let load = ref (fun ~allow_hidden ~unit_name ->
    let unit_name = CU.Name.to_string unit_name in
    match Load_path.find_uncap_with_visibility (unit_name ^ ".cmi") with
    | filename, visibility when allow_hidden ->
      Some { filename; cmi = read_cmi_lazy filename; visibility}
    | filename, Visible ->
      Some { filename; cmi = read_cmi_lazy filename; visibility = Visible}
    | _, Hidden
    | exception Not_found -> None)
end

type can_load_cmis =
  | Can_load_cmis
  | Cannot_load_cmis of Lazy_backtrack.log

type pers_struct = {
  ps_is_param: bool;
  ps_crcs: Import_info.Intf.t array;
  ps_filename: string;
  ps_visibility: Load_path.visibility;
}

(* If a .cmi file is missing (or invalid), we
   store it as Missing in the cache. *)
type 'a pers_struct_info =
  | Missing
  | Found of pers_struct * 'a

type 'a t = {
  persistent_structures :
    (CU.Name.t, 'a pers_struct_info) Hashtbl.t;
  imported_units: CU.Name.Set.t ref;
  imported_opaque_units: CU.Name.Set.t ref;
  param_imports : CU.Name.Set.t ref;
  crc_units: Consistbl.t;
  can_load_cmis: can_load_cmis ref;
}

let empty () = {
  persistent_structures = Hashtbl.create 17;
  imported_units = ref CU.Name.Set.empty;
  imported_opaque_units = ref CU.Name.Set.empty;
  param_imports = ref CU.Name.Set.empty;
  crc_units = Consistbl.create ();
  can_load_cmis = ref Can_load_cmis;
}

let clear penv =
  let {
    persistent_structures;
    imported_units;
    imported_opaque_units;
    param_imports;
    crc_units;
    can_load_cmis;
  } = penv in
  Hashtbl.clear persistent_structures;
  imported_units := CU.Name.Set.empty;
  imported_opaque_units := CU.Name.Set.empty;
  param_imports := CU.Name.Set.empty;
  Consistbl.clear crc_units;
  can_load_cmis := Can_load_cmis;
  ()

let clear_missing {persistent_structures; _} =
  let missing_entries =
    Hashtbl.fold
      (fun name r acc -> if r = Missing then name :: acc else acc)
      persistent_structures []
  in
  List.iter (Hashtbl.remove persistent_structures) missing_entries

let add_import {imported_units; _} s =
  imported_units := CU.Name.Set.add s !imported_units

let register_import_as_opaque {imported_opaque_units; _} s =
  imported_opaque_units := CU.Name.Set.add s !imported_opaque_units

let find_info_in_cache {persistent_structures; _} s =
  match Hashtbl.find persistent_structures s with
  | exception Not_found -> None
  | Missing -> None
  | Found (ps, pm) -> Some (ps, pm)

let find_in_cache penv name =
  find_info_in_cache penv name |> Option.map (fun (_ps, pm) -> pm)

let register_parameter_import ({param_imports; _} as penv) import =
  begin match find_info_in_cache penv import with
  | None ->
      (* Not loaded yet; if it's wrong, we'll get an error at load time *)
      ()
  | Some (ps, _) ->
      if not ps.ps_is_param then
        raise (Error (Not_compiled_as_parameter(import, ps.ps_filename)))
  end;
  param_imports := CU.Name.Set.add import !param_imports

let import_crcs penv ~source crcs =
  let {crc_units; _} = penv in
  let import_crc import_info =
    let name = Import_info.Intf.name import_info in
    let info = Import_info.Intf.info import_info in
    match info with
    | None -> ()
    | Some (kind, crc) ->
        add_import penv name;
        Consistbl.check crc_units name kind crc source
  in Array.iter import_crc crcs

let check_consistency penv ps =
  try import_crcs penv ~source:ps.ps_filename ps.ps_crcs
  with Consistbl.Inconsistency {
      unit_name = name;
      inconsistent_source = source;
      original_source = auth;
      inconsistent_data = source_kind;
      original_data = auth_kind;
    } ->
    match source_kind, auth_kind with
    | Normal source_unit, Normal auth_unit
      when not (CU.equal source_unit auth_unit) ->
        error (Inconsistent_package_declaration_between_imports(
            ps.ps_filename, auth_unit, source_unit))
    | (Normal _ | Parameter), _ ->
      error (Inconsistent_import(name, auth, source))

let is_registered_parameter_import {param_imports; _} import =
  CU.Name.Set.mem import !param_imports

let can_load_cmis penv =
  !(penv.can_load_cmis)
let set_can_load_cmis penv setting =
  penv.can_load_cmis := setting

let without_cmis penv f x =
  let log = Lazy_backtrack.log () in
  let res =
    Misc.(protect_refs
            [R (penv.can_load_cmis, Cannot_load_cmis log)]
            (fun () -> f x))
  in
  Lazy_backtrack.backtrack log;
  res

let fold {persistent_structures; _} f x =
  Hashtbl.fold (fun modname pso x -> match pso with
      | Missing -> x
      | Found (_, pm) -> f modname pm x)
    persistent_structures x

(* Reading persistent structures from .cmi files *)

let save_pers_struct penv crc modname impl flags filename =
  let {crc_units; _} = penv in
  List.iter
    (function
        | Rectypes -> ()
        | Alerts _ -> ()
        | Opaque -> register_import_as_opaque penv modname)
    flags;
  Consistbl.check crc_units modname impl crc filename;
  add_import penv modname

let process_pers_struct penv check modname pers_sig =
  let { Persistent_signature.filename; cmi; visibility } = pers_sig in
  let found_name = cmi.cmi_name in
  let kind = cmi.cmi_kind in
  let crcs = cmi.cmi_crcs in
  let flags = cmi.cmi_flags in
  let is_param =
    match kind with
    | Normal _ -> false
    | Parameter -> true
  in
  let ps = { ps_is_param = is_param;
             ps_crcs = crcs;
             ps_filename = filename;
             ps_visibility = visibility;
           } in
  if not (CU.Name.equal modname found_name) then
    error (Illegal_renaming(modname, found_name, filename));
  List.iter
    (function
        | Rectypes ->
            if not !Clflags.recursive_types then
              error (Need_recursive_types(modname))
        | Alerts _ -> ()
        | Opaque -> register_import_as_opaque penv modname)
    flags;
  if check then check_consistency penv ps;
  begin match kind, CU.get_current () with
  | Normal { cmi_impl = imported_unit }, Some current_unit ->
      let access_allowed =
        CU.can_access_by_name imported_unit ~accessed_by:current_unit
      in
      if not access_allowed then
        let prefix = CU.for_pack_prefix current_unit in
        error (Direct_reference_from_wrong_package (imported_unit, filename, prefix));
  | _, _ -> ()
  end;
  begin match is_param, is_registered_parameter_import penv modname with
  | true, false ->
      begin match CU.get_current () with
      | Some current_unit when CU.Name.equal modname (CU.name current_unit) ->
          error (Cannot_implement_parameter (modname, filename))
      | _ ->
          error (Illegal_import_of_parameter(modname, filename))
      end
  | false, true ->
      error (Not_compiled_as_parameter(modname, filename))
  | true, true
  | false, false -> ()
  end;
  ps

let bind_pers_struct penv modname ps pm =
  let {persistent_structures; _} = penv in
  Hashtbl.add persistent_structures modname (Found (ps, pm))

let acknowledge_pers_struct penv check modname pers_sig pm =
  let ps = process_pers_struct penv check modname pers_sig in
  bind_pers_struct penv modname ps pm;
  ps

let read_pers_struct penv val_of_pers_sig check modname filename ~add_binding =
  add_import penv modname;
  let cmi = read_cmi_lazy filename in
  let pers_sig = { Persistent_signature.filename; cmi; visibility = Visible } in
  let pm = val_of_pers_sig pers_sig in
  let ps = process_pers_struct penv check modname pers_sig in
  if add_binding then bind_pers_struct penv modname ps pm;
  (ps, pm)

let find_pers_struct ~allow_hidden penv val_of_pers_sig check name =
  let {persistent_structures; _} = penv in
  if CU.Name.equal name CU.Name.predef_exn then raise Not_found;
  match Hashtbl.find persistent_structures name with
  | Found (ps, pm) when allow_hidden || ps.ps_visibility = Load_path.Visible ->
    (ps, pm)
  | Found _ -> raise Not_found
  | Missing -> raise Not_found
  | exception Not_found ->
    match can_load_cmis penv with
    | Cannot_load_cmis _ -> raise Not_found
    | Can_load_cmis ->
        let psig =
          match !Persistent_signature.load ~allow_hidden ~unit_name:name with
          | Some psig -> psig
          | None ->
            if allow_hidden then Hashtbl.add persistent_structures name Missing;
            raise Not_found
        in
        add_import penv name;
        let pm = val_of_pers_sig psig in
        let ps = acknowledge_pers_struct penv check name psig pm in
        (ps, pm)

let describe_prefix ppf prefix =
  if CU.Prefix.is_empty prefix then
    Format.fprintf ppf "outside of any package"
  else
    Format.fprintf ppf "package %a" CU.Prefix.print prefix

(* Emits a warning if there is no valid cmi for name *)
let check_pers_struct ~allow_hidden penv f ~loc name =
  let name_as_string = CU.Name.to_string name in
  try
    ignore (find_pers_struct ~allow_hidden penv f false name)
  with
  | Not_found ->
      let warn = Warnings.No_cmi_file(name_as_string, None) in
        Location.prerr_warning loc warn
  | Cmi_format.Error err ->
      let msg = Format.asprintf "%a" Cmi_format.report_error err in
      let warn = Warnings.No_cmi_file(name_as_string, Some msg) in
        Location.prerr_warning loc warn
  | Error err ->
      let msg =
        match err with
        | Illegal_renaming(name, ps_name, filename) ->
            Format.asprintf
              " %a@ contains the compiled interface for @ \
               %a when %a was expected"
              Location.print_filename filename
              CU.Name.print ps_name
              CU.Name.print name
        | Inconsistent_import _ -> assert false
        | Need_recursive_types name ->
            Format.asprintf
              "%a uses recursive types"
              CU.Name.print name
        | Inconsistent_package_declaration_between_imports _ -> assert false
        | Direct_reference_from_wrong_package (unit, _filename, prefix) ->
            Format.asprintf "%a is inaccessible from %a"
              CU.print unit
              describe_prefix prefix
        | Illegal_import_of_parameter _ -> assert false
        | Not_compiled_as_parameter _ -> assert false
        | Cannot_implement_parameter _ -> assert false
      in
      let warn = Warnings.No_cmi_file(name_as_string, Some msg) in
        Location.prerr_warning loc warn

let read penv f modname filename ~add_binding =
  snd (read_pers_struct penv f true modname filename ~add_binding)

let find ~allow_hidden penv f name =
  snd (find_pers_struct ~allow_hidden penv f true name)

let check ~allow_hidden penv f ~loc name =
  let {persistent_structures; _} = penv in
  if not (Hashtbl.mem persistent_structures name) then begin
    (* PR#6843: record the weak dependency ([add_import]) regardless of
       whether the check succeeds, to help make builds more
       deterministic. *)
    add_import penv name;
    if (Warnings.is_active (Warnings.No_cmi_file("", None))) then
      !add_delayed_check_forward
        (fun () -> check_pers_struct ~allow_hidden penv f ~loc name)
  end

(* CR mshinwell: delete this having moved to 4.14 build compilers *)
module Array = struct
  include Array

  (* From stdlib/array.ml *)
  let find_opt p a =
    let n = Array.length a in
    let rec loop i =
      if i = n then None
      else
        let x = Array.unsafe_get a i in
        if p x then Some x
        else loop (succ i)
    in
    loop 0
end

let crc_of_unit penv f name =
  match Consistbl.find penv.crc_units name with
  | Some (_, crc) -> crc
  | None ->
    let (ps, _pm) = find_pers_struct ~allow_hidden:true penv f true name in
    match Array.find_opt (Import_info.Intf.has_name ~name) ps.ps_crcs with
    | None -> assert false
    | Some import_info ->
      match Import_info.Intf.crc import_info with
      | None -> assert false
      | Some crc -> crc

let imports {imported_units; crc_units; _} =
  let imports =
    Consistbl.extract (CU.Name.Set.elements !imported_units)
      crc_units
  in
  List.map (fun (cu_name, spec) -> Import_info.Intf.create cu_name spec)
    imports

let looked_up {persistent_structures; _} modname =
  Hashtbl.mem persistent_structures modname

let is_imported {imported_units; _} s =
  CU.Name.Set.mem s !imported_units

let is_imported_opaque {imported_opaque_units; _} s =
  CU.Name.Set.mem s !imported_opaque_units

let make_cmi penv modname kind sign alerts =
  let flags =
    List.concat [
      if !Clflags.recursive_types then [Cmi_format.Rectypes] else [];
      if !Clflags.opaque then [Cmi_format.Opaque] else [];
      [Alerts alerts];
    ]
  in
  let crcs = imports penv in
  {
    cmi_name = modname;
    cmi_kind = kind;
    cmi_sign = sign;
    cmi_crcs = Array.of_list crcs;
    cmi_flags = flags
  }

let save_cmi penv psig =
  let { Persistent_signature.filename; cmi; _ } = psig in
  Misc.try_finally (fun () ->
      let {
        cmi_name = modname;
        cmi_kind = kind;
        cmi_sign = _;
        cmi_crcs = _;
        cmi_flags = flags;
      } = cmi in
      let crc =
        output_to_file_via_temporary (* see MPR#7472, MPR#4991 *)
          ~mode: [Open_binary] filename
          (fun temp_filename oc -> output_cmi temp_filename oc cmi) in
      (* Enter signature in consistbl so that imports()
         will also return its crc *)
      let data : Import_info.Intf.Nonalias.Kind.t =
        match kind with
        | Normal { cmi_impl } -> Normal cmi_impl
        | Parameter -> Parameter
      in
      save_pers_struct penv crc modname data flags filename
    )
    ~exceptionally:(fun () -> remove_file filename)

let report_error ppf =
  let open Format in
  function
  | Illegal_renaming(modname, ps_name, filename) -> fprintf ppf
      "Wrong file naming: %a@ contains the compiled interface for@ \
       %a when %a was expected"
      Location.print_filename filename
      CU.Name.print ps_name
      CU.Name.print modname
  | Inconsistent_import(name, source1, source2) -> fprintf ppf
      "@[<hov>The files %a@ and %a@ \
              make inconsistent assumptions@ over interface %a@]"
      Location.print_filename source1 Location.print_filename source2
      CU.Name.print name
  | Need_recursive_types(import) ->
      fprintf ppf
        "@[<hov>Invalid import of %a, which uses recursive types.@ %s@]"
        CU.Name.print import
        "The compilation flag -rectypes is required"
  | Inconsistent_package_declaration_between_imports (filename, unit1, unit2) ->
      fprintf ppf
        "@[<hov>The file %s@ is imported both as %a@ and as %a.@]"
        filename
        CU.print unit1
        CU.print unit2
  | Illegal_import_of_parameter(modname, filename) ->
      fprintf ppf
        "@[<hov>The file %a@ contains the interface of a parameter.@ \
         %a is not declared as a parameter for the current unit (-parameter %a).@]"
        Location.print_filename filename
        CU.Name.print modname
        CU.Name.print modname
  | Not_compiled_as_parameter(modname, filename) ->
      fprintf ppf
        "@[<hov>The module %a@ is specified as a parameter, but %a@ \
         was not compiled with -as-parameter.@]"
        CU.Name.print modname
        Location.print_filename filename
  | Direct_reference_from_wrong_package(unit, filename, prefix) ->
      fprintf ppf
        "@[<hov>Invalid reference to %a (in file %s) from %a.@ %s]"
        CU.print unit
        filename
        describe_prefix prefix
        "Can only access members of this library's package or a containing package"
  | Cannot_implement_parameter(modname, _filename) ->
      fprintf ppf
        "@[<hov>The interface for %a@ was compiled with -as-parameter.@ \
         It cannot be implemented directly.@]"
        CU.Name.print modname

let () =
  Location.register_error_of_exn
    (function
      | Error err ->
          Some (Location.error_of_printer_file report_error err)
      | _ -> None
    )
