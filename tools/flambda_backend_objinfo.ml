(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*         Mehdi Dogguy, PPS laboratory, University Paris Diderot         *)
(*                                                                        *)
(*   Copyright 1996 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*   Copyright 2010 Mehdi Dogguy                                          *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* CR-someday lmaurer: This file should do no parsing or low-level binary I/O
   _whatsoever_. No magic numbers, no sections, and _especially_ no
   [input_value]. Any such code here is necessarily duplicated code, and worse,
   particularly fiddly duplicated code that segfaults rather than producing
   compile-time errors. *)

(* Dump info on .cmi, .cmo, .cmx, .cma, .cmxa, .cmxs files and on bytecode
   executables. *)

open Printf
open Misc
open Cmo_format

(* Command line options to prevent printing approximation, function code and
   CRC *)
let no_approx = ref false

let no_code = ref false

let no_crc = ref false

module Magic_number = Misc.Magic_number
module String = Misc.Stdlib.String

let input_stringlist ic len =
  let get_string_list sect len =
    let rec fold s e acc =
      if e != len
      then
        if sect.[e] = '\000'
        then fold (e + 1) (e + 1) (String.sub sect s (e - s) :: acc)
        else fold s (e + 1) acc
      else acc
    in
    fold 0 0 []
  in
  let sect = really_input_string ic len in
  get_string_list sect len

let dummy_crc = String.make 32 '-'

let null_crc = String.make 32 '0'

let string_of_crc crc = if !no_crc then null_crc else Digest.to_hex crc

let print_name_crc name crco =
  let crc =
    match crco with None -> dummy_crc | Some crc -> string_of_crc crc
  in
  printf "\t%s\t%a\n" crc Compilation_unit.Name.output name

(* CR-someday mshinwell: consider moving to [Import_info.print] *)

let print_intf_import import =
  let name = Import_info.name import in
  let crco = Import_info.crc import in
  print_name_crc name crco

let print_impl_import import =
  let name = Import_info.name import in
  let crco = Import_info.crc import in
  print_name_crc name crco

let print_global_name_binding global =
  printf "\t%a\n" Global.output global

let print_line name = printf "\t%s\n" name

let print_global_line glob =
  printf "\t%a\n" Global.Name.output glob

let print_global_as_name_line glob =
  printf "\t%a\n" Global.Name.output (Global.to_name glob)

let print_name_line cu =
  (* Drop the pack prefix for backward compatibility, but keep the instance
     arguments *)
  let cu_without_prefix =
    Compilation_unit.with_for_pack_prefix cu Compilation_unit.Prefix.empty
  in
  printf "\t%a\n" Compilation_unit.output cu_without_prefix

let print_required_global id = printf "\t%a\n" Compilation_unit.output id

let print_cmo_infos cu =
  printf "Unit name: %a\n" Compilation_unit.output cu.cu_name;
  print_string "Interfaces imported:\n";
  Array.iter print_intf_import cu.cu_imports;
  let () =
   match cu.cu_runtime_params with
   | [||] -> ()
   | params ->
     print_string "Runtime parameters:\n";
     Array.iter print_global_as_name_line params
  in
  print_string "Required globals:\n";
  List.iter print_required_global cu.cu_required_globals;
  printf "Uses unsafe features: ";
  (match cu.cu_primitives with
  | [] -> printf "no\n"
  | l ->
    printf "YES\n";
    printf "Primitives declared in this module:\n";
    List.iter print_line l);
  printf "Force link: %s\n" (if cu.cu_force_link then "YES" else "no")

let print_spaced_string s = printf " %s" s

let print_cma_infos (lib : Cmo_format.library) =
  printf "Force custom: %s\n" (if lib.lib_custom then "YES" else "no");
  printf "Extra C object files:";
  (* PR#4949: print in linking order *)
  List.iter print_spaced_string (List.rev lib.lib_ccobjs);
  printf "\nExtra C options:";
  List.iter print_spaced_string (List.rev lib.lib_ccopts);
  printf "\n";
  print_string "Extra dynamically-loaded libraries:";
  List.iter print_spaced_string (List.rev lib.lib_dllibs);
  printf "\n";
  List.iter print_cmo_infos lib.lib_units

let print_cmi_infos name crcs kind params global_name_bindings =
  let open Cmi_format in
  printf "Unit name: %a\n" Compilation_unit.Name.output name;
  let is_param =
    match kind with
    | Normal _ -> false
    | Parameter -> true
  in
  printf "Is parameter: %s\n" (if is_param then "YES" else "no");
  print_string "Parameters:\n";
  List.iter print_global_as_name_line params;
  begin
    match kind with
    | Normal { cmi_arg_for = Some arg_for; _ } ->
      printf "Argument for parameter:\n";
      print_global_line arg_for
    | Normal _ | Parameter ->
      ()
  end;
  printf "Interfaces imported:\n";
  Array.iter print_intf_import crcs;
  printf "Globals in scope:\n";
  Array.iter print_global_name_binding global_name_bindings

let print_cmt_infos cmt =
  let open Cmt_format in
  printf "Cmt unit name: %a\n" Compilation_unit.output cmt.cmt_modname;
  print_string "Cmt interfaces imported:\n";
  Array.iter print_intf_import cmt.cmt_imports;
  printf "Source file: %s\n"
    (match cmt.cmt_sourcefile with None -> "(none)" | Some f -> f);
  printf "Compilation flags:";
  Array.iter print_spaced_string cmt.cmt_args;
  printf "\nLoad path:";
  List.iter print_spaced_string cmt.cmt_loadpath;
  printf "\n";
  printf "cmt interface digest: %s\n"
    (match cmt.cmt_interface_digest with
    | None -> ""
    | Some crc -> string_of_crc crc)

let print_cms_infos cms =
  let open Cms_format in
  printf "Cms unit name: %a\n" Compilation_unit.output cms.cms_modname;
  printf "Source file: %s\n"
    (match cms.cms_sourcefile with None -> "(none)" | Some f -> f)

let print_general_infos print_name name crc defines implements_param
    runtime_params iter_cmi iter_cmx =
  printf "Name: %a\n" print_name name;
  printf "CRC of implementation: %s\n" (string_of_crc crc);
  printf "Globals defined:\n";
  List.iter print_name_line defines;
  let () =
    match implements_param with
    | None -> ()
    | Some arg_type ->
      printf "Parameter implemented: %a\n" Global.Name.output arg_type
  in
  printf "Interfaces imported:\n";
  iter_cmi print_intf_import;
  printf "Implementations imported:\n";
  iter_cmx print_impl_import;
  let () =
    match runtime_params with
    | [||] -> ()
    | _ ->
      printf "Runtime parameters:\n";
      Array.iter print_global_as_name_line runtime_params
  in
  ()

let print_global_table table =
  printf "Globals defined:\n";
  Symtable.iter_global_map (fun id _ -> print_line (Ident.name id)) table

open Cmx_format
open Cmxs_format

let unique_arity_identifier arity =
  if List.for_all (function [|Cmm.Val|] -> true | _ -> false) arity then
    Int.to_string (List.length arity)
  else
    String.concat "_" (List.map Cmm_helpers.machtype_identifier arity)

let return_arity_identifier t =
  match t with
  | [|Cmm.Val|] -> ""
  | _ -> "_R" ^ Cmm_helpers.machtype_identifier t

let print_generic_fns gfns =
  let pr_afuns _ fns =
    let mode = function Lambda.Alloc_heap -> "" | Lambda.Alloc_local -> "L" in
    List.iter (fun (arity,result,m) ->
        printf " %s%s%s"
          (unique_arity_identifier arity)
          (return_arity_identifier result)
          (mode m)) fns in
  let pr_cfuns _ fns =
    List.iter (function
      | (Lambda.Curried {nlocal}, arity, result) ->
        printf " %s%sL%d"
          (unique_arity_identifier arity)
          (return_arity_identifier result)
          nlocal
      | (Lambda.Tupled, arity, result) ->
        printf " -%s%s"
          (unique_arity_identifier arity)
          (return_arity_identifier result)) fns in
  printf "Currying functions:%a\n" pr_cfuns gfns.curry_fun;
  printf "Apply functions:%a\n" pr_afuns gfns.apply_fun;
  printf "Send functions:%a\n" pr_afuns gfns.send_fun

let print_cmx_infos (uir, sections, crc) =
  print_general_infos Compilation_unit.output uir.uir_unit crc uir.uir_defines
    uir.uir_implements_param uir.uir_runtime_params
    (fun f -> Array.iter f uir.uir_imports_cmi)
    (fun f -> Array.iter f uir.uir_imports_cmx);
  begin
    match uir.uir_export_info with
    | Clambda_raw approx ->
      if not !no_approx
      then begin
        printf "Clambda approximation:\n";
        Format.fprintf Format.std_formatter "  %a@." Printclambda.approx approx
      end
      else Format.printf "Clambda unit@."
    | Flambda1_raw export ->
      if (not !no_approx) || not !no_code
      then printf "Flambda export information:\n"
      else printf "Flambda unit\n";
      if not !no_approx
      then begin
        Compilation_unit.set_current (Some uir.uir_unit);
        let root_symbols =
          List.map Symbol.for_compilation_unit uir.uir_defines
        in
        Format.printf "approximations@ %a@.@." Export_info.print_approx
          (export, root_symbols)
      end;
      if not !no_code
      then Format.printf "functions@ %a@.@." Export_info.print_functions export
    | Flambda2_raw None ->
      printf "Flambda 2 unit (with no export information)\n"
    | Flambda2_raw (Some cmx) ->
      printf "Flambda 2 export information:\n";
      flush stdout;
      let cmx = Flambda2_cmx.Flambda_cmx_format.from_raw cmx ~sections in
      Format.printf "%a\n%!" Flambda2_cmx.Flambda_cmx_format.print cmx
  end;
  print_generic_fns uir.uir_generic_fns;
  printf "Force link: %s\n" (if uir.uir_force_link then "YES" else "no");
  Checks.Raw.print uir.uir_checks

let print_cmxa_infos (lib : Cmx_format.library_infos) =
  printf "Extra C object files:";
  List.iter print_spaced_string (List.rev lib.lib_ccobjs);
  printf "\nExtra C options:";
  List.iter print_spaced_string (List.rev lib.lib_ccopts);
  printf "\n";
  print_generic_fns lib.lib_generic_fns;
  let module B = Misc.Bitmap in
  lib.lib_units
  |> List.iter (fun u ->
         print_general_infos Compilation_unit.output u.li_name u.li_crc
           u.li_defines None [||]
           (fun f ->
             B.iter (fun i -> f lib.lib_imports_cmi.(i)) u.li_imports_cmi)
           (fun f ->
             B.iter (fun i -> f lib.lib_imports_cmx.(i)) u.li_imports_cmx);
         printf "Force link: %s\n" (if u.li_force_link then "YES" else "no"))

let print_cmxs_infos header =
  List.iter
    (fun ui ->
      print_general_infos Compilation_unit.output ui.dynu_name ui.dynu_crc
        ui.dynu_defines None [||]
        (fun f -> Array.iter f ui.dynu_imports_cmi)
        (fun f -> Array.iter f ui.dynu_imports_cmx))
    header.dynu_units

let p_title title = printf "%s:\n" title

let p_list title print = function
  | [] -> ()
  | l ->
    p_title title;
    List.iter print l

let dump_byte ic =
  Bytesections.read_toc ic;
  let toc = Bytesections.toc () in
  let toc = List.sort Stdlib.compare toc in
  List.iter
    (fun (section, _) ->
      try
        let len = Bytesections.seek_section ic section in
        if len > 0
        then
          match section with
          | "CRCS" ->
            p_list "Imported units" print_intf_import
              ((input_value ic : Import_info.t array) |> Array.to_list)
          | "DLLS" -> p_list "Used DLLs" print_line (input_stringlist ic len)
          | "DLPT" ->
            p_list "Additional DLL paths" print_line (input_stringlist ic len)
          | "PRIM" ->
            p_list "Primitives used" print_line (input_stringlist ic len)
          | "SYMB" -> print_global_table (input_value ic)
          | _ -> ()
      with _ -> ())
    toc

let find_dyn_offset filename =
  match Binutils.read filename with
  | Ok t -> Binutils.symbol_offset t "caml_plugin_header"
  | Error _ -> None

let exit_err msg =
  print_endline msg;
  exit 2

let exit_errf fmt = Printf.ksprintf exit_err fmt

let exit_magic_msg msg =
  exit_errf
    "Wrong magic number:\n\
     this tool only supports object files produced by compiler version\n\
     \t%s\n\
     %s"
    Sys.ocaml_version msg

let exit_magic_error ~expected_kind err =
  exit_magic_msg
    Magic_number.(
      match err with
      | Parse_error err -> explain_parse_error expected_kind err
      | Unexpected_error err -> explain_unexpected_error err)

(* assume that 'ic' is already positioned at the right place depending on the
   format (usually right after the magic number, but Exec and Cmxs differ) *)
let dump_obj_by_kind filename ic obj_kind =
  let open Magic_number in
  match obj_kind with
  | Cmo ->
    let cu_pos = input_binary_int ic in
    seek_in ic cu_pos;
    let cu = input_value ic in
    close_in ic;
    print_cmo_infos cu
  | Cma ->
    let toc_pos = input_binary_int ic in
    seek_in ic toc_pos;
    let toc = (input_value ic : library) in
    close_in ic;
    print_cma_infos toc
  | Cmi | Cmt ->
    close_in ic;
    let cmi, cmt = Cmt_format.read filename in
    begin
      match cmi with
      | None -> ()
      | Some cmi ->
        print_cmi_infos cmi.Cmi_format.cmi_name cmi.Cmi_format.cmi_crcs
          cmi.Cmi_format.cmi_kind cmi.Cmi_format.cmi_params
          cmi.Cmi_format.cmi_globals
    end;
    begin
      match cmt with None -> () | Some cmt -> print_cmt_infos cmt
    end
  | Cms ->
    close_in ic;
    let cms = Cms_format.read filename in
    print_cms_infos cms
  | Cmx _config ->
    let uir = (input_value ic : unit_infos_raw) in
    let first_section_offset = pos_in ic in
    seek_in ic (first_section_offset + uir.uir_sections_length);
    let crc = Digest.input ic in
    (* This consumes ic *)
    let sections = Flambda_backend_utils.File_sections.create
        uir.uir_section_toc filename ic ~first_section_offset in
    print_cmx_infos (uir, sections, crc)
  | Cmxa _config ->
    let li = (input_value ic : library_infos) in
    close_in ic;
    print_cmxa_infos li
  | Exec ->
    (* no assumptions on [ic] position, [dump_byte] will seek at the right
       place *)
    dump_byte ic;
    close_in ic
  | Cmxs ->
    (* we assume we are at the offset of the dynamic information, as returned by
       [find_dyn_offset]. *)
    let header = (input_value ic : dynheader) in
    close_in ic;
    print_cmxs_infos header
  | Ast_impl | Ast_intf ->
    exit_errf "The object file type %S is currently unsupported by this tool."
      (human_name_of_kind obj_kind)

let dump_obj filename =
  let open Magic_number in
  let dump_standard ic =
    match read_current_info ~expected_kind:None ic with
    | Error (Unexpected_error _ as err) ->
      exit_magic_error ~expected_kind:None err
    | Ok { kind; version = _ } ->
      dump_obj_by_kind filename ic kind;
      Ok ()
    | Error (Parse_error head_error) -> Error head_error
  and dump_exec ic =
    let pos_trailer = in_channel_length ic - Magic_number.magic_length in
    let _ = seek_in ic pos_trailer in
    let expected_kind = Some Exec in
    match read_current_info ~expected_kind ic with
    | Error (Unexpected_error _ as err) -> exit_magic_error ~expected_kind err
    | Ok _ ->
      dump_obj_by_kind filename ic Exec;
      Ok ()
    | Error (Parse_error _) -> Error ()
  and dump_cmxs ic =
    flush stdout;
    match find_dyn_offset filename with
    | None ->
      exit_errf "Unable to read info on %s %s." (human_name_of_kind Cmxs)
        filename
    | Some offset -> (
      LargeFile.seek_in ic offset;
      let header = (input_value ic : dynheader) in
      let expected_kind = Some Cmxs in
      match parse header.dynu_magic with
      | Error err -> exit_magic_error ~expected_kind (Parse_error err)
      | Ok info -> (
        match check_current Cmxs info with
        | Error err -> exit_magic_error ~expected_kind (Unexpected_error err)
        | Ok () ->
          LargeFile.seek_in ic offset;
          dump_obj_by_kind filename ic Cmxs;
          ()))
  in
  printf "File %s\n" filename;
  let ic = open_in_bin filename in
  match dump_standard ic with
  | Ok () -> ()
  | Error head_error -> (
    match dump_exec ic with
    | Ok () -> ()
    | Error () ->
      if Filename.check_suffix filename ".cmxs"
      then dump_cmxs ic
      else exit_magic_error ~expected_kind:None (Parse_error head_error))

let arg_list =
  [ ( "-no-approx",
      Arg.Set no_approx,
      " Do not print module approximation information" );
    ( "-no-code",
      Arg.Set no_code,
      " Do not print code from exported flambda functions" );
    "-null-crc", Arg.Set no_crc, " Print a null CRC for imported interfaces";
    ( "-args",
      Arg.Expand Arg.read_arg,
      "<file> Read additional newline separated command line arguments \n\
      \      from <file>" );
    ( "-args0",
      Arg.Expand Arg.read_arg0,
      "<file> Read additional NUL separated command line arguments from \n\
      \      <file>" ) ]

let arg_usage =
  Printf.sprintf "%s [OPTIONS] FILES : give information on files" Sys.argv.(0)

let main () =
  Arg.parse_expand arg_list dump_obj arg_usage;
  exit 0

let _ = main ()
