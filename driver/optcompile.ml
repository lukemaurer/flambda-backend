(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*                                                                        *)
(*   Copyright 2002 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(** The batch compiler *)

open Misc
open Compile_common

let tool_name = "ocamlopt"

let with_info = Compile_common.with_info ~native:true ~tool_name

let interface ~source_file ~output_prefix =
  with_info ~source_file ~output_prefix ~dump_ext:"cmi"
    ~compilation_unit:Inferred_from_output_prefix
  @@ fun info ->
  Compile_common.interface
  ~hook_parse_tree:(Compiler_hooks.execute Compiler_hooks.Parse_tree_intf)
  ~hook_typed_tree:(Compiler_hooks.execute Compiler_hooks.Typed_tree_intf)
    info

(** Native compilation backend for .ml files. *)

let compile_from_raw_lambda i raw_lambda ~unix ~pipeline =
  raw_lambda
  |> print_if i.ppf_dump Clflags.dump_rawlambda Printlambda.program
  |> Compiler_hooks.execute_and_pipe Compiler_hooks.Raw_lambda
  |> Profile.(record generate)
   (fun program ->
      let code = Simplif.simplify_lambda program.Lambda.code in
      { program with Lambda.code }
      |> print_if i.ppf_dump Clflags.dump_lambda Printlambda.program
      |> Compiler_hooks.execute_and_pipe Compiler_hooks.Lambda
      |> (fun program ->
           Asmgen.compile_implementation
             unix
             ~pipeline
             ~filename:i.source_file
             ~prefixname:i.output_prefix
             ~ppf_dump:i.ppf_dump
             program);
           Compilenv.save_unit_info (cmx i))

let compile_from_typed i typed ~transl_style ~unix ~pipeline =
  typed
  |> Profile.(record transl)
    (Translmod.transl_implementation i.module_name ~style:transl_style)
  |> compile_from_raw_lambda i ~unix ~pipeline

type flambda2 =
  ppf_dump:Format.formatter ->
  prefixname:string ->
  filename:string ->
  keep_symbol_tables:bool ->
  Lambda.program ->
  Cmm.phrase list

(* Emit assembly directly from Linear IR *)
let emit unix i =
  Compilenv.reset i.module_name;
  Asmgen.compile_implementation_linear unix
    i.output_prefix ~progname:i.source_file

type starting_point = Parsing | Emit | Instantiation

let starting_point_of_compiler_pass start_from  =
  match (start_from:Clflags.Compiler_pass.t) with
  | Parsing -> Parsing
  | Emit -> Emit
  | _ -> Misc.fatal_errorf "Cannot start from %s"
           (Clflags.Compiler_pass.to_string start_from)

let implementation0 unix ~backend ~(flambda2 : flambda2) ~start_from
      ~source_file ~output_prefix ~keep_symbol_tables
      ~(compilation_unit : Compile_common.compilation_unit_or_inferred) =
  let transl_style : Translmod.compilation_unit_style =
    if Config.flambda || Config.flambda2 then Plain_block
    else Set_individual_fields
  in
  let pipeline : Asmgen.pipeline =
    if Config.flambda2 then Direct_to_cmm (flambda2 ~keep_symbol_tables)
    else
      let middle_end =
        if Config.flambda then Flambda_middle_end.lambda_to_clambda
        else Closure_middle_end.lambda_to_clambda
      in
      Via_clambda { middle_end; backend; }
  in
  let backend info ({ structure; coercion; secondary_iface; _ }
                    : Typedtree.implementation) =
    Compilenv.reset info.module_name;
    let secondary_coercion =
      match secondary_iface with
      | Some { si_coercion_from_primary; si_signature = _ } ->
        Some si_coercion_from_primary
      | None -> None
    in
    let typed = structure, coercion, secondary_coercion in
    let transl_style : Translmod.compilation_unit_style =
      if Config.flambda || Config.flambda2 then Plain_block
      else Set_individual_fields
    in
    let pipeline : Asmgen.pipeline =
      if Config.flambda2 then Direct_to_cmm (flambda2 ~keep_symbol_tables)
      else
        let middle_end =
          if Config.flambda then Flambda_middle_end.lambda_to_clambda
          else Closure_middle_end.lambda_to_clambda
        in
        Via_clambda { middle_end; backend; }
    in
    if not (Config.flambda || Config.flambda2) then Clflags.set_oclassic ();
    compile_from_typed info typed ~unix ~transl_style ~pipeline
  in
  with_info ~source_file ~output_prefix ~dump_ext:"cmx" ~compilation_unit
  @@ fun info ->
  if !Flambda_backend_flags.internal_assembler then
      Emitaux.binary_backend_available := true;
  match start_from with
  | Parsing ->
    Compile_common.implementation
      ~hook_parse_tree:(Compiler_hooks.execute Compiler_hooks.Parse_tree_impl)
      ~hook_typed_tree:(fun (impl : Typedtree.implementation) ->
        Compiler_hooks.execute Compiler_hooks.Typed_tree_impl impl)
      info ~backend
  | Emit -> emit unix info ~ppf_dump:info.ppf_dump
  | Instantiation ->
    Compilenv.reset info.module_name;
    (* Consider the names of arguments to be parameters for the purposes of the
       subset rule - that is, a module we import can refer to our arguments as
       parameters. However, set [exported] to false because they're not
       parameters of _this_ module, that is, the instance we're generating. *)
    List.iter
      (fun (param, _value) -> Env.register_parameter param ~exported:false)
      (Compilation_unit.instance_arguments info.module_name);
    let cmx_info, _ = Compilenv.read_unit_info info.source_file in
    let runtime_params = cmx_info.ui_runtime_params in
    let impl =
      Translmod.transl_instance info.module_name ~runtime_params
        ~style:transl_style
    in
    if not (Config.flambda || Config.flambda2) then Clflags.set_oclassic ();
    compile_from_raw_lambda info impl ~unix ~pipeline

let implementation unix ~backend ~flambda2 ~start_from ~source_file
      ~output_prefix ~keep_symbol_tables =
  let start_from = start_from |> starting_point_of_compiler_pass in
  implementation0 unix ~backend ~flambda2 ~start_from ~source_file
    ~output_prefix ~keep_symbol_tables
    ~compilation_unit:Inferred_from_output_prefix

let instance unix ~backend ~flambda2 ~source_file
      ~output_prefix ~compilation_unit ~keep_symbol_tables =
  let start_from = Instantiation in
  implementation0 unix ~backend ~flambda2 ~start_from ~source_file
    ~output_prefix ~keep_symbol_tables
    ~compilation_unit:(Exactly compilation_unit)
