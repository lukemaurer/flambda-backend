(* TEST (* Just a test-driver *)
   * skip
   reason = "Broken, ask mshinwell if you want to try to fix it"
*)
(*
   * native-compiler
   ** script
       script = "sh ${test_source_directory}/has-afl-fuzz.sh"
       readonly_files = "readline.ml"
   *** setup-ocamlopt.byte-build-env
   **** ocamlopt.byte
         program = "${test_build_directory}/readline"
         flags = "-afl-instrument"
         all_modules = "readline.ml"
   ***** run
*)
