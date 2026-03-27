(** This file actually runs in the converter directory (parent) but the
    generated rules run in the expect directory*)

(** Expects [arm/um/test.*.toml]*)
let generate_rules file =
  (* Dune doesn't support generating files in subdirectory, or importing
     subdirectory stanza with dynamic_include so we have to flatten the
     directory structure*)
  let flat = file |> String.split_on_char '/' |> String.concat "_" in
  Printf.printf
    {|
(rule
 (deps ../../%s)
 (targets %s)
 (action
  (run archsem convert %%{deps} -o %%{targets})))

(rule
 (alias runtest)
 (action
  (diff %s %s)))
|}
     file flat file flat

let gen_for_dir dir =
  if Sys.is_directory (Filename.concat ".." dir) then
    Sys.readdir (Filename.concat "../" dir)
    |> Array.to_list |> List.sort String.compare
    |> List.map (fun s -> Filename.concat dir s)
    |> List.filter (fun s -> Filename.check_suffix s ".toml")
    |> List.iter generate_rules

let gen_for_arch arch =
  Sys.readdir ("../" ^ arch)
  |> Array.to_list |> List.sort String.compare
  |> List.map (fun s -> Filename.concat arch s)
  |> List.iter gen_for_dir

let () = gen_for_arch "arm"; gen_for_arch "x86"
