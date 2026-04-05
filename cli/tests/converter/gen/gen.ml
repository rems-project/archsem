(** Expects [arm/um/test.*.toml]*)
let generate_rules file =
  let dir = Filename.dirname file in
  let base = Filename.basename file in
  Printf.printf
    {|
(subdir %s
 (rule
  (deps ../../../%s)
  (targets %s)
  (action
   (run archsem convert %%{deps} -o %%{targets}))))

(rule
 (alias runtest)
 (action
  (diff expect/%s %s)))

|}
    dir file base file file

let gen_for_dir dir =
  if Sys.is_directory (Filename.concat ".." dir) then
    Sys.readdir (Filename.concat "../" dir)
    |> Array.to_list |> List.sort String.compare
    |> List.map (fun s -> Filename.concat dir s)
    |> List.iter generate_rules

let gen_for_arch arch =
  Sys.readdir ("../" ^ arch)
  |> Array.to_list |> List.sort String.compare
  |> List.map (fun s -> Filename.concat arch s)
  |> List.iter gen_for_dir

let () = gen_for_arch "arm"; gen_for_arch "x86"
