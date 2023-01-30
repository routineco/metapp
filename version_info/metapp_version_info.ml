let () = Findlib.init ()
let ppxlib_version_string = Findlib.package_property [] "ppxlib" "version"
let ppxlib_version =
  match String.split_on_char '.' ppxlib_version_string with
  | major::minor::patch::[] ->
      ((int_of_string major), (int_of_string minor), (int_of_string patch))
  | _ -> assert false
let ast_version =
  match ppxlib_version with
  | (0, (22 | 23 | 24 | 25), _) -> (4, 12)
  | _ -> (4, 14)
