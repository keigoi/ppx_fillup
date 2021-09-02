
let error = Util.error

let is_typeclass decl =
  match Util.typedecl_attr decl "typeclass" with
  | [] -> false
  | _::_ -> true

let check_is_typeclass env loc (typ : Types.type_expr) = 
  let typ = Util.expand_type env typ in
  let _, decl, decls = Util.type_head_decls loc env typ in
  if List.exists is_typeclass (decl::decls) then 
    ()
  else 
    error loc (Format.asprintf "Not a typeclass:%a" Ocaml_common.Printtyp.type_expr typ)

let is_instance vdescr =
  List.exists (fun attr -> attr.Parsetree.attr_name.txt="instance") vdescr.Types.val_attributes

type instance =
  {base:Ident.t; args:unit list}
  
let rec make_instance env ty ident inst_ty =
  match (Ctype.repr @@ Ctype.expand_head env inst_ty) with
  | {Types.desc=Types.Tarrow(_lab, arg, ret, _com);_} -> 
    check_is_typeclass env Location.none arg;
    let rest = make_instance env ty ident ret in
    {rest with args= ()::rest.args}
  | _ ->
    if Ctype.matches env ty inst_ty then
      {base=ident; args=[]}
    else
      raise Not_found

let try_make_instance env ty ident descr =
  if not @@ is_instance descr then
    None
  else
    try
      Some (make_instance env ty ident descr.val_type)
    with
      Not_found ->
        None

let print_tab lvl =
  for _i = 0 to lvl do
    print_string "  "
  done

let resolve_instances ty env =
  let rec find_instances lvl = function
  | Env.Env_empty -> []
  | Env_extension (s, _, _)
  | Env_modtype (s, _, _)
  | Env_class (s, _, _)
  | Env_cltype (s, _, _)
  | Env_functor_arg (s, _)
  | Env_type (s, _, _)
  | Env_constraints (s, _) 
  | Env_module (s, _, _, _) 
  | Env_copy_types s
  | Env_persistent (s, _)
  | Env_value_unbound (s, _, _)
  | Env_module_unbound (s, _, _) -> 
    find_instances lvl s
  | Env_value (s, ident, descr) ->
    (* print_tab lvl;
    print_endline @@ Ident.name ident; *)
    begin match try_make_instance env ty ident descr with
    | Some i -> i :: find_instances lvl s
    | _ -> find_instances lvl s
    end
  | Env_open (s, path) ->
      let str_items mdecl =
        match mdecl.Types.md_type with
        | Mty_signature sg -> sg
        | Mty_functor _ -> [] 
        | _ -> assert false
      in
      let lvl = lvl + 1 in
      let rest = find_instances lvl s in
      (* print_tab lvl;
      print_endline @@ "module: " ^ Path.name path; *)
      let md = Env.find_module path env in
      List.fold_left (fun res -> function
        | Types.Sig_value (ident, descr, _) ->
          (* print_tab lvl;
          print_endline @@ "  " ^ Ident.name ident; *)
          begin match try_make_instance env ty ident descr with
          | Some i -> i :: res
          | _ -> res
          end
        | _ -> res)
        rest (str_items md)
  in
  find_instances 0 (Env.summary env)

let gen_instance loc inst =
  let base = Util.mk_var (Ident.name inst.base) in
  match inst.args with
  | [] -> 
    base
  | _::_ ->
    Ast_helper.Exp.apply
      base
      (List.map (fun () -> (Asttypes.Nolabel, Util.hole ~loc)) inst.args)
