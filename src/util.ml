

let error loc (s:string) =
  Location.raise_errorf ~loc "%s" s

let hole ~loc = 
  let hole : Parsetree.expression = 
    let loc = loc in
    [%expr (assert false)] 
  in
  {hole with pexp_attributes=[{attr_name={txt="HOLE"; loc=Location.none}; attr_loc=loc; attr_payload=PStr[]}]}

let expand_type env typ =
  Ctype.repr (Ctype.expand_head env typ)

let rec abbrev_paths = function
  | Types.Mcons(_, path, _, _, xs) -> path :: abbrev_paths xs
  | Mnil -> []
  | Mlink xs -> abbrev_paths !xs

let type_head_decls loc env (hole_typ:Types.type_expr) =
  match hole_typ.desc with
  | Types.Tconstr(path, args, abbrevs) -> 
    let paths = abbrev_paths !abbrevs in
    args, Env.find_type path env, List.map (fun p -> Env.find_type p env) paths
  | _ -> 
    error loc (Format.asprintf "Bad hole type:%a" Ocaml_common.Printtyp.type_expr hole_typ)

let typedecl_attr tdecl name =
  List.filter (fun decl -> decl.Parsetree.attr_name.txt=name) tdecl.Types.type_attributes

let mk_var str = Ast_helper.Exp.ident (Location.mknoloc (Longident.Lident str))

let make_method fld exp =
  Ast_helper.Cf.method_ (Location.mknoloc fld) Public (Cfk_concrete(Fresh, exp))

let make_call exp fld =
  Ast_helper.Exp.send exp (Location.mknoloc fld)

let rec tyvar loc (typ : Types.type_expr) : string =
  match typ.desc with
  | Tvar(Some(argvar)) -> argvar
  | Tlink(typ) -> tyvar loc typ
  | Tsubst(typ) -> tyvar loc typ
  | _ -> 
    error loc (Format.asprintf "Parameter type is not a type variable: %a" Ocaml_common.Printtyp.type_expr typ)

let make_expr_mapper f str =
  let super = Ast_mapper.default_mapper in
  let f' self exp =
    match f exp with
    | Some exp -> exp
    | None -> super.expr self exp
  in
  let mapper = {super with expr = f'} in
  mapper.structure mapper str

let make_expr_mapper' f str =
  let super = Ast_mapper.default_mapper in
  let mapper = {super with expr = (f super)} in
  mapper.structure mapper str

let mark_as_filled loc exp : Parsetree.expression =
  let attr = {
    Parsetree.attr_name={txt="FILLED";loc=Location.none}; 
    attr_payload=PStr[]; 
    attr_loc=Location.none
    } 
  in
  {exp with pexp_attributes=attr::exp.Parsetree.pexp_attributes; pexp_loc=loc}

let rec remove_attrs name exp =
  let attrs = List.filter (fun a -> a.Parsetree.attr_name.txt<>name) exp.Parsetree.pexp_attributes in
  match exp with
  | {Parsetree.pexp_desc=Pexp_apply(f, args); _} ->
    let args = List.map (fun (l,e) -> (l, remove_attrs name e)) args in
    {exp with pexp_desc=Pexp_apply(remove_attrs name f, args); pexp_attributes=attrs}
  | _ -> 
    {exp with pexp_attributes=attrs}

let new_env () =
  Compmisc.init_path (); 
  Compmisc.initial_env () 

let make_expr_untyper f str =
  let env = new_env () in
  let (tstr, _, _, _) = Typemod.type_structure env str in
  let super = Untypeast.default_mapper in
  let f' self exp =
    match f exp with
    | Some exp -> exp
    | None -> super.expr self exp
  in
  let untyper = {super with expr = f'} in
  untyper.structure untyper tstr  
