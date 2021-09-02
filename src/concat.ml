exception Pending

let error = Util.error

let rec extract_fundeps ?(loc=Location.none) : Parsetree.core_type -> string list * string =
  (* let var_to_pos var = 
    match List.assoc_opt var argmap with
    | Some i -> i
    | None -> error loc (Format.asprintf "Unbound variable: %s" var)
  in *)
  let rec decompose_products : Parsetree.core_type -> string list = function
    | {ptyp_desc=Ptyp_tuple(elts); _} ->
      List.concat_map decompose_products elts
    | {ptyp_desc=Ptyp_var(var); _} -> 
      [var]
    | typ -> 
      error loc (Format.asprintf "Invalid disjointness parameter type: %a" Ocaml_common.Pprintast.core_type typ)
  in
  fun typ ->
  match typ with
  | {ptyp_desc=Ptyp_arrow(_lab, arg, ret); _} ->
    let args1, ret = extract_fundeps ret in
    let args2 = decompose_products arg in
    args2 @ args1, ret
  | {ptyp_desc=Ptyp_var(var); _} ->
    [], var
  | _ ->
    error loc (Format.asprintf "Invalid disjointness specification: %a" Ocaml_common.Pprintast.core_type typ)

let disjointness_params loc decl =
  match Util.typedecl_attr decl "disjoint_objects" with
  | [] -> 
    None
  | attr::_ ->
    begin match attr with
    | {attr_payload=PTyp(typ); _} -> 
      Some (extract_fundeps typ)
    | _ -> 
      error loc "attribute [@disjoint_objects] has an invalid payload; it must be of form [@disjoint_objects: 'l -> 'r -> 'lr]"
    end

let disjointness_typeclass_body loc (decl:Types.type_declaration) =
  match decl.type_kind with
  | Type_record(lds, _rep) -> 
    begin match disjointness_params loc decl with
    | Some deps ->
      Some (deps, lds)
    | None ->
      None
    end
  | _ -> 
    None

let fields typ =
  match Printtyp.tree_of_typexp false typ with
  | Otyp_object (flds, None) -> 
    Option.some @@ List.map fst flds
  | Otyp_object (_, Some _) -> 
    None
    (* error loc (Format.asprintf "object type is open: %a" Ocaml_common.Printtyp.type_expr typ) *)
  | _ -> 
    raise Pending
    (* error loc (Format.asprintf "not an object type: %a" Ocaml_common.Printtyp.type_expr typ) *)

exception Not_applicable

let generate_concatenator_body loc argmap domvars =
  let make_fields domvar =
    let typ = List.assoc domvar argmap in
    match fields typ with
    | Some flds -> 
      List.map (fun fld -> Util.make_method fld (Util.make_call (Util.mk_var domvar) fld)) flds
    | None -> 
      error loc (Format.asprintf "Concatenator's inferred parameter type is not an object: %a" Ocaml_common.Printtyp.type_expr typ)
  in
  Ast_helper.Exp.object_ 
  @@ Ast_helper.Cstr.mk [%pat? _] 
  @@ List.concat_map make_fields domvars

let generate_concatenator loc (domvars,rngvar) argmap fldtype =
  let rec loop rest typ =
    match typ.Types.desc with
    | Tarrow(_, argtype, rettype, _) -> 
      let argvar = Util.tyvar loc argtype in
      if not @@ List.mem argvar rest then
        raise Not_applicable
      else
      let domvars = List.filter (fun v -> argvar <> v) rest in
      let open Parsetree in
      let open Ast_helper in
      [%expr fun [%p Pat.var @@ Location.mknoloc argvar] -> [%e loop domvars rettype]]
    | Tvar(Some(retvar)) ->
      if rngvar<>retvar then
        error loc (Format.asprintf "Return type ('%s) does not match the specification ('%s): " retvar rngvar)
      else
        generate_concatenator_body loc argmap domvars
    | Tpoly(typ,_) | Tsubst(typ) | Tlink(typ) ->
      loop rest typ
    |Types.Tvar _ 
    |Types.Ttuple _ |Types.Tconstr (_, _, _) |Types.Tobject (_, _) |Types.Tfield (_, _, _, _) |Types.Tnil
    |Types.Tvariant _ |Types.Tunivar _
    |Types.Tpackage (_, _, _) ->
      error loc 
        (Format.asprintf "Field type (%a) is not an arrow type: %a" 
          Ocaml_common.Printtyp.type_expr fldtype 
          Ocaml_common.Printtyp.type_expr typ)
  in loop domvars fldtype

let generate_concatenator_or_splitter loc deps argmap fldtype =
  try 
    generate_concatenator loc deps argmap fldtype
  with
  | Not_applicable -> 
    error loc (Format.asprintf "Cannot generate from disjoint instance field type: %a" Ocaml_common.Printtyp.type_expr fldtype)


let fill_holes_disjoint loc env (texp: Typedtree.expression) =
  let typ = Util.expand_type env texp.exp_type in
  let args, decl, _ = Util.type_head_decls loc env typ in
  match disjointness_typeclass_body loc decl with
  | Some (deps,lds) ->
    let argmap = 
      List.mapi (fun i -> function {Types.desc=Tvar(Some var); _} -> (var,List.nth args i) | _ -> assert false) 
      decl.type_params 
    in
    let make_field ld =
      let fld = Location.mknoloc @@ Option.get @@ Longident.unflatten @@ [Ident.name ld.Types.ld_id] in
      let expr = generate_concatenator_or_splitter loc deps argmap ld.ld_type in
      (fld, expr)
    in
    Option.some @@ Ast_helper.Exp.record ~loc (List.map make_field lds) None
  | None ->
    None
    (* error loc (Format.asprintf "Not a record type: %a" Ocaml_common.Printtyp.type_expr texp.exp_type) *)
