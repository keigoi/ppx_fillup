exception Pending of Location.t * string

let error = Util.error

let rec extract_fundeps_body loc : Parsetree.core_type -> string list * string =
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
    let args1, ret = extract_fundeps_body loc ret in
    let args2 = decompose_products arg in
    args2 @ args1, ret
  | {ptyp_desc=Ptyp_var(var); _} ->
    [], var
  | _ ->
    error loc (Format.asprintf "Invalid disjointness specification: %a" Ocaml_common.Pprintast.core_type typ)

let extract_fundeps loc decl =
  match Util.typedecl_attr decl "disjoint_objects" with
  | [] -> 
    None
  | attr::_ ->
    begin match attr with
    | {attr_payload=PTyp(typ); _} -> 
      Some (extract_fundeps_body loc typ)
    | _ -> 
      error loc "attribute [@disjoint_objects] has an invalid payload; it must be of form [@disjoint_objects: 'l -> 'r -> 'lr]"
    end

let disjointness_typeclass_body loc (decl:Types.type_declaration) =
  match decl.type_kind with
  | Type_record(lds, _rep) -> 
    begin match extract_fundeps loc decl with
    | Some deps ->
      Some (deps, lds)
    | None ->
      None
    end
  | _ -> 
    None


let field_types loc typ =
  match typ with
  | Outcometree.Otyp_object (flds, None) -> 
    flds
  | _ -> 
    raise (Pending (loc, (Format.asprintf "not applicable for object concatenation: %a" !Ocaml_common.Oprint.out_type typ)))

exception Not_applicable

let list_of_opt = function
  | Some x -> [x]
  | None -> []

let generate_projection loc ?from ?onto subst' =
  let rec loop nests0 subst0 =
    let subst = List.map (fun (domvar,typ) -> domvar, field_types loc typ) subst0 in
    let make_field fld =
      let nests = fld::nests0 in
      match
        List.concat_map (fun (var,typ) -> 
          match List.assoc_opt fld typ with
          | Some typ -> [(var,typ)] | None -> []) subst
      with
      | [(var,_)] -> 
        let var = Option.value from ~default:var in
        (* field has no duplicate. just project onto it *)
        Util.make_method fld (List.fold_left (fun exp f -> Util.make_call exp f) (Util.mk_var var) @@ List.rev nests)
      | ents ->
        (* field has duplicates. try to separate it further *)
        Util.make_method fld (loop nests ents)
    in
    let all_fields = 
      List.sort_uniq String.compare 
      @@ List.concat_map (fun (var, obj) -> 
        match onto with
        | Some onto -> if var=onto then List.map fst obj else []
        | None -> List.map fst obj) subst 
    in
    Ast_helper.Exp.object_ @@ Ast_helper.Cstr.mk [%pat? _] @@ List.map make_field all_fields
  in   
  loop [] subst'

let generate_concatenator loc (domvars,rngvar) subst0 fldtype =
  let subst = List.filter (fun ((domvar,_)) -> List.mem domvar domvars) subst0 in
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
        generate_projection loc subst
    | Tpoly(typ,_) | Tsubst(typ) | Tlink(typ) ->
      loop rest typ
    | _ ->
      error loc 
        (Format.asprintf "Field type (%a) is not an arrow type: %a" 
          Ocaml_common.Printtyp.type_expr fldtype 
          Ocaml_common.Printtyp.type_expr typ)
  in loop domvars fldtype

let generate_splitter_body loc rngvar typ =
  let fields =
    let flds = field_types loc typ in
    List.map (fun (fld,_) -> Util.make_method fld (Util.make_call (Util.mk_var rngvar) fld)) flds
  in
  Ast_helper.Exp.object_ @@ Ast_helper.Cstr.mk [%pat? _] fields
  
let generate_splitter loc (domvars,rngvar) subst0 fldtype =
  let subst = List.filter (fun ((domvar,_)) -> List.mem domvar domvars) subst0 in
  let rec make_tuples (typ:Types.type_expr) =
    match typ.desc with
    | Tvar(Some(var)) ->
      if not @@ List.mem var domvars then
        error loc
          (Format.asprintf "Return type ('%s) is not in the argument list ('%a): " var (Format.pp_print_list Format.pp_print_string) domvars)
      else
        (* generate_splitter_body loc rngvar (List.assoc var subst) *)
        generate_projection loc ~from:rngvar ~onto:var  subst
    | Ttuple(typs) ->
      Ast_helper.Exp.tuple (List.map make_tuples typs)
    | Tpoly(typ,_) | Tsubst(typ) | Tlink(typ) ->
      make_tuples typ
    | _ ->
      error loc (Format.asprintf "Splitter return type must be tuple or typevar: %a" Ocaml_common.Printtyp.type_expr typ)
  in
  match fldtype.Types.desc with
  | Tarrow(_, argtype, rettype, _) -> 
    let argvar = Util.tyvar loc argtype in
    if rngvar <> argvar then
      raise Not_applicable
    else
    let open Parsetree in let open Ast_helper in
    [%expr fun [%p Pat.var @@ Location.mknoloc argvar] -> [%e make_tuples rettype]]
  | _ ->
    error loc 
      (Format.asprintf "Field type is not an arrow type: %a" 
        Ocaml_common.Printtyp.type_expr fldtype)


let generate_concatenator_or_splitter loc deps subst fldtype =
  try 
    generate_concatenator loc deps subst fldtype
  with
  | Not_applicable -> 
    begin try
      generate_splitter loc deps subst fldtype
    with
    | Not_applicable ->
      error loc (Format.asprintf "Cannot generate from disjoint instance field type: %a" Ocaml_common.Printtyp.type_expr fldtype)
    end

let to_otype typ = Printtyp.tree_of_typexp false typ


let fill_holes_disjoint loc env (texp: Typedtree.expression) =
  let typ = Util.expand_type env texp.exp_type in
  let args, decl, _ = Util.type_head_decls loc env typ in
  match disjointness_typeclass_body loc decl with
  | Some (deps,lds) ->
    let subst = 
      List.mapi (fun i -> function {Types.desc=Tvar(Some var); _} -> (var, to_otype @@ List.nth args i) | _ -> assert false) 
      decl.type_params 
    in
    let make_field ld =
      let fld = Location.mknoloc @@ Option.get @@ Longident.unflatten @@ [Ident.name ld.Types.ld_id] in
      let expr = generate_concatenator_or_splitter loc deps subst ld.ld_type in
      (fld, expr)
    in
    Option.some @@ Ast_helper.Exp.record ~loc (List.map make_field lds) None
  | None ->
    None
    (* error loc (Format.asprintf "Not a record type: %a" Ocaml_common.Printtyp.type_expr texp.exp_type) *)
