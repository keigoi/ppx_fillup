
Printexc.record_backtrace true

let error loc (s:string) =
  Location.raise_errorf ~loc "%s" s

let fields ?(loc=Location.none) typ =
  match Printtyp.tree_of_typexp false typ with
  | Otyp_object (flds, None) -> 
    Option.some @@ List.map fst flds
  | Otyp_object (_, Some _) -> 
    None
    (* error loc (Format.asprintf "object type is open: %a" Ocaml_common.Printtyp.type_expr typ) *)
  | _ -> 
    error loc (Format.asprintf "not an object type: %a" Ocaml_common.Printtyp.type_expr typ)

let make_method fld exp =
  Ast_helper.Cf.method_ (Location.mknoloc fld) Public (Cfk_concrete(Fresh, exp))

let make_call exp fld =
  Ast_helper.Exp.send exp (Location.mknoloc fld)

let (let+) = Option.bind
let (and+) x y =
  match x, y with
  | Some x, Some y -> Some (x,y)
  | _ -> None


let concat (arg1, argtyp1) (arg2, argtyp2) =
  let+ flds1 = fields ~loc:arg1.Parsetree.pexp_loc argtyp1
  and+ flds2 = fields ~loc:arg2.Parsetree.pexp_loc argtyp2
  in
  let has_dup = 
    List.exists (fun x -> List.exists (fun y -> x=y) flds1) flds2 
  in
  if has_dup then
    error arg2.pexp_loc (Format.asprintf "duplicate fields:%a" Ocaml_common.Printtyp.type_expr argtyp2)
  else begin
    let mths1 obj = List.map (fun f -> make_method f (make_call obj f)) flds1
    and mths2 obj = List.map (fun f -> make_method f (make_call obj f)) flds2
    in
    let loc = Location.none in
    Option.some @@
    Ast_helper.Exp.let_
      Nonrecursive
      [Ast_helper.Vb.mk [%pat? obj1] arg1;
       Ast_helper.Vb.mk [%pat? obj2] arg2;]
      (Ast_helper.Exp.object_ @@ 
        Ast_helper.Cstr.mk 
          [%pat? _]
          (mths1 [%expr obj1] @ mths2 [%expr obj2]))
  end


let hole ~loc = 
  let hole : Parsetree.expression = 
    let loc = Location.none in
    [%expr (assert false)] 
  in
  {hole with pexp_attributes=[{attr_name={txt="HOLE"; loc=Location.none}; attr_loc=loc; attr_payload=PStr[]}]}

let rec rettype env inst_ty =
  match (Ctype.repr @@ Ctype.expand_head env inst_ty).desc with
  | Types.Tarrow(_,_argty,retty,_) -> rettype env retty
  | _ -> inst_ty

let is_typeclass env path =
  let tdecl = Env.find_type path env in
  List.exists (fun decl -> decl.Parsetree.attr_name.txt="typeclass") tdecl.type_attributes

let rec abbrev_paths = function
  | Types.Mcons(_, path, _, _, xs) -> path :: abbrev_paths xs
  | Mnil -> []
  | Mlink xs -> abbrev_paths !xs

let check_is_typeclass env loc (typ_orig : Types.type_expr) = 
  let typ = Ctype.repr (Ctype.expand_head env typ_orig) in
  match typ.desc with
  | Types.Tconstr(path, _, abbrevs) -> 
    if is_typeclass env path 
      || List.exists (is_typeclass env) (abbrev_paths !abbrevs) then 
      ()
    else 
      error loc (Format.asprintf "Not a typeclass:%a" Ocaml_common.Printtyp.type_expr typ_orig);
  | _ -> 
    error loc (Format.asprintf "Bad hole type:%a" Ocaml_common.Printtyp.type_expr typ_orig)


let is_instance vdescr =
  List.exists (fun attr -> attr.Parsetree.attr_name.txt="instance") vdescr.Types.val_attributes

type instance =
  {base:Ident.t; args:unit list}
  
let rec make_instance env ty ident inst_ty =
  match (Ctype.repr @@ Ctype.expand_head env inst_ty) with
  | {Types.desc=Types.Tarrow(_, argty, retty,_);_} -> 
    check_is_typeclass env Location.none argty;
    let rest = make_instance env ty ident retty in
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
  | Env_module_unbound (s, _, _) -> find_instances lvl s
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

let mark_as_filled exp : Parsetree.expression =
  let attr = {
    Parsetree.attr_name={txt="FILLED";loc=Location.none}; 
    attr_payload=PStr[]; 
    attr_loc=Location.none
    } 
  in
  {exp with pexp_attributes=attr::exp.Parsetree.pexp_attributes}

let gen_instance loc inst =
  let base =
    Ast_helper.Exp.ident (Location.mknoloc (Longident.Lident (Ident.name inst.base)))
  in
  match inst.args with
  | [] -> 
    mark_as_filled @@ {base with pexp_loc=loc}
  | _::_ ->
    mark_as_filled @@
    Ast_helper.Exp.apply
      ~loc 
      base
      (List.map (fun () -> (Asttypes.Nolabel, hole ~loc)) inst.args)

let rec remove_attrs exp =
  match exp with
  | {Parsetree.pexp_desc=Pexp_apply(f, args); _} ->
    let args = List.map (fun (l,e) -> (l, remove_attrs e)) args in
    {exp with pexp_desc=Pexp_apply(remove_attrs f, args); pexp_attributes=[]}
  | _ -> 
    {exp with pexp_attributes=[]}

let instrument_concat (super:Untypeast.mapper) =
  fun (self:Untypeast.mapper) (texp : Typedtree.expression) ->
    match texp with
    | {exp_attributes=[{Parsetree.attr_name={txt="HOLE"; _}; attr_loc=attr_loc; _}];_} ->
      check_is_typeclass texp.exp_env texp.exp_loc texp.exp_type;
      begin match resolve_instances texp.exp_type texp.exp_env with
      | [] -> 
          error attr_loc (Format.asprintf "Instance not found: %a" Ocaml_common.Printtyp.type_expr texp.exp_type)
      | inst::_ ->  
          gen_instance texp.exp_loc inst
      end
    | {exp_desc=Texp_apply({exp_desc=Texp_ident(_,{txt=Lident("concat");_},_);_}, 
        [(_lab1, Some arg1);
         (_lab2, Some arg2)]); _} ->
          begin match 
            let untype = self.expr self in
            concat 
              (untype arg1, arg1.exp_type) 
              (untype arg2, arg2.exp_type)
          with
            | Some v -> v
            | None -> super.expr self texp
          end
    | _ -> 
      super.expr self texp


let mark_alert loc exp : Parsetree.expression =
  let expstr = 
    let exp' = remove_attrs exp in
    Format.asprintf "Filled: (%a)" Ocaml_common.Pprintast.expression exp' 
  in
  let payload : Parsetree.expression = 
    Ast_helper.Exp.constant (Ast_helper.Const.string expstr)
  in
  let attr = {
    Parsetree.attr_name={txt="ppwarning";loc=Location.none}; 
    attr_payload=PStr[{pstr_desc=Pstr_eval(payload,[]); pstr_loc=loc}]; 
    attr_loc=Location.none
    } 
  in
  {exp with pexp_attributes=attr::exp.Parsetree.pexp_attributes}
      

(* replace ## with hole *)
let replace_hashhash_with_holes (exp:Parsetree.expression) =
  match exp with
  | {pexp_desc=Pexp_apply(
      {pexp_desc=Pexp_ident({txt=Lident("##"); _}); pexp_loc=loc_hole; _}, 
      [(_, arg1); (_, arg2)]
    ); _} -> 
      Option.some @@
        Ast_helper.Exp.apply ~loc:exp.pexp_loc ~attrs:exp.pexp_attributes 
          arg1 
          [(Nolabel, {(hole ~loc:loc_hole) with pexp_loc=loc_hole}); (Nolabel, arg2)]
  | _ -> 
    None

(* annotate filled nodes with alerts *)
let annotate_filled (exp:Parsetree.expression) =
  match exp with
  | {pexp_desc=_; pexp_attributes={attr_name={txt="FILLED";_};_}::attrs;_} ->
    Option.some @@
      mark_alert exp.pexp_loc {exp with pexp_attributes=attrs}
  | _ -> 
    None

let make_expr_mapper f =
  let super = Ast_mapper.default_mapper in
  let f' self exp =
    match f exp with
    | Some exp -> exp
    | None -> super.expr self exp
  in
  {super with expr = f'}

let new_env () =
  Compmisc.init_path (); 
  Compmisc.initial_env () 
      
let transform str =
    let str = 
      let mapper = make_expr_mapper replace_hashhash_with_holes in
      mapper.structure mapper str
    in
    let env = new_env () in
    let (tstr, _, _, _) = Typemod.type_structure env str in
    let str =
      let super = Untypeast.default_mapper in
      let untyper = {super with expr = instrument_concat super} in
      untyper.structure untyper tstr  
    in
    str

let rec loop f str =
  let str' = f str in
  if str=str' then
    let str = 
      let mapper = make_expr_mapper annotate_filled in
      mapper.structure mapper str
    in
    str
  else
    loop f str'

let () =
  Ppxlib.Driver.register_transformation 
    ~impl:(loop transform)
    "ppx_concat"
