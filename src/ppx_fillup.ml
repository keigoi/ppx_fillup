
Printexc.record_backtrace true

let error loc (s:string) =
  Location.raise_errorf ~loc "%s" s

let fields ?(loc=Location.none) typ =
  match Printtyp.tree_of_typexp false typ with
  | Otyp_object (flds, None) -> 
    Option.some @@ List.map fst flds
  | Otyp_object (_, Some _) -> 
    None
    (* error loc (Format.asprintf "object type is open: %a@." Ocaml_common.Printtyp.type_expr typ) *)
  | _ -> 
    error loc (Format.asprintf "not an object type: %a@." Ocaml_common.Printtyp.type_expr typ)

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
    error arg2.pexp_loc (Format.asprintf "duplicate fields:%a@." Ocaml_common.Printtyp.type_expr argtyp2)
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

let str_items mdecl =
  match mdecl.Types.md_type with
  | Mty_signature sg -> sg
  | Mty_functor _ -> [] 
  | _ -> assert false

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
      error loc (Format.asprintf "Not a typeclass:%a@." Ocaml_common.Printtyp.type_expr typ_orig);
  | _ -> 
    error loc (Format.asprintf "Bad hole type:%a@." Ocaml_common.Printtyp.type_expr typ_orig)


let is_instance vdescr =
  List.exists (fun attr -> attr.Parsetree.attr_name.txt="instance") vdescr.Types.val_attributes

type instance =
  {base:Ident.t; args:instance list}

let rec make_instance env ty ident inst_ty =
  match (Ctype.repr @@ Ctype.expand_head env inst_ty) with
  | {Types.desc=Types.Tarrow(_, argty, retty,_);_} -> 
    check_is_typeclass env Location.none argty;
    let rest = make_instance env ty ident retty in
    begin match resolve_instances argty env with
    | [] -> 
      error Location.none (Format.asprintf "Context instance not found:%a@." Ocaml_common.Printtyp.type_expr argty) 
    | i::_ -> {rest with args= i::rest.args}
    end
  | _ ->
    (* Todo: unify and search *)
    if Ctype.matches env ty inst_ty then
      {base=ident; args=[]}
    else
      raise Not_found
and try_make_instance env ty ident descr =
  if not @@ is_instance descr then
    None
  else
    try
      Some (make_instance env ty ident descr.val_type)
    with
      Not_found ->
        None
and resolve_instances ty env =
  let rec find_instances = function
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
  | Env_module_unbound (s, _, _) -> find_instances s
  | Env_value (s, ident, descr) ->
    (* print_endline @@ Ident.name ident;
    List.iter (fun attr -> print_endline @@ attr.Parsetree.attr_name.txt) descr.val_attributes; *)
    begin match try_make_instance env ty ident descr with
    | Some i -> i :: find_instances s
    | _ -> find_instances s
    end
  | Env_open (s, path) ->
      let md = Env.find_module path env in
      List.fold_left (fun res -> function
        | Types.Sig_value (ident, descr, _) ->
          (* print_endline @@ Ident.name ident;
          List.iter (fun attr -> print_endline @@ attr.Parsetree.attr_name.txt) descr.val_attributes; *)
          begin match try_make_instance env ty ident descr with
          | Some i -> i :: find_instances s
          | _ -> find_instances s
          end
        | _ -> res)
        (find_instances s) (str_items md)
  in
  find_instances (Env.summary env)

let rec gen_instance loc inst =
  (* print_endline @@ "gen_instance:"^Ident.name inst.base; *)
  let base =
    Ast_helper.Exp.ident (Location.mknoloc (Longident.Lident (Ident.name inst.base)))
  in
  match inst.args with
  | [] -> {base with pexp_loc=loc}
  | _::_ ->
    Ast_helper.Exp.apply
      ~loc 
      base
      (List.map (fun x -> (Asttypes.Nolabel, gen_instance Location.none x)) inst.args)

let instrument_concat (super:Untypeast.mapper) =
  fun (self:Untypeast.mapper) (texp : Typedtree.expression) ->
    match texp with
    | {exp_attributes=[{Parsetree.attr_name={txt="HOLE";_};_}];_} ->
      check_is_typeclass texp.exp_env texp.exp_loc texp.exp_type;
      begin match resolve_instances texp.exp_type texp.exp_env with
      | [] -> error texp.exp_loc (Format.asprintf "Instance not found:%a@." Ocaml_common.Printtyp.type_expr texp.exp_type)
      | inst::_ ->  gen_instance texp.exp_loc inst
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

let hole : Parsetree.expression = 
  let loc = Location.none in
  [%expr (assert false)[@HOLE]] 
  
let replace_hashhash_with_hole (super:Ast_mapper.mapper) (self:Ast_mapper.mapper) (exp:Parsetree.expression) =
  match exp.pexp_desc with
  | Pexp_apply(
      {pexp_desc=Pexp_ident({txt=Lident("##"); _}); pexp_loc=loc_hole; _}, 
      [(_, arg1); (_, arg2)]
    ) -> 
      Ast_helper.Exp.apply ~loc:exp.pexp_loc ~attrs:exp.pexp_attributes 
        arg1 
        [(Nolabel, {hole with pexp_loc=loc_hole}); (Nolabel, arg2)]
  | _ -> super.expr self exp

let new_env () =
  Compmisc.init_path (); 
  Compmisc.initial_env () 
      
let transform str =
    let str = 
      let super = Ast_mapper.default_mapper in
      let mapper = {super with expr = replace_hashhash_with_hole super} in
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

let f (exp:Parsetree.expression) =
  match exp.pexp_desc with
  | Parsetree.Pexp_ident _ |Parsetree.Pexp_constant _ |Parsetree.Pexp_let(_, _, _) 
  | Parsetree.Pexp_function _ |Parsetree.Pexp_fun (_, _, _, _)
    |Parsetree.Pexp_apply (_, _) |Parsetree.Pexp_match (_, _) |Parsetree.Pexp_try
                                                                 (_, _) |Parsetree.Pexp_tuple _ |Parsetree.Pexp_construct (_, _)
    |Parsetree.Pexp_variant (_, _) |Parsetree.Pexp_record (_, _)
    |Parsetree.Pexp_field (_, _) |Parsetree.Pexp_setfield (_, _, _)
    |Parsetree.Pexp_array _ |Parsetree.Pexp_ifthenelse (_, _, _)
    |Parsetree.Pexp_sequence (_, _) |Parsetree.Pexp_while (_, _)
    |Parsetree.Pexp_for (_, _, _, _, _) |Parsetree.Pexp_constraint (_, _)
    |Parsetree.Pexp_coerce (_, _, _) |Parsetree.Pexp_send (_, _)
    |Parsetree.Pexp_new _ |Parsetree.Pexp_setinstvar (_, _)
    |Parsetree.Pexp_override _ |Parsetree.Pexp_letmodule (_, _, _)
    |Parsetree.Pexp_letexception (_, _) |Parsetree.Pexp_assert _
    |Parsetree.Pexp_lazy _ |Parsetree.Pexp_poly (_, _) |Parsetree.Pexp_object _
    |Parsetree.Pexp_newtype (_, _) |Parsetree.Pexp_pack _ |Parsetree.Pexp_open
                                                             (_, _) |Parsetree.Pexp_letop _ |Parsetree.Pexp_extension _
    |Parsetree.Pexp_unreachable -> assert false

let rec loop f str =
  let str' = f str in
  if str=str' then
    str
  else
    loop f str'

let () =
  Ppxlib.Driver.register_transformation 
    ~impl:(loop transform)
    "ppx_concat"
