
Printexc.record_backtrace true

let error loc (s:string) =
  Location.raise_errorf ~loc "%s" s

let env =
  lazy begin 
    Compmisc.init_path (); 
    Compmisc.initial_env () 
  end

let fields ?(loc=Location.none) typ =
  match Printtyp.tree_of_typexp false typ with
  | Otyp_object (flds, None) -> 
    List.map fst flds
  | Otyp_object (_, Some _) -> 
    error loc (Format.asprintf "object type is open: %a@." Ocaml_common.Printtyp.type_expr typ)
  | _ -> 
    error loc (Format.asprintf "not an object type: %a@." Ocaml_common.Printtyp.type_expr typ)

let make_method fld exp =
  Ast_helper.Cf.method_ (Location.mknoloc fld) Public (Cfk_concrete(Fresh, exp))

let make_call exp fld =
  Ast_helper.Exp.send exp (Location.mknoloc fld)

let concat untyp_f (arg1:Typedtree.expression) (arg2:Typedtree.expression) =
  let flds1 = fields ~loc:arg1.exp_loc arg1.exp_type 
  and flds2 = fields ~loc:arg2.exp_loc arg2.exp_type 
  in
  let has_dup = List.exists (fun x -> List.exists (fun y -> x=y) flds1) flds2 in
  if has_dup then
    error arg2.exp_loc (Format.asprintf "duplicate fields:%a@." Ocaml_common.Printtyp.type_expr arg2.exp_type)
  else begin
    let mths1 obj = List.map (fun f -> make_method f (make_call obj f)) flds1
    and mths2 obj = List.map (fun f -> make_method f (make_call obj f)) flds2
    in
    let loc = Location.none in
    Ast_helper.Exp.let_
      Nonrecursive
      [Ast_helper.Vb.mk [%pat? obj1] (untyp_f arg1);
       Ast_helper.Vb.mk [%pat? obj2] (untyp_f arg2);]
      (Ast_helper.Exp.object_ @@ 
        Ast_helper.Cstr.mk 
          [%pat? _]
          (mths1 [%expr obj1] @ mths2 [%expr obj2]))
  end


let tyexp_to_exp _env (super:Untypeast.mapper) =
  fun self (texp : Typedtree.expression) ->
    match texp.exp_desc with
    | Texp_apply({exp_desc=Texp_ident(_,{txt=Lident("concat");_},_);_}, 
        [(_lab1, Some arg1);
         (_lab2, Some arg2)]) ->
          concat (super.expr self) arg1 arg2
    | _ -> 
      super.expr self texp

let transform str =
    let env = Lazy.force env in
    let (tstr, _, _, _) = Typemod.type_structure env str in
    let super = Untypeast.default_mapper in
    let mapper =
      {super with expr = tyexp_to_exp env super}
    in
    mapper.structure mapper tstr

let () =
  Ppxlib.Driver.register_transformation 
    ~impl:transform
    "ppx_ty_test"
