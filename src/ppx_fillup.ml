
Printexc.record_backtrace true

let error = Util.error

let fill_holes (texp : Typedtree.expression) =
  match texp with
  | {exp_attributes=[{Parsetree.attr_name={txt="HOLE"; _}; attr_loc=attr_loc; _}];_} ->
    
    Typeclass.check_is_typeclass texp.exp_env texp.exp_loc texp.exp_type;

    begin match Concat.fill_holes_disjoint texp.exp_loc texp.exp_env texp with
    | Some exp -> 
      Some (Util.mark_as_filled texp.exp_loc exp)
    | exception (Concat.Pending (loc, str)) ->
      prerr_endline str;
      Some (Util.hole ~loc:loc)
    | None ->
      begin match Typeclass.resolve_instances texp.exp_type texp.exp_env with
      | [] -> 
        error attr_loc (Format.asprintf "Instance not found: %a" Ocaml_common.Printtyp.type_expr texp.exp_type)
      | inst::_ ->  
        Some (Util.mark_as_filled texp.exp_loc @@ Typeclass.gen_instance texp.exp_loc inst)
      end
    end
  | _ -> 
    None      

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
          [(Nolabel, {(Util.hole ~loc:loc_hole) with pexp_loc=loc_hole}); (Nolabel, arg2)]
  | _ -> 
    None

let mark_alert loc exp : Parsetree.expression =
  let expstr = 
    let exp' = Util.remove_attrs "FILLED" exp in
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
    
(* annotate filled nodes with alerts *)
let alert_filled (super:Ast_mapper.mapper) (self:Ast_mapper.mapper) (exp:Parsetree.expression) =
  match exp with
  | {pexp_desc=_; pexp_attributes={attr_name={txt="FILLED";_};_}::attrs;_} ->
    let exp = super.expr self exp in
    mark_alert exp.pexp_loc {exp with pexp_attributes=attrs}
  | _ ->
    if List.exists (fun a -> a.Parsetree.attr_name.txt = "HOLE") exp.pexp_attributes then
      error exp.pexp_loc "Can't fill"
    else
      super.expr self exp

let transform str =
    let str = Util.make_expr_mapper replace_hashhash_with_holes str in
    let str = Util.make_expr_untyper fill_holes str in
    str

let rec loop f str =
  let str' = f str in
  if str=str' then
    Util.make_expr_mapper' alert_filled str
  else
    loop f str'

let () =
  Ppxlib.Driver.register_transformation 
    ~impl:(loop transform)
    "ppx_concat"
