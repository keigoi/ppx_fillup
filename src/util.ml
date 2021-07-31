let print_typed_expression env (texp:Typedtree.expression) =
    let str = Typedtree.(
      {str_items=[{str_desc=Tstr_eval (texp, []); str_loc=texp.exp_loc; str_env=env}];
      str_type=[];
      str_final_env=env;
      }
      ) in
    Format.eprintf "%a@." Ocaml_common.Printtyped.implementation str
