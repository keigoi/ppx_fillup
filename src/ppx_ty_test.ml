
Printexc.record_backtrace true

let env =
  lazy begin 
    Compmisc.init_path (); 
    Compmisc.initial_env () 
  end

let tyexp_to_exp env (super:Untypeast.mapper) =
  fun self (texp : Typedtree.expression) ->
    let e = super.expr self texp in
    let loc = texp.exp_loc in
    if Ctype.matches env texp.exp_type Predef.type_int then begin
      let open Ppxlib in
      [%expr [%e e] + 42]
    end else begin
      e
    end

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
