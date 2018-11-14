module Lin = Zoo.Main (struct

    let name = "Lin"

    type command = Syntax.command

    let options = []

    type environment = {
      ty : Env.t ;
      name: Syntax.Rename.env ;
      value: Eval.env ;
    }
    let add_def x ty v env = {
      ty = Env.add x ty env.ty ;
      name = { env.name with env = Syntax.Rename.add x.name x env.name.env } ;
      value = Eval.add x v env.value ;
    }
    let add_decl ty schm env = {
      ty = Env.add_constr ty schm env.ty ;
      name = { env.name with tyenv = Syntax.Rename.add ty.name ty env.name.tyenv } ;
      value = env.value ;
    }
    let initial_environment = {
      ty = Builtin.initial_env;
      name = Builtin.initial_rename_env;
      value = Eval.initial_env ;
    }

    let read_more str = 
      let i = ref (String.length str - 1) in
      while !i >= 0 && List.mem str.[!i] [' '; '\n'; '\t'; '\r'] do decr i done ;
      !i < 1 || (str.[!i] <> ';' || str.[!i - 1] <> ';')

    let file_parser = Some (Parser.file Lexer.token)
    let toplevel_parser = Some (Parser.toplevel Lexer.token)

    let exec env c =
      let c = Syntax.Rename.command env.name c in
      match c with
      | Syntax.Def {name ; expr} ->
        let constr, types, scheme =
          try Typing.infer_top env.ty expr
          with
          | Typing.Unif.Fail (ty1, ty2) ->
            Zoo.error ~kind:"Type error"
              "Cannot unify types %a and %a@."
              Printer.typ ty1 Printer.typ ty2
          | Env.Type_not_found name -> 
            Zoo.error "Unknwon type %a" Printer.name name
          | Env.Var_not_found name -> 
            Zoo.error "Unknwon variable %a" Printer.name name
        in 
        let v = Eval.execute env.value expr in
        let env = { env with ty = types } in
        Zoo.print_info "@[<2>%a@ : @[%a@]@ = @[%a@]@.%a@.%a@]@."
          Printer.name name  Printer.scheme scheme  Printer.value v
          Printer.constrs constr
          Printer.env env.ty ;
        add_def name scheme v env
      | Syntax.Type decl ->
        let ty_name, ty_decl, constr_name, constr_decl =
          Transl.transl_decl ~env:env.ty decl
        in
        Zoo.print_info "@[<2>type %a@ = %a@]@." 
          Printer.name ty_name
          Printer.kscheme ty_decl ;
        Zoo.print_info "@[<2>constr %a@ = %a@]@."
          Printer.name constr_name
          Printer.scheme constr_decl ;        
        env
        |> add_def constr_name constr_decl (Syntax.Constructor (constr_name, None))
        |> add_decl ty_name ty_decl
  end)

let () = Lin.main ()
