open Types

let un = Un Global

let (@->) x y = Arrow (x,un,y)
let new_y () =
  let y_name = Name.create ~name:"a" () in
  let n = GenericVar y_name in
  (n @-> n) @-> n

let int_name = Name.create ~name:"int" ()
let int = App (int_name, [])
let int_kind = kscheme un

let array_name = Name.create ~name:"array" ()
let array x = App (array_name, [x])
let array_kind =
  let name, k = gen_kind_var () in
  kscheme ~kvars:[name] ~args:[k] (Aff Global)

let unit_name = Name.create ~name:"unit" ()
let unit_ty = App (unit_name, [])
let unit_kind = kscheme un
let unit = Syntax.Constructor (Name.create ~name:"()" ())

let initial_env =
  Env.empty
  |> Env.add_constr array_name array_kind
  |> Env.add_constr int_name int_kind
  |> Env.add_constr unit_name unit_kind

let initial_rename_env = Syntax.Rename.{
    env = SMap.empty;
    tyenv = SMap.(
        empty
        |> add "unit" int_name
        |> add "int" int_name
        |> add "ref" array_name
      );
  }
