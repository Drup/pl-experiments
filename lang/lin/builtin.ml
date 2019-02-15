open Types

let un = Un Global

let (@->) x y = Arrow (x,un,y)
let new_y () =
  let y_name = Name.create ~name:"a" () in
  let n = GenericVar y_name in
  (n @-> n) @-> n

let int_name = Name.create ~name:"int" ()
let int = App (int_name, [])

let ref_name = Name.create ~name:"ref" ()
let ref x = App (ref_name, [x])

let initial_env =
  Env.empty
  |> Env.add_constr ref_name (kscheme ~args:[un] un)
  |> Env.add_constr int_name (kscheme un)

let initial_rename_env = Syntax.Rename.{
    env = SMap.empty ;
    tyenv = SMap.(
        empty
        |> add "int" int_name
        |> add "ref" ref_name
      )
  }
