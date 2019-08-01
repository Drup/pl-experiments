open Types

let (@->) x y = Arrow (x,Kinds.un Global,y)
let new_y () =
  let y_name = Name.create ~name:"a" () in
  let n = GenericVar y_name in
  (n @-> n) @-> n

let int_name = Name.create ~name:"int" ()
let int = App (int_name, [])
let int_kind = kscheme @@ Kinds.un Global

let array_name = Name.create ~name:"array" ()
let array x = App (array_name, [x])
let array_kind =
  let name, k = gen_kind_var () in
  kscheme ~kvars:[name] ~args:[k] @@ Kinds.aff Global

let unit_name = Name.create ~name:"unit" ()
let unit_ty = App (unit_name, [])
let unit_kind = kscheme @@ Kinds.un Global
let unit_constr_name = Name.create ~name:"()" ()
let unit = Syntax.Constructor unit_constr_name

let bool_name = Name.create ~name:"bool" ()
let bool = App (bool_name, [])
let bool_kind = kscheme @@ Kinds.un Global
let true_constr_name = Name.create ~name:"True" ()
let true_val = Syntax.Constructor true_constr_name
let false_constr_name = Name.create ~name:"False" ()
let false_val = Syntax.Constructor false_constr_name

let initial_env =
  Env.empty
  |> Env.add_constr array_name array_kind
  |> Env.add_constr int_name int_kind
  |> Env.add_constr unit_name unit_kind
  |> Env.add_constr bool_name bool_kind
  |> Env.add unit_constr_name (tyscheme unit_ty)
  |> Env.add true_constr_name (tyscheme bool)
  |> Env.add false_constr_name (tyscheme bool)

module PrimMap = CCMap.Make(String)
let primitives =
  let open PrimMap in
  (* let un = Un Global in *)
  empty
  |> add "+" @@ tyscheme (int @-> int @-> int)
  |> add "-" @@ tyscheme (int @-> int @-> int)
  |> add "*" @@ tyscheme (int @-> int @-> int)
  |> add "/" @@ tyscheme (int @-> int @-> int)
  |> add "<" @@ tyscheme (int @-> int @-> bool)
  |> add ">" @@ tyscheme (int @-> int @-> bool)
  |> add "=" @@ tyscheme (int @-> int @-> bool)
  (* |> add "init" (
   *   let name, a = Types.gen_var () in
   *   tyscheme ~tyvars:[name, un]
   *     (int @-> (int @-> a) @-> array a)
   * )
   * |> add "free" (
   *   let name, a = Types.gen_var () in
   *   tyscheme ~tyvars:[name, un] (array a @-> unit_ty)
   * )
   * |> add "length"(
   *   let name, a = Types.gen_var () in
   *   let kname, k = Types.gen_kind_var () in
   *   let kname_borrow, k_borrow = Types.gen_kind_var () in
   *   tyscheme
   *     ~kvars:[kname; kname_borrow]
   *     ~tyvars:[name, k]
   *     ~constr:[(k, Un Never)]
   *     (Borrow (Read, k_borrow, array a) @-> int)
   * )
   * |> add "get"(
   *   let name, a = Types.gen_var () in
   *   let kname, k = Types.gen_kind_var () in
   *   let kname_borrow, k_borrow = Types.gen_kind_var () in
   *   tyscheme
   *     ~kvars:[kname; kname_borrow]
   *     ~tyvars:[name, k]
   *     ~constr:[(k, Un Never)]
   *     (Tuple [Borrow (Read, k_borrow, array a); int] @-> a )
   * )
   * |> add "set" (
   *   let name, a = Types.gen_var () in
   *   let kname, k = Types.gen_kind_var () in
   *   let kname_borrow, k_borrow = Types.gen_kind_var () in
   *   tyscheme
   *     ~kvars:[kname; kname_borrow]
   *     ~tyvars:[name, k]
   *     ~constr:[(k, Aff Never)]
   *     (Tuple [Borrow (Write, k_borrow, array a); int; a] @-> unit_ty)
   * ) *)
    
let initial_rename_env = Syntax.Rename.{
    env = SMap.(
        empty
        |> add "()" unit_constr_name
        |> add "True" true_constr_name
        |> add "False" false_constr_name
      );
    tyenv = SMap.(
        empty
        |> add "unit" unit_name
        |> add "int" int_name
        |> add "array" array_name
        |> add "bool" bool_name
      );
  }
