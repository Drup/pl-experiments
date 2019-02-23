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

(* let mk_tuple n =
 *   let name = Name.create ~name:("tup"^ string_of_int n) () in
 *   let ty l = App (name, l) in
 *   let kind =
 *     let name, k = gen_kind_var () in
 *     kscheme ~kvars:[name] ~args:(List.init n (fun _ -> k)) k
 *   in
 *   name, ty, kind *)

let initial_env =
  Env.empty
  |> Env.add_constr array_name array_kind
  |> Env.add_constr int_name int_kind
  |> Env.add_constr unit_name unit_kind

module PrimMap = CCMap.Make(String)
let primitives =
  let open PrimMap in
  let un = Un Global in
  empty
  |> add "plus" @@ tyscheme (int @-> int @-> int)
  |> add "init" (
    let name, a = Types.gen_var () in
    tyscheme ~tyvars:[name, un]
      (int @-> (int @-> a) @-> array a)
  )
  |> add "free" (
    let name, a = Types.gen_var () in
    tyscheme ~tyvars:[name, un] (array a @-> unit_ty)
  )
  |> add "length"(
    let name, a = Types.gen_var () in
    let kname, k = Types.gen_kind_var () in
    let kname_borrow, k_borrow = Types.gen_kind_var () in
    tyscheme
      ~kvars:[kname; kname_borrow]
      ~tyvars:[name, k]
      ~constr:[(k, Un Never)]
      (Borrow (Read, k_borrow, array a) @-> int)
  )
  |> add "get"(
    let name, a = Types.gen_var () in
    let kname, k = Types.gen_kind_var () in
    let kname_borrow, k_borrow = Types.gen_kind_var () in
    tyscheme
      ~kvars:[kname; kname_borrow]
      ~tyvars:[name, k]
      ~constr:[(k, Un Never)]
      (Tuple [Borrow (Read, k_borrow, array a); int] @-> a )
  )
  |> add "set" (
    let name, a = Types.gen_var () in
    let kname, k = Types.gen_kind_var () in
    let kname_borrow, k_borrow = Types.gen_kind_var () in
    tyscheme
      ~kvars:[kname; kname_borrow]
      ~tyvars:[name, k]
      ~constr:[(k, Aff Never)]
      (Tuple [Borrow (Write, k_borrow, array a); int; a] @-> unit_ty)
  )
    
let initial_rename_env = Syntax.Rename.{
    env = SMap.empty;
    tyenv = SMap.(
        empty
        |> add "unit" int_name
        |> add "int" int_name
        |> add "array" array_name
      );
  }
