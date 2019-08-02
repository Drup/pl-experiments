
exception Var_not_found of Name.t
exception Type_not_found of Name.t

type ('a, 'b) env = {
  vars : 'a Name.Map.t ;
  constr : 'b Name.Map.t ;
}
type t = (Types.scheme, Types.kscheme) env

let add k v env = { env with vars = Name.Map.add k v env.vars }
let add_constr k v env = { env with constr = Name.Map.add k v env.constr }

let find k env =
  try Name.Map.find k env.vars with
    Not_found -> raise (Var_not_found k)
let find_constr k env =
  try Name.Map.find k env.constr with
    Not_found -> raise (Type_not_found k)

let rm k env = { env with vars = Name.Map.remove k env.vars }

let empty = {
  vars = Name.Map.empty ;
  constr = Name.Map.empty ;
}

