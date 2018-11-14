module T = Types

module Normal = struct

  type t = T.normalized_constr

  let ctrue : t = []
  let cand : t list -> t = List.flatten
  let cleq k1 k2 : t = [ (k1, k2) ]
  let (@) : t -> t -> t = (@)

  type side = Left | Right
  let get = function Left -> fst | Right -> snd
  let opp = function Left -> Right | Right -> Left

  let split_equals : t -> t * t =
    let rec remove_opp ((k1, k2) as constr) = function
      | [] -> [], false
      | (k1', k2') as constr' :: t ->
        let l, b = remove_opp constr t in
        if k2 == k1' && k1 == k2' then
          l, true
        else
          constr' :: l, b
    in
    let rec aux = function
      | [] -> [], []
      | constr :: rest ->
        let rest, b = remove_opp constr rest in
        let l_eq, rest = aux rest in
        if b then constr :: l_eq, rest else l_eq, constr :: rest
    in
    aux
  
  let simplify_solved =
    let is_same_gen_var n = function
      | T.KGenericVar n' -> Name.equal n n'
      | _ -> false
    in
    let remove_kind k l =
      let f (k1, k2) =
        not (is_same_gen_var k k1 || is_same_gen_var k k2)
      in
      List.filter f l
    and is_unused_gen_var side k l =
      List.for_all (fun b -> not @@ is_same_gen_var k @@ get side b) l
    in
    let rec filter_useless ~keep_vars = function
      | [] -> []
      | constr :: t -> begin match constr with
          | T.KGenericVar kleft , _
            when not (Name.Set.mem kleft keep_vars)
                && is_unused_gen_var Right kleft t ->
            remove_kind kleft t
          | _, T.KGenericVar kright
            when not (Name.Set.mem kright keep_vars)
                && is_unused_gen_var Left kright t ->
            remove_kind kright t
          | _ ->  constr :: filter_useless ~keep_vars t
        end 
    in
    filter_useless

end
  

let denormal : Normal.t -> T.constr = fun l ->
  T.And (List.map (fun (k1, k2) -> T.KindLeq (k1, k2)) l)


let (<=) a b : T.constr = T.KindLeq (a, b)
let (===) a b : T.constr = T.Eq (a, b)
let (&&&) a b : T.constr = T.And [a ; b]
let cand l : T.constr = T.And l
