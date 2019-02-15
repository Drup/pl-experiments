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

module type LAT = sig
  type t
  val (<) : t -> t -> bool
  val (=) : t -> t -> bool
  val biggest : t
  val smallest : t
  val least_upper_bound : t list -> t
  val greatest_lower_bound : t list -> t
  val relations : t list -> (t * t) list
end

module type KINDS = sig
  type t
  val equal : t -> t -> bool
  val hash : t -> int
  val compare : t -> t -> int
  
  type constant
  val constant : constant -> t

  val classify : t -> [> `Var | `Constant of constant ]
  val unify : t list -> t
end

module Make (Lat : LAT) (K : KINDS with type constant = Lat.t) = struct

  module G = Graph.Persistent.Digraph.Concrete(K)
  module Check = Graph.Path.Check(G)
  module Scc = Graph.Components.Make(G)
  module O = Graph.Oper.P(G)
  module S = Set.Make(G.V)

  let add_lattice_inequalities g0 =
    let constants = 
      G.fold_vertex List.cons g0 []
      |> CCList.filter_map
        (fun x -> match K.classify x with `Var -> None | `Constant c -> Some c)
    in
    let relations = Lat.relations constants in
    List.fold_left
      (fun g (k1, k2) -> G.add_edge g (K.constant k1) (K.constant k2))
      g0 relations

  (* O(|V|*|C|) *)
  let lattice_closure g0 =
    let c = Check.create g0 in
    let constants, vars =
      let f k (cl,vl) = match K.classify k with
        | `Var -> (cl, k :: vl)
        | `Constant c -> ((k, c) :: cl, vl)
      in G.fold_vertex f g0 ([],[])
    in
    let add_bounds g var =
      let lesser, greater =
        let f (l,g) (vertex, constant) =
          if Check.check_path c var vertex then (l, constant::g)
          else if Check.check_path c vertex var then (constant::l, g)
          else (l, g)
        in
        List.fold_left f ([],[]) constants
      in
      let g = G.add_edge g (K.constant @@ Lat.greatest_lower_bound lesser) var in
      let g = G.add_edge g var (K.constant @@ Lat.least_upper_bound greater) in
      g
    in
    List.fold_left add_bounds g0 vars

  (* O(|V+C|*unification + |E|) *)
  let unify_clusters g0 =
    (* We use [Types.kind] as vertices, [K.unify] will mutate them,
       thus making the internal sets of the graph invalid. 
       To avoid issues, we extract the edges as a list and walk through it 
       afterwards. It would be better to use a representation of kinds
       that is immutable. *)
    let edges = G.fold_edges (fun v1 v2 l -> (v1,v2) ::l) g0 [] in
    let clusters = Scc.scc_array g0 in
    let _vertices = Array.map K.unify clusters in
    let g_minified =
      let add_minified_edge g (v1, v2) =
        G.add_edge g v1 v2
      in
      List.fold_left add_minified_edge G.empty edges
    in

    (* let n, cluster = Scc.scc g0 in *)
    (* let unified_vars =
     *   let a = Array.make n [] in
     *   let register_vertice v = a.(cluster v) <- v :: a.(cluster v) in
     *   G.iter_vertex register_vertice g0 ;
     *   Array.map K.unify a (\* g0 is invalid after this operation *\)
     * in
     * let g_minified =
     *   let add_minified_edge g (v1, v2) =
     *     G.add_edge g (unified_vars.(cluster v1)) unified_vars.(cluster v2)
     *   in
     *   List.fold_left add_minified_edge G.empty edges
     * in *)
    g_minified

  let cleanup_vertices must_keep_vars g0 =
    let g0 = O.transitive_closure g0 in
    let can_remove =
      match must_keep_vars with
      | Some vars -> fun k -> not (S.mem k vars)
      | None -> fun _ -> false
    in
    let cleanup_vertex v g =
      match K.classify v with
      | `Var when can_remove v -> G.remove_vertex g v
      | `Constant c when Lat.(c = smallest) || Lat.(c = biggest) ->
        G.remove_vertex g v
      | `Var | `Constant _ -> g
    in
    let g_cleaned = G.fold_vertex cleanup_vertex g0 g0 in
    O.transitive_reduction ~reflexive:true g_cleaned
  
  let from_normal l =
    List.fold_left (fun g (k1, k2) -> G.add_edge g k1 k2) G.empty l

  let to_normal g =
    G.fold_edges (fun k1 k2 l -> (k1, k2) :: l) g []

  let solve ?keep_vars l =
    from_normal l
    |> add_lattice_inequalities
    |> lattice_closure
    |> unify_clusters
    |> cleanup_vertices keep_vars
    |> to_normal

  let simplify ~keep_vars l =
    from_normal l
    |> cleanup_vertices (Some keep_vars)
    |> to_normal
end

let rec shorten = function
  | Types.KVar {contents = KLink k} -> shorten k
  | Types.Un _ | Types.Aff _ | Types.KGenericVar _
  | Types.KVar {contents = KUnbound _} as k -> k

let denormal : Normal.t -> T.constr = fun l ->
  T.And (List.map (fun (k1, k2) -> T.KindLeq (k1, k2)) l)


let (<=) a b : T.constr = T.KindLeq (a, b)
let (===) a b : T.constr = T.Eq (a, b)
let (&&&) a b : T.constr = T.And [a ; b]
let cand l : T.constr = T.And l
