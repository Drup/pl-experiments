module T = Types

module Normal = struct

  type t = T.normalized_constr

  let ctrue : t = []
  let cand : t list -> t = List.flatten
  let cleq k1 k2 : t = [ (k1, k2) ]
  let (@) : t -> t -> t = (@)

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

let (?>) f m g =
  match m with
  | Some m -> f m g
  | None -> g

module Make (Lat : LAT) (K : KINDS with type constant = Lat.t) = struct

  module G = Graph.Persistent.Digraph.Concrete(K)
  module Check = Graph.Path.Check(G)
  module Scc = Graph.Components.Make(G)
  module O = Graph.Oper.P(G)
  module Map = CCMap.Make(G.V)
  module Set = CCSet.Make(G.V)
  module H = Hashtbl.Make(G.V)

  let add_extra_vars map g =
    Map.fold (fun k _ g -> G.add_vertex g k) map g
  
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
      let g = G.add_edge g (K.constant @@ Lat.least_upper_bound lesser) var in
      let g = G.add_edge g var (K.constant @@ Lat.greatest_lower_bound greater) in
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
  

  exception FailLattice of K.t * K.t

  module Simplify = struct

    let edges g0 =
      let cleanup_edge v1 v2 g =
        match K.classify v1, K.classify v2 with
        | `Constant l1, `Constant l2 ->
          if Lat.(l1 < l2) then g
          else raise (FailLattice (v1, v2))
        | _ -> G.add_edge g v1 v2
      in
      G.fold_edges cleanup_edge g0 G.empty

    let unused_variables vars g0 =
      let cleanup_vertex v g =
        match K.classify v with
        | `Var when not (Map.mem v vars) -> G.remove_vertex g v
        | `Var | `Constant _ -> g
      in
      G.fold_vertex cleanup_vertex g0 g0

    (* Slightly modified version of Graph.Contraction(G).contract *)
    let contract prop unify g =
      (* if the edge is to be removed (property = true):
       * make a union of the two union-sets of start and end node;
       * put this set in the map for all nodes in this set *)
      let collect_clusters edge (m, edges) =
        if prop edge then
          let s_src, s_dst = Map.find (G.E.src edge) m, Map.find (G.E.dst edge) m in
          let s = Set.union s_src s_dst in
          let m = Set.fold (fun vertex m -> Map.add vertex s m) s m in
          m, edges
        else
          m, edge :: edges
      in
      (* initialize map with singleton-sets for every node (of itself) *)
      let m =
        G.fold_vertex (fun vertex m -> Map.add vertex (Set.singleton vertex) m)
          g Map.empty
      in
      (* find all closures *)
      let m, remaining_edges = G.fold_edges_e collect_clusters g (m, []) in
      (* WARNING: side effects in unify, the graph is invalid afterwards *)
      Map.iter (fun _ ks -> ignore @@ unify ks) m;
      let add_minified_edge g (v1, v2) = G.add_edge g v1 v2 in
      List.fold_left add_minified_edge G.empty remaining_edges

    let simplify_with_position variance_map g0 =
      let p (v1, v2) =
        match Map.find_opt v1 variance_map, Map.find_opt v2 variance_map with
        | Some Variance.(Neg | Bivar), Some _ when G.out_degree g0 v1 = 1 -> true
        | _, Some Variance.(Pos | Bivar) when G.in_degree g0 v2 = 1 -> true
        | _ -> false
      in
      let unif ks = K.unify @@ Set.elements ks in
      contract p unif g0

    let bounds g =
      let g = G.remove_vertex g (K.constant Lat.biggest) in
      let g = G.remove_vertex g (K.constant Lat.smallest) in
      g

    let go keep_vars g = 
      g
      |> O.transitive_closure
      |> ?> unused_variables keep_vars
      |> O.transitive_reduction ~reflexive:true
      |> ?> simplify_with_position keep_vars
      |> bounds
  end

  let from_normal l =
    List.fold_left (fun g (k1, k2) -> G.add_edge g k1 k2) G.empty l

  let to_normal g =
    G.fold_edges (fun k1 k2 l -> (k1, k2) :: l) g []

  let solve ?keep_vars l =
    from_normal l
    |> ?> add_extra_vars keep_vars
    |> add_lattice_inequalities
    |> lattice_closure
    |> unify_clusters
    |> Simplify.go keep_vars
    |> to_normal

  (* let simplify ?keep_vars l =
   *   from_normal l
   *   |> Simplify.go keep_vars
   *   |> to_normal *)
end

let denormal : Normal.t -> T.constr = fun l ->
  T.And (List.map (fun (k1, k2) -> T.KindLeq (k1, k2)) l)

let (<=) a b : T.constr = T.KindLeq (a, b)
let (<==) a b : T.constr = T.Eq (a, b)
let (&&&) a b : T.constr = T.And [a ; b]
let cand l : T.constr = T.And l
