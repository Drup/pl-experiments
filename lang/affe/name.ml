module M = struct
  type t = {name : string option ; id : int}
  let hash x = Hashtbl.hash x.id
  let compare n1 n2 = compare n1.id n2.id
  let equal n1 n2 = n1.id = n2.id
  let dummy name = { name = Some name ; id = -1 }
  let create =
    let r = ref 0 in
    fun ?name () ->
      let id = !r in incr r ;
      { name ; id }
end
include M
module Map = CCMap.Make(M)
module Set = CCSet.Make(M)
module Tbl = CCHashtbl.Make(M)
