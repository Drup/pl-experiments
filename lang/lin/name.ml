module M = struct
  type t = {name : string ; id : int}
  let compare n1 n2 = compare n1.id n2.id
  let equal n1 n2 = n1.id = n2.id
  let dummy name = { name ; id = -1 }
  let create =
    let r = ref 0 in
    fun ?(name="") () ->
      let id = !r in incr r ;
      { name ; id }
end
include M
module Map = Map.Make(M)
module Set = Set.Make(M)
