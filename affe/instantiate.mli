open Types

type ienv
val create : level -> ienv
val level : ienv -> level

val kvar : ienv:ienv -> Name.t -> Name.t * kind
val tyvar : ienv:ienv -> Name.t -> Name.t * typ

val constr : int -> normalized_constr -> normalized_constr

val kind_scheme : 
  ?args:kind list ->
  level:int -> kscheme -> normalized_constr * kind

val typ_scheme : 
  level:int ->
  scheme ->
  normalized_constr * typ
