(* Stolen from the plzoo *)

(** Source code locations. *)
type location

(** A datum tagged with a source code location *)
type 'a located = private { data : 'a ; loc : location }

(** Tag a datum with an (optional) location. *)
val locate : ?loc:location -> 'a -> 'a located

(** Convert a [Lexing.lexbuf] location to a [location] *)
val location_of_lex : Lexing.lexbuf -> location

(** [make_location p1 p2] creates a location which starts at [p1] and ends at [p2]. *)
val make_location : Lexing.position -> Lexing.position -> location

(** Print a location *)
val print_location : location -> Format.formatter -> unit

val utf8 : bool ref
(** Should we print utf8 ? *)

(** [error ~kind ~loc msg] raises an exception which is caught by the toplevel and
    prints the given message. *)
val error :
   ?kind:string -> ?loc:location -> ('a, Format.formatter, unit, 'b) format4 -> 'a

(** Print miscellaneous information *)
val print_info : ('a, Format.formatter, unit, unit) format4 -> 'a

type filename = string

(** The definition of a programming language *)
module type LANGUAGE =
  sig
    (** The name of the language (used for prompt) *)
    val name : string

    (** The type of top-level commands *)
    type command

    (** The runtime environment *)
    type environment

    (** Additional command-line options *)
    val options : (Arg.key * Arg.spec * Arg.doc) list

    (** The initial runtime environment *)
    val initial_environment : environment

    (** Given the interactive input so far, should we read more? *)
    val read_more : string -> bool

    (** A parser for parsing entire files *)
    val file_parser : (Lexing.lexbuf -> command list) option

    (** A parser for parsing one toplevel command *)
    val toplevel_parser : (Lexing.lexbuf -> command) option

    (** Execute a toplevel command in the given environment and
        return the new environment. *)
    val exec :
      (environment -> filename -> environment) ->
      environment -> command -> environment
  end

(** Create a language from its definition. *)
module Main (L : LANGUAGE) : sig
  (** The main program *)
  val main : unit -> unit
end

(*

MIT License

Copyright © 2016 Andrej Bauer, Matija Pretnar

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

*)
