(* This file contains all the common code used by the languages implemented in the PL Zoo. *)

type location =
  | Location of Lexing.position * Lexing.position (** delimited location *)
  | Nowhere (** no location *)

type 'a located = { data : 'a ; loc : location }

let make_location loc1 loc2 = Location (loc1, loc2)

let location_of_lex lex =
  Location (Lexing.lexeme_start_p lex, Lexing.lexeme_end_p lex)

let locate ?(loc=Nowhere) x = { data = x; loc = loc }

(** Exception [Error (loc, err, msg)] indicates an error of type [err] with error message
    [msg], occurring at location [loc]. *)
exception Error of (location * string * string)

(** [error ~loc ~kind] raises an error of the given [kind]. The [kfprintf] magic allows
    one to write [msg] using a format string. *)
let error ?(kind="Error") ?(loc=Nowhere) =
  let k _ =
    let msg = Format.flush_str_formatter () in
      raise (Error (loc, kind, msg))
  in
  Format.kfprintf k Format.str_formatter

let print_parens ?(max_level=9999) ?(at_level=0) ppf =
  if max_level < at_level then
    begin
      Format.fprintf ppf "(@[" ;
      Format.kfprintf (fun ppf -> Format.fprintf ppf "@])") ppf
    end
  else
    begin
      Format.fprintf ppf "@[" ;
      Format.kfprintf (fun ppf -> Format.fprintf ppf "@]") ppf
    end

let print_location loc ppf =
  match loc with
  | Nowhere ->
      Format.fprintf ppf "unknown location"
  | Location (begin_pos, end_pos) ->
      let begin_char = begin_pos.Lexing.pos_cnum - begin_pos.Lexing.pos_bol in
      let end_char = end_pos.Lexing.pos_cnum - begin_pos.Lexing.pos_bol in
      let begin_line = begin_pos.Lexing.pos_lnum in
      let filename = begin_pos.Lexing.pos_fname in

      if String.length filename != 0 then
        Format.fprintf ppf "file %S, line %d, charaters %d-%d" filename begin_line begin_char end_char
      else
        Format.fprintf ppf "line %d, characters %d-%d" (begin_line - 1) begin_char end_char

(** A fatal error reported by the toplevel. *)
let fatal_error msg = error ~kind:"Fatal error" msg

(** A syntax error reported by the toplevel *)
let syntax_error ?loc msg = error ~kind:"Syntax error" ?loc msg

(** Print a message at a given location [loc] of message type [msg_type]. *)
let print_message ?(loc=Nowhere) msg_type fmt =
  let ppf = Zoo_web.term in
  match loc with
  | Location _ ->
     Format.fprintf ppf ("%s at %t:@."^^fmt^^"@.") msg_type (print_location loc)
  | Nowhere ->
     Format.fprintf ppf ("%s: "^^fmt^^"@.") msg_type

(** Print the caught error *)
let print_error (loc, err_type, msg) = print_message ~loc err_type "%s" msg

let print_info msg =
  Format.fprintf Zoo_web.term msg

type filename = string

module type LANGUAGE =
sig
  val name : string
  type command
  type environment
  val options : (Arg.key * Arg.spec * Arg.doc) list
  val initial_environment : environment
  val read_more : string -> bool
  val file_parser : (Lexing.lexbuf -> command list) option
  val toplevel_parser : (Lexing.lexbuf -> command) option
  val exec :
    (environment -> filename -> environment) ->
    environment -> command -> environment
end

module Main (L : LANGUAGE) =
struct

  (** Parse the contents from a file, using a given [parser]. *)
  let read_file parser (fn, str) =
    let lex = Lexing.from_string (str ^"\n") in
    lex.Lexing.lex_curr_p <- {lex.Lexing.lex_curr_p with Lexing.pos_fname = fn};
    let terms = parser lex in
    terms
          
  (** Parser wrapper that catches syntax-related errors and converts them to errors. *)
  let wrap_syntax_errors parser lex =
    try[@warning "-52"]
      parser lex
    with
      | Failure _ ->
        syntax_error ~loc:(location_of_lex lex) "unrecognised symbol"
      | _ ->
        syntax_error ~loc:(location_of_lex lex) "syntax error"

  (** Load directives from the given file. *)
  let use_file ctx (filename, content) =
    match L.file_parser with
    | Some f ->
      let cmds = read_file (wrap_syntax_errors f) (filename, content) in
      List.fold_left
        (L.exec (fun _ _ -> fatal_error "Cannot load files in the web toplevel"))
        ctx cmds
    | None ->
      fatal_error "Cannot load files, only interactive shell is available"


  let eval (name, s) =
    let name = Js_of_ocaml.Js.to_string name in
    let s = Js_of_ocaml.Js.to_string s in
    begin try
        Zoo_web.clear_term ();
        Zoo_web.add_to_term "(* Starting typing *)\n";
        let _ = use_file L.initial_environment (name, s) in
        ()
      with
      | Error err -> print_error err
      | _e ->
        error "Uncaught exception"
    end ;
    Zoo_web.add_to_term "(* Finished typing *)\n";
    ()

  let load_files l =
    let open Js_of_ocaml_tyxml.Tyxml_js in
    
    let elem s =
      Html.(li [a ~a:[a_class ["file"]; a_href ("#"^s); a_title s;
                  a_onclick (fun _ -> Zoo_web.load_file s; false);]
              [txt s]])
    in
    let l = Html.ul (List.map elem l) in
    Register.id ~keep:true "examples" [l]
  
  let main () =
    Zoo_web.set_lang_name L.name;
    Js_of_ocaml.Js.export "Affe" (object%js
      method eval name s = eval (name, s)
    end)
    
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
