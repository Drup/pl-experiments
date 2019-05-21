open Js_of_ocaml
open Js_of_ocaml_tyxml.Tyxml_js

let set_lang_name name =
  Dom_html.document##.title := Js.string name;
  Register.id ~keep:false "lang" [Html.txt name]

let load_file s : unit =
  Js.Unsafe.fun_call (Js.Unsafe.js_expr "loadfile")
    [|Js.Unsafe.inject @@ Js.string s|]

let clear_term () : unit = 
  Js.Unsafe.fun_call (Js.Unsafe.js_expr "clear_term")
    [||]

let add_to_term s : unit =
  Js.Unsafe.fun_call (Js.Unsafe.js_expr "add_to_term")
    [|Js.Unsafe.inject @@ Js.string s|]
let flush_term () : unit =
  Js.Unsafe.fun_call (Js.Unsafe.js_expr "flush_term")
    [||]

let term =
  let t = Format.make_formatter
    (fun s pos len ->
       let s = String.sub s pos len in
       add_to_term s)
    flush_term
  in
  Format.pp_set_max_boxes t 42 ;
  Format.pp_set_ellipsis_text t "..." ;
  Format.pp_set_margin t 60 ;
  Format.pp_set_max_indent t 30 ;
  t
