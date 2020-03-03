let doc =
  let open Js_of_ocaml_tyxml.Tyxml_js in
  [%html{|
<p>
  Welcome to the online demo of the Affe language!
</p>
<p>
 This language aims to prevent linearity violations, notably bugs such as 
 use-after-free. Affe is an ML-like language similar to OCaml. 
 In particular, Affe is functional with arbitrary side effects and
 complete type inference (i.e., users never need to write type annotations).
</p>
<!--<p>
  The implementation is available
  <a href="https://github.com/Drup/pl-experiments">on github</a>.
</p>-->
<p>
You can find a list of examples below. Only typing is implemented is this
online demo. The result of the typing (or the appropriate type error) is displayed
in the bottom right. Beware, this is a prototype: error messages
(and the UI in general) are research-quality.
</p>
<p>
  <em>Have fun!</em>
</p>
|}]



let l = [
  "intro.affe";
  "channel.affe";
  "sessions.affe";
  "sudoku.affe";
]

let () =
  Js_of_ocaml_tyxml.Tyxml_js.Register.id "content" doc;
  Printer.debug := false ;
  Affe_lang.load_files l ;
  Affe_lang.main ()
