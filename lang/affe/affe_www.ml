let l = [
  "intro.affe";
  "sessions.affe";
]

let () =
  Printer.debug := false ;
  Affe_lang.load_files l ;
  Affe_lang.main ()
