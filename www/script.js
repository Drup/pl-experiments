var filename = ""
var edit = undefined;
var term = undefined;

function loadfile(fn) {
    window.location.hash = fn;
    dir = "examples/";
    filename = fn;
    $.ajax({
        type     : "GET",
        url      : dir + fn,
        dataType : 'text',
        success  : function (data) {edit.setValue(data);}
    });
}

$(function() {
    // Creation of editors.
    edit = CodeMirror(document.getElementById("edit"), {
        lineNumbers    : true,
        lineWrapping   : true,
        theme          : "solarized",
        scrollbarStyle : "simple"
    });

    edit.on('cursorActivity',
            function(instance){
                var pos = instance.getCursor();
                $( "#pos" ).text((pos.line+1)+','+pos.ch);
            });

    term = CodeMirror(document.getElementById("term"), {
        lineWrapping   : true,
        readOnly       : false,
        theme          : "solarized",
        scrollbarStyle : "simple"
    });

    // Loading default file in the editor.
    var s = location.hash.substring(1) ;
    if (s === "") { s = "intro.affe"; };
    loadfile(s);

    // Making things resizable.
    $( "#west" ).resizable({
        handles  : "e",
        minWidth : 400,
        maxWidth : (document.body.clientWidth - 400)
    });

    $( "#edit" ).resizable({
        handles    : "s",
        minHeight  : 100,
        maxHeight  : (document.body.clientHeight - 120),
        resize     :
        function( event, ui ) {
            $( "#term" ).css("height", "calc(100% - "+ui.size.height+"px - 3ex)");
            term.refresh();
            edit.refresh();
        }
    });
});


// var worker_handler = new Object ();

function clear_term() {
    term.setValue('')
}

function add_to_term(s) {
    var doc = term.getDoc();
    var line = doc.lastLine();
    var pos = {
        line: line,
        ch: doc.getLine(line).length
        // set the character position to the end of the line
    }
    doc.replaceRange(s, pos); // adds a new line
}
function flush_term() {
    var doc = term.getDoc();
    term.scrollIntoView(doc.getCursor());
}

// worker.onmessage =
//   function (m) {
//     if (m.data.typ != 'result') add_to_term(m.data.result);
//     else add_to_term(m.data.result);
//   }

// function ASYNCH (action_name, action_args, cont) {
//   worker_handler[action_name] = cont;
//   worker.postMessage ({fname: action_name, args: action_args});
// }

function eval() {
    var s = edit.getValue();
    Affe.eval (filename, s);
}
