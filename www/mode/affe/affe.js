// (function(mod) {
//   if (typeof exports == "object" && typeof module == "object") // CommonJS
//     mod(require("../../lib/codemirror"));
//   else if (typeof define == "function" && define.amd) // AMD
//     define(["../../lib/codemirror"], mod);
//   else // Plain browser env
//     mod(CodeMirror);
// })(function(CodeMirror) {
// "use strict";

RegExpPrepare= function(s) {
    return s.replace(/[-\/\\^$*+?.()|[\]{}]/g, '\\$&');
};

var keywords = [
    "type", "fun", "val", "match", "of", "include", "fix",
    "rec", "let", "in", "for","all", "un", "aff", "lin"
];

var op = [
    "=", ";", ":", ".", ",", "|", "\u2200",
    "*", "/", "+", "-", "%", ">", "<", "->", "<-", "\\"
];
var op2 = [
    "-{", "}>", "{", "}", "&&!", "&&", "&!", "&"
];

function mkre (l) {
    return '(?:' + l.map(RegExpPrepare).join('|') + ')'
};

var tyRE = /['^][a-z_'A-Z0-9]*/;
var smallRE = /[a-z_][a-z_'A-Z0-9]*/;
var largeRE = /[A-Z][a-z_'A-Z0-9]*/;
var intRE   = /[0-9]+/;

var mode = {
    // The start state contains the rules that are intially used
    start: [
        {regex: new RegExp (mkre(keywords) + '\\b'), token: "keyword"},
        {regex: new RegExp (mkre(op2)), token: "builtin"},
        {regex: new RegExp (mkre(op))},
        {regex: /"(?:[^\\]|\\.)*?(?:"|$)/, token: "string"},
        
        // A next property will cause the mode to move to a different state
        // indent and dedent properties guide autoindentation
        {regex: /[\{\[\(]/, indent: true},
        {regex: /[\}\]\)]/, dedent: true},
        {regex: new RegExp(smallRE), token: "variable"},
        {regex: new RegExp(largeRE), token: "variable-2"},
        {regex: new RegExp(tyRE), token: "variable-3"},
        {regex: new RegExp(intRE, 'i'), token: "number"},
        {regex: /\(\*/, token: "comment", next: "comment"},
        {regex: /\#.*/, token: "comment"},
    ],
    // The multi-line comment state.
    comment: [
        {regex: /.*?\*\)/, token: "comment", next: "start"},
        {regex: /.*/, token: "comment"}
    ],
    // The meta property contains global information about the mode. It
    // can contain properties like lineComment, which are supported by
    // all modes, and also directives like dontIndentStates, which are
    // specific to simple modes.
    meta: {
        dontIndentStates: ["comment"],
        lineComment: "#"
    }
};

CodeMirror.defineSimpleMode("affe", mode);


// CodeMirror.defineMode("affe", function(_config, modeConfig) {

//     function switchState(source, setState, f) {
//         setState(f);
//         return f(source, setState);
//     }

//     var tyRE = /['^]/;
//     var smallRE = /[0-9a-z_]/;
//     var largeRE = /[A-Z]/;
//     var idRE    = /[a-z_'A-Z0-9]/;
//     var intRE   = /[0-9]/;
//     var whiteRE = /[ \t\v\f]/; // newlines are handled in tokenizer

//     function normal(source, setState) {
//         if (source.eatWhile(whiteRE)) {
//             return null;
//         }

//         var ch = source.next();

//         // Handling of comments.
//         if (ch == '(' && source.eat('*')) {
//             return switchState(source, setState, ncomment("comment", 1));
//         }
//         if (ch == '#') {
//             return switchState(source, setState, linecomment);
//         }

//         // Handling of string literals.
//         if (ch == '"') {
//             return switchState(source, setState, stringLiteral);
//         }

//         if (ch == '*' && source.eol()) {
//             return "special";
//         }

//         if (ch == '-' && source.eat('>') && source.eol()) {
//             return "special";
//         }

//         // Handling of variables and constructors.
//         if (largeRE.test(ch)) {
//             source.eatWhile(idRE);
//             return "variable-2";
//         }

//         if (smallRE.test(ch)) {
//             source.eatWhile(idRE);
//             return "variable";
//         }

//         if (tyRE.test(ch)) {
//             source.eatWhile(idRE);
//             return "variable-3";
//         }

//         // Default to error.
//         return "error";
//     }

//     function linecomment(source, setState) {
//         source.skipToEnd();
//         setState(normal);
//         return "comment";
//     }

//     function ncomment(type, nest) {
//         if (nest == 0) {
//             return normal;
//         }
//         return function(source, setState) {
//             var currNest = nest;
//             while (!source.eol()) {
//                 var ch = source.next();
//                 if (ch == '(' && source.eat('*')) {
//                     ++currNest;
//                 }
//                 else if (ch == '*' && source.eat(')')) {
//                     --currNest;
//                     if (currNest == 0) {
//                         setState(normal);
//                         return type;
//                     }
//                 }
//             }
//             setState(ncomment(type, currNest));
//             return type;
//         };
//     }

//     function stringLiteral(source, setState) {
//         while (!source.eol()) {
//             var ch = source.next();
//             if (ch == '"') {
//                 setState(normal);
//                 return "string";
//             }
//             if (ch == '\\') {
//                 var ch = source.next();
//                 if (ch != '\\' && ch != 'n' && ch != 't'){
//                     return "error";
//                 }
//             }
//         }
//         setState(normal);
//         return "error";
//     }

//     var wellKnownWords = (function() {
//         var wkw = {};
//         function setType(t) {
//             return function () {
//                 for (var i = 0; i < arguments.length; i++)
//                     wkw[arguments[i]] = t;
//             };
//         }

//         setType("keyword")(
//             "type", "fun", "val", "match", "of", "include", "fix",
//             "rec", "let", "in", "for all", "un", "aff", "lin"
//         );

//         setType("builtin")(
//             "=", ";", ":", ".", "(", ")", ",", "[", "]", "|", "\u2200",
//             "*", "/", "+", "-", "%", ">", "<", "->", "<-", "\\"
//         );
//         setType("builtin-2")(
//             "{", "}", "&&!", "&&", "&!", "&", "-{", "}>"
//         );

//         var override = modeConfig.overrideKeywords;
//         if (override) for (var word in override) if (override.hasOwnProperty(word))
//             wkw[word] = override[word];

//         return wkw;
//     })();



//     return {
//         startState: function ()  { return { f: normal }; },
//         copyState:  function (s) { return { f: s.f }; },

//         token: function(stream, state) {
//             var t = state.f(stream, function(s) { state.f = s; });
//             var w = stream.current();
//             return wellKnownWords.hasOwnProperty(w) ? wellKnownWords[w] : t;
//         },

//         lineComment: "#",
//         blockCommentStart: "(*",
//         blockCommentEnd: "*)"
//     };

// });

CodeMirror.defineMIME("text/x-affe", "affe");

// });
