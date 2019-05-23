(function(mod) {
  if (typeof exports == "object" && typeof module == "object") // CommonJS
    mod(require("../../lib/codemirror"));
  else if (typeof define == "function" && define.amd) // AMD
    define(["../../lib/codemirror"], mod);
  else // Plain browser env
    mod(CodeMirror);
})(function(CodeMirror) {
"use strict";

function RegExpPrepare (s) {
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
    "-{", "}>", "&&!", "&&", "&!", "&"
];

function mkre (l) {
    return '(?:' + l.map(RegExpPrepare).join('|') + ')'
};

var tyRE = /['^][a-z_'A-Z0-9]*[₀₁₂₃₄₅₆₇₈₉]*/u;
var smallRE = /[a-z_][a-z_'A-Z0-9]*/;
var largeRE = /[A-Z][a-z_'A-Z0-9]*/;
var intRE   = /[0-9]+/;

var mode = {
    // The start state contains the rules that are intially used
    start: [
        {regex: /\(\*/, token: "comment", next: "comment"},
        {regex: /\##.*/, token: "comment-2"},
        {regex: /\#.*/, token: "comment"},
        {regex: new RegExp (mkre(keywords) + '\\b'), token: "keyword"},
        {regex: new RegExp (mkre(op2)), token: "builtin"},
        {regex: new RegExp (mkre(op)), token: "operator"},
        {regex: /"(?:[^\\]|\\.)*?(?:"|$)/, token: "string"},
        
        // A next property will cause the mode to move to a different state
        // indent and dedent properties guide autoindentation
        {regex: /[\{\[\(]/, token: "bracket", indent: true},
        {regex: /[\}\]\)]/, token: "bracket", dedent: true},
        {regex: new RegExp(smallRE), token: "variable"},
        {regex: new RegExp(largeRE), token: "variable-2"},
        {regex: new RegExp(tyRE), token: "type"},
        {regex: new RegExp(intRE, 'i'), token: "number"},
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
CodeMirror.defineMIME("text/x-affe", "affe");

});
