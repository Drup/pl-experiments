# The Affe prototype typechecker

This is a prototype implementation of the Affe typechecker. It complements
the article "Kindly Bent To Free Us". The last version of the article is
available in the sources (`article.pdf`).

This typechecker implements the feature from the article (full inference, kinds, linearity, regions and borrows) and adds algebraic datatype and pattern matching.
As noted in Section 3 of the article, regions variable are implemented using
integers instead of full blown region variables.

## Online version 

An online version of the typechecker with a selected set of examples is available here:

  https://drup.github.io/pl-experiments/affe/
  
## Content

This repository contains:
- The implementation of the typechecker `affe` in the directory `affe/`
  This can be build with `make all`
- A set of examples and their expected output in the directory `examples/`
  These can be build with `make test`
  A description of the examples can be found below

For simplicity, only the files directly necessary to evaluate the 
typechecker have been included. The full source (with, notably,
the implementation of the webpage) is available here:

  https://github.com/Drup/pl-experiments

## Running the typechecker

Running the typechecker will return the inferred type-signature for each declaration
in the file.

You can run the typechecker interactively with 
```
dune exec affe
```

you can run the typechecker on any file of your choosing with
```
dune exec affe -- <file>
```

See `dune exec affe -- --help` for help

## Included examples 

The following examples should be used as an introduction
to the language:

- `channel.affe` A simple implementation of untyped channels
- `session.affe` Example A.1 from the article
- `sudoku.affe` Example 2.2 from the article
- `pool.affe` Example A.2 from the article

Additional examples:

- `array.affe` contains the basic array primitives
- `cow.affe` implements Copy-on-write arrays based on array primitives

Expected failures:

- `fail.affe`
- `nonlexical.affe` this file requires the extension for non-lexical lifetime described in 6.4.

Several other tests for individual features are also available in `basic.affe`, `example.affe`, `constructor.affe`, `patmatch.affe`, `region.affe` and `test_un.affe`.


## The Affe language

The language is largely described in section 2 of the article. We recommend 
discovering the language using the "main" examples described before.
We now describe some of the syntax of the language that might differ from the
article.

### Toplevel commands

```
import "file"
```
runs the typechecker on the file `file` and imports all its declarations.

```
val some_name : <scheme>
```
declares a symbol `some_name` with the given type. The type is checked for well-formedness, but not more. This is used to assume the existence of some primitives without implementing them fully.

```
type ('a : k1, 'b: k2) t : <kind>
```
allows to declare an abstract type `t` with the given parameters and kind. See `session.affe` for examples.

```
type ('a : 'k) option : 'k = None of unit | Some of 'a
```
allows to declare an algebraic data type. Kinds must be fully specified.

```
let some_name = <expr>
```
define `some_name` and add it to the environment.

### Types

The kind `un`, `lin` and `aff` are available.

The types `unit` and `'a array` are pre-defined

The type schemes and expressions form a subset of OCaml, with
the following differences:
- Arrows can be annotated with a kind using the syntax `-{<kind>}>`
- Borrow types are noted `&(<kind>,<type>)` and `&!(<kind>,<type>)`.
- Universal quantification in type schemes is explicit. For instance in `sudoku.affe`:
  ```
  val iter_set : \ 'k . (int -{'k}> unit) -> intset -{'k}> unit
  ```
  The `\` indicates a forall (∀).

### Expressions

The expression language is equivalent to a subset of OCaml, with the following
differences:
- Regions are indicated with `{ <expr> }`
- Borrows are noted `&(<expr>)` and `&!(<expr>)`
- Delimiters in pattern matching are mandatory: `match <expr> with { <cases> }`. See `patmatch.affe` for example. Deep pattern matching is not supported.
