# My PL experiments

A collection of personal PL research and experiments.
For a more stable and pedagogic collection, please consult the [plzoo](http://andrej.com/plzoo/).

## The languages

### [Affe](lang/affe/) [**Try the online demo here!**](https://drup.github.io/pl-experiments/affe/)

An ML language with affine/linear type system, kinds and a borrow system.
Only the type system is implemented.
  
### [HM](lang/hm)

An ML-like language with side-effects. 
Implemented by a run-of-the-mill hindley-milner in the style of HM(X)
with a big-step evaluator.

## How to use

`dune exec lang/<lang>/<lang>.exe` to launch the toplevel for `<lang>`

`dune runtest lang/<lang>` to run the tests for `<lang>`.
