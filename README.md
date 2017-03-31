# Ditto

Ditto is a dependently typed language for _research_.
This means emphazing a small and straightfoward implementation
over performance, and type checking code over running code.
However, Ditto is a high-level language, rather
than a core language. 

By focusing on a simple implementation, 
extending Ditto with experimental type system features
becomes easy.
By focusing on high-level language features,
writing non-trivial programs becomes possible,
without verbose encodings that appear when programming
in a core language.

![Ditto](http://cdn.bulbagarden.net/upload/7/72/Ditty.png)

## Features

* Open universe of types.
* Dependent pattern matching.
  * Searches all possible coverings.
  * Enhanced catch-all clauses (novel).
* Implicit arguments.
  * Miller-pattern unification.
  * Constraint postponement.
* Mutual definitions.
  * Functions.
  * Induction-recursion.
  * Induction-induction.
* Eta-equality for functions.
* Interactivity via command-line interface.
  * Holes.
  * Case splitting.
* Tracking user vs machine-introduced variables.

## Development

* Make sure you have [Stack](https://github.com/commercialhaskell/stack#how-to-install) installed.
* Build the project with `stack build`.
* Run the tests with `stack test`.
* Work interactively with `stack ghci`.
* Run the current version of the binary with `stack exec -- dtt -t PATH/TO/Foo.dtt`.

## Installation

* Make sure you have [Stack](https://github.com/commercialhaskell/stack#how-to-install) installed.
* Make sure `$HOME/.local/bin` is in your `$PATH`.
* Run `stack install` in this directory.
* Run `dtt -t PATH/TO/Foo.dtt` to type check a file.
