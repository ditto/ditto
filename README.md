# Ditto

Ditto is a super kawaii dependently typed language for you!

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
* Run the tests with `stack runghc src/Ditto/Test.hs`.
* Work interactively with `stack ghci`.
* Run the current version of the binary with `stack exec -- dtt -t PATH/TO/Foo.dtt`.

## Installation

* Make sure you have [Stack](https://github.com/commercialhaskell/stack#how-to-install) installed.
* Make sure `$HOME/.local/bin` is in your `$PATH`.
* Run `stack install` in this directory.
* Run `dtt -t PATH/TO/Foo.dtt` to type check a file.
