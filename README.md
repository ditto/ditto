# Ditto

Ditto is a super kawaii dependently typed programming language.
It is _super kawaii_ due to its small and straightfoward
implementation, and adorable syntax ;)

Taking advantage of its simple implementation, we
use Ditto as a vehicle for experimenting with type system features.
Despite being implemented simply, Ditto is a high-level language
that supports terse programs, rather a core language
necessitating verbose encodings.

Put together, these things make Ditto a good language for _research_.
When confronted with a simple versus performant implementation
decision, we tend to choose the former. For now, we are
concerned with type checking code rather than running code.

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
