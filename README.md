# An executable formal semantics of Agda in 𝕂

[Agda](https://wiki.portal.chalmers.se/agda/) is a dependently typed programming language and interactive theorem prover based on Martin-Löf type theory. This repository contains [𝕂 Framework](https://www.kframework.org/) code for an executable formal semantics of (a portion of) Agda. See [my Master's thesis](https://is.muni.cz/th/ssggj/Thesis.pdf) for a discussion of its development and structure.

Parsing and scope analysis is performed via a patched version of the official Agda type checker. The semantics itself then covers the following features:

* type-checking and type inference algorithms,
* function clauses to introduce dependently typed functions,
* `data` declarations of inductively defined families,
* insertion of metavariables in place of implicit arguments,
* a relatively ad-hoc implementation of pattern matching.

Within the scope of these features, the executable semantics can be used as a drop-in replacement for the official Agda type-checker.

## Installation

The following versions were used during the development:

* 𝕂 Framework 3.4 (released 15-Oct-2014),
* Agda 2.4.2.2 (released 26-Nov-2014).

𝕂 Framework can be downloaded and installed in the form of precompiled binaries. Presumably, a different minor version of 𝕂 should be usable as well.

Agda, however, must be compiled manually in precisely this version with some changes made to the source code. After the archive is downloaded and extracted, the patch [`agda-2.4.2.2-kshow.diff`](./agda-2.4.2.2-kshow.diff) from this repository should be applied:

```sh
$ cd [path to the agda-2.4.2.2 directory]
$ patch -p1 <[path to agda-2.4.2.2-kshow.diff]
### expected output:
patching file Agda.cabal
patching file src/full/Agda/Interaction/Imports.hs
patching file src/full/Agda/KShow.hs
patching file src/full/Agda/Syntax/Concrete/KShow.hs
patching file src/full/Agda/Syntax/Concrete/Name.hs
patching file src/full/Agda/Syntax/Concrete/Pretty.hs
patching file src/full/Agda/Syntax/Concrete.hs
patching file src/full/Agda/Syntax/Translation/AbstractToConcrete.hs
```

Agda should be then built as per the usual instructions in its `README`. Make the resulting `agda` binary available as `agda-kshow` in the shell's `$PATH` (e.g., by creating a symlink `~/.local/bin/agda-kshow` pointing to `[agda-2.4.2.2]/dist/build/agda/agda`).

Note that the patched version of Agda cannot be directly employed in its capacity as type-checker – its execution flow is stopped prematurely to return an AST for our semantics.

Once 𝕂 is installed and `agda-kshow` is prepared, we can finally `kompile` the semantics:
```sh
$ cd [path to a clone of this repo]
$ ./kompile.sh
### prints out reports about the stages of the compilation, concluding with...
Number of Modules                             =   13
Number of Sentences                           =  350
Number of Productions                         =  207
Number of Cells                               =    8
```
This should produce an `agda-kompiled` subdirectory.

## Type-checking with the semantics

Use `krun.sh` to type-check standard Agda files. As the 𝕂 Framework output tends to be rather large and cumbersome, the script also saves it to the file named `out` in the current directory while still printing to the console.

```
$ ./krun.sh ./tests/DepStructs.lagda
### ...
<k>
  .K
</k>
<mgu>
  subst(.KList)
</mgu>
<ctx-stack>
  .List
</ctx-stack>
<sig>
  ### 𝕂 doesn't print unicode, the number ‘8469’ is a code for the symbol ‘ℕ’ used in the input file
  Data ( "8469" ) |-> Set ( 0 )
  Con ( "zero" ) |-> Data ( "8469" )
  Con ( "succ" ) |-> ( #symVariable(30) : Data ( "8469" ) ) -> Data ( "8469" )
  
  Data ( "Fin" ) |-> ( #symVariable(466) : Data ( "8469" ) ) -> Set ( 0 )
  Con ( "fzero" ) |-> { #symVariable(475) : Data ( "8469" ) } -> (Data ( "Fin" ) (Con ( "succ" ) #symVariable(475)))
  Con ( "fsucc" ) |-> { #symVariable(489) : Data ( "8469" ) } -> ( #symVariable(488) : (Data ( "Fin" ) #symVariable(489)) ) -> (Data ( "Fin" ) (Con ( "succ" ) #symVariable(489)))

  ### etc.
</sig>
<ctx>
  .Map
</ctx>
### ...
```

If you are not familiar with 𝕂, you can consult [my Master's thesis](https://is.muni.cz/th/ssggj/Thesis.pdf) to get an idea on how to interpret the output.

## Testing

You can also execute the [tests](./tests) by running:
```sh
$ ./ktest.sh
```

The script runs the test suite and for each test file compares the `krun` output with the expected result. If all the test cases pass, the script finishes with a green `SUCCESS` printed to the console.

The `tests` directory is divided into `covered` and `beyond`. The former subdirectory contains programs that use only the features covered by our semantics whereas the latter contains also examples that fall beyond its scope. One can examine the cases in `beyond` to get an idea about the limitations of this 𝕂-based type-checker. Only the files in `covered` are used when running `ktest.sh`.
