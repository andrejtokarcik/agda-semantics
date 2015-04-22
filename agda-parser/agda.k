require "agda-syntax.k"
require "agda-semantics.k"

// TODO: closures (@Fun) like metadata wrappers by passing
// cell fragments as in kool-typed-dynamic.k

module AGDA
  imports AGDA-SYNTAX
  imports AGDA-SEMANTICS

  // sequentialise any whitespace-separated list that gets on top
  // (don't I want to deal with declaration lists *only*?)
  rule 'Cons(D,, Ds) => D ~> Ds           [structural]
  rule '.List`{""`}(.KList) => .          [structural]

  // metadata bureaucracy
  syntax K ::= md(MetadataCellFragment, K)
             | md(MetadataCellFragment)
  rule [R:Range] K => md(<range> R </range>, K)  [macro]
  rule <k> md(M, K) => K ~> md(M') ...</k>
       <metadata> M' => M </metadata>   [structural]
  //rule <k> _:KResult ~> md(M') => . ...</k>
  //     <metadata> _ => M' </metadata>   [structural]
  rule <k> md(M') => . ...</k>
       <metadata> _ => M' </metadata>   [structural]

  syntax KItem ::= "test"
  rule <k> test => whnf(Name("map") Name("tt") (Name("_::_") {Set(1)} Set(0) (Name("nil") {Set(1)}))) ...</k>

  configuration <T>
                  <k> $PGM:Program /*~> test*/ </k>
                  <tenv> .Map </tenv>   // <ctx>    --- contains only metas' types after completion
                  <fenv> .Map </fenv>   // <fun> alebo <env> alebo <fenv>
                  <mgu> .Mgu </mgu>
                  <sig> .Map </sig>
                  <ncat> .Map </ncat>
                  <metavars> .Map </metavars>   // <meta>   --- mozno uplne zmazat?
                  <metadata>                    // <md> [?]
                    <range> .K </range>
                  </metadata>
                  <funtenvs> .Map </funtenvs>   // <fctx>  (mozno spravit <fun> <env>..</env> <ctx>..</ctx> </fun> ?)
                </T>
endmodule
