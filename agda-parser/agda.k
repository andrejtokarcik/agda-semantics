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
  // TODO: then use #tokenToString() when printing range
  syntax K ::= m(MetadataCellFragment, K)
             | m(MetadataCellFragment)
  rule [R:Range] K => m(<range> R </range>, K)  [macro]
  rule <k> m(M, K) => K ~> m(M') ...</k>
       <metadata> M' => M </metadata>   [structural]
  //rule <k> _:KResult ~> m(M') => . ...</k>
  //     <metadata> _ => M' </metadata>   [structural]
  rule <k> m(M') => . ...</k>
       <metadata> _ => M' </metadata>   [structural]

  configuration <T>
                  <k> $PGM:Program </k>
                  <tenv> .Map </tenv>
                  <fenv> .Map </fenv>
                  <mgu> .Mgu </mgu>
                  <sig> .Map </sig>    // zlucit do <tenv>?
                  <metavars> .Map </metavars>
                  <metadata>
                    <range> .K </range>
                  </metadata>
                  <funtenv> .Map </funtenv>
                </T>
endmodule
