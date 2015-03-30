require "agda-syntax.k"
require "agda-semantics.k"

// TODO: closures (@Fun) as well as metadata wrappers by passing
// cell fragments as in kool-typed-dynamic.k

module AGDA
  imports AGDA-SYNTAX
  imports AGDA-SEMANTICS

  // sequentialise a comma-separated list anytime it gets on top
  rule '_`,_(D,, Ds) => D ~> Ds           [structural]
  rule '.List`{"`,"`}(.KList) => .        [structural]

  // metadata bureaucracy
  syntax K ::= m(MetadataCellFragment, K)
             | m(MetadataCellFragment)
  rule m(R:Range, K) => m(<range> R </range>, K)  [macro]
  rule <k> m(M, K) => K ~> m(M') ...</k>
       <metadata> M' => M </metadata>   [structural]
  rule <k> _:KResult ~> m(M') => . ...</k>
       <metadata> _ => M' </metadata>   [structural]

  configuration <T>
                  <k> $PGM:Program </k>
                  <tenv> .Map </tenv>
                  <fenv> .Map </fenv>
                  <metadata>
                    <range> .K </range>
                  </metadata>
                </T>
endmodule
