require "agda-syntax.k"
require "agda-semantics.k"

module AGDA
  imports AGDA-SYNTAX
  imports AGDA-SEMANTICS

  // sequentialise a comma-separated list anytime it gets on top
  rule '_`,_(D,, Ds) => D ~> Ds           [structural]
  rule '.List`{"`,"`}(.KList) => .        [structural]
  // this last rule not necessary, helps readability
  //rule _ ~> ('.List`{"`,"`}(.KList) => .)     [structural]

  /*
  syntax KItem ::= parseDeclarationL(DeclarationL) [function]
  rule parseDeclarationL(.DeclarationL) => .
  rule parseDeclarationL((D:Declaration , Ds:DeclarationL)) => D ~> parseDeclarationL(Ds)
  */

  syntax KItem ::= updateMetaData(MetaData)
  rule m(M:MetaData, K:K) => updateMetaData(M) ~> K [structural]
  rule <k> updateMetaData(R:Range) => . ...</k>
       <metadata> <range> _ => R </range> </metadata> [structural]

  configuration
    <k> $PGM:Program </k>
    <ctx> .Map </ctx>
    <sig> .Map </sig>
    <metadata>
      <range> .K </range>
    </metadata>
endmodule
