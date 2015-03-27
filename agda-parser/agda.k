require "agda-syntax.k"
require "agda-semantics.k"

module AGDA
  imports AGDA-SYNTAX
  imports AGDA-SEMANTICS

  // sequentialise a comma-separated list anytime it gets on top
  rule '_`,_(D,, Ds) => D ~> Ds        [structural]
  rule '.List`{"`,"`}(.KList) => .     [structural]
  // this last rule not necessary, helps readability
  //rule _ ~> ('.List`{"`,"`}(.KList) => .)     [structural]

  /*
  syntax KItem ::= parseDeclarationL(DeclarationL) [function]
  rule parseDeclarationL(.DeclarationL) => .
  rule parseDeclarationL((D:Declaration , Ds:DeclarationL)) => D ~> parseDeclarationL(Ds)
  */

  rule <k> annotated R K => K ...</k>
       <range> _ => R </range> [structural]

  configuration
    <k> $PGM:K </k>
    <ctx> .Map </ctx>
    <range> .K </range>
endmodule
