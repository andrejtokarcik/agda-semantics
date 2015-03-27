require "agda-syntax.k"
require "agda-semantics.k"

module AGDA
  imports AGDA-SYNTAX
  imports AGDA-SEMANTICS

  /*
  rule '.List`{""`}(.KList) => . [structural]
  rule '__(E,, Ls) => E ~> Ls [structural]
  */
  syntax KItem ::= parseDeclarationL(DeclarationL) [function]
  rule parseDeclarationL(.DeclarationL) => .
  rule parseDeclarationL(D:Declaration , Ds:DeclarationL) => D ~> parseDeclarationL(Ds)

  configuration <k> parseDeclarationL($PGM:DeclarationL) </k>
                <tenv> .Map </tenv>
endmodule
