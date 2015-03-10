require "modules/unification.k"
require "modules/substitution.k"
require "agda-syntax.k"
require "agda-semantics.k"

module AGDA
  imports UNIFICATION
  imports SUBSTITUTION
  imports AGDA-SYNTAX
  imports AGDA-SEMANTICS

  syntax KResult ::= ExprT

  syntax KItem ::= parseProgram(Program) [function]
  rule parseProgram(expr = E:Expr) => E
  rule parseProgram(D:DataDecl P:Program) => D ~> parseProgram(P)

  configuration <k color="green"> parseProgram($PGM:Program) </k>
                <tenv color="red"> .Map </tenv>
                <data> .Map </data>   // signatures
                <meta> .Map </meta>
                <mgu color="blue"> .Mgu </mgu>
                //<orig> $PGM </orig>

  // a separate tag <solution /> as in logik.k?
  /*
  syntax KItem ::= "Solution" ExprT [strict(all(context('nf2)))]
  rule <k> S:ExprT => Solution S </k>
  */
  rule <k> T:ExprT => nf2(T) </k>
endmodule
