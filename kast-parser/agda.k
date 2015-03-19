require "modules/unification.k"
require "modules/substitution.k"
require "agda-syntax.k"
require "agda-semantics.k"

module AGDA
  imports UNIFICATION
  imports SUBSTITUTION
  imports AGDA-SYNTAX
  imports AGDA-SEMANTICS

  // XXX:
  //   syntax KResult ::= Whnf2ExprT
  syntax KResult ::= ExprT

  syntax KItem ::= parseProgram(Program) [function]
  rule parseProgram(.Program) => .
  rule parseProgram(D:Decl ; P:Program) => D ~> parseProgram(P)

  configuration <T color="yellow">
                  <k color="green"> parseProgram($PGM:Program) </k>
                  <data color="violet"> .Map </data>   // signatures
                  <fun color="cyan"> .Map </fun>       // XXX: use .MyMap instead?
                  <tenv color="red"> .Map </tenv>
                  <meta color="black"> .Map </meta>
                  <mgu color="blue"> .Mgu </mgu>
                  //<orig> $PGM </orig>
                </T>
                //<out stream="stdout"> .List </out>

  // Run with `krun --output none`, cf. kool-typed-static.k
  /*
  rule (<T>... <k> .K </k> <mgu> _:Mgu </mgu> ...</T> => .)
       <out>... . => ListItem("Type checked!\n") </out>
    [structural]
  */
endmodule
