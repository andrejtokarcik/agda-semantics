require "library.k"
require "syntax/main.k"
require "semantics/main.k"

module AGDA
  imports AGDA-SYNTAX
  imports AGDA-SEMANTICS

  configuration <k> $PGM:Program  </k>
                <sig> .Map </sig>
                <ctx> .Map </ctx>
                <ctx-stack> .List </ctx-stack>
                <fun> .Map </fun>
                <meta> .Map </meta>
                <ncat> .Map </ncat>
                <mgu> .Mgu </mgu>
endmodule
