require "library.k"
require "syntax/main.k"
require "semantics/main.k"

module AGDA
  imports AGDA-SYNTAX
  imports AGDA-SEMANTICS

  configuration <k color="green"> $PGM:Program  </k>
                <sig color="blue"> .Map </sig>
                <ctx color="red"> .Map </ctx>
                <ctx-stack color="purple"> .List </ctx-stack>
                <fun color="yellow"> .Map </fun>
                <meta color="cyan"> .Map </meta>
                <ncat color="brown"> .Map </ncat>
                <mgu color="gray"> .Mgu </mgu>
endmodule
