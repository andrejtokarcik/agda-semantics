require "agda-semantics-common.k"
require "agda-semantics-typesystem.k"
require "agda-semantics-decl-data.k"
require "agda-semantics-decl-fun.k"

module AGDA-SEMANTICS
  imports AGDA-SEMANTICS-COMMON
  imports AGDA-SEMANTICS-TYPESYSTEM
  imports AGDA-SEMANTICS-DECL-DATA
  imports AGDA-SEMANTICS-DECL-FUN

  syntax KResult ::= TypedExpr


  rule module N Tel where Decls => Decls
  rule postulate Sig => Sig

  context _ : (HOLE => checkSetType(HOLE))   [result(SetTypedExpr)]
  rule <k> N : t(E, Set(_)) => . ...</k>
       <sig> Sigma (. => N |-> E@Rho) </sig>
       <fenv> Rho </fenv>
    when notBool (N in keys(Sigma))
endmodule
