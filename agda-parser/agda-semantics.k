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

  syntax Bool ::= cond5(Expr)  [function]
  rule cond5(Name("i")) => true

  context _ : (HOLE => checkSetType(HOLE))   [result(SetTypedExpr)]
  rule <k> N : t(E, Set(_)) => . ...</k>
       <ncat> NCat (. => N |-> Fun(N)) </ncat>
       <sig> Sigma (. => Fun(N) |-> E) </sig>
    when notBool (N in keys(NCat)) andBool cond5(N) ==K true
  rule <k> N : t(E, Set(_)) => . ...</k>
       <ncat> NCat (. => N |-> Fun(N)) </ncat>
       <sig> Sigma (. => Fun(N) |-> E) </sig>
    when notBool (N in keys(NCat)) andBool cond5(N) =/=K true

endmodule
