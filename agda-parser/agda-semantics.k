require "agda-semantics-typesystem.k"
require "agda-semantics-decl-data.k"
require "agda-semantics-decl-fun.k"

module AGDA-SEMANTICS
  imports AGDA-SEMANTICS-TYPESYSTEM
  imports AGDA-SEMANTICS-DECL-DATA
  imports AGDA-SEMANTICS-DECL-FUN

  syntax KResult ::= TypedExpr

  rule module N Tel where Decls => Decls
  //rule postulate Sig => Sig

  // TODO: attributes: s/type-sig/postulate/ ?
  context postulate _ : (HOLE => checkSetType(HOLE))   [infer-type-sig, result(SetTypedExpr)]
  rule [process-type-sig]:
       <k> postulate N : t(E, Set(_)) => . ...</k>
       //<ncat> NCat (. => Name(F) |-> Fun(F)) </ncat>
       <sig> Sigma (. => N |-> E) </sig>
    when notBool (N in keys(Sigma)) andBool isUniverse(E) =/=K true
    //when notBool (Name(F) in keys(NCat))
  rule <k> postulate Name(N) : t(E, Set(_)) => . ...</k>
       <ncat> NCat (. => Name(N) |-> Data(N)) </ncat>
       <sig>... . => Data(N) |-> E ...</sig>
    when notBool (Name(N) in keys(NCat)) andBool isUniverse(E) ==K true
endmodule
