require "agda-semantics-typesystem.k"
require "agda-semantics-decl-data.k"
require "agda-semantics-decl-fun.k"

module AGDA-SEMANTICS
  imports AGDA-SEMANTICS-TYPESYSTEM
  imports AGDA-SEMANTICS-DECL-DATA
  imports AGDA-SEMANTICS-DECL-FUN

  syntax KResult ::= TypedExpr

  // sequentialise declarations as they get to the top
  rule D ; Ds => D ~> Ds  [structural]
  rule .Declarations => . [structural]
  // the whole program is wrapped in an additional list for some reason...
  rule '.List`{""`}(.KList) => . [structural]

  rule module N Tel where Decls => Decls
  rule postulate Sig => Sig

  context _ : (HOLE => checkSetType(HOLE))   [infer-type-sig, result(SetTypedExpr)]
  //context postulate _ : t(HOLE => whnf(HOLE), _)       [result(Whnf)]
  rule [process-type-sig]:
       <k> N : t(E, Set(_)) => . ...</k>
       //<k> (. => block 3000) ~> postulate N : t(E, Set(_)) ...</k>
       //<ncat> NCat (. => Name(F) |-> Fun(F)) </ncat>
       <sig> Sigma (. => N |-> renameBoundVariables(E)) </sig>
    when notBool (N in keys(Sigma))
endmodule
