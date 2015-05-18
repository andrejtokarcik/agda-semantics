require "agda-semantics-typesystem.k"
require "agda-semantics-decl-data.k"
require "agda-semantics-decl-fun.k"

module AGDA-SEMANTICS
  imports AGDA-SEMANTICS-TYPESYSTEM
  imports AGDA-SEMANTICS-DECL-DATA
  imports AGDA-SEMANTICS-DECL-FUN

  syntax KResult ::= TypedExpr

  // sequentialise any whitespace-separated list that gets on top
  // (don't I want to deal with declaration lists *only*?)
  rule 'Cons(D,, Ds) => D ~> Ds           [structural]
  rule '.List`{""`}(.KList) => .          [structural]

  rule module N Tel where Decls => Decls
  //rule postulate Sig => Sig

  // TODO: attributes: s/type-sig/postulate/ ?
  context postulate _ : (HOLE => checkSetType(HOLE))   [infer-type-sig, result(SetTypedExpr)]
  //context postulate _ : t(HOLE => whnf(HOLE), _)       [result(Whnf)]
  rule [process-type-sig]:
       <k> postulate N : t(E, Set(_)) => . ...</k>
       //<k> (. => block 3000) ~> postulate N : t(E, Set(_)) ...</k>
       //<ncat> NCat (. => Name(F) |-> Fun(F)) </ncat>
       <sig> Sigma (. => N |-> renameBoundVariables(E)) </sig>
    when notBool (N in keys(Sigma))
endmodule
