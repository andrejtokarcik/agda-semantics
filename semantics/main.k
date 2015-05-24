require "modules/substitution.k"
require "modules/unification.k"
require "./common.k"
require "./normal.k"
require "./typesystem.k"
require "./unification.k"
require "./declarations/main.k"

module AGDA-SEMANTICS
  imports AGDA-SEMANTICS-TYPESYSTEM
  imports AGDA-SEMANTICS-DECLARATIONS

  syntax KResult ::= TypedExpr

  // Sequentialise declarations as they get to the top.
  rule D ; Ds => D ~> Ds  [structural]
  rule .Declarations => . [structural]
  // The whole program is wrapped in an additional list for some reason...
  rule '.List`{""`}(.KList) => . [structural]

  rule module N Tel where Decls => Decls
  rule postulate Sig => Sig

  context _ : (HOLE => checkSetType(HOLE))    [infer-type-sig, result(SetTypedExpr)]
  rule [process-type-sig]:
       <k> N : t(E, Set(_)) => . ...</k>
       <sig> Sigma (. => N |-> renameBoundVariables(E)) </sig>
    when notBool (N in keys(Sigma))
endmodule
