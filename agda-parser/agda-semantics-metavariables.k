require "agda-semantics-common.k"

module AGDA-SEMANTICS-METAVARIABLES
  imports AGDA-SEMANTICS-COMMON

  rule <k> %underscore => E ...</k>
       <tenv>... . => E |-> T ...</tenv>
       <metavars>... . => E |-> t(E, T) ...</metavars>
    when fresh(E:Expr) andBool fresh(T:Expr)   // hack with .Map


  syntax MetaVariable
  rule isMetaVariable(#symExpr(_)) => true
  syntax Whnf ::= MetaVariable

  syntax Set ::= freeVariablesM(K)    [function]   // free vars without metas
  rule freeVariablesM(K) => removeMetas(freeVariables(K))  [structural]
  syntax Set ::= removeMetas(Set)  [function]
  rule removeMetas(.Set) => .Set   [structural]
  rule removeMetas(SetItem(_:MetaVariable) S:Set => S)  [structural]
  rule removeMetas(SetItem(E:Expr) S:Set => S) (. => SetItem(E))  [owise, structural]

  // Metavariables should be always substituted *for*, not vice versa.
  // The LHS of eqn() below gets replaced with the RHS: swapping the sides
  // when necessary.
  rule eqns((eqn(E:Expr,,#symExpr(I)) => eqn(#symExpr(I),,E)),,_)
    when getKLabel(E) =/=KLabel #symExpr /* <=> isMetaVariable(E) =/=K true*/  [structural, anywhere]
  //rule eqns((eqn(X:Variable,,#symVariable(I)) => eqn(#symVariable(I),,X)),,_)
  //  when getKLabel(X) =/=KLabel #symVariable  [structural, anywhere]
  //rule eqns((eqn(#symExpr(I),,#symVariable(J)) => eqn(#symVariable(J),,#symExpr(I))),,_)  [structural, anywhere]
endmodule
