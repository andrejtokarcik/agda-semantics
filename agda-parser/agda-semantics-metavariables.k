require "agda-semantics-common.k"

module AGDA-SEMANTICS-METAVARIABLES
  imports AGDA-SEMANTICS-COMMON

  rule <k> %underscore => E ...</k>
       <tenv>... . => E |-> T@Rho ...</tenv>
       <metavars>... . => E |-> t(E, T@Rho) ...</metavars>
       <fenv> Rho </fenv>
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
  // The LHS of eqn() below gets replaced with the RHS -- swap the sides
  // when necessary.
  rule eqns((eqn(E:Expr,,H:MetaVariable) => eqn(H,,E)),,_)
    when isMetaVariable(E) =/=K true  [structural, anywhere]

  // TODO: swap accordingly when one of the metavariables is more specified than
  // (i.e., a subsort of the other).  e.g., #symExpr(_) should be replaced with #symVariable(_),
  // never the other way around...
endmodule
