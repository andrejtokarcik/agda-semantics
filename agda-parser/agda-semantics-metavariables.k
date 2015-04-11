require "agda-semantics-common.k"

module AGDA-SEMANTICS-METAVARIABLES
  imports AGDA-SEMANTICS-COMMON

  rule <k> $metavar => E ...</k>
       <tenv>... . => E |-> T ...</tenv>
       <metavars>... . => E |-> t(E, T) ...</metavars>
    when fresh(E:Expr) andBool fresh(T:Expr)


  syntax MetaVariable
  //rule isMetaVariable(#symName(_)) => true
  rule isMetaVariable(#symExpr(_)) => true
  //syntax Variable ::= MetaVariable
  // presupposed that Nf < Whnf < Expr holds
  syntax Nf ::= MetaVariable

  /*
  rule <k> E:MetaVariable => t(E, T) ...</k>
       <tenv> Gamma (. => E |-> T) </tenv>
       <metavars>... . => E |-> t(E, T) ...</metavars>
    when notBool (E in keys(Gamma)) andBool fresh(T:Expr)
  */

  /*
  // if Name was based on Variable, the Name rule from -typesystem.k would be sufficient
  rule <k> E:MetaVariable => t(E, T) ...</k>
       <tenv>... E |-> T ...</tenv>
  */

  // FIXME: teraz vobec nevyuzivam Variable, takze si mozno budem musiet zadefinovat
  // aj sam vlastne freeVariables(), aby to fungovalo spravne
  syntax Set ::= freeVariablesM(K)    [function]   // free vars without metas
  rule freeVariablesM(K) => removeMetas(freeVariables(K))  [structural]
  syntax Set ::= removeMetas(Set)  [function]
  rule removeMetas(.Set) => .Set   [structural]
  rule removeMetas(SetItem(_:MetaVariable) S:Set => S)  [structural]
  rule removeMetas(SetItem(E:Expr) S:Set => S) (. => SetItem(E))  [owise, structural]

  // Metavariables should be always substituted *for*, not vice versa.
  // The LHS of eqn() below gets replaced with the RHS -- swap the sides
  // when necessary.
  rule eqns((eqn(E:Expr,,H:MetaVariable) => eqn(H,,E)),,_)   [structural, anywhere]

  // TODO: swap accordingly when one of the metavariables is more specified than
  // (i.e., a subsort of the other).  e.g., #symExpr(_) should be replaced with #symVariable(_),
  // never the other way around...
endmodule
