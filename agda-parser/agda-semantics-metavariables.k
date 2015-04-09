require "agda-semantics-common.k"

module AGDA-SEMANTICS-METAVARIABLES
  imports AGDA-SEMANTICS-COMMON

  syntax MetaVariable
  rule isMetaVariable(#symName(_)) => true
  rule isMetaVariable(#symExpr(_)) => true
  // presupposed that Nf < Whnf < Expr holds
  syntax Nf ::= MetaVariable

  rule <k> E:MetaVariable => t(E, T) ...</k>
       <tenv> Gamma (. => E |-> T) </tenv>
       <metavars>... . => E |-> t(E, T) ...</metavars>
    when notBool (E in keys(Gamma)) andBool fresh(T:Expr)

  // if Name was based on Variable, the Name rule from -typesystem.k would be sufficient
  rule <k> E:MetaVariable => t(E, T) ...</k>
       <tenv>... E |-> T ...</tenv>

  // FIXME: teraz vobec nevyuzivam Variable, takze si mozno budem musiet zadefinovat
  // aj sam vlastne freeVariables(), aby to fungovalo spravne
  syntax Set ::= freeVariablesM(K)    [function]   // free vars without metas
  rule freeVariablesM(K) => removeMetas(freeVariables(K))  [structural]
  syntax Set ::= removeMetas(Set)  [function]
  rule removeMetas(.Set) => .Set   [structural]
  rule removeMetas(SetItem(_:MetaVariable) S:Set => S)  [structural]
  rule removeMetas(SetItem(E:Expr) S:Set => S) (. => SetItem(E))  [owise, structural]
endmodule
