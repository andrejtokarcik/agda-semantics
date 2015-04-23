require "modules/unification.k"
require "agda-semantics-common.k"

module AGDA-SEMANTICS-UNIFICATION
  imports UNIFICATION
  imports AGDA-SEMANTICS-COMMON

  // Not every updateMgu is actually guaranteed to update the mgu;
  // e.g. if T is identical to T', <mgu /> content remains the same.

  syntax KItem ::= Expr "==" Expr | Expr "#==" Expr
  rule E == E' => nf(E) #== nf(E')
  rule <k> nf(E) #== E' => nf(applyMgu(Theta, E)) ~> HOLE #== E' ...</k>
       <mgu> Theta </mgu>
  rule nf(E) ~> HOLE #== E' => E #== E'  when isNf(E)
  rule <k> E #== nf(E') => nf(applyMgu(Theta, E')) ~> E #== HOLE ...</k>
       <mgu> Theta </mgu>
  rule nf(E') ~> E #== HOLE => E #== E'  when isNf(E')
  rule <k> E #== E' => . ...</k>
       <mgu> Theta => updateMgu(Theta, E, E') </mgu>
    when getKLabel(E) =/=KLabel 'nf andBool getKLabel(E') =/=KLabel 'nf

  syntax KItem ::= "unifyConf"
  rule R:KResult ~> unifyConf => unifyConf ~> R  [structural]
  rule <k> unifyConf => . ...</k>
       <sig> Sigma => applyMgu(Theta, Sigma) </sig>
       <tenv> Gamma => applyMguKeys(Theta, Gamma) </tenv>
       <tenvRestore> TEnvR => applyMguKeysL(Theta, TEnvR) </tenvRestore>
       <fenv> Rho => applyMgu(Theta, Rho) </fenv>
       <metavars> Meta => applyMgu(Theta, Meta) </metavars>
       <mgu> Theta => .Mgu </mgu>
    when isMguError(Theta) =/=K true

  syntax KItem ::= unify(K)
  rule <k> unify(K:K) => applyMgu(Theta, K) ...</k>
       <mgu> Theta </mgu>

  /*
  syntax MetaVariable
  rule isMetaVariable(K) => true  when getKLabel(K) ==KLabel #symExpr
  // it holds that Variable ::= MetaVariable  (i.e., #symExpr's are also Variable)
  */

  syntax List ::= applyMguKeysL(Mgu, List)   [function]
  rule applyMguKeysL(Theta, .List) => .List
  rule applyMguKeysL(Theta, _ (ListItem(m(TEnv)) => .List)) (.List => ListItem(m(applyMguKeys(Theta, TEnv))))

  syntax Map ::= applyMguKeys(Mgu, Map)  [function]
  rule applyMguKeys(_, .Map) => .Map
  rule applyMguKeys(Theta, _ (K |-> V => .Map)) (.Map => (K |-> applyMgu(Theta, V)) (applyMgu(Theta, K) |-> applyMgu(Theta, V)))
    when isVariable(K) andThenBool isVariable(applyMgu(Theta, K)) andThenBool applyMgu(Theta, K) =/=K K
  rule applyMguKeys(Theta, _ (K |-> V => .Map)) (.Map => K |-> applyMgu(Theta, V))  [owise]

  // The LHS of eqn() below gets replaced with the RHS: swapping the sides
  // when necessary.
  // - Metavariables should be always substituted *for*, not vice versa.
  rule eqns((eqn(K,,#symExpr(I)) => eqn(#symExpr(I),,K)),,_)
    when getKLabel(K) =/=KLabel #symExpr  [structural, anywhere]
  //rule eqns((eqn(K,,K') => .KList),,_)
  //  when isVariable(K) andBool isVariable(K')  [structural, anywhere]

  rule eqns((eqn(X:Variable,,#symVariable(I)) => eqn(#symVariable(I),,X)),,_)
    when getKLabel(X) =/=KLabel #symVariable  [structural, anywhere]
  //rule eqns((eqn(#symExpr(I),,#symVariable(J)) => eqn(#symVariable(J),,#symExpr(I))),,_)  [structural, anywhere]

endmodule
