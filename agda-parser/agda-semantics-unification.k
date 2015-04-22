require "modules/unification.k"
require "agda-semantics-common.k"

module AGDA-SEMANTICS-UNIFICATION
  imports UNIFICATION
  imports AGDA-SEMANTICS-COMMON

  // Not every updateMgu is actually guaranteed to update the mgu;
  // e.g. if T is identical to T', <mgu /> content remains the same.
  syntax KItem ::= Expr "==" Expr
  rule <k> E == E' => . ...</k>
       <mgu> Theta => updateMgu(Theta, E, E') </mgu>

  syntax KItem ::= "unify"
  rule <k> unify => . ...</k>
       <sig> Sigma => applyMgu(Theta, Sigma) </sig>
       <tenv> Gamma => applyMguKeys(Theta, applyMgu(Theta, Gamma)) </tenv>
       <fenv> Rho => applyMgu(Theta, Rho) </fenv>
       <metavars> Meta => applyMgu(Theta, Meta) </metavars>
       <mgu> Theta => .Mgu </mgu>
    when isMguError(Theta) =/=K true

  syntax KItem ::= unify(Expr)
  rule <k> unify(E:Expr) => unify ~> applyMgu(Theta, E) ...</k>
       <mgu> Theta </mgu>

  /*
  syntax MetaVariable
  rule isMetaVariable(K) => true  when getKLabel(K) ==KLabel #symExpr
  // it holds that Variable ::= MetaVariable  (i.e., #symExpr's are also Variable)
  */

  syntax Map ::= applyMguKeys(Mgu, Map)  [function]
  rule applyMguKeys(_, .Map) => .Map
  rule applyMguKeys(Theta, (K |-> V => .Map) _) (.Map => (K |-> V) (applyMgu(Theta, K) |-> V))
    when isVariable(K) andThenBool isVariable(applyMgu(Theta, K)) andThenBool applyMgu(Theta, K) =/=K K
  rule applyMguKeys(_, (K |-> V => .Map) _) (.Map => K |-> V)  [owise]

  // The LHS of eqn() below gets replaced with the RHS: swapping the sides
  // when necessary.
  // - Metavariables should be always substituted *for*, not vice versa.
  rule eqns((eqn(K,,#symExpr(I)) => eqn(#symExpr(I),,K)),,_)
    when getKLabel(K) =/=KLabel #symExpr  [structural, anywhere]
  //rule eqns((eqn(K,,K') => .KList),,_)
  //  when isVariable(K) andBool isVariable(K')  [structural, anywhere]

  //rule eqns((eqn(X:Variable,,#symVariable(I)) => eqn(#symVariable(I),,X)),,_)
  //  when getKLabel(X) =/=KLabel #symVariable  [structural, anywhere]
  //rule eqns((eqn(#symExpr(I),,#symVariable(J)) => eqn(#symVariable(J),,#symExpr(I))),,_)  [structural, anywhere]

endmodule
