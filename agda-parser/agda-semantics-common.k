require "agda-syntax.k"
require "agda-semantics-unification.k"
require "agda-semantics-normal.k"

module AGDA-SEMANTICS-COMMON
  imports AGDA-SYNTAX
  imports AGDA-SEMANTICS-UNIFICATION
  imports AGDA-SEMANTICS-NORMAL

  syntax KItem ::= "chich"

  syntax TypedExpr ::= t(Expr, Expr)    [latex(({#1}\downarrow{#2}))]    // the down arrow would indicate a type-*inference* result
  syntax Expr ::= TypedExpr

  syntax Name ::= Data(Identifier) | Con(Identifier) | Fun(Identifier)

  syntax TEnvRestore
  rule isTEnvRestore(_:KResult) => true
  /*
  syntax KItem ::= tenv(Map)
  rule R:TEnvRestore ~> tenv(Gamma) => tenv(Gamma) ~> R  [structural]
  rule <k> tenv(Gamma) => . ...</k>
       <tenv> _ => Gamma </tenv>
  */
  syntax KItem ::= saveTEnv(Map) | "restoreTEnv"
  rule <k> saveTEnv(Gamma) => . ...</k>
       <tenvRestore> L => ListItem(m(Gamma)) L </tenvRestore>
  rule R:TEnvRestore ~> restoreTEnv => restoreTEnv ~> R  [structural]
  rule <k> restoreTEnv => . ...</k>
       <tenv> _ => Gamma </tenv>
       <tenvRestore> ListItem(m(Gamma)) L => L </tenvRestore>

  syntax KItem ::= "pass?" | error(String)
  syntax GuardPass
  rule isGuardPass(true) => true
  rule _:GuardPass ~> pass? => .

  // perform unification in order to obtain a universe type
  syntax KItem ::= checkSetType(Expr)  [strict(all(context('whnfType))), context(result(SetTypedExpr))]
  rule checkSetType(t(E, T)) => T == Set(I) ~> unify(t(E, T)) ~> unifyConf ~> checkSetType(HOLE)
    when isSetTypedExpr(t(E, T)) =/=K true andBool fresh(I:Int)
  rule Te:SetTypedExpr ~> checkSetType(HOLE) => checkSetType(Te)

  syntax K ::= leftmost(Expr)  [function]
  rule leftmost(E _ => E) [structural]
  rule leftmost(E) => E   [owise, structural]

  syntax Expr ::= replaceLeftmost(Expr, Expr)  [function]
  rule replaceLeftmost(E E', R) => replaceLeftmost(E, R) E'
  rule replaceLeftmost(_, R) => R    [owise]

  syntax List ::= args(Expr)  [function]
  rule args(E E') => args(E) ListItem(E')
  rule args(_) => .List [owise]

  syntax KItem ::= tsubst(Map)
  rule <k> t(E, T) ~> tsubst(M) => t(E, T[applyMguKeys(Theta, M)]) ...</k>
       <mgu> Theta </mgu> [structural]

  // wrappers for containers (not of sort K)
  syntax K ::= l(List)
  syntax List ::= unl(K) [function]
  rule unl(l(L)) => L  [structural]
  syntax K ::= m(Map)
  syntax Map ::= unm(K)  [function]
  rule unm(m(M)) => M  [structural]
endmodule
