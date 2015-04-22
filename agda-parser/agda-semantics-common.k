require "modules/pattern-matching.k"
require "agda-syntax.k"
require "agda-semantics-unification.k"
require "agda-semantics-normal.k"

module AGDA-SEMANTICS-COMMON
  imports PATTERN-MATCHING
  imports AGDA-SYNTAX
  imports AGDA-SEMANTICS-UNIFICATION
  imports AGDA-SEMANTICS-NORMAL

  syntax KItem ::= "chich"

  syntax TypedExpr ::= t(Expr, Expr)    [latex(({#1}\downarrow{#2}))]    // XXX this would indicate a type-*inference* result
  syntax Expr ::= TypedExpr

  syntax Name ::= Data(Name) | Con(Name) | Fun(Name)

  syntax TEnvRestore
  rule isTEnvRestore(_:TypedExpr) => true
  syntax KItem ::= tenv(Map)
  rule <k> tenv(Gamma) => . ...</k>
       <tenv> _ => Gamma </tenv>
  rule R:TEnvRestore ~> tenv(Gamma) => tenv(Gamma) ~> R

  syntax GuardPass
  rule isGuardPass(true) => true
  syntax KItem ::= "pass?"
  rule _:GuardPass ~> pass? => .

  syntax KItem ::= checkSetType(Expr)  [strict(all(context('whnfType))), context(result(SetTypedExpr))]
  rule checkSetType(t(E, T)) => T == Set(I) ~> unify(t(E, T)) ~> checkSetType(HOLE)
    when isSetTypedExpr(t(E, T)) =/=K true andBool fresh(I:Int)
  rule Te:SetTypedExpr ~> checkSetType(HOLE) => checkSetType(Te)

  syntax K ::= leftmost(Expr)  [function]
  rule leftmost(E _ => E) [structural]
  rule leftmost(E) => E   [owise, structural]

  syntax KItem ::= tsubst(Map)
  rule t(E, T:Expr) ~> tsubst(M) => t(E, T[M])  [structural]
endmodule
