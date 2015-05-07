require "agda-syntax.k"
require "agda-semantics-unification.k"
require "agda-semantics-normal.k"

module AGDA-SEMANTICS-COMMON
  imports AGDA-SYNTAX
  imports AGDA-SEMANTICS-UNIFICATION
  imports AGDA-SEMANTICS-NORMAL

  syntax KItem ::= "chich"

  syntax TypedExpr ::= t(Expr, Expr)    [latex(\ktyped{#1}{#2})]    // the down arrow would indicate a type-*inference* result
  syntax Expr ::= TypedExpr

  syntax Name ::= Data(Identifier) | Con(Identifier) | Fun(Identifier) | Postulate(Identifier)

  syntax CtxLoader
  rule isCtxLoader(_:KResult) => true
  /*
  syntax KItem ::= ctx(Map)
  rule R:CtxLoader ~> ctx(Gamma) => ctx(Gamma) ~> R  [structural]
  rule <k> ctx(Gamma) => . ...</k>
       <ctx> _ => Gamma </ctx>
  */
  syntax KItem ::= saveCtx(Map) | "loadCtx"
  rule <k> saveCtx(Gamma) => . ...</k>
       <ctxstack> L => ListItem(m(Gamma)) L </ctxstack>
  rule R:CtxLoader ~> loadCtx => loadCtx ~> R  [structural]
  rule <k> loadCtx => . ...</k>
       <ctx> _ => Gamma </ctx>
       <ctxstack> ListItem(m(Gamma)) L => L </ctxstack>

  syntax KItem ::= "pass?" | error(String)
  syntax GuardPass
  rule isGuardPass(true) => true
  rule _:GuardPass ~> pass? => .

  syntax KItem ::= "cleanMetas"
  rule <k> cleanMetas => . ...</k>
       <meta> _ => .Map </meta>

  // perform unification in order to obtain a universe type
  syntax KItem ::= checkSetType(Expr)  [strict(all(context('whnfType))), context(result(SetTypedExpr))]
  rule checkSetType(t(E, T)) => T == Set(Alpha) ~> unify(t(E, T)) ~> unifyConf ~> checkSetType(HOLE)
    when isSetTypedExpr(t(E, T)) =/=K true andBool fresh(Alpha:Int)
  rule Te:SetTypedExpr ~> checkSetType(HOLE) => checkSetType(Te)

  syntax KItem ::= tsubst(Map)
  rule <k> t(E, T) ~> tsubst(M) => t(E, T[applyMguKeys(Theta, M)]) ...</k>
       <mgu> Theta </mgu> [structural]


  /* General auxiliary functions. */

  syntax K ::= leftmost(Expr)  [function]
  rule leftmost(E _ => E) [structural]
  rule leftmost(E) => E   [owise, structural]

  syntax Expr ::= replaceLeftmost(Expr, Expr)  [function]
  rule replaceLeftmost(E E', R) => replaceLeftmost(E, R) E'
  rule replaceLeftmost(_, R) => R    [owise]

  syntax List ::= args(Expr)  [function]
  rule args(E E') => args(E) ListItem(E')
  rule args(_) => .List [owise]

  syntax Bool ::= all(KLabel, List)  [function]
  rule all(Pred, .List) => true      [structural]
  rule all(Pred, ListItem(K) L) => Pred(K) ==K true andBool all(Pred, L)  [structural]
  syntax Bool ::= any(KLabel, List)  [function]
  rule any(Pred, .List) => false     [structural]
  rule any(Pred, ListItem(K) L) => Pred(K) ==K true orBool any(Pred, L)   [structural]

  // if length of the given list is less than the desired number,
  // the whole list is returned
  syntax List ::= take(Int, List)    [function]
  rule take(_, .List) => .List
  rule take(0, _) => .List
  rule (.List => ListItem(K)) take(I => I -Int 1, (ListItem(K) => .List) _)   [owise]

  syntax K ::= head(List)   [function]
  rule head(ListItem(K) _) => K

  // wrappers for containers (that do not belong to sort K)
  // NOTE: module K-WRAPPERS-LABELS in k-prelude.k seems to provide similar functionality
  syntax K ::= l(List)   [latex({#1})]
  syntax List ::= unl(K) [function]
  rule unl(l(L)) => L  [structural]
  syntax K ::= m(Map)    [latex({#1})]
  syntax Map ::= unm(K)  [function]
  rule unm(m(M)) => M  [structural]
endmodule
