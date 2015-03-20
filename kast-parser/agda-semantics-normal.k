require "modules/substitution.k"
require "agda-syntax.k"
require "agda-semantics-decl-fun.k"    // FIXME

module AGDA-SEMANTICS-NORMAL
  imports SUBSTITUTION
  imports AGDA-SYNTAX
  imports AGDA-SEMANTICS-DECL-FUN

  // TODO: move into agda-syntax-common.k or something
  syntax ExprT ::= (Expr, Expr)
  syntax Expr ::= ExprT

  syntax Whnf ::= "(" Whnf ")" [bracket]
                | WhNeut
                | Universe
                | "Pi" Variable Expr Expr [binder(1 -> 3)]
                | "Lambda" Variable Expr Expr [binder(1 -> 3)]
  syntax WhNeut ::= Name
                  | WhNeut Whnf [left]
  syntax Expr ::= Whnf

  // XXX: why not Whnf2ExprT ::= (Expr, Whnf)  actually?
  syntax Whnf2ExprT
  rule isWhnf2ExprT((_:Expr, _:Whnf)) => true
  syntax ExprT ::= Whnf2ExprT

  syntax K ::= whnf(Expr)                   [context(result(Whnf))]

  syntax K ::= whnf2(Expr)                  [strict, context(result(Whnf2ExprT))]
  context whnf2((_, (HOLE => whnf(HOLE))))  [result(Whnf)]

  syntax Whnf21ExprT
  rule isWhnf21ExprT((_:Whnf, _:Whnf)) => true
  syntax Whnf2ExprT ::= Whnf21ExprT

  syntax K ::= whnf2eval1(Expr)            [strict(all(context('whnf2))), context(result(Whnf21ExprT))]
  context whnf2eval1(((HOLE => eval(HOLE)), _:Whnf))   [result(Whnf)]

  syntax Nf ::= "(" Nf ")" [bracket]
                | Neut
                | Universe
                | "Pi" Variable Nf Nf [binder(1 -> 3)]
                | "Lambda" Variable Nf Nf [binder(1 -> 3)]
  syntax Neut ::= Name
                | Variable   // FIXME?
                | Neut Nf [left]
  //syntax Whnf ::= Nf     // this spoils Whnf because of the Variable production in Neut above

  /*
  syntax Nf2ExprT
  rule isNf2ExprT((_:Expr, _:Nf)) => true
  syntax Whnf2ExprT ::= Nf2ExprT
  */

  syntax K ::= nf(Expr)                   [strict(all(context('whnf))), context(result(Nf))]
  context nf(Pi _ (HOLE => nf(HOLE)) _)   [result(Nf)]
  context nf(Pi _ _ (HOLE => nf(HOLE)))   [result(Nf)]
  context nf(Lambda _ (HOLE => nf(HOLE)) _)   [result(Nf)]
  context nf(Lambda _ _ (HOLE => nf(HOLE)))   [result(Nf)]
  context nf((HOLE => nf(HOLE)) _:Expr)   [result(Nf)]
  context nf(_:Expr (HOLE => nf(HOLE)))   [result(Nf)]

  /*
  syntax K ::= nf2(Expr)                [strict, context(result(Nf2ExprT))]
  context nf2((_, (HOLE => nf(HOLE))))  [result(Nf)]
  */

  syntax TypeT
  rule isTypeT((_:Expr, _:Universe)) => true
  //syntax Nf2ExprT ::= TypeT
endmodule
