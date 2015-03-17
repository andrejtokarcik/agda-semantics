require "modules/substitution.k"
require "agda-syntax.k"

module AGDA-SEMANTICS-NORMAL
  imports SUBSTITUTION
  imports AGDA-SYNTAX

  // TODO: move into agda-syntax-common.k or something
  syntax ExprT ::= (Expr, Expr)
  syntax Expr ::= ExprT

  syntax Whnf ::= "(" Whnf ")" [bracket]
                | WhNeut
                | Universe
                | "Pi" Variable Expr Expr [binder]
                | "Lambda" Variable Expr Expr [binder]
  syntax WhNeut ::= Name
                  | WhNeut Whnf [left]
  syntax Expr ::= Whnf

  // XXX: why not Whnf2ExprT ::= (Expr, Whnf)  actually?
  syntax Whnf2ExprT
  rule isWhnf2ExprT((_:Expr, _:Whnf)) => true
  syntax ExprT ::= Whnf2ExprT

  syntax K ::= whnf(Expr)                   [context(result(Whnf))]
  // TODO: (contextual) closures for evaluation
  rule whnf((Lambda X _ E1) E2 => E1[E2/X])
  syntax K ::= whnf2(Expr)                  [strict, context(result(Whnf2ExprT))]
  context whnf2((_, (HOLE => whnf(HOLE))))  [result(Whnf)]

  syntax Whnf21ExprT
  rule isWhnf21ExprT((_:Whnf, _:Whnf)) => true
  syntax Whnf2ExprT ::= Whnf21ExprT

  syntax K ::= whnf21(Expr)            [strict(all(context('whnf2))), context(result(Whnf21ExprT))]
  context whnf21(((HOLE => whnf(HOLE)), _:Whnf))   [result(Whnf)]

  syntax Nf ::= "(" Nf ")" [bracket]
                | Neut
                | Universe
                | "Pi" Variable Nf Nf [binder]
                | "Lambda" Variable Nf Nf [binder]
  syntax Neut ::= Name
                | Variable   // FIXME?
                | Neut Nf [left]
  syntax Whnf ::= Nf

  syntax Nf2ExprT
  rule isNf2ExprT((_:Expr, _:Nf)) => true
  syntax Whnf2ExprT ::= Nf2ExprT

  syntax K ::= nf(Expr)                   [strict(all(context('whnf))), context(result(Nf))]
  context nf(Pi _ (HOLE => nf(HOLE)) _)   [result(Nf)]
  context nf(Pi _ _ (HOLE => nf(HOLE)))   [result(Nf)]
  context nf(Lambda _ (HOLE => nf(HOLE)) _)   [result(Nf)]
  context nf(Lambda _ _ (HOLE => nf(HOLE)))   [result(Nf)]
  context nf((HOLE => nf(HOLE)) _:Expr)   [result(Nf)]
  context nf(_:Expr (HOLE => nf(HOLE)))   [result(Nf)]

  syntax K ::= nf2(Expr)                [strict, context(result(Nf2ExprT))]
  context nf2((_, (HOLE => nf(HOLE))))  [result(Nf)]

  syntax TypeT
  rule isTypeT((_:Expr, _:Universe)) => true
  syntax Nf2ExprT ::= TypeT
endmodule
