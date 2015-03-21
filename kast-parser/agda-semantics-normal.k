require "modules/substitution.k"
require "agda-syntax.k"
require "agda-semantics-decl-fun.k"    // FIXME

module AGDA-SEMANTICS-NORMAL
  imports SUBSTITUTION
  imports AGDA-SYNTAX
  imports AGDA-SEMANTICS-DECL-FUN

  // TODO: move into agda-syntax-common.k or something
  syntax ExprT ::= (Expr, Expr)    // syntax: Expr ":" Expr [cf. java-semantics, kde maju ::]
  syntax Expr ::= ExprT

  syntax Whnf ::= "(" Whnf ")" [bracket]
                | WhNeut
                | Universe
                | "Pi" Variable Expr Expr [binder(1 -> 3)]
                | "Lambda" Variable Expr Expr [binder(1 -> 3)]
  syntax WhNeut ::= Name
                  | WhNeut Expr [left]
  syntax Expr ::= Whnf

  // XXX: why not Whnf2ExprT ::= (Expr, Whnf)  actually?
  syntax Whnf2ExprT
  rule isWhnf2ExprT((_:Expr, _:Whnf)) => true
  syntax ExprT ::= Whnf2ExprT

  // TODO, what result context to use, when Val < Expr, ValWhnf < Whnf, etc.?
  // rename Whnf -> ExprWhnf and then set Whnf ::= ExprWhnf,
  // whnf context to have ExprWhnf as result

  //syntax K ::= whnf(Expr)                   [strict(all(context('eval))), context(result(Whnf))]
  //rule whnf(V:ValWhnf => unval(V))         // << TODO ^ implement unval here directly
  syntax K ::= whnf(Expr)                     [context(result(Whnf))]
  context whnf((HOLE:Expr => whnf(HOLE)) _) [result(Whnf)]
  rule whnf((Lambda X _ E1) E2 => E1[E2/X])


  syntax K ::= whnf2(Expr)                  [strict, context(result(Whnf2ExprT))]
  context whnf2((_, (HOLE => whnf(HOLE))))  [result(Whnf)]

  syntax K ::= eval2(Expr)                  [strict, context(result(ValWhnf2ExprT))] //superheat]
  context eval2((_, HOLE => eval(HOLE)))    [result(ValWhnf)] //superheat]
  //rule eval2((_, E => stripNeut(E)))  when isNeutlessExpr(E) =/=K true
  //context eval2((_, HOLE => eval(HOLE)))  when isNeutlessExpr(HOLE) ==K true   [result(Whnf)]
  /*
  rule <k> eval2((E, T)) => eval(T) ~> (E, HOLE) ~> fenv(Fun) ...</k>
       <fun> Fun </fun>   when isValWhnf(T) =/=K true
  rule eval(T) ~> (E, HOLE) => (E, T)  when isValWhnf(T) ==K true
  */

  syntax Whnf21ExprT
  rule isWhnf21ExprT((_:Whnf, _:Whnf)) => true
  syntax Whnf2ExprT ::= Whnf21ExprT


  syntax K ::= whnf21(Expr)            [strict(all(context('whnf2))), context(result(Whnf21ExprT))]
  context whnf21(((HOLE => whnf(HOLE)), _:Whnf))   [result(Whnf)]

  /*
  syntax K ::= whnf2eval1(Expr)            [strict(all(context('whnf2))), context(result(Whnf21ExprT))]
  context whnf2eval1(((HOLE => eval(HOLE)), _:Whnf))   [result(Whnf)]
  */
  syntax K ::= eval21(Expr)            [strict(all(context('eval2))), context(result(ValWhnf21ExprT))]
  context eval21(((HOLE => eval(HOLE)), _:ValWhnf))   [result(ValWhnf)]


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
  context nf((HOLE:Expr => nf(HOLE)) _:Expr)   [result(Nf)]
  context nf(_:Expr (HOLE:Expr => nf(HOLE)))   [result(Nf)]

  /*
  syntax K ::= nf2(Expr)                [strict, context(result(Nf2ExprT))]
  context nf2((_, (HOLE => nf(HOLE))))  [result(Nf)]
  */

  syntax TypeT
  rule isTypeT((_:Expr, _:Universe)) => true
  //syntax Nf2ExprT ::= TypeT
endmodule
