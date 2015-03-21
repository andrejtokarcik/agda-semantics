require "agda-syntax.k"
require "agda-semantics-normal.k"

module AGDA-SEMANTICS-METAVARIABLES
  imports AGDA-SYNTAX
  imports AGDA-SEMANTICS-NORMAL

  rule <k> ? => (E, T) ...</k>
       <meta>... . => E |-> (E, T) ...</meta>
    when fresh(E:Expr) andBool fresh(T:Expr)

  // WAAT? was E => Et
  rule <k> E:SymExpr => (E, Et) ...</k>
       <meta>... E |-> Et ...</meta>
    //when isSymExpr(E)

  // NOTE: is*() functions are assumed to correspond to syntax sorts
  //syntax Bool ::= isSymExpr(Expr) [function]
  syntax SymExpr
  rule isSymExpr(#symExpr(_)) => true
  //syntax Expr ::= SymExpr
  syntax Whnf ::= SymExpr
  //syntax Nf ::= SymExpr // is Nf a subsort of Whnf already?
  //rule isSymExpr(#symWhnf(_)) => true
  //rule isSymExpr(#symNf(_)) => true

  /*
  rule isWhnf(#symExpr(_)) => true
  rule isNf(#symExpr(_)) => true
  */
  /*
  rule isWhnf(_:SymExpr) => true
  rule isNf(_:SymExpr) => true
  */

  syntax Expr ::= leftMost(Expr) [function]
  rule leftMost(E:Expr _:Expr) => leftMost(E)
  rule leftMost(E:Expr) => E [owise] 

  // TODO: make it more formal in accordance with Norell's thesis, guarded constants etc.
  // (only given eta-equality for function spaces)
  rule eqns((eqn((E1:Expr E2:Expr),,E':Expr) => eqn(E1,,Lambda X T E')),,_)
    when isSymExpr(leftMost(E1)) andBool fresh(X:Variable) andBool fresh(T:Expr)   [anywhere]
  rule eqns(E':Expr,,(eqn((E1:Expr E2:Expr)) => eqn(E1,,Lambda X T E')),,_)
    when isSymExpr(leftMost(E1)) andBool fresh(X:Variable) andBool fresh(T:Expr)   [anywhere]
endmodule
