require "agda-syntax.k"
require "agda-semantics-normal.k"

module AGDA-SEMANTICS-METAVARIABLES
  imports AGDA-SYNTAX
  imports AGDA-SEMANTICS-NORMAL

  syntax Bool ::= isSymExpr(Expr) [function]
  rule isSymExpr(#symExpr(_)) => true
  //rule isSymExpr(#symWhnf(_)) => true
  //rule isSymExpr(#symNf(_)) => true

  rule isWhnf(#symExpr(_)) => true
  rule isNf(#symExpr(_)) => true

  rule <k> ? => (E, T) ...</k>
       <meta>... . => E |-> (E, T) ...</meta>
    when fresh(E:Expr) andBool fresh(T:Expr)

  rule <k> E => Et ...</k>
       <meta>... E |-> Et ...</meta>
    when isSymExpr(E)

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
