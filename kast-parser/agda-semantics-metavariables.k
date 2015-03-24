require "agda-syntax.k"
require "agda-semantics-normal.k"

module AGDA-SEMANTICS-METAVARIABLES
  imports AGDA-SYNTAX
  imports AGDA-SEMANTICS-NORMAL

  // kvoli tomuto to NEcykli
  syntax KItem ::= "Mmm"
  rule <k> ? => (E, T) ...</k>
       <meta>... . => E |-> (E, T) ...</meta>
       <tenv>... . => E |-> T ...</tenv>
    when fresh(E:Expr) andBool fresh(T:Expr)


  // XXX: the #sym*(_) things appear to be part of Variable, i.e. the E:SymExpr rule isn't necessary
  // -- it's handled already in the base typesystem when matching on Variables!
  // -- commenting out the following rule

  // WAAT? was E => Et
  /*
  rule <k> E:SymExpr => (E, Et) ...</k>
       <meta>... E |-> Et ...</meta>
    //when isSymExpr(E)
  */

  // NOTE: is*() functions are assumed to correspond to syntax sorts;
  // in builtins/k-equal.k they use it as a Bool function too

  //syntax Bool ::= isSymExpr(Expr) [function]
  // XXX: veci z builtins/smt.k (e.g. collectConstants()) by tiez mohli byt relevantne k SymExpr
  syntax SymExpr
  rule isSymExpr(#symExpr(_)) => true
  //syntax Expr ::= SymExpr
  //syntax Whnf ::= SymExpr
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
