//require "agda-syntax-pretty.k"
require "agda-semantics-common.k"
require "agda-semantics-typesystem.k"
require "agda-semantics-decl-data.k"

module AGDA-SEMANTICS
  //imports AGDA-SYNTAX-PRETTY
  imports AGDA-SEMANTICS-COMMON
  imports AGDA-SEMANTICS-TYPESYSTEM
  imports AGDA-SEMANTICS-DECL-DATA

  rule module N Tel where Decls => Decls
  rule postulate Sig => Sig

  context _ : (HOLE => whnfType(HOLE))  //[result(TypedType)]
  rule <k> N : t(E, Set(_)) => . ...</k>
       <sig>... . => N |-> E ...</sig>



  //rule isExpr(_:LHS) => true
  //rule isLHS(_:TypedExpr) => true
  //syntax TypedRHS ::= t(RHS, Expr)
  //syntax RHS ::= TypedRHS
  //syntax TypedExpr ::= TypedLHS //| TypedRHS

  /*
  syntax Map ::= loadTelescope(Map, Expr) [function]
  rule loadTelescope(Sigma, (X : T) -> E) => (X |-> T) loadTelescope(Sigma, E)
  rule loadTelescope(Sigma, _) => Sigma [owise]

  rule <k> (. => bound!) ~> L = _ ~> (. => sig(Sigma)) </k>
       <sig> Sigma => loadTelescope(Sigma, Sigma(leftMost(L))) </sig>
  context bound! ~> HOLE = _
  context bound! ~> _ = HOLE
  */

  syntax Name ::= funName(LHS)  [function]
  rule funName(L) => leftmost(L)

  syntax KItem ::= autoVarTypes(LHS)
  rule autoVarTypes(P1 P2) => autoVarTypes(P1) ~> autoVarTypes(P2)
  /*
  rule <k> autoVarTypes(X:Name) => . ...</k>
       <sig> Sigma </tenv>
    when X in keys(Sigma)
  rule <k> autoVarTypes(X:Name) => . ...</k>
       <sig> Sigma (. => X |-> T) </tenv>
    when notBool (X in keys(Sigma)) andBool fresh(T:Expr)
  */
  rule autoVarTypes(_:Name) => .
  rule <k> autoVarTypes(X:Variable) => . ...</k>
       <tenv> Gamma </tenv>
    when X in keys(Gamma)
  rule <k> autoVarTypes(X:Variable) => . ...</k>
       <tenv> Gamma (. => X |-> T) </tenv>
    when notBool (X in keys(Gamma)) andBool fresh(T:Expr)


  rule <k> L:LHS = R:Expr => autoVarTypes(L) ~> bound! ~> L = R ...</k>
       <tenv> Gamma </tenv>
       <sig> Sigma (. => funName(L) |-> T) </sig>
    when notBool (funName(L) in keys(Sigma)) andBool fresh(T:Expr)
  rule <k> L:LHS = R:Expr => autoVarTypes(L) ~> bound! ~> L = R ...</k>
       <tenv> Gamma </tenv>
       <sig> Sigma </sig>
    when funName(L) in keys(Sigma)

  /*
  context HOLE = _     // FIXME: whnfType or something
  context _ = HOLE
  rule <k> t(L, Tl) = t(R, Tr) => Tl == Tr ~> unify ...</k>
       <fenv>... . => L |-> R ...</fenv>   // << ako kluc chcem mat len fun name, kvoli partial application
                                         // ALTERNATIVA: ale asi by slo vymysliet, zeby som si vytvaral fresh funkcie
                                         // co by len lambda abstrakciou zaobalili tu pattern matching funkciu
                                         // (typu map = \a -> \b -> map a b spolu s pattern-matching-based definiciami mapu)
                                         // vyhol by som sa takto tomu fun() konstruktu
                                         // kazdopadne, <fenv /> by potom musel byt list (lebo nas zaujima poradie
                                         // fun klauzuli v orig kode) a nie map
  */
endmodule
