require "agda-semantics-common.k"

module AGDA-SEMANTICS-NORMAL
  imports AGDA-SEMANTICS-COMMON

  syntax WhNeut
  rule isWhNeut(_:Variable) => true
  rule isWhNeut(_:Name) => true
  rule isWhNeut(_:WhNeut _:Expr) => true
  syntax Whnf ::= "(" Whnf ")" [bracket]
                | WhNeut
  rule isWhnf(Set(_)) => true
  rule isWhnf({_:Whnf}) => true
  rule isWhnf((_ : _) -> _) => true
  rule isWhnf({_ : _} -> _) => true     // AT FIXME hack - generalise
  rule isWhnf(\ (_ : _) -> _) => true
  rule isWhnf(\ {_ : _} -> _) => true
  
  syntax Expr ::= Whnf

  syntax WhnfTypedExpr
  rule isWhnfTypedExpr(t(_, _:ValWhnf)) => true
  syntax TypedExpr ::= WhnfTypedExpr

  syntax SetTypedExpr
  rule isSetTypedExpr(t(_, Set(_))) => true
  syntax WhnfTypedExpr ::= SetTypedExpr

  syntax ValWhnf ::= Universe   // so that it can be parsed in rules
  rule isValWhnf(V) => true when isWhnf(deval(V))
  syntax Val ::= ValWhnf


  syntax KItem ::= whnfType(K) [strict, context(result(WhnfTypedExpr))]
  context whnfType(t(_, HOLE => whnf(HOLE)))  [result(ValWhnf)]

  syntax KItem ::= whnf(Val)      [context(result(ValWhnf))]
  context whnf((HOLE::Val => whnf(HOLE)) E)
    when isFunClauses(leftmost(HOLE)) =/=K true orElseBool numArgs(HOLE) +Int 1 >Int numReqArgs(leftmost(HOLE))   [result(ValWhnf)]

  rule isFEnvRestore(whnf(_:ValWhnf)) => true
  rule <k> whnf((\ (X : _) -> E:Expr)@Rho' V:Val => E@(Rho'[Rho[V/X]])) ~> (. => fenv(Rho)) ...</k>
       <fenv> Rho </fenv>
    when isImplicit(deval(V)) =/=K true

  rule <k> whnf((\ {X : _} -> E1:Expr)@Rho1 {E2}@Rho2 => E1@(Rho1[Rho[E2@Rho2/X]])) ~> (. => fenv(Rho)) ...</k>
       <fenv> Rho => Rho[E2@Rho2/X] </fenv>

  /*
  rule <k> whnf((\ {X : T} -> E)@Rho' V => ((\ {X : T} -> E)@Rho' {%underscore}@Rho) V) ...</k>
       <fenv> Rho </fenv>
    when isImplicit(deval(V)) =/=K true
  */

  rule <k> whnf(V => matchClause(leftmost(V), deval(V), gatherClosures(V))) ~> (. => fenv(Rho)) ...</k>
       <fenv> Rho </fenv>  when isFunClauses(leftmost(V))


  syntax Int ::= numArgs(Expr)  [function]
  rule numArgs(E _) => numArgs(E) +Int 1
  rule numArgs(_) => 0   [owise]

  syntax FunClauses ::= FunClauses(Int, List)    // need wrapper around List
  syntax Expr ::= FunClauses
  rule isFunClauses(_:FunClauses@_) => true

  syntax Int ::= numReqArgs(FunClauses)  [function]
  rule numReqArgs(FunClauses(I, _)) => I

  syntax Map ::= gatherClosures(Val)  [function]
  rule gatherClosures(V1 V2) => gatherClosures(V1) gatherClosures(V2)
  rule gatherClosures(E@Rho) => Rho
  rule gatherClosures(E) => .Map  [owise]

  // TODO: ked sa zoznam vo FunClauses zredukuje na .List (t.j. nenasli sme match) a zaroven uz nie vo V co skonkretizovat tak daj error
  syntax Val ::= matchClause(Val, Expr, Map)  [function]
  //rule matchClause(FunClauses(_, .List)@_, _, _) => Name("(T)ERROR")
  rule matchClause(FunClauses(_, ListItem(L = R) _)@Rho, E, Rho') => R@(Rho[Rho'[getMatching(L, E)]])  when isMatching(L, E)
  rule matchClause(FunClauses(_, _ Cs:List => Cs)@_, _, _)  [owise]

  syntax Expr ::= deval(Val)  [function]
  rule deval(V1 V2) => deval(V1) deval(V2)
  rule deval(E@_) => E
  rule deval(E) => E  [owise]
endmodule
