require "modules/substitution.k"
require "agda-semantics-common.k"

module AGDA-SEMANTICS-NORMAL
  imports AGDA-SEMANTICS-DECL-FUN  // for debug

  imports SUBSTITUTION
  imports AGDA-SEMANTICS-COMMON

  syntax WhNeut
  rule isWhNeut(_:Variable) => true
  // most notably, Fun's are not accepted
  rule isWhNeut(Data(_)) => true
  rule isWhNeut(Con(_)) => true
  rule isWhNeut(_:WhNeut _:Expr) => true
  syntax Whnf ::= "(" Whnf ")" [bracket]
                | WhNeut
  rule isWhnf(Set(_)) => true
  rule isWhnf({_:Whnf}) => true
  rule isWhnf((_ : _) -> _) => true
  rule isWhnf({_ : _} -> _) => true
  rule isWhnf(\ (_ : _) -> _) => true
  rule isWhnf(\ {_ : _} -> _) => true
  
  syntax Expr ::= Whnf

  syntax WhnfTypedExpr
  rule isWhnfTypedExpr(t(_, _:Whnf)) => true
  syntax TypedExpr ::= WhnfTypedExpr

  syntax SetTypedExpr
  rule isSetTypedExpr(t(_, Set(_))) => true
  syntax WhnfTypedExpr ::= SetTypedExpr

  syntax Bool ::= cond8(Expr)  [function]
  rule cond8(Fun("thmPlusZero") _) => true

  syntax KItem ::= whnfType(Expr)  [strict, context(result(WhnfTypedExpr))]
  context whnfType(t(E, HOLE => whnf(HOLE))) when cond8(E) [result(Whnf)]
  context whnfType(t(E, HOLE => whnf(HOLE))) when cond8(E) =/=K true [result(Whnf)]


  syntax KItem ::= whnf(Expr)                   [context(result(Whnf))]
  context whnf({HOLE => whnf(HOLE)})            [result(Whnf)]
  //context whnf((_ : (HOLE => whnf(HOLE))) -> _)  [result(Whnf)]
  //context whnf({_ : (HOLE => whnf(HOLE))} -> _)  [result(Whnf)]
  //context whnf(\ (_ : (HOLE => whnf(HOLE))) -> _)  [result(Whnf)]
  //context whnf(\ {_ : (HOLE => whnf(HOLE))} -> _)  [result(Whnf)]

  context whnf((HOLE => whnf(HOLE)) _)   [result(Whnf)]
    //when isFunClauses(leftmost(HOLE)) =/=K true   [result(Whnf)]
    //orElseBool numArgs(HOLE) +Int 1 >Int numReqArgs(leftmost(HOLE))   [result(Whnf)]

  // (Fun ( Name ( "thmPlusZero" ) ) Con ( Name ( "zero" ) )) , ((Fun ( Name ( "_==_" ) ) ((Fun ( Name ( "plus" ) ) Con ( Name ( "zero" ) ) ) Con ( Name ( "zero" ) ))) Con ( Name ( "zero" ) ))
  syntax Bool ::= cond3(Expr)  [function]
  rule cond3(Aux(Fun("_==_"))) => true
  //rule whnf(E => chich ~> E) when cond3(E)

  rule <k> whnf(N => Nc) ...</k>  <ncat>... N |-> Nc ...</ncat>
  rule <k> whnf(F => E) ...</k>   <fenv>... F |-> E ...</fenv>  when cond3(F) =/=K true
  rule <k> whnf(F => E) ...</k>   <fenv>... F |-> E ...</fenv>  when cond3(F)


  rule whnf((\ (X : _) -> E1) E2 => E1[E2/X])
    when isImplicit(E2) =/=K true

  rule whnf((\ {X : _} -> E1) {E2} => E1[E2/X])

  /*
  rule <k> whnf((\ {X : T} -> E) V => ((\ {X : T} -> E) {%underscore}) V) ...</k>
    when isImplicit(V) =/=K true
  */

  context whnf(E (HOLE => whnf(HOLE)))
    when isFunClauses(leftmost(E)) /*andThenBool lengthList(args(E)) <Int numReqArgs(leftmost(E))*/ andThenBool notBool matches(leftmost(E), E HOLE)   [result(Whnf)]

  syntax Bool ::= condd(Expr)  [function]
  rule condd(_ E) => E =/=K Con("zero")

  // TODO: musim vediet konkretizovat argumenty pre pattern-matching funkcie.
  // proste to rozvetvit podla konstruktorov a ocheckovat ze to plati pre vsetky moznosti...

  rule whnf(E => matchClause(leftmost(E), freshFunName(E), leftmost(E), freshFunName(E)))
    when condd(E) andThenBool isFunClauses(leftmost(E)) andThenBool matches(leftmost(E), E) //andThenBool lengthList(args(E)) ==Int numReqArgs(leftmost(E))
  rule whnf(E => matchClause(leftmost(E), freshFunName(E), leftmost(E), freshFunName(E)))
    when notBool condd(E) andThenBool isFunClauses(leftmost(E)) andThenBool matches(leftmost(E), E) //andThenBool lengthList(args(E)) ==Int numReqArgs(leftmost(E))


  syntax FunClauses ::= FunClauses(Int, List)
  syntax Expr ::= FunClauses
  // isWhnf(E:Expr) would generate a sort memebership check,
  // leading to an infinite cycle because of Expr ::= Whnf
  rule isWhnf(E) => true
    when isFunClauses(leftmost(E)) /*andThenBool lengthList(args(E)) <Int numReqArgs(leftmost(E))*/ andThenBool allWhnf(args(E)) andThenBool notBool matches(leftmost(E), E)

  syntax Bool ::= matches(FunClauses, Expr)  [function]
  rule matches(FunClauses(_, .List), _) => false
  rule matches(FunClauses(_, ListItem(L = _) _), E) => true  when isMatching(L, E)
  rule matches(FunClauses(_, _ Cs:List => Cs), _)  [owise]

  syntax Expr ::= matchClause(FunClauses, Expr, Expr, Expr)  [function]
  rule matchClause(FunClauses(_, .List), _, E1, E2) => E1 ~> E2 ~> error("nay matchin' cap'n")
  rule matchClause(FunClauses(_, ListItem(L = R) _), E, _, _) => R[getMatching(L, E)]  when isMatching(L, E)
  rule matchClause(FunClauses(_, _ Cs:List => Cs), _, _, _)  [owise]

  syntax Int ::= numReqArgs(FunClauses)  [function]
  rule numReqArgs(FunClauses(I, _)) => I

  syntax Bool ::= allWhnf(List)   [function]
  rule allWhnf(.List) => true
  rule allWhnf(ListItem(_:Whnf) L) => true  when allWhnf(L)
endmodule
