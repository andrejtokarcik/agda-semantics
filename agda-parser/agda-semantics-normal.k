require "modules/substitution.k"
require "agda-semantics-common.k"

module AGDA-SEMANTICS-NORMAL
  imports SUBSTITUTION
  imports AGDA-SEMANTICS-COMMON

  syntax WhNeut
  rule isWhNeut(_:Variable) => true
  // Fun(_) is not accepted
  rule isWhNeut(Data(_)) => true
  rule isWhNeut(Con(_)) => true
  rule isWhNeut(_:WhNeut _:Expr) => true
  syntax Whnf ::= "(" Whnf ")" [bracket]
                | WhNeut
  rule isWhnf(Set(_)) => true
  rule isWhnf({_:Whnf}) => true
  rule isWhnf((_ : _:Whnf) -> _) => true
  rule isWhnf({_ : _:Whnf} -> _) => true
  rule isWhnf(\ (_ : _:Whnf) -> _) => true
  rule isWhnf(\ {_ : _:Whnf} -> _) => true
  
  syntax Expr ::= Whnf

  syntax WhnfTypedExpr
  rule isWhnfTypedExpr(t(_, _:Whnf)) => true
  syntax TypedExpr ::= WhnfTypedExpr

  syntax SetTypedExpr
  rule isSetTypedExpr(t(_, Set(_))) => true
  syntax WhnfTypedExpr ::= SetTypedExpr

  syntax KItem ::= whnfType(Expr)  [strict, context(result(WhnfTypedExpr))]
  context whnfType(t(_, HOLE => whnf(HOLE)))  [result(Whnf)]

  syntax KItem ::= whnf(Expr)                   [context(result(Whnf))]
  context whnf({HOLE => whnf(HOLE)})            [result(Whnf)]
  context whnf((_ : (HOLE => whnf(HOLE))) -> _)  [result(Whnf)]
  context whnf({_ : (HOLE => whnf(HOLE))} -> _)  [result(Whnf)]
  context whnf(\ (_ : (HOLE => whnf(HOLE))) -> _)  [result(Whnf)]
  context whnf(\ {_ : (HOLE => whnf(HOLE))} -> _)  [result(Whnf)]

  context whnf((HOLE => whnf(HOLE)) _)   [result(Whnf)]
    //when isFunClauses(leftmost(HOLE)) =/=K true   [result(Whnf)]
    //orElseBool numArgs(HOLE) +Int 1 >Int numReqArgs(leftmost(HOLE))   [result(Whnf)]

  rule <k> whnf(N => Nc) ...</k>  <ncat>... N |-> Nc ...</ncat>
  rule <k> whnf(F => E) ...</k>   <fenv>... F |-> E ...</fenv>

  rule whnf((\ (X : _) -> E1) E2 => E1[E2/X])
    when isImplicit(E2) =/=K true

  rule whnf((\ {X : _} -> E1) {E2} => E1[E2/X])

  /*
  rule <k> whnf((\ {X : T} -> E) V => ((\ {X : T} -> E) {%underscore}) V) ...</k>
    when isImplicit(V) =/=K true
  */

  rule whnf(E => matchClause(leftmost(E), E))
    when isFunClauses(leftmost(E)) andThenBool numArgs(E) ==Int numReqArgs(leftmost(E))


  syntax FunClauses ::= FunClauses(Int, List)
  syntax Expr ::= FunClauses
  // isWhnf(E:Expr) would generate a sort memebership check,
  // leading to an infinite cycle because of Expr ::= Whnf
  rule isWhnf(E) => true
    when isFunClauses(leftmost(E)) andThenBool numArgs(E) <Int numReqArgs(leftmost(E))

  // TODO: ked sa zoznam vo FunClauses zredukuje na .List (t.j. nenasli sme match) a zaroven uz nie vo V co skonkretizovat tak daj error
  syntax Expr ::= matchClause(Expr, Expr)  [function]
  //rule matchClause(FunClauses(_, .List)@_, _, _) => Name("(T)ERROR")
  rule matchClause(FunClauses(_, ListItem(L = R) _), E) => R[getMatching(L, E)]  when isMatching(L, E)
  rule matchClause(FunClauses(_, _ Cs:List => Cs), _)  [owise]

  syntax Int ::= numArgs(Expr)  [function]
  rule numArgs(E _) => numArgs(E) +Int 1
  rule numArgs(_) => 0   [owise]

  syntax Int ::= numReqArgs(FunClauses)  [function]
  rule numReqArgs(FunClauses(I, _)) => I
endmodule
