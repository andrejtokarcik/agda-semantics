require "modules/substitution.k"
require "agda-semantics-common.k"

module AGDA-SEMANTICS-NORMAL
  imports AGDA-SEMANTICS-DECL-FUN  // for debug

  imports SUBSTITUTION
  imports AGDA-SEMANTICS-COMMON


  syntax Neut
  rule isNeut(_:Variable) => true
  // most notably, Fun's are not accepted
  rule isNeut(Data(_)) => true
  rule isNeut(Con(_)) => true
  rule isNeut(_:Neut _:Nf) => true
  syntax Nf ::= "(" Nf ")"  [bracket]
              | Neut
  rule isNf(Set(_)) => true
  rule isNf({_:Nf}) => true
  rule isNf((_ : _:Nf) -> _:Nf) => true
  rule isNf({_ : _:Nf} -> _:Nf) => true
  rule isNf(\ (_ : _:Nf) -> _:Nf) => true
  rule isNf(\ {_ : _:Nf} -> _:Nf) => true

  syntax WhNeut ::= Neut
  rule isWhNeut(_:WhNeut _:Expr) => true
  syntax Whnf ::= "(" Whnf ")" [bracket]
                | WhNeut
                | Nf
  rule isWhnf({_:Whnf}) => true
  rule isWhnf((_ : _) -> _) => true
  rule isWhnf({_ : _} -> _) => true
  rule isWhnf(\ (_ : _) -> _) => true
  rule isWhnf(\ {_ : _} -> _) => true

  syntax Expr ::= Whnf

  syntax NfTypedExpr
  rule isNfTypedExpr(t(_, _:Nf)) => true
  syntax WhnfTypedExpr ::= NfTypedExpr
  rule isWhnfTypedExpr(t(_, _:Whnf)) => true
  syntax TypedExpr ::= WhnfTypedExpr

  syntax SetTypedExpr
  rule isSetTypedExpr(t(_, Set(_))) => true
  syntax NfTypedExpr ::= SetTypedExpr


  syntax KItem ::= nf(Expr)                   [strict(all(context('whnf))), context(result(Nf))]
  context nf({HOLE => nf(HOLE)})             [result(Nf)]
  context nf((HOLE => nf(HOLE)) _)           [result(Nf)]
  context nf(_::Expr (HOLE => nf(HOLE)))           [result(Nf)]
  context nf((_ : (HOLE => nf(HOLE))) -> _)  [result(Nf)]
  context nf((_ : _) -> (HOLE => nf(HOLE)))  [result(Nf)]
  context nf({_ : (HOLE => nf(HOLE))} -> _)  [result(Nf)]
  context nf({_ : _} -> (HOLE => nf(HOLE)))  [result(Nf)]
  context nf(\ (_ : (HOLE => nf(HOLE))) -> _)  [result(Nf)]
  context nf(\ (_ : _) -> (HOLE => nf(HOLE)))  [result(Nf)]
  context nf(\ {_ : (HOLE => nf(HOLE))} -> _)  [result(Nf)]
  context nf(\ {_ : _} -> (HOLE => nf(HOLE)))  [result(Nf)]


  syntax Bool ::= cond8(Expr)  [function]
  rule cond8(Fun("thmPlusZero") _) => true

  syntax KItem ::= whnfType(Expr)  [strict, context(result(WhnfTypedExpr))]
  context whnfType(t(E, HOLE => whnf(HOLE))) when cond8(E) [result(Whnf)]
  context whnfType(t(E, HOLE => whnf(HOLE))) when cond8(E) =/=K true [result(Whnf)]


  syntax KItem ::= whnf(Expr)                   [context(result(Whnf))]
  context whnf({HOLE => whnf(HOLE)})            [result(Whnf)]

  context whnf((HOLE => whnf(HOLE)) _)   [result(Whnf)]
    //when isFunClauses(leftmost(HOLE)) =/=K true   [result(Whnf)]
    //orElseBool numArgs(HOLE) +Int 1 >Int numReqArgs(leftmost(HOLE))   [result(Whnf)]

  syntax Bool ::= cond3(Expr)  [function]
  //rule cond3(Aux(Fun("_==_"))) => true
  //rule whnf(E => chich ~> E) when cond3(E)

  rule <k> whnf(N => Nc) ...</k>  <ncat>... N |-> Nc ...</ncat>
  rule <k> whnf(F => E) ...</k>   <fenv>... F |-> E ...</fenv>  when cond3(F) =/=K true
  rule <k> whnf(F => E) ...</k>   <fenv>... F |-> E ...</fenv>  when cond3(F)


  rule whnf((\ (X : _) -> E1) E2 => E1[E2/X])
    when isImplicit(E2) =/=K true

  rule whnf((\ {X : _} -> E1) {E2} => E1[E2/X])

  // is this insertion already performed in -typesystem?
  /*
  rule <k> whnf((\ {X : T} -> E) V => ((\ {X : T} -> E) {%underscore}) V) ...</k>   // %underscore isn't expanded in whnf
    when isImplicit(V) =/=K true
  */

  /*
  context whnf(E (HOLE => whnf(HOLE)))
    when isFunClauses(leftmost(E)) andBool lengthList(args(E HOLE)) <=Int numReqArgs(leftmost(E)) andBool notBool matches(leftmost(E), E HOLE)   [result(Whnf)]
  */
  context whnf(HOLE => nf(HOLE))
    when isFunClauses(leftmost(HOLE)) andBool lengthList(args(HOLE)) <=Int numReqArgs(leftmost(HOLE))  [result(Nf)]


  syntax Bool ::= condd(Expr)  [function]
  rule condd(_ E) => E =/=K Con("zero")

  // TODO: odstran tie posledne dva argumenty z matchClause
  rule whnf(E => matchClause(leftmost(E), E))
    when condd(E) andThenBool isFunClauses(leftmost(E)) andThenBool matches(leftmost(E), E) //andThenBool lengthList(args(E)) ==Int numReqArgs(leftmost(E))
  rule whnf(E => matchClause(leftmost(E), E))
    when notBool condd(E) andThenBool isFunClauses(leftmost(E)) andThenBool matches(leftmost(E), E) //andThenBool lengthList(args(E)) ==Int numReqArgs(leftmost(E))


  // isWhnf(E:Expr) would generate a sort memebership check,
  // leading to an infinite cycle because of Expr ::= Whnf
  //rule isWhNeut(E) => true
  //  when isFunClauses(leftmost(E)) andBool all(isWhnf, take(numReqArgs(leftmost(E)), args(E))) andBool notBool matches(leftmost(E), E)
  rule isNf(E) => true
    when isFunClauses(leftmost(E)) andBool all(isNf, args(E)) andBool notBool matches(leftmost(E), E)

  syntax Bool ::= matches(FunClauses, Expr)  [function]
  rule matches(FunClauses(.List), _) => false
  rule matches(FunClauses(ListItem(L = _) _), E) => true  when isMatching(L, E)
  rule matches(FunClauses(_ Cs:List => Cs), _)  [owise]

  syntax Expr ::= matchClause(FunClauses, Expr)  [function]
  //rule matchClause(FunClauses(.List), _) => error("nay matchin' cap'n")   // FIXME?
  rule matchClause(FunClauses(ListItem(L = R) _), E) => R[getMatching(L, E)]  when isMatching(L, E)
  rule matchClause(FunClauses(_ Cs:List => Cs), _)  [owise]
endmodule
