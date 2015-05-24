module AGDA-SEMANTICS-NORMAL
  imports SUBSTITUTION
  imports AGDA-SEMANTICS-COMMON
  imports AGDA-SEMANTICS-UNIFICATION
  imports AGDA-SEMANTICS-DECLARATIONS-FUNCTIONS

  syntax Neut
  rule isNeut(_:Variable) => true
  rule isNeut(_:MetaVariable) => true
  // note that Fun's are not listed among the neutral terms
  rule isNeut(Data(_)) => true
  rule isNeut(Con(_)) => true
  rule isNeut(Postlt(_)) => true
  rule isNeut(_:Neut _:Nf) => true
  syntax Nf ::= "(" Nf ")"  [bracket]
              | Neut
  rule isNf(Set(_)) => true
  rule isNf({_:Nf}) => true
  rule isNf(DotP(_:Nf)) => true
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

  syntax KItem ::= nf(Expr)                    [strict(all(context('whnf))), context(result(Nf))]
  context nf({HOLE => nf(HOLE)})               [result(Nf)]
  context nf(_::Expr (HOLE => nf(HOLE)))       [result(Nf)]
  context nf((HOLE => nf(HOLE)) _::Nf)         [result(Nf)]
  context nf((_ : (HOLE => nf(HOLE))) -> _)    [result(Nf)]
  context nf((_ : _) -> (HOLE => nf(HOLE)))    [result(Nf)]
  context nf({_ : (HOLE => nf(HOLE))} -> _)    [result(Nf)]
  context nf({_ : _} -> (HOLE => nf(HOLE)))    [result(Nf)]
  context nf(\ (_ : (HOLE => nf(HOLE))) -> _)  [result(Nf)]
  context nf(\ (_ : _) -> (HOLE => nf(HOLE)))  [result(Nf)]
  context nf(\ {_ : (HOLE => nf(HOLE))} -> _)  [result(Nf)]
  context nf(\ {_ : _} -> (HOLE => nf(HOLE)))  [result(Nf)]

  context nf(FunClauses(_, 'fc(_,,((HOLE => nf(HOLE)) = _),,_)))  [result(Nf)]

  rule <k> nf(E) =>
           renameVariablesConf(suitableLHS(Theta,
                  leftmost(getFunClausesAppPattern(Theta, leftmost(E), E)), unhide(args(E)(indexOfFunClausesAppPattern(Theta, leftmost(E), E)))
           )) ~> unhide(getFunClausesAppPattern(Theta, leftmost(E), E)) #== HOLE ~>
           unify(nf(E)) ~> killMgu
       ...</k>
       <mgu> Theta </mgu>
    when isFunClausesApp(E) andBool lengthList(args(E)) ==Int numReqArgs(leftmost(E)) andBool notBool matches(leftmost(E), E) andBool
         indexOfFunClausesAppPattern(Theta, leftmost(E), E) >=Int 0 andBool
         isVariable(unhide(args(E)(indexOfFunClausesAppPattern(Theta, leftmost(E), E)))) =/=K true andBool
         getKLabel(suitableLHS(Theta, leftmost(getFunClausesAppPattern(Theta, leftmost(E), E)), unhide(args(E)(indexOfFunClausesAppPattern(Theta, leftmost(E), E))))) =/=KLabel 'suitableLHS

  syntax FunClausesApp ::= getFunClausesAppPattern(Mgu, FunClauses, Expr)  [function]
  rule getFunClausesAppPattern(Theta, FunClauses(_, 'fc((L = _),, _)), E) => args(L)(index(isFunClausesApp, args(L)))
    when any(isFunClausesApp, args(L)) andBool
         notBool canUnify(Theta, args(L)(index(isFunClausesApp, args(L))), args(E)(index(isFunClausesApp, args(L))))
  rule getFunClausesAppPattern(_, FunClauses(_, 'fc((_ = _ => .KList),, _)), _)  [owise]

  syntax Int ::= indexOfFunClausesAppPattern(Mgu, FunClauses, Expr)  [function]
  rule indexOfFunClausesAppPattern(Theta, FunClauses(_, 'fc((L = _),, _)), E) => index(isFunClausesApp, args(L))
    when any(isFunClausesApp, args(L)) andBool
         notBool canUnify(Theta, args(L)(index(isFunClausesApp, args(L))), args(E)(index(isFunClausesApp, args(L))))
  rule indexOfFunClausesAppPattern(_, FunClauses(_, 'fc((_ = _ => .KList),, _)), _)  [owise]


  syntax KItem ::= whnfType(Expr)               [strict, context(result(WhnfTypedExpr))]
  context whnfType(t(_, HOLE => whnf(HOLE)))    [result(Whnf)]

  syntax KItem ::= whnf(Expr)                   [context(result(Whnf))]
  context whnf({HOLE => whnf(HOLE)})            [result(Whnf)]
  context whnf((HOLE => whnf(HOLE)) _)          [result(Whnf)]

  rule <k> whnf(N => Nc) ...</k>  <ncat>... N |-> Nc ...</ncat>
  rule <k> whnf(Name(N)) ...</k>
       <ncat> NCat (. => Name(N) |-> Postlt(N)) </ncat>
       <sig>... (Name(N) => Postlt(N)) |-> _ ...</sig>
    when notBool Name(N) in keys(NCat)
  rule <k> whnf(F => replaceInaccessible(FunClauses(F, E))) ...</k>   <fun>... F |-> E ...</fun>
    when getKLabel(E) ==KLabel 'fc
  rule <k> whnf(F => renameVariables(E)) ...</k>   <fun>... F |-> E ...</fun>
    when getKLabel(E) =/=KLabel 'fc

  rule <k> whnf(<E, LocalSigs, LocalFuns> => E) ~> (. => localData(LocalSigs, LocalFuns)) ...</k>
       <fun> Rho => Rho[LocalFuns] </fun>
  rule (. => localNames(keys(LocalSigs))) ~> whnf(W:Whnf => <W, LocalSigs, LocalFuns>) ~> (localData(LocalSigs, LocalFuns) => .)  [structural]

  rule whnf((\ (X : _) -> E1) E2 => E1[E2/X])
    when isImplicit(E2) =/=K true

  rule whnf((\ {X : _} -> E1) {E2} =>  E1[E2/X])

  context whnf(HOLE => nf(HOLE))
    when isFunClausesApp(HOLE) andBool lengthList(args(HOLE)) <=Int numReqArgs(leftmost(HOLE))   [result(Nf)]

  rule whnf(E => matchClause(leftmost(E), E))
    when isFunClausesApp(E) andBool lengthList(args(E)) ==Int numReqArgs(leftmost(E)) andBool matches(leftmost(E), E)


  // you don't want FunClauses as WhNeut:
  // isWhnf(E:Expr) would generate a sort memebership check,
  // leading to an infinite cycle because of Expr ::= Whnf
  rule isNf(E) => true
    when isFunClausesApp(E) andBool all(isNf, args(E)) andBool
          ((lengthList(args(E)) <Int numReqArgs(leftmost(E))) orBool
           (hasNfPatterns(leftmost(E)) andBool notBool matches(leftmost(E), subExpr(numReqArgs(leftmost(E)), E))))

  syntax Bool ::= hasNfPatterns(FunClauses)   [function]
  rule hasNfPatterns(FunClauses(_, 'fc(.KList))) => true
  rule hasNfPatterns(FunClauses(F, 'fc(L = _,, Cs))) => all(isNf, args(L)) andBool hasNfPatterns(FunClauses(F, 'fc(Cs)))

  // We distinguish between a mismatch and inconclusive matching --- by attempting to unify.
  syntax Bool ::= matches(FunClauses, Expr)  [function]
  rule matches(FunClauses(_, 'fc(.KList)), _) => false
  rule matches(FunClauses(_, 'fc((L = _),, _)), E) => true    when isMatching(L, unhide(E))
  rule matches(FunClauses(_, 'fc((L = _),, Cs)), E) => false  when notBool isMatching(L, unhide(E)) andBool canUnify(renameVariables(L), unhide(E)) andBool anotherCanUnify(Cs, unhide(E))
  rule matches(FunClauses(_, 'fc((L = _),, Cs)), E) => true   when notBool isMatching(L, unhide(E)) andBool canUnify(renameVariables(L), unhide(E)) andBool notBool anotherCanUnify(Cs, unhide(E))
  rule matches(FunClauses(_, 'fc((_ = _ => .KList),, _)), _)  [owise]

  syntax Bool ::= anotherCanUnify(KList, Expr)  [function]
  rule anotherCanUnify(.KList, _) => false
  rule anotherCanUnify(((L = _),, _), E) => true  when canUnify(renameVariables(L), E)
  rule anotherCanUnify(((_ = _ => .KList),, _), _)  [owise]

  syntax Expr ::= matchClause(FunClauses, Expr)   [function]
                | #unifyClause(K, LHS, Expr, RHS) [function]
  rule matchClause(FunClauses(_, 'fc((L = R),, _)), E) => R[getMatching(L, unhide(E))]  when isMatching(L, unhide(E))
  rule matchClause(FunClauses(_, 'fc((L = R),, _)), E) => #unifyClause(getAlpha(L), L, unhide(E), R)
    when notBool isMatching(L, unhide(E)) andBool canUnify(renameVariables(L), unhide(E))
  rule matchClause(FunClauses(_, 'fc((_ = _ => .KList),, _)), _)  [owise]
  rule #unifyClause(Alpha, L, E, R) => unifyRightNow(applySubst(Alpha, L), E, applySubst(Alpha, R))


  syntax FunClauses ::= replaceInaccessible(FunClauses)  [function]
  syntax FunClause ::= replaceInaccessible(FunClause)    [function]
  syntax LHS ::= replaceInaccessible(LHS)                [function]
  rule replaceInaccessible(FunClauses(F, 'fc(Cs))) => FunClauses(F, 'fc(map('replaceInaccessible, Cs)))
  rule replaceInaccessible(L = R) => renameVariables(replaceInaccessible(L) = R)
  rule replaceInaccessible(L P) => replaceInaccessible(L) replaceInaccessible(P)
  rule replaceInaccessible({P}) => {replaceInaccessible(P)}
  rule replaceInaccessible(DotP(P)) => E  when fresh(E:Expr)
  rule replaceInaccessible(L:LHS) => L   [owise]
endmodule
