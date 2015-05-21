require "modules/substitution.k"
require "agda-semantics-common.k"
require "agda-semantics-unification.k"
require "agda-semantics-decl-fun.k"

module AGDA-SEMANTICS-NORMAL
  imports SUBSTITUTION
  imports AGDA-SEMANTICS-COMMON
  imports AGDA-SEMANTICS-UNIFICATION
  imports AGDA-SEMANTICS-DECL-FUN

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


  syntax KItem ::= "block" Int
  /*
  rule block _ => .
  rule whnf((block _ => .) ~> _)
  rule nf((block _ => .) ~> _)
  */

  syntax KItem ::= nf(Expr)                   [strict(all(context('whnf))), context(result(Nf))]
  context nf({HOLE => nf(/*block 1 ~>*/ HOLE)})             [result(Nf)]
  context nf(_::Expr (HOLE => nf(/*block 3 ~>*/ HOLE)))           [result(Nf)]
  context nf((HOLE => nf(/*block 2 ~>*/ HOLE)) _::Nf)           [result(Nf)]
  context nf((_ : (HOLE => nf(/*block 4 ~>*/ HOLE))) -> _)  [result(Nf)]
  context nf((_ : _) -> (HOLE => nf(/*block 5 ~>*/ HOLE)))  [result(Nf)]
  context nf({_ : (HOLE => nf(/*block 6 ~>*/ HOLE))} -> _)  [result(Nf)]
  context nf({_ : _} -> (HOLE => nf(/*block 7 ~>*/ HOLE)))  [result(Nf)]
  context nf(\ (_ : (HOLE => nf(/*block 8 ~>*/ HOLE))) -> _)  [result(Nf)]
  context nf(\ (_ : _) -> (HOLE => nf(/*block 9 ~>*/ HOLE)))  [result(Nf)]
  context nf(\ {_ : (HOLE => nf(/*block 10 ~>*/ HOLE))} -> _)  [result(Nf)]
  context nf(\ {_ : _} -> (HOLE => nf(/*block 11 ~>*/ HOLE)))  [result(Nf)]

  context nf(FunClauses(_, 'fc(_,,((HOLE => /*block 15 ~>*/ nf(HOLE)) = _),,_)))  [result(Nf)]

  syntax KItem ::= hold(K) | "xx" LHS
  rule <k> nf(E) => //block 12 ~>
  renameVariablesConf(suitableLHS(Theta,
  leftmost(getFunClausesAppPattern(Theta, leftmost(E), E)), unhide(args(E)(indexOfFunClausesAppPattern(Theta, leftmost(E), E))),
  leftmost(getFunClausesAppPattern(Theta, leftmost(E), E))
  )) ~> unhide(getFunClausesAppPattern(Theta, leftmost(E), E)) #== HOLE ~> 
  
/*
xx suitableLHS(Theta,
  leftmost(getFunClausesAppPattern(Theta, leftmost(E), E)), unhide(args(E)(indexOfFunClausesAppPattern(Theta, leftmost(E), E))), Set(0)) ~>
*/
 
  //unify(hold(E)) ~> chich ~>
           //chich ~>
  unify(nf(E)) ~> killMgu //~> chich
           //~>
           //unifyKill(nf(E))
           //~> chich
           ...</k>
       <mgu> Theta </mgu>
       <dbg> I => I +Int 1 </dbg>
    when isFunClausesApp(E) andBool lengthList(args(E)) ==Int numReqArgs(leftmost(E)) andBool notBool matches(leftmost(E), E) andBool
         indexOfFunClausesAppPattern(Theta, leftmost(E), E) >=Int 0 andBool

         //isFunClausesApp(args(E)(indexOfFunClausesAppPattern(Theta, leftmost(E), E))) =/=K true
         //getKLabel(suitableLHS(Theta, leftmost(E), E, leftmost(E))) =/=KLabel 'suitableLHS
isVariable(unhide(args(E)(indexOfFunClausesAppPattern(Theta, leftmost(E), E)))) =/=K true andBool
//args(getFunClausesAppPattern(Theta, leftmost(E), E))(indexOfFunClausesAppPattern(Theta, leftmost(E), E)) =/=K args(lhs2expr(suitableLHS(Theta, leftmost(getFunClausesAppPattern(Theta, leftmost(E), E)), unhide(args(E)(indexOfFunClausesAppPattern(Theta, leftmost(E), E))), Set(0))))(indexOfFunClausesAppPattern(Theta, leftmost(E), E)) andBool
         getKLabel(suitableLHS(Theta,
  leftmost(getFunClausesAppPattern(Theta, leftmost(E), E)), unhide(args(E)(indexOfFunClausesAppPattern(Theta, leftmost(E), E))), Set(0))) =/=KLabel 'suitableLHS
  andBool I <Int 50

syntax KItem ::= l(List)
  rule <k> nf(E) => chich ~> 
args(getFunClausesAppPattern(Theta, leftmost(E), E))(indexOfFunClausesAppPattern(Theta, leftmost(E), E))  ~>

args(lhs2expr(suitableLHS(Theta, leftmost(getFunClausesAppPattern(Theta, leftmost(E), E)), unhide(args(E)(indexOfFunClausesAppPattern(Theta, leftmost(E), E))), Set(0))))(indexOfFunClausesAppPattern(Theta, leftmost(E), E)) ~>

args(E)(indexOfFunClausesAppPattern(Theta, leftmost(E), E))
~>
renameVariablesConf(suitableLHS(Theta,
  leftmost(getFunClausesAppPattern(Theta, leftmost(E), E)), unhide(args(E)(indexOfFunClausesAppPattern(Theta, leftmost(E), E))),
  leftmost(getFunClausesAppPattern(Theta, leftmost(E), E))
  )) ~> unhide(getFunClausesAppPattern(Theta, leftmost(E), E)) #== HOLE ~> 

getFunClausesAppPattern(Theta, leftmost(E), E) ~> args(E)(indexOfFunClausesAppPattern(Theta, leftmost(E), E)) ~>
xx suitableLHS(Theta,
  leftmost(getFunClausesAppPattern(Theta, leftmost(E), E)), unhide(args(E)(indexOfFunClausesAppPattern(Theta, leftmost(E), E))), Set(0))
~> nf(E)
           ...</k>
       <mgu> Theta </mgu>
       <dbg> I </dbg>
when I >=Int 50



  syntax KItem ::= whnfType(Expr)  [strict, context(result(WhnfTypedExpr))]
  context whnfType(t(_, HOLE => whnf(HOLE)))  [result(Whnf)]

  syntax KItem ::= whnf(Expr)                   [context(result(Whnf))]
  context whnf({HOLE => /*block 1000 ~>*/ whnf(HOLE)})            [result(Whnf)]

  context whnf((HOLE => /*block 1001 ~>*/ whnf(HOLE)) _)   [result(Whnf)]

  rule <k> whnf(N => Nc) ...</k>  <ncat>... N |-> Nc ...</ncat>
  rule <k> whnf(Name(N)) ...</k>
       <ncat> NCat (. => Name(N) |-> Postlt(N)) </ncat>
       <sig>... (Name(N) => Postlt(N)) |-> _ ...</sig>
    when notBool Name(N) in keys(NCat)
  rule <k> whnf(F => /*block 1002 ~>*/ replaceInaccessible(FunClauses(F, E)))/*renameVariables(E))*/ ...</k>   <fun>... F |-> E ...</fun>
    when getKLabel(E) ==KLabel 'fc
  // THE RENAME MAY CAUSE CYCLES
  rule <k> whnf(F => /*block 1002 ~>*/ renameVariables(E)) ...</k>   <fun>... F |-> E ...</fun>
    when getKLabel(E) =/=KLabel 'fc


  rule <k> whnf(<E, LocalSigs, LocalFuns> => /*block 1003 ~>*/ E) ~> (. => localData(LocalSigs, LocalFuns)) ...</k>
       <fun> Rho => Rho[LocalFuns] </fun>
  rule (. => localNames(keys(LocalSigs))) ~> whnf(W:Whnf => /*block 1004 ~>*/ <W, LocalSigs, LocalFuns>) ~> (localData(LocalSigs, LocalFuns) => .)  [structural]

  //rule isWhnf(_:Whnf@_) => true

  /*
  syntax Bool ::= K "hasFunFrom" Set   [function, klabel('hasFunFrom)]
  rule L:KLabel(Ks:KList) => any('hasFunFrom, List Ks)  when isName(L(Ks)) =/=K true
  rule F:Name hasFunFrom Fs => F in Fs
  rule _ hasFunFrom _ => false    [owise]
  */

  rule whnf((\ (X : _) -> E1) E2 => /*block 2000 ~>*/ E1[E2/X])
    when isImplicit(E2) =/=K true

  rule whnf((\ {X : _} -> E1) {E2} => /*block 2001 ~>*/  E1[E2/X])

  context whnf(HOLE => nf(HOLE))
    when isFunClausesApp(HOLE) andBool lengthList(args(HOLE)) <=Int numReqArgs(leftmost(HOLE))   [result(Nf)]

  rule <k> whnf(E => matchClause(leftmost(E), E)) ...</k>  //<dbg> I => I +Int 1 </dbg>
    when isFunClausesApp(E) andBool lengthList(args(E)) ==Int numReqArgs(leftmost(E)) andBool matches(leftmost(E), E)
  //andBool I <Int 50

  /*
  rule <k> whnf(E) => getFunClausesAppPattern(Theta, leftmost(E), E) == args(E)(indexOfFunClausesAppPattern(Theta, leftmost(E), E)) ~>
           unify(whnf(E)) ~> unifyConf ~> killMgu ...</k>
       <mgu> Theta </mgu>
    when isFunClausesApp(E) andBool lengthList(args(E)) ==Int numReqArgs(leftmost(E)) andBool notBool matches(leftmost(E), E) andBool
         indexOfFunClausesAppPattern(Theta, leftmost(E), E) >=Int 0 andBool
         isFunClausesApp(args(E)(indexOfFunClausesAppPattern(Theta, leftmost(E), E))) =/=K true
  */

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

  // you don't want FunClauses as WhNeut:
  // isWhnf(E:Expr) would generate a sort memebership check,
  // leading to an infinite cycle because of Expr ::= Whnf
  //rule isWhNeut(E) => true
  //  when isFunClausesApp(E) andBool all(isWhnf, take(numReqArgs(leftmost(E)), args(E))) andBool notBool matches(leftmost(E), E)
  rule isNf(E) => true
    when isFunClausesApp(E) andBool all(isNf, args(E)) andBool
          ((lengthList(args(E)) <Int numReqArgs(leftmost(E))) orBool
           (hasNfPatterns(leftmost(E)) andBool notBool matches(leftmost(E), subExpr(numReqArgs(leftmost(E)), E)))) //andBool
         //((indexOfFunClausesAppPattern(Theta, leftmost(E), E) >=Int 0) =/=K true orBool  true)

  syntax Bool ::= hasNfPatterns(FunClauses)   [function]
  rule hasNfPatterns(FunClauses(_, 'fc(.KList))) => true
  rule hasNfPatterns(FunClauses(F, 'fc(L = _,, Cs))) => all(isNf, args(L)) andBool hasNfPatterns(FunClauses(F, 'fc(Cs)))

  // We must distinguish between a mismatch and inconclusive matching.
  // --- by attempting to unify
  syntax Bool ::= matches(FunClauses, Expr)  [function]
  //rule matches(Cs, E) => #matches(replaceInaccessible(Cs), E)
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
  //rule matchClause(Cs, E) => #matchClause(replaceInaccessible(Cs), E)
  //rule matchClause(FunClauses(.KList),, _) => error("nay matchin' cap'n")   // FIXME?
  rule matchClause(FunClauses(_, 'fc((L = R),, _)), E) => R[getMatching(L, unhide(E))]  when isMatching(L, unhide(E))
  rule matchClause(FunClauses(_, 'fc((L = R),, _)), E) => //applyMgu(updateMgu(.Mgu, L, unhide(E)), R)
        #unifyClause(getAlpha(L), L, unhide(E), R)
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
  rule replaceInaccessible(L:LHS) => /*renameVariables(L)*/L   [owise]
endmodule
