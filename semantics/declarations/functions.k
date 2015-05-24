module AGDA-SEMANTICS-DECLARATIONS-FUNCTIONS
  imports SUBSTITUTION
  imports AGDA-SEMANTICS-COMMON
  imports AGDA-SEMANTICS-DECLARATIONS-LOCAL

  // For now, an absurd pattern causes its respective clause (consisting only of the LHS)
  // to be discarded with no checks.
  // (TODO: should verify that there really are no suitable constructors.)
  rule Absurd(_) => .


  rule <k> L = R where Ds => Ds ~> L = R ~> globalNames(funName(L), SetItem(funName(L)) keys(Sigma)) ...</k>
       <sig> Sigma </sig>
  rule <k> globalNames(F, GlobalKeys) => updateLastFunClause(F, Sigma(keys(Sigma) -Set GlobalKeys), Rho(keys(Rho) -Set GlobalKeys)) ~>
                                         localNames(keys(Sigma) -Set GlobalKeys) ...</k>
       <sig> Sigma </sig>
       <fun> Rho </fun>

  syntax KItem ::= updateLastFunClause(Name, Map, Map)
  rule <k> updateLastFunClause(F, LocalSigs, LocalFuns) => . ...</k>
       <fun>... F |-> 'fc(_,,(_ = (R => <R, LocalSigs, LocalFuns>))) ...</fun>
  rule <k> updateLastFunClause(F, LocalSigs, LocalFuns) => . ...</k>
       <fun>... F |-> (E => <E, LocalSigs, LocalFuns>) ...</fun>
    when getKLabel(E) =/=KLabel 'fc


  syntax KItem ::= "prepared!"

  syntax Expr ::= piTarget(Int, Pi)  [strict(2(context('nf)))]
  rule piTarget(I => I -Int 1, {_ : _} -> T => T)   when I >Int 0
  rule piTarget(I => I -Int 1, (_ : _) -> T => T)   when I >Int 0

  rule (piTarget(I, E2) => .) ~> E1 == (HOLE => E2)  when I ==Int 0

  syntax LHS ::= mkLHS(LHS, List)  [function]
  rule mkLHS(F => F A, _ (ListItem(A) => .List))
  rule mkLHS(F, .List) => F  [owise]

  rule <k> (. => updateFunName(L) ~> saveCtx(Gamma) ~> autotype(L) ~> prepared!) ~>
           L = _ ~>
           (. => loadCtx) ...</k>
       <ctx> Gamma </ctx>
       <ncat> NCat </ncat>

  //rule <k> L = R => saveCtx(Gamma) ~> updateFunName(funName(L)) ~> autotype(L) ~> prepared! ~> L = R ~> loadCtx ...</k>
  rule <k> (. => updateFunName(L) ~> saveCtx(Gamma) ~> autotype(L) ~> prepared!) ~>
  //checkPatterns(funName(L), args(/*renameVariables*/ncatReplace(NCat, wildReplace(L))))) ~>
           //(L => HOLE) = _ ~>
           L = _ ~>
           (. => loadCtx) ...</k>
       <ctx> Gamma </ctx>
       <ncat> NCat </ncat>



  context prepared! ~> (HOLE => whnfType(HOLE)) = _
    [result(WhnfTypedExpr)]

  context prepared! ~> L::WhnfTypedExpr = (HOLE => whnfType(HOLE))
    [result(WhnfTypedExpr)]

  // Insert implicit wildcards/metavariables at the end of the {left,right}-hand side of function clauses.
  rule prepared! ~> (t(L, {_ : _} -> _) => L {%wild}) = _
  rule prepared! ~> _ = (t(R, {_ : _} -> _) => R {%meta})

  // XXX: Check for alpha-equality instead of unification?
  rule <k> (prepared! => .) ~>
           (t(L, Tl) = t(R, Tr)
            =>
            piTarget(lengthList(args(L)), renameBoundVariables(Sigma(funName(L)))) ~>
            Tl == HOLE ~>
            piTarget(lengthList(args(L)), renameBoundVariables(Sigma(funName(L)))) ~>
            Tr == HOLE ~> Tl == Tr ~>
            addFunClause(funName(L), insertDots(L), R) ~>
            unifyConf ~> killMgu ~>
            cleanMetas) ...</k>
       <sig> Sigma </sig>

  syntax Implicit ::= "{" LHS "}"
  syntax LHS ::= insertDots(LHS)        [function]
               | #insertDots(LHS, List, Set)  [function]
  rule insertDots(L) => #insertDots(L, .List, .Set)
  rule #insertDots(L {P} => L, _ (.List => ListItem({#insertDots(P, .List, Metas)})), Metas => Metas freeMetaVariables(P))
  rule #insertDots(L P => L, _ (.List => ListItem(#insertDots(P, .List, Metas))), Metas => Metas freeMetaVariables(P))
    when isImplicit(P) =/=K true
  rule #insertDots(P, Args, Metas) => mkLHS(#if P in Metas #then DotP(P) #else P #fi, Args)  [owise]

  syntax KItem ::= autotype(LHS)
  rule autotype(P1 P2) => autotype(P1) ~> autotype(P2)
  rule autotype({E} => E)
  rule autotype(DotP(E) => E)
  rule autotype(_:Name) => .
  rule autotype(%meta) => .
  rule <k> autotype(X:Variable) => . ...</k>
       <ctx> Gamma </ctx>
    when X in keys(Gamma)
  rule <k> autotype(X:Variable) => . ...</k>
       <ctx> Gamma => Gamma[T/X] </ctx>
    when notBool (X in keys(Gamma)) andBool fresh(T:Expr)

  syntax KLabel ::= "'fc"
  syntax FunClauses ::= FunClauses(Name, K)
  syntax Expr ::= FunClauses

  syntax KItem ::= addFunLambda(Name, Expr)  [strict(2)]   // strict to expand metas
  rule <k> addFunLambda(F, t(E, _)) => . ...</k>
       <fun> Rho (. => F |-> E) </fun>
    when notBool (F in keys(Rho))

  syntax KItem ::= addFunClause(Name, LHS, RHS)
                 | #addFunClause(Name, LHS, RHS)
  rule addFunClause(F, L, R) => #addFunClause(F, L, R)
  rule <k> #addFunClause(F, L, R) => addFunLambda(F, Lam(castTelescope(args(L)), R)) ...</k>
       <fun> Rho </fun>
    when notBool (F in keys(Rho)) andBool all(isVariable, args(L))
  rule <k> #addFunClause(F, L, R) => . ...</k>
       <fun> Rho
             (. => F |-> 'fc(freshFunName(L) = R)) </fun>
    when notBool (F in keys(Rho)) andBool notBool all(isVariable, args(L))
  rule <k> #addFunClause(F, L, R) => . ...</k>
       <fun>... F |-> 'fc(Cs,, (.KList => freshFunName(L) = R)) ...</fun>
    when lengthList(args(L)) ==Int numReqArgs('fc(Cs))   // check the arities are equal

  syntax Name ::= funName(LHS)  [function]
  rule funName(Name(F)) => Fun(F)
  rule funName(Fun(F))  => Fun(F)
  rule funName(L => leftmost(L))    [owise]

  syntax Expr ::= freshFunName(LHS)  [function]
  rule freshFunName(L) => replaceLeftmost(L, F)  when fresh(F:FunClauses)

  syntax KItem ::= updateFunName(LHS)
                 | #updateFunName(Name)
  rule updateFunName(L) => #updateFunName(leftmost(L))
  rule <k> #updateFunName(Name(N)) => . ...</k>
       <ncat> NCat (. => Name(N) |-> Fun(N)) </ncat>
       <sig>... (Name(N) => Fun(N)) |-> _ ...</sig>
    when notBool Name(N) in keys(NCat)
  rule <k> #updateFunName(Name(N)) => . ...</k>
       <ncat>... Name(N) |-> Fun(N) ...</ncat>
       <sig>... Fun(N) |-> _ ...</sig>
  rule #updateFunName(Fun(_)) => .

  syntax Int ::= numReqArgs(FunClauses)  [function]
               | numReqArgs(K)           [function]
  rule numReqArgs(FunClauses(_, 'fc(Cs)) => 'fc(Cs))
  rule numReqArgs('fc((L = _),,_)) => lengthList(args(L))

  syntax FunClausesApp
  rule isFunClausesApp(E) => true when isFunClauses(leftmost(E)) andBool getKLabel(leftmost(E)) =/=KLabel #symFunClauses
  syntax App ::= FunClausesApp
endmodule
