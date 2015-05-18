require "modules/unification.k"
require "agda-semantics-common.k"

module AGDA-SEMANTICS-UNIFICATION
  imports UNIFICATION
  imports SUBSTITUTION
  imports AGDA-SEMANTICS-COMMON

  // == ---> ==unif or ==mgu (alebo aj nie)
  syntax KItem ::= Expr "==" Expr | K "#==" K
  rule <k> E == E' => E #== E' ...</k>
       <mgu> Theta </mgu>
    when canUnify(Theta, E, E')
  rule <k> E == E' => nf(E) #== nf(E') ...</k>
       <mgu> Theta </mgu>
    when notBool canUnify(Theta, E, E')
  rule <k> nf(E) #== E' => nf(applyMgu(Theta, E)) ~> HOLE #== E' ...</k>
       <mgu> Theta </mgu>
  // TODO? dat nf(E:Nf)?
  rule nf(E) ~> HOLE #== E' => E #== E'  when isNf(E)
  rule <k> E #== nf(E') => nf(applyMgu(Theta, E')) ~> E #== HOLE ...</k>
       <mgu> Theta </mgu>
  rule nf(E') ~> E #== HOLE => E #== E'  when isNf(E')
  rule L:LHS ~> E #== HOLE => E #== L    // FIXME?
  rule <k> E:K #== E':K => . ...</k>
       <mgu> Theta => updateMguDummy(Theta, E, E') </mgu>
    when getKLabel(E) =/=KLabel 'nf andBool getKLabel(E') =/=KLabel 'nf andBool canUnify(Theta, E, E')
  // kinda hack because we rely on rename applied to the LHS specifically (rename of RHS/both would cause troubles)  [because of tsubst or why?]
  // treba pre 'id id' aplikaciu
  rule <k> E:K #== E':K => renameVariables(E) #== E' ...</k>
  //rule <k> E:K #== E':K => renameBoundVariables(E) #== renameBoundVariables(E') ...</k>
       <mgu> Theta </mgu>
       //<dbg> I => I +Int 1 </dbg>
    when getKLabel(E) =/=KLabel 'nf andBool getKLabel(E') =/=KLabel 'nf andBool
         getKLabel(updateMguDummy(Theta, E, E')) ==KLabel cycle
         //cycleWithBoundVariables(updateMgu(Theta, E, E'), E E')
    //andBool I <Int 50
  // FIXME tu Theta a updateMgu si viem zistit aj potom v resolveFunClauses, nemusim predavat ako arg
  rule <k> E:K #== E':K => resolveFunClauses(Theta, updateMguDummy(Theta, E, E'), ListItem(E), ListItem(E')) ...</k>
       <mgu> Theta </mgu>
       //<dbg> I => I +Int 1 </dbg>
    when getKLabel(E) =/=KLabel 'nf andBool getKLabel(E') =/=KLabel 'nf andBool
         notBool canUnify(Theta, E, E') andBool
         troublesomeFunClauses(updateMguDummy(Theta, E, E'))
      //andBool I <Int 50

  syntax KItem ::= "unifyConf"
  rule R:KResult ~> unifyConf => unifyConf ~> R  [structural]
  rule <k> unifyConf => . ...</k>
       <sig> Sigma => applyMgu(Theta, Sigma) </sig>
       <ctx> Gamma => applyMgu/*Keys*/(Theta, Gamma) </ctx>
       <ctxstack> Gammas => applyMguL/*KeysL*/(Theta, Gammas) </ctxstack>
       <fun> Rho => applyMgu(Theta, Rho) </fun>
       <meta> Meta => extendMeta(applyMgu(Theta, Meta)) </meta>
       <mgu> Theta </mgu>

  syntax KItem ::= unify(K)
  rule <k> unify(K:K) => applyMgu(Theta, K) ...</k>
       <mgu> Theta </mgu>

  /*
  syntax KItem ::= unifyKill(K)
  rule <k> unifyKill(K:K) => killMgu ~> applyMgu(Theta, K) ...</k>
       <mgu> Theta </mgu>
  */

  syntax KItem ::= "killMgu"
  rule R:KResult ~> killMgu => killMgu ~> R  [structural]
  rule <k> killMgu => . ...</k>
       <mgu> Theta => .Mgu </mgu>

  syntax Bool ::= cycleWithBoundVariables(Mgu, Expr)  [function]
  rule cycleWithBoundVariables(cycle(Ks), E) => (Set Ks) <=Set getBoundVariables(E)

  syntax Bool ::= troublesomeFunClauses(Mgu)  [function]
  rule troublesomeFunClauses(clash(C1,,C2)) => true
    when isFunClausesApp(C1) orElseBool isFunClausesApp(C2)

  syntax KItem ::= resolveFunClauses(Mgu, Mgu, List, List)
  rule resolveFunClauses(_, _, ListItem(E1 => E2) _, ListItem(E2 => E1) _)
    when isFunClausesApp(E1) =/=K true andBool isFunClausesApp(E2)
  rule resolveFunClauses(_, clash((C1:K => C2),,(C2:K => C1)), _, _)
    when isFunClausesApp(C1) =/=K true andBool isFunClausesApp(C2)
  rule resolveFunClauses(Theta, clash(C1,,C2), ListItem(E1) _, ListItem(E2) _)
    => renameVariablesConf(replaceLeftmost(suitableLHS(Theta, leftmost(E1), C2, leftmost(E1)), leftmost(E1))) ~> subExpr(numReqArgs(leftmost(E1)), E1) #== HOLE ~> E1 == E2
    when isFunClausesApp(C1) andBool isFunClausesApp(E1) andBool
         leftmost(C1) ==K leftmost(E1) andBool leftmost(C2) ==K leftmost(E2)
  rule resolveFunClauses(Theta, clash(C1,,C2), ListItem(E1) L1, ListItem(E2) L2)
    => #if lengthList(args(E1)) ==Int lengthList(args(E2))
       #then resolveFunClauses(Theta, clash(C1,,C2), args(E1) L1, args(E2) L2)
       #else .
       #fi ~> E1 == E2
    when isFunClausesApp(C1) andBool
         ((isFunClausesApp(E1) ==K true andBool (leftmost(C1) =/=K leftmost(E1) orBool leftmost(C2) =/=K leftmost(E2))) orBool
          (isFunClausesApp(E1) =/=K true andBool isFunClausesApp(E2) =/=K true))

  syntax Bool ::= condd(Expr)  [function]
  rule condd(T) => true when leftmost(T) ==K Con("_<<_")

  // XXX posledny arg len na debug
  syntax K ::= suitableLHS(Mgu, FunClauses, Expr, Expr)  [function]
  rule suitableLHS(Theta, FunClauses(_, 'fc((L = R),, _)), T, _) => L
    when canUnify(Theta, subExpr(lengthList(args(T)), R), T)
  rule suitableLHS(_, FunClauses(_, 'fc((_ = _ => .KList),, _)), _, _)  [owise]

  syntax Bool ::= canUnify(K, K)       [function]
                | canUnify(Mgu, K, K)  [function]
                | #canUnifyImpl(Mgu, K, K)  [function]
  rule canUnify(K:K, K':K) => canUnify(.Mgu, K, K')
  rule canUnify(Theta, K:K, K':K) => isMguError(updateMguDummy(Theta, K, K')) =/=K true 
  /*#canUnifyImpl(Theta, K, K')
  rule #canUnifyImpl(Theta, E => E', E' => E)              when isImplicitPi(E) =/=K true andBool isImplicitPi(E')
  rule #canUnifyImpl(Theta, E:ImplicitPi => E', E':ImplicitPi => E)              when numPiArgs(E) <Int numPiArgs(E')
  rule #canUnifyImpl(Theta, E:ImplicitPi, E' => {X : T} -> E)
    when numPiArgs(E) >Int numPiArgs(E') andBool fresh(X:Variable) andBool fresh(T:Expr)
  rule #canUnifyImpl(Theta, K, K') => isMguError(updateMgu(Theta, K, K')) =/=K true [owise]
  */

  syntax Expr ::= subExpr(Int, Expr)   [function]
  rule subExpr(I, E) => E when lengthList(args(E)) <=Int I
  rule subExpr(I, E _ => E)  [owise]


  syntax MetaVariable
  rule isMetaVariable(K) => true  when getKLabel(K) ==KLabel #symExpr
  //rule isVariable(_:MetaVariable) => false
  // it holds that Variable ::= MetaVariable  (i.e., #symExpr's are also Variable)

  /*
  // a parallel infrastructure: we want metavars neither to be caught by accumulateVars
  // or to be renamed by renameVariables but we still want to retain pattern-matching
  // and unification for metavars (and so they must belong to Variables sort)
  // the solution is to hack renameVariables & friends
  syntax K ::= renameNonMetaVariables(K)  [function]
  rule renameNonMetaVariables(K) => applySubst(getNonMetaAlpha(K), K)
  syntax K ::= getNonMetaAlpha(K)  [function]
  rule getNonMetaAlpha(K) => freshSubst(subst(.KList),, accumulateNonMetaVars(#vars(.KList),, K))
  syntax K ::= accumulateNonMetaVars(KList)   [function]
  rule accumulateNonMetaVars(#vars(Xs:KList),,X:Variable,,Ks:KList)
    => #if (X inKList Xs)
       #then accumulateNonMetaVars(#vars(Xs),,Ks)
       #else accumulateNonMetaVars(#vars(Xs,,X),,Ks)
       #fi
    when isMetaVariable(X) =/=K true
  rule accumulateNonMetaVars(_:K,,(_:MetaVariable => .KList),,_)
  rule accumulateNonMetaVars(_:K,,(L:KLabel(Ks:KList) => Ks),,_)
    when isVariable(L(Ks)) =/=K true
  rule accumulateNonMetaVars(#vars(Xs:KList)) => #vars(Xs)
  */

  // TODO move to -common or -utils or something
  syntax KItem ::= renameVariablesConf(K) | #renameVarsConf(K, K)
  rule renameVariablesConf(K) => #renameVarsConf(getAlpha(K), K)
  rule <k> #renameVarsConf(Alpha, K) => applySubst(Alpha, K) ...</k>
       <ctx> Gamma => Gamma[#renameVarsCtx(Gamma, Alpha)] </ctx>
       // TODO: pridaj aj do <meta>?
  syntax Map ::= #renameVarsCtx(Map, K)  [function]
  rule #renameVarsCtx(_, subst(.KList)) => .Map
  rule #renameVarsCtx(_ (K |-> V), subst((eqn(K,,X) => .KList),,_)) (.Map => X |-> V)
  rule #renameVarsCtx(_, subst((eqn(_,,X) => .KList),,_)) (.Map => X |-> T)  when fresh(T:Expr)  [owise]

  // KLabel-based map could be used if applyMgu was an unary function...
  syntax List ::= applyMguL(Mgu, List)   [function]
  rule applyMguL(Theta, .List) => .List
  rule applyMguL(Theta, _ (ListItem(#map(Gamma)) => .List)) (.List => ListItem(#map(applyMgu(Theta, Gamma))))

  syntax List ::= applyMguKeysL(Mgu, List)   [function]
  rule applyMguKeysL(Theta, .List) => .List
  rule applyMguKeysL(Theta, _ (ListItem(#map(Gamma)) => .List)) (.List => ListItem(#map(applyMguKeys(Theta, Gamma))))

  rule <ctx>... E |-> _ => .Map ...</ctx>  when isVariable(E) =/=K true

  syntax Map ::= applyMguKeys(Mgu, Map)  [function]
  rule applyMguKeys(_, .Map) => .Map
  rule applyMguKeys(Theta, _ (K |-> V => .Map)) (.Map => (K |-> applyMgu(Theta, V)) (applyMgu(Theta, K) |-> applyMgu(Theta, V)))
    when isVariable(applyMgu(Theta, K)) andBool applyMgu(Theta, K) =/=K K
  rule applyMguKeys(Theta, _ (K |-> V => .Map)) (.Map => K |-> applyMgu(Theta, V))  [owise]

  syntax Map ::= extendMeta(Map)  [function]
               | #extendMeta(Map, Map)  [function]
  rule extendMeta(M) => #extendMeta(M, .Map)
  rule #extendMeta(.Map, M') => M'
  rule #extendMeta(M (X |-> t(E, T)), M' (.Map => E |-> t(E, T)))
    when isMetaVariable(E) andBool E =/=K X andBool notBool (E in keys(M) keys(M'))
  rule #extendMeta(_ (X |-> V => .Map), _ (.Map => X |-> V))  [owise]

  // The LHS of eqn() below gets replaced with the RHS: swapping the sides
  // when necessary.
  // - Metavariables should be always substituted *for*, not vice versa.
  /*
  rule eqns((eqn(K,,#symExpr(Ls)) => eqn(#symExpr(Ls),,K)),,_)
    when getKLabel(K) =/=KLabel #symExpr  [structural, anywhere]
  */

  //rule eqns((eqn(#symVariable(Ls),,K) => eqn(K,,#symVariable(Ls))),,_)
  //  when getKLabel(K) =/=KLabel #symVariable andBool isVariable(K) [structural, anywhere]
  //rule eqns((eqn(#symVariable(LsV),,#symExpr(LsE)) => eqn(#symExpr(LsE),,#symVariable(LsV))),,_)  [structural, anywhere]

  rule eqns((eqn(K,,#symVariable(Ls)) => eqn(#symVariable(Ls),,K)),,_)
    when getKLabel(K) =/=KLabel #symVariable andBool getKLabel(K) =/=KLabel #symExpr [structural, anywhere]
  rule eqns((eqn(K,,#symExpr(Ls)) => eqn(#symExpr(Ls),,K)),,_)
    when getKLabel(K) =/=KLabel #symVariable andBool getKLabel(K) =/=KLabel #symExpr [structural, anywhere]
  rule eqns((eqn(K,,X) => eqn(X,,K)),,_)
    when isVariable(X) ==K true andBool isVariable(K) =/=K true  [structural, anywhere]
  //rule eqns((eqn(K,,K') => .KList),,_)
  //  when isUltraDummy(K) ==K true orBool isUltraDummy(K') ==K true  [structural, anywhere]
  //rule eqns((eqn(#symVariable(_),,#symVariable(_)) => .KList),,_)



  //rule eqns((eqn(#symExpr(Ls),,#symVariable(J)) => eqn(#symVariable(J),,#symExpr(Ls))),,_)  [structural, anywhere]

  // hackity hack: using functions from both substitution and unification module
  rule getVariables(K) => #getVarsFromK(#getVars(K))
  syntax Set ::= getBoundVariables(K)       [function]
  rule getBoundVariables(K) => getVariables(K) -Set freeVariables(K)
  syntax K ::= renameBoundVariables(K)      [function]
  rule renameBoundVariables(K) => applySubst(freshSubst(subst(.KList),, #vars(KList getBoundVariables(K))), K)
  /*
             | #substituteBoundVars(Set, K) [function]
  rule renameBoundVariables(K) => #substituteBoundVars(getVariables(K) -Set freeVariables(K), K)
  rule #substituteBoundVars(.Set, K) => K
  rule #substituteBoundVars((SetItem(X) => .Set) _, K => K[Y/X])  when fresh(Y:Variable)
  */

  syntax Set ::= freeMetaVariables(K)  [function]
  rule freeMetaVariables(K) => filter(isMetaVariable, freeVariables(K))

  syntax UltraDummy ::= "#dummy"//(Variable)
  syntax Variable ::= UltraDummy

  syntax K ::= dummyVarsInBinders(K)  [function]
  //rule dummyVarsInBinders(K) => K
  rule dummyVarsInBinders((X : T) -> E) => (#dummy : dummyVarsInBinders(T)) -> dummyVarsInBinders(E)
  rule dummyVarsInBinders({X : T} -> E) => {#dummy : dummyVarsInBinders(T)} -> dummyVarsInBinders(E)
  rule dummyVarsInBinders(\ (X : T) -> E) => \ (#dummy : dummyVarsInBinders(T)) -> dummyVarsInBinders(E)
  rule dummyVarsInBinders(\ {X : T} -> E) => \ {#dummy : dummyVarsInBinders(T)} -> dummyVarsInBinders(E)
  rule dummyVarsInBinders(K:KLabel(Ls:KList)) => K(dummyVarsInBinders(Ls))  [owise]
  syntax KList ::= dummyVarsInBinders(KList)  [function]
  rule dummyVarsInBinders(.KList) => .KList
  rule dummyVarsInBinders(K:K,,Ks:KList) => dummyVarsInBinders(K),,dummyVarsInBinders(Ks)

  syntax Mgu ::= updateMguDummy(Mgu, K, K)  [function]
  rule updateMguDummy(Mgu, K1, K2) => #if getKLabel(updateMgu(Mgu, dummyVarsInBinders(K1), K2)) =/=KLabel cycle
                                      #then Mgu
                                      #else updateMgu(Mgu, K1, K2)
                                      #fi
    when getKLabel(updateMgu(Mgu, K1, K2)) ==KLabel cycle
  rule updateMguDummy(Mgu, K1, K2) => updateMgu(Mgu, K1, K2)    [owise]

  syntax K ::= unifyRightNow(K, K, K)  [function]
  rule unifyRightNow(K1, K2, K) => applyMgu(updateMguDummy(.Mgu, K1, K2), K)
endmodule
