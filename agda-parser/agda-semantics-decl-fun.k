require "agda-semantics-common.k"

module AGDA-SEMANTICS-DECL-FUN
  imports SUBSTITUTION    // import once and for all in -common?
  imports AGDA-SEMANTICS-COMMON

  // for now, an absurd pattern causes its respective clause (consisting only of the LHS)
  // to be discarded with no checks  (TODO: should verify that there really are
  // no suitable constructors.)
  rule Absurd(_) => .

  /*
  syntax KItem ::= sandbox(FunClause, Declarations)
                 | localDefs(Set)
  rule <k> (. => Ds) ~> sandbox(_, Ds => .) ~> (. => localDefs(keys(Sigma))) ...</k>
       <sig> Sigma </sig>
    when Ds =/=K .
  rule <k> (sandbox(C, _) => C) ~> (localDefs(OldKeys) => localDefs(keys(Sigma) -Set OldKeys)) ...</k>
       <sig> Sigma </sig>
  */

  /*
  syntax Map ::= mapDiff(Map, Map)  [function]
  rule mapDiff(_, .Map) => .Map
  rule mapDiff((K |-> _) _, (K |-> _ => .Map) _)
  rule mapDiff(MapOld, (KNew |-> VNew => .Map) _) (.Map => KNew |-> VNew)  when notBool (KNew in keys(MapOld))
  */

  //context _ = _ where (HOLE => sandbox(HOLE))  [result(FunExt)]

  //rule (. => sandbox(Ds)) ~> L = R where (Ds => .Declarations)

  //rule L = R where Ds => sandbox(L = R, Ds)

  syntax KItem ::= global(Name, Set)
  rule <k> (. => Ds) ~> L = _ where (Ds => .Declarations) ~> (. => global(funName(L), SetItem(funName(L)) keys(Sigma))) ...</k>
       <sig> Sigma </sig>
  rule <k> global(F, GlobalKeys) => updateLastFunClause(F, Rho(keys(Rho) -Set GlobalKeys)) ~> local(keys(Sigma) -Set GlobalKeys) ...</k>
       <fun> Rho </fun>
       <sig> Sigma </sig>

  syntax KItem ::= updateLastFunClause(Name, Map)
  rule <k> updateLastFunClause(F, LocalDefs) => . ...</k>
       <fun>... F |-> 'fc(_,,(_ = (R => R@LocalDefs))) ...</fun>
  rule <k> updateLastFunClause(F, LocalDefs) => . ...</k>
       <fun>... F |-> (E => E@LocalDefs) ...</fun>
    when getKLabel(E) =/=KLabel 'fc

  syntax KItem ::= local(Set) | localFun(Map)
  rule <k> local(.Set) => . ...</k>
  rule <k> local((SetItem(N) => .Set) _) ...</k>
       <ncat>... _ |-> N => . ...</ncat>
       <sig>... N |-> _ => . ...</sig>
       <fun>... N |-> _ => . ...</fun>
  rule <k> local((SetItem(N) => .Set) _) ...</k>
       <ncat>... _ |-> N => . ...</ncat>
       <sig>... N |-> _ => . ...</sig>
       <fun> Rho </fun>
    when notBool (N in keys(Rho))
  rule <k> local((SetItem(N) => .Set) _) ...</k>
       <fun>... N |-> _ => . ...</fun>
       <ncat> NCat </ncat>
       <sig> Sigma </sig>
    when notBool (N in keys(Sigma)) andBool notBool (N in keys(NCat))


  syntax KItem ::= "prepared!"
                 //| prepared(LHS)

  /*
  syntax KItem ::= autotype(Set)
  rule autotype(.Set) => .
  rule <k> autotype((SetItem(X) => .Set) _) ...</k>
       <ctx> Gamma </ctx>
       <meta> Meta </meta>
    when X in keys(Gamma) orBool X in keys(Meta)
  rule <k> autotype((SetItem(X) => .Set) _) ...</k>
       <ctx> Gamma (. => X |-> T) </ctx>
    when fresh(T:Expr) andBool notBool (X in keys(Gamma)) andBool isMetaVariable(X) =/=K true
  rule <k> autotype((SetItem(X) => .Set) _) ...</k>
       <meta> Meta (. => X |-> (X, T)) </meta>
    when fresh(T:Expr) andBool notBool (X in keys(Meta)) andBool isMetaVariable(X) ==K true
  */


  /*
  syntax KItem ::= checkPatterns(Name, List)   // ten fun type chcem po rename variable!
                 | #checkPatterns(Name, Expr, List, List)
                 | #checkSubPattern(Expr, Expr)
  rule <k> checkPatterns(F, Args) => #checkPatterns(F, T, Args, .List) ...</k>
       <sig>... F |-> T ...</sig>
  rule <k> #checkPatterns(_, {X : _} -> T, (.List => ListItem({W})) ListItem(E) _, _) ...</k>
       <fenv> FEnv </fenv>
    when isImplicit(E) =/=K true andBool notBool (X in freeVariables(values(FEnv))) andBool fresh(W:Expr)
  rule <k> #checkPatterns(_, {X : _} -> T, (.List => ListItem(DotP({X}))) ListItem(E) _, _) ...</k>
       <fenv> FEnv </fenv>
    when isImplicit(E) =/=K true andBool X in freeVariables(values(FEnv))

  // insert wildcard as the last pattern if still implicit pi-abstraction
  rule <k> #checkPatterns(_, {X : _} -> T, (.List => ListItem({W})), _) ...</k>
       <fenv> FEnv </fenv>
    when notBool (X in freeVariables(values(FEnv))) andBool fresh(W:Expr)
  rule <k> #checkPatterns(_, {X : _} -> T, (.List => ListItem(DotP({X}))), _) ...</k>
       <fenv> FEnv </fenv>
    when X in freeVariables(values(FEnv))

  //rule (. => autotype(freeVariables(E)) ~> checkType(E, T)) ~>

  syntax Bool ::= condc(Expr)   [function]
  rule condc(E) => true when leftmost(E) ==K Con("_::_")

  rule <k> #checkSubPattern(E, T) => autotype(freeVariables(E)) ~>
            #if isName(leftmost(E)) ==K true
            #then saveFEnv ~> cleanFEnv ~> chich ~> Sigma(leftmost(E)) ~> T[FEnv] ~>
                  checkType(#checkPatterns(leftmost(E), applyMgu(updateMgu(.Mgu, target(Sigma(leftmost(E))), T[FEnv]),
                    Sigma(leftmost(E))), args(E), .List), T) ~> loadFEnv
            #else checkType(E, T) #fi ...</k>
       <sig> Sigma </sig>
       <fenv> FEnv </fenv>
    when condc(E) ==K true

  rule <k> #checkSubPattern(E, T) => autotype(freeVariables(E)) ~>
            #if isName(leftmost(E)) ==K true
            #then saveFEnv ~> cleanFEnv ~>
                  checkType(#checkPatterns(leftmost(E), applyMgu(updateMgu(.Mgu, target(Sigma(leftmost(E))), T[FEnv]),
                    Sigma(leftmost(E))), args(E), .List), T) ~> loadFEnv
            #else checkType(E, T) #fi ...</k>
       <sig> Sigma </sig>
       <fenv> FEnv </fenv>
    when condc(E) =/=K true


  rule <k> (. => #checkSubPattern(E, T)) ~>
           #checkPatterns(_, {X : T} -> T' => T', (ListItem({E}) => .List) _, _ (.List => ListItem({E}))) ...</k>
       <fenv> FEnv (. => X |-> E) </fenv>
    when notBool (X in keys(FEnv))
  rule <k> (. => #checkSubPattern(E, T)) ~>
           #checkPatterns(_, (X : T) -> T' => T', (ListItem(E) => .List) _, _ (.List => ListItem(E))) ...</k>
       <fenv> FEnv (. => X |-> E) </fenv>
    when isImplicit(E) =/=K true andBool notBool (X in keys(FEnv))

  syntax Bool ::= funcond(Name)   [function]
  rule funcond(F) => true when F ==K Fun("map")

  rule #checkPatterns(F, T, .List, NewArgs) => mkLHS(F, NewArgs)  //prepared(mkLHS(F, NewArgs))
    when isImplicitPi(T) =/=K true andBool funcond(F) =/=K true
  rule #checkPatterns(F, T, .List, NewArgs) => mkLHS(F, NewArgs)  //prepared(mkLHS(F, NewArgs))
    when isImplicitPi(T) =/=K true andBool funcond(F) ==K true
  */

  syntax Expr ::= piTarget(Int, Pi)  [strict(2(context('nf)))]
  rule piTarget(I => I -Int 1, {_ : _} -> T => T)   when I >Int 0
  rule piTarget(I => I -Int 1, (_ : _) -> T => T)   when I >Int 0
  //rule piTarget(_, T) => T    [owise]

  rule (piTarget(I, E2) => .) ~> E1 == (HOLE => E2)  when I ==Int 0 //orBool isPi(E2) =/=K true

  syntax LHS ::= mkLHS(LHS, List)  [function]
  rule mkLHS(F => F A, _ (ListItem(A) => .List))
  rule mkLHS(F, .List) => F  [owise]

  /*
  syntax K ::= wildReplace(LHS)  [function]
  rule wildReplace(P1 P2) => wildReplace(P1)::Arg wildReplace(P2)::Arg
  rule wildReplace(%wild) => W  when fresh(W:Expr)
  rule wildReplace(P) => P   [owise]
  */

  //rule <k> L = R => saveCtx(Gamma) ~> updateFunName(funName(L)) ~> autotype(L) ~> prepared! ~> L = R ~> loadCtx ...</k>
  rule <k> (. => updateFunName(L) ~> saveCtx(Gamma) ~> autotype(L) ~> prepared!) ~>
  //checkPatterns(funName(L), args(/*renameVariables*/ncatReplace(NCat, wildReplace(L))))) ~>
           //(L => HOLE) = _ ~>
           L = _ ~>
           (. => loadCtx) ...</k>
       <ctx> Gamma </ctx>
       <ncat> NCat </ncat>

  //rule (. => prepared!) ~> (L:LHS ~> HOLE = R => L = R)  //when cond0(L) ==K true
  //rule L:LHS ~> HOLE = R => prepared! ~> L = R  when cond0(L) =/=K true



  context prepared! ~> (HOLE => whnfType(HOLE)) = _        //when cond0(HOLE) =/=K true
    [result(WhnfTypedExpr)]
  //context prepared! ~> (HOLE => chich ~> whnfType(chich ~> HOLE)) = _        when cond0(HOLE) ==K true          [result(WhnfTypedExpr)]

  syntax Bool ::= cond0(LHS)  [function]
  /*
  rule cond0(L) => true when leftmost(L) ==K Fun("'map")
  rule cond0(L) => true when leftmost(L) ==K Name("'map")
  rule cond0(L) => true when L ==K Fun("thmPlusZero") (Con("suc") Var("n"))
  */
  /*
  rule cond0(L) => true when leftmost(L) ==K Name("thmPlusZero")
  rule cond0(L) => true when leftmost(L) ==K Fun("thmPlusZero")
  */

  rule cond0(L) => true when leftmost(L) ==K Fun ( "[a->b]->[zzzb->za]" )


  context prepared! ~> L::WhnfTypedExpr = (HOLE => whnfType(HOLE))   //when cond0(L) =/=K true
    [result(WhnfTypedExpr)]
  //context prepared! ~> L::WhnfTypedExpr = (HOLE => chich ~> whnfType(chich ~> HOLE)) when cond0(L) ==K true   [result(WhnfTypedExpr)]


  // insert implicit wildcards/metavariables at the end of the {left,right}-hand side of function clauses as appropriate
  // already done in #checkPatterns for LHS
  //rule prepared! ~> (t(L, Tl) => L {W}) = t(_, Tr)
  //  when isImplicitPi(Tl) andBool isImplicitPi(Tr) =/=K true andBool fresh(W:Expr)
  rule prepared! ~> (t(L, {_ : _} -> _) => L {%meta}) = _
  rule prepared! ~> _ = (t(R, {_ : _} -> _) => R {%meta})
    //when /*isImplicitPi(Tl) =/=K true andBool* isImplicitPi(Tr) andBool*/ fresh(W:Expr)
  //rule prepared! ~> t(L, Tl) = t(R, Tr) => L {W} = R {W}   // NOTE: this gives a different behaviour from offic Agda, cf. Id8 test case
  //  when isImplicitPi(Tl) andBool isImplicitPi(Tr) andBool fresh(W:Expr)

  rule <k> (prepared! => .) ~>
           (t(L, Tl) = t(R, Tr)
            =>
            piTarget(lengthList(args(L)), renameBoundVariables(Sigma(funName(L)))) ~>
            Tl == HOLE ~>
            piTarget(lengthList(args(L)), renameBoundVariables(Sigma(funName(L)))) ~>
            Tr == HOLE ~> Tl == Tr ~>
               addFunClause(funName(L), insertDots(L), R) ~>
               unifyConf ~> killMgu ~>
               cleanMetas) ...</k>  // tests/Vec will take ages without this
       <sig> Sigma </sig>
       //<fenv> FEnv </fenv> //=> .Map </fenv>
    when cond0(L) ==K true
  rule <k> (prepared! => .) ~>
           (t(L, Tl) = t(R, Tr)
            =>
            piTarget(lengthList(args(L)), renameBoundVariables(Sigma(funName(L)))) ~>
            Tl == HOLE ~>
            piTarget(lengthList(args(L)), renameBoundVariables(Sigma(funName(L)))) ~>
            Tr == HOLE ~> Tl == Tr ~>
               addFunClause(funName(L), renameBoundVariables(insertDots(L)), renameBoundVariables(R)) ~>
               unifyConf ~> killMgu ~>
               cleanMetas) ...</k>  // tests/Vec will take ages without this
       <sig> Sigma </sig>
       //<fenv> FEnv => .Map </fenv>
    when cond0(L) =/=K true

  syntax Implicit ::= "{" LHS "}"
  syntax LHS ::= insertDots(LHS)        [function]
               | #insertDots(LHS, List, Set)  [function]
  rule insertDots(L) => #insertDots(L, .List, .Set)
  rule #insertDots(L {P} => L, _ (.List => ListItem({#insertDots(P, .List, Metas)})), Metas => Metas freeMetaVariables(P))
  rule #insertDots(L P => L, _ (.List => ListItem(#insertDots(P, .List, Metas))), Metas => Metas freeMetaVariables(P))
    when isImplicit(P) =/=K true
    //when notBool (freeMetaVariables(P) <=Set Metas)
  //rule #insertDots(L P => L, _ (.List => ListItem(#insertDots(P, .List, Metas))), Metas)  when freeMetaVariables(P) <=Set Metas
  /*
  rule #insertDots({P}, .List, Metas) => {DotP(P)}  when P in Metas
  rule #insertDots(P, .List, Metas) => DotP(P)      when P in Metas
  rule #insertDots(P, Args, _) => mkLHS(P, Args)    [owise]
  */
  //rule #insertDots(P, Args, Metas) => mkLHS(#if P in Metas orBool unhide(P) in Metas #then DotP(P) #else P #fi, Args)  [owise]
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
    when notBool (X in keys(Gamma)) andBool fresh(T:Expr) andBool X =/=K Var ( "_8853_" ) orBool true
  rule <k> autotype(X:Variable) => block -2321 ...</k>
       <ctx> Gamma => Gamma[T/X] </ctx>
    when notBool (X in keys(Gamma)) andBool fresh(T:Expr) andBool X ==K Var ( "_8853_" ) andBool false

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
  //rule funName(L) => leftmost(L)
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
  /*
  rule <k> #updateFunName(Name(N)@F) => . ...</k>
       <ncat> NCat (. => Name(N)@F |-> Fun(N)@F) </ncat>
       <sig>... (Name(N)@F => Fun(N)@F) |-> _ ...</sig>
    when notBool Name(N)@F in keys(NCat)
  rule <k> #updateFunName(Name(N)@F) => . ...</k>
       <ncat>... Name(N)@F |-> Fun(N)@F ...</ncat>
       <sig>... Fun(N)@F |-> _ ...</sig>
  rule #updateFunName(Fun(_)@_) => .
  */

  syntax Int ::= numReqArgs(FunClauses)  [function]
               | numReqArgs(K)           [function]
  rule numReqArgs(FunClauses(_, 'fc(Cs)) => 'fc(Cs))
  rule numReqArgs('fc((L = _),,_)) => lengthList(args(L))
  //rule numReqArgs(FunClauses(ListItem(L = _) _)) => lengthList(args(L))

  //syntax Bool ::= isFunClausesApp(Expr)  [function]
  syntax FunClausesApp
  rule isFunClausesApp(E) => true when isFunClauses(leftmost(E)) andBool getKLabel(leftmost(E)) =/=KLabel #symFunClauses
  syntax App ::= FunClausesApp
endmodule
