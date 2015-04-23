require "agda-semantics-common.k"

module AGDA-SEMANTICS-DECL-FUN
  imports AGDA-SEMANTICS-COMMON

  syntax Bool ::= cond5(Expr)  [function]
  rule cond5(Name("i")) => true

  context _ : (HOLE => checkSetType(HOLE))   [result(SetTypedExpr)]
  rule <k> Name(F) : t(E, Set(_)) => . ...</k>
       <ncat> NCat (. => Name(F) |-> Fun(F)) </ncat>
       <sig> Sigma (. => Fun(F) |-> E) </sig>
    when notBool (Name(F) in keys(NCat)) andBool cond5(Name(F)) ==K true
  rule <k> Name(F) : t(E, Set(_)) => . ...</k>
       <ncat> NCat (. => Name(F) |-> Fun(F)) </ncat>
       <sig> Sigma (. => Fun(F) |-> E) </sig>
    when notBool (Name(F) in keys(NCat)) andBool cond5(Name(F)) =/=K true

  syntax KItem ::= "autotyped!"

  rule <k> L = R => saveTEnv(Gamma) ~> autotype(L) ~> autotyped! ~> L = R ~> restoreTEnv ...</k>
       <tenv> Gamma </tenv>
       <funtenvs> GammaF => .Map </funtenvs>    // => .Map to unclutter the cache
    when notBool (funName(L) in keys(GammaF))
  rule <k> L = R => saveTEnv(Gamma) ~> autotype(L) ~> autotyped! ~> L = R ~> restoreTEnv ...</k>
       <tenv> Gamma => unm(GammaF(funName(L))) </tenv>
       <funtenvs> GammaF </funtenvs>
    when funName(L) in keys(GammaF)

  syntax Bool ::= cond2(Expr)  [function]
  rule cond2(Name("thmPlusZero") _) => true
  rule cond2(t(Fun("thmPlusZero") _, _)) => true
  rule cond2(t(Fun("i"), _)) => true

  context autotyped! ~> (HOLE => whnfType(HOLE)) = _  when cond2(HOLE) =/=K true [result(WhnfTypedExpr)]
  context autotyped! ~> (HOLE => whnfType(HOLE)) = _  when cond2(HOLE) ==K true [result(WhnfTypedExpr)]

  context autotyped! ~> L::WhnfTypedExpr = (HOLE => whnfType(HOLE)) when cond2(L) =/=K true   [result(WhnfTypedExpr)]
  context autotyped! ~> L::WhnfTypedExpr = (HOLE => whnfType(HOLE)) when cond2(L) ==K true   [result(WhnfTypedExpr)]

  // insert implicit metavariables at the end of the {left,right}-hand side of function clauses
  rule autotyped! ~> (t(L, ({_ : _} -> _)) => L {%underscore}) = _
  rule autotyped! ~> _ = (t(R, ({_ : _} -> _)) => R {%underscore})

  syntax Bool ::= condz(LHS, RHS) [function]
  //rule condz(L, R) => true
  //  when leftmost(L) ==K Fun("vec") andBool leftmost(R) ==K Con("pair")

  rule <k> (autotyped! => .) ~>
           (t(L, Tl) = t(R, Tr)
            => Tl == Tr ~> unifyConf ~>
               addFunClause(funName(L), L, R)) ...</k>
       <tenv> Gamma </tenv>
       <funtenvs> GammaF => GammaF[m(Gamma)/funName(L)] </funtenvs>
    when condz(L, R) =/=K true
  rule <k> (autotyped! => .) ~>
           (t(L, Tl) = t(R, Tr)
            => chich ~> Tl == Tr ~> unifyConf ~>
               addFunClause(funName(L), L, R)) ...</k>
       <tenv> Gamma </tenv>
       <funtenvs> GammaF => GammaF[m(Gamma)/funName(L)] </funtenvs>
    when condz(L, R) ==K true


  syntax KItem ::= autotype(LHS)
  rule autotype(P1 P2) => autotype(P1) ~> autotype(P2)
  rule autotype({E} => E)
  rule autotype(_:Name) => .
  rule autotype(%underscore) => .
  rule <k> autotype(X:Variable) => . ...</k>
       <tenv> Gamma </tenv>
    when X in keys(Gamma)
  rule <k> autotype(X:Variable) => . ...</k>
       <tenv> Gamma => Gamma[T/X] </tenv>
    when notBool (X in keys(Gamma)) andBool fresh(T:Expr)

  syntax KItem ::= addFunClause(Name, LHS, RHS)
  rule <k> addFunClause(F, L, R) => . ...</k>
       <fenv> Rho
              (. => F |-> FunClauses(lengthList(args(L)), ListItem(freshFunName(L) = R))) </fenv>
    when notBool (F in keys(Rho))
  rule <k> addFunClause(F, L, R) => . ...</k>
       <fenv>... F |-> FunClauses(I, _ (. => ListItem(freshFunName(L) = R))) ...</fenv>
    when lengthList(args(L)) ==Int I

  rule FunClauses(0, ListItem(_ = R)) => R   [structural, anywhere]

  syntax Name ::= funName(LHS)  [function]
  rule funName(L) => leftmost(L)

  syntax Variable ::= "%fun"
  syntax Expr ::= freshFunName(LHS)  [function]
  rule freshFunName(L) => replaceLeftmost(L, %fun)
endmodule
