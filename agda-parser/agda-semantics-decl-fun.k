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

  // for now, an absurd pattern causes its respective clause (consisting only of the LHS)
  // to be discarded with no checks  (FIXME, we would like to update funtenvs
  // at the very least.  we also should verify that there really are no suitable
  // constructors.)
  rule %absurd ~> _ => .

  syntax KItem ::= "autotyped!"

  /*
  syntax LHS ::= freshArgs(LHS)  [function]
  rule freshArgs(L {_}) => freshArgs(L) {%meta}
  rule freshArgs(L A) => freshArgs(L) %meta  when isImplicit(A) =/=K true
  rule freshArgs(L) => L  [owise]
  */

  rule <k> L = R => saveTEnv(Gamma) ~> autotype(L) ~> autotyped! ~> /*freshArgs(L)*/ L = R ~> restoreTEnv ...</k>
       <tenv> Gamma </tenv>
       <funtenvs> GammaF </funtenvs>
    when notBool (funName(L) in keys(GammaF))
  rule <k> L = R => saveTEnv(Gamma) ~> autotype(L) ~> autotyped! ~> /*freshArgs(L)*/ L = R ~> restoreTEnv ...</k>
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

  // insert implicit metavariables at the end of the {left,right}-hand side of function clauses as appropriate
  rule autotyped! ~> (t(L, Tl) => L {%meta}) = t(_, Tr)  when isImplicitPi(Tl) andBool isImplicitPi(Tr) =/=K true
  rule autotyped! ~> t(_, Tl) = (t(R, Tr) => R {%meta})  when isImplicitPi(Tl) =/=K true andBool isImplicitPi(Tr)
  rule autotyped! ~> t(L, Tl) = t(R, Tr) => L {X} = R {X}   // NOTE: this gives a different behaviour as offic Agda, cf. Id8 test case
    when isImplicitPi(Tl) andBool isImplicitPi(Tr) andBool fresh(X:Variable)

  syntax Bool ::= condz(LHS, RHS) [function]
  //rule condz(L, R) => true
  //  when leftmost(L) ==K Fun("vec") andBool leftmost(R) ==K Con("pair")
  //rule condz(L, R) => true
  //  when leftmost(L) ==K Fun("thmPlusZero") andBool leftmost(R) ==K Fun("thmPlusZero")

  rule <k> (autotyped! => .) ~>
           (t(L, Tl) = t(R, Tr)
            => Tl == Tr ~> unifyConf ~>
               addFunClause(funName(L), L, R)) ...</k>
       <tenv> Gamma </tenv>
       <funtenvs> GammaF => funName(L) |-> m(Gamma) </funtenvs>   // TODO: don't save #symExpr's & co. [side effect of separating tenv and meta]
       //<metavars> _ => .Map </metavars>   // these metas shouldn't be needed any more, clean-up for speed-up
    when condz(L, R) =/=K true
  rule <k> (autotyped! => .) ~>
           (t(L, Tl) = t(R, Tr)
            => nf(Tl) ~> nf(Tr) ~> Tl == Tr ~> unifyConf ~>
               addFunClause(funName(L), L, R)) ...</k>
       <tenv> Gamma </tenv>
       <funtenvs> _ => funName(L) |-> m(Gamma) </funtenvs>
       //<metavars> _ => .Map </metavars>
    when condz(L, R) ==K true


  syntax KItem ::= autotype(LHS)
  rule autotype(P1 P2) => autotype(P1) ~> autotype(P2)
  rule autotype({E} => E)
  rule autotype(_:Name) => .
  rule autotype(%meta) => .
  rule <k> autotype(X:Variable) => . ...</k>
       <tenv> Gamma </tenv>
    when X in keys(Gamma)
  rule <k> autotype(X:Variable) => . ...</k>
       <tenv> Gamma => Gamma[T/X] </tenv>
    when notBool (X in keys(Gamma)) andBool fresh(T:Expr)

  // TODO get rid of the Int, the information can be extracted from the ListItems
  syntax FunClauses ::= FunClauses(Int, List)
  syntax Expr ::= FunClauses

  syntax KItem ::= addFunClause(Name, LHS, RHS)
  rule <k> addFunClause(F, L, R) => . ...</k>
       <fenv> Rho
              (. => F |-> FunClauses(lengthList(args(L)), ListItem(freshFunName(L) = R))) </fenv>
    when notBool (F in keys(Rho))
  rule <k> addFunClause(F, L, R) => . ...</k>
       <fenv>... F |-> FunClauses(I, _ (. => ListItem(freshFunName(L) = R))) ...</fenv>
    when lengthList(args(L)) ==Int I

  rule FunClauses(0, ListItem(_ = R)) => R   [structural, anywhere]

  // XXX hack for typing FunClauses
  rule <k> F:FunClauses => t(F, T) ...</k>
       <fenv>... N |-> F ...</fenv>
       <sig>... N |-> T ...</sig>

  syntax Name ::= funName(LHS)  [function]
  rule funName(L) => leftmost(L)

  //syntax Variable ::= "%fun"
  syntax Expr ::= freshFunName(LHS)  [function]
  //rule freshFunName(L) => replaceLeftmost(L, %fun)
  //rule freshFunName(L) => L    // << toto nechces lebo ten List obshuje Fun("plus") napr. ale v reali tam uz mas nasubstituovane plusove FunClauses
  rule freshFunName(L) => replaceLeftmost(L, F)  when fresh(F:FunClauses)

  // the information can be extracted from the ListItems
  syntax Int ::= numReqArgs(FunClauses)  [function]
  rule numReqArgs(FunClauses(I, _)) => I
endmodule
