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

  rule <k> L = R => autotype(L) ~> autotyped! ~> L = R ~> tenv(Gamma) ...</k>
       <tenv> Gamma </tenv>
       <funtenvs> GammaF </funtenvs>
    when notBool (funName(L) in keys(GammaF))
  rule <k> L = R => autotype(L) ~> autotyped! ~> L = R ~> tenv(Gamma) ...</k>
       <tenv> Gamma => unwrap(GammaF(funName(L))) </tenv>
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

  rule <k> (autotyped! => .) ~>
           (t(L, Tl) = t(R, Tr)
            => Tl == Tr ~> unifyConf ~>
               addFunClause(funName(L), L, R) ~> addFunWrapper(funName(L), L)) ...</k>
       <tenv> Gamma </tenv>
       <funtenvs> GammaF => GammaF[m(Gamma)/funName(L)] </funtenvs>
    when cond2(t(L, Tl)) =/=K true
  rule <k> (autotyped! => .) ~>
           (t(L, Tl) = t(R, Tr)
            => Tl == Tr ~> unifyConf ~>
               addFunClause(funName(L), L, R) ~> addFunWrapper(funName(L), L)) ...</k>
       <tenv> Gamma </tenv>
       <funtenvs> GammaF => GammaF[m(Gamma)/funName(L)] </funtenvs>
    when cond2(t(L, Tl)) ==K true


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

  syntax Name ::= Aux(Name)
  syntax KItem ::= addFunClause(Name, LHS, RHS)
  rule <k> addFunClause(F, L, R) => . ...</k>
       <fenv> Rho
              (. => Aux(F) |-> FunClauses(lengthList(args(L)), ListItem(freshFunName(L) = R))) </fenv>   // Aux(F) maps to the list of pattern-matching clauses
    when notBool (F in keys(Rho))
  rule <k> addFunClause(F, L, R) => . ...</k>
       <fenv>... Aux(F) |-> FunClauses(I, _ (. => ListItem(freshFunName(L) = R))) ...</fenv>
    when lengthList(args(L)) ==Int I
    // ... already matching on Aux(F), don't have to check for its presence in keys

  rule FunClauses(0, ListItem(_ = R)) => R   [structural, anywhere]
  //rule <fenv>... (F |-> V) ((Aux(F) |-> V') => .) ...</fenv> when V ==K V'  [structural]     // << cannot occur without @Rho

  syntax Expr ::= genLambda(List, Expr)  [function]
  rule genLambda(ListItem({_}) L, E) => \ {X : T} -> genLambda(L, E {X})  when fresh(X:Variable) andBool fresh(T:Expr)
  rule genLambda(ListItem(A) L, E) => \ (X : T) -> genLambda(L, E X)      when isImplicit(A) =/=K true andBool fresh(X:Variable) andBool fresh(T:Expr)
  rule genLambda(_, E) => E  [owise]
  // wouldn't untyped lambdas be actually better, I wonder...

  syntax KItem ::= addFunWrapper(Name, LHS)
  rule <k> addFunWrapper(F, L) => . ...</k>
       <fenv> Rho
              (. => F |-> genLambda(args(L), Aux(F))) </fenv>   // forcing the evaluation of a pattern-matching function to have a sufficient no. of args
    when notBool (F in keys(Rho))
  rule <k> addFunWrapper(F, L) => . ...</k>  <fenv> Rho </fenv>  when F in keys(Rho)

  syntax Name ::= funName(LHS)  [function]
  rule funName(L) => leftmost(L)

  syntax Variable ::= "%fun"
  syntax Expr ::= freshFunName(LHS)  [function]
  rule freshFunName(L) => replaceLeftmost(L, %fun)

  syntax K ::= m(Map)
  syntax Map ::= unwrap(K)  [function]
  rule unwrap(m(M)) => M  [structural]
endmodule
