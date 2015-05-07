require "agda-semantics-common.k"

module AGDA-SEMANTICS-DECL-FUN
  imports AGDA-SEMANTICS-COMMON

  // for now, an absurd pattern causes its respective clause (consisting only of the LHS)
  // to be discarded with no checks  (FIXME, should verify that there really are
  // no suitable constructors.)
  rule Absurd(_) => .

  syntax KItem ::= "autotyped!"

  rule <k> L = R => saveCtx(Gamma) ~> updateFunName(funName(L)) ~> autotype(L) ~> autotyped! ~> L = R ~> loadCtx ...</k>
       <ctx> Gamma </ctx>

  context autotyped! ~> (HOLE => whnfType(HOLE)) = _  [result(WhnfTypedExpr)]
  context autotyped! ~> _::WhnfTypedExpr = (HOLE => whnfType(HOLE))  [result(WhnfTypedExpr)]

  // insert implicit metavariables at the end of the {left,right}-hand side of function clauses as appropriate
  rule autotyped! ~> (t(L, Tl) => L {%meta}) = t(_, Tr)  when isImplicitPi(Tl) andBool isImplicitPi(Tr) =/=K true
  rule autotyped! ~> t(_, Tl) = (t(R, Tr) => R {%meta})  when isImplicitPi(Tl) =/=K true andBool isImplicitPi(Tr)
  rule autotyped! ~> t(L, Tl) = t(R, Tr) => L {X} = R {X}   // NOTE: this gives a different behaviour from offic Agda, cf. Id8 test case
    when isImplicitPi(Tl) andBool isImplicitPi(Tr) andBool fresh(X:Variable)

  rule <k> (autotyped! => .) ~>
           (t(L, Tl) = t(R, Tr)
            => Tl == Tr ~> unifyConf ~>
               addFunClause(funName(L), L, R) ~>
               cleanMetas) ...</k>  // Vec will take ages without this
       <ctx> Gamma </ctx>

  syntax KItem ::= updateFunName(Name)
  rule <k> updateFunName(Name(N)) => . ...</k>
       <ncat> NCat (. => Name(N) |-> Fun(N)) </ncat>
       <sig>... (Name(N) => Fun(N)) |-> _ ...</sig>
    when notBool Name(N) in keys(NCat)
  rule <k> updateFunName(Name(N)) => . ...</k>
       <ncat>... Name(N) |-> Fun(N) ...</ncat>
       <sig>... Fun(N) |-> _ ...</sig>
  rule updateFunName(Fun(_)) => .

  syntax KItem ::= autotype(LHS)
  rule autotype(P1 P2) => autotype(P1) ~> autotype(P2)
  rule autotype({E} => E)
  rule autotype(_:Name) => .
  rule autotype(%meta) => .
  rule <k> autotype(X:Variable) => . ...</k>
       <ctx> Gamma </ctx>
    when X in keys(Gamma)
  rule <k> autotype(X:Variable) => . ...</k>
       <ctx> Gamma => Gamma[T/X] </ctx>
    when notBool (X in keys(Gamma)) andBool fresh(T:Expr)

  syntax FunClauses ::= FunClauses(List)
  syntax Expr ::= FunClauses

  syntax KItem ::= addFunLambda(Name, Expr)  [strict(2)]   // strict to expand metas
  rule <k> addFunLambda(F, t(E, _)) => . ...</k>
       <fun> Rho (. => F |-> E) </fun>
    when notBool (F in keys(Rho))

  syntax KItem ::= addFunClause(Name, LHS, RHS)
  rule <k> addFunClause(F, L, R) => addFunLambda(F, Lam(castTelescope(args(L)), R)) ...</k>
       <fun> Rho </fun>
    when notBool (F in keys(Rho)) andBool all(isVariable, args(L))
  rule <k> addFunClause(F, L, R) => . ...</k>
       <fun> Rho
             (. => F |-> FunClauses(ListItem(freshFunName(L) = R))) </fun>
    when notBool (F in keys(Rho)) andBool notBool all(isVariable, args(L))
  rule <k> addFunClause(F, L, R) => . ...</k>
       <fun>... F |-> FunClauses(Cs (. => ListItem(freshFunName(L) = R))) ...</fun>
    when lengthList(args(L)) ==Int numReqArgs(FunClauses(Cs))   // check the arities are equal

  // XXX hack for typing FunClauses
  rule <k> F:FunClauses => t(F, T) ...</k>
       <fun>... N |-> F ...</fun>
       <sig>... N |-> T ...</sig>

  syntax Name ::= funName(LHS)  [function]
  rule funName(L) => leftmost(L)
  //rule funName(Name(F)) => Fun(F)
  //rule funName(Fun(F))  => Fun(F)
  //rule funName(L => leftmost(L))    [owise]

  syntax Expr ::= freshFunName(LHS)  [function]
  rule freshFunName(L) => replaceLeftmost(L, F)  when fresh(F:FunClauses)

  syntax Int ::= numReqArgs(FunClauses)  [function]
  rule numReqArgs(FunClauses(ListItem(L = _))) => lengthList(args(L))
  rule numReqArgs(FunClauses(ListItem(L = _) _)) => lengthList(args(L))
endmodule
