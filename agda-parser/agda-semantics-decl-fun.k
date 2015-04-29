require "agda-semantics-common.k"

module AGDA-SEMANTICS-DECL-FUN
  imports AGDA-SEMANTICS-COMMON

  context _ : (HOLE => checkSetType(HOLE))   [infer-type-sig, result(SetTypedExpr)]
  rule [process-type-sig]:
       <k> Name(F) : t(E, Set(_)) => . ...</k>
       <ncat> NCat (. => Name(F) |-> Fun(F)) </ncat>
       <sig>... . => Fun(F) |-> E ...</sig>
    when notBool (Name(F) in keys(NCat))

  // for now, an absurd pattern causes its respective clause (consisting only of the LHS)
  // to be discarded with no checks  (FIXME, should verify that there really are
  // no suitable constructors.)
  rule Absurd(_) => .

  syntax KItem ::= "autotyped!"

  /*
  syntax LHS ::= freshArgs(LHS)  [function]
  rule freshArgs(L {_}) => freshArgs(L) {%meta}
  rule freshArgs(L A) => freshArgs(L) %meta  when isImplicit(A) =/=K true
  rule freshArgs(L) => L  [owise]
  */

  rule <k> L = R => saveCtx(Gamma) ~> autotype(L) ~> autotyped! ~> /*freshArgs(L)*/ L = R ~> loadCtx ...</k>
       <ctx> Gamma </ctx>

  context autotyped! ~> (HOLE => whnfType(HOLE)) = _  [result(WhnfTypedExpr)]

  context autotyped! ~> L::WhnfTypedExpr = (HOLE => whnfType(HOLE))  [result(WhnfTypedExpr)]

  // insert implicit metavariables at the end of the {left,right}-hand side of function clauses as appropriate
  rule autotyped! ~> (t(L, Tl) => L {%meta}) = t(_, Tr)  when isImplicitPi(Tl) andBool isImplicitPi(Tr) =/=K true
  rule autotyped! ~> t(_, Tl) = (t(R, Tr) => R {%meta})  when isImplicitPi(Tl) =/=K true andBool isImplicitPi(Tr)
  rule autotyped! ~> t(L, Tl) = t(R, Tr) => L {X} = R {X}   // NOTE: this gives a different behaviour as offic Agda, cf. Id8 test case
    when isImplicitPi(Tl) andBool isImplicitPi(Tr) andBool fresh(X:Variable)

  rule <k> (autotyped! => .) ~>
           (t(L, Tl) = t(R, Tr)
            => Tl == Tr ~> unifyConf ~>
               addFunClause(funName(L), L, R)) ...</k>
       <ctx> Gamma </ctx>
       <meta> _ => .Map </meta>   // these metas shouldn't be needed any more, clean-up for speed-up

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

  syntax KItem ::= addFunClause(Name, LHS, RHS)
  rule <k> addFunClause(F, L, R) => . ...</k>
       <fun> Rho
              (. => F |-> FunClauses(ListItem(freshFunName(L) = R))) </fun>
    when notBool (F in keys(Rho))
  rule <k> addFunClause(F, L, R) => . ...</k>
       <fun>... F |-> FunClauses(Cs (. => ListItem(freshFunName(L) = R))) ...</fun>
    when lengthList(args(L)) ==Int numReqArgs(FunClauses(Cs))   // check the arities are equal

  rule FunClauses(ListItem(L = R)) => R
    when lengthList(args(L)) ==Int 0   // i.e., when numReqArgs for the FunClauses is zero
    [structural, anywhere]

  // XXX hack for typing FunClauses
  rule <k> F:FunClauses => t(F, T) ...</k>
       <fun>... N |-> F ...</fun>
       <sig>... N |-> T ...</sig>

  syntax Name ::= funName(LHS)  [function]
  rule funName(L) => leftmost(L)

  syntax Expr ::= freshFunName(LHS)  [function]
  rule freshFunName(L) => replaceLeftmost(L, F)  when fresh(F:FunClauses)

  syntax Int ::= numReqArgs(FunClauses)  [function]
  rule numReqArgs(FunClauses(ListItem(L = _))) => lengthList(args(L))
  rule numReqArgs(FunClauses(ListItem(L = _) _)) => lengthList(args(L))
endmodule
