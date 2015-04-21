require "agda-semantics-common.k"
require "agda-semantics-metavariables.k"

module AGDA-SEMANTICS-DECL-FUN
  imports AGDA-SEMANTICS-COMMON
  imports AGDA-SEMANTICS-METAVARIABLES

  syntax KItem ::= "autotyped!"

  rule <k> L = R => autotype(L) ~> autotyped! ~> L = R ~> tenv(Gamma) ...</k>
       <tenv> Gamma </tenv>
       <funtenvs> GammaF </funtenvs>
    when notBool (funName(L) in keys(GammaF))
  rule <k> L = R => autotype(L) ~> autotyped! ~> L = R ~> tenv(Gamma) ...</k>
       <tenv> Gamma => unwrap(GammaF(funName(L))) </tenv>
       <funtenvs> GammaF </funtenvs>
    when funName(L) in keys(GammaF)

  context autotyped! ~> (HOLE => whnfType(HOLE)) = _  [result(WhnfTypedExpr)]
  context autotyped! ~> _::WhnfTypedExpr = (HOLE => whnfType(HOLE))    [result(WhnfTypedExpr)]

  // insert implicit metavariables at the end of the {left,right}-hand side of function clauses
  rule autotyped! ~> (t(L, ({_ : _} -> _)@_) => L {%underscore}) = _
  rule autotyped! ~> _ = (t(R, ({_ : _} -> _)@_) => R {%underscore})

  rule <k> (autotyped! => .) ~>
           (t(L, Tl) = t(R, Tr)
            => //notBool (funName(L) in keys(Rho)) ~> true? ~>                    // verify that F isn't already defined
               //freeVariablesM(E) <=Set freeVariablesM(L) keys(Fun) ~> true? ~>    // that the body of F doesn't contain undefined functions (check TEnv instead b/c of mutual recursion)
               deval(Tl) == deval(Tr) ~> unify ~>
               addFunClause(funName(L), L, R) ~> addFunWrapper(funName(L), L)) ...</k>
       <tenv> Gamma </tenv>
       <funtenvs> GammaF => GammaF[m(Gamma)/funName(L)] </funtenvs>


  syntax Name ::= funName(LHS)  [function]
  rule funName(L) => leftmost(L)

  syntax KItem ::= autotype(LHS)
  rule autotype(P1 P2) => autotype(P1) ~> autotype(P2)
  rule autotype({E} => E)
  rule autotype(_:Name) => .
  rule autotype(%underscore) => .
  rule <k> autotype(X:Variable) => . ...</k>
       <tenv> Gamma </tenv>
    when X in keys(Gamma)
  rule <k> autotype(X:Variable) => . ...</k>
       <tenv> Gamma => Gamma[T@(Rho[^/X])/X] </tenv>
       <fenv> Rho </fenv>
       //<fenv> Rho => Rho[^/X] </fenv>          // it would be nice to do this, but if it isn't necessary,
                                                 // then it's more convenient not to because the current fenv-restoring
                                                 // mechanism cannot be directed to restore everything except the just
                                                 // declared function clause
    when notBool (X in keys(Gamma)) andBool fresh(T:Expr)

  syntax Name ::= Aux(Name)
  syntax Expr ::= freshFunName(Expr)  [function]
  rule freshFunName(P P') => freshFunName(P) P'
  rule freshFunName(_:Name) => F  when fresh(F:Variable)     // mozno fresh variable nahradit nejakou spesl entitou ktoru pridam do sortu Variable?

  syntax KItem ::= addFunClause(Name, LHS, RHS)
  rule <k> addFunClause(F, L, R) => . ...</k>
       <fenv> Rho
              (. => Aux(F) |-> FunClauses(numArgs(L), ListItem(freshFunName(L) = R))@Rho) </fenv>   // Aux(F) maps to the list of pattern-matching clauses
    when notBool (F in keys(Rho))
  rule <k> addFunClause(F, L, R) => . ...</k>
       <fenv>... Aux(F) |-> FunClauses(I, _ (. => ListItem(freshFunName(L) = R)))@_ ...</fenv>
    when numArgs(L) ==Int I
    // ... already matching on Aux(F), don't have to check for its presence in keys

  rule FunClauses(0, ListItem(_ = R)) => R   [structural, anywhere]
  rule <fenv>... (F |-> V) ((Aux(F) |-> V') => .) ...</fenv> when V ==K V'  [structural]

  syntax Expr ::= genLambda(List, Expr)  [function]
  rule genLambda(ListItem({_}) L, E) => \ {X : T} -> genLambda(L, E {X})  when fresh(X:Variable) andBool fresh(T:Expr)
  rule genLambda(ListItem(A) L, E) => \ (X : T) -> genLambda(L, E X)      when isImplicit(A) =/=K true andBool fresh(X:Variable) andBool fresh(T:Expr)
  rule genLambda(_, E) => E  [owise]
  // wouldn't untyped lambdas be actually better, I wonder...

  syntax List ::= argsList(Expr)  [function]
  rule argsList(E E') => argsList(E) ListItem(E')
  rule argsList(_) => .List [owise]

  syntax KItem ::= addFunWrapper(Name, LHS)
  rule <k> addFunWrapper(F, L) => . ...</k>
       <fenv> Rho
              (. => F |-> genLambda(argsList(L), Aux(F))@Rho) </fenv>   // forcing the evaluation of a pattern-matching function to have a sufficient no. of args
    when notBool (F in keys(Rho))
  rule <k> addFunWrapper(F, L) => . ...</k>
       <fenv> Rho (F |-> _@(_ => Rho)) </fenv>
    // ... already matching on F, don't have to check for its presence in keys


  syntax K ::= m(Map)
  syntax Map ::= unwrap(K)  [function]
  rule unwrap(m(M)) => M  [structural]
endmodule
