//require "agda-syntax-pretty.k"
//require "modules/substitution.k"
require "agda-semantics-common.k"
require "agda-semantics-typesystem.k"
require "agda-semantics-decl-data.k"

module AGDA-SEMANTICS
  //imports SUBSTITUTION    // for freshFunName(), FIXME?
  //imports AGDA-SYNTAX-PRETTY
  imports AGDA-SEMANTICS-COMMON
  imports AGDA-SEMANTICS-TYPESYSTEM
  imports AGDA-SEMANTICS-DECL-DATA

  rule module N Tel where Decls => Decls
  rule postulate Sig => Sig

  // TODO: do I wanna E below also in whnf? and also when adding a constructor/datatype..?
  // --- doing it, necessary for ImplArg.agda; extend to datatypes, too, then?
  context _ : (HOLE => checkSetType(HOLE))   [result(SetTypedExpr)]
  syntax KItem ::= m(Map)
  rule <k> N : t(E, Set(_)) => . ...</k>
       <sig>... . => N |-> E ...</sig>
       <fenv> Rho </fenv>
    //when N =/=K Name("cons")
  /*
  rule <k> N : t(E, Set(_)) => needsEval(E, Rho) ...</k>
       <sig>... . => N |-> E@Rho ...</sig>
       <fenv> Rho </fenv>
    when N ==K Name("cons")
  */




  //syntax Expr ::= Pattern
  //syntax LHS ::= Expr

  /*
  syntax TypedPattern
  rule isTypedPattern(t(_:Pattern, _)) => true
  //syntax TypedRHS
  //rule isTypedRHS(t(_:RHS, _)) => true
  syntax TypedExpr ::= TypedPattern   //| TypedRHS
  syntax Pattern ::= TypedPattern
  //syntax RHS ::= TypedRHS
  */

  //rule isExpr(_:LHS) => true
  //rule isLHS(_:TypedExpr) => true
  //syntax TypedRHS ::= t(RHS, Expr)
  //syntax RHS ::= TypedRHS
  //syntax TypedExpr ::= TypedLHS //| TypedRHS

  syntax Name ::= funName(LHS)  [function]
  rule funName(L) => leftmost(L)

  syntax KItem ::= autotype(LHS)
  rule autotype(P1 P2) => autotype(P1) ~> autotype(P2)
  rule autotype({E} => E)
  rule autotype(_:Name) => .
  rule autotype(%underscore) => .
  rule <k> autotype(X:Variable) => . ...</k>
       <tenv> Gamma => Gamma[T/X] </tenv>
       //<fenv> Rho => Rho[^/X] </fenv>        // it would be nice to do this, but if it isn't necessary,
                                               // then it's more convenient not to because the current fenv-restoring
                                               // mechanism cannot be directed to restore everything except the just
                                               // declared function clause
    when /*notBool (X in keys(Gamma)) andBool*/ fresh(T:Expr)

  rule <k> L = R => autotype(L) ~> bound! ~> L = R ~> tenv(Gamma) ...</k>
       <tenv> Gamma </tenv>
       <sig> Sigma (. => funName(L) |-> T) </sig>
    when notBool (funName(L) in keys(Sigma)) andBool fresh(T:Expr)    // occurs when missing type sig
  rule <k> L = R => autotype(L) ~> bound! ~> L = R ~> tenv(Gamma) ...</k>
       <tenv> Gamma </tenv>
       <sig> Sigma </sig>
    when funName(L) in keys(Sigma)

  context bound! ~> (HOLE => whnfType(HOLE)) = _   [result(WhnfTypedExpr)]
  //context bound! ~> HOLE = _
  //rule bound! ~> (X => whnfType(X) ~> HOLE) = _  when isWhnfTypedExpr(X) =/=K true
  //rule bound! ~> (whnfType(X) ~> HOLE => X) = _  when isWhnfTypedExpr(X) =/=K true
  context bound! ~> _ = (HOLE => chich ~> whnfType(HOLE))   [result(WhnfTypedExpr)]


  syntax Name ::= Aux(Name)
  syntax Expr ::= freshFunName(Expr)  [function]
  rule freshFunName(P P') => freshFunName(P) P'
  rule freshFunName(Name(S)) => F  when fresh(F:Variable)     // mozno fresh variable nahradit nejakou spesl entitou ktoru pridam do sortu Variable?

  // NOTE: the Aux-name is redundant when the function has no arguments (LHS contains only the fun name)
  syntax KItem ::= addFunClause(Name, LHS, RHS)
  rule <k> addFunClause(F, L, R) => . ...</k>
       <fenv> Rho
              (. => Aux(F) |-> FunClauses(numArgs(L), ListItem(freshFunName(L) = R))@Rho) </fenv>   // Aux(F) maps to the list of pattern-matching clauses
    when notBool (F in keys(Rho))
  rule <k> addFunClause(F, L, R) => . ...</k>
       <fenv>... Aux(F) |-> FunClauses(I, _ (. => ListItem(freshFunName(L) = R)))@_ ...</fenv>
    when numArgs(L) ==Int I
    // already matching on Aux(F), don't have to check for presence in keys


  syntax Expr ::= genLambda(Int, Expr)  [function]
  rule genLambda(0, E) => E
  rule genLambda(I, E) => \ (X : T) -> genLambda(I -Int 1, E X)  when fresh(X:Variable) andBool fresh(T:Expr)  [owise]
  // wouldn't untyped lambdas be actually better, I wonder...

  syntax KItem ::= addFunWrapper(Name, LHS)
  rule <k> addFunWrapper(F, L) => . ...</k>
       <fenv> Rho
              (. => F |-> genLambda(numArgs(L), Aux(F))@Rho) </fenv>   // forcing the evaluation of a pattern-matching function to have a sufficient no. of args
    when notBool (F in keys(Rho))
  rule <k> addFunWrapper(F, L) => . ...</k>
       <fenv> Rho' (F |-> _@(Rho => Rho')) </fenv>
    // already matching on F, don't have to check for presence in keys

  // insert implicit metavariables at the end
  rule bound! ~> (t(L, {_ : _} -> _) => L {%underscore}) = _
  rule bound! ~> _ = (t(R, {_ : _} -> _) => R {%underscore})

  rule <k> (bound! => .) ~>
           (t(L, Tl) = t(R, Tr)
            => //notBool (funName(L) in keys(Rho)) ~> true? ~>                    // verify that F isn't already defined
               //freeVariablesM(E) <=Set freeVariablesM(L) keys(Fun) ~> true? ~>    // that the body of F doesn't contain undefined functions (check TEnv instead b/c of mutual recursion)
               Tl == Tr ~> unify ~>
               addFunClause(funName(L), L, R) ~> addFunWrapper(funName(L), L)) ...</k>
endmodule
