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
  rule <k> N : t(E, Set(_)) => . ...</k>
       <sig> Sigma (. => N |-> E@Rho) </sig>
       <fenv> Rho </fenv>
    when notBool (N in keys(Sigma))



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

  /*
  rule <k> L = R => autotype(L) ~> bound! ~> L = R ~> tenv(Gamma) ...</k>
       <tenv> Gamma </tenv>
       <sig> Sigma (. => funName(L) |-> T) </sig>
    when notBool (funName(L) in keys(Sigma)) andBool fresh(T:Expr)    // occurs when missing type sig  --- an underscore-sig is generated for missing type sigs
  */
  rule <k> L = R => autotype(L) ~> bound! ~> L = R ~> tenv(Gamma) ...</k>
       <tenv> Gamma </tenv>
       <funtenv> GammaF </funtenv>
    when notBool (funName(L) in keys(GammaF))
  rule <k> L = R => autotype(L) ~> bound! ~> L = R ~> tenv(Gamma) ...</k>
       <tenv> Gamma => unM(GammaF(funName(L))) </tenv>
       <funtenv> GammaF </funtenv>
    when funName(L) in keys(GammaF)

  context bound! ~> (HOLE => whnfType(HOLE)) = _  [result(WhnfTypedExpr)]

  syntax Bool ::= cond(K) [function]
  rule cond(K) => leftmost(K) ==K Name("_::_")
  // `_:WhnfTypedExpr' enforces seqstrict
  context bound! ~> _::WhnfTypedExpr = (HOLE => whnfType(HOLE)) when cond(HOLE)   [result(WhnfTypedExpr)]
  context bound! ~> _::WhnfTypedExpr = (HOLE => whnfType(HOLE)) when notBool cond(HOLE)  [result(WhnfTypedExpr)]

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
    // already matching on Aux(F), don't have to check for presence in keys


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

  /*
  syntax Telescope ::= genLamTel(LHS)    [function]
  // potreboval som dat genLamTel(L) pred ten #if...
  rule genLamTel(L A) => #if isImplicit(A) ==K true #then {X : T} #else (X : T) #fi genLamTel(L)
    when fresh (X:Variable) andBool fresh(T:Expr)
  rule genLamTel(_) => .Telescope  [owise]
  syntax Expr ::= genLamBody(Telescope, Expr)  [function]
  rule genLamBody((X : _) Tel, E) => genLamBody(Tel, E)  X
  rule genLamBody({X : _} Tel, E) => genLamBody(Tel, E) {X}
  rule genLamBody(.Telescope, E) => E  [owise]
  */

  syntax KItem ::= addFunWrapper(Name, LHS)
  rule <k> addFunWrapper(F, L) => . ...</k>
       <fenv> Rho
              (. => F |-> genLambda(argsList(L), Aux(F))@Rho) </fenv>   // forcing the evaluation of a pattern-matching function to have a sufficient no. of args
    when notBool (F in keys(Rho))
  rule <k> addFunWrapper(F, L) => . ...</k>
       <fenv> Rho (F |-> _@(_ => Rho)) </fenv>
    // already matching on F, don't have to check for presence in keys

  // insert implicit metavariables at the end
  rule bound! ~> (t(L, ({_ : _} -> _)@_) => L {%underscore}) = _
  rule bound! ~> _ = (t(R, ({_ : _} -> _)@_) => R {%underscore})

  rule <k> (bound! => .) ~>
           (t(L, Tl) = t(R, Tr)
            => //notBool (funName(L) in keys(Rho)) ~> true? ~>                    // verify that F isn't already defined
               //freeVariablesM(E) <=Set freeVariablesM(L) keys(Fun) ~> true? ~>    // that the body of F doesn't contain undefined functions (check TEnv instead b/c of mutual recursion)
               deval(Tl) == deval(Tr) ~> unify ~>
               addFunClause(funName(L), L, R) ~> addFunWrapper(funName(L), L)) ...</k>
       <tenv> Gamma </tenv>
       <funtenv> GammaF => GammaF[m(Gamma)/funName(L)] </funtenv>



  // auxiliary
  syntax K ::= m(Map)
  syntax Map ::= unM(K)  [function]
  rule unM(m(M)) => M  [structural]
endmodule
