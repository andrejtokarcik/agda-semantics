//require "agda-syntax-pretty.k"
require "agda-semantics-common.k"
require "agda-semantics-typesystem.k"
require "agda-semantics-decl-data.k"

module AGDA-SEMANTICS
  //imports AGDA-SYNTAX-PRETTY
  imports AGDA-SEMANTICS-COMMON
  imports AGDA-SEMANTICS-TYPESYSTEM
  imports AGDA-SEMANTICS-DECL-DATA

  rule module N Tel where Decls => Decls
  rule postulate Sig => Sig

  context _ : (HOLE => whnfType(HOLE))  //[result(TypedType)]
  rule <k> N : t(E, Set(_)) => . ...</k>
       <sig>... . => N |-> E ...</sig>



  syntax Expr ::= Pattern
  syntax LHS ::= Expr
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

  syntax KItem ::= autoVarTypes(LHS)
  rule autoVarTypes(P1 P2) => autoVarTypes(P1) ~> autoVarTypes(P2)
  rule autoVarTypes(_:Name) => .
  rule <k> autoVarTypes(X:Variable) => . ...</k>
       <tenv> Gamma => Gamma[T/X] </tenv>
       //<fenv> Rho => Rho[^/X] </fenv>        // it would be nice to do this, but if it isn't necessary,
                                               // then it's more convenient not to because the current fenv-restoring
                                               // mechanism cannot be directed to restore everything except the just
                                               // declared function clause
    when /*notBool (X in keys(Gamma)) andBool*/ fresh(T:Expr)

  rule <k> L = R => autoVarTypes(L) ~> bound! ~> L = R ~> tenv(Gamma) ...</k>
       <tenv> Gamma </tenv>
       <sig> Sigma (. => funName(L) |-> T) </sig>
    when notBool (funName(L) in keys(Sigma)) andBool fresh(T:Expr)    // occurs when missing type sig
  rule <k> L = R => autoVarTypes(L) ~> bound! ~> L = R ~> tenv(Gamma) ...</k>
       <tenv> Gamma </tenv>
       <sig> Sigma </sig>
    when funName(L) in keys(Sigma)

  context bound! ~> HOLE = _     // TODO? whnfType or something
  context bound! ~> _ = HOLE


  syntax Int ::= numArgs(LHS)  [function]
  rule numArgs(P _) => numArgs(P) +Int 1
  rule numArgs(_) => 0   [owise]

  syntax Name ::= Aux(Name)  //[function]
  //rule fakeName(Name(S)) => Name(";" +String S)

  /*
  syntax Expr ::= #genLam(Int, LamBindings, Expr)  [function]
  rule #genLam(0, Tel, E) => Lam(Tel, E)    // gets automatically desugared into std lambda (with successive bindings)
  rule #genLam(I => I, Bs:LamBindings => X Bs, E => #genLam(E X)  when fresh(X:Variable)  [owise]
  */
  syntax Expr ::= genLambda(Int, Expr)  [function]
  rule genLambda(0, E) => E
  rule genLambda(I, E) => genLambda(I -Int 1, \ (X : T) -> E) X  when fresh(X:Variable) andBool fresh(T:Expr)  [owise]
  // wouldn't untyped lambdas be actually better, I wonder...

  syntax K ::= Clauses(List)    // need wrapper around List
  syntax RHS ::= Val
  syntax KItem ::= addFunClause(Name, LHS, RHS)
  rule <k> addFunClause(F, L, R) => . ...</k>
       <fenv> Rho
              (. => F |-> genLambda(numArgs(L), Aux(F)))
              (. => Aux(F) |-> Clauses(ListItem(L = R))@Rho) </fenv>
    when notBool (F in keys(Rho))
  rule <k> addFunClause(F, L, R) => . ...</k>
       <fenv> Rho (Aux(F) |-> Clauses(_ (. => ListItem(L = R)))@Rho) </fenv>
    when F in keys(Rho)   // TODO: check that no. of args is the same for all clauses

  rule <k> (bound! => .) ~>
           (t(L, Tl) = t(R, Tr)
            => //notBool (funName(L) in keys(Rho)) ~> true? ~>                    // verify that F isn't already defined
               //freeVariablesM(E) <=Set freeVariablesM(L) keys(Fun) ~> true? ~>    // that the body of F doesn't contain undefined functions (check TEnv instead b/c of mutual recursion)
               Tl == Tr ~> unify ~>
               addFunClause(funName(L), L, R)) ...</k>

  /*
  rule <k> t(L, Tl) = t(R, Tr) => Tl == Tr ~> unify ...</k>
       <fenv>... . => L |-> R ...</fenv>   // << ako kluc chcem mat len fun name, kvoli partial application
                                         // ALTERNATIVA: ale asi by slo vymysliet, zeby som si vytvaral fresh funkcie
                                         // co by len lambda abstrakciou zaobalili tu pattern matching funkciu
                                         // (typu map = \a -> \b -> map a b spolu s pattern-matching-based definiciami mapu)
                                         // vyhol by som sa takto tomu fun() konstruktu
                                         // kazdopadne, <fenv /> by potom musel byt list (lebo nas zaujima poradie
                                         // fun klauzuli v orig kode) a nie map
  */
endmodule
