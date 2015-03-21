require "agda-syntax.k"
require "agda-semantics-normal.k"
require "agda-semantics-typesystem.k"
require "agda-semantics-decl-data.k"

module AGDA-SEMANTICS-DECL-FUN
  imports AGDA-SYNTAX
  imports AGDA-SEMANTICS-TYPESYSTEM
  imports AGDA-SEMANTICS-NORMAL
  imports AGDA-SEMANTICS-DECL-DATA

  //syntax Expr ::= Pattern
  //context (HOLE:Pattern => pattype(HOLE))
  /*
  syntax Pattern ::= (Pattern, Expr)
  rule isExprT((Pattern, Expr)) => true

  syntax K ::= pattype2(Patterns)
  context pattype2((HOLE:Pattern => pattype(HOLE)) _:Patterns)

  syntax K ::= pattype(Expr)
  context pattype(HOLE)  when isVariable(HOLE) =/=K true
  rule <k> pattype(X:Variable => (X, T)) ...</k>
       <tenv>... X |-> T ...</tenv>
  rule <k> pattype(X:Variable => (X, T)) ...</k>
       <tenv> TEnv </tenv>
    when notBool (X in keys(TEnv)) andBool fresh(T:Expr)
  */

  //rule patvar(X:Variable) => (X, T)   when fresh(T:Expr)
  //rule patvar(X:Variable => (X, T))   when fresh(T:Expr)
  //rule patvar(X:Variable) => (X, T)    when fresh(T:Expr)  [anywhere]


  // TODO? move into a separate module for generic functions?
  // this is bad, we need tenv() for recovery after the definition is dealt with
  /*
  syntax ExprT ::= autotype(Variable)
  rule <k> autotype(X) => (X, T) ...</k>
       <tenv>... X |-> T ...</tenv>
  rule <k> autotype(X) => (X, T) ...</k>
       <tenv> TEnv (. => X |-> T) </tenv>
    when notBool (X in keys(TEnv)) andBool fresh(T:Expr)
  */

  /*
  syntax Expr ::= prependPatternTypes(Patterns, Expr)  [function]
  rule prependPatternTypes((_, Pt:Expr) Ps:Patterns, T:Expr) => Pi X Pt prependPatternTypes(Ps, T)   when fresh(X:Variable)
  */

  /*
  syntax KItem ::= typecheck(Patterns, Expr)
  rule typecheck(.Patterns, T) => .  when notPi(T)
  rule typecheck(X:Variable Ps:Patterns, Pi _ Xt T) => typecheck(Ps, T)
  rule <k> typecheck((N:Name .Patterns) Ps:Patterns, Pi _ Xt T) => Xt == Nt ...</k>
       <data>... N |-> Nt ...</data>
  rule <k> typecheck(
  */

  /*
  syntax Map ::= Map "withVarsOf" Patterns  [function]
               | Map "withVarsOf" Pattern   [function]
  //context _ withVarsOf (pattype(HOLE:Pattern) _:Patterns)
  rule M:Map withVarsOf .Patterns => M
  rule M:Map withVarsOf (P:Pattern Ps:Patterns) => (M withVarsOf P) withVarsOf Ps
  rule M:Map withVarsOf _:Name => M
  rule M:Map withVarsOf X:Variable => M[T/X]  when fresh(T:Expr)
  rule M:Map withVarsOf (_:Name P:Pattern) => M withVarsOf P

  context _ (HOLE => pattype2(HOLE)) = _
  rule <k> F:Variable Ps:Patterns = _ ~> (. => tenv(TEnv)) ...</k>
       <tenv> TEnv => TEnv withVarsOf Ps </tenv>
  context _ _ = (HOLE:Expr => whnf2(HOLE)) ~> tenv(_)  [result(Whnf2ExprT)]
  rule <k> F:Variable Ps:Patterns = (E:Expr, T:Whnf) => . ...</k>
       <fun> Fun (. => F Ps |-> E[Fun]) </fun>
       <tenv> TEnv (. => F |-> prependPatternTypes(Ps, T)) </tenv>
         //when notBool (F in keys(Fun)) andBool notBool (F in keys(TEnv))
  */

  syntax KItem ::= typeVars(LHS)
  rule typeVars(L:LHS P:Pattern) => typeVars(L) ~> typeVarsP(P)
  rule typeVars(X:Variable) => autotype(X)

  syntax KItem ::= typeVarsP(Pattern)
  rule typeVarsP(_:Name P:Pattern) => typeVarsP(P)
  rule typeVarsP(_:Name) => .
  rule typeVarsP(X:Variable) => autotype(X)

  syntax KItem ::= autotype(Variable)
  rule <k> autotype(X) => . ...</k>
       <tenv>... X |-> _ ...</tenv>
  rule <k> autotype(X) => . ...</k>
       <tenv> TEnv (. => X |-> T) </tenv>
    when notBool (X in keys(TEnv)) andBool fresh(T:Expr)

  syntax Variable ::= funName(LHS)  [function]
  rule funName(F:Variable) => F
  rule funName(L:LHS _:Pattern) => funName(L)

  syntax Expr ::= LHS
  syntax LHST ::= (LHS, Expr)
  syntax ExprT ::= LHST
  syntax FunDecl ::= LHST "=" ExprT

  // would be nice to create a separate task for typeVars() here
  // well, not really context-based evaluation (defined below) of L = E _depends_ on typeVars() having been completed

  // this is number of args before the equality sign `=',
  // not counting possible arguments in inner lambdas
  syntax Int ::= numArgs(LHS)  [function]
  rule numArgs(_:Variable) => 0
  rule numArgs(L:LHS _:Pattern) => numArgs(L) +Int 1

  rule <k> L:LHS = E:Expr ...</k>
       <fun> Fun (. => funName(L) |-> fun(closure(.List, Fun))) </fun>
    when notBool (funName(L) in keys(Fun)) andBool numArgs(L) >Int 0

  rule <k> L:LHS = E:Expr => typeVars(L) ~> L = E ~> funDecl(funName(L), TEnv) ...</k>
       <tenv> TEnv </tenv>
  // if a clause of the same function has been already processed, the type
  // assigned to the function name will be re-used, causing type errors
  // if the clauses' respective result/arg types aren't compatible

  context HOLE:LHS = _ ~> funDecl(_, _)

  // NOTE: whnf21 nizsie blblo kvoli meta-id.dt -- co je ale aj tak dzivne
  // whnf2 je ale ok lebo aj tak nechcem evaluavat vyrazy pokial nemusim ci?
  // (typy, narozdiel od striktnych 'vyrazov', musim kvoli checkingu)
  context _:LHST = (HOLE => whnf2(HOLE)) ~> funDecl(_, _)  [result(Whnf2ExprT)]

  syntax Case ::= mkCase(LHS, Case)   [function]
  rule mkCase(_:Variable, C:Case) => C
  rule mkCase(L:LHS P:Pattern, C:Case) => mkCase(L, P -> C)

  rule <k> ((L:LHS, Tl:Expr) = (E:Expr, Te:Expr) => notBool (F in keys(Fun)) ~> true? ~> Tl == Te) ~> funDecl(F:Variable, _) ...</k>
       <fun> Fun (. => F |-> evalF(E, Fun)) </fun>
     when numArgs(L) ==Int 0

  // XXX: manually apply updateMgu() & applyMgu() in order to get rid of funDecl()?
  // TODO: check that number of patterns is the same as for the other definitional equations (see error msg in offic typechecker)
  rule <k> ((L:LHS, Tl:Expr) = (E:Expr, Te:Expr) => Fun[undef/F] ==Map Fun'[undef/F] ~> true? ~> Tl == Te) ~> funDecl(F:Variable, _) ...</k>
       <fun> Fun (F |-> fun(closure(_ (. => ListItem(mkCase(L, evalF(E, Fun)))), Fun'))) </fun>
     when numArgs(L) >Int 0

  syntax Case ::= Expr
                | Pattern "->" Case   [binder]

  syntax Closure ::= closure(Variable, Expr, Map)  [binder(1 -> 2)]
                   | closure(List, Map)
  /*
  syntax Val ::= "(" Val ")" [bracket]
                 //closure(Variable, Expr, Map)  [binder(1 -> 2)]     // ~ closure(Lambda X E, Fun)  kebyze mam netypovane lambda abstrakcie
               | lambda(Closure)
               | pi(Val, Closure)
               | fun(Closure)
               | Universe
               | Name
               | Val Val
               | neut(Expr, Map)
  */
  syntax ValWhnf ::= //closure(Binder, Map)
                   //| closure(fun(List), Map)
                     lambda(Closure)
                   | pi(ValWhnf, Closure)
                   | fun(Closure)
                   | Universe
                   | ValNeut
  //rule isValWhnf(_:SymExpr) => true
  syntax ValNeut ::= Name
                   | neut(Expr, Map)
                   | ValNeut Expr [left]
                   | SymExpr
  syntax Val ::= ValWhnf
               | pi(Val, Closure)
               | Val Val
  /*
               | ValNeut
  syntax ValNeut ::= Name
                   | ValNeut Val [left]
  syntax Whnf ::= Val
  */

  // rename: readback?
  syntax Expr ::= unval(Expr)   [function]
  rule unval(lambda(closure(X, E, _))) => Lambda X T unval(E) when fresh(T:Expr)
  rule unval(pi(T, closure(X, E, _))) => Pi X unval(T) unval(E)
  rule unval(U:Universe) => U
  rule unval(neut(E, _)) => unval(E)
  rule unval(N:Name) => N
  rule unval(V1:Val V2:Val) => unval(V1) unval(V2)
  rule unval(E:Expr) => E [owise]

  /*
  syntax NeutlessExpr //::= Expr
  //rule isNeutlessExpr(neut(_, _)) => false
  rule isNeutlessExpr(E:Expr) => isValneut(E) =/=K true
  //syntax Expr ::= NeutlessExpr
  */


  syntax Expr ::= Val
  syntax Whnf ::= ValWhnf
  syntax ValWhnf2ExprT
  rule isValWhnf2ExprT((_:Expr, _:ValWhnf)) => true
  syntax Whnf2ExprT ::= ValWhnf2ExprT

  //rule isWhNeut(neut(_:Expr, _)) => true

  syntax Val ::= evalF(Expr, Map)   [function]
  rule evalF(X:Variable, Fun) => Fun(X)  when X in keys(Fun)   // the condition isn't necessary, perhaps, if evalF() is matched from top to bottom
  rule evalF(X:Variable, Fun) => neut(X, Fun) when notBool (X in keys(Fun))
  //rule evalF(X:Variable, Fun) => V       when notBool (X in keys(Fun)) andBool fresh(V:Val)
  rule evalF(Lambda X _ E, Fun) => lambda(closure(X, E, Fun))
  rule evalF(Pi X T1 T2, Fun) => pi(evalF(T1, Fun), closure(X, T2, Fun))
  rule evalF(E1:Expr E2:Expr, Fun) => evalF(E1, Fun) evalF(E2, Fun)
  //rule evalF(U:Universe, _) => U
  //rule evalF(N:Name, _) => N
  rule evalF(V:Val, _) => V


  // TODO: Consolidate with the unification (triggered on encountering a 'final'
  //       typed expr) and type env restoration mechanisms from -typesystem.k.
  syntax KItem ::= funDecl(Variable, Map)
  rule <k> funDecl(F, TEnv) => . ...</k>
       <meta> Meta => applyMgu(Theta, Meta) </meta>
       <tenv> TEnv' => TEnv[applyMgu(Theta, TEnv')(F)/F] </tenv>
       <mgu> Theta => .Mgu </mgu>


  /*
  syntax K ::= eval(Expr) [context(result(Val))]
  rule <k> eval(E => evalF(E, Fun)) ...</k>
       <fun> Fun </fun>  when notBool isVal(E)
  rule eval(app(closure(X, E, Fun), V) => E[Fun[V/X]])
  rule eval(app(fun(Cs), E) => matchCase(Cs, E))
  */

  /*
  syntax K ::= whnfEval1(Expr) [strict]  //, context(result(Whnf1ExprT))]
  context whnfEval1((HOLE => eval(HOLE), _:Whnf))  when notBool isVal(HOLE)
  context whnfEval1((HOLE:Val => whnf(HOLE), _:Whnf))
  */

  // TODO: rewrite for environments (substitution-based now)
  syntax Expr ::= matchCase(List, Expr)  [function]
  rule matchCase(ListItem(P -> E1) _, E2) => E1[getMatching(P, E2)]  when isMatching(P, E2)
  rule matchCase(_ Cs:List => Cs, _)  [owise]

  //syntax EnvRecovery ::= eval(Whnf)
  rule isEnvRecovery(eval(_:Whnf)) => true

  /*
  syntax Expr ::= stripneut(Expr)   [function] //[context(result(NeutlessExpr))]
  rule stripneut(neut(E, _) => E)
  rule stripneut(E) => E               [owise] //when isNeutlessExpr(E) ==K true
  */

  syntax K ::= eval(Expr)     [context(result(ValWhnf))] //superheat]
  //context eval((HOLE:Val => eval(HOLE)) _:Val)   [result(ValWhnf)]
  //context eval(_:Val (HOLE:Val => eval(HOLE)))   [result(ValWhnf)]
  context eval(pi(HOLE => eval(HOLE), _))  /*when isValWhnf(HOLE) =/=K true*/   [result(ValWhnf)]

  rule <k> eval(E:Expr => evalF(E, Fun)) ...</k>
       <fun> Fun </fun>
    when isVal(E) =/=K true
  rule <k> eval(neut(E:Expr, Fun) => E) ...</k>
       <fun> Fun' </fun>
    when Fun =/=Map Fun'
  /*
  rule <k> eval(E1:Expr neut(E2:Expr, Fun) => E1 E2) ...</k>
       <fun> Fun </fun>
    when Fun =/=Map Fun'
  rule <k> eval(neut(E1:Expr, Fun) E2:Expr => neut(E1 E2, Fun)) ...</k>
       <Fun> Fun' </fun>
    when Fun =/=Map Fun'
  */

  rule <k> eval(E1:Expr neut(E2:Expr, Fun) => neut(E1 E2, Fun)) ...</k>
       //<fun> Fun </fun>
  rule <k> eval(neut(E1:Expr, Fun) E2:Expr => neut(E1 E2, Fun)) ...</k>
       //<fun> Fun </fun>
  rule <k> eval(lambda(closure(X, E, Fun)) V:Val => E) ~> (. => fenv(Fun')) ...</k>
       //<tenv> TEnv' </tenv>
       <fun> Fun' => Fun[V/X] </fun>
  rule <k> eval(fun(closure(ListItem(P:Pattern -> E:Expr) _, Fun)) V:Val => E) ~> (. => fenv(Fun')) ...</k>
       //<tenv> TEnv' </tenv>
       <fun> Fun' => Fun[getMatching(P, V)] </fun>
    when isMatching(P, V)
  rule eval(fun(closure(ListItem(P:Pattern -> _) Cs:List => Cs, _)) V:Val)
    when notBool isMatching(P, V)
  // TODO: add rules ^ for general P -> C:Case, not just when isExpr(C)


  syntax KItem ::= "Hihi" Map Map


  // deal with neut in typed expr
  /*
  rule <k> ... neut(E, Fun') => Hihi Fun Fun' ~> E ...</k>
       <fun> Fun </fun>
  [anywhere]
  */
  //rule (neut(E, _) => E, _) [anywhere]    // causes infinite recursion as it gets triggerred too soon (immediately after eval has finished, causing it to run once again)

  // deal with neut in matching equations etc.
  //rule eqns((eqn(neut(E:Expr),,E':Expr) => eqn(E,,E')),,_)   [anywhere]
  //rule eqns((eqn(E':Expr,,neut(E:Expr)) => eqn(E,,E')),,_)   [anywhere]
endmodule
