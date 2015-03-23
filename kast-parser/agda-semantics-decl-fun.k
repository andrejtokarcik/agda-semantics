require "modules/substitution.k"
require "agda-syntax.k"
require "agda-semantics-normal.k"
require "agda-semantics-typesystem.k"
require "agda-semantics-decl-data.k"

module AGDA-SEMANTICS-DECL-FUN
  imports SUBSTITUTION      // FIXME: move these imports into a generic module (or particular declarations, freeVariables() in this case)
  imports AGDA-SYNTAX
  imports AGDA-SEMANTICS-TYPESYSTEM
  imports AGDA-SEMANTICS-NORMAL
  imports AGDA-SEMANTICS-DECL-DATA

  // TODO: skratit/zlucit tieto dve
  syntax KItem ::= typeVars(LHS)
  rule typeVars(L:LHS P:Pattern) => typeVars(L) ~> typeVarsP(P)
  rule typeVars(X:Variable) => autotype(X)

  syntax KItem ::= typeVarsP(Pattern)
  rule typeVarsP(_:Name P:Pattern) => typeVarsP(P)
  rule typeVarsP(_:Name) => .
  rule typeVarsP(X:Variable) => autotype(X)

  syntax KItem ::= autotype(Variable)
  rule <k> autotype(X) => . ...</k>
       <tenv> TEnv </tenv>
    when X in keys(TEnv)
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
       <fun> Fun (. => funName(L) |-> fun(.List)@Fun) </fun>
    when notBool (funName(L) in keys(Fun)) andBool numArgs(L) >Int 0

  syntax KItem ::= "Hihi"
  rule <k> L:LHS = E:Expr => typeVars(L) ~> L = E ~> funDecl(funName(L), TEnv) ...</k>
       <tenv> TEnv </tenv>
  // if a clause of the same function has been already processed, the type
  // assigned to the function name will be re-used, causing type errors
  // if the clauses' respective result/arg types aren't compatible

  context (HOLE:LHS => HOLE ~> Hihi) = _ ~> funDecl(_, _)

  // NOTE: eval21 nizsie blblo kvoli meta-id.dt -- co je ale aj tak dzivne
  // eval2 je ale ok lebo aj tak nechcem evaluavat vyrazy pokial nemusim ci?
  // (typy, narozdiel od striktnych 'vyrazov', musim kvoli checkingu)
  // XXX: jj, imo nech mam pristup: be as lazy as possible [a nech sa evaluuje aj viackrat to iste,
  // hoci to bude neefektivne -- hram predovsetkym na korektnost]
  // ved aj tak robim typechecker a nie interpreter... ci?
  // (pozri poznamky ku kompilacii agdy, main ako entry point = vyraz na vyhodnotenie)
  context _:LHST = (HOLE => eval2(HOLE)) ~> funDecl(_, _)  [result(Whnf2ExprT)]

  syntax Case ::= mkCase(LHS, Case)   [function]
  rule mkCase(_:Variable, C:Case) => C
  rule mkCase(L:LHS P:Pattern, C:Case) => mkCase(L, P -> C)

  rule <k> ((L:LHS, Tl:Expr) = (E:Expr, Te:Expr) => notBool (F in keys(Fun)) ~> true? ~> Tl == Te) ~> funDecl(F:Variable, _) ...</k>
       <fun> Fun (. => F |-> E@Fun) </fun>
     when numArgs(L) ==Int 0

  // XXX: manually apply updateMgu() & applyMgu() in order to get rid of funDecl()?
  // TODO: check that number of patterns is the same as for the other definitional equations (see error msg in offic typechecker)
  rule <k> ((L:LHS, Tl:Expr) = (E:Expr, Te:Expr) => Fun[undef/F] ==Map Fun'[undef/F] ~> true? ~> Tl == Te) ~> funDecl(F:Variable, _) ...</k>
       <fun> Fun (F |-> fun(_ (. => ListItem(mkCase(L, E@Fun))))@Fun') </fun>
     when numArgs(L) >Int 0

  syntax Case ::= Expr
                | Pattern "->" Case   [binder]
  syntax Whnf ::= fun(List)

  syntax Val ::= "(" Val ")" [bracket]
               | Expr "@" Map   // closure
  // XXX: rewrite with [prec(_)] attribute? perhaps my K version doesn't support it yet?
  syntax priorities '_@_ > '__      // closure > app

  //rule isVal(E) => true  when isEmptySet(freeVariables(E))
  //rule E@.Map => E       when isEmptySet(freeVariables(E)) [structural, anywhere]

  //syntax Universe ::= Universe "@" Map
  //rule isUniverse(_:Universe@_:Map) => true

  // XXX STRASNY HACK (podobna situacia jak pri Neut v Nf)
  //syntax WhNeut ::= Variable
  //syntax WhNeut ::= Variable "@" Map

  syntax ValWhnf ::= Universe | WhNeut
  rule isValWhnf(_:Whnf@_) => true

  //rule isValWhnf(E) => true  when isEmptySet(freeVariables(E))
  //rule E@_ => E  when isEmptySet(freeVariables(E))  [structural, anywhere]

  // may replace these with an isBinder() and an #if clause for the case of updating Fun
  rule X:Variable@_ => [X] [structural, anywhere]
  rule U:Universe@_ => U [structural, anywhere]
  rule N:WhNeut@_ => N   [structural, anywhere]
  rule (E1 E2)@Rho => E1@Rho E2@Rho [structural, anywhere]

  syntax Val ::= ValWhnf

  syntax Expr ::= Val
  syntax Whnf ::= ValWhnf
  syntax ValWhnf2ExprT
  rule isValWhnf2ExprT((_:Expr, _:ValWhnf)) => true
  syntax Whnf2ExprT ::= ValWhnf2ExprT
  syntax ValWhnf21ExprT
  rule isValWhnf21ExprT((_:ValWhnf, _:ValWhnf)) => true
  syntax ValWhnf2ExprT ::= ValWhnf21ExprT
  syntax Whnf21ExprT ::= ValWhnf21ExprT


  // TODO: Consolidate with the unification (triggered on encountering a 'final'
  //       typed expr) and type env restoration mechanisms from -typesystem.k.
  syntax KItem ::= funDecl(Variable, Map)
  rule <k> funDecl(F, TEnv) => . ...</k>
       <meta> Meta => applyMgu(Theta, Meta) </meta>
       <tenv> TEnv' => TEnv[applyMgu(Theta, TEnv')(F)/F] </tenv>
       <mgu> Theta => .Mgu </mgu>

  // TODO: rewrite for environments (substitution-based now)
  syntax Expr ::= matchCase(List, Expr)  [function]
  rule matchCase(ListItem(P -> E1) _, E2) => E1[getMatching(P, E2)]  when isMatching(P, E2)
  rule matchCase(_ Cs:List => Cs, _)  [owise]

  rule isEnvRecovery(eval(_:ValWhnf)) => true

  syntax WhNeut ::= "[" Variable "]"    // <<< XXX THIS IS MY FIX FOR DA WHNF SPOIL OF OBDRZALEK REVISION


  // whnf-eval-deval
  syntax K ::= whnfED(Expr)     [context(result(Whnf))]
  context whnfED((HOLE:Expr => whnfED(HOLE)) _)      [result(Whnf)]

  rule whnfED(V:ValWhnf => deval(V))
  rule <k> whnfED(X:Variable => #if X in keys(Fun) #then Fun(X) #else [X] #fi) ...</k>
       <fun> Fun </fun>

  rule <k> whnfED(Pi X T T' => (Pi X whnfED(T) T')@Fun) ...</k>
       <fun> Fun </fun>
  rule <k> whnfED(Lambda X T E => (Lambda X whnfED(T) E)@Fun) ...</k>
       <fun> Fun </fun>

  rule <k> whnfED((Lambda X _ E)@Fun V => E) ~> (. => fenv(Fun')) ...</k>
       <fun> Fun' => Fun[V/X] </fun>
  rule <k> whnfED(fun(ListItem(P:Pattern -> E:Expr _))@Fun V:Val => E) ~> (. => fenv(Fun')) ...</k>
       <fun> Fun' => Fun[getMatching(P, V)] </fun>
    when isMatching(P, V)
  rule whnfED((fun(ListItem(P:Pattern -> _) Cs:List => Cs))@_ V:Val)
    when notBool isMatching(P, V)
  // TODO: add rules ^ for general P -> C:Case, not just when isExpr(C)





  // TODO eval + deval ~~ normalne whnf (see above)
  // turn eval() into normal function, aj tak neviem vymysliet context, ktory by vravel 'vyevaluovane vsetky premenne' -- co tak ValNf?
  syntax K ::= eval(Expr)     [context(result(ValWhnf))]
  context eval((HOLE:Expr => eval(HOLE)) _)      [result(ValWhnf)]
  context eval(_:Expr (HOLE => eval(HOLE)))      [result(ValWhnf)]
  context eval(Pi _ (HOLE => eval(HOLE)) _)      [result(ValWhnf)]
  context eval(Lambda _ (HOLE => eval(HOLE)) _)  [result(ValWhnf)]

  rule <k> eval(X:Variable => #if X in keys(Fun) #then Fun(X) #else [X] #fi) ...</k>
       <fun> Fun </fun>

  /*
  rule eval([E1] E2 => [E1 E2])
  rule eval(E1 [E2] => [E1 E2])
  rule [_:Expr ([E] => E)]  [structural, anywhere]
  rule [([E:Expr] => E) _]  [structural, anywhere]
  */

  /*
  rule <k> eval(X:Variable => E) ...</k>
       <fun>... X |-> E ...</fun>
  */
  /*
  rule <k> eval(X:Variable => X@Fun) ...</k>
       <fun> Fun </fun>
    when notBool (X in keys(Fun))
  rule <k> eval(X:Variable@Fun => X) ...</k>
       <fun> Fun' </fun>
    when Fun =/=Map Fun'   // Fun is attached to X as trigger only, functionally the condition should be equivalent to   X in keys(Fun')
  */
  /*
  rule <k> eval(E:Expr => E@Fun) ...</k>
       <fun> Fun </fun>
    when isVal(E) =/=K true andBool isVariable(E) =/=K true
  */
  rule <k> eval(Pi X T T' => (Pi X deval(T) T')@Fun) ...</k>
       <fun> Fun </fun>
  rule <k> eval(Lambda X T E => (Lambda X deval(T) E)@Fun) ...</k>
       <fun> Fun </fun>

  rule <k> eval((Lambda X _ E)@Fun V => E) ~> (. => fenv(Fun')) ...</k>
       <fun> Fun' => Fun[V/X] </fun>
  rule <k> eval(fun(ListItem(P:Pattern -> E:Expr _))@Fun V:Val => E) ~> (. => fenv(Fun')) ...</k>
       <fun> Fun' => Fun[getMatching(P, V)] </fun>
    when isMatching(P, V)
  rule eval((fun(ListItem(P:Pattern -> _) Cs:List => Cs))@_ V:Val)
    when notBool isMatching(P, V)
  // TODO: add rules ^ for general P -> C:Case, not just when isExpr(C)





  /*
  syntax Expr ::= deneut(Expr) [function]
  rule deneut([E]) => E
  rule deneut(E) => E [owise]
  */


  // TODO: remove
  syntax Expr ::= deval(Expr)  [function]
  rule deval([E] => E)
  rule deval(E:Expr@_ => E)
  //rule deval(E:Expr@_ => E)  //when isEmptySet(freeVariables(E))
  //rule deval(Pi X _ (E => deval(E)))  //when freeVariables(E) <=Set SetItem(X)
  //rule deval(Lambda X _ (E => deval(E)))  //when freeVariables(E) <= SetItem(X)
  rule deval((E1 => deval(E1)) (E2 => deval(E2)))
  rule deval(E:Expr) => E  [owise]
endmodule
