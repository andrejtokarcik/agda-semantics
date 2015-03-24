require "modules/substitution.k"
require "agda-syntax.k"
require "agda-semantics-normal.k"
require "agda-semantics-typesystem.k"
require "agda-semantics-decl-data.k"

module AGDA-SEMANTICS-DECL-FUN
  imports SUBSTITUTION      // FIXME: move these imports into a generic module (or specific declarations used, freeVariables() in this case)
  imports AGDA-SYNTAX
  imports AGDA-SEMANTICS-TYPESYSTEM
  imports AGDA-SEMANTICS-NORMAL
  imports AGDA-SEMANTICS-DECL-DATA


  // put into -metavariables.k
  syntax Set ::= freeVariablesM(K)    [function]   // free vars without metas
  rule freeVariablesM(K) => removeMetas(freeVariables(K))
  syntax Set ::= removeMetas(Set)  [function]
  rule removeMetas(.Set) => .Set
  rule removeMetas(SetItem(_:MetaVar) S:Set => S)
  rule removeMetas(SetItem(E:Expr) S:Set) => SetItem(E) removeMetas(S)  [owise]



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

  syntax KItem ::= "Hihi"
  rule <k> L:LHS = E:Expr => typeVars(L) ~> L = E ~> funDecl(funName(L), TEnv) ...</k>
       <tenv> TEnv </tenv>
    when notBool (funName(L) in keys(TEnv))
  // if a clause of the same function has been already processed, the type
  // assigned to the function name will be re-used, causing type errors
  // if the clauses' respective result/arg types aren't unifiable

  context (HOLE:LHS => HOLE) = _ ~> funDecl(_, _)

  // NOTE: eval21 nizsie blblo kvoli meta-id.dt -- co je ale aj tak dzivne
  // eval2 je ale ok lebo aj tak nechcem evaluavat vyrazy pokial nemusim ci?
  // (typy, narozdiel od striktnych 'vyrazov', musim kvoli checkingu)
  // XXX: jj, imo nech mam pristup: be as lazy as possible [a nech sa evaluuje aj viackrat to iste,
  // hoci to bude neefektivne -- hram predovsetkym na korektnost]
  // ved aj tak robim typechecker a nie interpreter... ci?
  // (pozri poznamky ku kompilacii agdy, main ako entry point = vyraz na vyhodnotenie)
  context _:LHST = (HOLE => evalWhnf2(HOLE)) ~> funDecl(_, _)  [result(Whnf2ExprT)]


  rule <k>
         (
           (L:LHS, Tl:Expr) = (E:Expr, Te:Expr)
             =>
           notBool (F in keys(Fun)) ~> true? ~>                             // verify that F isn't already defined
           freeVariablesM(E) <=Set freeVariablesM(L) keys(Fun) ~> true? ~>    // that the body of F doesn't contain undefined functions (check TEnv instead b/c of mutual recursion)
           Tl == Te
         ) ~> funDecl(F:Variable, _)
       ...</k>
       <fun> Fun (. => F |-> E@Fun) </fun>
     when numArgs(L) ==Int 0


  rule <k> L:LHS = E:Expr ...</k>
       <fun> Fun (. => funName(L) |-> fun(.List)@Fun) </fun>
    when numArgs(L) >Int 0 andBool notBool (funName(L) in keys(Fun))

  // XXX: manually apply updateMgu() & applyMgu() in order to get rid of funDecl()?
  // TODO: check that number of patterns is the same as for the other definitional equations (see error msg in offic typechecker)
  // TODO: podobny check s freeVariables ako vyssie
  rule <k> ((L:LHS, Tl:Expr) = (E:Expr, Te:Expr) => Fun[undef/F] ==Map Fun'[undef/F] ~> true? ~> Tl == Te) ~> funDecl(F:Variable, _) ...</k>
       <fun> Fun (F |-> fun(_ (. => ListItem(mkCase(L, E@Fun))))@Fun') </fun>
     when numArgs(L) >Int 0

  syntax Case ::= mkCase(LHS, Case)   [function]
  rule mkCase(_:Variable, C:Case) => C
  rule mkCase(L:LHS P:Pattern, C:Case) => mkCase(L, P -> C)

  syntax Case ::= Expr
                | Pattern "->" Case   [binder]
  syntax Whnf ::= fun(List)     // ~ List{Case}

  // TODO: Consolidate with the unification (triggered on encountering a 'final'
  //       typed expr) and type env restoration mechanisms from -typesystem.k.
  syntax KItem ::= funDecl(Variable, Map)
  rule <k> funDecl(F, TEnv) => . ...</k>
       <meta> Meta => applyMgu(Theta, Meta) </meta>
       <tenv> TEnv' => TEnv[applyMgu(Theta, TEnv')(F)/F] </tenv>
       <mgu> Theta => .Mgu </mgu>















  syntax Val ::= "(" Val ")" [bracket]
               | Expr "@" Map   // closure
  // XXX: rewrite with [prec(_)] attribute? perhaps my K version doesn't support it yet?
  syntax priorities '_@_ > '__      // closure > app

  syntax ValWhnf ::= Universe | WhNeut
  rule isValWhnf(E:Whnf@_) => true  when isWhNeut(E) =/=K true    // ValWhnf contains WhNeut directly, don't wanna @Fun duplications

  //rule isValWhnf(E) => true  when isEmptySet(freeVariables(E))
  //rule E@_ => E  when isEmptySet(freeVariables(E))  [structural, anywhere]

  //syntax WhNeut ::= "[" Variable "]"    // <<< XXX THIS IS MY FIX FOR DA WHNF SPOIL OF OBDRZALEK REVISION
  // `--- added to Whnf as well as Nf's Neut

  syntax Val ::= "^"   // bound -- vraj historicky symbol na oznacenie prave bound premennych

  syntax Set ::= boundKeys(Map)  [function]
  rule boundKeys(M) => onlyBound(keys(M), M)
  // prepend these helper functions with $ or #?
  syntax Set ::= onlyBound(Set, Map)  [function]
  rule onlyBound(.Set, _) => .Set
  rule onlyBound(SetItem(K) S:Set, M) => SetItem(K) onlyBound(S, M)  when M(K) ==K ^
  rule onlyBound(SetItem(K) S:Set => S, _)  [owise]



  // may replace these with an isBinder() and an #if clause for the case of updating Fun
  //rule X:Variable@Rho => #if X in keys(Rho) #then Rho(X) #else S #fi when fresh(S:Expr) [structural, anywhere]
  rule X:Variable@Rho => #if X in keys(Rho) andBool Rho(X) =/=K ^ #then Rho(X)@Rho #else X #fi  [structural, anywhere]
  rule U:Universe@_ => U [structural, anywhere]
  rule N:WhNeut@_ => N   [structural, anywhere]
  rule (E1:Expr E2:Expr)@Rho => E1@Rho E2@Rho [structural, anywhere]

  syntax Val ::= ValWhnf

  syntax Expr ::= Val
  /*
  syntax Whnf ::= ValWhnf
  syntax ValWhnf2ExprT
  rule isValWhnf2ExprT((_:Expr, _:ValWhnf)) => true
  syntax Whnf2ExprT ::= ValWhnf2ExprT
  syntax ValWhnf21ExprT
  rule isValWhnf21ExprT((_:ValWhnf, _:ValWhnf)) => true
  syntax ValWhnf2ExprT ::= ValWhnf21ExprT
  syntax Whnf21ExprT ::= ValWhnf21ExprT
  */


  // TODO: rewrite for environments (substitution-based now)
  syntax Expr ::= matchCase(List, Expr)  [function]
  rule matchCase(ListItem(P -> E1) _, E2) => E1[getMatching(P, E2)]  when isMatching(P, E2)
  rule matchCase(_ Cs:List => Cs, _)  [owise]



  rule isEnvRecovery(evalWhnf(_:Whnf)) => true


  

  syntax K ::= evalWhnf(Expr)     [context(result(Whnf))]
  context evalWhnf((HOLE:Expr => evalWhnf(HOLE)) _)      [result(Whnf)]

  /*
  rule <k> evalWhnf(E1:Expr E2:Expr) => evalWhnf(E1) ~> evalWhnf(HOLE E2) ...</k>
       <fun> Fun </fun>
    when needEval(E1, Fun) [heat]

  rule <k> evalWhnf(E1:Whnf) ~> evalWhnf(HOLE E2:Expr) => evalWhnf(E1 E2) ...</k>
       <fun> Fun </fun>
    when notBool needEval(E1, Fun) [cool]
  */


  rule evalWhnf(E:ValWhnf => deval(E))  when isWhnf(E) =/=K true

  // to force evaluation
  /*
  syntax Expr ::= Expr "@-"
  rule <k> evalWhnf(E:Expr@- => E@Fun) ...</k>
       <fun> Fun </fun>
  */

  rule <k> evalWhnf(X:Variable => X@Fun) ...</k>
       <fun> Fun </fun>
    when X in keys(Fun)
  rule <k> evalWhnf(E:Expr => E@Fun) ...</k>
       <fun> Fun </fun>
    when /*isWhnf(E) =/=K true andBool // << implicit in context(result(Whnf)) */ isVal(E) =/=K true

  rule <k> evalWhnf((Lambda X _ E)@Fun V => E) ~> (. => fenv(Fun')) ...</k>
       <fun> Fun' => Fun[V/X] </fun>
  rule <k> evalWhnf(fun(ListItem(P:Pattern -> E:Expr _))@Fun V:Val => E) ~> (. => fenv(Fun')) ...</k>
       <fun> Fun' => Fun[getMatching(P, V)] </fun>
    when isMatching(P, V)
  rule evalWhnf((fun(ListItem(P:Pattern -> _) Cs:List => Cs))@_ V:Val)
    when notBool isMatching(P, V)
  // TODO: add rules ^ for general P -> C:Case, not just when isExpr(C)



  syntax K ::= evalNf(Expr)     [strict(all(context('evalWhnf)))]   //, context(result(Nf))]
  /*
  context evalNf((HOLE:Expr => evalNf(HOLE)) _)      [result(Nf)]
  context evalNf(_:Expr (HOLE => evalNf(HOLE)))      [result(Nf)]
  context evalNf(Pi _ (HOLE => evalNf(HOLE)) _)      [result(Nf)]
  context evalNf(Pi _ _ (HOLE => evalNf(HOLE)))      [result(Nf)]
  context evalNf(Lambda _ (HOLE => evalNf(HOLE)) _)  [result(Nf)]
  context evalNf(Lambda _ _ (HOLE => evalNf(HOLE)))  [result(Nf)]
  */

  syntax KItem ::= "nft"

  /*
  rule <k> evalNf(E:Expr) => evalWhnf(E) ~> evalNf(HOLE) ...</k>
       <fun> Fun </fun>
    when isWhnf(E) =/=K true //orBool needEval(E, Fun) //[heat]
  rule <k> evalWhnf(E:Whnf) ~> evalNf(HOLE) => evalNf(E) ...</k>
       <fun> Fun </fun>
    //when notBool needEval(E, Fun) //[cool]
  */
  

  // TODO: some general scheme/function for all the rules below, or something
  rule <k> evalNf(E1:Expr E2:Expr) => evalNf(E1@Fun) ~> evalNf(HOLE:Expr E2) ...</k>
       <fun> Fun </fun>
    when needEval(E1, Fun) //andBool isWhnf(E1 E2) //[heat]

  rule <k> evalNf(E1:Nf) ~> evalNf(HOLE:Expr E2:Expr) => evalNf(E1 E2) ...</k>
       <fun> Fun </fun>
    when notBool needEval(E1, Fun) //[cool]

  rule <k> evalNf(E1:Expr E2:Expr) => evalNf(E2@Fun) ~> evalNf(E1 HOLE:Expr) ...</k>
       <fun> Fun </fun>
    when needEval(E2, Fun) //andBool isWhnf(E1 E2) //[heat]

  rule <k> evalNf(E2:Nf) ~> evalNf(E1:Expr HOLE:Expr) => evalNf(E1 E2) ...</k>
       <fun> Fun </fun>
    when notBool needEval(E2, Fun) //[cool]


  rule <k> evalNf(Pi X:Variable E1:Expr E2:Expr) => evalNf(E1@Fun) ~> evalNf(Pi X HOLE E2) ...</k>
       <fun> Fun </fun>
    when needEval(E1, Fun) //[heat]

  rule <k> evalNf(E1:Nf) ~> evalNf(Pi X:Variable HOLE E2:Expr) => evalNf(Pi X E1 E2) ...</k>
       <fun> Fun </fun>
    when notBool needEval(E1, Fun) //[cool]

  rule <k> evalNf(Pi X:Variable E1:Expr E2:Expr) => evalNf(E2@Fun) ~> evalNf(Pi X E1 HOLE) ...</k>
       <fun> Fun </fun>
    when needEval(E2, Fun) //[heat]

  rule <k> evalNf(E2:Nf) ~> evalNf(Pi X:Variable E1:Expr HOLE) => evalNf(Pi X E1 E2) ...</k>
       <fun> Fun </fun>
    when notBool needEval(E2, Fun) //[cool]


  rule <k> evalNf(Lambda X:Variable E1:Expr E2:Expr) => evalNf(E1@Fun) ~> evalNf(Lambda X HOLE E2) ...</k>
       <fun> Fun </fun>
    when needEval(E1, Fun) //[heat]

  rule <k> evalNf(E1:Nf) ~> evalNf(Lambda X:Variable HOLE E2:Expr) => evalNf(Lambda X E1 E2) ...</k>
       <fun> Fun </fun>
    when notBool needEval(E1, Fun) //[cool]

  rule <k> evalNf(Lambda X:Variable E1:Expr E2:Expr) => evalNf(E2@Fun) ~> evalNf(Lambda X E1 HOLE) ...</k>
       <fun> Fun </fun>
    when needEval(E2, Fun) //[heat]

  rule <k> evalNf(E2:Nf) ~> evalNf(Lambda X:Variable E1:Expr HOLE) => evalNf(Lambda X E1 E2) ...</k>
       <fun> Fun </fun>
    when notBool needEval(E2, Fun) //[cool]




  /*
  rule <k> evalNf(Pi X [T] T' => (Pi X T T')@Fun) ...</k>
       <fun> Fun </fun>
  rule <k> evalNf(Lambda X [T] E => (Lambda X T E)@Fun) ...</k>
       <fun> Fun </fun>
  */






  // TODO: remove  resp. slo by to urobit jak context? co by bol ale result? akesi BaseExpr?
  syntax Expr ::= deval(Expr)  [function]
  //rule deval([E] => E)
  rule deval(E:Expr@_ => E)
  //rule deval(E:Expr@_ => E)  //when isEmptySet(freeVariables(E))
  //rule deval(Pi X _ (E => deval(E)))  //when freeVariables(E) <=Set SetItem(X)
  //rule deval(Lambda X _ (E => deval(E)))  //when freeVariables(E) <= SetItem(X)
  rule deval((E1 => deval(E1)) (E2 => deval(E2)))
  rule deval(E:Expr) => E  [owise]
endmodule
