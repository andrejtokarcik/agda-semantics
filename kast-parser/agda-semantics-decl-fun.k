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
  rule freeVariablesM(K) => removeMetas(freeVariables(K))  [structural]
  syntax Set ::= removeMetas(Set)  [function]
  rule removeMetas(.Set) => .Set   [structural]
  rule removeMetas(SetItem(_:MetaVar) S:Set => S)  [structural]
  rule removeMetas(SetItem(E:Expr) S:Set => S) (. => SetItem(E))  [owise, structural]



  // TODO: skratit/zlucit tieto dve typeVars
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
    //when notBool (funName(L) in keys(TEnv))
  // if a clause of the same function has been already processed, the type
  // assigned to the function name will be re-used, causing type errors
  // if the clauses' respective result/arg types aren't unifiable

  context HOLE:LHS = _ ~> funDecl(_, _)

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
     when numArgs(L) ==Int 0 //andBool notBool (F in keys(Fun))  // << checked for with 'true?'
  // it is an error to have numArgs == 0 && F in keys(Fun)

  rule <k> (L:LHS, _) = _ ~> funDecl(F:Variable, _) ...</k>
       <fun> Fun (. => F |-> fun(.List)@Fun) </fun>
    when numArgs(L) >Int 0 andBool notBool (F in keys(Fun))

  // TODO: check that number of patterns is the same as for the other definitional equations (see error msg in offic typechecker)
  // TODO: podobny check s freeVariables ako vyssie
  syntax KItem ::= s(Set)
  rule <k> ((L:LHS, Tl:Expr) = (E:Expr, Te:Expr) => /*Fun <=Map Fun' ~> true? ~> keys(Fun') -Set keys(Fun) <=Set SetItem(F) ~> true? ~>*/ Tl == Te) ~> funDecl(F:Variable, _) ...</k>
       <fun> Fun (F |-> fun(_:List (. => ListItem(mkCase(L, E))))@Fun) </fun>
       //// Fun' may contain F as key (from the funDecl <fun/> update), Fun certainly does not (since Fun is matched as the rest of the map besides F)
     when numArgs(L) >Int 0 //andBool F in keys(Fun)

  syntax Case ::= mkCase(LHS, Case)   [function]
  rule mkCase(_:Variable, C:Case) => C
  rule mkCase(L:LHS P:Pattern, C:Case) => mkCase(L, P -> C)

  syntax Case ::= Expr
                | Pattern "->" Case   [binder]
  // NOTE: to put fun(List) into Nf isn't sufficient for fun may be applied to a variable that is only bound (not instantiated),
  // in which case we can't know yet which branch of the cases list to follow
  //syntax Neut ::= fun(List)     // ~ List{Case}
  syntax FunL ::= fun(List)
  syntax Nf ::= FunL
  syntax Neut ::= FunL Variable

  // TODO: Consolidate with the unification (triggered on encountering a 'final'
  //       typed expr) and type env restoration mechanisms from -typesystem.k.
  syntax KItem ::= funDecl(Variable, Map)
  rule <k> funDecl(F, TEnv) => . ...</k>
       <meta> Meta => applyMgu(Theta, Meta) </meta>
       <tenv> TEnv' => TEnv[applyMgu(Theta, TEnv')(F)/F] </tenv>
       //<fun> Fun => Fun[Fun(F)@Fun/F] </fun>   // XXX enclose the function body within the complete decl environment
       <mgu> Theta => .Mgu </mgu>















  syntax Val ::= "(" Val ")" [bracket]
               | Expr "@" Map   // closure
               | Val Val

  // XXX: rewrite with [prec(_)] attribute? perhaps my K version doesn't support it yet?
  syntax priorities '_@_ > '__      // closure > app

  syntax ValWhnf ::= Universe | WhNeut
  syntax ValWhnf ::= WhNeut Val [left]
  rule isValWhnf(E:Whnf@_) => true  when isWhNeut(E) =/=K true    // ValWhnf contains WhNeut directly, don't wanna @Fun duplications

  //rule isValWhnf(E) => true  when isEmptySet(freeVariables(E))
  //rule E@_ => E  when isEmptySet(freeVariables(E))  [structural, anywhere]

  //syntax WhNeut ::= "[" Variable "]"    // <<< XXX THIS IS MY FIX FOR DA WHNF SPOIL OF OBDRZALEK REVISION
  // `--- added to Whnf as well as Nf's Neut

  syntax Val ::= "^"   // bound -- vraj historicky symbol na oznacenie prave bound premennych

  syntax Set ::= boundKeys(Map)  [function]
  rule boundKeys(.Map) => .Set   [structural]
  rule boundKeys((E |-> ^ => .) _) (. => SetItem(E)) [structural]
  rule boundKeys((_ |-> _ => .) _) [owise, structural]
  /*
  syntax Set ::= boundKeys(Map)  [function]
  rule boundKeys(M) => onlyBound(keys(M), M)
  // prepend these helper functions with $ or #?
  syntax Set ::= onlyBound(Set, Map)  [function]
  rule onlyBound(.Set, _) => .Set
  rule onlyBound(SetItem(K) S:Set, M) => SetItem(K) onlyBound(S, M)  when M(K) ==K ^
  rule onlyBound(SetItem(K) S:Set => S, _)  [owise]
  */



  // may replace these with an isBinder() and an #if clause for the case of updating Fun
  //rule X:Variable@Rho => #if X in keys(Rho) #then Rho(X) #else S #fi when fresh(S:Expr) [structural, anywhere]
  rule X:Variable@Rho => #if X in keys(Rho) andBool Rho(X) =/=K ^ #then Rho(X)@Rho #else X #fi  [structural, anywhere]
  rule U:Universe@_ => U [structural, anywhere]
  rule N:WhNeut@_ => N   [structural, anywhere]
  rule (E1:Expr E2:Expr)@Rho => E1@Rho E2@Rho [structural, anywhere]

  // have to take advantage of abstract syntax here, or else K complains about E@RhoOrig's not being an Expr but a Val
  // i.e. (E@R1)@R2 => update
  rule '_@_(E:Expr@RhoOrig,, Map2KLabel(RhoNew:Map)(.KList)) => E@(RhoNew[RhoOrig]) [structural, anywhere]     // original context has higher priority, its values are just extended not modified
  //rule K:Expr@M => nft [structural, anywhere]
  //rule '_@_(E:Expr@RhoOrig,, RhoNew:Map) => E@(RhoNew[RhoOrig]) [structural, anywhere]
  //rule (((E:Expr@RhoOrig)::Expr)@RhoNew) => E@(RhoNew[RhoOrig]) [structural, anywhere]     // original context has higher priority

  /*
  syntax Val ::= extendCon(Val, Map) [function]
  rule extendCon(V@RhoOrig, RhoNew) => V@(RhoNew[RhoOrig])   // original context has higher priority
  rule exntedCon(V, RhoNew) => V@RhoNew [owise]
  */

  syntax Val ::= ValWhnf

  //syntax Expr ::= Val
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




  rule isFunRestore(evalWhnf(_:Whnf)) => true


  

  syntax K ::= evalWhnf(K)     [context(result(Whnf))]
  // XXX !!! HOLE:<sort> does NOT enforce dynamic checks that HOLE is of sort <sort>,
  // possibly a bug in K (check newer versions before reporting),
  // it might be just an indication how to _parse_ the item [as with ::]
  context evalWhnf((HOLE:Expr => nft ~> isExpr(HOLE) ~> evalWhnf(HOLE)) _)
      when isExpr(HOLE)    [result(Whnf)]  // << 'when' clause necessary due to the bug mentioned above

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

  // the following rule isn't ever triggerred anyway as Variable is in Whnf,
  // which is the context result of evalWhnf and thus evalWhnf stops
  // on encountering it
  /*
  rule <k> evalWhnf(X:Variable => X@Fun) ...</k>
       <fun> Fun </fun>
    when X in keys(Fun)
  */
  rule <k> evalWhnf(E:Expr => E@Fun) ...</k>
       <fun> Fun </fun>
    when /*isWhnf(E) =/=K true andBool // << implicit in context(result(Whnf)) */ isVal(E) =/=K true

  rule <k> evalWhnf((Lambda X _ E:Expr)@Fun V:Val => E@(Fun[V/X])) ~> (. => fenv(Fun')) ...</k>
       <fun> Fun' </fun>
  rule <k> evalWhnf(fun(Cs:List)@Fun V:Val => matchCase(Cs, V, Fun)) ~> (. => fenv(Fun')) ...</k>
       <fun> Fun' </fun>
  // TODO: add rules ^ for general P -> C:Case, not just when isExpr(C)

  // TODO: ked sa zoznam zredukuje na .List (t.j. nenasli sme match) a zaroven V neobsahuje bound premenne (t.j. V je uplne konkretna) tak daj error?
  syntax Expr ::= matchCase(List, Val, Map)  [function]
  rule matchCase(ListItem(P -> E) _, V, Rho) => E@(Rho[getMatching(P, V)])  when isMatching(P, V)
  rule matchCase(_ Cs:List => Cs, _, _)  [owise]



  syntax K ::= evalNf(K)     [strict(all(context('evalWhnf)))]   //, context(result(Nf))]
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

  rule <k> evalNf(Pi X:Variable E1:Expr E2:Expr) => evalNf(E2@(Fun[^/X])) ~> evalNf(Pi X E1 HOLE) ...</k>
       <fun> Fun </fun>
    when needEval(E2, Fun[^/X]) //[heat]

  rule <k> evalNf(E2:Nf) ~> evalNf(Pi X:Variable E1:Expr HOLE) => evalNf(Pi X E1 E2) ...</k>
       <fun> Fun </fun>
    when notBool needEval(E2, Fun) //[cool]


  rule <k> evalNf(Lambda X:Variable E1:Expr E2:Expr) => evalNf(E1@Fun) ~> evalNf(Lambda X HOLE E2) ...</k>
       <fun> Fun </fun>
    when needEval(E1, Fun) //[heat]

  rule <k> evalNf(E1:Nf) ~> evalNf(Lambda X:Variable HOLE E2:Expr) => evalNf(Lambda X E1 E2) ...</k>
       <fun> Fun </fun>
    when notBool needEval(E1, Fun) //[cool]

  rule <k> evalNf(Lambda X:Variable E1:Expr E2:Expr) => evalNf(E2@(Fun[^/X])) ~> evalNf(Lambda X E1 HOLE) ...</k>
       <fun> Fun </fun>
    when needEval(E2, Fun[^/X]) //[heat]

  rule <k> evalNf(E2:Nf) ~> evalNf(Lambda X:Variable E1:Expr HOLE) => evalNf(Lambda X E1 E2) ...</k>
       <fun> Fun </fun>
    when notBool needEval(E2, Fun) //[cool]


  // XXX added fun(List) to Nf (was Whnf), the following shouldn't be necessary
  /*
  rule <k> evalNf(fun(L:List)) => evalNf(L@Fun) ~> evalNf(fun(HOLE)) ...</k>
       <fun> Fun </fun>
    when needEval(L, Fun) //[heat]

  rule <k> evalNf(L:List) ~> evalNf(fun(HOLE)) => evalNf(L) ...</k>
       <fun> Fun </fun>
    when notBool needEval(L, Fun) //[cool]
  */




  /*
  rule <k> evalNf(Pi X [T] T' => (Pi X T T')@Fun) ...</k>
       <fun> Fun </fun>
  rule <k> evalNf(Lambda X [T] E => (Lambda X T E)@Fun) ...</k>
       <fun> Fun </fun>
  */






  // TODO: remove  resp. slo by to urobit jak context? co by bol ale result? akesi BaseExpr?
  syntax Expr ::= deval(K)  [function]
  //rule deval([E] => E)
  rule deval(E:Expr@_ => E)
  //rule deval(E:Expr@_ => E)  //when isEmptySet(freeVariables(E))
  //rule deval(Pi X _ (E => deval(E)))  //when freeVariables(E) <=Set SetItem(X)
  //rule deval(Lambda X _ (E => deval(E)))  //when freeVariables(E) <= SetItem(X)
  rule deval((E1 => deval(E1)) (E2 => deval(E2)))
  rule deval(E:Expr) => E  [owise]
endmodule
