require "modules/pattern-matching.k"
require "modules/unification.k"
require "agda-syntax.k"//-pretty.k"

module AGDA-SEMANTICS-COMMON
  imports PATTERN-MATCHING
  imports UNIFICATION
  imports AGDA-SYNTAX//-PRETTY

  syntax KResult ::= TypedExpr

  /*
  // TODO: if we defined ValNf, we could reduce needEval() to a check
  // of belonging to the syntactic sort ValNf
  syntax Bool ::= needEval(K, Map)  [function]
  rule needEval((_, T:Expr) => T, _)
  rule needEval(E:Expr, _) => true when isNf(E) =/=K true
  // do *not* want freeVariablesM here
  rule needEval(E, Rho) => notBool isEmptySet(intersectSet(freeVariables(E), keys(Rho) -Set boundKeys(Rho))) [owise]
  // `-Set boundKeys` not necessary because binder takes care of it?
  // -- it *is* necessary since the var may have been bound in a 'higher' bounder, not in this one,
  //    i.e. it will be superfluous only for the var bound just now
  */

  syntax TEnvRestore
  rule isTEnvRestore(_:TypedExpr) => true
  syntax KItem ::= tenv(Map)
  rule <k> tenv(Gamma) => . ...</k>
       <tenv> _ => Gamma </tenv>
  rule R:TEnvRestore ~> tenv(Gamma) => tenv(Gamma) ~> R

  syntax KItem ::= "chich"
  syntax FEnvRestore
  //rule isFEnvRestore(_:NfTypedExpr) => true
  rule isFEnvRestore(_:TypedExpr) => true
  syntax KItem ::= fenv(Map)
  // XXX: must use 'isTypedExpr(HOLE)' instead of 'HOLE:TypedExpr'
  // due to the possible K BUG described below  (the latter doesn't
  // generate the dynamic sort check as intended).
  //context (HOLE => nfType(HOLE)) ~> fenv(_) when isTypedExpr(HOLE)  [result(NfTypedExpr)]
  // XXX: why do I need to use nfType here actually, isn't whnf enough...?
  // no, because of pattern matching -- an arg of a pattern-matching function must be evaluated
  // but this should be done by whnf as well, I guess, given there is the right number of arguments
  // --- potom by som tu nemusel robit ziaden spesl eval a nechal to proste na tie whnfType volania,
  // co sa urobia v buducnosti pri inych konstruktoch, ak bude treba
  rule <k> _:FEnvRestore ~> (fenv(Rho) => .) ...</k>
       <fenv> _ => Rho </fenv>

  syntax GuardPass
  rule isGuardPass(true) => true
  syntax KItem ::= "pass?"
  rule _:GuardPass ~> pass? => .
  // TODO: error handling/reporting like:
  //  rule E ~> pass? => error(E) when E =/=K true




  syntax K ::= leftmost(K)  [function]
  rule leftmost(E:Expr _ => E)
  rule leftmost(V:Val _ => V)
  rule leftmost(K) => K [owise]




  syntax TypedExpr ::= t(Expr, Expr)    [latex(({#1}\downarrow{#2}))]    // XXX this would indicate a type-*inference* result
  syntax Expr ::= TypedExpr


  // XXX: should these be in a separate file -normal.k as before...?

  syntax Whnf ::= "(" Whnf ")" [bracket]
                | WhNeut
                /*
                | "Set" Int
                | "(" Name ":" Expr ")" "->" Expr        [binder(2 -> 4)]
                | "\\" "(" Name ":" Expr ")" "->" Expr   [binder(2 -> 4)]
                */
  syntax WhNeut /*::= Variable     // considered neutral only if cannot be evaluted
                  | Name
                  | WhNeut Expr [left]
                  */
  rule isWhNeut(_:WhNeut _:Expr) => true
  rule isWhnf({_:Whnf}) => true
  rule isWhnf(Set(_)) => true
  rule isWhnf((_ : _) -> _) => true
  rule isWhnf({_ : _} -> _) => true     // AT FIXME hack - generalise
  rule isWhnf(\ (_ : _) -> _) => true
  
  syntax Nf ::= "(" Nf ")" [bracket]
                | Neut
                /*
                | "Set" Int
                | "(" Name ":" Nf ")" "->" Nf        [binder(2 -> 4)]
                | "\\" "(" Name ":" Nf ")" "->" Nf   [binder(2 -> 4)]
                */
  syntax Neut //::= Neut(Name)
  /*::= Variable       // considered neutral only if cannot be evaluated
                | Name
                | Neut Nf [left]
                */
  //rule isNeut(_:Variable) => true   // AT HACK?
  rule isNeut(_:Name) => true
  rule isNeut(_:Neut _:Nf) => true
  rule isNf(Set(_)) => true
  rule isNf((_ : _:Nf) -> _:Nf) => true
  rule isNf(\ (_ : _:Nf) -> _:Nf) => true

  syntax WhNeut ::= Neut
  syntax Whnf ::= Nf
  syntax Expr ::= Whnf

  syntax NfTypedExpr
  rule isNfTypedExpr(t(_, _:Nf)) => true
  syntax WhnfTypedExpr ::= NfTypedExpr
  rule isWhnfTypedExpr(t(_, _:Whnf)) => true
  syntax TypedExpr ::= WhnfTypedExpr | NfTypedExpr

  syntax SetTypedExpr
  //rule isSetTypedExpr(t(_:Expr, _:MetaVariable)) => true   // XXX hack
  rule isSetTypedExpr(t(_, Set(_))) => true
  syntax NfTypedExpr ::= SetTypedExpr




  /*
  syntax KItem ::= Expr "==" Expr
             | Mgu "&&" Expr "==" Expr
  rule T1 == T2 => .Mgu && T1 == T2   [macro]
  rule Theta:Mgu && T1 == T2 => updateMgu(Theta, T1, T2)  [macro]
  */

  /*
  syntax Bool ::= "noMguError"
  rule <k> noMguError => isMguError(Theta) =/=K true ...</k>
       <mgu> Theta </mgu>
  */

  syntax KItem ::= K "==" K
  rule <k> K == K' => . ...</k>
       <mgu> Theta => updateMgu(Theta, K, K') </mgu>

  syntax KItem ::= "unify"
  rule <k> unify => . ...</k>
       <sig> Sigma => applyMgu(Theta, Sigma) </sig>
       <tenv> Gamma => applyMgu(Theta, Gamma) </tenv>
       <fenv> Rho => applyMgu(Theta, Rho) </fenv>
       <metavars> Meta => applyMgu(Theta, Meta) </metavars>
       <mgu> Theta => .Mgu </mgu>
    when isMguError(Theta) =/=K true

  /*
  syntax KItem ::= unify(K)         [context(result(Unified))]   //[strict(all(context('whnf)))]
  syntax Unified ::= unified(K)
  rule <k> (. => unify) ~> unify(K => unified(unify(Theta, K))) ...</k>
       <mgu> Theta </mgu>
    when getKLabel(K) =/=KLabel 'unified
  */

  syntax KItem ::= unify(Expr)
  rule <k> unify(E) => unify ~> applyMgu(Theta, E) ...</k>
       <mgu> Theta </mgu>

  syntax KItem ::= unifyType(TypedExpr)     //[context(result(Unified))]
  rule <k> unifyType(t(E, T)) => unify ~> t(E, applyMgu(Theta, T)) ...</k>
       <mgu> Theta </mgu>

  /*
  context unifyType(t(_, HOLE => unify(HOLE)))   [result(Unified)]
  rule unifyType(t(E, unified(T)) => unified(t(E, T)))
  */

  syntax KItem ::= checkUniverse(Expr)
  rule checkUniverse(T) => whnf(T) == Set(I) ~> unify(whnf(T))  when fresh(I:Int)
  /*
  syntax KItem ::= checkSetType(Expr)  [strict]
  rule checkSetType(t(E, T)) => whnf(T) == Set(I) ~> unifyType(t(E, whnf(T)))  when fresh(I:Int)
  */
  /*
  syntax KItem ::= checkSetType(Expr)  [strict, context(result(SetTypedExpr))]  //[strict(all(context('whnfType))), 
  rule checkSetType(t(E, T)) => T == Set(I) ~> unifyType(t(E, T)) ~> checkSetType(HOLE)  //[heat]
    when isSetTypedExpr(t(E, T)) =/=K true andBool fresh(I:Int)
  rule Te:SetTypedExpr ~> checkSetType(HOLE) => checkSetType(Te)
  */
  /*
  rule checkSetType(t(E, T:Expr)) => T == Set I ~> unifyType(t(E, T)) ~> checkSetType(HOLE)
    when isSetTypedExpr(t(E, T)) =/=K true andBool fresh(I:Int)
  rule Set I ~> checkSetType(t(E, HOLE)) => checkSetType(t(E, Set I))
  */




  syntax Val ::= "(" Val ")" [bracket]
               | Expr "@" Map   [klabel('closure)]   // << may mark as function?
               | Val Val  [left]

  syntax Val ::= "^"      [latex(^\wedge)]  // bound -- vraj aj historicky symbol na oznacenie prave bound premennych
  // ^ imo nie je nutne ale nie som si isty...


  /*
  syntax Map ::= Map "[" K "/" Set "]"  [function]
  rule M[K/(S SetItem(X))] => M[K/X][K/S]  [structural]
  rule M[K/.Set] => M  [structural]
  */
  // NOTE: use instead of freeVariables & co.
  /*
  syntax Bool ::= needsEval(Expr, Map)   [function]
  rule needsEval(X:Variable, Rho) => Rho(X) ==K ^
  rule needsEval(N:Name, Rho) => N in keys(Rho)
  //rule needsEval(Set(_), _) => false
  rule needsEval(E1:Expr E2:Expr, Rho) => needsEval(E1, Rho) orBool needsEval(E2, Rho)
  */
  /*
  rule needsEval((X : _) -> E => E, Rho (. => X |-> ^))
  rule needsEval({X : _} -> E => E, Rho (. => X |-> ^))
  rule needsEval(\ (X : _) -> E => E, Rho (. => X |-> ^))
  rule needsEval(\ {X : _} -> E => E, Rho (. => X |-> ^))
  */
  /*
  rule needsEval(L = R => R, Rho => Rho[^/freeVariables(L)])
  rule needsEval(FunClauses(I, ListItem(L = R) Cs), Rho) => needsEval(L = R, Rho) orBool needsEval(FunClauses(I, Cs), Rho)
  rule needsEval(FunClauses(_, .List), _) => false
  */

  syntax Set ::= boundKeys(Map)  [function]
  rule boundKeys(.Map) => .Set   [structural]
  rule boundKeys((E |-> ^ => .) _) (. => SetItem(E)) [structural]
  rule boundKeys((_ |-> _ => .) _) [owise, structural]

  /*
  syntax Map ::= sanitise(Expr, Map)  [function]
  rule sanitise(, Rho) => 
  */

  // The following rules are where most of the evaluation magic happens...
  rule X:Variable@Rho => #if X in keys(Rho) -Set boundKeys(Rho) #then Rho(X)@Rho #else X #fi  [structural, anywhere]

  //rule Neut(E)@_ => Neut(E)  [structural, anywhere]
  rule N:Name@Rho => #if N in keys(Rho) #then Rho(N)@Rho #else N #fi [structural, anywhere]

  //rule X:Variable@Rho => Rho(X)@Rho  when needsEval(X, Rho)   [structural, anywhere]
  //rule N:Name@Rho => Rho(N)@Rho  when needsEval(N, Rho)     [structural, anywhere]

  rule (Set(I))@_ => Set(I) [structural, anywhere]
  rule E:WhNeut@Rho => E when notBool needsEval(E, Rho)  [structural, anywhere]
  //rule E:WhNeut@_ => E  when isVariable(leftmost(E)) =/=K true andBool isName(leftmost(E)) =/=K true [structural, anywhere]
  //rule E:WhNeut@Rho => E when notBool (leftmost(E) in keys(Rho) -Set boundKeys(Rho))   [structural, anywhere]


  rule (E1:Expr E2:Expr)@Rho => E1@Rho E2@Rho  [structural, anywhere]
  //rule (E1:Expr E2:Expr)@Rho => E1@Rho E2@Rho  when needsEval(E1 E2, Rho) [structural, anywhere]    // nestaci E1@Rho E2 -- dat @Rho len na prvy expr?
                                                                                                      // NIE lebo tym prave stracam tie data o argumentoch vo WhNeut

  //rule E:Expr@Rho => E  when isValWhnf(E@Rho) [structural, anywhere]
  //rule E:Expr@Rho => E when isEmptySet(intersectSet(freeVariables(E), keys(Rho) -Set boundKeys(Rho)))  [structural, anywhere]
  //rule E:Expr@(Rho => sanitise(E, Rho)) when isLambda(E) orBool   [structural, anywhere]

  // handle (E@R1)@R2 --- have to take advantage of abstract syntax here, or else K complains about E@RhoOrig's not being an Expr but a Val
  // (the more immediate context, closer to the expression, has higher priority, its values are just extended not modified)  --- DOES THIS HOLD?
  rule 'closure(E:Expr@RhoOrig,, Map2KLabel(RhoNew:Map)(.KList)) => E@(RhoNew[RhoOrig]) [structural, anywhere]

  syntax ValNf ::= Neut
                 | Neut ValNf [left]
  //rule isValNf(E:Nf@Rho) => true when isEmptySet(intersectSet(freeVariables(E), keys(Rho) -Set boundKeys(Rho)))

  syntax ValWhnf ::= WhNeut
                   | WhNeut Val [left]
  rule isValWhnf(E:Whnf@Rho) => true when /*isVariable(leftmost(E)) ==K true impliesBool*/ notBool (leftmost(E) in keys(Rho) -Set boundKeys(Rho))
                                          // ^ ten predpoklad by mal checkovat aj isName(leftmost(E))
  //rule isValWhnf(E:WhNeut) => true when /*isVariable(leftmost(E)) ==K true impliesBool*/ notBool (leftmost(E) in keys(Rho) -Set boundKeys(Rho))
                                          // ^ ten predpoklad by mal checkovat aj isName(leftmost(E))


  syntax ValWhnf ::= ValNf
  syntax Val ::= ValWhnf


  syntax Bool ::= needsEval(K, Map)   [function]
  rule needsEval(K, Rho) => leftmost(K) in keys(Rho) -Set boundKeys(Rho)

  syntax KItem ::= eval(K)
  rule <k> eval(E:Expr => E@Rho) ...</k>
       <fenv> Rho </fenv>  //when needsEval(E, Rho)

  /*
  syntax K ::= Expr "@" "-"
  syntax KItem ::= eval(K)  [context(result(Val))]
  rule eval(K => K@-)
  rule <k> eval(K@- => K@Rho) ...</k>
       <fenv> Rho </fenv>
  */

  // alebo mozno len syntax Expr, ak zrusim sort Whnf
  syntax Whnf ::= whnfF(Expr, Map)   [function]
  rule whnfF(E, Rho) => deval(evalWhnf(E@Rho))

  syntax KItem ::= whnf(Expr)
  rule <k> whnf(E) => whnfF(E, Rho) ...</k>
       <fenv> Rho </fenv>

  /*
  syntax KItem ::= whnfType(Expr)  [strict]
  rule <k> whnfType(t(E, T)) => t(E, whnfF(T, Rho)) ...</k>
       <fenv> Rho </fenv>
  */

  /*
  syntax KItem ::= "doneEval!" | "doneEvalWhnf!"
  syntax KItem ::= whnf(K)  [context(result(Whnf))]
  //context whnf(HOLE => eval(HOLE))
  //  when isVal(HOLE) =/=K true andBool isWhnf(HOLE) =/=K true [result(Val)]
  //rule <k> whnf(E:Expr => doneEval! ~> E@Rho) ...</k>
  //     <fenv> Rho </fenv>   when needsEval(E, Rho) orBool isWhnf(E) =/=K true
  rule         <k> (. => eval(E)) ~> whnf(E:Expr => HOLE) ...</k>  <fenv> Rho </fenv>  when needsEval(E, Rho) orBool isWhnf(E) =/=K true
  rule         (eval(V:Val) => .) ~> whnf((. => doneEval!) ~> (HOLE => V))
  rule         (. => evalWhnf(V)) ~> whnf(doneEval! ~> (V:Val => HOLE))   //[heat]
  rule (evalWhnf(V:ValWhnf) => .) ~> whnf((doneEval! => doneEvalWhnf!) ~> (HOLE => V))  //[cool]
  rule            (. => deval(V)) ~> whnf(doneEvalWhnf! ~> (V:ValWhnf => HOLE))   //[heat]
  rule       (deval(E:Whnf) => .) ~> whnf((doneEvalWhnf! => .) ~> (HOLE => E))  //[cool]
  //context whnf(doneEval! ~> HOLE => doneEvalWhnf! ~> evalWhnf(HOLE))  when isVal(HOLE)      [result(ValWhnf)]
  //context whnf(doneEvalWhnf! ~> HOLE => deval(HOLE))     when isValWhnf(HOLE)  [result(Whnf)]
  */
  /*
  syntax KItem ::= whnfType(Expr) [strict, context(result(WhnfTypedExpr))]
  context whnfType(t(_, HOLE::Expr => whnf(HOLE)))  [result(Whnf)]
  */

  // see comment at l. ~40, I shouldn't need Nf
  /*
  syntax KItem ::= nf(K)  [context(result(Nf))]
  context nf(HOLE => eval(HOLE))
    when isVal(HOLE) =/=K true andBool isNf(HOLE) =/=K true [result(Val)]
  context nf(HOLE => evalNf(HOLE))    when isVal(HOLE)      [result(ValNf)]
  context nf(HOLE => deval(HOLE))     when isValNf(HOLE)    [result(Nf)]

  syntax KItem ::= nfType(K) [strict, context(result(NfTypedExpr))]
  context nfType(t(_, (HOLE::Expr => nf(HOLE))))  [result(Nf)]
  */



  syntax Int ::= numArgs(Expr)  [function]
  rule numArgs(E _) => numArgs(E) +Int 1
  rule numArgs(_) => 0   [owise]

  syntax FunClauses ::= FunClauses(Int, List)    // need wrapper around List
                      //| FunClauses "@" Map
  syntax Expr ::= FunClauses
  rule isFunClauses(_:FunClauses@_) => true
  //syntax /*Nf*/Neut ::= FunClauses
  //syntax Neut ::= FunL Variable

  syntax Int ::= numReqArgs(FunClauses)  [function]
  rule numReqArgs(FunClauses(I, _)) => I


  syntax ValWhnf ::= evalWhnf(Val)
  rule evalWhnf(V) => matchClause(leftmost(V), V)
    when isFunClauses(leftmost(V)) andBool numArgs(V) ==Int numReqArgs(leftmost(V))
  rule evalWhnf((V1 => evalWhnf(V1)) V2)
  rule evalWhnf((\(X : _) -> E:Expr)@Rho V => E@(Rho[V/X]))
  rule evalWhnf(V) => V  [owise]

  /*
  syntax KItem ::= evalWhnf(Val)     [context(result(ValWhnf))]  //[strict(all(context('eval))),
  // XXX !!! HOLE:<sort> does NOT enforce dynamic checks that HOLE is of sort <sort>,
  // possibly A BUG IN K (check newer versions before reporting),
  // it might be just an indication how to _parse_ the item [as with ::]
  // GRosu at k-user maillist: ``any variable sorting except to K
  // may yield a runtime sort membership checking'' -- notice the 'may'
  // there -- perhaps it isn't guaranteed as I thought
  // TODO: create a test for this!

  /*
  context evalWhnf((HOLE:Expr => nft ~> isExpr(HOLE) ~> evalWhnf(HOLE)) _)
      when isExpr(HOLE)    [result(ValWhnf)]  // << 'when' clause necessary due to the bug mentioned above
  *
  context evalWhnf((HOLE::Val => evalWhnf(HOLE)) E)
    when isFunClauses(leftmost(HOLE)) =/=K true orElseBool numArgs(HOLE) +Int 1 >Int numReqArgs(leftmost(HOLE))   [result(ValWhnf)]
    // ^ orElseBool necessary instead of impliesBool because numReqArgs is defined only for FunClauses

  rule isFEnvRestore(evalWhnf(_:ValWhnf)) => true
  rule <k> evalWhnf((\ (X : _) -> E:Expr)@Rho V:Val => E@(Rho[V/X])) ~> (. => fenv(Rho')) ...</k>
       <fenv> Rho' </fenv>

  rule <k> evalWhnf(V => matchClause(leftmost(V), V)) ~> (. => fenv(Rho')) ...</k>
       <fenv> Rho' </fenv>  when isFunClauses(leftmost(V))
  */

  // TODO: ked sa zoznam vo FunClauses zredukuje na .List (t.j. nenasli sme match) a zaroven V neobsahuje bound premenne (t.j. V je uplne konkretna) tak daj error
  syntax Val ::= matchClause(Val, Val)  [function]
  rule matchClause(FunClauses(_, ListItem(L = R) _)@Rho, V) => R@(Rho[getMatching(L, V)])  when isMatching(L, V)
  rule matchClause(FunClauses(_, _ Cs:List => Cs)@_, _)  [owise]



  /*
  syntax KItem ::= evalNf(K)     [strict(all(context('evalWhnf))), context(result(ValNf))]
  context evalNf((HOLE::Val => evalNf(HOLE)) _)  [result(ValNf)]
  context evalNf(_::Val (HOLE => evalNf(HOLE)))  [result(ValNf)]
  // TODO !!!!!!
  /*
  context evalNf((_ : (HOLE:Val => evalNf(HOLE))) -> _)  [result(Nf)]
  context evalNf((X : _)-> (HOLE:Expr@Rho => evalNf(HOLE@(Rho[^/X]))))  [result(Nf)]
  context evalNf(\ (_ : (HOLE:Val => evalNf(HOLE))) -> _)  [result(Nf)]
  context evalNf(\ (X : _)-> (HOLE:Expr@Rho => evalNf(HOLE@(Rho[^/X]))))  [result(Nf)]
  */



  /*
  syntax KItem ::= deval(K) [context(result(Expr))]
  context deval((HOLE::Val => deval(HOLE)) _)  [result(Expr)]
  context deval(E::Expr (HOLE => deval(HOLE))) [result(Expr)]
  rule deval(E:Expr@_ => E)  // wr getKLabel(E) ~> isWhnf(E) ~> isExpr(E) ~> E)
  //rule deval(Neut(E) => E)
  */

  syntax Expr ::= deval(Val)  [function]
  rule deval(V1 V2) => deval(V1) deval(V2)
  rule deval(E@_ => E)
  rule deval(E) => E  [owise]
endmodule
