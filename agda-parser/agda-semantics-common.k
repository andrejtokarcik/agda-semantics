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
  syntax Bool ::= needEval(K, Map)  [fenvction]
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
  rule isFEnvRestore(_:NfTypedExpr) => true
  syntax KItem ::= fenv(Map)
  // XXX: must use 'isTypedExpr(HOLE)' instead of 'HOLE:TypedExpr'
  // due to the possible K BUG described below  (the latter doesn't
  // generate the dynamic sort check as intended).
  context (HOLE => nfType(HOLE)) ~> fenv(_) when isTypedExpr(HOLE)  [result(NfTypedExpr)]
  // why do I need to use nfType here actually, isn't whnf enough...?
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
  syntax Neut /*::= Variable       // considered neutral only if cannot be evaluated
                | Name
                | Neut Nf [left]
                */
  rule isNeut(_:Variable) => true
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

  syntax KItem ::= unify(K)
  rule <k> unify(K:K) => unify ~> applyMgu(Theta, K) ...</k>
       <mgu> Theta </mgu>

  syntax KItem ::= unifyType(TypedExpr)     //[context(result(Unified))]
  rule <k> unifyType(t(E, T)) => unify ~> t(E, applyMgu(Theta, T)) ...</k>
       <mgu> Theta </mgu>

  /*
  context unifyType(t(_, HOLE => unify(HOLE)))   [result(Unified)]
  rule unifyType(t(E, unified(T)) => unified(t(E, T)))
  */

  syntax KItem ::= checkSetType(Expr)  [strict(all(context('whnfType))), context(result(SetTypedExpr))]
  rule checkSetType(t(E, T)) => T == Set(I) ~> unifyType(t(E, T)) ~> checkSetType(HOLE)  //[heat]
    when isSetTypedExpr(t(E, T)) =/=K true andBool fresh(I:Int)
  rule Te:SetTypedExpr ~> checkSetType(HOLE) => checkSetType(Te)
  /*
  rule checkSetType(t(E, T:Expr)) => T == Set I ~> unifyType(t(E, T)) ~> checkSetType(HOLE)
    when isSetTypedExpr(t(E, T)) =/=K true andBool fresh(I:Int)
  rule Set I ~> checkSetType(t(E, HOLE)) => checkSetType(t(E, Set I))
  */




  syntax Val ::= "(" Val ")" [bracket]
               | Expr "@" Map   [klabel('closure)]
               | Val Val  [left]

  syntax Val ::= "^"      [latex(^\wedge)]  // bound -- vraj aj historicky symbol na oznacenie prave bound premennych

  syntax Set ::= boundKeys(Map)  [function]
  rule boundKeys(.Map) => .Set   [structural]
  rule boundKeys((E |-> ^ => .) _) (. => SetItem(E)) [structural]
  rule boundKeys((_ |-> _ => .) _) [owise, structural]

  // The following rules are where most of the evaluation magic happens...
  rule X:Variable@Rho => #if X in keys(Rho) andBool Rho(X) =/=K ^ #then Rho(X)@Rho #else X #fi  [structural, anywhere]
  rule N:Name@Rho => #if N in keys(Rho) #then Rho(N)@Rho #else N #fi [structural, anywhere]
  rule (Set(I))@_ => Set(I) [structural, anywhere]
  //rule N:WhNeut@_ => N  when isVariable(N) =/=K true andBool isName(N) =/=K true [structural, anywhere]
  rule (E1:Expr E2:Expr)@Rho => E1@Rho E2@Rho [structural, anywhere]
  // handle (E@R1)@R2 --- have to take advantage of abstract syntax here, or else K complains about E@RhoOrig's not being an Expr but a Val
  // (the more immediate context, closer to the expression, has higher priority, its values are just extended not modified)
  rule 'closure(E:Expr@RhoOrig,, Map2KLabel(RhoNew:Map)(.KList)) => E@(RhoNew[RhoOrig]) [structural, anywhere]

  syntax ValNf ::= Neut
                 | Neut ValNf [left]
  rule isValNf(E:Nf@Rho) => true when isEmptySet(intersectSet(freeVariables(E), keys(Rho) -Set boundKeys(Rho)))

  syntax ValWhnf ::= WhNeut
                   | WhNeut Val [left]
  rule isValWhnf(E:Whnf@Rho) => true when isVariable(leftmost(E)) ==K true impliesBool notBool (leftmost(E) in keys(Rho) -Set boundKeys(Rho))


  syntax ValWhnf ::= ValNf
  syntax Val ::= ValWhnf


  syntax K ::= Expr "@" "-"
  syntax KItem ::= eval(K)  [context(result(Val))]
  rule eval(E:Expr => E@-)
  rule <k> eval(E:Expr@- => E@Rho) ...</k>
       <fenv> Rho </fenv>

  syntax KItem ::= "wr" KLabel
  syntax KItem ::= whnf(K)  [context(result(Whnf))]
  context whnf(HOLE => eval(HOLE))
    when isVal(HOLE) =/=K true andBool isWhnf(HOLE) =/=K true [result(Val)]
  context whnf(HOLE => evalWhnf(HOLE))  when isVal(HOLE)      [result(ValWhnf)]
  context whnf(HOLE => deval(HOLE))     when isValWhnf(HOLE)  [result(Whnf)]

  syntax KItem ::= whnfType(K) [strict, context(result(WhnfTypedExpr))]
  context whnfType(t(_, HOLE::Expr => whnf(HOLE)))  [result(Whnf)]

  syntax KItem ::= nf(K)  [context(result(Nf))]
  context nf(HOLE => eval(HOLE))
    when isVal(HOLE) =/=K true andBool isNf(HOLE) =/=K true [result(Val)]
  context nf(HOLE => evalNf(HOLE))    when isVal(HOLE)      [result(ValNf)]
  context nf(HOLE => deval(HOLE))     when isValNf(HOLE)    [result(Nf)]

  syntax KItem ::= nfType(K) [strict, context(result(NfTypedExpr))]
  context nfType(t(_, (HOLE::Expr => nf(HOLE))))  [result(Nf)]




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

  syntax KItem ::= evalWhnf(K)     [strict(all(context('eval))), context(result(ValWhnf))]
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
  */
  context evalWhnf((HOLE::Val => evalWhnf(HOLE)) E)
    when isFunClauses(leftmost(HOLE)) =/=K true orElseBool numArgs(HOLE) +Int 1 >Int numReqArgs(leftmost(HOLE))   [result(ValWhnf)]
    // ^ orElseBool necessary instead of impliesBool because numReqArgs is defined only for FunClauses

  rule isFEnvRestore(evalWhnf(_:ValWhnf)) => true
  rule <k> evalWhnf((\ (X : _) -> E:Expr)@Rho V:Val => E@(Rho[V/X])) ~> (. => fenv(Rho')) ...</k>
       <fenv> Rho' </fenv>

  rule <k> evalWhnf(V => matchClause(leftmost(V), V)) ~> (. => fenv(Rho')) ...</k>
       <fenv> Rho' </fenv>  when isFunClauses(leftmost(V))

  // TODO: ked sa zoznam vo FunClauses zredukuje na .List (t.j. nenasli sme match) a zaroven V neobsahuje bound premenne (t.j. V je uplne konkretna) tak daj error
  syntax Val ::= matchClause(Val, Val)  [function]
  rule matchClause(FunClauses(_, ListItem(L = R) _)@Rho, V) => R@(Rho[getMatching(L, V)])  when isMatching(L, V)
  rule matchClause(FunClauses(_, _ Cs:List => Cs)@_, _)  [owise]



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



  syntax KItem ::= deval(K) [context(result(Expr))]
  context deval((HOLE::Val => deval(HOLE)) _)  [result(Expr)]
  context deval(E::Expr (HOLE => deval(HOLE))) [result(Expr)]
  rule deval(E:Expr@_ => E)  // wr getKLabel(E) ~> isWhnf(E) ~> isExpr(E) ~> E)

endmodule
