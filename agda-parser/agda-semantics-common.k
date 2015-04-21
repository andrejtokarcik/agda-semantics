require "modules/pattern-matching.k"
require "modules/unification.k"
require "agda-syntax.k"//-pretty.k"

module AGDA-SEMANTICS-COMMON
  imports PATTERN-MATCHING
  imports UNIFICATION
  imports AGDA-SYNTAX//-PRETTY

  syntax KResult ::= TypedExpr

  syntax TEnvRestore
  rule isTEnvRestore(_:TypedExpr) => true
  syntax KItem ::= tenv(Map)
  rule <k> tenv(Gamma) => . ...</k>
       <tenv> _ => Gamma </tenv>
  rule R:TEnvRestore ~> tenv(Gamma) => tenv(Gamma) ~> R

  syntax KItem ::= "chich"
  syntax FEnvRestore
  rule isFEnvRestore(_:TypedExpr) => true
  syntax KItem ::= fenv(Map)
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

  syntax TypedExpr ::= t(Expr, Val)    [latex(({#1}\downarrow{#2}))]    // XXX this would indicate a type-*inference* result
  syntax Expr ::= TypedExpr

  // XXX: should these be in a separate file -normal.k as before...?

  syntax Whnf ::= "(" Whnf ")" [bracket]
                | WhNeut
  syntax WhNeut
  rule isWhNeut(_:Variable) => true
  rule isWhNeut(_:Name) => true
  rule isWhNeut(_:WhNeut _:Expr) => true
  rule isWhnf(Set(_)) => true
  rule isWhnf({_:Whnf}) => true
  rule isWhnf((_ : _) -> _) => true
  rule isWhnf({_ : _} -> _) => true     // AT FIXME hack - generalise
  rule isWhnf(\ (_ : _) -> _) => true
  rule isWhnf(\ {_ : _} -> _) => true
  
  syntax Expr ::= Whnf

  syntax WhnfTypedExpr
  rule isWhnfTypedExpr(t(_, _:ValWhnf)) => true
  syntax TypedExpr ::= WhnfTypedExpr

  syntax SetTypedExpr
  rule isSetTypedExpr(t(_, Set(_))) => true
  syntax WhnfTypedExpr ::= SetTypedExpr

  syntax Val ::= updateClosure(Val, Map)  [function]
  rule updateClosure(V1 V2, Rho) => updateClosure(V1, Rho) updateClosure(V2, Rho)
  rule updateClosure(E@Rho', Rho) => E@(Rho'[Rho])
  rule updateClosure(E, Rho) => E@Rho  [owise]

  syntax Map ::= updateClosures(Map, Map)  [function]
  rule updateClosures(_, .Map) => .Map
  rule updateClosures(Rho, (K |-> V => .) _) (.Map => K |-> updateClosure(V, Rho))
  rule updateClosures(Rho, (K |-> t(E, T) => .) _) (.Map => K |-> t(E, updateClosure(T, Rho)))
  rule updateClosures(_, (K |-> V => .) _) (.Map => K |-> V)  [owise]

  // TODO: move the unification machinery to a separate file
  // NOTE: not every updateMgu is actually guaranteed to update the mgu;
  // e.g. if T is identical to T', <mgu /> content remains the same.

  syntax KItem ::= Expr "==" Expr
  rule <k> E == E' => . ...</k>
       <mgu> Theta => updateMgu(Theta, E, E') </mgu>

  syntax KItem ::= "unify"
  rule <k> unify => . ...</k>
       <sig> Sigma => applyMgu(Theta, Sigma) </sig>
       <tenv> Gamma => updateClosures(applyMgu(Theta, Rho), applyMgu(Theta, Gamma)) </tenv>
       <fenv> Rho => updateClosures(applyMgu(Theta, Rho), applyMgu(Theta, Rho)) </fenv>
       <metavars> Meta => updateClosures(applyMgu(Theta, Rho), applyMgu(Theta, Meta)) </metavars>
       <mgu> Theta => .Mgu </mgu>
    when isMguError(Theta) =/=K true

  syntax KItem ::= unify(Expr)
  rule <k> unify(E:Expr) => unify ~> applyMgu(Theta, E) ...</k>
       <mgu> Theta </mgu>

  syntax KItem ::= unifyType(TypedExpr)
  rule <k> unifyType(t(E, T)) => unify ~> t(E, applyMgu(Theta, T)) ...</k>
       <mgu> Theta </mgu>

  syntax KItem ::= checkSetType(Expr)  [strict(all(context('whnfType))), context(result(SetTypedExpr))]
  rule checkSetType(t(E, T)) => deval(T) == Set(I) ~> unifyType(t(E, T)) ~> checkSetType(HOLE)
    when isUniverse(T) =/=K true andBool fresh(I:Int)
  rule Te:SetTypedExpr ~> checkSetType(HOLE) => checkSetType(Te)



  syntax Val ::= "(" Val ")" [bracket]
               | Expr "@" Map
               | Val Val  [left]

  // bound -- vraj aj historicky symbol na oznacenie prave bound premennych
  syntax Val ::= "^"      [latex(^\wedge)]

  syntax Set ::= boundKeys(Map)  [function]
  rule boundKeys(.Map) => .Set   [structural]
  rule boundKeys((E |-> ^ => .) _) (. => SetItem(E)) [structural]
  rule boundKeys((_ |-> _ => .) _) [owise, structural]

  syntax KList ::= unnecessaryKeys(Expr, Map)   [function]
  rule unnecessaryKeys(_, .Map) => .KList    [structural]
  rule unnecessaryKeys(_, (N:Name |-> _ => .) _),,(.KList => N) [structural]
  rule unnecessaryKeys(E, (X:Variable |-> _ => .) _),,(.KList => X) when notBool X in freeVariables(E)  [structural]
  rule unnecessaryKeys(_, (_ |-> _ => .) _)  [owise, structural]

  // The following rules are where most of the evaluation magic happens...

  //rule X:Variable@Rho => #if X in keys(Rho) andBool Rho(X) =/=K ^ #then Rho(X)@Rho #else X #fi  [structural, anywhere]
  // FIXME
  rule X:Variable@(_ X |-> V) => V /*updateClosure(V, X |-> V)*/  when deval(V) =/=K ^ /*X in keys(Rho) andBool Rho(X) =/=K ^*/  [structural, anywhere]
  //rule N:Name@Rho => #if N in keys(Rho) #then Rho(N)@Rho #else N #fi [structural, anywhere]
  rule N:Name@(_ N |-> V) => V /*updateClosure(V, N |-> V)*/  /*when N in keys(Rho)*/   [structural, anywhere]

  rule Set(I)@_ => Set(I) [structural, anywhere]
  //rule N:WhNeut@_ => N  when isVariable(N) =/=K true andBool isName(N) =/=K true [structural, anywhere]

  // this would require Expr ::= Val
  //rule ((_ : (E => E@Rho)) -> _)@Rho  when isVal(E) =/=K true  [structural, anywhere]

  rule (E1:Expr E2:Expr)@Rho => E1@Rho E2@Rho [structural, anywhere]

  // NOTE: enormous amounts of data when not using unnecessaryKeys
  rule E@(Rho => Rho[undef/unnecessaryKeys(E, Rho)]) when unnecessaryKeys(E, Rho) =/=KList .KList  [structural, anywhere]
  //rule E@.Map => E  [structural, anywhere]

  syntax ValWhnf ::= Universe   // so that it can be parsed in rules
  rule isValWhnf(V) => true when isWhnf(deval(V))
  syntax Val ::= ValWhnf

  syntax KItem ::= whnf(Val)  [context(result(ValWhnf))]
  context whnf(HOLE => evalWhnf(HOLE))  [result(ValWhnf)]

  syntax KItem ::= whnfType(K) [strict, context(result(WhnfTypedExpr))]
  context whnfType(t(_, HOLE => whnf(HOLE)))  [result(ValWhnf)]

  syntax Int ::= numArgs(Expr)  [function]
  rule numArgs(E _) => numArgs(E) +Int 1
  rule numArgs(_) => 0   [owise]

  syntax FunClauses ::= FunClauses(Int, List)    // need wrapper around List
  syntax Expr ::= FunClauses
  rule isFunClauses(_:FunClauses@_) => true

  syntax Int ::= numReqArgs(FunClauses)  [function]
  rule numReqArgs(FunClauses(I, _)) => I

  syntax KItem ::= evalWhnf(Val)      [context(result(ValWhnf))]
  context evalWhnf((HOLE::Val => evalWhnf(HOLE)) E)
    when isFunClauses(leftmost(HOLE)) =/=K true orElseBool numArgs(HOLE) +Int 1 >Int numReqArgs(leftmost(HOLE))   [result(ValWhnf)]

  rule isFEnvRestore(evalWhnf(_:ValWhnf)) => true
  rule <k> evalWhnf((\ (X : _) -> E:Expr)@Rho' V:Val => E@(Rho'[Rho[V/X]])) ~> (. => fenv(Rho)) ...</k>
       <fenv> Rho </fenv>
    when isImplicit(deval(V)) =/=K true

  rule <k> evalWhnf((\ {X : _} -> E1:Expr)@Rho1 {E2}@Rho2 => E1@(Rho1[Rho[E2@Rho2/X]])) ~> (. => fenv(Rho)) ...</k>
       <fenv> Rho => Rho[E2@Rho2/X] </fenv>

  /*
  rule <k> evalWhnf((\ {X : T} -> E)@Rho' V => ((\ {X : T} -> E)@Rho' {%underscore}@Rho) V) ...</k>
       <fenv> Rho </fenv>
    when isImplicit(deval(V)) =/=K true
  */

  rule <k> evalWhnf(V => matchClause(leftmost(V), deval(V), gatherClosures(V))) ~> (. => fenv(Rho)) ...</k>
       <fenv> Rho </fenv>  when isFunClauses(leftmost(V))

  syntax Map ::= gatherClosures(Val)  [function]
  rule gatherClosures(V1 V2) => gatherClosures(V1) gatherClosures(V2)
  rule gatherClosures(E@Rho) => Rho
  rule gatherClosures(E) => .Map  [owise]

  // TODO: ked sa zoznam vo FunClauses zredukuje na .List (t.j. nenasli sme match) a zaroven uz nie vo V co skonkretizovat tak daj error
  syntax Val ::= matchClause(Val, Expr, Map)  [function]
  //rule matchClause(FunClauses(_, .List)@_, _, _) => Name("(T)ERROR")
  rule matchClause(FunClauses(_, ListItem(L = R) _)@Rho, E, Rho') => R@(Rho[Rho'[getMatching(L, E)]])  when isMatching(L, E)
  rule matchClause(FunClauses(_, _ Cs:List => Cs)@_, _, _)  [owise]



  syntax Expr ::= deval(Val)  [function]
  rule deval(V1 V2) => deval(V1) deval(V2)
  rule deval(E@_) => E
  rule deval(E) => E  [owise]
endmodule
