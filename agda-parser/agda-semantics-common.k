require "modules/pattern-matching.k"
require "agda-syntax.k"
require "agda-semantics-unification.k"
require "agda-semantics-normal.k"

module AGDA-SEMANTICS-COMMON
  imports PATTERN-MATCHING
  imports AGDA-SYNTAX
  imports AGDA-SEMANTICS-UNIFICATION
  imports AGDA-SEMANTICS-NORMAL

  syntax KItem ::= "chich"

  syntax TypedExpr ::= t(Expr, Val)    [latex(({#1}\downarrow{#2}))]    // XXX this would indicate a type-*inference* result
  syntax Expr ::= TypedExpr

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

  /** The following rules are where most of the evaluation magic happens... */

  //rule X:Variable@Rho => #if X in keys(Rho) andBool Rho(X) =/=K ^ #then Rho(X)@Rho #else X #fi  [structural, anywhere]
  // FIXME!!
  rule X:Variable@(_ X |-> V) => V /*updateClosure(V, X |-> V)*/  when deval(V) =/=K ^ /*X in keys(Rho) andBool Rho(X) =/=K ^*/  [structural, anywhere]
  //rule N:Name@Rho => #if N in keys(Rho) #then Rho(N)@Rho #else N #fi [structural, anywhere]
  rule N:Name@(_ N |-> V) => V /*updateClosure(V, N |-> V)*/  /*when N in keys(Rho)*/   [structural, anywhere]

  rule Set(I)@_ => Set(I) [structural, anywhere]
  //rule N:WhNeut@_ => N  when isVariable(N) =/=K true andBool isName(N) =/=K true [structural, anywhere]

  // this would require Expr ::= Val
  //rule ((_ : (E => E@Rho)) -> _)@Rho  when isVal(E) =/=K true  [structural, anywhere]

  rule (E1:Expr E2:Expr)@Rho => E1@Rho E2@Rho [structural, anywhere]

  // NOTE: enormous amounts of data when not using unnecessaryKeys
  rule E@(Rho => Rho[undef/unnecessaryKeys(E, Rho)])
    when isSymbolicExpr(E) =/=K true andBool unnecessaryKeys(E, Rho) =/=KList .KList  [structural, anywhere]
  //rule E@.Map => E  [structural, anywhere]


  syntax TEnvRestore
  rule isTEnvRestore(_:TypedExpr) => true
  syntax KItem ::= tenv(Map)
  rule <k> tenv(Gamma) => . ...</k>
       <tenv> _ => Gamma </tenv>
  rule R:TEnvRestore ~> tenv(Gamma) => tenv(Gamma) ~> R

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

  syntax KItem ::= checkSetType(Expr)  [strict(all(context('whnfType))), context(result(SetTypedExpr))]
  rule checkSetType(t(E, T)) => deval(T) == Set(I) ~> unifyType(E, T, .Map) ~> checkSetType(HOLE)
    when isUniverse(T) =/=K true andBool fresh(I:Int)
  rule Te:SetTypedExpr ~> checkSetType(HOLE) => checkSetType(Te)
endmodule
