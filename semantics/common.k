module AGDA-SEMANTICS-COMMON
  imports LIBRARY
  imports AGDA-SYNTAX
  imports AGDA-SEMANTICS-NORMAL
  imports AGDA-SEMANTICS-UNIFICATION

  syntax TypedExpr ::= t(Expr, Expr)    [latex(\ktyped{#1}{#2})]
  syntax Expr ::= TypedExpr

  syntax Name ::= Data(Identifier) | Con(Identifier) | Fun(Identifier) | Postlt(Identifier)


  syntax KItem ::= saveCtx(Map) | "loadCtx"
  rule <k> saveCtx(Gamma) => . ...</k>
       <ctx-stack> L => ListItem(#map(Gamma)) L </ctx-stack>
  rule <k> loadCtx => . ...</k>
       <ctx> _ => Gamma </ctx>
       <ctx-stack> ListItem(#map(Gamma)) L => L </ctx-stack>
  rule (. => loadCtx) ~> R:KResult ~> (loadCtx => .)  [structural]


  syntax KItem ::= "cleanMetas"
  rule <k> cleanMetas => . ...</k>
       <meta> _ => .Map </meta>


  syntax KItem ::= checkType(Expr, Expr)  [strict(1)]
  rule checkType(t(_, T1), T2) => renameBoundVariables(T1) == renameBoundVariables(T2) /*unifyConf ~>* killMgu*/
    when isPi(T1) =/=K true
  rule checkType(t(_, T1), T2) => T1 ~> renameBoundVariables(T1) ~> T2 ~> renameBoundVariables(T2) ~> renameBoundVariables(T1) == renameBoundVariables(T2) /*unifyConf ~>* killMgu*/
    when isPi(T1) ==K true


  syntax KItem ::= checkSetType(Expr)  [strict, context(result(SetTypedExpr))]
  rule checkSetType(t(E, T)) => T == Set(Alpha) ~> unify(t(E, T)) ~> unifyConf ~> killMgu ~> checkSetType(HOLE)
    when isSetTypedExpr(t(E, T)) =/=K true andBool fresh(Alpha:Int)
  rule Te:SetTypedExpr ~> checkSetType(HOLE) => checkSetType(Te)


  /* General auxiliary functions. */

  syntax Expr ::= unhide(Expr)  [function]
  rule unhide({E}) => E
  rule unhide(E) => E   [owise]

  syntax K ::= leftmost(Expr)  [function]
  rule leftmost({E} => E)
  rule leftmost(E _ => E)
  rule leftmost(E) => E   [owise]

  syntax Expr ::= replaceLeftmost(Expr, Expr)  [function]
  rule replaceLeftmost(E E', R) => replaceLeftmost(E, R) E'
  rule replaceLeftmost(_, R) => R    [owise]

  syntax List ::= args(Expr)  [function]
  rule args({E} => E)
  rule args(E E' => E) (.List => ListItem(E'))
  rule args(_) => .List [owise]

  syntax Int ::= numPiArgs(Pi)   [function]
               | #numPiArgs(Pi, Int)  [function]
  rule numPiArgs(E) => #numPiArgs(E, 0)
  rule #numPiArgs((_ : _) -> E => E, I => I +Int 1)
  rule #numPiArgs({_ : _} -> E => E, I => I +Int 1)
  rule #numPiArgs(_, I) => I   [owise]
endmodule
