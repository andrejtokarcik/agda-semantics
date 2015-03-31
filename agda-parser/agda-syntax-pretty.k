module AGDA-SYNTAX-PRETTY
  imports AGDA-SYNTAX

  // NOTE: annotating the vars with their explicit sorts is problematic
  // due to the inner metadata wrappers
  // --- which are now gone, so?

  /*
  syntax K ::= killMetaData(K) [function]
  rule killMetaData('m(_,, K) => K)
  rule killMetaData(KLabel:KLabel(KList:KList)) => KLabel(killMetaDataL(KList)) when KLabel =/=KLabel 'm
  syntax KList ::= killMetaDataL(KList)
  rule killMetaDataL(.KList) => .KList
  rule killMetaDataL(K:K,,KList:KList) => killMetaData(K),,killMetaDataL(KList)
  */

  // getting rid of those 'constructors'
  // --- call this 'syntax sort flattening' or something
  syntax ArgInfo ::= Hiding Relevance ColorL | Hiding Relevance
  rule ArgInfo H:Hiding R:Relevance Cs:ColorL => H R Cs   [macro]
  rule H:Hiding R:Relevance .ColorL => H R [macro]

  syntax BoundName ::= AgdaName
  rule BName N _ _ => N [macro]

  // these may cause troubles as AgdaName can be contained not only in an identifier but in a literal as well
  syntax Expr ::= AgdaName
  rule Ident N => N [macro]
  syntax Pattern ::= AgdaName
  rule IdentP N => N [macro]

  syntax ArgInfoName ::= ArgInfo AgdaName
                    | "{" AgdaName "}"
                    | "." AgdaName
                    | AgdaName
  rule (NotHidden Relevant) N => N [macro]
  rule (Hidden Relevant) N => {N}  [macro]

  syntax PrettyBinding ::= "(" PrettyBinding ")" [bracket]
                         | ArgInfoName ":" Expr          [strict(2)]

  syntax ArgTypedBinding ::= PrettyBinding
                           | PrettyBinding ArgTypedBinding [right]
  rule Arg _ (TBind .BoundNameL E) => . [macro]
  rule Arg AInf (TBind (N,L:BoundNameL) E) => (AInf N : E) (Arg AInf (TBind L E))  [macro]

  syntax TypedBindings ::= ArgTypedBinding
  rule TypedBindings Bnds => Bnds [macro]

  // not using PrettyBinding in order to specify the binder attribute
  syntax Expr ::= "(" ArgInfoName ":" Expr ")" "->" Expr   [strict(2(context('whnf))), binder(1 -> 3)]
  rule Pi .Telescope E => E   [macro]
  rule Pi (., Tel:Telescope => Tel) _ [macro]
  rule Pi (((N : T) Bnds),Tel:Telescope) E => (N : T) -> Pi (Bnds,Tel) E  [macro]
  rule Fun E1 E2 => (N : E1) -> E2 when fresh(N:ArgInfoName) [macro]

  syntax LamBinding ::= PrettyBinding | TypedBindings
  rule DomainFree AInf BndN => AInf BndN : T when fresh(T:Expr)  [macro]
  rule DomainFull TypBnds => TypBnds  [macro]

  syntax Expr ::= "\\" "(" ArgInfoName ":" Expr ")" "->" Expr   [strict(2(context('whnf))), binder(1 -> 3)]
  rule Lam .LamBindingL E => E   [macro]
  rule Lam ((N : T), LamBnds) E => \ (N : T) -> Lam LamBnds E [macro]

  syntax Expr ::= ArgExpr
  syntax Expr ::= Expr Expr [left]
  rule App E1 E2 => E1 E2   [macro]

  syntax Declaration ::= PrettyBinding
  rule TypeSig AInf N T => AInf N : T  [macro]
  // re TypeSig's AInf: ``Axioms and functions can be irrelevant. (Hiding should be NotHidden)''
  // --- we admit only NotHidden Relevant ATM

  syntax LHS ::= Pattern
  rule LHS P .PatternL .RewriteEqnL .WithExprL => P [macro]

  syntax RHS ::= Expr
  rule RHS E => E [macro]

  syntax Declaration ::= LHS "=" RHS "where" WhereClause
                       | LHS "=" RHS
  rule FunClause L R W => L = R where W [macro]
  rule L = R where NoWhere => L = R [macro]
endmodule
