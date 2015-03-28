module AGDA-SYNTAX-PRETTY
  imports AGDA-SYNTAX

  // NOTE: annotating the vars with their explicit sorts is problematic

  /*
  syntax K ::= killMetaData(K) [function]
  rule killMetaData('m(_,, K) => K)
  rule killMetaData(KLabel:KLabel(KList:KList)) => KLabel(killMetaDataL(KList)) when KLabel =/=KLabel 'm
  syntax KList ::= killMetaDataL(KList)
  rule killMetaDataL(.KList) => .KList
  rule killMetaDataL(K:K,,KList:KList) => killMetaData(K),,killMetaDataL(KList)
  */

  syntax ArgInfo ::= Hiding Relevance ColorL | Hiding Relevance
  rule ArgInfo H:Hiding R:Relevance Cs:ColorL => H R Cs   [macro]
  rule H:Hiding R:Relevance .ColorL => H R [macro]

  syntax BoundName ::= AgdaName
  rule BName N _ _ => N [macro]

  // these may cause troubles as AgdaName can be a literal as well
  syntax Expr ::= AgdaName
  rule Ident N => N [macro]
  syntax Pattern ::= AgdaName
  rule IdentP N => N [macro]

  syntax PrettyBinding ::= "(" PrettyBinding ")" [bracket]
                         | ArgInfo AgdaName ":" Expr
                         | AgdaName ":" Expr
  rule NotHidden Relevant N : E => N : E  [macro]

  syntax ArgTypedBinding ::= PrettyBinding
                           | ArgTypedBinding PrettyBinding  [left]
  rule Arg _ (TBind .BoundNameL E) => . [macro]
  rule Arg AInf (TBind (N,L:BoundNameL) E) => (Arg AInf (TBind L E)) (AInf N : E)  [macro]

  syntax TypedBindings ::= ArgTypedBinding
  rule TypedBindings Bnds => Bnds [macro]

  syntax Expr ::= PrettyBinding "->" Expr
  rule Pi .Telescope E => E   [macro]
  rule Pi (.K,Tel:Telescope => Tel) _ [macro]
  rule Pi (Bnds (N : T),Tel:Telescope) E => Pi (Bnds,Tel) ((N : T) -> E)  [macro]
  rule Fun E1 E2 => (N : E1) -> E2 when fresh(N:AgdaName) [macro]

  syntax Declaration ::= PrettyBinding
  rule TypeSig AInf N T => AInf N : T  [macro]

  syntax LHS ::= Pattern
  rule LHS P .PatternL .RewriteEqnL .WithExprL => P [macro]

  syntax Declaration ::= LHS "=" RHS "where" WhereClause
                       | LHS "=" RHS
  rule FunClause L R W => L = R where W [macro]
  rule L = R where NoWhere => L = R [macro]
endmodule
