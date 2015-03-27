module AGDA-SYNTAX-PRETTY
  imports AGDA-SYNTAX

  syntax Declaration ::= ArgInfo Name ":" Expr
  rule TypeSig AInf:ArgInfo N:Name E:Expr => AInf N : E       [macro]

  syntax Declaration ::= Name ":" Expr
  rule (NotHidden Relevant .ColorL) N:Name : E:Expr => N : E  [macro]
endmodule
