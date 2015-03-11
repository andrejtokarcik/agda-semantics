module AGDA-SYNTAX
  syntax Variable ::= Token{[a-z][a-zA-Z0-9\_]*}  [onlyLabel]
  syntax Name ::= Token{[A-Z][a-zA-Z0-9\_]*}      [onlyLabel]

  syntax Universe ::= "Set" Int
  syntax Expr ::= "(" Expr ")" [bracket]
                | Variable | Name | "?"
                | Universe | "Set"
                > Expr Expr                       [left, strict(1(context('whnf2)), 2)]
                > "Pi" Variable Expr Expr         [binder, strict(2(context('whnf21),result(TypeT)))]
                | "Lambda" Variable Expr Expr     [binder, strict(2(context('whnf21),result(TypeT)))]
  rule Set => Set 0 [macro]

  syntax DataDecl ::= "(" DataDecl ")" [bracket]
                    | "data" Name Params ":" Expr "where" Constrs [strict(3)]

  syntax Param ::= "(" Param ")" [bracket]
                 | Variable ":" Expr
  // TODO: this should be just standard application, not a list (Expr to contain telescopes)
  //       --- then remove applyParams() function
  syntax Params ::= List{Param,","}

  syntax Constr ::= "(" Constr ")" [bracket]
                  | Name ":" Expr
  // TODO: make Constrs newline-separated to match Agda's syntax
  syntax Constrs ::= List{Constr,","}

  syntax FunDecl ::= Variable "=" Expr  [strict(2(context('whnf21))), prefer]

  /*
  syntax Program ::= FunDecl
                   | DataDecl
                   | Program Program  [assoc, id('.Program)]   // << doesn't work
                   //| DataDecl Program [klabel(p)]
  */

  syntax Decl ::= DataDecl | FunDecl
  // klabel below is necessary to avoid "Cannot use '__ as a right
  // child of '__" errors (which are apparently due to [left] attribute
  // assigned to Expr application)
  syntax Program ::= List{Decl,""}  [klabel(p)]
endmodule
