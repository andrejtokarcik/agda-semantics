module AGDA-SYNTAX
  // perhaps I don't have to include ranges at all? is it good for anything
  // besides error reporting?

  syntax Program ::= Declarations

  syntax FunClause ::= LHS "=" RHS                                    [klabel('FunClause)]
  syntax Declaration ::= "(" Declaration ")" [bracket]
    | TypeSignature
    | FunClause
    | "postulate" Declaration                        [klabel('Postulate)]
    | "module" Name Telescope "where" Declarations   [klabel('Module)]
  syntax Declarations ::= //"(" Declarations ")" [bracket]
                       List{Declaration, ""}

  syntax Expr ::= "(" Expr ")" [bracket]
    | Variable
    | Name
    | Lambda
    | Pi
    | Expr Expr    [left]
    //| "Set"        [notInRules, klabel('Set)]
    | "Set" Int    [klabel('Set_)]
  //rule 'Set(.KList) => Set 0 [macro]
  //syntax Expr ::= UntypedExpr

  syntax Identifier ::= Token{[a-zA-Z0-9\_]+}        [notInRules]
  syntax Variable ::= var(Identifier)                [klabel('Var)]
  syntax Name ::= name(Identifier)                   [klabel('Name)]
  // See c-semantics/cil-semantics/cil-syntax.k for Char syntax, including EscapeString.
  syntax Literal ::= Int | Float | "\""String"\"" | "'"Char"'" //| QName

  syntax TypeSignature ::= Name ":" Expr  [klabel('TypeSig)]

  syntax Lambda ::= //K "->" Expr   [klabel('Lam)]
                  "\\" "(" Variable ":" Expr ")" "->" Expr [binder(1 -> 3), notInPrograms, klabel('Lam)]
  syntax Pi ::= //K "->" Expr   [notInRules, klabel('Pi)]
              //| K "->" Exp    [notInRules, klabel('Fun)]
              "(" Variable ":" Expr ")" "->" Expr [binder(1 -> 3), notInPrograms, klabel('Pi)]

  syntax TypedBinding ::= //"(" K ":" Expr ")"  [notInRules, klabel('TBind)]
                        "(" Variable ":" Expr ")"  [notInPrograms]
  syntax Telescope ::= List{TypedBinding, ""}

  syntax Pattern ::= "(" Pattern ")" [bracket]
    | Variable
    | Name
    | Name Pattern  [klabel('AppP), left]
  syntax LHS ::= Name
               | LHS Pattern  [left]
  syntax RHS ::= Expr



  // metadata
  /*
  syntax Range ::= "$noRange"
    | "$someRange"
    | Token{([a-zA-Z0-9\/\-]+ "." "l"? "agda" ":")? [0-9]+ "," [0-9]+ "-" ([0-9]+ ",")? [0-9]+}  [notInRules]
  */
  syntax Range ::= String
  syntax Declaration ::= "[" Range "]" Declaration
endmodule
