module AGDA-SYNTAX
  // perhaps I don't have to include ranges at all? is it good for anything
  // besides error reporting?

  syntax Program ::= Declarations

  syntax Declaration ::= "(" Declaration ")" [bracket]
    | TypeSignature
    | LHS "=" RHS                                    [klabel('FunClause)]
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
    | "Set"  [klabel('Set), notInRules]
    | "Set" Int  [klabel('Set_)]
  rule 'Set(.KList) => Set 0 [macro]

  syntax Identifier ::= Token{[a-zA-Z0-9\_]+}  [notInRules, notInGround]
  syntax Variable ::= Identifier               [klabel('Var)]
  syntax Name ::= Identifier                   [klabel('Name)]
  // See c-semantics/cil-semantics/cil-syntax.k for Char syntax, including EscapeString.
  syntax Literal ::= Int | Float | "\""String"\"" | "'"Char"'" //| QName

  syntax TypeSignature ::= Name ":" Expr  [klabel('TypeSig)]
  //syntax TypeSignatures ::= List{TypeSignature, ";"}

  syntax Lambda ::= "\\" Binding "->" Expr   [klabel('Lam)]
                  //| "\\" "(" Variable ":" Expr ")" "->" Expr [notInPrograms, binder(1 -> 3)]
  // TODO: macro
  syntax Pi ::= Binding "->" Expr   [klabel('Pi)]
              //| "(" Variable ":" Expr ")" "->" Expr [notInPrograms, binder(1 -> 3)]
  // TODO: macro

  syntax Binding ::= Variable
                   | TypedBinding
  syntax TypedBinding ::= "(" Variable ":" Expr ")"  [klabel('TBind)]
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
  syntax Range ::= "@noRange"
    | "@someRange"
    | Token{([a-zA-Z0-9\/\-]+ "." "l"? "agda" ":")? [0-9]+ "," [0-9]+ "-" ([0-9]+ ",")? [0-9]+}  [notInRules]
  */
  syntax Range ::= String
  syntax Declaration ::= "[" Range "]" Declaration
endmodule
