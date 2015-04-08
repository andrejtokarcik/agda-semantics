module AGDA-SYNTAX
  // perhaps I don't have to include ranges at all? is it good for anything
  // besides error reporting?

  syntax Program ::= Declarations

  syntax Declaration ::= "(" Declaration ")" [bracket]
    | TypeSignature
    | LHS "=" RHS    //WhereClause
    //| "DataSig" Induction Name LamBindingL Expr
    //| "Data" Induction Name LamBindingL ExprM TypeSignatureOrInstanceBlockL
    | "syntax" Name "..."
    | "postulate" Declarations
    | "module" Name Telescope "where" Declarations
  syntax Declarations ::= //"(" Declarations ")" [bracket]
                       List{Declaration, ";"}

  syntax Expr ::= "(" Expr ")" [bracket]
    | Variable
    | Name
    | Lambda
    | Pi
    | Expr Expr    [left]
    | "Set"  [notInRules]
    | "Set"Int
  rule 'Set(.KList) => Set0 [macro]

  syntax Variable ::= //"(" Variable ")" [bracket]
                    "(" "Var" String ")"
  syntax Variables ::= List{Variable, ""}
  syntax Name ::= //"(" Name ")" [bracket]
                "(" "Name" String ")"
  //syntax QName ::= Name | Name"."QName  // FIXME
  // See c-semantics/cil-semantics/cil-syntax.k for Char syntax, including EscapeString.
  syntax Literal ::= Int | Float | "\""String"\"" | "'"Char"'" //| QName

  syntax TypeSignature ::= //"(" TypeSignature ")" [bracket]
                         Name ":" Expr
  syntax TypeSignatures ::= //"(" TypeSignatures ")" [bracket]
                          List{TypeSignature, ";"}

  syntax Lambda ::= "\\" Bindings "->" Expr
                  //| "\\" "(" Variable ":" Expr ")" "->" Expr [notInPrograms, binder(1 -> 3)]
  // TODO: macro
  syntax Pi ::= Bindings "->" Expr
              //| "(" Variable ":" Expr ")" "->" Expr [notInPrograms, binder(1 -> 3)]
  // TODO: macro

  syntax TypedBinding ::= //"(" TypedBinding ")" [bracket]
                        "(" Variables ":" Expr ")"
  syntax Telescope ::= List{TypedBinding, ""}
  syntax Binding ::= Variables //[bracket]
                   | TypedBinding
  syntax Bindings ::= List{Binding, ""}

  syntax Pattern ::= "(" Pattern ")" [bracket]
    | Variable
    | Name
    | Name Pattern  [left]
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
