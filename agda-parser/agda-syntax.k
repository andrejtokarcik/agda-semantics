module AGDA-SYNTAX
  // perhaps I don't have to include ranges at all? is it good for anything
  // besides error reporting?

  //syntax Identifier ::= Token{[a-zA-Z0-9\_]+}        [notInRules]
  syntax Variable ::= Var(String)                [klabel('Var)]
  syntax Variables ::= List{Variable, ""}
  syntax Name ::= Name(String)                   [klabel('Name)]
  // See c-semantics/cil-semantics/cil-syntax.k for Char syntax, including EscapeString.
  syntax Literal ::= Int | Float | "\""String"\"" | "'"Char"'" //| QName

  syntax TypedBinding ::= "(" Variable ":" Expr ")"
                        | TBind(Variables, Expr)     [klabel('TBind)]
  syntax Telescope ::= List{TypedBinding, ""}
  rule TBind(X:Variable Xs:Variables, E:Expr) Tel:Telescope => (X : E) (TBind(Xs, E) Tel)  [macro]
  rule TBind(.Variables, E:Expr) Tel:Telescope => Tel                            [macro]

  // TODO: 'Fun
  syntax Pi ::= "(" Variable ":" Expr ")" "->" Expr  [binder(1 -> 3)]
              | Pi(Telescope, Expr)                  [klabel('Pi)]
  rule Pi((X:Variable : T:Expr) Tel:Telescope, E:Expr) => (X : T) -> Pi(Tel, E)  [macro]
  rule Pi(.Telescope, E:Expr) => E                                               [macro]

  syntax LamBinding ::= Variable | TypedBinding
  syntax LamBindings ::= List{LamBinding, ""}
                       | Telescope
  syntax Lambda ::= "\\" "(" Variable ":" Expr ")" "->" Expr  [binder(1 -> 3)]
                  | Lam(LamBindings, Expr)           [klabel('Lam)]

  syntax Telescope ::= coerceTelescope(LamBindings)  [function, notInPrograms]
  rule coerceTelescope(X:Variable Bnds:LamBindings) => (X : $metavar) coerceTelescope(Bnds)  [structural]
  rule coerceTelescope(Bnd:TypedBinding Bnds:LamBindings) => Bnd coerceTelescope(Bnds)  [structural]
  rule coerceTelescope(.LamBindings) => .Telescope   [structural]

  rule Lam(Bnds:LamBindings => coerceTelescope(Bnds), _)    when isTelescope(Bnds) =/=K true       [macro]
  rule Lam((X:Variable : T:Expr) Bnds:LamBindings, E:Expr) => \ (X : T) -> Lam(Bnds, E)  [macro]
  rule Lam(.LamBindings, E:Expr) => E                                            [macro]

  syntax Expr ::= "(" Expr ")" [bracket]
    | Variable
    | Name
    | Pi
    | Lambda
    | Expr Expr    [left]
    | "Set"        [klabel('Set), notInRules]
    | "Set" Int    [klabel('SetN)]
    | "$metavar"      [klabel('Underscore)]     // '_' is reserved for K rules
  rule 'Set(.KList) => Set0  [macro]

  syntax TypeSignature ::= Name ":" Expr  [klabel('TypeSig)]

  syntax Pattern ::= "(" Pattern ")" [bracket]
    | Variable
    | Name
    | Name Pattern  [klabel('AppP), left]
  syntax LHS ::= Name
               | LHS Pattern  [left]
  syntax RHS ::= Expr
  syntax FunClause ::= LHS "=" RHS                   [klabel('FunClause)]

  syntax Declaration ::= "(" Declaration ")" [bracket]
    | TypeSignature
    | FunClause
    | "postulate" Declaration                        [klabel('Postulate)]
    | "module" Name Telescope "where" Declarations   [klabel('Module)]
  syntax Declarations ::= List{Declaration, ""}

  syntax Program ::= Declarations


  // metadata
  /*
  syntax Range ::= "$noRange"
    | "$someRange"
    | Token{([a-zA-Z0-9\/\-]+ "." "l"? "agda" ":")? [0-9]+ "," [0-9]+ "-" ([0-9]+ ",")? [0-9]+}  [notInRules]
  */
  syntax Range ::= String
  syntax Declaration ::= "[" Range "]" Declaration
endmodule
