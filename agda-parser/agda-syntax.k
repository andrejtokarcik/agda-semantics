module AGDA-SYNTAX
  // TODO: agda-syntax-utils.k    -- presunut tam aj makra?
  syntax Telescope ::= castTelescope(LamBindings)  [function, notInPrograms]
  rule castTelescope(X:Variable Bs:LamBindings) => (X : %underscore) castTelescope(Bs)  [structural]
  rule castTelescope(B:TypedBinding Bs:LamBindings) => B castTelescope(Bs)  [structural]
  rule castTelescope(.LamBindings) => .Telescope   [structural]


  // perhaps I don't have to include ranges at all? is it good for anything
  // besides error reporting?

  //syntax Identifier ::= Token{[a-zA-Z0-9\_]+}        [notInRules]
  syntax Identifier ::= String
  // NOTE: The sort Variable is used in unification/pattern-matching.
  syntax Variable ::= Var(Identifier)                [klabel('Var)]
  syntax Variables ::= List{Variable, ""}    [klabel('Cons)]
  syntax Name ::= Name(Identifier)                   [klabel('Name)]
  // See c-semantics/cil-semantics/cil-syntax.k for Char syntax, including EscapeString.
  syntax Literal ::= Int | Float | "\""String"\"" | "'"Char"'" //| QName

  syntax TypedBinding ::= "(" Variable ":" Expr ")"
                        | TBind(Variables, Expr)     [klabel('TBind)]
  syntax Telescope ::= List{TypedBinding, ""}    [klabel('Cons)]
  rule TBind(X:Variable Xs:Variables, E:Expr) Tel:Telescope => (X : E) (TBind(Xs, E) Tel)  [macro]
  rule TBind(.Variables, E:Expr) Tel:Telescope => Tel                            [macro]

  // TODO: 'Fun
  syntax Pi ::= "(" Variable ":" Expr ")" "->" Expr  [binder(1 -> 3), latex(({#1}\,:\,{#2}) \rightarrow {#3})]
              | Pi(Telescope, Expr)                  [klabel('Pi)]
              | Fun(Expr, Expr)                      [klabel('Fun)]
  rule Pi((X:Variable : T1:Expr) Tel:Telescope, T2:Expr) => (X : T1) -> Pi(Tel, T2)  [macro]
  rule Pi(.Telescope, T:Expr) => T                                                   [macro]
  rule Fun(T1:Expr, T2:Expr) => (X : T1) -> T2  when fresh(X:Variable)               [macro]

  syntax LamBinding ::= Variable | TypedBinding
  syntax LamBindings ::= List{LamBinding, ""}    [klabel('Cons)]
                       | Telescope
  syntax Lambda ::= "\\" "(" Variable ":" Expr ")" "->" Expr  [binder(1 -> 3), latex(\lambda ({#1}\,:\,{#2}) \rightarrow {#3})]
                  | Lam(LamBindings, Expr)           [klabel('Lam)]

  rule Lam(Bs:LamBindings => castTelescope(Bs), _)    when isTelescope(Bs) =/=K true       [macro]
  rule Lam((X:Variable : T:Expr) Bs:Telescope, E:Expr) => \ (X : T) -> Lam(Bs, E)  [macro]
  rule Lam(.LamBindings, E:Expr) => E                                            [macro]

  syntax App ::= Expr Expr  [left]
               | App(Expr, Exprs)    [klabel('App)]
               | OpApp(Expr, Exprs)  [klabel('OpApp)]
  rule OpApp(E:Expr, Es:Exprs) => App(E, Es) [macro]
  rule App(E:Expr, 'Cons(E':Expr,, Es:Exprs)) => E App(E', Es) when Es =/=K '.List`{""`}(.KList) [macro]
  rule App(E:Expr, 'Cons(E':Expr,, '.List`{""`}(.KList))) => E E'  [macro]

  syntax Universe ::= Set(Int)     [klabel('SetN), latex(\terminal{Set}_{#1})]
                    | "Set"        [klabel('Set), notInRules]
  rule 'Set(.KList) => Set(0)  [macro]

  syntax Expr ::= "(" Expr ")" [bracket]
    | Variable
    | Name
    | Universe
    | Pi
    | Lambda
    | App
    | "%underscore"      [klabel('Underscore)]
  syntax Exprs ::= List{Expr, ""}    [klabel('Cons), notInRules]

  syntax TypeSignature ::= Name ":" Expr  [klabel('TypeSig)]
  syntax TypeSignatures ::= List{TypeSignature, ""}    [klabel('Cons)]

  syntax Pattern ::= "(" Pattern ")" [bracket]
    | Variable
    | Name
    | AppP
  syntax AppP ::= Pattern Pattern [left, notInRules]
    | AppP(Pattern, Pattern)     [klabel('AppP)]
    | OpAppP(Pattern, Patterns)  [klabel('OpAppP)]
  //syntax Expr ::= Pattern
  syntax Patterns ::= List{Pattern, ""}    [klabel('Cons), notInRules]

  rule AppP(P:Pattern, P':Pattern) => '__(P,, P')  [macro]
  //rule OpAppP(P:Pattern, 'Cons(P':Pattern,, Ps:Patterns)) => P OpAppP(P', Ps)  [macro]
  //rule OpAppP(P:Pattern, 'Cons(P':Pattern,, '.List`{""`}(.KList))) => P P'    [macro]
  rule OpAppP(P:Pattern, 'Cons(P':Pattern,, Ps:Patterns)) => OpAppP('__(P,, P'), Ps)   [macro]
  rule OpAppP(P:Pattern, '.List`{""`}(.KList)) => P   [macro]

  /*
  syntax LHS ::= Name
               | LHS Pattern  [left]
  */
  syntax LHS ::= Pattern
  //rule isLHS(_:Name) => true
  //rule isLHS(_:LHS _:Pattern) => true
  syntax RHS ::= Expr
  syntax FunClause ::= LHS "=" RHS                   [binder, klabel('FunClause)]

  syntax DataDeclaration ::= Data(Name, LamBindings, Expr, TypeSignatures)  [klabel('Data)]
                           | "data" Name Telescope ":" Expr "where" TypeSignatures
  rule Data(_, Ps:LamBindings => castTelescope(Ps), _, _)
    when isTelescope(Ps) =/=K true  [macro]
  rule Data(N, Ps:Telescope, T, Cons) => data N Ps : T where Cons  [macro]

  syntax Declaration ::= "(" Declaration ")" [bracket]
    | TypeSignature
    | FunClause
    | DataDeclaration
    | "postulate" TypeSignatures                     [klabel('Postulate)]
    | "module" /*Q*/Name Telescope "where" Declarations   [klabel('Module)]
  syntax Declarations ::= List{Declaration, ""}    [klabel('Cons)]

  syntax Program ::= Declarations


  // metadata
  /*
  syntax Range ::= "%noRange"
    | "%someRange"
    | Token{([a-zA-Z0-9\/\-]+ "." "l"? "agda" ":")? [0-9]+ "," [0-9]+ "-" ([0-9]+ ",")? [0-9]+}  [notInRules]
  */
  syntax Range ::= String
  syntax Declaration ::= "[" Range "]" Declaration
endmodule
