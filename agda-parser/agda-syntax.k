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
  syntax Variables ::= List{Variable, ""}            [klabel('Cons)]
  syntax Name ::= Name(Identifier)                   [klabel('Name)]
  // See c-semantics/cil-semantics/cil-syntax.k for Char syntax, including EscapeString.
  syntax Literal ::= Int | Float | "\""String"\"" | "'"Char"'" //| QName

  syntax Relevance ::= "Relevant"
  syntax Hiding ::= "Hidden" | "NotHidden"
  syntax TypedBinding ::= "(" Variable ":" Expr ")"
                        | "{" Variable ":" Expr "}"
                        | TBind(Relevance, Hiding, Variables, Expr)     [klabel('TBind)]
  syntax Telescope ::= List{TypedBinding, ""}    [klabel('Cons)]
  rule TBind(Relevant, NotHidden, X:Variable Xs:Variables, E:Expr) Tel:Telescope
       => (X : E) (TBind(Relevant, NotHidden, Xs, E) Tel)  [macro]
  rule TBind(Relevant, Hidden, X:Variable Xs:Variables, E:Expr) Tel:Telescope
       => {X : E} (TBind(Relevant, Hidden, Xs, E) Tel)     [macro]
  rule TBind(_:Relevance, _:Hiding, .Variables, E:Expr) Tel:Telescope => Tel         [macro]

  // these binders get really repetitive.  do I need them after all? pattern matching doesn't take them
  // into account anyway (or does it?).  the only occassion when it appears to be of use is when
  // calling freeVariables() which I could, however, implement on my own.
  // syntax Pi ::= TypedBinding -> Expr    would be quite ideal
  // (so that I can latter have rules with `_ -> _` on LHS instead of both `(_ : _) -> _` and `{_ : _} -> _`)
  // TODO: gotta test all those binding gotchas anyway.
  syntax Pi ::= "(" Variable ":" Expr ")" "->" Expr  [binder(1 -> 3), latex(({#1}\,:\,{#2}) \rightarrow {#3})]
              | "{" Variable ":" Expr "}" "->" Expr  [binder(1 -> 3), latex({\{#1}\,:\,{#2}\} \rightarrow {#3})]
              | Pi(Telescope, Expr)                  [klabel('Pi)]
              | Fun(Expr, Expr)                      [klabel('Fun)]
  rule Pi((X:Variable : T1:Expr) Tel:Telescope, T2:Expr) => (X : T1) -> Pi(Tel, T2)  [macro]
  rule Pi({X:Variable : T1:Expr} Tel:Telescope, T2:Expr) => {X : T1} -> Pi(Tel, T2)  [macro]
  rule Pi(.Telescope, T:Expr) => T                                                   [macro]
  rule Fun(T1:Expr, T2:Expr) => (X : T1) -> T2  when fresh(X:Variable)               [macro]

  syntax LamBinding ::= Variable | TypedBinding
  syntax LamBindings ::= List{LamBinding, ""}    [klabel('Cons)]
                       | Telescope
  syntax Lambda ::= "\\" "(" Variable ":" Expr ")" "->" Expr  [binder(1 -> 3), latex(\lambda ({#1}\,:\,{#2}) \rightarrow {#3})]
                  | "\\" "{" Variable ":" Expr "}" "->" Expr  [binder(1 -> 3), latex(\lambda \{{#1}\,:\,{#2}\} \rightarrow {#3})]
                  | Lam(LamBindings, Expr)           [klabel('Lam)]

  rule Lam(Bs:LamBindings => castTelescope(Bs), _)    when isTelescope(Bs) =/=K true       [macro]
  rule Lam((X:Variable : T:Expr) Bs:Telescope, E:Expr) => \ (X : T) -> Lam(Bs, E)  [macro]
  rule Lam({X:Variable : T:Expr} Bs:Telescope, E:Expr) => \ {X : T} -> Lam(Bs, E)  [macro]
  rule Lam(.LamBindings, E:Expr) => E                                              [macro]

  syntax Arg ::= Expr
               | Arg(Hiding, Expr)  [klabel('Arg)]
  rule Arg(NotHidden, E:Expr) => E  [macro]
  rule Arg(Hidden, E:Expr) => {E}   [macro]
  syntax Args ::= List{Arg, ""}     [klabel('Cons), notInRules]
  syntax App ::= "(" App ")"        [bracket]
               | Arg Arg            [left]
               | App(Arg, Args)     [klabel('App)]
               | OpApp(Arg, Args)   [klabel('OpApp)]
  rule OpApp(A:Arg, As:Args) => App(A, As) [macro]
  rule App(A:Arg, 'Cons(A':Arg,, As:Args)) => App(A A', As) [macro]
  rule App(A:Arg, '.List`{""`}(.KList)) => A  [macro]

  syntax Universe ::= Set(Int)     [klabel('SetN), latex(\terminal{Set}_{#1})]
                    | "Set"        [klabel('Set), notInRules]
  rule 'Set(.KList) => Set(0)  [macro]

  syntax Underscore ::= "%underscore"      [klabel('Underscore)]
  syntax Implicit ::= "{" Expr "}"
  syntax Expr ::= "(" Expr ")" [bracket]
    | Variable
    | Name
    | Universe
    | Pi
    | Lambda
    | App
    | Underscore
    | Implicit
  syntax Exprs ::= List{Expr, ""}    [klabel('Cons), notInRules]

  syntax TypeSignature ::= Name ":" Expr  [klabel('TypeSig)]
  syntax TypeSignatures ::= List{TypeSignature, ""}    [klabel('Cons)]

  syntax Pattern ::= "(" Pattern ")" [bracket]
    | Arg
    | App
  syntax Patterns ::= List{Pattern, ""}    [klabel('Cons), notInRules]
  syntax App ::= AppP(Arg, Arg)     [klabel('AppP)]
               | OpAppP(Arg, Args)  [klabel('OpAppP)]
  rule AppP(A:Arg, A':Arg) => App(A, A')  [macro]  //'Cons(A':Arg,, '.List`{""`}(.KList))) [macro]
  rule OpAppP(A:Arg, As:Args) => OpApp(A, As) [macro]

  syntax LHS ::= Pattern
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
