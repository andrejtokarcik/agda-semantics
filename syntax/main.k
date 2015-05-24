require "utils.k"

module AGDA-SYNTAX
  imports AGDA-SYNTAX-UTILS

  syntax Identifier ::= String
  syntax Variable ::= Var(Identifier)        [klabel('Var)]
  syntax Variables ::= List{Variable, ""}    [klabel('Cons)]
  syntax Name ::= Name(Identifier)           [klabel('Name)]

  syntax Relevance ::= "Relevant"
  syntax Hiding ::= "Hidden" | "NotHidden"

  syntax TypedBinding ::= "(" Variable ":" Expr ")"
                        | "{" Variable ":" Expr "}"
                        | TBind(Relevance, Hiding, Variables, Expr)                  [klabel('TBind)]
  syntax Telescope ::= List{TypedBinding, ""}                                        [klabel('Cons)]
  rule TBind(Relevant, NotHidden, X:Variable Xs:Variables, E:Expr) Tel:Telescope
       => (X : E) (TBind(Relevant, NotHidden, Xs, E) Tel)                            [macro]
  rule TBind(Relevant, Hidden, X:Variable Xs:Variables, E:Expr) Tel:Telescope
       => {X : E} (TBind(Relevant, Hidden, Xs, E) Tel)                               [macro]
  rule TBind(_:Relevance, _:Hiding, .Variables, E:Expr) Tel:Telescope => Tel         [macro]

  syntax ImplicitPi ::= "{" Variable ":" Expr "}" "->" Expr          [binder(1 -> 3), latex(\{{#1}\,:\,{#2}\} \rightarrow {#3})]
  syntax Pi ::= "(" Variable ":" Expr ")" "->" Expr                  [binder(1 -> 3), latex(({#1}\,:\,{#2}) \rightarrow {#3})]
              | ImplicitPi
              | Pi(Telescope, Expr)                                                  [klabel('Pi)]
              | Fun(Expr, Expr)                                                      [klabel('Fun)]
  rule Pi((X:Variable : T1:Expr) Tel:Telescope, T2:Expr) => (X : T1) -> Pi(Tel, T2)  [macro]
  rule Pi({X:Variable : T1:Expr} Tel:Telescope, T2:Expr) => {X : T1} -> Pi(Tel, T2)  [macro]
  rule Pi(.Telescope, T:Expr) => T                                                   [macro]
  rule Fun(T1:Expr, T2:Expr) => (X : T1) -> T2  when fresh(X:Variable)               [macro]

  syntax LamBinding ::= LamBind(Relevance, Hiding, Variable)                         [klabel('LamBind)]
                      | TypedBinding
  syntax LamBindings ::= List{LamBinding, ""}                                        [klabel('Cons)]
                       | Telescope
  syntax Lambda ::= "\\" "(" Variable ":" Expr ")" "->" Expr         [binder(1 -> 3), latex(\lambda ({#1}\,:\,{#2}) \rightarrow {#3})]
                  | "\\" "{" Variable ":" Expr "}" "->" Expr         [binder(1 -> 3), latex(\lambda \{{#1}\,:\,{#2}\} \rightarrow {#3})]
                  | Lam(LamBindings, Expr)                                           [klabel('Lam)]

  rule Lam(Bs:LamBindings => castTelescope(Bs), _)  when isTelescope(Bs) =/=K true   [macro]
  rule Lam((X:Variable : T:Expr) Bs:Telescope, E:Expr) => \ (X : T) -> Lam(Bs, E)    [macro]
  rule Lam({X:Variable : T:Expr} Bs:Telescope, E:Expr) => \ {X : T} -> Lam(Bs, E)    [macro]
  rule Lam(.LamBindings, E:Expr) => E                                                [macro]

  syntax Arg ::= Arg(Hiding, K)                                [klabel('Arg)]
  rule Arg(NotHidden, K:K) => K                                [macro]
  rule Arg(Hidden, K:K) => {K}                                 [macro]
  syntax Args ::= List{Arg, ""}                                [klabel('Cons), notInRules]
                | Telescope
  syntax App ::= "(" App ")"                                   [bracket]
               | Arg Arg                                       [left]
               | App(Arg, Args)                                [klabel('App)]
               | App(Arg, Telescope)
               | OpApp(Arg, Args)                              [klabel('OpApp)]
  rule OpApp(A:Arg, As:Args) => App(A, As)                     [macro]
  rule App(A:Arg, '.List`{""`}(.KList)) => A                   [macro]
  rule App(A:Arg, 'Cons(A':Arg,, As:Args)) => App(A A', As)    [macro]
  rule App(A:Arg, (X : _) Tel) => App(A X, Tel)                [macro]
  rule App(A:Arg, {X : _} Tel) => App(A {X}, Tel)              [macro]

  syntax Universe ::= Set(Int)     [klabel('SetN), latex(\KSet_{#1})]
                    | "Set"        [klabel('Set), notInRules]
  rule 'Set(.KList) => Set(0)      [macro]

  syntax Arg ::= Expr
  syntax Meta ::= "%meta"                               [klabel('Underscore)]
  syntax Implicit ::= "{" Expr "}"
  syntax Let ::= "let" Declarations "in" Expr           [klabel('Let)]

  syntax Expr ::= "(" Expr ")" [bracket]
    | Variable
    | Name
    | Universe
    | Pi
    | Lambda
    | App
    | Meta
    | Implicit
    | Let
  syntax Exprs ::= List{Expr, ""}                       [klabel('Cons), notInRules]

  syntax TypeSignature ::= Name ":" Expr                [klabel('TypeSig)]
  syntax TypeSignatures ::= List{TypeSignature, ";"}    [klabel('Cons)]

  syntax Absurd ::= "%absurd"                           [klabel('AbsurdP)]
  syntax Wildcard ::=  "%wild"                          [klabel('WildP)]
  syntax InaccessiblePattern ::= DotP(Pattern)          [klabel('DotP)]
  syntax Arg ::= Absurd
               | Wildcard
               | InaccessiblePattern
  syntax App ::= AppP(Arg, Arg)                         [klabel('AppP)]
               | OpAppP(Arg, Args)                      [klabel('OpAppP)]
  rule AppP(A:Arg, A':Arg) => App(A, A')                [macro]
  rule OpAppP(A:Arg, As:Args) => OpApp(A, As)           [macro]
  syntax Pattern ::= "(" Pattern ")"                    [bracket]
    | Arg
    | App

  // XXX Distinct wildcards may get expanded into the same variable
  //     (as though the macro expansion executed in parallel).
  // WAS:  => X  when fresh(X:Variable)  [macro]
  rule %wild => %meta                                   [macro]
  syntax Patterns ::= List{Pattern, ""}                 [klabel('Cons), notInRules]

  syntax LHS ::= Pattern
  syntax RHS ::= Expr
               | "AbsurdRHS"                            [klabel('AbsurdRHS)]
  syntax FunClause ::= LHS "=" RHS
                     | LHS "=" RHS "where" Declarations [klabel('FunClause)]
                     | Absurd(LHS)
  rule L:LHS = R:RHS where .Declarations => L = R       [macro]
  rule L:LHS = AbsurdRHS => Absurd(L)                   [macro]

  syntax DataDeclaration ::= Data(Name, LamBindings, Expr, TypeSignatures)  [klabel('Data)]
                           | "data" Name Telescope ":" Expr "where" TypeSignatures
  rule Data(_, Ps:LamBindings => castTelescope(Ps), _, _)
    when isTelescope(Ps) =/=K true  [macro]
  rule Data(N, Ps:Telescope, T, Cons) => data N Ps : T where Cons  [macro]

  syntax Declaration ::= "(" Declaration ")"            [bracket]
    | TypeSignature
    | FunClause
    | DataDeclaration
    | "postulate" TypeSignatures                        [klabel('Postulate)]
    | "module" /*Q*/Name Telescope "where" Declarations [klabel('Module)]
  syntax Declarations ::= List{Declaration, ";"}        [klabel('Cons)]

  syntax Program ::= Declarations
endmodule
