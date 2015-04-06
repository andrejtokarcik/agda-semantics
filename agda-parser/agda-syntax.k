module AGDA-SYNTAX
  // perhaps I don't have to include ranges at all? is it good for anything
  // besides error reporting?

  // TODO: get rid of Color as done for Range...
  // TODO: convert all of those into functions (i.e. klabels without underscores)
  // and then mark everything as [onlyLabel] -> we should refer to -pretty.k terms exclusively

  // output z `agda` je teraz dvakrat zabaleny zoznam (neviem preco)
  syntax Program ::= List{DeclarationL, ","}

  // elementom DeclarationL moze byt aj samotne DeclarationL, kedze
  // K automaticky zoznam nastavi ako subsort toho sortu elementov,
  // t. j. DeclarationL < Declaration
  syntax DeclarationL ::= List{Declaration, ","}

  // TODO: skus to urobit tak ze tu v K budem pracovat s peknou beznou citatelnou syntaxou
  // Agda programov, ale z K parsera dostanem Concrete
  // tak zachovam vyhody (scope checking, spracovane operatory atd.) i budem mat
  // pekne pravidla v semantike.

  syntax Declaration ::= "(" Declaration ")" [bracket]
    | "TypeSig" ArgInfo Name Expr
    | "FunClause" LHS RHS WhereClause
    | "DataSig" Induction Name LamBindingL Expr
    | "Data" Induction Name LamBindingL ExprM TypeSignatureOrInstanceBlockL
    | "Syntax" Name Notation
    | "Postulate" TypeSignatureOrInstanceBlockL
    | "Module" QName Telescope DeclarationL

  syntax Expr ::= "(" Expr ")" [bracket]
    | "Ident" Name
    | "Lam" LamBindingL Expr
    | "App" Expr ArgExpr
    | "Fun" Expr Expr
    | "Pi" Telescope Expr
    | "Set"  [onlyLabel]
    | "Set" Int
  rule 'Set(.KList) => (Set 0) [macro]

  syntax LHS ::= "(" LHS ")" [bracket]
    | "LHS" Pattern PatternL RewriteEqnL WithExprL      // LHS lhsOriginalPattern lhsWithPattern lhsRewriteEqn lhsWithExpr
    //| "Ellipsis" ...
  syntax PatternL ::= List{Pattern, ","}
  syntax Pattern ::= "(" Pattern ")" [bracket]
    | "IdentP" QName
    | "QuoteP"
    //| ... etc, TODO
  syntax RewriteEqnL ::= List{RewriteEqn, ","}
  syntax RewriteEqn ::= Expr
  syntax WithExprL ::= List{WithExpr, ","}
  syntax WithExpr ::= Expr

  syntax RHS ::= "(" RHS ")" [bracket]
    | "AbsurdRHS"
    | "RHS" Expr

  syntax WhereClause ::= "(" WhereClause ")" [bracket]
    | "NoWhere"
    | "AnyWhere" DeclarationL
    | "SomeWhere" Name DeclarationL

  syntax Induction ::= "Inductive"   // don't support "CoInductive"

  syntax LamBindingL ::= List{LamBinding, ","}
  syntax LamBinding ::= "(" LamBinding ")" [bracket]
    | "DomainFree" ArgInfo BoundName
    | "DomainFull" TypedBindings

  syntax Telescope ::= "(" Telescope ")" [bracket]
    | List{TypedBindings, ","}
  syntax TypedBindings ::= "(" TypedBindings ")" [bracket]
    | "TypedBindings" ArgTypedBinding
  syntax ArgTypedBinding ::= "(" ArgTypedBinding ")" [bracket]
    | "Arg" ArgInfo TypedBinding
  syntax TypedBinding ::= "(" TypedBinding ")" [bracket]
    | "TBind" BoundNameL Expr
    | "TLet" DeclarationL Expr
  syntax BoundNameL ::= List{BoundName, ","}
  syntax BoundName ::= "(" BoundName ")" [bracket]
    | "BName" Name Name FixityP
  syntax FixityP ::= "(" FixityP ")" [bracket]
    | "Fixity'" Fixity Notation
  syntax Fixity ::= "(" Fixity ")" [bracket] 
    | "LeftAssoc" Int
    | "RightAssoc" Int
    | "NonAssoc" Int
  syntax Notation ::= GenPartL [bracket]
  syntax GenPartL ::= List{Bool, ","}   // FIXME

  syntax ArgExpr ::= "(" ArgExpr ")" [bracket]
                   | "Arg" ArgInfo Expr

  // ---
  // preliminaries:

  // TODO: accept unicode
  syntax Name ::= Token{[a-zA-Z][a-zA-Z0-9\_]*}  [notInRules]
  syntax QName ::= Name | Name"."QName
  // See c-semantics/cil-semantics/cil-syntax.k for Char syntax, including EscapeString.
  syntax Literal ::= Int | Float | "\""String"\"" | "'"Char"'" | QName

  syntax Hiding ::= "Hidden" | "NotHidden"
  syntax Relevance ::= "Relevant" | "Irrelevant" | "UnusedArg"
  syntax Color ::= Expr
  syntax ColorL ::= List{Color, ","}
  syntax ArgInfo ::= "(" ArgInfo ")" [bracket] 
    | "ArgInfo" Hiding Relevance ColorL

  syntax TypeSignatureOrInstanceBlockL ::= List{TypeSignatureOrInstanceBlock, ","}
  syntax TypeSignatureOrInstanceBlock ::= Declaration

  syntax ExprM ::= "Just" Expr | "Nothing"

  syntax Range ::= "@noRange"
    | "@someRange"
    | Token{([a-zA-Z0-9\/\-]+ "." "l"? "agda" ":")? [0-9]+ "," [0-9]+ "-" ([0-9]+ ",")? [0-9]+}  [notInRules]
  syntax K ::= m(Range, K)    // generic metadata wrapper
endmodule
